/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.NumberTheory.ModularExponentiation
public import Mathlib.FieldTheory.Finite.Basic

/-!
# The Miller–Rabin witness test

`WITNESS(a, n)` and `MILLER-RABIN(n, s)` from CLRS, third edition, Section 31.8. Write
`n - 1 = 2^t * u` with `u` odd and compute `x₀ = a^u mod n` by modular exponentiation; then square
`t` times, `xᵢ = x_{i-1}² mod n`. `a` is a *witness* to the compositeness of `n` when some squaring
produces `1` from a value other than `±1` (a nontrivial square root of `1`), or when the final value
`x_t = a^(n-1) mod n` is not `1` (a Fermat witness). `MILLER-RABIN` reports *composite* as soon as
one of its bases is a witness, and *prime* otherwise.

This module formalizes the test and its one-sided correctness, the part of CLRS's analysis that
needs no probability:

* `witness_eq_false_of_prime`: a prime has no witnesses among `1, …, n - 1`, so
  `millerRabin_of_prime`: on a prime, `MILLER-RABIN` answers *prime* for any such bases.
* Contrapositively (`not_prime_of_witness`, `not_prime_of_millerRabin_eq_false`), a *composite*
  answer is always correct when the bases lie in `1, …, n - 1` (CLRS draws them from that range;
  outside it, `witness 2 2 = true` although `2` is prime).
* `witness_of_pow_ne_one`: every Fermat witness (`a^(n-1) ≢ 1 mod n`) is a witness, so the test
  is at least as strong as Fermat's.

The bound on the number of witnesses of an odd composite (CLRS Theorem 31.38, at least
`(n - 1) / 2`; Monier and Rabin, at least `3(n - 1) / 4`) and the resulting error probability are
not part of this module. The random choice of bases is modeled by passing the bases explicitly.

## Cost model

Modular multiplications, as in `ModularExponentiation`: computing `x₀` costs what
`modularExponentiation a u n` costs (between `⌊log₂ u⌋ + 1` and `2(⌊log₂ u⌋ + 1) - 1`), and each of
the `t` squarings costs one. Comparisons, the split of `n - 1` and control flow are free.
`MILLER-RABIN` adds the costs of the witness tests it runs.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.MillerRabin

open Cslib.Algorithms.Lean TimeM ModularExponentiation

/-- **Splitting off the power of two.** For a natural number $m > 0$, the two-adic split of $m$
is the pair $(t, u)$ of natural numbers with $m = 2^t u$ and $u$ odd. For $m = 0$ it is
$(0, 0)$. -/
def twoAdicSplit (m : ℕ) : ℕ × ℕ :=
  if m ≠ 0 ∧ m % 2 = 0 then
    let r := twoAdicSplit (m / 2)
    (r.1 + 1, r.2)
  else (0, m)
termination_by m
decreasing_by omega

theorem twoAdicSplit_spec (m : ℕ) (hm : 0 < m) :
    m = 2 ^ (twoAdicSplit m).1 * (twoAdicSplit m).2 ∧ (twoAdicSplit m).2 % 2 = 1 := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    rw [twoAdicSplit]
    split_ifs with h
    · obtain ⟨h1, h2⟩ := ih (m / 2) (by omega) (by omega)
      refine ⟨?_, h2⟩
      rw [pow_succ, Nat.mul_assoc, Nat.mul_comm 2, ← Nat.mul_assoc, ← h1]
      omega
    · refine ⟨by simp, ?_⟩
      simp only
      omega

/-- **The Miller–Rabin squaring loop.** Fix a modulus $n$. With no squarings remaining, the loop
at the current value $x$ reports a witness exactly when $x \ne 1$, at no cost. With $k + 1$
squarings remaining, it costs one modular multiplication and computes $y = x^2 \bmod n$; it
reports a witness if $y = 1$, $x \ne 1$ and $x \ne n - 1$, and otherwise continues at $y$ with
$k$ squarings remaining.

Here $x^2 \bmod 0 = x^2$, and $n - 1$ is $0$ when $n = 0$. -/
def witnessLoop (n : ℕ) : ℕ → ℕ → TimeM ℕ Bool
  | 0, x => pure (x != 1)
  | k + 1, x => do
      ✓
      let y := x * x % n
      if y = 1 ∧ x ≠ 1 ∧ x ≠ n - 1 then pure true else witnessLoop n k y

/-- **Miller–Rabin witness test.** For natural numbers $a$ and $n$, write $n - 1 = 2^t u$ with $u$
odd (here $n - 1$ is truncated at $0$, and $t = u = 0$ when $n \le 1$). The test sets $x_0$ to the
result of modular exponentiation of $a$ to the power $u$ modulo $n$, which is $a^u \bmod n$ when
$u > 0$ and $1$ when $u = 0$. For $i = 1, \dots, t$ it computes $x_i = x_{i-1}^2 \bmod n$ and
returns true as soon as $x_i = 1$, $x_{i-1} \ne 1$ and $x_{i-1} \ne n - 1$. If no such step
occurs, it returns true exactly when $x_t \ne 1$. Its cost is the cost of the modular
exponentiation plus one for each squaring performed.

For a base with $0 < a < n$, the answer true proves that $n$ is composite; outside that range the
answer carries no such guarantee (for example, the test returns true for $a = n = 2$), as in CLRS,
whose bases are drawn from $1, \dots, n - 1$. -/
def witness (a n : ℕ) : TimeM ℕ Bool := do
  let tu := twoAdicSplit (n - 1)
  let x ← modularExponentiation a tu.2 n
  witnessLoop n tu.1 x

/-- **The Miller–Rabin test.** Given a natural number $n$ and a list of bases
$a_1, \dots, a_s$, the test runs the witness test for $n$ on each base in turn. It answers
*composite* as soon as some base $a_i$ is a witness to the compositeness of $n$, and *prime* if
none is (in particular on the empty list). Its cost is the sum of the costs of the witness tests
it runs.

This is CLRS `MILLER-RABIN(n, s)` with the bases given explicitly instead of drawn by
`RANDOM(1, n - 1)`. A *composite* answer is guaranteed correct only when every base lies in
$1, \dots, n - 1$. -/
def millerRabin (n : ℕ) : List ℕ → TimeM ℕ Bool
  | [] => pure true
  | a :: as => do
      let w ← witness a n
      if w then pure false else millerRabin n as

/-! ## Cost -/

/-- **Cost bound for the Miller–Rabin squaring loop.** For all natural numbers $n$, $k$ and $x$,
the cost of the squaring loop modulo $n$ started at $x$ with $k$ squarings remaining is at most
$k$. -/
@[simp]
theorem witnessLoop_time_le (n k x : ℕ) : (witnessLoop n k x).time ≤ k := by
  induction k generalizing x with
  | zero => simp [witnessLoop]
  | succ k ih =>
      simp only [witnessLoop, time_bind, time_tick]
      split_ifs
      · simp
      · have := ih (x * x % n)
        omega

/-- **Cost of the Miller–Rabin witness test.** For natural numbers $a$ and $n$, write
$n - 1 = 2^t u$ with $u$ odd (here $n - 1$ is truncated at $0$, and $t = u = 0$ when $n \le 1$).
The cost of the witness test on base $a$ and modulus $n$ is at most the cost of the modular
exponentiation of $a$ to the power $u$ modulo $n$ plus $t$: at most one multiplication for each
of the $t$ squarings. -/
theorem witness_time_le (a n : ℕ) :
    (witness a n).time ≤ (modularExponentiation a (twoAdicSplit (n - 1)).2 n).time +
      (twoAdicSplit (n - 1)).1 := by
  simp only [witness, time_bind]
  exact Nat.add_le_add_left (witnessLoop_time_le _ _ _) _

/-! ## Correctness -/

/-- The only square roots of `1` modulo a prime are `1` and `-1`. -/
private theorem eq_one_or_eq_sub_one_of_mul_mod {p x : ℕ} (hp : p.Prime) (hx : x < p)
    (h : x * x % p = 1) : x = 1 ∨ x = p - 1 := by
  have := Fact.mk hp
  have hsq : ((x : ZMod p)) * (x : ZMod p) = 1 := by
    rw [← Nat.cast_mul, ← ZMod.natCast_mod, h, Nat.cast_one]
  rcases mul_self_eq_one_iff.1 hsq with h1 | h1
  · left
    have := congrArg ZMod.val h1
    rwa [ZMod.val_natCast_of_lt hx, ZMod.val_one] at this
  · right
    have := congrArg ZMod.val h1
    rw [ZMod.val_natCast_of_lt hx] at this
    obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by have := hp.one_lt; omega⟩
    rw [ZMod.val_neg_one] at this
    omega

/-- **The squaring loop modulo a prime finds no witness when it ends at 1.** Let $p$ be a prime
and let $k$ and $x$ be natural numbers with $x < p$ and $x^{2^k} \bmod p = 1$. Then the squaring
loop modulo $p$ started at $x$ with $k$ squarings remaining reports no witness. -/
theorem witnessLoop_eq_false {p : ℕ} (hp : p.Prime) :
    ∀ k x, x < p → x ^ (2 ^ k) % p = 1 → (witnessLoop p k x).ret = false := by
  intro k
  induction k with
  | zero =>
      intro x hx h
      simp only [pow_zero, pow_one, Nat.mod_eq_of_lt hx] at h
      simp [witnessLoop, h]
  | succ k ih =>
      intro x hx h
      have hy : (x * x % p) ^ (2 ^ k) % p = 1 := by
        rw [Nat.pow_mod, Nat.mod_mod, ← Nat.pow_mod, ← pow_two, ← pow_mul, ← pow_succ']
        exact h
      have hylt : x * x % p < p := Nat.mod_lt _ hp.pos
      simp only [witnessLoop, ret_bind]
      split_ifs with hc
      · exfalso
        rcases eq_one_or_eq_sub_one_of_mul_mod hp hx hc.1 with h1 | h1
        · exact hc.2.1 h1
        · exact hc.2.2 h1
      · exact ih _ hylt hy

/-- **A prime has no Miller–Rabin witnesses in range.** Let $n$ be a prime and $a$ a natural
number with $0 < a < n$. Then the witness test does not report $a$ as a witness to the
compositeness of $n$.

Source: CLRS Section 31.8. -/
theorem witness_eq_false_of_prime {n a : ℕ} (hn : n.Prime) (ha : 0 < a) (han : a < n) :
    (witness a n).ret = false := by
  have := Fact.mk hn
  obtain ⟨hsplit, hodd⟩ := twoAdicSplit_spec (n - 1) (by have := hn.one_lt; omega)
  set t := (twoAdicSplit (n - 1)).1
  set u := (twoAdicSplit (n - 1)).2
  have hu : 0 < u := by omega
  simp only [witness, ret_bind]
  rw [modularExponentiation_correct a u n hu hn.pos]
  refine witnessLoop_eq_false hn t _ (Nat.mod_lt _ hn.pos) ?_
  -- Fermat: a^(n-1) ≡ 1
  rw [← Nat.pow_mod, ← pow_mul, Nat.mul_comm, ← hsplit]
  have ha0 : (a : ZMod n) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    exact fun hdvd => absurd (Nat.le_of_dvd ha hdvd) (by omega)
  have hfermat := ZMod.pow_card_sub_one_eq_one ha0
  have h : a ^ (n - 1) % n = 1 % n :=
    (ZMod.natCast_eq_natCast_iff' _ _ _).1 (by rw [Nat.cast_pow, Nat.cast_one]; exact hfermat)
  rwa [Nat.one_mod_eq_one.2 hn.one_lt.ne'] at h

/-- **A Miller–Rabin witness in range proves compositeness.** Let $n$ and $a$ be natural numbers
with $0 < a < n$. If the witness test reports $a$ as a witness to the compositeness of $n$, then
$n$ is not prime. -/
theorem not_prime_of_witness {n a : ℕ} (ha : 0 < a) (han : a < n)
    (h : (witness a n).ret = true) : ¬ n.Prime := fun hn => by
  simp [witness_eq_false_of_prime hn ha han] at h

/-- **The Miller–Rabin test never rejects a prime when its bases lie in range.** Let $n$ be a
prime. For every list of bases $a_1, \dots, a_s$ (possibly empty) with $0 < a_i < n$ for each
$i$, the Miller–Rabin test run on $n$ with these bases answers *prime*. -/
theorem millerRabin_of_prime {n : ℕ} (hn : n.Prime) :
    ∀ bases : List ℕ, (∀ a ∈ bases, 0 < a ∧ a < n) → (millerRabin n bases).ret = true
  | [], _ => by simp [millerRabin]
  | a :: as, hb => by
      have ha := hb a List.mem_cons_self
      simp only [millerRabin, ret_bind, witness_eq_false_of_prime hn ha.1 ha.2, Bool.false_eq_true,
        ite_false]
      exact millerRabin_of_prime hn as (fun b hb' => hb b (List.mem_cons_of_mem _ hb'))

/-- **With bases in range, a composite answer of the Miller–Rabin test is correct.** Let $n$ be
a natural number and $a_1, \dots, a_s$ a list of bases with $0 < a_i < n$ for each $i$. If the
Miller–Rabin test run on $n$ with these bases answers *composite*, then $n$ is not prime. -/
theorem not_prime_of_millerRabin_eq_false {n : ℕ} {bases : List ℕ}
    (hb : ∀ a ∈ bases, 0 < a ∧ a < n) (h : (millerRabin n bases).ret = false) : ¬ n.Prime :=
  fun hn => by simp [millerRabin_of_prime hn bases hb] at h

/-- **The squaring loop reports a witness when it does not end at 1.** Let $n$, $k$ and $x$ be
natural numbers with $n > 0$, $x < n$ and $x^{2^k} \bmod n \ne 1$. Then the squaring loop modulo
$n$ started at $x$ with $k$ squarings remaining reports a witness. -/
theorem witnessLoop_eq_true {n : ℕ} (hn : 0 < n) :
    ∀ k x, x < n → x ^ (2 ^ k) % n ≠ 1 → (witnessLoop n k x).ret = true := by
  intro k
  induction k with
  | zero =>
      intro x hx h
      simp only [pow_zero, pow_one, Nat.mod_eq_of_lt hx] at h
      simp [witnessLoop, h]
  | succ k ih =>
      intro x hx h
      have hy : (x * x % n) ^ (2 ^ k) % n ≠ 1 := by
        rw [Nat.pow_mod, Nat.mod_mod, ← Nat.pow_mod, ← pow_two, ← pow_mul, ← pow_succ']
        exact h
      simp only [witnessLoop, ret_bind]
      split_ifs with hc
      · rfl
      · exact ih _ (Nat.mod_lt _ hn) hy

/-- **Fermat witnesses are Miller–Rabin witnesses.** Let $a$ and $n$ be natural numbers with
$n > 1$. If $a^{n-1} \bmod n \ne 1$, that is, $a^{n-1} \not\equiv 1 \pmod{n}$, then the Miller–Rabin
witness test on base $a$ and modulus $n$ returns true. -/
theorem witness_of_pow_ne_one {n a : ℕ} (hn : 1 < n) (h : a ^ (n - 1) % n ≠ 1) :
    (witness a n).ret = true := by
  obtain ⟨hsplit, hodd⟩ := twoAdicSplit_spec (n - 1) (by omega)
  set t := (twoAdicSplit (n - 1)).1
  set u := (twoAdicSplit (n - 1)).2
  have hu : 0 < u := by omega
  simp only [witness, ret_bind]
  rw [modularExponentiation_correct a u n hu (by omega)]
  refine witnessLoop_eq_true (by omega) t _ (Nat.mod_lt _ (by omega)) ?_
  rw [← Nat.pow_mod, ← pow_mul, Nat.mul_comm, ← hsplit]
  exact h

end Cslib.Algorithms.Lean.MillerRabin

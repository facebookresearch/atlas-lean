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

/-- The split `m = 2^t * u` with `u` odd, as `(t, u)`, for `m > 0` (and `(0, 0)` for `m = 0`). -/
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

/-- The squaring loop: `k` squarings remain and `x` is the current value. -/
def witnessLoop (n : ℕ) : ℕ → ℕ → TimeM ℕ Bool
  | 0, x => pure (x != 1)
  | k + 1, x => do
      ✓
      let y := x * x % n
      if y = 1 ∧ x ≠ 1 ∧ x ≠ n - 1 then pure true else witnessLoop n k y

/-- CLRS `WITNESS(a, n)`. For a base with `0 < a < n`, `true` proves `n` composite
(`not_prime_of_witness`); outside that range the answer carries no such guarantee (for example
`witness 2 2 = true`), as in CLRS, whose bases are drawn from `1, …, n - 1`. -/
def witness (a n : ℕ) : TimeM ℕ Bool := do
  let tu := twoAdicSplit (n - 1)
  let x ← modularExponentiation a tu.2 n
  witnessLoop n tu.1 x

/-- CLRS `MILLER-RABIN(n, s)` with the bases given explicitly: `false` (*composite*) as soon as a
base is a witness, `true` (*prime*) otherwise. The caller supplies bases in `1, …, n - 1`, as
CLRS's `RANDOM(1, n - 1)` does; only then is a *composite* answer guaranteed correct
(`not_prime_of_millerRabin_eq_false`). -/
def millerRabin (n : ℕ) : List ℕ → TimeM ℕ Bool
  | [] => pure true
  | a :: as => do
      let w ← witness a n
      if w then pure false else millerRabin n as

/-! ## Cost -/

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

/-- A witness test costs the modular exponentiation plus at most one multiplication per
squaring. -/
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

/-- On a prime, the loop finds no witness if the final value `x^(2^k)` is `1`. -/
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

/-- CLRS Section 31.8: a prime `n` has no witnesses `a` with `0 < a < n`. -/
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

/-- A witness proves compositeness. -/
theorem not_prime_of_witness {n a : ℕ} (ha : 0 < a) (han : a < n)
    (h : (witness a n).ret = true) : ¬ n.Prime := fun hn => by
  simp [witness_eq_false_of_prime hn ha han] at h

/-- On a prime, `MILLER-RABIN` answers *prime* for every list of bases in `1, …, n - 1`. -/
theorem millerRabin_of_prime {n : ℕ} (hn : n.Prime) :
    ∀ bases : List ℕ, (∀ a ∈ bases, 0 < a ∧ a < n) → (millerRabin n bases).ret = true
  | [], _ => by simp [millerRabin]
  | a :: as, hb => by
      have ha := hb a List.mem_cons_self
      simp only [millerRabin, ret_bind, witness_eq_false_of_prime hn ha.1 ha.2, Bool.false_eq_true,
        ite_false]
      exact millerRabin_of_prime hn as (fun b hb' => hb b (List.mem_cons_of_mem _ hb'))

/-- A *composite* answer from `MILLER-RABIN` is always correct. -/
theorem not_prime_of_millerRabin_eq_false {n : ℕ} {bases : List ℕ}
    (hb : ∀ a ∈ bases, 0 < a ∧ a < n) (h : (millerRabin n bases).ret = false) : ¬ n.Prime :=
  fun hn => by simp [millerRabin_of_prime hn bases hb] at h

/-- If the final value `x^(2^k)` is not `1`, the loop reports a witness. -/
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

/-- Every Fermat witness is a Miller–Rabin witness: if `a^(n-1) ≢ 1 (mod n)` then `WITNESS(a, n)`
returns `true`. -/
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

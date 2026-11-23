/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Crypto.PublicKey.Assumptions
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.NumberTheory.LegendreSymbol.Basic

/-!
# The Rabin function: inversion is as hard as factoring

Rabin (*Digitalized signatures and public-key functions as intractable as factorization*,
MIT/LCS/TR-212, January 1979) proposes the public-key function `E_{n,b}(x) = x (x + b) mod n`
for `n = p q` a product of two primes (`rabinFunction`, his Definition 1). With `b = 2 d`,
`E_{n,b}(x) = (x + d)² - d²`, so inverting `E_{n,b}` extracts square roots modulo `n`
(`rabinFunction_two_mul`). The owner of `p` and `q` extracts square roots prime by prime; for
`p ≡ 3 (mod 4)` the root of a square `m` is `m^((p + 1)/4)` (`pow_add_one_div_four_sq`, his
equation (2)).

Rabin's Theorem 1 turns any square-root algorithm into a factoring algorithm: draw a random unit
`k`, ask the algorithm for a square root `k₁` of `k²`, and output `gcd(k - k₁, n)`. Its proof is
the counting statement `two_mul_card_gcd_mem_eq_totient`: for distinct primes `p`, `q` with `q`
odd and **every** square-root oracle `O` (any function with `O(k²)² = k²` for all units `k`),
exactly half of the units `k` modulo `p q` have `gcd(k - O(k²), p q) ∈ {p, q}`. So one trial with
a uniform unit factors `n` with probability exactly `1/2`, whatever the oracle.
`isFactorization_of_gcd_mem` connects a successful trial with the factoring experiment of
`Cslib.Crypto.PublicKey.Assumptions`.
`two_mul_card_gcd_mem_eq_card` is the same count for an oracle that answers only on a set `Q` of
squares (the core of Rabin's Theorem 2): exactly half of the units `k` with `k² ∈ Q` succeed.

The proof pairs `k` with `c k`, where `c ≡ 1 (mod p)` and `c ≡ -1 (mod q)`: both have the same
square, hence the same oracle answer `k₁`, and exactly one of `k - k₁`, `c k - k₁` vanishes modulo
`q`, while both agree modulo `p`.

**Scope.** Only the counting cores are formalized: running times (Rabin's `2F(n) + 2 log₂ n` and
`2eF(n) + 2 log₂ n` steps) and the expected number of trials are not. The
statement assumes only that `q` is odd; Rabin takes `p`, `q` to be large primes, so the statement
here is slightly more general.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Crypto.PublicKey.Rabin

/-- **The Rabin function.** `E_{n,b}(x) = x (x + b)` in `ZMod n`, the public-key function of
Rabin (MIT/LCS/TR-212, 1979, Section 1, Definition 1), where the public key is `(n, b)` with
`n = p q` a product of two large primes and `0 ≤ b < n`. -/
def rabinFunction (n b : ℕ) (x : ZMod n) : ZMod n := x * (x + b)

/-- **Inverting the Rabin function extracts square roots.** With `b = 2 d`,
`E_{n,b}(x) = (x + d)² - d²`, so a preimage `x` of `m - d²` gives the square root `x + d` of `m`
(Rabin, MIT/LCS/TR-212, 1979, Section 4, pp. 11-12). -/
theorem rabinFunction_two_mul (n d : ℕ) (x : ZMod n) :
    rabinFunction n (2 * d) x = (x + d) ^ 2 - (d : ZMod n) ^ 2 := by
  simp only [rabinFunction]
  push_cast
  ring

/-- **Square roots modulo a prime `p ≡ 3 (mod 4)`.** If `m` is a square in `ZMod p`, then
`m^((p + 1)/4)` is a square root of `m` (Rabin, MIT/LCS/TR-212, 1979, Section 2, equation (2);
the proof is Euler's criterion `m^((p - 1)/2) = 1`). -/
theorem pow_add_one_div_four_sq {p : ℕ} [Fact p.Prime] (hp : p % 4 = 3) {m : ZMod p}
    (hm : IsSquare m) : (m ^ ((p + 1) / 4)) ^ 2 = m := by
  rw [← pow_mul]
  by_cases h0 : m = 0
  · subst h0
    exact zero_pow (by omega)
  · have h := (ZMod.euler_criterion p h0).1 hm
    rw [show (p + 1) / 4 * 2 = p / 2 + 1 by omega, pow_succ, h, one_mul]

section Factoring

variable {p q : ℕ}

/-- The first component of the Chinese remainder isomorphism vanishes exactly when `p` divides
the representative. -/
private theorem crt_fst_eq_zero_iff [NeZero p] [NeZero q] (h : p.Coprime q) (x : ZMod (p * q)) :
    (ZMod.chineseRemainder h x).1 = 0 ↔ p ∣ x.val := by
  have : NeZero (p * q) := ⟨Nat.mul_ne_zero (NeZero.ne p) (NeZero.ne q)⟩
  change (ZMod.cast x : ZMod p × ZMod q).1 = 0 ↔ _
  rw [Prod.fst_zmod_cast, ZMod.cast_eq_val, ZMod.natCast_eq_zero_iff]

/-- The second component of the Chinese remainder isomorphism vanishes exactly when `q` divides
the representative. -/
private theorem crt_snd_eq_zero_iff [NeZero p] [NeZero q] (h : p.Coprime q) (x : ZMod (p * q)) :
    (ZMod.chineseRemainder h x).2 = 0 ↔ q ∣ x.val := by
  have : NeZero (p * q) := ⟨Nat.mul_ne_zero (NeZero.ne p) (NeZero.ne q)⟩
  change (ZMod.cast x : ZMod p × ZMod q).2 = 0 ↔ _
  rw [Prod.snd_zmod_cast, ZMod.cast_eq_val, ZMod.natCast_eq_zero_iff]

/-- **The gcd with `p q` is a prime factor exactly when one prime divides.** For distinct primes
`p`, `q` and any `v`, `gcd(v, p q) ∈ {p, q}` if and only if exactly one of `p`, `q` divides `v`.
This is the success test `1 < (k - k₁, n) < n` in Rabin's proof of Theorem 1 (MIT/LCS/TR-212,
1979, Section 4, equation (6)). -/
theorem gcd_mul_mem_iff (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) (v : ℕ) :
    Nat.gcd v (p * q) ∈ ({p, q} : Finset ℕ) ↔ (p ∣ v ∧ ¬ q ∣ v) ∨ (q ∣ v ∧ ¬ p ∣ v) := by
  have hcop : p.Coprime q := (Nat.coprime_primes hp hq).2 hpq
  rw [Nat.Coprime.gcd_mul v hcop, Finset.mem_insert, Finset.mem_singleton]
  have hgp : Nat.gcd v p = if p ∣ v then p else 1 := by
    split_ifs with h
    · exact Nat.gcd_eq_right h
    · exact Nat.coprime_comm.1 ((Nat.Prime.coprime_iff_not_dvd hp).2 h)
  have hgq : Nat.gcd v q = if q ∣ v then q else 1 := by
    split_ifs with h
    · exact Nat.gcd_eq_right h
    · exact Nat.coprime_comm.1 ((Nat.Prime.coprime_iff_not_dvd hq).2 h)
  have hp1 := hp.one_lt
  have hq1 := hq.one_lt
  rw [hgp, hgq]
  by_cases h1 : p ∣ v <;> by_cases h2 : q ∣ v
  · simp only [h1, h2, ↓reduceIte]
    constructor
    · rintro (h | h) <;> exfalso <;> nlinarith
    · intro h; exfalso; tauto
  · simp only [h1, h2, ↓reduceIte, mul_one]
    simp
  · simp only [h1, h2, ↓reduceIte, one_mul]
    simp
  · simp only [h1, h2, ↓reduceIte, mul_one]
    constructor
    · rintro (h | h) <;> omega
    · intro h; exfalso; tauto

/-- **A successful trial factors `p q`.** If `g ∈ {p, q}` for distinct primes `p`, `q`, then
`(g, p q / g)` is a nontrivial factorization of `p q` in the sense of the factoring experiment
(`Cslib.Crypto.PublicKey.Assumptions.IsFactorization`; Katz and Lindell, Section 8.2.3). -/
theorem isFactorization_of_gcd_mem (hp : p.Prime) (hq : q.Prime) {g : ℕ}
    (hg : g ∈ ({p, q} : Finset ℕ)) :
    Cslib.Crypto.PublicKey.Assumptions.IsFactorization (p * q) (g, p * q / g) := by
  rw [Finset.mem_insert, Finset.mem_singleton] at hg
  rcases hg with rfl | rfl
  · refine ⟨Nat.mul_div_cancel' (dvd_mul_right _ _), hp.one_lt, ?_⟩
    rw [Nat.mul_div_cancel_left _ hp.pos]
    exact hq.one_lt
  · refine ⟨Nat.mul_div_cancel' (dvd_mul_left _ _), hq.one_lt, ?_⟩
    rw [Nat.mul_div_cancel _ hq.pos]
    exact hp.one_lt

/-- **A square-root oracle that answers on a set of squares factors `p q` on half of its
domain** (Rabin, MIT/LCS/TR-212, 1979, Section 4, proof of Theorem 2). Let `p ≠ q` be primes with
`q` odd, `Q` a set of residues modulo `p q`, and `O` any function with `O(k²)² = k²` for every unit
`k` with `k² ∈ Q` (an algorithm that returns a square root on the squares in `Q` only). Then
exactly half of the units `k` with `k² ∈ Q` satisfy `gcd(k - O(k²), p q) ∈ {p, q}`. Rabin's
Theorem 2 takes `Q` to be the squares on which the algorithm succeeds within its time bound, a
fraction `1/e` of them; then each trial succeeds with probability `1/(2e)`. -/
theorem two_mul_card_gcd_mem_eq_card [hp : Fact p.Prime] [hq : Fact q.Prime] (hpq : p ≠ q)
    (hq2 : q ≠ 2) (Q : Set (ZMod (p * q))) [DecidablePred (· ∈ Q)]
    (O : ZMod (p * q) → ZMod (p * q))
    (hO : ∀ k : (ZMod (p * q))ˣ, (k : ZMod (p * q)) ^ 2 ∈ Q →
      O ((k : ZMod (p * q)) ^ 2) ^ 2 = (k : ZMod (p * q)) ^ 2) :
    2 * (Finset.univ.filter fun k : (ZMod (p * q))ˣ => (k : ZMod (p * q)) ^ 2 ∈ Q ∧
        Nat.gcd ((k : ZMod (p * q)) - O ((k : ZMod (p * q)) ^ 2)).val (p * q) ∈
          ({p, q} : Finset ℕ)).card =
      (Finset.univ.filter fun k : (ZMod (p * q))ˣ => (k : ZMod (p * q)) ^ 2 ∈ Q).card := by
  have hcop : p.Coprime q := (Nat.coprime_primes hp.out hq.out).2 hpq
  have : NeZero (p * q) := ⟨Nat.mul_ne_zero hp.out.ne_zero hq.out.ne_zero⟩
  set e := ZMod.chineseRemainder hcop with he
  -- the unit `c ≡ 1 (mod p)`, `c ≡ -1 (mod q)`
  set c0 : ZMod (p * q) := e.symm (1, -1) with hc0
  have hc0sq : c0 * c0 = 1 := by
    apply e.injective
    rw [map_mul, hc0, RingEquiv.apply_symm_apply, map_one]
    ext <;> simp
  let c : (ZMod (p * q))ˣ := ⟨c0, c0, hc0sq, hc0sq⟩
  have hec : e (c : ZMod (p * q)) = (1, -1) := by
    change e c0 = _
    rw [hc0, RingEquiv.apply_symm_apply]
  -- the success predicate, componentwise
  let good : (ZMod (p * q))ˣ → Prop := fun k =>
    ((e ((k : ZMod (p * q)) - O ((k : ZMod (p * q)) ^ 2))).1 = 0 ∧
        ¬ (e ((k : ZMod (p * q)) - O ((k : ZMod (p * q)) ^ 2))).2 = 0) ∨
      ((e ((k : ZMod (p * q)) - O ((k : ZMod (p * q)) ^ 2))).2 = 0 ∧
        ¬ (e ((k : ZMod (p * q)) - O ((k : ZMod (p * q)) ^ 2))).1 = 0)
  have hgood : ∀ k : (ZMod (p * q))ˣ,
      Nat.gcd ((k : ZMod (p * q)) - O ((k : ZMod (p * q)) ^ 2)).val (p * q) ∈
        ({p, q} : Finset ℕ) ↔ good k := by
    intro k
    have hf := fun x => crt_fst_eq_zero_iff hcop x
    have hs := fun x => crt_snd_eq_zero_iff hcop x
    rw [← he] at hf hs
    rw [gcd_mul_mem_iff hp.out hq.out hpq]
    simp only [good, hf, hs]
  have htwo : (2 : ZMod q) ≠ 0 := by
    intro h
    have : ((2 : ℕ) : ZMod q) = 0 := by exact_mod_cast h
    rw [ZMod.natCast_eq_zero_iff] at this
    rcases (Nat.dvd_prime Nat.prime_two).1 this with h1 | h1
    · exact hq.out.one_lt.ne' h1
    · exact hq2 h1
  -- the pairing `k ↦ c k` flips the success predicate
  have hsq' : ∀ k : (ZMod (p * q))ˣ,
      ((c * k : (ZMod (p * q))ˣ) : ZMod (p * q)) ^ 2 = (k : ZMod (p * q)) ^ 2 := by
    intro k
    push_cast
    rw [mul_pow, sq c0, hc0sq, one_mul]
  have hflip : ∀ k : (ZMod (p * q))ˣ, (k : ZMod (p * q)) ^ 2 ∈ Q →
      (good (c * k) ↔ ¬ good k) := by
    intro k hkQ
    have hsq : ((c * k : (ZMod (p * q))ˣ) : ZMod (p * q)) ^ 2 = (k : ZMod (p * q)) ^ 2 := by
      push_cast
      rw [mul_pow, sq c0, hc0sq, one_mul]
    set k1 := O ((k : ZMod (p * q)) ^ 2) with hk1
    have hkq : (e (k : ZMod (p * q))).2 ≠ 0 := by
      intro h0
      have h1 : (e ((k : ZMod (p * q)) * ((k⁻¹ : (ZMod (p * q))ˣ) : ZMod (p * q)))).2 = 1 := by
        rw [Units.mul_inv, map_one]; rfl
      rw [map_mul, Prod.snd_mul, h0, zero_mul] at h1
      exact zero_ne_one h1
    have hk1sq : ((e k1).2) ^ 2 = ((e (k : ZMod (p * q))).2) ^ 2 := by
      have := congrArg (fun x => (e x).2) (hO k hkQ)
      simpa [map_pow, Prod.pow_snd] using this
    simp only [good, hsq, ← hk1]
    have hck : e ((c * k : (ZMod (p * q))ˣ) : ZMod (p * q)) =
        ((e (k : ZMod (p * q))).1, -(e (k : ZMod (p * q))).2) := by
      push_cast
      rw [map_mul, hec]
      ext <;> simp
    rw [map_sub, map_sub, hck]
    simp only [Prod.fst_sub, Prod.snd_sub]
    rcases sq_eq_sq_iff_eq_or_eq_neg.1 hk1sq with h | h
    · -- `k₁ ≡ k (mod q)`
      have hA : -(e (k : ZMod (p * q))).2 - (e k1).2 ≠ 0 := by
        rw [h, show -(e (k : ZMod (p * q))).2 - (e (k : ZMod (p * q))).2 =
          -(2 * (e (k : ZMod (p * q))).2) by ring, neg_ne_zero]
        exact mul_ne_zero htwo hkq
      have hB : (e (k : ZMod (p * q))).2 - (e k1).2 = 0 := by rw [h, sub_self]
      simp only [hA, hB, not_true, not_false_eq_true, and_true, and_false, or_false,
        false_or, true_and, false_and]
      tauto
    · -- `k₁ ≡ -k (mod q)`
      have hA : -(e (k : ZMod (p * q))).2 - (e k1).2 = 0 := by
        rw [h, sub_neg_eq_add, neg_add_cancel]
      have hB : (e (k : ZMod (p * q))).2 - (e k1).2 ≠ 0 := by
        rw [h, sub_neg_eq_add, ← two_mul]
        exact mul_ne_zero htwo hkq
      simp only [hA, hB, not_true, not_false_eq_true, and_true, and_false, or_false,
        false_or, true_and, false_and]
  -- counting
  have hcc : ∀ k : (ZMod (p * q))ˣ, c * (c * k) = k := by
    intro k
    rw [← mul_assoc]
    have : c * c = 1 := Units.ext hc0sq
    rw [this, one_mul]
  set S := Finset.univ.filter fun k : (ZMod (p * q))ˣ => (k : ZMod (p * q)) ^ 2 ∈ Q with hS
  have hcard : (S.filter good).card = (S.filter fun k => ¬ good k).card := by
    refine Finset.card_bij' (fun k _ => c * k) (fun k _ => c * k) ?_ ?_ ?_ ?_
    · intro k hk
      simp only [hS, Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
      exact ⟨by rw [hsq']; exact hk.1, fun h => ((hflip k hk.1).1 h) hk.2⟩
    · intro k hk
      simp only [hS, Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
      exact ⟨by rw [hsq']; exact hk.1, (hflip k hk.1).2 hk.2⟩
    · intro k _; exact hcc k
    · intro k _; exact hcc k
  have htot := Finset.card_filter_add_card_filter_not (s := S) good
  rw [← htot, ← hcard, two_mul, Finset.filter_filter]
  congr 1 <;> exact congrArg _ (Finset.filter_congr fun k _ => and_congr_right fun _ => hgood k)

/-- **A square-root oracle factors `p q` on exactly half of the units** (Rabin, MIT/LCS/TR-212,
1979, Section 4, Theorem 1 and its proof, equation (6)). Let `p ≠ q` be primes with `q` odd and let
`O` be any function with `O(k²)² = k²` for every unit `k` modulo `p q` (a deterministic algorithm
that returns one square root of each unit square). Then exactly half of the units `k` satisfy
`gcd(k - O(k²), p q) ∈ {p, q}`, that is, the trial "draw `k`, compute `gcd(k - O(k²), n)`"
factors `n` with probability exactly `1/2`. Rabin states the probability `1/2` for `n` a product
of two (large) primes; here only `q` needs to be odd. -/
theorem two_mul_card_gcd_mem_eq_totient [hp : Fact p.Prime] [hq : Fact q.Prime] (hpq : p ≠ q)
    (hq2 : q ≠ 2) (O : ZMod (p * q) → ZMod (p * q))
    (hO : ∀ k : (ZMod (p * q))ˣ, O ((k : ZMod (p * q)) ^ 2) ^ 2 = (k : ZMod (p * q)) ^ 2) :
    2 * (Finset.univ.filter fun k : (ZMod (p * q))ˣ =>
        Nat.gcd ((k : ZMod (p * q)) - O ((k : ZMod (p * q)) ^ 2)).val (p * q) ∈
          ({p, q} : Finset ℕ)).card = Nat.totient (p * q) := by
  classical
  have h := two_mul_card_gcd_mem_eq_card hpq hq2 Set.univ O (fun k _ => hO k)
  simp only [Set.mem_univ, true_and, Finset.filter_true_of_mem fun _ _ => trivial,
    Finset.card_univ, ZMod.card_units_eq_totient] at h
  convert h using 2

end Factoring

end Cslib.Crypto.PublicKey.Rabin

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module
public import Mathlib.FieldTheory.Finite.Basic
public import MathlibExt.NumberTheory.WieferichPrime
import MathlibExt.NumberTheory.WilsonPrimePow
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Data.Nat.Choose.Dvd
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Prime.Factorial
import Mathlib.NumberTheory.Multiplicity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
@[expose] public section

/-!
# Fermat quotient

This module defines the integer-valued Fermat quotient `q_p(a)` for a
prime modulus `p` and integer `a` coprime to `p`, and proves its classical
congruences modulo `p`.

## Main statements

* `Int.fermatQuotient_mul_modEq`: `q_p(ab) ≡ q_p(a) + q_p(b) (mod p)`.
* `Int.fermatQuotient_add_mul_modEq`: `q_p(a + pt) ≡ q_p(a) - ā t (mod p)`, where
  `a ā ≡ 1 (mod p)`.
* `Int.natCast_mul_fermatQuotient_eq_sum`: Lerch's formula
  `a q_p(a) = (a ^ p - a) / p ≡ ∑_{j=1}^{p-1} j⁻¹ ⌊a j / p⌋ (mod p)`.
* `Int.fermatQuotient_two_eq_sum`: `q_p(2) ≡ ∑_{j=1}^{p-1} (-1) ^ (j + 1) / (2 j) (mod p)`.
* `Int.two_pow_modEq_one_sq_iff_dvd_num_alternating`: `2 ^ (p - 1) ≡ 1 (mod p ^ 2)` iff `p`
  divides the numerator of `1 - 1/2 + 1/3 - ⋯ - 1/(p - 1)`.
* `Nat.isWieferichPrime_iff_dvd_num_alternating`: the same criterion for Wieferich primes.
-/

namespace Int

/-- Fermat quotient `q_p(a) = (a ^ (p - 1) - 1) / p` for prime `p` and `a`
coprime to `p`. Integrality follows from `Int.prime_dvd_pow_sub_one`.
Proof arguments `_hp` and `_ha` are retained to enforce the domain
restriction to prime moduli and coprime integers, though the computed
value is independent of witnesses. -/
@[nolint unusedArguments]
def fermatQuotient (p : ℕ) (_hp : Nat.Prime p) (a : ℤ)
    (_ha : IsCoprime a (p : ℤ)) : ℤ :=
  (a ^ (p - 1) - 1) / (p : ℤ)

/-- Evaluation formula for the Fermat quotient. -/
theorem fermatQuotient_eq (p : ℕ) (hp : Nat.Prime p) (a : ℤ)
    (ha : IsCoprime a (p : ℤ)) :
    fermatQuotient p hp a ha = (a ^ (p - 1) - 1) / (p : ℤ) :=
  rfl

/-- Exact recovery: `p * q_p(a) = a ^ (p - 1) - 1`. -/
theorem natCast_mul_fermatQuotient (p : ℕ) (hp : Nat.Prime p) (a : ℤ)
    (ha : IsCoprime a (p : ℤ)) :
    (p : ℤ) * fermatQuotient p hp a ha = a ^ (p - 1) - 1 := by
  unfold fermatQuotient
  exact Int.mul_ediv_cancel' (Int.prime_dvd_pow_sub_one hp ha)

/-- The Fermat quotient is a logarithm modulo `p`: `q_p(ab) ≡ q_p(a) + q_p(b) (mod p)`. -/
theorem fermatQuotient_mul_modEq (p : ℕ) (hp : Nat.Prime p) {a b : ℤ}
    (ha : IsCoprime a (p : ℤ)) (hb : IsCoprime b (p : ℤ)) :
    fermatQuotient p hp (a * b) (ha.mul_left hb) ≡
      fermatQuotient p hp a ha + fermatQuotient p hp b hb [ZMOD (p : ℤ)] := by
  have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hab := natCast_mul_fermatQuotient p hp (a * b) (ha.mul_left hb)
  have hu := natCast_mul_fermatQuotient p hp a ha
  have hv := natCast_mul_fermatQuotient p hp b hb
  set w := fermatQuotient p hp (a * b) (ha.mul_left hb)
  set u := fermatQuotient p hp a ha
  set v := fermatQuotient p hp b hb
  have hw : w = u + v + p * u * v := by
    apply mul_left_cancel₀ hp0
    rw [hab, mul_pow]
    linear_combination -(b ^ (p - 1)) * hu - (1 + (p : ℤ) * u) * hv
  rw [hw]
  exact (Int.modEq_iff_dvd.mpr ⟨-(u * v), by ring⟩)

/-- `q_p(a + p t) ≡ q_p(a) - ā t (mod p)`, where `ā` is an inverse of `a` modulo `p`. -/
theorem fermatQuotient_add_mul_modEq (p : ℕ) (hp : Nat.Prime p) {a ā : ℤ} (t : ℤ)
    (ha : IsCoprime a (p : ℤ)) (hat : IsCoprime (a + p * t) (p : ℤ))
    (hā : a * ā ≡ 1 [ZMOD p]) :
    fermatQuotient p hp (a + p * t) hat ≡ fermatQuotient p hp a ha - ā * t [ZMOD p] := by
  obtain ⟨k, hk⟩ := hā.dvd
  have hu := natCast_mul_fermatQuotient p hp a ha
  have hv := natCast_mul_fermatQuotient p hp (a + p * t) hat
  set u := fermatQuotient p hp a ha
  set v := fermatQuotient p hp (a + p * t) hat
  have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
  obtain ⟨m, rfl⟩ : ∃ m, p = m + 2 := ⟨p - 2, by have := hp.two_le; omega⟩
  simp only [show m + 2 - 1 = m + 1 by omega] at hu hv
  obtain ⟨w, hw⟩ := sq_dvd_add_pow_sub_sub (((m + 2 : ℕ) : ℤ) * t) a (m + 1)
  simp only [Nat.add_sub_cancel] at hw
  refine ((Int.modEq_iff_dvd).2 ⟨-a ^ m * t - t ^ 2 * w + t * a ^ m * k + t * ā * u, ?_⟩)
  apply mul_left_cancel₀ hp0
  push_cast at hu hv hw hk ⊢
  linear_combination (1 - ((m : ℤ) + 2) * t * ā) * hu - hv - hw +
    ((m : ℤ) + 2) * t * a ^ m * hk

/-- For `p` prime and `a` a unit mod `p`, `a j mod p` lies in `[1, p - 1]` whenever `j` does. -/
private theorem mul_mod_mem_Icc_one_sub_one {p : ℕ} [Fact p.Prime] {a j : ℕ}
    (ha : (a : ZMod p) ≠ 0) (hj : j ∈ Finset.Icc 1 (p - 1)) :
    a * j % p ∈ Finset.Icc 1 (p - 1) := by
  have hp : p.Prime := Fact.out
  rw [Finset.mem_Icc] at hj ⊢
  have hjZ : (j : ZMod p) ≠ 0 := by
    intro h
    rw [ZMod.natCast_eq_zero_iff] at h
    have := Nat.le_of_dvd (by omega) h
    omega
  refine ⟨?_, ?_⟩
  · by_contra h0
    have h0' : a * j % p = 0 := by omega
    have hc : ((a * j : ℕ) : ZMod p) = 0 := by
      rw [ZMod.natCast_eq_zero_iff]; exact Nat.dvd_of_mod_eq_zero h0'
    push_cast at hc
    exact mul_ne_zero ha hjZ hc
  · have := Nat.mod_lt (a * j) hp.pos
    omega

/-- For `p` prime and `a` a unit mod `p`, `j ↦ a j mod p` permutes `Icc 1 (p - 1)`. -/
private theorem sum_Icc_mul_mod_eq {M : Type*} [AddCommMonoid M] {p : ℕ} [Fact p.Prime]
    {a : ℕ} (ha : (a : ZMod p) ≠ 0) (f : ℕ → M) :
    ∑ j ∈ Finset.Icc 1 (p - 1), f (a * j % p) = ∑ j ∈ Finset.Icc 1 (p - 1), f j := by
  have hp : p.Prime := Fact.out
  set b : ℕ := ((a : ZMod p)⁻¹).val with hb
  have hbZ : ((b : ℕ) : ZMod p) = (a : ZMod p)⁻¹ := ZMod.natCast_zmod_val _
  have key : ∀ m n : ℕ, m < p → n < p → (m : ZMod p) = n → m = n := by
    intro m n hm hn h
    rw [ZMod.natCast_eq_natCast_iff'] at h
    rwa [Nat.mod_eq_of_lt hm, Nat.mod_eq_of_lt hn] at h
  apply Finset.sum_nbij' (fun j => a * j % p) (fun j => b * j % p)
  · intro j hj
    exact mul_mod_mem_Icc_one_sub_one ha hj
  · intro j hj
    exact mul_mod_mem_Icc_one_sub_one (by rw [hbZ]; exact inv_ne_zero ha) hj
  · intro j hj
    simp only [Finset.mem_Icc] at hj
    apply key _ _ (Nat.mod_lt _ hp.pos) (by omega)
    simp only [ZMod.natCast_mod, Nat.cast_mul, hbZ]
    rw [← mul_assoc, inv_mul_cancel₀ ha, one_mul]
  · intro j hj
    simp only [Finset.mem_Icc] at hj
    apply key _ _ (Nat.mod_lt _ hp.pos) (by omega)
    simp only [ZMod.natCast_mod, Nat.cast_mul, hbZ]
    rw [← mul_assoc, mul_inv_cancel₀ ha, one_mul]
  · intro j _
    rfl

/-- **Lerch's formula**: for a prime `p` and a natural number `a` prime to `p`,
`a q_p(a) = (a ^ p - a) / p ≡ ∑_{j=1}^{p-1} j⁻¹ ⌊a j / p⌋ (mod p)`. -/
theorem natCast_mul_fermatQuotient_eq_sum (p : ℕ) [hp : Fact p.Prime] {a : ℕ}
    (ha : IsCoprime (a : ℤ) (p : ℤ)) :
    (a : ZMod p) * (fermatQuotient p hp.out a ha : ZMod p) =
      ∑ j ∈ Finset.Icc 1 (p - 1), ((j : ℕ) : ZMod p)⁻¹ * ((a * j / p : ℕ) : ZMod p) := by
  have hpp : p.Prime := hp.out
  have hp2 := hpp.two_le
  set F : ℕ → ZMod p := fun n => (((((n : ℤ) ^ (p - 1) - 1) / p : ℤ)) : ZMod p) with hF
  have hne : ∀ n : ℕ, 1 ≤ n → n ≤ p - 1 → ((n : ℕ) : ZMod p) ≠ 0 := by
    intro n h1 h2 h
    rw [ZMod.natCast_eq_zero_iff] at h
    have := Nat.le_of_dvd (by omega) h
    omega
  have hcopN : ∀ n : ℕ, (n : ZMod p) ≠ 0 → IsCoprime (n : ℤ) (p : ℤ) := by
    intro n hn
    rw [Int.isCoprime_iff_gcd_eq_one, Int.gcd_natCast_natCast]
    refine Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hpp).mpr fun h => hn ?_)
    rwa [ZMod.natCast_eq_zero_iff]
  have haZ : ((a : ℕ) : ZMod p) ≠ 0 := by
    intro h
    have h' : ((a : ℤ) : ZMod p) = 0 := by exact_mod_cast h
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h'
    exact hpp.one_lt.ne'
      (Nat.isUnit_iff.mp (Int.ofNat_isUnit.mp (ha.symm.isUnit_of_dvd' dvd_rfl h')))
  have hr : ∀ j ∈ Finset.Icc 1 (p - 1), 1 ≤ a * j % p ∧ a * j % p ≤ p - 1 := fun j hj =>
    Finset.mem_Icc.mp (mul_mod_mem_Icc_one_sub_one haZ hj)
  have h1 : ∀ j ∈ Finset.Icc 1 (p - 1), F (a * j) = F a + F j := by
    intro j hj
    rw [Finset.mem_Icc] at hj
    have hj' := hcopN j (hne j hj.1 hj.2)
    have := (ZMod.intCast_eq_intCast_iff _ _ p).mpr (fermatQuotient_mul_modEq p hpp ha hj')
    unfold fermatQuotient at this
    simp only [hF]
    push_cast at this ⊢
    exact this
  have h2 : ∀ j ∈ Finset.Icc 1 (p - 1), F (a * j) =
      F (a * j % p) - ((a * j % p : ℕ) : ZMod p)⁻¹ * ((a * j / p : ℕ) : ZMod p) := by
    intro j hj
    obtain ⟨hr1, hr2⟩ := hr j hj
    set r := a * j % p with hrdef
    set q := a * j / p with hqdef
    have hrq : r + p * q = a * j := Nat.mod_add_div _ _
    have hrZ := hne r hr1 hr2
    set ā : ℕ := ((r : ZMod p)⁻¹).val with hā
    have hāZ : ((ā : ℕ) : ZMod p) = (r : ZMod p)⁻¹ := ZMod.natCast_zmod_val _
    have hinv : (r : ℤ) * (ā : ℤ) ≡ 1 [ZMOD p] := by
      apply (ZMod.intCast_eq_intCast_iff _ _ p).mp
      push_cast
      rw [hāZ, mul_inv_cancel₀ hrZ]
    have hcopR := hcopN r hrZ
    have hcopRQ : IsCoprime ((r : ℤ) + p * q) (p : ℤ) := by
      have : (((r + p * q : ℕ) : ℤ) : ZMod p) ≠ 0 := by
        push_cast
        rw [ZMod.natCast_self, zero_mul, add_zero]
        exact_mod_cast hrZ
      have h' := hcopN (r + p * q) (by exact_mod_cast this)
      push_cast at h'
      exact h'
    have := fermatQuotient_add_mul_modEq p hpp q hcopR hcopRQ hinv
    have := (ZMod.intCast_eq_intCast_iff _ _ p).mpr this
    simp only [hF, ← hrq]
    unfold fermatQuotient at this
    push_cast at this ⊢
    rw [this, hāZ]
  have h3 := sum_Icc_mul_mod_eq haZ F
  have hsum1 : ∑ j ∈ Finset.Icc 1 (p - 1), F (a * j) =
      -F a + ∑ j ∈ Finset.Icc 1 (p - 1), F j := by
    rw [Finset.sum_congr rfl h1, Finset.sum_add_distrib, Finset.sum_const, Nat.card_Icc,
      nsmul_eq_mul]
    congr 1
    rw [show p - 1 + 1 - 1 = p - 1 by omega, Nat.cast_sub (by omega), ZMod.natCast_self]
    ring
  have hsum2 : ∑ j ∈ Finset.Icc 1 (p - 1), F (a * j) =
      ∑ j ∈ Finset.Icc 1 (p - 1), F j - ∑ j ∈ Finset.Icc 1 (p - 1),
        ((a : ZMod p) * (j : ZMod p))⁻¹ * ((a * j / p : ℕ) : ZMod p) := by
    rw [Finset.sum_congr rfl h2, Finset.sum_sub_distrib, h3]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [ZMod.natCast_mod]
    push_cast
    rfl
  have hFa : F a = ∑ j ∈ Finset.Icc 1 (p - 1),
      ((a : ZMod p) * (j : ZMod p))⁻¹ * ((a * j / p : ℕ) : ZMod p) := by
    linear_combination hsum1 - hsum2
  change (a : ZMod p) * F a = _
  rw [hFa, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [mul_inv, ← mul_assoc, ← mul_assoc, mul_inv_cancel₀ haZ, one_mul]

/-- For an odd prime `p`, `q_p(2) ≡ ∑_{j=1}^{p-1} (-1) ^ (j + 1) / (2 j) (mod p)`. -/
theorem fermatQuotient_two_eq_sum (p : ℕ) [hp : Fact p.Prime] (h2 : IsCoprime (2 : ℤ) (p : ℤ)) :
    (fermatQuotient p hp.out 2 h2 : ZMod p) =
      ∑ j ∈ Finset.Icc 1 (p - 1), (-1 : ZMod p) ^ (j + 1) / (2 * (j : ZMod p)) := by
  have hpp : p.Prime := hp.out
  have hp2 : 2 ≤ p := hpp.two_le
  have h2ne : (2 : ZMod p) ≠ 0 := by
    intro h
    have h' : (((2 : ℤ)) : ZMod p) = 0 := by exact_mod_cast h
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h'
    exact hpp.one_lt.ne'
      (Nat.isUnit_iff.mp (Int.ofNat_isUnit.mp (h2.isUnit_of_dvd' h' dvd_rfl)))
  set c : ℕ → ℕ := fun j => p.choose j / p with hc
  have hcp : ∀ j ∈ Finset.Icc 1 (p - 1), p * c j = p.choose j := by
    intro j hj
    rw [Finset.mem_Icc] at hj
    exact Nat.mul_div_cancel' (hpp.dvd_choose_self (by omega) (by omega))
  have hQ := natCast_mul_fermatQuotient p hpp 2 h2
  set Q := fermatQuotient p hpp 2 h2
  have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast hpp.ne_zero
  have hbin : ((2 : ℤ) ^ p - 2) = ∑ j ∈ Finset.Icc 1 (p - 1), ((p.choose j : ℕ) : ℤ) := by
    have h := Nat.sum_range_choose p
    rw [Finset.sum_range_succ, Finset.range_eq_Ico,
      Finset.sum_eq_sum_Ico_succ_bot (by omega), zero_add] at h
    have hI : Finset.Icc 1 (p - 1) = Finset.Ico 1 p := by
      ext x; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega
    rw [hI]
    have h' : ((∑ k ∈ Finset.Ico 1 p, p.choose k : ℕ) : ℤ) = 2 ^ p - 2 := by
      have : (((p.choose 0 + ∑ k ∈ Finset.Ico 1 p, p.choose k) + p.choose p : ℕ) : ℤ)
          = ((2 ^ p : ℕ) : ℤ) := by rw [h]
      push_cast at this
      simp only [Nat.choose_zero_right, Nat.choose_self, Nat.cast_one] at this
      push_cast
      linarith
    rw [← h']
    push_cast
    rfl
  have h2Q : 2 * Q = ∑ j ∈ Finset.Icc 1 (p - 1), ((c j : ℕ) : ℤ) := by
    apply mul_left_cancel₀ hp0
    rw [Finset.mul_sum]
    rw [Finset.sum_congr rfl (fun j hj => by
      exact_mod_cast hcp j hj : ∀ j ∈ Finset.Icc 1 (p - 1),
        (p : ℤ) * ((c j : ℕ) : ℤ) = ((p.choose j : ℕ) : ℤ)), ← hbin]
    have hpow : (2 : ℤ) ^ p = 2 * 2 ^ (p - 1) := by
      rw [← pow_succ']; congr 1; omega
    rw [hpow]
    linear_combination 2 * hQ
  have hcj : ∀ j ∈ Finset.Icc 1 (p - 1),
      ((c j : ℕ) : ZMod p) = (-1) ^ (j + 1) / (j : ZMod p) := by
    intro j hj
    have hj' := Finset.mem_Icc.mp hj
    have hjne : (j : ZMod p) ≠ 0 := by
      rw [Ne, ZMod.natCast_eq_zero_iff]
      intro h
      have := Nat.le_of_dvd (by omega) h
      omega
    have hN : c j * j.factorial * (p - j).factorial = (p - 1).factorial := by
      apply Nat.eq_of_mul_eq_mul_left hpp.pos
      rw [← mul_assoc, ← mul_assoc, hcp j hj, Nat.choose_mul_factorial_mul_factorial (by omega),
        Nat.mul_factorial_pred hpp.ne_zero]
    rw [← Nat.mul_factorial_pred (show j ≠ 0 by omega)] at hN
    have hNz : ((c j * (j * (j - 1).factorial) * (p - j).factorial : ℕ) : ZMod p)
        = (((p - 1).factorial : ℕ) : ZMod p) := by rw [hN]
    rw [ZMod.wilsons_lemma] at hNz
    have h54 := ZMod.factorial_sub_mul_factorial_pred p hj'.1 hj'.2
    push_cast at h54 hNz
    rw [eq_div_iff hjne]
    have h2 : ((-1 : ZMod p)) ^ j * (-1) ^ j = 1 := by rw [← mul_pow]; simp
    linear_combination (-1 : ZMod p) ^ j * hNz - ((c j : ℕ) : ZMod p) * j * h2
      - ((c j : ℕ) : ZMod p) * j * (-1) ^ j * h54
  have hZ : (2 : ZMod p) * (Q : ZMod p) = ∑ j ∈ Finset.Icc 1 (p - 1), ((c j : ℕ) : ZMod p) := by
    have := congrArg (fun z : ℤ => (z : ZMod p)) h2Q
    push_cast at this
    exact this
  rw [Finset.sum_congr rfl hcj] at hZ
  have hR : ∑ j ∈ Finset.Icc 1 (p - 1), (-1 : ZMod p) ^ (j + 1) / (2 * (j : ZMod p))
      = 2⁻¹ * ∑ j ∈ Finset.Icc 1 (p - 1), (-1 : ZMod p) ^ (j + 1) / (j : ZMod p) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [div_eq_mul_inv, div_eq_mul_inv, mul_inv]
    ring
  rw [hR, ← hZ, ← mul_assoc, inv_mul_cancel₀ h2ne, one_mul]

/-- For an odd prime `p`, `2 ^ (p - 1) ≡ 1 (mod p ^ 2)` if and only if `p` divides the numerator
(in lowest terms) of the alternating harmonic sum `1 - 1/2 + 1/3 - ⋯ - 1/(p - 1)`. -/
theorem two_pow_modEq_one_sq_iff_dvd_num_alternating (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) :
    (2 : ℤ) ^ (p - 1) ≡ 1 [ZMOD (p : ℤ) ^ 2] ↔
      (p : ℤ) ∣ (∑ j ∈ Finset.Icc 1 (p - 1), ((-1 : ℚ) ^ (j + 1) / (j : ℚ))).num := by
  have : Fact p.Prime := ⟨hp⟩
  have h2cop : IsCoprime (2 : ℤ) (p : ℤ) := by
    rw [Int.isCoprime_iff_gcd_eq_one]
    have : Nat.Coprime 2 p :=
      (Nat.coprime_primes Nat.prime_two hp).mpr (Ne.symm hp2)
    exact_mod_cast this
  have h5a := fermatQuotient_two_eq_sum p h2cop
  set D : ℕ := (p - 1).factorial with hD
  set N : ℤ := ∑ j ∈ Finset.Icc 1 (p - 1), (-1 : ℤ) ^ (j + 1) * ((D / j : ℕ) : ℤ) with hN
  set H : ℚ := ∑ j ∈ Finset.Icc 1 (p - 1), ((-1 : ℚ) ^ (j + 1) / (j : ℚ)) with hH
  set S : ZMod p := ∑ j ∈ Finset.Icc 1 (p - 1), (-1 : ZMod p) ^ (j + 1) / (j : ZMod p) with hS
  have hjD : ∀ j ∈ Finset.Icc 1 (p - 1), j * (D / j) = D := by
    intro j hj
    rw [Finset.mem_Icc] at hj
    exact Nat.mul_div_cancel' (Nat.dvd_factorial hj.1 hj.2)
  have hjne : ∀ j ∈ Finset.Icc 1 (p - 1), (j : ZMod p) ≠ 0 := by
    intro j hj
    rw [Finset.mem_Icc] at hj
    rw [Ne, ZMod.natCast_eq_zero_iff]
    intro h
    have := Nat.le_of_dvd (by omega) h
    have := hp.two_le
    omega
  have hDne : (D : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff, hD, hp.dvd_factorial]
    have := hp.two_le
    omega
  have hDpos : (0 : ℚ) < D := by positivity
  have hHD : H * D = N := by
    rw [hH, hN, Finset.sum_mul]
    simp only [Int.cast_sum, Int.cast_mul, Int.cast_pow, Int.cast_neg, Int.cast_one,
      Int.cast_natCast]
    refine Finset.sum_congr rfl fun j hj => ?_
    have h1 := hjD j hj
    have hj0 : (j : ℚ) ≠ 0 := by
      rw [Finset.mem_Icc] at hj; exact_mod_cast (show j ≠ 0 by omega)
    have : ((D / j : ℕ) : ℚ) = (D : ℚ) / j := by
      rw [eq_div_iff hj0, mul_comm]; exact_mod_cast h1
    rw [this]; field_simp
  have hNS : (N : ZMod p) = S * D := by
    rw [hN, hS, Finset.sum_mul]
    simp only [Int.cast_sum, Int.cast_mul, Int.cast_pow, Int.cast_neg, Int.cast_one,
      Int.cast_natCast]
    refine Finset.sum_congr rfl fun j hj => ?_
    have h1 := hjD j hj
    have : ((D / j : ℕ) : ZMod p) = (D : ZMod p) / j := by
      rw [eq_div_iff (hjne j hj), mul_comm, ← Nat.cast_mul, h1]
    rw [this]; ring
  have hHeq : H = Rat.divInt N D := by
    rw [Rat.divInt_eq_div]; push_cast; rw [← hHD]; field_simp
  have hden : (H.den : ℤ) ∣ D := by
    rw [hHeq]; exact Rat.den_dvd N D
  have hpden : ¬ (p : ℤ) ∣ H.den := by
    intro h
    have h2 := h.trans hden
    have h3 : p ∣ D := by exact_mod_cast h2
    apply hDne
    rwa [ZMod.natCast_eq_zero_iff]
  have hcross : N * H.den = H.num * D := by
    have h1 := Rat.num_div_den H
    have : (N : ℚ) * H.den = H.num * D := by
      rw [← hHD]; nth_rewrite 1 [← h1]; field_simp
    exact_mod_cast this
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hpD : ¬ (p : ℤ) ∣ (D : ℤ) := by
    intro h
    apply hDne
    rw [ZMod.natCast_eq_zero_iff]; exact_mod_cast h
  have hnumN : (p : ℤ) ∣ H.num ↔ (p : ℤ) ∣ N := by
    constructor
    · intro h
      have : (p : ℤ) ∣ N * H.den := hcross ▸ h.mul_right _
      exact (hpZ.dvd_or_dvd this).resolve_right hpden
    · intro h
      have : (p : ℤ) ∣ H.num * D := hcross ▸ h.mul_right _
      exact (hpZ.dvd_or_dvd this).resolve_right hpD
  have hNS0 : (p : ℤ) ∣ N ↔ S = 0 := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, hNS, mul_eq_zero, or_iff_left hDne]
  have h2ne : (2 : ZMod p) ≠ 0 := by
    intro h
    have : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
    rw [ZMod.natCast_eq_zero_iff] at this
    have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp this
    exact hp2 this
  have hsum : ∑ j ∈ Finset.Icc 1 (p - 1), (-1 : ZMod p) ^ (j + 1) / (2 * (j : ZMod p)) =
      S / 2 := by
    rw [hS, Finset.sum_div]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [mul_comm, div_div]
  have hk := natCast_mul_fermatQuotient p hp 2 h2cop
  set k := fermatQuotient p hp 2 h2cop
  have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
  rw [hsum] at h5a
  rw [hnumN, hNS0, Int.modEq_comm, Int.modEq_iff_dvd, ← hk, pow_two,
    mul_dvd_mul_iff_left hp0, ← ZMod.intCast_zmod_eq_zero_iff_dvd, h5a, div_eq_zero_iff,
    or_iff_left h2ne]

end Int

namespace Nat

/-- An odd prime `p` is a Wieferich prime (to base two) if and only if `p` divides the numerator
(in lowest terms) of the alternating harmonic sum `1 - 1/2 + 1/3 - ⋯ - 1/(p - 1)`. -/
theorem isWieferichPrime_iff_dvd_num_alternating {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    p.IsWieferichPrime ↔
      (p : ℤ) ∣ (∑ j ∈ Finset.Icc 1 (p - 1), ((-1 : ℚ) ^ (j + 1) / (j : ℚ))).num := by
  rw [isWieferichPrime_iff_modEq, and_iff_right hp,
    ← Int.two_pow_modEq_one_sq_iff_dvd_num_alternating p hp hp2, ← Int.natCast_modEq_iff]
  push_cast
  rfl

end Nat

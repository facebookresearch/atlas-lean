/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.NumberTheory.Bernoulli
public import MathlibExt.NumberTheory.RatResidue
import Mathlib.Algebra.Field.ZMod
import MathlibExt.NumberTheory.Bernoulli.SumModPrime
import MathlibExt.NumberTheory.Bernoulli.TruncatedSumModPrime

/-!
# A prime-scaled sum of Bernoulli numbers divided by complementary indices

For every odd prime `p`, the rational number `p * ∑ j ∈ range (p + 1), B_j / (p - j + 1)`
has denominator prime to `p` and residue `-1` modulo `p`.

Source: Levent Kargın and Merve Mutluer, *A New Expression for the Bernoulli
Numbers and Its Applications*, INTEGERS 26 (2026), Article A120, Corollary 4,
equation (26).
-/

namespace MetaMathlibExt

open Finset

namespace prime_mul_sum_bernoulli_div_mod_prime

-- Implementation note: `integral_bernoulli` adapts the private
-- `padicValuation_bernoulli_le_one` of `MathlibExt/NumberTheory/Bernoulli/SumModPrime.lean`
-- to the index `p - 1`, `den_ne_zero` is the denominator argument in the proof of
-- `sum_bernoulli_to_prime_sub_three_mod_prime` (`Bernoulli/TruncatedSumModPrime.lean`), and
-- `hres` below is the private `ratResidue_eq_ratCast` of `Bernoulli/SumModPrime.lean`.

private lemma integral_bernoulli (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2)
    (j : ℕ) (hj : j ≤ p) (hjp : j ≠ p - 1) :
    Rat.padicValuation p (bernoulli j) ≤ 1 := by
  by_cases hlt : j < p - 1
  · rw [bernoulli.eq_def, map_mul]
    exact mul_le_one' (by simp) (padicValuation_bernoulli'_le_one (p := p) j (by omega))
  · have heq : j = p := by omega
    rw [heq, bernoulli_eq_zero_of_odd ((Fact.out : p.Prime).odd_of_ne_two hp2)
      (Fact.out : p.Prime).one_lt]
    simp

private lemma den_ne_zero (p : ℕ) [Fact p.Prime] (x : ℚ)
    (hx : Rat.padicValuation p x ≤ 1) : (x.den : ZMod p) ≠ 0 :=
  mt (ZMod.natCast_eq_zero_iff _ _).mp (Rat.padicValuation_le_one_iff.mp hx)

private lemma cast_sum (p : ℕ) [Fact p.Prime] (s : Finset ℕ) (f : ℕ → ℚ)
    (hs : ∀ j ∈ s, Rat.padicValuation p (f j) ≤ 1) :
    ((∑ j ∈ s, f j : ℚ) : ZMod p) = ∑ j ∈ s, (f j : ZMod p) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    have hfa := hs a (mem_insert_self a s)
    have hfs : ∀ j ∈ s, Rat.padicValuation p (f j) ≤ 1 :=
      fun j hj => hs j (mem_insert_of_mem hj)
    rw [sum_insert ha, sum_insert ha,
      Rat.cast_add_of_ne_zero (den_ne_zero p _ hfa)
        (den_ne_zero p _ ((Rat.padicValuation p).map_sum_le hfs)), ih hfs]

end prime_mul_sum_bernoulli_div_mod_prime

open prime_mul_sum_bernoulli_div_mod_prime

@[expose] public section

/--
**The congruence $p\sum_{j=0}^{p} B_j/(p-j+1) \equiv -1 \pmod p$.** Let $B_j$ denote the
Bernoulli numbers with $B_1 = -\tfrac12$. For every odd prime $p$, the rational number
$$S = p \sum_{j=0}^{p} \frac{B_j}{p-j+1}$$
has denominator not divisible by $p$, and its residue modulo $p$ (its numerator times the
inverse of its denominator in $\mathbb{Z}/p\mathbb{Z}$) equals $-1$.

Source: Levent Kargın and Merve Mutluer, *A New Expression for the Bernoulli
Numbers and Its Applications*, INTEGERS 26 (2026), Article A120, Corollary 4,
equation (26).
-/
public theorem prime_mul_sum_bernoulli_div_mod_prime (p : ℕ)
    (hp : p.Prime) (hp2 : p ≠ 2) :
    ¬p ∣ ((p : ℚ) * ∑ j ∈ Finset.range (p + 1),
      bernoulli j / ((p - j + 1 : ℕ) : ℚ)).den ∧
      ratResidue p ((p : ℚ) * ∑ j ∈ Finset.range (p + 1),
        bernoulli j / ((p - j + 1 : ℕ) : ℚ)) = ratResidue p (-1)
    := by
  let : Fact p.Prime := ⟨hp⟩
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  have hres (x : ℚ) : ratResidue p x = (x : ZMod p) := by
    rw [Rat.cast_def, div_eq_mul_inv]
    rfl
  have hother (j : ℕ) (hj : j ∈ range (p + 1)) (hjp : j ≠ p - 1) :
      Rat.padicValuation p ((p : ℚ) * bernoulli j) ≤ 1 ∧
        (((p : ℚ) * bernoulli j : ℚ) : ZMod p) = 0 := by
    have hBj := integral_bernoulli p hp2 j (by simpa using hj) hjp
    refine ⟨?_, ?_⟩
    · rw [map_mul, Rat.padicValuation_natCast]
      exact mul_le_one' (Int.padicValuation_le_one _ _) hBj
    · rw [Rat.cast_mul_of_ne_zero (by simp) (den_ne_zero p _ hBj)]
      simp
  obtain ⟨hA, hAc⟩ := sum_prime_mul_bernoulli_mod_prime p hp hp2
  rw [hres, hres] at hAc
  let T := ∑ j ∈ (range (p + 1)).erase (p - 1), (p : ℚ) * bernoulli j
  have hT : Rat.padicValuation p T ≤ 1 :=
    (Rat.padicValuation p).map_sum_le fun j hj =>
      (hother j (mem_erase.mp hj).2 (mem_erase.mp hj).1).1
  have hTc : (T : ZMod p) = 0 := by
    rw [cast_sum p _ _ (fun j hj =>
      (hother j (mem_erase.mp hj).2 (mem_erase.mp hj).1).1)]
    exact sum_eq_zero fun j hj =>
      (hother j (mem_erase.mp hj).2 (mem_erase.mp hj).1).2
  have hsplit : ∑ j ∈ range (p + 1), (p : ℚ) * bernoulli j =
      (p : ℚ) * bernoulli (p - 1) + T :=
    (add_sum_erase _ _ (mem_range.mpr (by omega))).symm
  have hB : Rat.padicValuation p ((p : ℚ) * bernoulli (p - 1)) ≤ 1 := by
    rw [← add_sub_cancel_right ((p : ℚ) * bernoulli (p - 1)) T, ← hsplit]
    exact (Rat.padicValuation p).map_sub_le (Rat.padicValuation_le_one_iff.mpr hA) hT
  have hBc : (((p : ℚ) * bernoulli (p - 1) : ℚ) : ZMod p) = -1 := by
    rw [hsplit, Rat.cast_add_of_ne_zero (den_ne_zero p _ hB) (den_ne_zero p _ hT),
      hTc, add_zero] at hAc
    simpa using hAc
  have hnum (j : ℕ) (hj : j ∈ range (p + 1)) :
      Rat.padicValuation p ((p : ℚ) * bernoulli j) ≤ 1 := by
    by_cases hjp : j = p - 1
    · simpa [hjp] using hB
    · exact (hother j hj hjp).1
  have hden (j : ℕ) (hj : j ∈ range (p + 1)) (hj1 : j ≠ 1) :
      ¬p ∣ p - j + 1 := by
    by_cases hj0 : j = 0
    · rw [hj0, Nat.sub_zero, ← Nat.dvd_add_iff_right (dvd_refl p)]
      simpa only [Nat.dvd_one] using hp.ne_one
    · exact Nat.not_dvd_of_pos_of_lt (by omega) (by have := mem_range.mp hj; omega)
  let f (j : ℕ) : ℚ := (p : ℚ) * bernoulli j / ((p - j + 1 : ℕ) : ℚ)
  have hf1 : f 1 = bernoulli 1 := by
    dsimp [f]
    rw [Nat.sub_add_cancel hp.one_le]
    exact mul_div_cancel_left₀ _ (Nat.cast_ne_zero.mpr hp.ne_zero)
  have hf (j : ℕ) (hj : j ∈ range (p + 1)) : Rat.padicValuation p (f j) ≤ 1 := by
    by_cases hj1 : j = 1
    · rw [hj1, hf1]
      exact integral_bernoulli p hp2 1 (by omega) (by omega)
    · dsimp [f]
      have hunit : Int.padicValuation p ((p - j + 1 : ℕ) : ℤ) = 1 := by
        rw [Int.padicValuation_eq_one_iff, Int.natCast_dvd_natCast]
        exact hden j hj hj1
      rw [map_div₀, Rat.padicValuation_natCast, hunit, div_one]
      exact hnum j hj
  have hfc (j : ℕ) (hj : j ∈ range (p + 1)) (hj1 : j ≠ 1) :
      (f j : ZMod p) = (((p : ℚ) * bernoulli j : ℚ) : ZMod p) / (p - j + 1 : ℕ) := by
    dsimp [f]
    rw [Rat.cast_div_of_ne_zero (den_ne_zero p _ (hnum j hj)) (by
      simpa only [Rat.num_natCast, Int.cast_natCast, Ne, ZMod.natCast_eq_zero_iff]
        using hden j hj hj1), Rat.cast_natCast]
  have hf1c : (f 1 : ZMod p) = -1 / 2 := by
    rw [hf1, bernoulli_one]
    norm_num [Rat.cast_def]
  have hsum : ∑ j ∈ (range (p + 1)).erase 1, (f j : ZMod p) = -1 / 2 := by
    rw [sum_eq_single (p - 1)]
    · rw [hfc (p - 1) (mem_range.mpr (by omega)) (by omega), hBc]
      congr 1
      have heq : p - (p - 1) + 1 = 2 := by omega
      simp [heq]
    · intro j hj hjp
      rw [hfc j (mem_erase.mp hj).2 (mem_erase.mp hj).1,
        (hother j (mem_erase.mp hj).2 hjp).2, zero_div]
    · intro h
      exact (h (mem_erase.mpr ⟨by omega, mem_range.mpr (by omega)⟩)).elim
  rw [mul_sum]
  simp_rw [← mul_div_assoc]
  change ¬p ∣ (∑ j ∈ range (p + 1), f j).den ∧
    ratResidue p (∑ j ∈ range (p + 1), f j) = ratResidue p (-1)
  refine ⟨Rat.padicValuation_le_one_iff.mp ((Rat.padicValuation p).map_sum_le hf), ?_⟩
  rw [hres, hres, cast_sum p _ _ hf,
    ← add_sum_erase _ _ (mem_range.mpr (by omega) : 1 ∈ range (p + 1)), hf1c, hsum]
  have htwo : (2 : ZMod p) ≠ 0 := by
    change ((2 : ℕ) : ZMod p) ≠ 0
    rw [Ne, ZMod.natCast_eq_zero_iff]
    exact fun h => hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h)
  norm_num
  field_simp
  ring

end

end MetaMathlibExt

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.FieldTheory.ComplexPartialFractions
import Mathlib.Tactic.LinearCombination

/-! # Tests for `MathlibExt.FieldTheory.ComplexPartialFractions` -/

namespace MathlibExtTest.FieldTheory.ComplexPartialFractions

open scoped Polynomial RatFunc
open Polynomial MathlibExt.FieldTheory.ComplexPartialFractionsWanted

/-- The conclusion of `ratFunc_partial_fractions_complex` for `f`. -/
abbrev Decomposes (f : ℂ⟮X⟯) : Prop :=
  ∃ (q : ℂ[X]) (s : Finset ℂ[X]) (g : ℂ[X] → ℕ → ℂ[X]) (m : ℂ[X] → ℕ),
    (∀ p ∈ s, p.Monic ∧ p.natDegree = 1) ∧
      (∀ p ∈ s, ∀ k < m p, (g p k).natDegree < p.natDegree) ∧
      f = algebraMap ℂ[X] ℂ⟮X⟯ q + ∑ p ∈ s, ∑ k ∈ Finset.range (m p),
        algebraMap ℂ[X] ℂ⟮X⟯ (g p k) / algebraMap ℂ[X] ℂ⟮X⟯ p ^ (k + 1)

-- The theorem applies to `1 / (X ^ 2 + 1)`, to a polynomial and to `0`.
example : Decomposes (1 / algebraMap ℂ[X] ℂ⟮X⟯ (X ^ 2 + 1)) :=
  ratFunc_partial_fractions_complex _

example : Decomposes (algebraMap ℂ[X] ℂ⟮X⟯ (X ^ 3 - 2 * X)) :=
  ratFunc_partial_fractions_complex _

example : Decomposes 0 :=
  ratFunc_partial_fractions_complex 0

/-- A hand-made decomposition: `1 / (X ^ 2 + 1) = (i / 2) / (X + i) - (i / 2) / (X - i)`. -/
theorem one_div_X_sq_add_one :
    1 / algebraMap ℂ[X] ℂ⟮X⟯ (X ^ 2 + 1) =
      algebraMap ℂ[X] ℂ⟮X⟯ (C (Complex.I / 2)) / algebraMap ℂ[X] ℂ⟮X⟯ (X + C Complex.I) -
        algebraMap ℂ[X] ℂ⟮X⟯ (C (Complex.I / 2)) / algebraMap ℂ[X] ℂ⟮X⟯ (X - C Complex.I) := by
  have h₁ := RatFunc.algebraMap_ne_zero (X_add_C_ne_zero Complex.I)
  have h₂ := RatFunc.algebraMap_ne_zero (X_sub_C_ne_zero Complex.I)
  have h₃ : algebraMap ℂ[X] ℂ⟮X⟯ (X ^ 2 + 1) ≠ 0 := by
    rw [← C_1]
    exact RatFunc.algebraMap_ne_zero (X_pow_add_C_ne_zero two_pos 1)
  rw [div_sub_div _ _ h₁ h₂, div_eq_div_iff h₃ (mul_ne_zero h₁ h₂), one_mul, ← map_mul, ← map_mul,
    ← map_mul, ← map_sub, ← map_mul]
  congr 1
  have hI : C Complex.I ^ 2 = -1 := by rw [← C_pow, Complex.I_sq, C_neg, C_1]
  have hI₂ : 2 * C (Complex.I / 2) = C Complex.I := by
    rw [← map_ofNat C 2, ← C_mul, mul_div_cancel₀ _ two_ne_zero]
  linear_combination X ^ 2 * hI + C Complex.I * (X ^ 2 + 1) * hI₂

-- The same decomposition, as a witness of the shape of the theorem: the numerator over
-- `X - C a` is `C (-a / 2)`, that is, `C (p.coeff 0 / 2)` for `p = X - C a`.
example : Decomposes (1 / algebraMap ℂ[X] ℂ⟮X⟯ (X ^ 2 + 1)) := by
  classical
  have hne : X + C Complex.I ≠ X - C Complex.I := fun h => by
    have h₀ := congrArg (fun p : ℂ[X] => p.coeff 0) h
    norm_num [Complex.ext_iff] at h₀
  have hs : ∀ p ∈ ({X + C Complex.I, X - C Complex.I} : Finset ℂ[X]),
      p.Monic ∧ p.natDegree = 1 := by
    simp only [Finset.mem_insert, Finset.mem_singleton]
    rintro p (rfl | rfl)
    exacts [⟨monic_X_add_C _, natDegree_X_add_C _⟩, ⟨monic_X_sub_C _, natDegree_X_sub_C _⟩]
  refine ⟨0, {X + C Complex.I, X - C Complex.I}, fun p _ => C (p.coeff 0 / 2), fun _ => 1, hs,
    fun p hp _ _ => by simp [(hs p hp).2], ?_⟩
  rw [one_div_X_sq_add_one, Finset.sum_pair hne]
  simp only [Finset.sum_range_one, zero_add, pow_one, map_zero, coeff_add, coeff_sub,
    coeff_X_zero, coeff_C_zero, zero_sub, neg_div, map_neg]
  ring

-- A consequence: each denominator is a power of some `X - C a`, and each numerator is a
-- constant.
example (f : ℂ⟮X⟯) :
    ∃ (q : ℂ[X]) (s : Finset ℂ[X]) (g : ℂ[X] → ℕ → ℂ[X]) (m : ℂ[X] → ℕ),
      (∀ p ∈ s, ∃ a : ℂ, p = X - C a) ∧ (∀ p ∈ s, ∀ k < m p, ∃ c : ℂ, g p k = C c) ∧
        f = algebraMap ℂ[X] ℂ⟮X⟯ q + ∑ p ∈ s, ∑ k ∈ Finset.range (m p),
          algebraMap ℂ[X] ℂ⟮X⟯ (g p k) / algebraMap ℂ[X] ℂ⟮X⟯ p ^ (k + 1) := by
  obtain ⟨q, s, g, m, hs, hg, hf⟩ := ratFunc_partial_fractions_complex f
  refine ⟨q, s, g, m, fun p hp => ⟨-p.coeff 0, ?_⟩, fun p hp k hk => ⟨(g p k).coeff 0, ?_⟩, hf⟩
  · rw [C_neg, sub_neg_eq_add]
    exact (hs p hp).1.eq_X_add_C (hs p hp).2
  · apply eq_C_of_natDegree_eq_zero
    have h := hg p hp k hk
    rw [(hs p hp).2] at h
    omega

end MathlibExtTest.FieldTheory.ComplexPartialFractions

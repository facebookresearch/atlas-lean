/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Algebra.Field.Rat
import MathlibExt.NumberTheory.FunctionField.BFreeConvolution

/-! # Tests for Möbius convolution with the B-free indicator -/

open Polynomial UniqueFactorizationMonoid MetaMathlibExt

namespace MetaMathlibExt.monicDirichletConv_bFreeIndicator_moebius

private noncomputable def exponents (p : ℚ[X]) : ℕ :=
  open Classical in if p = X then 2 else 1

private theorem exponents_ne_zero (p : ℚ[X]) : exponents p ≠ 0 := by
  unfold exponents
  split <;> decide

private theorem free_one : IsBFree exponents 1 := by
  intro p _ hp hd
  exact hp.not_isUnit ((isUnit_pow_iff (exponents_ne_zero p)).mp (isUnit_of_dvd_one hd))

private theorem conv_prime {p : ℚ[X]} (hm : p.Monic) (hp : Irreducible p) :
    monicDirichletConv ({g : ℚ[X] | IsBFree exponents g}.indicator 1)
      (fun g => (moebius g : ℂ)) p = ({g : ℚ[X] | IsBFree exponents g}.indicator 1) p - 1 := by
  classical
  have hset : {d : ℚ[X] | d.Monic ∧ d ∣ p} = {1, p} := by
    ext d
    simp only [Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨hdm, ⟨e, he⟩⟩
      rcases hp.isUnit_or_isUnit he with hu | hu
      · exact Or.inl (hdm.isUnit_iff.mp hu)
      · have hem := hdm.of_mul_monic_left (he ▸ hm)
        exact Or.inr (by simpa [hem.isUnit_iff.mp hu] using he.symm)
    · rintro (rfl | rfl)
      · exact ⟨monic_one, one_dvd _⟩
      · exact ⟨hm, dvd_rfl⟩
  have h1 : (1 : ℚ[X]) ∉ ({p} : Set ℚ[X]) := by simpa using Ne.symm hp.ne_one
  have hq : p /ₘ p = 1 := by simpa using mul_divByMonic_cancel_left (1 : ℚ[X]) hm
  rw [monicDirichletConv, hset, finsum_mem_insert _ h1 (Set.finite_singleton p), finsum_mem_singleton]
  simp [divByMonic_one, hq, hp.moebius_eq, Set.indicator_of_mem
    (show (1 : ℚ[X]) ∈ {g : ℚ[X] | IsBFree exponents g} from free_one), sub_eq_add_neg, add_comm]

-- The unit has convolution value 1.
example : ∑ᶠ r ∈ {r : ℚ[X] | r.Monic ∧ kappaPow exponents r = 1}, (moebius r : ℂ) = 1 := by
  rw [← monicDirichletConv_bFreeIndicator_moebius exponents (fun p _ _ => exponents_ne_zero p)
    monic_one, monicDirichletConv_one]
  simp [Set.indicator_of_mem (show (1 : ℚ[X]) ∈ {g : ℚ[X] | IsBFree exponents g} from free_one)]

-- X is below its threshold of 2, so the two Möbius contributions cancel.
example : ∑ᶠ r ∈ {r : ℚ[X] | r.Monic ∧ kappaPow exponents r = X}, (moebius r : ℂ) = 0 := by
  classical
  have hfree : IsBFree exponents X := by
    intro p hm hp hd
    have hpx : p ∣ X := (dvd_pow_self _ (exponents_ne_zero p)).trans hd
    have he := eq_of_monic_of_dvd_of_natDegree_le hm monic_X hpx
      (natDegree_le_of_dvd (hp.dvd_symm irreducible_X hpx) hm.ne_zero)
    subst p
    have hdeg := natDegree_le_of_dvd hd X_ne_zero
    simp [exponents, natDegree_pow] at hdeg
  rw [← monicDirichletConv_bFreeIndicator_moebius exponents (fun p _ _ => exponents_ne_zero p)
    monic_X, conv_prime monic_X irreducible_X]
  simp [Set.indicator_of_mem (show (X : ℚ[X]) ∈ {g : ℚ[X] | IsBFree exponents g} from hfree)]

-- The other linear prime has threshold 1 and contributes its Möbius value -1.
example : ∑ᶠ r ∈ {r : ℚ[X] | r.Monic ∧ kappaPow exponents r = X - C 1}, (moebius r : ℂ) = -1 := by
  classical
  have hn : ¬ IsBFree exponents (X - C 1) := by
    intro h
    apply h _ (monic_X_sub_C 1) (irreducible_X_sub_C 1)
    simp [exponents]
  rw [← monicDirichletConv_bFreeIndicator_moebius exponents (fun p _ _ => exponents_ne_zero p)
    (monic_X_sub_C 1), conv_prime (monic_X_sub_C 1) (irreducible_X_sub_C 1)]
  rw [Set.indicator_of_notMem
    (show (X - C 1 : ℚ[X]) ∉ {g : ℚ[X] | IsBFree exponents g} from hn), zero_sub]

end MetaMathlibExt.monicDirichletConv_bFreeIndicator_moebius

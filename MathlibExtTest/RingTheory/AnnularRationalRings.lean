/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.RingTheory.AdicRationalRingModels
import Mathlib.Tactic.NormNum

/-! In the actual annular presentation Z[2/2], the integral ring remains
Z, where two is not a unit; inversion happens after the completion.
This fixture detects replacing the integral ring of definition by Z[1/2]. -/

open MathlibExt.RingTheory.AdicRationalRingModels

private noncomputable abbrev Definition := definitionAlgebra ℤ {(2 : ℤ)} 2
private abbrev PeriodIdeal : Ideal ℤ := Ideal.span {(2 : ℤ)}

private noncomputable def integralEquiv : ℤ ≃ₐ[ℤ] Definition := by
  classical
  apply AlgEquiv.ofBijective (Algebra.ofId ℤ Definition)
  constructor
  · intro a b h
    apply IsLocalization.injective (Localization.Away (2 : ℤ))
      (powers_le_nonZeroDivisors_of_noZeroDivisors (by decide : (2 : ℤ) ≠ 0))
    exact congrArg Subtype.val h
  · intro x
    have hx : (x : Localization.Away (2 : ℤ)) ∈
        (⊥ : Subalgebra ℤ (Localization.Away (2 : ℤ))) := by
      rw [← definitionAlgebra_singleton_denominator ℤ (2 : ℤ)]
      exact x.property
    obtain ⟨a, ha⟩ := Algebra.mem_bot.mp hx
    exact ⟨a, Subtype.ext ha⟩

example : IsAnnular ℤ PeriodIdeal {(2 : ℤ)} 2 := by
  constructor
  · exact ⟨1, by simp [PeriodIdeal]⟩
  · refine ⟨1, by decide, ?_⟩
    simp only [pow_one]
    exact Ideal.subset_span (Set.mem_singleton (2 : ℤ))

example : ¬ IsUnit (2 : Definition) := by
  intro h
  have h' := h.map integralEquiv.symm.toRingHom
  have h'' : IsUnit (2 : ℤ) := by simpa only [map_ofNat] using h'
  exact (by decide : ¬ IsUnit (2 : ℤ)) h''

example : IsUnit (coefficient ℤ PeriodIdeal {(2 : ℤ)} 2 2) :=
  coefficient_denominator ℤ PeriodIdeal {(2 : ℤ)} 2

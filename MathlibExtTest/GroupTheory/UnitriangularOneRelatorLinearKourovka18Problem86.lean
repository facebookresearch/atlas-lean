/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.GroupTheory.UnitriangularOneRelatorLinearKourovka18Problem86

open MathlibExt.GroupTheory.UnitriangularOneRelatorLinearKourovka18Problem86Wanted

-- The exponent of b distinguishes the two generators in the presented group.
private theorem distinct_generators :
    (PresentedGroup.of (0 : Fin 2) : OneRelatorGroup) ≠ PresentedGroup.of 1 := by
  let f : Fin 2 → Multiplicative ℤ := ![1, Multiplicative.ofAdd 1]
  have h : ∀ r ∈ ({relator} : Set (FreeGroup (Fin 2))), FreeGroup.lift f r = 1 := by
    rintro _ ⟨⟩
    simp [relator, f]
  intro heq
  have he := congrArg (PresentedGroup.toGroup h) heq
  change (0 : ℤ) = 1 at he
  exact zero_ne_one he

-- A faithful representation separates the generators even after passing to matrices.
example : ∃ (K : Type) (_ : Field K) (n : ℕ)
    (ρ : OneRelatorGroup →* Matrix.GeneralLinearGroup (Fin n) K),
    Function.Injective ρ ∧ ρ (PresentedGroup.of 0) ≠ ρ (PresentedGroup.of 1) := by
  obtain ⟨K, inst, n, ρ, hρ⟩ := oneRelatorGroupIsLinear_holds
  exact ⟨K, inst, n, ρ, hρ, hρ.ne distinct_generators⟩

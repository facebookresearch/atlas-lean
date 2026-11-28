/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import Mathlib.Algebra.Module.LinearMap.Basic

/-!
# Bijectivity through compatible linear retractions

Let R be a semiring and α : D → C, β : E → F R-linear maps. Suppose D and C retract from E and
F through i_D,r_D and i_C,r_C, and βi_D=i_Cα and αr_D=r_Cβ.

If β is bijective, then α is bijective. The two commuting squares and the retraction
identities give injectivity and surjectivity separately, without equality of the carrier
universes.
-/

@[expose] public section

namespace LinearMap

universe uR uD uE uC uF

variable {R : Type uR} [Semiring R]
  {D : Type uD} {E : Type uE} {C : Type uC} {F : Type uF}
  [AddCommMonoid D] [Module R D] [AddCommMonoid E] [Module R E]
  [AddCommMonoid C] [Module R C] [AddCommMonoid F] [Module R F]

/-- Let R be a semiring and D,E,C,F R-modules with additive commutative monoid carriers in
independent universes. Let α : D →ₗ[R] C, β : E →ₗ[R] F, and retractions r_Di_D=id_D,
r_Ci_C=id_C. If βi_D=i_Cα, αr_D=r_Cβ, and β is bijective, then α is bijective. Both
commuting-square equations and both retraction identities are hypotheses. -/
theorem comparison_bijective_of_retract
    (α : D →ₗ[R] C) (β : E →ₗ[R] F)
    (iD : D →ₗ[R] E) (rD : E →ₗ[R] D)
    (iC : C →ₗ[R] F) (rC : F →ₗ[R] C)
    (hD : rD.comp iD = LinearMap.id) (hC : rC.comp iC = LinearMap.id)
    (hi : β.comp iD = iC.comp α) (hr : α.comp rD = rC.comp β)
    (hβ : Function.Bijective β) : Function.Bijective α := by
  constructor
  · intro x y h
    have h₁ : β (iD x) = β (iD y) := by
      calc
        β (iD x) = iC (α x) := LinearMap.congr_fun hi x
        _ = iC (α y) := congrArg iC h
        _ = β (iD y) := (LinearMap.congr_fun hi y).symm
    have h₂ := congrArg rD (hβ.injective h₁)
    simpa only [← LinearMap.comp_apply, hD, LinearMap.id_apply] using h₂
  · intro y
    obtain ⟨x, hx⟩ := hβ.surjective (iC y)
    refine ⟨rD x, ?_⟩
    calc
      α (rD x) = rC (β x) := LinearMap.congr_fun hr x
      _ = rC (iC y) := congrArg rC hx
      _ = y := LinearMap.congr_fun hC y

end LinearMap

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

public import MathlibExt.Analysis.CStarAlgebra.Extension.UnitaryHomClasses
public import MathlibExt.Analysis.CStarAlgebra.CStarMatrix.DiagonalPair
public import Mathlib.Analysis.CStarAlgebra.CStarMatrix

/-!
# Literal diagonal lifts of multiplier-quotient homomorphisms

Entrywise matrix maps commute with the actual algebraic diagonal pairing.
Two real multiplier-valued lifts therefore give a real diagonal matrix lift;
no source fold or quotient class operation is assumed.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped CStarAlgebra Matrix MultiplierAlgebra

universe uC uM uQ uP

namespace NonUnitalStarAlgHom

variable {C : Type uC} {M : Type uM} {Q : Type uQ}
variable [NonUnitalNonAssocSemiring C] [DistribMulAction ℂ C] [Star C]
variable [Semiring M] [StarRing M] [Algebra ℂ M]
variable [Semiring Q] [StarRing Q] [Algebra ℂ Q]

/-- Actual entrywise projection commutes with the literal two-hom diagonal pairing. -/
theorem map_diagonalPair (q : M →⋆ₙₐ[ℂ] Q) (rho₀ rho₁ : C →⋆ₙₐ[ℂ] M) :
    (CStarMatrix.mapₙₐ (n := Fin 2) q).comp (diagonalPair rho₀ rho₁) =
      diagonalPair (q.comp rho₀) (q.comp rho₁) := by
  apply NonUnitalStarAlgHom.ext
  intro a
  apply CStarMatrix.ext
  intro i j
  change q (diagonalPair rho₀ rho₁ a i j) =
    diagonalPair (q.comp rho₀) (q.comp rho₁) a i j
  rw [diagonalPair_apply, diagonalPair_apply]
  by_cases hij : i = j
  · subst j
    simp only [ite_true]
    by_cases hi : i = 0
    · simp only [ite_eq_left hi, NonUnitalStarAlgHom.comp_apply]
    · simp only [ite_eq_right hi, NonUnitalStarAlgHom.comp_apply]
  · simp only [ite_eq_right hij, map_zero]

end NonUnitalStarAlgHom

namespace CStarExtension

variable {C : Type uC} {P : Type uP}
variable [NonUnitalNonAssocSemiring C] [DistribMulAction ℂ C] [StarAddMonoid C]
variable [NonUnitalCStarAlgebra P]

attribute [local instance] CStarExtension.outerCStarAlgebra

/-- Literal multiplier lifts of two Busby maps give their literal diagonal matrix lift.
The matrix projection is the actual map induced by the outer quotient. -/
theorem diagonalPair_hasLift
    {tau₀ tau₁ : BusbyHom C P} (h₀ : IsTrivial tau₀) (h₁ : IsTrivial tau₁) :
    ∃ rhoPair : C →⋆ₙₐ[ℂ] CStarMatrix (Fin 2) (Fin 2) (DoubleCentralizer ℂ P),
      (CStarMatrix.mapₙₐ (n := Fin 2)
        (outerQuotientMap (A := P)).toNonUnitalStarAlgHom).comp rhoPair =
        NonUnitalStarAlgHom.diagonalPair tau₀ tau₁ := by
  let _ : CStarAlgebra (OuterMultiplier P) := outerMultiplierCStarAlgebra P
  obtain ⟨rho₀, hrho₀⟩ := h₀
  obtain ⟨rho₁, hrho₁⟩ := h₁
  refine ⟨NonUnitalStarAlgHom.diagonalPair rho₀ rho₁, ?_⟩
  rw [NonUnitalStarAlgHom.map_diagonalPair, hrho₀, hrho₁]

end CStarExtension

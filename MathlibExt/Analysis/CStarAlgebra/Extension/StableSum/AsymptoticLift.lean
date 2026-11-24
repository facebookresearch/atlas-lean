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

public import MathlibExt.Analysis.CStarAlgebra.Extension.AsymptoticLift
public import MathlibExt.Analysis.CStarAlgebra.AsymptoticMorphism.Prod
public import MathlibExt.Analysis.CStarAlgebra.Extension.StableSum.Basic
public import MathlibExt.Analysis.CStarAlgebra.CStarMatrix.DiagonalPair
import Mathlib.Tactic.FinCases

/-!
# Exact asymptotic lifts of supplied stable sums

For arbitrary compatible stable-sum data, product pairing and actual diagonal
postcomposition combine two nonlinear exact asymptotic lifts. The multiplier
matrix equivalence preserves each time-continuous orbit and all four defect
limits. Its compatibility with the actual quotient gives the exact Busby-sum
identity at every time in [1, infinity), including the initial time.
-/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
open scoped BigOperators CStarAlgebra Matrix MultiplierAlgebra Topology
noncomputable section

namespace CStarExtension

universe uA uB
variable {B : Type uB} [NonUnitalCStarAlgebra B]
attribute [local instance] CStarExtension.outerCStarAlgebra


section Lifts

variable {A : Type uA} [NonUnitalCStarAlgebra A]

/-- Sum two actual nonlinear exact lifts, by true diagonal/fold postcomposition. -/
def StableSumData.asymptoticLift (S : StableSumData A B) {tau₁ tau₂ : BusbyHom A B}
    (L₁ : ExactAsymptoticLift tau₁) (L₂ : ExactAsymptoticLift tau₂) :
    ExactAsymptoticLift (S.sum tau₁ tau₂) := by
  letI : PartialOrder 𝓜(ℂ, B) := CStarAlgebra.spectralOrder 𝓜(ℂ, B)
  letI : StarOrderedRing 𝓜(ℂ, B) := CStarAlgebra.spectralOrderedRing 𝓜(ℂ, B)
  let diagonal : (𝓜(ℂ, B) × 𝓜(ℂ, B)) →⋆ₙₐ[ℂ] CStarMatrix (Fin 2) (Fin 2) 𝓜(ℂ, B) :=
    (NonUnitalStarAlgHom.fst ℂ 𝓜(ℂ, B) 𝓜(ℂ, B)).diagonalPair
      (NonUnitalStarAlgHom.snd ℂ 𝓜(ℂ, B) 𝓜(ℂ, B))
  let matrixFamily : AsymptoticMorphism A (CStarMatrix (Fin 2) (Fin 2) 𝓜(ℂ, B)) :=
    AsymptoticMorphism.postcomp (AsymptoticMorphism.prod L₁.family L₂.family) diagonal
  let resultFamily : AsymptoticMorphism A 𝓜(ℂ, B) :=
    AsymptoticMorphism.postcomp matrixFamily S.multiplierMatrixEquiv.toNonUnitalStarAlgHom
  refine ⟨resultFamily, ?_⟩
  intro t a
  change outerQuotientMap (AsymptoticMorphism.postcomp matrixFamily
    S.multiplierMatrixEquiv.toNonUnitalStarAlgHom t a) = S.sum tau₁ tau₂ a
  rw [AsymptoticMorphism.postcomp_apply]
  change outerQuotientMap (S.multiplierMatrixEquiv
    (AsymptoticMorphism.postcomp (AsymptoticMorphism.prod L₁.family L₂.family) diagonal t a)) =
      S.sum tau₁ tau₂ a
  rw [AsymptoticMorphism.postcomp_apply, AsymptoticMorphism.prod_apply,
    ← S.quotient_compatible, S.sum_apply]
  congr 1
  ext i j
  simp only [CStarMatrix.map_apply, diagonal, NonUnitalStarAlgHom.diagonalPair_apply,
    NonUnitalStarAlgHom.fst_apply, NonUnitalStarAlgHom.snd_apply, twoDiagonal]
  split_ifs <;> simp [L₁.quotient_eq, L₂.quotient_eq]

/-- The actual generic matrix family, before the fixed multiplier fold. -/
theorem StableSumData.asymptoticLift_apply (S : StableSumData A B)
    {tau₁ tau₂ : BusbyHom A B} (L₁ : ExactAsymptoticLift tau₁) (L₂ : ExactAsymptoticLift tau₂)
    (t : AsymptoticTime) (a : A) :
    (S.asymptoticLift L₁ L₂).family t a = S.multiplierMatrixEquiv
      (CStarMatrix.ofMatrix (Matrix.diagonal ![L₁.family t a, L₂.family t a])) := by
  let : PartialOrder 𝓜(ℂ, B) := CStarAlgebra.spectralOrder 𝓜(ℂ, B)
  let : StarOrderedRing 𝓜(ℂ, B) := CStarAlgebra.spectralOrderedRing 𝓜(ℂ, B)
  rw [StableSumData.asymptoticLift, AsymptoticMorphism.postcomp_apply,
    AsymptoticMorphism.postcomp_apply, AsymptoticMorphism.prod_apply]
  change S.multiplierMatrixEquiv
    ((NonUnitalStarAlgHom.fst ℂ 𝓜(ℂ, B) 𝓜(ℂ, B)).diagonalPair
      (NonUnitalStarAlgHom.snd ℂ 𝓜(ℂ, B) 𝓜(ℂ, B)) (L₁.family t a, L₂.family t a)) = _
  apply congrArg S.multiplierMatrixEquiv
  apply CStarMatrix.ext
  intro i j
  simp only [NonUnitalStarAlgHom.diagonalPair_apply, NonUnitalStarAlgHom.fst_apply,
    NonUnitalStarAlgHom.snd_apply, CStarMatrix.ofMatrix_apply, Matrix.diagonal_apply]
  fin_cases i <;> fin_cases j <;> rfl

/-- Asymptotic splitting is closed under the actual compatible stable sum. -/
theorem StableSumData.sum_isAsymptoticallySplit (S : StableSumData A B)
    {tau₁ tau₂ : BusbyHom A B}
    (h₁ : IsAsymptoticallySplit tau₁) (h₂ : IsAsymptoticallySplit tau₂) :
    IsAsymptoticallySplit (S.sum tau₁ tau₂) := by
  obtain ⟨L₁⟩ := h₁
  obtain ⟨L₂⟩ := h₂
  exact ⟨S.asymptoticLift L₁ L₂⟩

end Lifts
end CStarExtension

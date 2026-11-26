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
# Exact asymptotic lifts of matrix-fold sums

For nonunital C-star algebras `A,B`, compatible folds `S` and exact asymptotic lifts `ρ₁,ρ₂` of
`τ₁,τ₂`, define `ρ_t(a) = S.multiplierMatrixEquiv (diag(ρ₁_t(a),ρ₂_t(a)))`. This is an
asymptotic morphism into `M(B)` and satisfies `q(ρ_t(a)) = S.sum τ₁ τ₂ a` at every time `t ∈
[1,∞)`.

The diagonal pairing and multiplier fold preserve continuous time orbits and all four defect
limits. Therefore asymptotic splitting is closed under these compatible sums, without an
associativity assumption on `S`.
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

/-- **Folded diagonal of two exact lifts.** For compatible `S` and exact lifts `L₁,L₂`, fold
`diag(L₁.family t a,L₂.family t a)` through the multiplier matrix equivalence; the resulting
family exactly lifts `S.sum τ₁ τ₂` at every time. -/
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

/-- **Value of the folded asymptotic lift.** `(S.asymptoticLift L₁ L₂).family t a =
S.multiplierMatrixEquiv (diag(L₁.family t a,L₂.family t a))`. -/
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

/-- **Asymptotic splitting under compatible sums.** For nonunital C-star algebras `A,B` and
compatible folds `S`, asymptotically split `τ₁,τ₂` have asymptotically split sum `S.sum τ₁
τ₂`. -/
theorem StableSumData.sum_isAsymptoticallySplit (S : StableSumData A B)
    {tau₁ tau₂ : BusbyHom A B}
    (h₁ : IsAsymptoticallySplit tau₁) (h₂ : IsAsymptoticallySplit tau₂) :
    IsAsymptoticallySplit (S.sum tau₁ tau₂) := by
  obtain ⟨L₁⟩ := h₁
  obtain ⟨L₂⟩ := h₂
  exact ⟨S.asymptoticLift L₁ L₂⟩

end Lifts
end CStarExtension

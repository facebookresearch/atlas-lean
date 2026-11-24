/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentRelativeHornLift
import Mathlib.AlgebraicTopology.Quasicategory.InnerFibration

/-!
# The actual coherent nerve of an original Hom fibration is inner

Relative scalar lifting and whole enriched horn assembly give the
original nerve map's right lifting property against every inner horn.
Neither enrichment needs to be locally Kan and no Bergner model or
nerve-fibration outcome is assumed.
-/

noncomputable section
universe u
open CategoryTheory MonoidalCategory Opposite HomotopicalAlgebra
open scoped Simplicial SSet.modelCategoryQuillen

namespace CategoryTheory.CoherentRealization.NerveInnerFibration
open SimplicialEnrichment

variable {C D : Carrier.{u}} (F : C ⟶ D)

/-- Every original inner-horn square of the actual coherent nerve map lifts from genuine original Hom fibrations. -/
theorem hasLiftingProperty_innerHorn (hF : ∀ x y : C, Fibration (F.map x y))
    {n : ℕ} (i : Fin (n + 3)) (h₀ : 0 < i) (hₙ : i < Fin.last (n + 2)) :
    HasLiftingProperty (Λ[n + 2, i]).ι (coherentNerveFunctor.map F) := by
  refine ⟨fun {f g} sq => ?_⟩
  let σ : coherentSimplex.{u} ⦋n + 2⦌ ⟶ D := SSet.yonedaEquiv g
  have hσ : SSet.yonedaEquiv.symm σ = g := Equiv.symm_apply_apply _ _
  let sq' : CommSq f (Λ[n + 2, i]).ι (coherentNerveFunctor.map F) (SSet.yonedaEquiv.symm σ) :=
    ⟨sq.w.trans (congrArg (fun g' => (Λ[n + 2, i]).ι ≫ g') hσ.symm)⟩
  let τ := RelativeHornLift.simplex F f σ sq' (ne_of_gt h₀) (ne_of_lt hₙ) hF
  let l : (Δ[n + 2] : SSet.{u}) ⟶ coherentNerveFunctor.obj C := SSet.yonedaEquiv.symm τ
  refine ⟨⟨{ l := l, fac_left := ?_, fac_right := ?_ }⟩⟩
  · apply SSet.horn.hom_ext'
    intro j hj
    have hJ : SSet.stdSimplex.δ j ≫ l = SSet.horn.ι i j hj ≫ f := by
      apply SSet.yonedaEquiv.injective
      have hY := (SSet.yonedaEquiv_naturality (SimplexCategory.δ j) l).symm
      have hEval : SSet.yonedaEquiv l = τ := Equiv.apply_symm_apply _ _
      exact hY.trans
        ((congrArg (fun t => coherentSimplexMap (SimplexCategory.δ j) ≫ t) hEval).trans
          ((RelativeHornLift.simplex_face F f σ sq' (ne_of_gt h₀) (ne_of_lt hₙ) hF j hj).trans
            (HornFaces.faceFunctor_yoneda f j hj)))
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (fun p => p ≫ l) (SSet.horn.ι_ι i j hj)).trans hJ)
  · have hImage : τ ≫ F = σ := RelativeHornLift.simplex_image F f σ sq' (ne_of_gt h₀) (ne_of_lt hₙ) hF
    exact (SSet.yonedaEquiv_symm_comp τ (coherentNerveFunctor.map F)).trans
      ((congrArg SSet.yonedaEquiv.symm hImage).trans hσ)

/-- The actual original coherent-nerve map is an inner fibration whenever every original enriched Hom map is
  a genuine scalar fibration. -/
theorem innerFibration (hF : ∀ x y : C, Fibration (F.map x y)) :
    SSet.InnerFibration (coherentNerveFunctor.map F) := by
  constructor
  intro A B p hp
  cases hp with
  | intro i h₀ hₙ => exact hasLiftingProperty_innerHorn F hF i h₀ hₙ

end CategoryTheory.CoherentRealization.NerveInnerFibration

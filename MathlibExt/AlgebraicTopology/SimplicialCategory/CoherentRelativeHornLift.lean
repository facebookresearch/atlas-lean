/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentRelativeHornImages
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentHornAssembly

/-!
# Actual enriched relative inner-horn fillers

Genuine scalar fibrations on the original enriched Homs construct an
actual whole enriched simplex over the prescribed target simplex.
Every supplied face, individual original vertex and whole target Hom
map is retained. There is no local Kan source/target or enriched-model
outcome hypothesis.
-/

noncomputable section
universe u
open CategoryTheory MonoidalCategory Opposite HomotopicalAlgebra
open scoped Simplicial SSet.modelCategoryQuillen

namespace CategoryTheory.CoherentRealization.RelativeHornLift
open SimplicialEnrichment

variable {C D : Carrier.{u}} {n : ℕ} {i : Fin (n + 3)}
  (F : C ⟶ D) (f : (Λ[n + 2, i] : SSet.{u}) ⟶ coherentNerveFunctor.obj C)
  (σ : coherentSimplex.{u} ⦋n + 2⦌ ⟶ D)
  (sq : CommSq f (Λ[n + 2, i]).ι (coherentNerveFunctor.map F) (SSet.yonedaEquiv.symm σ))
  (hi₀ : i ≠ 0) (hiₙ : i ≠ Fin.last (n + 2))

/-- The actual whole original enriched simplex constructed by scalar relative lifting and canonical assembly. -/
def simplex (hF : ∀ x y : C, Fibration (F.map x y)) : coherentSimplex.{u} ⦋n + 2⦌ ⟶ C :=
  HornAssembly.simplex f hi₀ hiₙ (RelativeHornData.outerMap F f σ sq hi₀ hiₙ hF)
    (RelativeHornData.outerMap_box F f σ sq hi₀ hiₙ hF)

variable (hF : ∀ x y : C, Fibration (F.map x y))

/-- Every supplied individual original vertex is retained by the actual relative filler. -/
theorem simplex_obj (a : Fin (n + 3)) :
    (simplex F f σ sq hi₀ hiₙ hF).obj (.mk (ULift.up a)) = HornFaces.object f a :=
  HornAssembly.simplex_obj _ _ _ _ _ a

/-- Every whole supplied original coherent face is exactly retained by the relative filler. -/
theorem simplex_face (j : Fin (n + 3)) (hj : j ≠ i) :
    coherentSimplexMap (SimplexCategory.δ j) ≫ simplex F f σ sq hi₀ hiₙ hF = HornFaces.faceFunctor f j hj :=
  HornAssembly.simplex_face _ _ _ _ _ j hj

/-- The full original enriched filler maps to precisely the specified target simplex, on every original
  object and every whole Hom. -/
theorem simplex_image : simplex F f σ sq hi₀ hiₙ hF ≫ F = σ := by
  let τ := simplex F f σ sq hi₀ hiₙ hF
  have hObj (a : coherentSimplex.{u} ⦋n + 2⦌) : (τ ≫ F).obj a = σ.obj a :=
    RelativeHornData.object_image F f σ sq a.as.down
  refine EnrichedFunctor.ext SSet.{u} (F := τ ≫ F) (G := σ) hObj ?_
  intro a b
  rcases a with ⟨⟨a⟩⟩
  rcases b with ⟨⟨b⟩⟩
  let T := RelativeHornImages.homIso F f σ sq a b
  change (τ.map (.mk (ULift.up a)) (.mk (ULift.up b)) ≫
      F.map (HornFaces.object f a) (HornFaces.object f b)) ≫ T.hom =
    σ.map (.mk (ULift.up a)) (.mk (ULift.up b))
  by_cases hOuter : a = 0 ∧ b = Fin.last (n + 2)
  · obtain ⟨rfl, rfl⟩ := hOuter
    have hMap := HornAssembly.simplex_outer_map f hi₀ hiₙ
      (RelativeHornData.outerMap F f σ sq hi₀ hiₙ hF)
      (RelativeHornData.outerMap_box F f σ sq hi₀ hiₙ hF)
    exact (congrArg (fun p => (p ≫ F.map (HornFaces.object f 0)
      (HornFaces.object f (Fin.last (n + 2)))) ≫
        (RelativeHornImages.homIso F f σ sq 0 (Fin.last (n + 2))).hom) hMap).trans
      (RelativeHornImages.outer_map_image F f σ sq hi₀ hiₙ hF)
  · by_cases hab : a ≤ b
    · have h : a ≠ 0 ∨ b ≠ Fin.last (n + 2) := by
        by_cases ha : a = 0
        · exact Or.inr (fun hb => hOuter ⟨ha, hb⟩)
        · exact Or.inl ha
      have hMap := HornAssembly.simplex_ordered_map f hi₀ hiₙ
        (RelativeHornData.outerMap F f σ sq hi₀ hiₙ hF)
        (RelativeHornData.outerMap_box F f σ sq hi₀ hiₙ hF) a b hab h
      exact (congrArg (fun p => (p ≫ F.map (HornFaces.object f a) (HornFaces.object f b)) ≫ T.hom) hMap).trans
        (RelativeHornImages.ordered_map_image F f σ sq hi₀ hiₙ a b hab h)
    · exact HomUnitsAndEmpty.empty_hom_ext
        (show ¬(ULift.up.{u} a : ULift.{u} (Fin (n + 3))) ≤ ULift.up b from hab) _ _

end CategoryTheory.CoherentRealization.RelativeHornLift

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentRelativeFullBoundaryData
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentFullBoundaryTwoFaces
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentRelativeHornImages

/-!
# Actual full relative coherent-boundary fillers in every degree at least two

The SAME full outer Hom lift assembles the prescribed original enriched
simplex. All original boundary faces and the entire target enriched
functor are retained, including the two-simplex middle face.
-/

noncomputable section
universe u
open CategoryTheory MonoidalCategory Opposite HomotopicalAlgebra
open scoped Simplicial SSet.modelCategoryQuillen

namespace CategoryTheory.CoherentRealization.RelativeFullBoundaryLift
open SimplicialEnrichment HornBoxFaces

variable {C D : Carrier.{u}} {n : ℕ}
  (F : C ⟶ D) (f : (∂Δ[n+2] : SSet.{u}) ⟶ coherentNerveFunctor.obj C)
  (σ : coherentSimplex.{u} ⦋n+2⦌ ⟶ D)
  (sq : CommSq f (SSet.boundary.{u} (n+2)).ι (coherentNerveFunctor.map F)
    (SSet.yonedaEquiv.symm σ))
  (hF : ∀ x y : C, SSet.modelCategoryQuillen.I.rlp (F.map x y))

/-- The entire original enriched simplex constructed by the genuine scalar full-boundary lift. -/
def simplex : coherentSimplex.{u} ⦋n+2⦌ ⟶ C :=
  BoundaryHomAssembly.simplex f (RelativeFullBoundaryData.outerMap F f σ sq hF)
    (RelativeFullBoundaryData.outerMap_boundary F f σ sq hF)
    (BoundaryHomFaces.canonicalIndex (n := n))
    (BoundaryHomFaces.canonicalIndex_ne_zero (n := n))
    (BoundaryHomFaces.canonicalIndex_ne_last (n := n))

/-- Every supplied individual original vertex is preserved literally. -/
theorem simplex_obj (a : Fin (n+3)) :
    (simplex F f σ sq hF).obj (.mk (ULift.up a)) = BoundaryFaces.object f a := rfl

/-- Every whole original full-boundary face is retained in all original degrees at least two. -/
theorem simplex_face (j : Fin (n+3)) :
    coherentSimplexMap (SimplexCategory.δ j) ≫ simplex F f σ sq hF =
      BoundaryFaces.faceFunctor f j := by
  by_cases hn : n = 0
  · subst n
    exact BoundaryHomAssembly.simplex_two_all_faces f
      (RelativeFullBoundaryData.outerMap F f σ sq hF)
      (RelativeFullBoundaryData.outerMap_boundary F f σ sq hF) j
  · exact BoundaryHomAssembly.simplex_all_faces f
      (RelativeFullBoundaryData.outerMap F f σ sq hF)
      (RelativeFullBoundaryData.outerMap_boundary F f σ sq hF) hn
      (BoundaryHomFaces.canonicalIndex (n := n))
      (BoundaryHomFaces.canonicalIndex_ne_zero (n := n))
      (BoundaryHomFaces.canonicalIndex_ne_last (n := n)) j

/-- The entire original assembled simplex maps to the SAME prescribed target on every object and complete Hom. -/
theorem simplex_image : simplex F f σ sq hF ≫ F = σ := by
  let τ := simplex F f σ sq hF
  let i := BoundaryHomFaces.canonicalIndex (n := n)
  let r := BoundaryFaces.horn f i
  let s := RelativeFullBoundaryData.hornSquare F f σ sq
  let g := RelativeFullBoundaryData.outerMap F f σ sq hF
  let hg := RelativeFullBoundaryData.outerMap_boundary F f σ sq hF
  let hi₀ := BoundaryHomFaces.canonicalIndex_ne_zero (n := n)
  let hiₙ := BoundaryHomFaces.canonicalIndex_ne_last (n := n)
  let hr := BoundaryHomAssembly.horn_extension f g hg i hi₀ hiₙ
  have hObj (a : coherentSimplex.{u} ⦋n+2⦌) : (τ ≫ F).obj a = σ.obj a :=
    RelativeFullBoundaryData.object_image F f σ sq a.as.down
  apply EnrichedFunctor.ext SSet.{u} (F := τ ≫ F) (G := σ) hObj
  intro a b
  rcases a with ⟨⟨a⟩⟩
  rcases b with ⟨⟨b⟩⟩
  let T := RelativeHornImages.homIso F r σ s a b
  change (τ.map (.mk (ULift.up a)) (.mk (ULift.up b)) ≫
      F.map (BoundaryFaces.object f a) (BoundaryFaces.object f b)) ≫ T.hom =
    σ.map (.mk (ULift.up a)) (.mk (ULift.up b))
  by_cases hOuter : a = 0 ∧ b = Fin.last (n+2)
  · obtain ⟨rfl,rfl⟩ := hOuter
    have hMap := HornAssembly.simplex_outer_map r hi₀ hiₙ g hr
    have hTarget := RelativeFullBoundaryData.outerMap_target F f σ sq hF
    have hImage : (g ≫ F.map (BoundaryFaces.object f 0) (BoundaryFaces.object f (Fin.last (n+2)))) ≫
        T.hom = σ.map (.mk (ULift.up 0)) (.mk (ULift.up (Fin.last (n+2)))) := by
      let E := RelativeFullBoundaryData.endpointIso F f σ sq
      let M := σ.map (.mk (ULift.up 0)) (.mk (ULift.up (Fin.last (n+2))))
      exact (congrArg (fun q => q ≫ E.hom) hTarget).trans
        ((Category.assoc M E.inv E.hom).trans
          ((congrArg (fun q => M ≫ q) E.inv_hom_id).trans (Category.comp_id M)))
    exact (congrArg (fun q => (q ≫ F.map (BoundaryFaces.object f 0)
      (BoundaryFaces.object f (Fin.last (n+2)))) ≫ T.hom) hMap).trans hImage
  · by_cases hab : a ≤ b
    · have h : a ≠ 0 ∨ b ≠ Fin.last (n+2) := by
        by_cases ha : a = 0
        · exact Or.inr (fun hb => hOuter ⟨ha,hb⟩)
        · exact Or.inl ha
      have hMap := HornAssembly.simplex_ordered_map r hi₀ hiₙ g hr a b hab h
      exact (congrArg (fun q => (q ≫ F.map (BoundaryFaces.object f a)
        (BoundaryFaces.object f b)) ≫ T.hom) hMap).trans
          (RelativeHornImages.ordered_map_image F r σ s hi₀ hiₙ a b hab h)
    · exact HomUnitsAndEmpty.empty_hom_ext
        (show ¬(ULift.up.{u} a : ULift.{u} (Fin (n+3))) ≤ ULift.up b from hab) _ _

/-- The actual whole original nerve simplex retains the entire supplied boundary simplicial map. -/
theorem simplex_boundary :
    (SSet.boundary.{u} (n+2)).ι ≫ SSet.yonedaEquiv.symm (simplex F f σ sq hF) = f := by
  apply SSet.boundary.hom_ext
  intro j
  let τ := simplex F f σ sq hF
  let l : (Δ[n+2] : SSet.{u}) ⟶ coherentNerveFunctor.obj C := SSet.yonedaEquiv.symm τ
  have hJ : SSet.stdSimplex.δ j ≫ l = SSet.boundary.ι j ≫ f := by
    apply SSet.yonedaEquiv.injective
    have hY := (SSet.yonedaEquiv_naturality (SimplexCategory.δ j) l).symm
    have hEval : SSet.yonedaEquiv l = τ := Equiv.apply_symm_apply _ _
    exact hY.trans
      ((congrArg (fun q => coherentSimplexMap (SimplexCategory.δ j) ≫ q) hEval).trans
        (simplex_face F f σ sq hF j))
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun q => q ≫ l) (SSet.boundary.ι_ι j)).trans hJ)

include sq hF in
/-- A genuine full original relative enriched boundary filler exists in every dimension at least two. -/
theorem exists_enriched_boundary_lift :
    ∃ τ : coherentSimplex.{u} ⦋n+2⦌ ⟶ C,
      (SSet.boundary.{u} (n+2)).ι ≫ SSet.yonedaEquiv.symm τ = f ∧ τ ≫ F = σ :=
  ⟨simplex F f σ sq hF, simplex_boundary F f σ sq hF, simplex_image F f σ sq hF⟩

end CategoryTheory.CoherentRealization.RelativeFullBoundaryLift

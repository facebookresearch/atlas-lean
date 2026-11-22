/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.NativeTailFaceSourceIso
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.NativeChartWholeOperator
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.EnrichedLeftKanCompositeHom

/-!
# The original native zeroth-face attaching map

The canonical source isomorphism preserves the actual original chart
restriction. Its adjoint transpose is the original whole cone image
followed by the target unit, with the genuine coherent base transport.
Thus the source comparison identifies the map itself, not merely its
source object.
-/

noncomputable section
universe u v
open CategoryTheory Limits Opposite
open scoped Simplicial

namespace SSet.Marked
open CoherentWeight CategoryTheory.CoherentRealization
attribute [local instance] markedSimplicialCategory enrichedDiagramCategory

/-- The inverse canonical composite comparison retains the whole original native left-extension Hom transpose. -/
theorem nativeTailComposite_inv_universal (B : SSet.{u}) (n : ℕ) (σ : B _⦋n + 1⦌)
    (W : EnrichedDiagram (Index.{u} n)ᵒᵖ) (F : EnrichedDiagram (realization B)ᵒᵖ)
    (g : (EnrichedLeftKan.leftExtension (coneTailIndex n) ⋙
      EnrichedLeftKan.leftExtension (EnrichedFunctor.opposite (simplexInto B σ))).obj W ⟶ F) :
    EnrichedLeftKan.universalHomEquiv
        (EnrichedFunctor.opposite (simplexInto B (B.map (SimplexCategory.δ (0 : Fin (n + 2))).op σ))) W F
          ((nativeTailCompositeNatIso B n σ).inv.app W ≫ g) =
      (nativeTailCompositeAdjunction B n σ).homEquiv W F g := by
  let j := EnrichedFunctor.opposite (simplexInto B (B.map (SimplexCategory.δ (0 : Fin (n + 2))).op σ))
  let a := nativeTailCompositeAdjunction B n σ
  let b := EnrichedLeftKan.adjunction j
  let L := EnrichedLeftKan.leftExtension (coneTailIndex n) ⋙
    EnrichedLeftKan.leftExtension (EnrichedFunctor.opposite (simplexInto B σ))
  let e := nativeTailCompositeNatIso B n σ
  let R := enrichedDiagramRestrict j
  have hi : b.homEquiv W (L.obj W) (e.inv.app W) = a.unit.app W :=
    (congrArg (b.homEquiv W (L.obj W)) (Adjunction.leftAdjointUniq_inv_app a b W)).trans
      (Adjunction.homEquiv_leftAdjointUniq_hom_app b a W)
  have ht := b.homEquiv_naturality_right (e.inv.app W) g
  exact (enrichedLeftKanAdjunction_homEquiv_eq j W F (e.inv.app W ≫ g)).symm.trans
    (ht.trans ((congrArg (fun f => f ≫ R.map g) hi).trans (a.homEquiv_unit W F g).symm))

/-- The original composite left-extension transpose is exactly the whole original coface operator and target
  unit with its actual coefficient transport. -/
theorem nativeTailComposite_original_operator (B : SSet.{u}) (n : ℕ) (σ : B _⦋n + 1⦌) :
    (nativeTailCompositeAdjunction B n σ).homEquiv (coneDiagram.{u} n) (nativeSimplexChart B (n + 1) σ)
        (EnrichedLeftKan.map (EnrichedFunctor.opposite (simplexInto B σ))
          (W := EnrichedLeftKan.object (coneTailIndex.{u} n) (coneDiagram.{u} n))
          (V := coneDiagram.{u} (n + 1)) (coneTailLeftKanInclusion.{u} n)) =
      (coneOperator (coneTailEmbedding.{u} n).toOrderHom ≫
          (enrichedDiagramRestrict (coneTailIndex.{u} n)).map
            (EnrichedLeftKan.unit (EnrichedFunctor.opposite (simplexInto B σ)) (coneDiagram.{u} (n + 1)))) ≫
        eqToHom (nativeChartWholeOperatorTargetEq B (SimplexCategory.δ (0 : Fin (n + 2))) σ) := by
  let j := coneTailIndex.{u} n
  let k := EnrichedFunctor.opposite (simplexInto B σ)
  let W := coneDiagram.{u} n
  let F := nativeSimplexChart B (n + 1) σ
  let p := EnrichedLeftKan.unit k (coneDiagram.{u} (n + 1))
  let f := coneTailLeftKanInclusion.{u} n
  let g := EnrichedLeftKan.map k (W := EnrichedLeftKan.object j W) (V := coneDiagram (n + 1)) f
  let a := (EnrichedLeftKan.adjunction j).comp (EnrichedLeftKan.adjunction k)
  let r := eqToIso (nativeTail_restriction_comp B n σ)
  have h₀ := Adjunction.homEquiv_ofNatIsoRight_apply (X := W) (Y := F) a r g
  have hgoal : (nativeTailCompositeAdjunction B n σ).homEquiv W F g =
      a.homEquiv W F g ≫ r.hom.app F := h₀
  have h₁ := enrichedLeftKanComposite_map_hom j k W (coneDiagram (n + 1)) f
  have h₅ := (EnrichedLeftKan.universalHomEquiv j W (coneDiagram (n + 1))).apply_symm_apply
    (coneOperator (coneTailEmbedding n).toOrderHom)
  have hs : a.homEquiv W F g = coneOperator (coneTailEmbedding n).toOrderHom ≫
      (enrichedDiagramRestrict j).map p :=
    h₁.trans (congrArg (fun e => e ≫ (enrichedDiagramRestrict j).map p) h₅)
  have hr : r.hom.app F =
      eqToHom (nativeChartWholeOperatorTargetEq B (SimplexCategory.δ (0 : Fin (n + 2))) σ) :=
    eqToHom_app (nativeTail_restriction_comp B n σ) F
  let Rsrc := (enrichedDiagramRestrict j).obj ((enrichedDiagramRestrict k).obj F)
  let Rdst := (enrichedDiagramRestrict
    (EnrichedFunctor.opposite (simplexInto B (B.map (SimplexCategory.δ (0 : Fin (n + 2))).op σ)))).obj F
  have hpost := congrArg (fun e : W ⟶ Rsrc => e ≫ r.hom.app F) hs
  have htransport := congrArg (fun e : Rsrc ⟶ Rdst =>
    (coneOperator (coneTailEmbedding n).toOrderHom ≫ (enrichedDiagramRestrict j).map p) ≫ e) hr
  exact hgoal.trans (hpost.trans htransport)

/-- The actual original zeroth-face chart map is precisely the native root attachment through its genuine
  whole source isomorphism. -/
theorem nativeTailFaceSourceIso_attachment (B : SSet.{u}) (n : ℕ) (σ : B _⦋n + 1⦌) :
    (nativeTailFaceSourceIso B n σ).hom ≫ nativePositiveRootChartMap B (n + 1) σ =
      nativeSimplexChartRestriction B (SimplexCategory.δ (0 : Fin (n + 2))) σ := by
  let j := EnrichedFunctor.opposite (simplexInto B (B.map (SimplexCategory.δ (0 : Fin (n + 2))).op σ))
  let k := EnrichedFunctor.opposite (simplexInto B σ)
  let L := EnrichedLeftKan.leftExtension k
  let W := coneDiagram.{u} n
  let F := nativeSimplexChart B (n + 1) σ
  let e := nativeTailCompositeNatIso B n σ
  let f := coneAfterDiagramInclusion (⊥ : Vertex.{u} (n + 1))
  let g := L.map (coneTailLeftKanInclusion n)
  have hm : L.map (coneTailLeftKanMap n) ≫ L.map f = g :=
    (L.map_comp (coneTailLeftKanMap n) f).symm.trans
      (congrArg L.map (coneTailLeftKanMap_inclusion n))
  have he : (nativeTailFaceSourceIso B n σ).hom ≫ nativePositiveRootChartMap B (n + 1) σ =
      e.inv.app W ≫ g := by
    change (e.inv.app W ≫ L.map (coneTailLeftKanMap n)) ≫ L.map f = _
    exact (Category.assoc _ _ _).trans (congrArg (fun a => e.inv.app W ≫ a) hm)
  apply (EnrichedLeftKan.universalHomEquiv j W F).injective
  exact (congrArg (EnrichedLeftKan.universalHomEquiv j W F) he).trans
    ((nativeTailComposite_inv_universal B n σ W F g).trans
      ((nativeTailComposite_original_operator B n σ).trans
        (nativeChartRestriction_whole_operator B (SimplexCategory.δ (0 : Fin (n + 2))) σ)))

end SSet.Marked

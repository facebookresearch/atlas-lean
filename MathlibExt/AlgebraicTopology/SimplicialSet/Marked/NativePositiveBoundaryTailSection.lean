/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.NativeUpperRootInverseUnit
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.NativeTailFaceMate
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.EnrichedLeftKanFreeNaturality

/-!
# The exact original positive-boundary section on all tail coefficients

The actual original tail and base adjunctions read their unchanged
tail mate followed by a target map as the same original tail operator
and whole target section. The genuine original tail source isomorphism
therefore reads the positive boundary inverse on every full marked
tail coefficient as the actual original zeroth-coface unit section.
Original coherent base transports are retained throughout.
-/

noncomputable section
universe u
open CategoryTheory Limits Opposite
open scoped Simplicial

namespace SSet.Marked
open CoherentWeight CategoryTheory.CoherentRealization
attribute [local instance] markedSimplicialCategory enrichedDiagramCategory

/-- The actual original tail/base composite adjunction reads the original tail mate followed by any actual target
map as exactly the original tail operator followed by its whole native positive-cone section and genuine coherent
base transport. -/
theorem nativeTailComposite_post_operator (B : SSet.{u}) (n : ℕ) (σ : B _⦋n + 1⦌)
    (F : EnrichedDiagram (realization B)ᵒᵖ) (g : nativePositiveRootChart B (n + 1) σ ⟶ F) :
    (nativeTailCompositeAdjunction B n σ).homEquiv (coneDiagram n) F
      ((EnrichedLeftKan.leftExtension (EnrichedFunctor.opposite (simplexInto B σ))).map (coneTailLeftKanMap n) ≫ g) =
      (coneTailOperator n ≫ (enrichedDiagramRestrict (coneTailIndex n)).map
        (EnrichedLeftKan.universalHomEquiv (EnrichedFunctor.opposite (simplexInto B σ))
          (coneAfterDiagram (⊥ : Vertex.{u} (n + 1))) F g)) ≫
            (eqToHom (nativeTail_restriction_comp B n σ)).app F := by
  let j := coneTailIndex.{u} n
  let k := EnrichedFunctor.opposite (simplexInto B σ)
  let W := coneDiagram.{u} n
  let V := coneAfterDiagram (⊥ : Vertex.{u} (n + 1))
  let f := coneTailLeftKanMap.{u} n
  let x := (EnrichedLeftKan.leftExtension k).map f ≫ g
  let a := EnrichedLeftKan.adjunction j
  let b := EnrichedLeftKan.adjunction k
  let R := enrichedDiagramRestrict k
  let P := EnrichedLeftKan.universalHomEquiv k V F g
  let r := eqToIso (nativeTail_restriction_comp B n σ)
  have h₀ : (nativeTailCompositeAdjunction B n σ).homEquiv W F x =
      (a.comp b).homEquiv W F x ≫ r.hom.app F :=
    Adjunction.homEquiv_ofNatIsoRight_apply (X := W) (Y := F) (a.comp b) r x
  have h₁ : (a.comp b).homEquiv W F x = a.homEquiv W (R.obj F)
      (b.homEquiv (EnrichedLeftKan.object j W) F x) :=
    congrArg (fun e => e W F x) (Adjunction.comp_homEquiv a b)
  have h₂ : b.homEquiv (EnrichedLeftKan.object j W) F x = f ≫ P :=
    (enrichedLeftKanAdjunction_homEquiv_eq k (EnrichedLeftKan.object j W) F x).trans
      (enrichedLeftKan_universal_map_post k f g)
  have h₃ := enrichedLeftKanAdjunction_homEquiv_eq j W (R.obj F) (f ≫ P)
  have h₄ := EnrichedLeftKan.universalHomEquiv_natural_right j W f P
  have h₅ : EnrichedLeftKan.universalHomEquiv j W V f = coneTailOperator n :=
    (EnrichedLeftKan.universalHomEquiv j W V).apply_symm_apply (coneTailOperator n)
  have hread : (a.comp b).homEquiv W F x = coneTailOperator n ≫ (enrichedDiagramRestrict j).map P :=
    h₁.trans ((congrArg (a.homEquiv W (R.obj F)) h₂).trans
      (h₃.trans (h₄.trans (congrArg (fun z => z ≫ (enrichedDiagramRestrict j).map P) h₅))))
  exact h₀.trans (congrArg (fun z => z ≫ r.hom.app F) hread)

/-- The genuine original tail source isomorphism reads every actual whole positive-chart target map as its unchanged
original tail coefficient operator and native section, with the same original coherent base transport. -/
theorem nativeTailFaceSourceIso_post_section (B : SSet.{u}) (n : ℕ) (σ : B _⦋n + 1⦌)
    (F : EnrichedDiagram (realization B)ᵒᵖ) (g : nativePositiveRootChart B (n + 1) σ ⟶ F) :
    EnrichedLeftKan.universalHomEquiv
      (EnrichedFunctor.opposite (simplexInto B (B.map (SimplexCategory.δ (0 : Fin (n + 2))).op σ)))
      (coneDiagram n) F ((nativeTailFaceSourceIso B n σ).hom ≫ g) =
      (coneTailOperator n ≫ (enrichedDiagramRestrict (coneTailIndex n)).map
        (EnrichedLeftKan.universalHomEquiv (EnrichedFunctor.opposite (simplexInto B σ))
          (coneAfterDiagram (⊥ : Vertex.{u} (n + 1))) F g)) ≫
            (eqToHom (nativeTail_restriction_comp B n σ)).app F := by
  let W := coneDiagram.{u} n
  let e := nativeTailCompositeNatIso B n σ
  let L := EnrichedLeftKan.leftExtension (EnrichedFunctor.opposite (simplexInto B σ))
  let x := L.map (coneTailLeftKanMap n) ≫ g
  let U := EnrichedLeftKan.universalHomEquiv
    (EnrichedFunctor.opposite (simplexInto B (B.map (SimplexCategory.δ (0 : Fin (n + 2))).op σ))) W F
  have hs : (nativeTailFaceSourceIso B n σ).hom ≫ g = e.inv.app W ≫ x := Category.assoc _ _ _
  exact (congrArg U hs).trans
    ((nativeTailComposite_inv_universal B n σ W F x).trans (nativeTailComposite_post_operator B n σ F g))

/-- The actual whole original positive-boundary inverse reads the same original zeroth-boundary-coface native unit
through its unchanged entire tail operator and genuine coherent base transport. -/
theorem nativePositiveBoundarySection_tail (B : SSet.{u}) (n : ℕ) (σ : B _⦋n + 1⦌) :
    (coneTailOperator n ≫ (enrichedDiagramRestrict (coneTailIndex n)).map (nativePositiveRootBoundarySection B σ)) ≫
        (eqToHom (nativeTail_restriction_comp B n σ)).app (nativeSubcomplexChart B (n + 1) σ (boundary (n + 1))) =
      EnrichedLeftKan.universalHomEquiv
        (EnrichedFunctor.opposite (simplexInto B (B.map (SimplexCategory.δ (0 : Fin (n + 2))).op σ)))
        (coneDiagram n) (nativeSubcomplexChart B (n + 1) σ (boundary (n + 1)))
        (nativeBoundaryCofaceChartMap B n σ (0 : Fin (n + 2))) := by
  let F := nativeSubcomplexChart B (n + 1) σ (boundary (n + 1))
  let U := EnrichedLeftKan.universalHomEquiv
    (EnrichedFunctor.opposite (simplexInto B (B.map (SimplexCategory.δ (0 : Fin (n + 2))).op σ))) (coneDiagram n) F
  let e := nativeTailFaceSourceIso B n σ
  have hc : e.hom ≫ nativeBoundaryPositiveInverse B n σ = nativeBoundaryCofaceChartMap B n σ (0 : Fin (n + 2)) :=
    e.hom_inv_id_assoc _
  exact (nativeTailFaceSourceIso_post_section B n σ F (nativeBoundaryPositiveInverse B n σ)).symm.trans
    (congrArg U hc)

private theorem indexEqToHom_component (n : ℕ) {F G : EnrichedDiagram (Index.{u} n)ᵒᵖ}
    (h : F = G) (i : (Index.{u} n)ᵒᵖ) :
    (eqToHom h).app i = eqToHom (congrArg (fun A : EnrichedDiagram (Index.{u} n)ᵒᵖ => A.obj i) h) := by
  cases h
  rfl

private theorem coefficient_transport_heq {A X Y : Marked.{u}} (h : X = Y)
    (a : A ⟶ X) (b : A ⟶ Y) (hab : a ≫ eqToHom h = b) : HEq b a := by
  cases h
  exact heq_of_eq (hab.symm.trans (Category.comp_id a))

/-- At every original tail vertex, the entire actual positive-boundary coefficient section has the same original
whole marked zeroth-coface unit readback, retaining the genuine original tail coefficient isomorphism and original
dependent base-object presentation. -/
theorem nativePositiveBoundarySection_tail_heq (B : SSet.{u}) (n : ℕ) (σ : B _⦋n + 1⦌)
    (i : (Index.{u} n)ᵒᵖ) :
    HEq ((EnrichedLeftKan.universalHomEquiv
      (EnrichedFunctor.opposite (simplexInto B (B.map (SimplexCategory.δ (0 : Fin (n + 2))).op σ)))
      (coneDiagram n) (nativeSubcomplexChart B (n + 1) σ (boundary (n + 1)))
      (nativeBoundaryCofaceChartMap B n σ (0 : Fin (n + 2)))).app i)
      ((coneTailAfterCoefficientIso n i.unop.as).hom ≫
        (nativePositiveRootBoundarySection B σ).app (op (SimplicialThickening.mk (coneTailEmbedding n i.unop.as))))
          := by
  let F := nativeSubcomplexChart B (n + 1) σ (boundary (n + 1))
  let h := nativeTail_restriction_comp B n σ
  let hF := Functor.congr_obj h F
  let hi := congrArg (fun A : EnrichedDiagram (Index.{u} n)ᵒᵖ => A.obj i) hF
  let a := (coneTailAfterCoefficientIso n i.unop.as).hom ≫
    (nativePositiveRootBoundarySection B σ).app (op (SimplicialThickening.mk (coneTailEmbedding n i.unop.as)))
  let b := (EnrichedLeftKan.universalHomEquiv
    (EnrichedFunctor.opposite (simplexInto B (B.map (SimplexCategory.δ (0 : Fin (n + 2))).op σ)))
    (coneDiagram n) F (nativeBoundaryCofaceChartMap B n σ (0 : Fin (n + 2)))).app i
  have ht : ((eqToHom h).app F).app i = eqToHom hi :=
    (congrArg (fun z => z.app i) (eqToHom_app h F)).trans (indexEqToHom_component n hF i)
  have hw : a ≫ ((eqToHom h).app F).app i = b :=
    congrArg (fun z => z.app i) (nativePositiveBoundarySection_tail B n σ)
  have hc : a ≫ eqToHom hi = b := (congrArg (fun z => a ≫ z) ht.symm).trans hw
  exact coefficient_transport_heq hi a b hc

end SSet.Marked

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.NativeCriticalSupportedMarkingPushouts
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.NativeChartWholeOperator
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.EnrichedLeftKanCompositeHom
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.NativeSharpMarkingChart

/-!
# Exact original critical edge composition and native whole operator readback

The whole original marked critical edge is its actual ordinal operator.
Composing its real interval left extension with extension along the
supplied original base simplex has precisely the original base-edge
restriction adjunction. Canonical adjoint uniqueness preserves the full
minimal and sharp charts, their same marking map, and the actual native
minimal edge attaching map through its original unit mate.
-/

noncomputable section
universe u
open CategoryTheory Limits Opposite
open scoped Simplicial

namespace SSet.Marked
open CoherentWeight CategoryTheory.CoherentRealization
attribute [local instance] markedSimplicialCategory enrichedDiagramCategory

/-- The SAME original marked critical edge is its whole actual ordinal operator. -/
def nativeCriticalEdgeOperator (n : ℕ) : ⦋1⦌ ⟶ ⦋n + 2⦌ :=
  stdSimplex.objEquiv (cartesianCriticalImageEdge.{u} n)

/-- The exact original critical base edge retains the supplied whole base simplex. -/
def nativeCriticalBaseEdge (B : SSet.{u}) (n : ℕ) (σ : B _⦋n + 2⦌) : B _⦋1⦌ :=
  B.map (nativeCriticalEdgeOperator.{u} n).op σ

/-- The actual whole original base restrictions compose along precisely the SAME original critical edge. -/
theorem nativeCriticalEdge_restriction_comp (B : SSet.{u}) (n : ℕ) (σ : B _⦋n + 2⦌) :
    enrichedDiagramRestrict (EnrichedFunctor.opposite (simplexInto B σ)) ⋙
      enrichedDiagramRestrict (coneCriticalEdgeIndex n) =
        enrichedDiagramRestrict (EnrichedFunctor.opposite (simplexInto B (nativeCriticalBaseEdge B n σ))) :=
  nativeChartBase_restriction_comp B (nativeCriticalEdgeOperator.{u} n) σ

/-- The two actual original critical-edge left extensions have the SAME genuine original base-edge restriction
adjunction. -/
def nativeCriticalEdgeCompositeAdjunction (B : SSet.{u}) (n : ℕ) (σ : B _⦋n + 2⦌) :
    EnrichedLeftKan.leftExtension (coneCriticalEdgeIndex n) ⋙
      EnrichedLeftKan.leftExtension (EnrichedFunctor.opposite (simplexInto B σ)) ⊣
        enrichedDiagramRestrict (EnrichedFunctor.opposite (simplexInto B (nativeCriticalBaseEdge B n σ))) :=
  ((EnrichedLeftKan.adjunction (coneCriticalEdgeIndex n)).comp
    (EnrichedLeftKan.adjunction (EnrichedFunctor.opposite (simplexInto B σ)))).ofNatIsoRight
      (eqToIso (nativeCriticalEdge_restriction_comp B n σ))

/-- Actual adjoint uniqueness identifies BOTH entire original critical interval extensions with the SAME native
base-edge chart functor. -/
def nativeCriticalEdgeCompositeNatIso (B : SSet.{u}) (n : ℕ) (σ : B _⦋n + 2⦌) :
    EnrichedLeftKan.leftExtension (coneCriticalEdgeIndex n) ⋙
      EnrichedLeftKan.leftExtension (EnrichedFunctor.opposite (simplexInto B σ)) ≅
        EnrichedLeftKan.leftExtension (EnrichedFunctor.opposite (simplexInto B (nativeCriticalBaseEdge B n σ))) :=
  Adjunction.leftAdjointUniq (nativeCriticalEdgeCompositeAdjunction B n σ)
    (EnrichedLeftKan.adjunction (EnrichedFunctor.opposite (simplexInto B (nativeCriticalBaseEdge B n σ))))

/-- The SAME full original minimal critical edge chart has its genuine whole composition isomorphism. -/
def nativeCriticalMinimalEdgeCompositionIso (B : SSet.{u}) (n : ℕ) (σ : B _⦋n + 2⦌) :
    nativeCriticalMinimalEdgeChart B n σ ≅ nativeSimplexChart B 1 (nativeCriticalBaseEdge B n σ) :=
  (nativeCriticalEdgeCompositeNatIso B n σ).app (coneDiagram 1)

/-- The entire original sharp critical edge chart has the SAME actual whole composition isomorphism. -/
def nativeCriticalSharpEdgeCompositionIso (B : SSet.{u}) (n : ℕ) (σ : B _⦋n + 2⦌) :
    nativeCriticalSharpEdgeChart B n σ ≅ nativeSharpChart B (nativeCriticalBaseEdge B n σ) :=
  (nativeCriticalEdgeCompositeNatIso B n σ).app (sharpConeDiagram 1)

/-- The whole original critical edge marking map is retained by BOTH genuine composition isomorphisms. -/
theorem nativeCriticalEdgeComposition_marking (B : SSet.{u}) (n : ℕ) (σ : B _⦋n + 2⦌) :
    nativeCriticalEdgeMarkingChartMap B n σ ≫ (nativeCriticalSharpEdgeCompositionIso B n σ).hom =
      (nativeCriticalMinimalEdgeCompositionIso B n σ).hom ≫
        nativeSharpMarkingChartMap B (nativeCriticalBaseEdge B n σ) :=
  (nativeCriticalEdgeCompositeNatIso B n σ).hom.naturality (coneSharp 1)

/-- The SAME actual critical composition inverse preserves the full original universal Hom transpose. -/
theorem nativeCriticalEdgeComposite_inv_universal (B : SSet.{u}) (n : ℕ) (σ : B _⦋n + 2⦌)
    (W : EnrichedDiagram (Index.{u} 1)ᵒᵖ) (F : EnrichedDiagram (realization B)ᵒᵖ)
    (g : (EnrichedLeftKan.leftExtension (coneCriticalEdgeIndex n) ⋙
      EnrichedLeftKan.leftExtension (EnrichedFunctor.opposite (simplexInto B σ))).obj W ⟶ F) :
    EnrichedLeftKan.universalHomEquiv
      (EnrichedFunctor.opposite (simplexInto B (nativeCriticalBaseEdge B n σ))) W F
        ((nativeCriticalEdgeCompositeNatIso B n σ).inv.app W ≫ g) =
      (nativeCriticalEdgeCompositeAdjunction B n σ).homEquiv W F g := by
  let j := EnrichedFunctor.opposite (simplexInto B (nativeCriticalBaseEdge B n σ))
  let a := nativeCriticalEdgeCompositeAdjunction B n σ
  let b := EnrichedLeftKan.adjunction j
  let L := EnrichedLeftKan.leftExtension (coneCriticalEdgeIndex n) ⋙
    EnrichedLeftKan.leftExtension (EnrichedFunctor.opposite (simplexInto B σ))
  let e := nativeCriticalEdgeCompositeNatIso B n σ
  let R := enrichedDiagramRestrict j
  have hi : b.homEquiv W (L.obj W) (e.inv.app W) = a.unit.app W :=
    (congrArg (b.homEquiv W (L.obj W)) (Adjunction.leftAdjointUniq_inv_app a b W)).trans
      (Adjunction.homEquiv_leftAdjointUniq_hom_app b a W)
  have ht := b.homEquiv_naturality_right (e.inv.app W) g
  exact (enrichedLeftKanAdjunction_homEquiv_eq j W F (e.inv.app W ≫ g)).symm.trans
    (ht.trans ((congrArg (fun f => f ≫ R.map g) hi).trans (a.homEquiv_unit W F g).symm))

/-- The actual critical composite transpose retains the SAME full original edge operator and target unit, with the
actual base transport. -/
theorem nativeCriticalEdgeComposite_original_operator (B : SSet.{u}) (n : ℕ) (σ : B _⦋n + 2⦌) :
    (nativeCriticalEdgeCompositeAdjunction B n σ).homEquiv (coneDiagram 1) (nativeSimplexChart B (n + 2) σ)
      (nativeCriticalConeEdgeMap B n σ) =
    (coneOperator (coneCriticalEdgeOrder n) ≫
      (enrichedDiagramRestrict (coneCriticalEdgeIndex n)).map
        (EnrichedLeftKan.unit (EnrichedFunctor.opposite (simplexInto B σ)) (coneDiagram (n + 2)))) ≫
      eqToHom (nativeChartWholeOperatorTargetEq B (nativeCriticalEdgeOperator.{u} n) σ) := by
  let j := coneCriticalEdgeIndex.{u} n
  let k := EnrichedFunctor.opposite (simplexInto B σ)
  let W := coneDiagram.{u} 1
  let F := nativeSimplexChart B (n + 2) σ
  let p := EnrichedLeftKan.unit k (coneDiagram.{u} (n + 2))
  let f := coneCriticalConeEdgeMap.{u} n
  let g := EnrichedLeftKan.map k (W := EnrichedLeftKan.object j W) (V := coneDiagram (n + 2)) f
  let a := (EnrichedLeftKan.adjunction j).comp (EnrichedLeftKan.adjunction k)
  let r := eqToIso (nativeCriticalEdge_restriction_comp B n σ)
  have hgoal : (nativeCriticalEdgeCompositeAdjunction B n σ).homEquiv W F g =
      a.homEquiv W F g ≫ r.hom.app F :=
    Adjunction.homEquiv_ofNatIsoRight_apply (X := W) (Y := F) a r g
  have hs : a.homEquiv W F g = coneOperator (coneCriticalEdgeOrder n) ≫
      (enrichedDiagramRestrict j).map p :=
    (enrichedLeftKanComposite_map_hom j k W (coneDiagram (n + 2)) f).trans
      (congrArg (fun e => e ≫ (enrichedDiagramRestrict j).map p) (coneCriticalConeEdgeMap_homEquiv n))
  have hr : r.hom.app F = eqToHom (nativeChartWholeOperatorTargetEq B (nativeCriticalEdgeOperator.{u} n) σ) :=
    eqToHom_app (nativeCriticalEdge_restriction_comp B n σ) F
  let Rsrc := (enrichedDiagramRestrict j).obj ((enrichedDiagramRestrict k).obj F)
  let Rdst := (enrichedDiagramRestrict
    (EnrichedFunctor.opposite (simplexInto B (nativeCriticalBaseEdge B n σ)))).obj F
  have hpost := congrArg (fun e : W ⟶ Rsrc => e ≫ r.hom.app F) hs
  have htransport := congrArg (fun e : Rsrc ⟶ Rdst =>
    (coneOperator (coneCriticalEdgeOrder n) ≫ (enrichedDiagramRestrict j).map p) ≫ e) hr
  exact hgoal.trans (hpost.trans htransport)

/-- The SAME original native critical edge attaching map is the full critical cone mate through its genuine
composition inverse. -/
theorem nativeCriticalMinimalEdgeComposition_attachment (B : SSet.{u}) (n : ℕ) (σ : B _⦋n + 2⦌) :
    (nativeCriticalMinimalEdgeCompositionIso B n σ).inv ≫ nativeCriticalConeEdgeMap B n σ =
      nativeSimplexChartRestriction B (nativeCriticalEdgeOperator.{u} n) σ := by
  let j := EnrichedFunctor.opposite (simplexInto B (nativeCriticalBaseEdge B n σ))
  let W := coneDiagram.{u} 1
  let F := nativeSimplexChart B (n + 2) σ
  apply (EnrichedLeftKan.universalHomEquiv j W F).injective
  exact (nativeCriticalEdgeComposite_inv_universal B n σ W F (nativeCriticalConeEdgeMap B n σ)).trans
    ((nativeCriticalEdgeComposite_original_operator B n σ).trans
      (nativeChartRestriction_whole_operator B (nativeCriticalEdgeOperator.{u} n) σ))

end SSet.Marked

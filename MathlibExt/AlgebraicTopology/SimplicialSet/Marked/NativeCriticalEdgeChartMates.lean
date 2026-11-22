/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.NativeCriticalEdgeOverCharts

/-!
# Same whole original horn and cone critical edge mates

The original minimal and sharp interval operators retain the full horn
inclusion. Their exact native mates do so as well. The genuine original
positive terminal-horn Source Iso and actual projective monicity then
identify the SAME physical minimal critical edge map with its original
full interval-chart mate, preserving its entire original base record.
-/

noncomputable section
universe u
open CategoryTheory Limits Opposite
open scoped Simplicial

namespace SSet.Marked
open CoherentWeight CategoryTheory.CoherentRealization
attribute [local instance] markedSimplicialCategory enrichedDiagramCategory vertexDecidableEq

/-- The actual whole minimal critical interval operator retains the SAME full original horn inclusion. -/
theorem coneCriticalEdgeMinimalHornOperator_inclusion (n : ℕ) :
    coneCriticalEdgeMinimalHornOperator n ≫
      (enrichedDiagramRestrict (coneCriticalEdgeIndex n)).map
        (coneRootHornDiagramInclusion (Fin.last (n + 2))) = coneOperator (coneCriticalEdgeOrder.{u} n) := by
  apply EnrichedDiagramMap.ext
  funext i
  let k := coneCriticalEdgeOrder.{u} n i.unop.as
  let e := coneRootHornAboveIso (Fin.last (n + 2)) (coneCriticalEdgePositive n i.unop.as)
  have he : e.inv ≫ coneRootHornInclusion (Fin.last (n + 2)) k = 𝟙 _ :=
    (congrArg (fun f => e.inv ≫ f)
      (coneRootHornAboveIso_hom (Fin.last (n + 2)) (coneCriticalEdgePositive n i.unop.as))).symm.trans e.inv_hom_id
  change (coneImage (coneCriticalEdgeOrder n) i.unop.as ≫ e.inv) ≫
    coneRootHornInclusion (Fin.last (n + 2)) k = coneImage (coneCriticalEdgeOrder n) i.unop.as
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun f => coneImage (coneCriticalEdgeOrder n) i.unop.as ≫ f) he).trans (Category.comp_id _))

/-- The SAME full sharp original critical interval operator retains its complete critically marked horn inclusion. -/
theorem coneCriticalEdgeSharpHornOperator_inclusion (n : ℕ) :
    coneCriticalEdgeSharpHornOperator n ≫
      (enrichedDiagramRestrict (coneCriticalEdgeIndex n)).map (coneCriticalHornInclusion n) =
        coneCriticalEdgeSharpOperator.{u} n := by
  apply EnrichedDiagramMap.ext
  funext i
  let k := coneCriticalEdgeOrder.{u} n i.unop.as
  let e := coneCriticalHornAboveIso n (coneCriticalEdgePositive n i.unop.as)
  have he : e.inv ≫ coneCriticalHornCoefficientInclusion n k = 𝟙 _ :=
    (congrArg (fun f => e.inv ≫ f)
      (coneCriticalHornAboveIso_hom n (coneCriticalEdgePositive n i.unop.as))).symm.trans e.inv_hom_id
  change (coneCriticalEdgeSharpWeight n i.unop.as ≫ e.inv) ≫
    coneCriticalHornCoefficientInclusion n k = coneCriticalEdgeSharpWeight n i.unop.as
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun f => coneCriticalEdgeSharpWeight n i.unop.as ≫ f) he).trans (Category.comp_id _))

/-- The same entire original minimal interval chart mate preserves the original full horn inclusion. -/
theorem coneCriticalHornEdgeMap_inclusion (n : ℕ) :
    coneCriticalHornEdgeMap n ≫ coneRootHornDiagramInclusion (Fin.last (n + 2)) = coneCriticalConeEdgeMap.{u} n := by
  let j := coneCriticalEdgeIndex.{u} n
  apply (EnrichedLeftKan.universalHomEquiv j (coneDiagram 1) (coneDiagram (n + 2))).injective
  have h := EnrichedLeftKan.universalHomEquiv_natural_right j (coneDiagram 1)
    (coneCriticalHornEdgeMap n) (coneRootHornDiagramInclusion (Fin.last (n + 2)))
  rw [coneCriticalHornEdgeMap_homEquiv] at h
  exact h.trans ((coneCriticalEdgeMinimalHornOperator_inclusion n).trans (coneCriticalConeEdgeMap_homEquiv n).symm)

/-- The SAME whole original sharp critical interval mate preserves precisely the critically marked full horn
inclusion. -/
theorem coneCriticalHornSharpEdgeMap_inclusion (n : ℕ) :
    coneCriticalHornSharpEdgeMap n ≫ coneCriticalHornInclusion n = coneCriticalConeSharpEdgeMap.{u} n := by
  let j := coneCriticalEdgeIndex.{u} n
  apply (EnrichedLeftKan.universalHomEquiv j (sharpConeDiagram 1) (coneCriticalDiagram n)).injective
  have h := EnrichedLeftKan.universalHomEquiv_natural_right j (sharpConeDiagram 1)
    (coneCriticalHornSharpEdgeMap n) (coneCriticalHornInclusion n)
  rw [coneCriticalHornSharpEdgeMap_homEquiv] at h
  exact h.trans ((coneCriticalEdgeSharpHornOperator_inclusion n).trans (coneCriticalConeSharpEdgeMap_homEquiv n).symm)

/-- The entire original minimal native critical interval mate retains the SAME original supported terminal horn
attaching map. -/
theorem nativeCriticalHornEdgeMap_inclusion (B : SSet.{u}) (n : ℕ) (σ : B _⦋n + 2⦌) :
    nativeCriticalHornEdgeMap B n σ ≫ nativeSupportedRootHornChartMap B σ (Fin.last (n + 2)) =
      nativeCriticalConeEdgeMap B n σ := by
  let L := EnrichedLeftKan.leftExtension (EnrichedFunctor.opposite (simplexInto B σ))
  exact (L.map_comp _ _).symm.trans ((congrArg L.map (coneCriticalHornEdgeMap_inclusion n)).trans rfl)

/-- The SAME full sharp native critical interval mate keeps the entire critically marked supported horn attaching
map. -/
theorem nativeCriticalHornSharpEdgeMap_inclusion (B : SSet.{u}) (n : ℕ) (σ : B _⦋n + 2⦌) :
    nativeCriticalHornSharpEdgeMap B n σ ≫ nativeCriticalSupportedHornChartMap B n σ =
      nativeCriticalConeSharpEdgeMap B n σ := by
  let L := EnrichedLeftKan.leftExtension (EnrichedFunctor.opposite (simplexInto B σ))
  exact (L.map_comp _ _).symm.trans ((congrArg L.map (coneCriticalHornSharpEdgeMap_inclusion n)).trans rfl)

/-- The entire original native supported horn marking square retains its SAME critical attaching map and full
original simplex marking. -/
theorem nativeCriticalHornMarkingChartMap_inclusion (B : SSet.{u}) (n : ℕ) (σ : B _⦋n + 2⦌) :
    nativeCriticalHornMarkingChartMap B n σ ≫ nativeCriticalSupportedHornChartMap B n σ =
      nativeSupportedRootHornChartMap B σ (Fin.last (n + 2)) ≫ nativeCriticalSimplexMarkingChartMap B n σ := by
  let L := EnrichedLeftKan.leftExtension (EnrichedFunctor.opposite (simplexInto B σ))
  exact (L.map_comp _ _).symm.trans
    ((congrArg L.map (coneCriticalHornDiagramMark_inclusion n)).trans (L.map_comp _ _))

/-- The original terminal horn is an actual positive omitted coordinate in every original critical arity. -/
theorem nativeCriticalLastPositive (n : ℕ) : (0 : Fin (n + 3)) < Fin.last (n + 2) := by
  change 0 < n + 2
  omega

/-- The SAME entire original minimally marked terminal horn has its genuine full native supported source isomorphism. -/
def nativeCriticalMinimalHornSourceIso (B : SSet.{u}) (n : ℕ) (σ : B _⦋n + 2⦌) :
    nativeSubcomplexChart B (n + 2) σ (horn (n + 2) (Fin.last (n + 2))) ≅
      nativeSupportedRootHornChart B σ (Fin.last (n + 2)) :=
  nativePositiveHornSourceIso B σ (Fin.last (n + 2)) (nativeCriticalLastPositive n)

/-- Its SAME whole original attaching map is retained by the actual full terminal-horn source isomorphism. -/
theorem nativeCriticalMinimalHornSourceIso_attachment (B : SSet.{u}) (n : ℕ) (σ : B _⦋n + 2⦌) :
    (nativeCriticalMinimalHornSourceIso B n σ).hom ≫ nativeSupportedRootHornChartMap B σ (Fin.last (n + 2)) =
      nativeHornChartMap B (n + 2) (Fin.last (n + 2)) σ :=
  nativePositiveHornSourceIso_attachment B σ (Fin.last (n + 2)) (nativeCriticalLastPositive n)

/-- The SAME physical original minimal critical edge-to-horn map is its entire native interval mate through the
actual source and composition isomorphisms. -/
theorem nativeCriticalMinimalHornEdge_image (B : SSet.{u}) (n : ℕ) (σ : B _⦋n + 2⦌) :
    (nativeStraightening B).map (nativeCriticalMinimalHornEdgeOverMap B n σ) ≫
      (nativeCriticalMinimalHornSourceIso B n σ).hom =
    (nativeSimplexImageIso B 1 (nativeCriticalBaseEdge B n σ)).hom ≫
      ((nativeCriticalMinimalEdgeCompositionIso B n σ).inv ≫ nativeCriticalHornEdgeMap B n σ) := by
  let S := nativeStraightening B
  let a := S.map (nativeCriticalMinimalHornEdgeOverMap B n σ)
  let e := nativeSimplexImageIso B 1 (nativeCriticalBaseEdge B n σ)
  let d := nativeSimplexImageIso B (n + 2) σ
  let κ := (nativeCriticalMinimalHornSourceIso B n σ).hom
  let m := nativeSupportedRootHornChartMap B σ (Fin.last (n + 2))
  let _ : Mono m := nativeSupportedRootHornChartMap_mono_all B σ (Fin.last (n + 2))
  apply (cancel_mono m).mp
  have hl : (a ≫ κ) ≫ m = e.hom ≫ nativeSimplexChartRestriction B (nativeCriticalEdgeOperator.{u} n) σ := by
    have h₀ : (a ≫ κ) ≫ m = a ≫ (κ ≫ m) := Category.assoc _ _ _
    have h₁ : a ≫ (κ ≫ m) = a ≫ nativeHornChartMap B (n + 2) (Fin.last (n + 2)) σ :=
      congrArg (fun f => a ≫ f) (nativeCriticalMinimalHornSourceIso_attachment B n σ)
    have h₂ : a ≫ nativeHornChartMap B (n + 2) (Fin.last (n + 2)) σ =
        (a ≫ S.map (nativeSubcomplexInclusion B (n + 2) σ (horn (n + 2) (Fin.last (n + 2))))) ≫ d.hom :=
      (Category.assoc _ _ _).symm
    have h₃ : (a ≫ S.map (nativeSubcomplexInclusion B (n + 2) σ (horn (n + 2) (Fin.last (n + 2))))) ≫ d.hom =
        S.map (nativeCriticalMinimalHornEdgeOverMap B n σ ≫
          nativeSubcomplexInclusion B (n + 2) σ (horn (n + 2) (Fin.last (n + 2)))) ≫ d.hom :=
      congrArg (fun f => f ≫ d.hom) (S.map_comp _ _).symm
    have h₄ : S.map (nativeCriticalMinimalHornEdgeOverMap B n σ ≫
        nativeSubcomplexInclusion B (n + 2) σ (horn (n + 2) (Fin.last (n + 2)))) ≫ d.hom =
        S.map (nativeSimplexRestriction B (nativeCriticalEdgeOperator.{u} n) σ) ≫ d.hom :=
      congrArg (fun f => S.map f ≫ d.hom) (nativeCriticalMinimalHornEdgeOverMap_inclusion B n σ)
    have h₅ : S.map (nativeSimplexRestriction B (nativeCriticalEdgeOperator.{u} n) σ) ≫ d.hom =
        e.hom ≫ nativeSimplexChartRestriction B (nativeCriticalEdgeOperator.{u} n) σ :=
      (nativeSimplexChartRestriction_square B (nativeCriticalEdgeOperator.{u} n) σ).symm
    exact h₀.trans (h₁.trans (h₂.trans (h₃.trans (h₄.trans h₅))))
  have hr : (e.hom ≫ ((nativeCriticalMinimalEdgeCompositionIso B n σ).inv ≫ nativeCriticalHornEdgeMap B n σ)) ≫ m =
      e.hom ≫ nativeSimplexChartRestriction B (nativeCriticalEdgeOperator.{u} n) σ := by
    calc
      _ = e.hom ≫ ((nativeCriticalMinimalEdgeCompositionIso B n σ).inv ≫ (nativeCriticalHornEdgeMap B n σ ≫ m)) := by
        simp only [Category.assoc]
      _ = e.hom ≫ ((nativeCriticalMinimalEdgeCompositionIso B n σ).inv ≫ nativeCriticalConeEdgeMap B n σ) :=
        congrArg (fun f => e.hom ≫ ((nativeCriticalMinimalEdgeCompositionIso B n σ).inv ≫ f))
          (nativeCriticalHornEdgeMap_inclusion B n σ)
      _ = e.hom ≫ nativeSimplexChartRestriction B (nativeCriticalEdgeOperator.{u} n) σ :=
        congrArg (fun f => e.hom ≫ f) (nativeCriticalMinimalEdgeComposition_attachment B n σ)
  exact hl.trans hr.symm

end SSet.Marked

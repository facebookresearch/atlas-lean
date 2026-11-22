/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.NativeSharpMarkingChart
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.EnrichedLeftKanFreeNaturality

/-!
# Exact original unit readback of the native sharp marking attachment

The actual whole marking cell has the original underlying identity.
The original pullback adjunction therefore reads its minimal and sharp
edge as the same raw coherent edge. The genuine native chart adjunction
reads the entire original cone maximalization, retaining the unchanged
base and section maps in the actual full marking-cell unit equation.
-/

noncomputable section
universe u
open CategoryTheory Limits Opposite
open scoped Simplicial

namespace SSet.Marked
open CoherentWeight CategoryTheory.CoherentRealization
attribute [local instance] markedSimplicialCategory enrichedDiagramCategory

/-- Precomposition with the unchanged original whole native marking cell keeps exactly the same original coherent
unstraightening edge and complete base data. -/
theorem nativeMarkingCell_un_raw (B : SSet.{u}) (σ : B _⦋1⦌) (F : EnrichedDiagram (realization B)ᵒᵖ)
    (f : nativeSharpBasis B σ ⟶ (nativeUnstraightening B).obj F) :
    (nativeSimplexUnHomEquiv B 1 σ F (nativeMarkingCell B σ ≫ f)).val = nativeSharpUnRaw B σ F f := by
  let a := Over.mapPullbackAdj (maximal.map (unit B))
  let L := Over.map (maximal.map (unit B))
  let K := nativeSimplexBasis B 1 σ
  let E := nativeSharpBasis B σ
  let U := coherentUnstraighteningFunctor (realization B)
  let t := (a.homEquiv E (U.obj F)).symm f
  have h := a.homEquiv_naturality_left_symm (nativeMarkingCell B σ) f
  have ht : (L.map (nativeMarkingCell B σ) ≫ t).left.hom = t.left.hom := Category.id_comp _
  exact (nativeSimplexUnHomEquiv_val B 1 σ F (nativeMarkingCell B σ ≫ f)).trans
    ((congrArg (fun g : L.obj K ⟶ U.obj F => SSet.yonedaEquiv g.left.hom) h).trans
      (congrArg SSet.yonedaEquiv ht))

/-- The actual entire sharp marking chart map reads precisely the original whole marking cell followed by its
unchanged original sharp chart Hom map. -/
theorem nativeSharpMarkingChartMap_homEquiv (B : SSet.{u}) (σ : B _⦋1⦌)
    (F : EnrichedDiagram (realization B)ᵒᵖ) (g : nativeSharpChart B σ ⟶ F) :
    nativeSimplexChartHomEquiv B 1 σ F (nativeSharpMarkingChartMap B σ ≫ g) =
      nativeMarkingCell B σ ≫ nativeSharpChartHomEquiv B σ F g := by
  let j := EnrichedFunctor.opposite (simplexInto B σ)
  let a := EnrichedLeftKan.universalHomEquiv j (sharpConeDiagram 1) F g
  apply (nativeSimplexUnHomEquiv B 1 σ F).injective
  apply Subtype.ext
  have hl := congrArg Subtype.val
    (nativeSimplexChartHomEquiv_section B 1 σ F (nativeSharpMarkingChartMap B σ ≫ g))
  have hn := enrichedLeftKan_universal_map_post j (coneSharp 1) g
  have hg := nativeSharpUnRaw_inverseSection B σ F a
  have hr := nativeMarkingCell_un_raw B σ F (nativeSharpChartHomEquiv B σ F g)
  exact hl.trans ((congrArg (fun q => ((fixedSectionEquiv F (simplexInto B σ)).symm q).val) hn).trans
    (hg.symm.trans hr.symm))

end SSet.Marked

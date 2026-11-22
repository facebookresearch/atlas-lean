/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.NativeProperBoundaryFace

/-!
# Exact original proper native boundary maps followed by actual sections

The original proper native face map has its unchanged supported cone
operator and actual root-boundary unit. Postcomposing an actual target
map retains its whole original universal section and genuine coherent
base transport. The original transport naturality and unit equations
are proved on every full marked coefficient.
-/

noncomputable section
universe u
open CategoryTheory Opposite
open scoped Simplicial

namespace SSet.Marked
open CoherentWeight CategoryTheory.CoherentRealization
attribute [local instance] markedSimplicialCategory enrichedDiagramCategory

/-- Every original proper native boundary map followed by an actual target map reads its same full original
supported operator and genuine whole native section, with original coherent base transport. -/
theorem nativeProperBoundaryFace_post_section (B : SSet.{u}) {n m : ℕ}
    (f : ⦋n⦌ ⟶ ⦋m⦌) (σ : B _⦋m⦌) (hf : ¬ Function.Surjective f.toOrderHom.uliftMap)
    (F : EnrichedDiagram (realization B)ᵒᵖ) (g : nativeRootBoundaryChart B m σ ⟶ F) :
    EnrichedLeftKan.universalHomEquiv
      (EnrichedFunctor.opposite (simplexInto B (B.map f.op σ))) (coneDiagram n) F
      (nativeProperBoundaryFaceMap B f σ hf ≫ g) =
      (coneProperBoundaryOperator f.toOrderHom.uliftMap hf ≫
        (enrichedDiagramRestrict (EnrichedFunctor.opposite (indexMap f.toOrderHom.uliftMap))).map
          (EnrichedLeftKan.universalHomEquiv (EnrichedFunctor.opposite (simplexInto B σ))
            (coneRootBoundaryDiagram m) F g)) ≫ (eqToHom (nativeChartBase_restriction_comp B f σ)).app F := by
  let j := EnrichedFunctor.opposite (simplexInto B σ)
  let R := enrichedDiagramRestrict j
  let Rf := enrichedDiagramRestrict (EnrichedFunctor.opposite (simplexInto B (B.map f.op σ)))
  let η := EnrichedLeftKan.unit j (coneRootBoundaryDiagram m)
  let φ := coneProperBoundaryOperator f.toOrderHom.uliftMap hf
  let V := EnrichedLeftKan.universalHomEquiv j (coneRootBoundaryDiagram m) F g
  let h := nativeChartBase_restriction_comp B f σ
  let tR := (eqToHom h).app (nativeRootBoundaryChart B m σ)
  let tF := (eqToHom h).app F
  have hfront : EnrichedLeftKan.universalHomEquiv
      (EnrichedFunctor.opposite (simplexInto B (B.map f.op σ))) (coneDiagram n) F
      (nativeProperBoundaryFaceMap B f σ hf ≫ g) = nativeProperBoundaryFaceSection B f σ hf ≫ Rf.map g :=
    (EnrichedLeftKan.universalHomEquiv_natural_right
      (EnrichedFunctor.opposite (simplexInto B (B.map f.op σ))) (coneDiagram n)
      (nativeProperBoundaryFaceMap B f σ hf) g).trans
        (congrArg (fun p => p ≫ Rf.map g) (nativeProperBoundaryFaceMap_homEquiv B f σ hf))
  apply EnrichedDiagramMap.ext
  funext i
  let x := op ((indexMap f.toOrderHom.uliftMap).obj i.unop)
  let a := φ.app i
  let b := η.app x
  let c := (R.map g).app x
  let d := V.app x
  let p := tR.app i
  let q := tF.app i
  let z := (Rf.map g).app i
  have ht : p ≫ z = c ≫ q :=
    (congrArg (fun k => k.app i) ((eqToHom h).naturality g)).symm
  have hu : b ≫ c = d :=
    (congrArg (fun k => k.app x) (EnrichedLeftKan.universalHomEquiv_unit j (coneRootBoundaryDiagram m) F g)).symm
  have ha : (EnrichedLeftKan.universalHomEquiv
      (EnrichedFunctor.opposite (simplexInto B (B.map f.op σ))) (coneDiagram n) F
      (nativeProperBoundaryFaceMap B f σ hf ≫ g)).app i = ((a ≫ b) ≫ p) ≫ z :=
    congrArg (fun k => k.app i) hfront
  exact ha.trans
    ((Category.assoc _ _ _).trans
      ((congrArg (fun k => (a ≫ b) ≫ k) ht).trans
        ((Category.assoc _ _ _).symm.trans
          ((congrArg (fun k => k ≫ q) (Category.assoc a b c)).trans
            (congrArg (fun k => (a ≫ k) ≫ q) hu)))))

end SSet.Marked

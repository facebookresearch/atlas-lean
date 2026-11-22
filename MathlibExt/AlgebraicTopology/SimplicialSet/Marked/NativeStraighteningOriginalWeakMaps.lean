/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.NativeCoherentFibrantHomotopyTesting
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.NativeUnstraighteningExactCartesianMarking

/-!
# The same native straightening preserves full original Cartesian weak maps

Full original Cartesian weakness gives all original relative homotopy
tests into the actual intrinsic Cartesian Un of every fibrant coherent
diagram. The genuine original native adjunction identifies those tests
with actual coherent-model homotopy classes, preserving precomposition
by the whole original map. The native objects are actually cofibrant.
Actual coherent-model homotopy recognition therefore proves weakness
of the same entire native image in both original models. No Quillen,
weak-image, filler or source-fibration-class equality is a premise.
-/

noncomputable section
universe u
open CategoryTheory Limits HomotopicalAlgebra MorphismProperty Opposite
open scoped Simplicial

namespace SSet.Marked
open CategoryTheory.CoherentRealization
attribute [local instance] markedSimplicialCategory enrichedDiagramCategory coefficientMarkedModelCategory

/-- Every full original Cartesian mapping-test weak arrow has a weak image under the same actual native
straightening over an arbitrary original quasicategory base, without Kan or source fibrancy hypotheses. -/
theorem nativeStraightening_original_cartesianWeak (B : SSet.{u}) [Quasicategory B]
    {X Y : Over (max B)} (f : X ⟶ Y) (hf : cartesianWeakEquivalences B f) :
    let _ := coherentDiagramModelCategory B
    WeakEquivalence ((nativeStraightening B).map f) := by
  let _ := coherentDiagramModelCategory B
  dsimp only
  apply nativeCoherentFibrantHomotopyTesting_weak B ((nativeStraightening B).map f)
    (nativeStraightening_object_isCofibrant B X) (nativeStraightening_object_isCofibrant B Y)
  intro F hF
  let EX := nativeOriginalRightHomotopyClassEquiv B X F hF
  let EY := nativeOriginalRightHomotopyClassEquiv B Y F hF
  let T := (nativeUnstraightening B).obj F
  have hT : cartesianObjects B T := nativeUnstraightening_original_intrinsic B F hF
  have htest : Function.Bijective ((relativeIntervalCylinder (max B)).homotopyClassPrecomp f T) :=
    (cartesianRelativeHomotopyTesting_iff f).mp
      (cartesianWeakEquivalences_le_relativeHomotopyTesting B f hf) T hT
  constructor
  · intro a b hab
    apply EY.injective
    apply htest.1
    exact (nativeOriginalRightHomotopyClassEquiv_pre B f F hF a).symm.trans
      ((congrArg EX hab).trans (nativeOriginalRightHomotopyClassEquiv_pre B f F hF b))
  · intro c
    obtain ⟨d, hd⟩ := htest.2 (EX c)
    refine ⟨EY.symm d, EX.injective ?_⟩
    exact (nativeOriginalRightHomotopyClassEquiv_pre B f F hF (EY.symm d)).trans
      ((congrArg ((relativeIntervalCylinder (max B)).homotopyClassPrecomp f T)
        (EY.apply_symm_apply d)).trans hd)

/-- The same whole native straightening map preserves actual weak equivalences in BOTH original model structures,
with no fibrancy hypothesis on either original source object. -/
theorem nativeStraightening_original_weakEquivalence (B : SSet.{u}) [Quasicategory B]
    {X Y : Over (max B)} (f : X ⟶ Y) :
    let _ := markedCofibrationStructure (max B)
    let _ := cartesianMarkedFibrationStructure B
    let _ := cartesianMarkedWeakStructure B
    let _ := cartesianMarkedModelCategory B
    let _ := coherentDiagramModelCategory B
    WeakEquivalence f → WeakEquivalence ((nativeStraightening B).map f) := by
  let _ := markedCofibrationStructure (max B)
  let _ := cartesianMarkedFibrationStructure B
  let _ := cartesianMarkedWeakStructure B
  let _ := cartesianMarkedModelCategory B
  let _ := coherentDiagramModelCategory B
  dsimp only
  intro hf
  have hf' := (weakEquivalence_iff f).mp hf
  change cartesianWeakEquivalences B f at hf'
  exact nativeStraightening_original_cartesianWeak B f hf'

/-- Every actual marked coefficient of the same whole native image of an original Cartesian weak map is weak in the
unchanged original coefficient model. -/
theorem nativeStraightening_original_evaluationWeak (B : SSet.{u}) [Quasicategory B]
    {X Y : Over (max B)} (f : X ⟶ Y) (hf : cartesianWeakEquivalences B f)
    (c : (realization B)ᵒᵖ) :
    let _ := coefficientMarkedModelCategory.{u}
    WeakEquivalence (((nativeStraightening B).map f).app c) := by
  let _ := coefficientMarkedModelCategory.{u}
  dsimp only
  let _ := coherentDiagramModelCategory B
  have hw := (weakEquivalence_iff ((nativeStraightening B).map f)).mp
    (nativeStraightening_original_cartesianWeak B f hf)
  change coherentDiagramWeakEquivalences B ((nativeStraightening B).map f) at hw
  exact (weakEquivalence_iff _).mpr
    ((EvaluationTransfer.evaluationProperty_iff
      (fun c : (realization B)ᵒᵖ => enrichedDiagramEvaluation _ c)
        (weakEquivalences Marked.{u}) ((nativeStraightening B).map f)).mp hw c)

end SSet.Marked

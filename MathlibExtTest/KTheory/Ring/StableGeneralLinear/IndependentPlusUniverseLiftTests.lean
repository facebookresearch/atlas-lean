/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.KTheory.Ring.StableGeneralLinear.IndependentPlusUniverseLift
public import Mathlib.Data.ZMod.Defs

noncomputable section

open CategoryTheory HomotopicalAlgebra
open scoped ContinuousMap

universe uR uM uObj uHom uNative uProbe

namespace IndependentPlusUniverseLiftTests

private abbrev fullTarget (R : Type uR) [Ring R] :
    TopCat.{max (max (max ((max uR uM) + 1) uObj) (max (max uR uM) uHom)) uNative} :=
  AlgebraicKTheory.StableGL.independentBGLCellTargetLift.{uR,
    max (max (max ((max uR uM) + 1) uObj) (max (max uR uM) uHom)) uNative} R

private abbrev fullSource (R : Type uR) [Ring R] :=
  AlgebraicKTheory.StableGL.independentBGLSourceLift.{uR,
    max (max (max ((max uR uM) + 1) uObj) (max (max uR uM) uHom)) uNative} R

private abbrev fullInclusion (R : Type uR) [Ring R] :
    fullSource.{uR, uM, uObj, uHom, uNative} R ⟶
      fullTarget.{uR, uM, uObj, uHom, uNative} R :=
  AlgebraicKTheory.StableGL.independentBGLCellInclusionLift.{uR,
    max (max (max ((max uR uM) + 1) uObj) (max (max uR uM) uHom)) uNative} R

/-- The full carrier really keeps separate ring, module, object, Hom and
native levels while using the same raw ring-only target. -/
example (R : Type uR) [Ring R] (b : AlgebraicKTheory.StableGL.independentBGLCellTarget R) :
    AlgebraicKTheory.StableGL.independentBGLCellTargetDown.{uR,
      max (max (max ((max uR uM) + 1) uObj) (max (max uR uM) uHom)) uNative} R
        (ULift.up b : fullTarget.{uR, uM, uObj, uHom, uNative} R) = b := by
  exact AlgebraicKTheory.StableGL.independentBGLCellTargetDown_apply.{uR,
    max (max (max ((max uR uM) + 1) uObj) (max (max uR uM) uHom)) uNative} R
      (ULift.up b : fullTarget.{uR, uM, uObj, uHom, uNative} R)

example (R : Type uR) [Ring R] :
    TopCat.IsLocalCoefficientHomologyEquivalence
      (fullInclusion.{uR, uM, uObj, uHom, uNative} R) :=
  AlgebraicKTheory.StableGL.independentBGLCellInclusionLift_allLocalCoefficients R

example (R : Type uR) [Ring R] (b : fullTarget.{uR, uM, uObj, uHom, uNative} R) :
    TopCat.IsAcyclicMapAt (fullInclusion.{uR, uM, uObj, uHom, uNative} R) b :=
  AlgebraicKTheory.StableGL.independentBGLCellInclusionLift_acyclic_all R b

example (R : Type uR) [Ring R] :
    MonoidHom.ker (FundamentalGroup.mapOfEq
      (fullInclusion.{uR, uM, uObj, uHom, uNative} R).hom
      (AlgebraicKTheory.StableGL.independentBGLCellInclusionLift_point R)) =
        AlgebraicKTheory.StableGL.BGLPlusSubgroupLift.{uR,
          max (max (max ((max uR uM) + 1) uObj) (max (max uR uM) uHom)) uNative} R :=
  AlgebraicKTheory.StableGL.independentBGLCellInclusionLift_kernel R

example (R : Type uR) [Ring R] :
    Function.Surjective (FundamentalGroup.mapOfEq
      (fullInclusion.{uR, uM, uObj, uHom, uNative} R).hom
      (AlgebraicKTheory.StableGL.independentBGLCellInclusionLift_point R)) :=
  AlgebraicKTheory.StableGL.independentBGLCellInclusionLift_pi1_surjective R

example (R : Type uR) [Ring R] :
    ∃ C : TopCat.{max (max (max ((max uR uM) + 1) uObj)
        (max (max uR uM) uHom)) uNative}, ∃ _ : T2Space C,
      ∃ _ : Topology.CWComplex (Set.univ : Set C),
        Nonempty (C ≃ₕ fullTarget.{uR, uM, uObj, uHom, uNative} R) :=
  AlgebraicKTheory.StableGL.independentBGLCellTargetLift_cwType R

/-- The carrier transport introduces no nontrivial-ring assumption. -/
example : TopCat.IsLocalCoefficientHomologyEquivalence
    (AlgebraicKTheory.StableGL.independentBGLCellInclusionLift.{0, uNative} (ZMod 1)) :=
  AlgebraicKTheory.StableGL.independentBGLCellInclusionLift_allLocalCoefficients (ZMod 1)

/-- The original two/three-cell composite remains the actual inclusion. -/
example (R : Type uR) [Ring R] :
    fullInclusion.{uR, uM, uObj, uHom, uNative} R =
      AlgebraicKTheory.StableGL.independentBGLTwoCellInclusionLift R ≫
        AlgebraicKTheory.StableGL.independentBGLThreeCellInclusionLift R :=
  AlgebraicKTheory.StableGL.independentBGLCellInclusionLift_eq_two_three R

private local instance originalSourcePC (R : Type uR) [Ring R] :
    PathConnectedSpace (AlgebraicKTheory.StableGL.ordinaryBGL R) :=
  CategoryTheory.groupClassifyingOrdinary_pathConnected (AlgebraicKTheory.StableGL R)

private local instance originalSourceT2 (R : Type uR) [Ring R] :
    T2Space (AlgebraicKTheory.StableGL.ordinaryBGL R) :=
  SSet.realization_t2Space (AlgebraicKTheory.StableGL.classifyingNerve R)

private local instance originalSourceCW (R : Type uR) [Ring R] :
    Topology.CWComplex (Set.univ : Set (AlgebraicKTheory.StableGL.ordinaryBGL R)) :=
  SSet.instCWComplexToTop (AlgebraicKTheory.StableGL.classifyingNerve R)

/-- The first stage is the literal lift of the original whole-space two-cell inclusion. -/
example (R : Type uR) [Ring R] (x : AlgebraicKTheory.StableGL.ordinaryBGL R) :
    AlgebraicKTheory.StableGL.independentBGLTwoCellInclusionLift.{uR, uNative} R (ULift.up x) =
      ULift.up (AlgebraicTopology.LoopCellAttachment.inclusion
        (AlgebraicKTheory.StableGL.ordinaryBGL R)
        (AlgebraicKTheory.StableGL.ordinaryBGLBasepoint R)
        (AlgebraicKTheory.StableGL.BGLPlusSubgroup R) x) := by
  rfl

/-- The second stage is the literal lift of the original three-cell inclusion. -/
example (R : Type uR) [Ring R]
    (y : AlgebraicTopology.LoopCellAttachment.space
      (AlgebraicKTheory.StableGL.ordinaryBGL R)
      (AlgebraicKTheory.StableGL.ordinaryBGLBasepoint R)
      (AlgebraicKTheory.StableGL.BGLPlusSubgroup R)) :
    AlgebraicKTheory.StableGL.independentBGLThreeCellInclusionLift.{uR, uNative} R (ULift.up y) =
      ULift.up (AlgebraicTopology.LoopCellRegularThreeComparison.originalThreeInclusion
        (AlgebraicKTheory.StableGL.ordinaryBGL R)
        (AlgebraicKTheory.StableGL.ordinaryBGLBasepoint R)
        (AlgebraicKTheory.StableGL.BGLPlusSubgroup R) y) := by
  rfl

/-- Each actual original characteristic two-cell keeps its chosen boundary corner. -/
example (R : Type uR) [Ring R] (p : AlgebraicKTheory.StableGL.BGLPlusSubgroup R) :
    (TopCat.uliftFunctor.{uNative, uR}.map
      (AlgebraicTopology.LoopCellAttachment.cell
        (AlgebraicKTheory.StableGL.ordinaryBGL R)
        (AlgebraicKTheory.StableGL.ordinaryBGLBasepoint R)
        (AlgebraicKTheory.StableGL.BGLPlusSubgroup R) p))
      (ULift.up ((Topology.CWComplex.classicalCellDiskPair.{uR} 2).map
        Topology.CWComplex.classicalCellSquareBottomLeft.{uR})) =
      AlgebraicKTheory.StableGL.independentBGLTwoCellInclusionLift.{uR, uNative} R
        (AlgebraicKTheory.StableGL.independentBGLSourcePointLift.{uR, uNative} R) := by
  change ULift.up (AlgebraicTopology.LoopCellAttachment.cell
      (AlgebraicKTheory.StableGL.ordinaryBGL R)
      (AlgebraicKTheory.StableGL.ordinaryBGLBasepoint R)
      (AlgebraicKTheory.StableGL.BGLPlusSubgroup R) p
      ((Topology.CWComplex.classicalCellDiskPair.{uR} 2).map
        Topology.CWComplex.classicalCellSquareBottomLeft.{uR})) =
    ULift.up (AlgebraicTopology.LoopCellAttachment.inclusion
      (AlgebraicKTheory.StableGL.ordinaryBGL R)
      (AlgebraicKTheory.StableGL.ordinaryBGLBasepoint R)
      (AlgebraicKTheory.StableGL.BGLPlusSubgroup R)
      (AlgebraicKTheory.StableGL.ordinaryBGLBasepoint R))
  exact congrArg ULift.up (AlgebraicTopology.LoopCellAttachment.cell_basepoint
    (AlgebraicKTheory.StableGL.ordinaryBGL R)
    (AlgebraicKTheory.StableGL.ordinaryBGLBasepoint R)
    (AlgebraicKTheory.StableGL.BGLPlusSubgroup R) p)

/-- Both literal stages carry the original BGL vertex to the original three-cell point. -/
example (R : Type uR) [Ring R] :
    AlgebraicKTheory.StableGL.independentBGLThreeCellInclusionLift.{uR, uNative} R
      (AlgebraicKTheory.StableGL.independentBGLTwoCellInclusionLift.{uR, uNative} R
        (AlgebraicKTheory.StableGL.independentBGLSourcePointLift.{uR, uNative} R)) =
      AlgebraicKTheory.StableGL.independentBGLCellPointLift.{uR, uNative} R := by
  have h := AlgebraicKTheory.StableGL.independentBGLCellInclusionLift_point.{uR, uNative} R
  rw [AlgebraicKTheory.StableGL.independentBGLCellInclusionLift_eq_two_three] at h
  exact h

end IndependentPlusUniverseLiftTests

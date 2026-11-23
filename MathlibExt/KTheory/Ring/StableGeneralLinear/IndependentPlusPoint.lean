/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.KTheory.Ring.StableGeneralLinear.IndependentPlusConstruction
public import MathlibExt.AlgebraicTopology.PlusConstruction.ClassicalMappingGeometry
public import MathlibExt.CategoryTheory.ClassifyingSpace.Group

/-!
# The actual independently constructed BGL plus and its point

These maps are the original two/three-cell target, inclusion and marked
point. Their plus, all-local-coefficient and connectedness conclusions
reuse the existing complete classical construction. Point cofibrancy
comes from the original realized vertex followed by the actual cell
cofibrations, not a selected based-model witness.
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory HomotopicalAlgebra AlgebraicTopology
open scoped ContinuousMap TopCat.modelCategory

universe u

namespace AlgebraicKTheory.StableGL

/-- Path connectedness is derived from the actual original one-object nerve. -/
public local instance ordinaryBGLPathConnected (R : Type u) [Ring R] :
    PathConnectedSpace (ordinaryBGL R) := by
  let K : SSet.{u} := classifyingNerve R
  letI : K.IsConnected :=
    CategoryTheory.groupClassifyingNerve_isConnected (StableGL R)
  exact SSet.pathConnectedSpace_realization_of_isConnected K

private local instance ordinaryBGLHausdorff (R : Type u) [Ring R] :
    T2Space (ordinaryBGL R) := SSet.realization_t2Space (classifyingNerve R)

private local instance ordinaryBGLClassicalCW (R : Type u) [Ring R] :
    Topology.CWComplex (Set.univ : Set (ordinaryBGL R)) :=
  SSet.instCWComplexToTop (classifyingNerve R)

private local instance ordinaryBGLPerfectNormal (R : Type u) [Ring R] :
    (BGLPlusSubgroup R).Normal := BGLPlusSubgroup.instNormal R

private local instance ordinaryBGLPlusPerfect (R : Type u) [Ring R] :
    Group.IsPerfect (BGLPlusSubgroup R) := BGLPlusSubgroup.instIsPerfect R

/-- The SAME independently constructed actual three-cell BGL plus target. -/
public abbrev independentBGLCellTarget (R : Type u) [Ring R] : TopCat.{u} :=
  LoopCellRegularThreeComparison.originalThree
    (ordinaryBGL R) (ordinaryBGLBasepoint R) (BGLPlusSubgroup R)

/-- The original composite of its two-cell and three-cell inclusions. -/
public abbrev independentBGLCellInclusion (R : Type u) [Ring R] :
    ordinaryBGL R ⟶ independentBGLCellTarget R :=
  LoopCellAttachment.inclusion (ordinaryBGL R) (ordinaryBGLBasepoint R) (BGLPlusSubgroup R) ≫
    LoopCellRegularThreeComparison.originalThreeInclusion
      (ordinaryBGL R) (ordinaryBGLBasepoint R) (BGLPlusSubgroup R)

/-- The original marked point of that actual cell target. -/
public abbrev independentBGLCellPoint (R : Type u) [Ring R] : independentBGLCellTarget R :=
  LoopCellRegularThreeComparison.originalThreeBasePoint
    (ordinaryBGL R) (ordinaryBGLBasepoint R) (BGLPlusSubgroup R)

/-- The named target is the SAME original three-cell construction. -/
public theorem independentBGLCellTarget_eq_original (R : Type u) [Ring R] :
    independentBGLCellTarget R =
      LoopCellRegularThreeComparison.originalThree
        (ordinaryBGL R) (ordinaryBGLBasepoint R) (BGLPlusSubgroup R) := rfl

/-- The named inclusion is the SAME two/three-cell composite, as a morphism equality. -/
public theorem independentBGLCellInclusion_eq_original (R : Type u) [Ring R] :
    independentBGLCellInclusion R =
      LoopCellAttachment.inclusion (ordinaryBGL R) (ordinaryBGLBasepoint R) (BGLPlusSubgroup R) ≫
        LoopCellRegularThreeComparison.originalThreeInclusion
          (ordinaryBGL R) (ordinaryBGLBasepoint R) (BGLPlusSubgroup R) := rfl

/-- The named point is the SAME original marked vertex, as a carrier equality. -/
public theorem independentBGLCellPoint_eq_original (R : Type u) [Ring R] :
    independentBGLCellPoint R =
      LoopCellRegularThreeComparison.originalThreeBasePoint
        (ordinaryBGL R) (ordinaryBGLBasepoint R) (BGLPlusSubgroup R) := rfl

/-- The literal inclusion retains its original marked point. -/
public theorem independentBGLCellInclusion_point (R : Type u) [Ring R] :
    independentBGLCellInclusion R (ordinaryBGLBasepoint R) = independentBGLCellPoint R := by
  rw [independentBGLCellInclusion_eq_original, independentBGLCellPoint_eq_original]
  rfl

/-- Plusness is derived for this literal map from the existing full
classical construction over the unchanged arbitrary ring. -/
public theorem independentBGLCellInclusion_isPlus (R : Type u) [Ring R] :
    TopCat.IsPlusConstructionAt (independentBGLCellInclusion R) (ordinaryBGLBasepoint R)
      (independentBGLCellPoint R) (independentBGLCellInclusion_point R) (BGLPlusSubgroup R) := by
  simpa only [independentBGLCellInclusion_eq_original, independentBGLCellPoint_eq_original] using
    (LoopCellIndependentPlus.original_connected_CW_plus_construction_full
      (ordinaryBGL R) (ordinaryBGLBasepoint R) (BGLPlusSubgroup R)).1

/-- The actual constructed map is an equivalence for ALL original integer
local systems, including nonflat systems. -/
public theorem independentBGLCellInclusion_allLocalCoefficients (R : Type u) [Ring R] :
    TopCat.IsLocalCoefficientHomologyEquivalence (independentBGLCellInclusion R) := by
  simpa only [independentBGLCellInclusion_eq_original] using
    (LoopCellIndependentPlus.original_connected_CW_plus_construction_full
      (ordinaryBGL R) (ordinaryBGLBasepoint R) (BGLPlusSubgroup R)).2.1

/-- The connectedness of the actual constructed target is derived. -/
public theorem independentBGLCellTarget_pathConnected (R : Type u) [Ring R] :
    PathConnectedSpace (independentBGLCellTarget R) := by
  simpa only [independentBGLCellTarget_eq_original] using
    (LoopCellIndependentPlus.original_connected_CW_plus_construction_full
      (ordinaryBGL R) (ordinaryBGLBasepoint R) (BGLPlusSubgroup R)).2.2.2.2.2.1

/-- The actual original two/three-cell composite is a cofibration. -/
public theorem independentBGLCellInclusion_cofibration (R : Type u) [Ring R] :
    Cofibration (independentBGLCellInclusion R) := by
  simpa only [independentBGLCellInclusion_eq_original] using
    LoopCellIndependentPlus.originalInclusion_cofibration
      (ordinaryBGL R) (ordinaryBGLBasepoint R) (BGLPlusSubgroup R)

/-- The SAME target's original marked point is cofibrant, through the
actual realized source vertex and actual cell inclusion. -/
public theorem independentBGLCellPoint_cofibration (R : Type u) [Ring R] :
    Cofibration (TopCat.const (independentBGLCellPoint R) :
      TopCat.of PUnit.{u + 1} ⟶ independentBGLCellTarget R) := by
  letI : Cofibration (TopCat.const (ordinaryBGLBasepoint R) :
      TopCat.of PUnit.{u + 1} ⟶ ordinaryBGL R) :=
    SSet.realizedVertex_pointMap_cofibration (classifyingNerve R) (classifyingVertex R)
  letI : Cofibration (independentBGLCellInclusion R) :=
    independentBGLCellInclusion_cofibration R
  have hpoint : TopCat.const (independentBGLCellPoint R) =
      (TopCat.const (ordinaryBGLBasepoint R) : TopCat.of PUnit.{u + 1} ⟶ ordinaryBGL R) ≫
        independentBGLCellInclusion R := by
    apply TopCat.hom_ext
    apply ContinuousMap.ext
    intro q
    exact (independentBGLCellInclusion_point R).symm
  rw [hpoint]
  infer_instance

end AlgebraicKTheory.StableGL

end

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.KTheory.Ring.StableGeneralLinear.IndependentPlusPoint
import MathlibExt.Topology.Category.TopCat.HomotopyFiberFundamentalGroup

/-!
# The original low-degree plus-fiber sequence

The fiber is the compact-open homotopy fiber of the independently constructed
two/three-cell inclusion `BGL(R) → BGL(R)⁺`. Its point has the original BGL
vertex and the constant path at the original plus point.

The connecting homomorphism starts at the actual cube-based second homotopy
group of that plus space and ends at the ordinary fundamental group of this
same fiber. The singular comparison and the full ending-path/strict-fiber
isomorphisms transport the original Kan connecting map. Exactness identifies
its image with the kernel of the original projection. That projection has
image the existing stable elementary subgroup.

These are the low-degree exact-sequence maps in Weibel, *The K-book*, IV.1.7,
printed pages 264–265 (official PDF pages 272–273). Centrality, injectivity of
the connecting map, and the Steinberg identification require subsequent
theorems.
-/

noncomputable section

open CategoryTheory
open scoped Topology

universe u

namespace AlgebraicKTheory.StableGL

/-- The original complete ending-path fiber of the actual independent plus inclusion. -/
abbrev independentPlusFiber (R : Type u) [Ring R] : TopCat.{u} :=
  TopCat.homotopyFiber (independentBGLCellInclusion R) (independentBGLCellPoint R)

/-- Its point has the original source vertex and the constant ending path. -/
def independentPlusFiberPoint (R : Type u) [Ring R] : independentPlusFiber R :=
  TopCat.homotopyFiberSelectedPointMap (independentBGLCellInclusion R)
    (ordinaryBGLBasepoint R) (independentBGLCellPoint R)
    (independentBGLCellInclusion_point R) PUnit.unit

/-- The source coordinate of the original plus-fiber point is the BGL vertex. -/
theorem independentPlusFiberPoint_total (R : Type u) [Ring R] :
    TopCat.homotopyFiberToTotal (independentBGLCellInclusion R) (independentBGLCellPoint R)
      (independentPlusFiberPoint R) = ordinaryBGLBasepoint R :=
  ConcreteCategory.congr_hom (TopCat.homotopyFiberSelectedPointMap_toTotal
    (independentBGLCellInclusion R) (ordinaryBGLBasepoint R)
    (independentBGLCellPoint R) (independentBGLCellInclusion_point R)) PUnit.unit

/-- The path coordinate of the original plus-fiber point is the constant path. -/
theorem independentPlusFiberPoint_path (R : Type u) [Ring R] :
    TopCat.homotopyFiberPath (independentBGLCellInclusion R) (independentBGLCellPoint R)
      (independentPlusFiberPoint R) = ContinuousMap.const TopCat.I (independentBGLCellPoint R) :=
  ConcreteCategory.congr_hom (TopCat.homotopyFiberSelectedPointMap_path
    (independentBGLCellInclusion R) (ordinaryBGLBasepoint R)
    (independentBGLCellPoint R) (independentBGLCellInclusion_point R)) PUnit.unit

/-- The ordinary fundamental-group map of the original source projection. -/
def independentPlusFiberProjection (R : Type u) [Ring R] :
    FundamentalGroup (independentPlusFiber R) (independentPlusFiberPoint R) →*
      FundamentalGroup (ordinaryBGL R) (ordinaryBGLBasepoint R) :=
  TopCat.homotopyFiberFundamentalGroupProjection (independentBGLCellInclusion R) (ordinaryBGLBasepoint R)
    (independentBGLCellPoint R) (independentBGLCellInclusion_point R)

/-- The original connecting map from the actual cube-based plus second homotopy group. -/
def independentPlusFiberConnectingHom (R : Type u) [Ring R] :
    HomotopyGroup.Pi 2 (independentBGLCellTarget R) (independentBGLCellPoint R) →*
      FundamentalGroup (independentPlusFiber R) (independentPlusFiberPoint R) :=
  TopCat.homotopyFiberConnectingHom (independentBGLCellInclusion R) (ordinaryBGLBasepoint R)
    (independentBGLCellPoint R) (independentBGLCellInclusion_point R)

/-- The actual connecting map is killed by the actual source projection. -/
@[simp]
theorem independentPlusFiberProjection_connecting (R : Type u) [Ring R]
    (a : HomotopyGroup.Pi 2 (independentBGLCellTarget R) (independentBGLCellPoint R)) :
    independentPlusFiberProjection R (independentPlusFiberConnectingHom R a) = 1 :=
  TopCat.homotopyFiberFundamentalGroupProjection_connecting _ _ _ _ a

/-- Exactness at the original fiber fundamental group, for the same connecting map. -/
theorem independentPlusFiberProjection_ker (R : Type u) [Ring R] :
    (independentPlusFiberProjection R).ker = (independentPlusFiberConnectingHom R).range := by
  ext g
  exact TopCat.homotopyFiberFundamentalGroupProjection_exact _ _ _ _ g

/-- The image of the original projection is the existing stable elementary plus subgroup. -/
theorem independentPlusFiberProjection_range (R : Type u) [Ring R] :
    (independentPlusFiberProjection R).range = BGLPlusSubgroup R :=
  (TopCat.homotopyFiberFundamentalGroupProjection_range _ _ _ _).trans (independentBGLCellInclusion_isPlus R).kernel_eq

/-- The original projection restricted to the existing stable elementary group. -/
def independentPlusFiberToStableE (R : Type u) [Ring R] :
    FundamentalGroup (independentPlusFiber R) (independentPlusFiberPoint R) →* StableE R :=
  (BGLPlusSubgroup.mulEquivStableE R).toMonoidHom.comp
    ((independentPlusFiberProjection R).codRestrict (BGLPlusSubgroup R) (fun g => by
      rw [← independentPlusFiberProjection_range R]
      exact ⟨g, rfl⟩))

/-- Every original stable elementary element is the projection of a plus-fiber loop. -/
theorem independentPlusFiberToStableE_surjective (R : Type u) [Ring R] :
    Function.Surjective (independentPlusFiberToStableE R) := by
  intro g
  let p := (BGLPlusSubgroup.mulEquivStableE R).symm g
  have hp : (p : FundamentalGroup (ordinaryBGL R) (ordinaryBGLBasepoint R)) ∈
      (independentPlusFiberProjection R).range := by
    rw [independentPlusFiberProjection_range R]
    exact p.property
  obtain ⟨a, ha⟩ := hp
  refine ⟨a, ?_⟩
  change BGLPlusSubgroup.mulEquivStableE R _ = g
  rw [← (BGLPlusSubgroup.mulEquivStableE R).apply_symm_apply g]
  apply congrArg (BGLPlusSubgroup.mulEquivStableE R)
  apply Subtype.ext
  exact ha

end AlgebraicKTheory.StableGL

end

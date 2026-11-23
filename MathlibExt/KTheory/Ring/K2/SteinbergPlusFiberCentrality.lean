/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.KTheory.Ring.SteinbergPlusFiberExtension
import MathlibExt.Topology.Category.TopCat.HomotopyFiberFundamentalGroup
import MathlibExt.GroupTheory.CentralExtension

/-!
# Centrality of the original Steinberg plus-fiber extension

The canonical connecting homomorphism of a complete homotopy fiber has central
image in its ordinary fundamental group. Specializing that public theorem to
the independent plus inclusion gives the original cube-based connecting map
and its original ending-path fiber at the selected constant-path point.

The original projection kernel is therefore central, and the existing
plus-fiber extension of the stable elementary group is a central extension.
These are the original maps in the centrality clause of Weibel IV.1.7.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

universe u

namespace AlgebraicKTheory.StableGL

/-- The unchanged original cube-π₂ connecting homomorphism has central image in the same fiber. -/
theorem independentPlusFiberConnectingHom_range_le_center (R : Type u) [Ring R] :
    (independentPlusFiberConnectingHom R).range ≤
      Subgroup.center (FundamentalGroup (independentPlusFiber R) (independentPlusFiberPoint R)) :=
  TopCat.homotopyFiberConnectingHom_range_le_center (independentBGLCellInclusion R)
    (ordinaryBGLBasepoint R) (independentBGLCellPoint R) (independentBGLCellInclusion_point R)

/-- The kernel of the original projection to the stable elementary group is central. -/
theorem independentPlusFiberToStableE_ker_le_center (R : Type u) [Ring R] :
    (independentPlusFiberToStableE R).ker ≤
      Subgroup.center (FundamentalGroup (independentPlusFiber R) (independentPlusFiberPoint R)) := by
  rw [independentPlusFiberToStableE_ker R]
  exact independentPlusFiberConnectingHom_range_le_center R

/-- The actual original plus-fiber extension, with its original maps, is central. -/
theorem independentPlusFiberExtension_isCentral (R : Type u) [Ring R] :
    (independentPlusFiberExtension R).IsCentral := by
  change (independentPlusFiberToStableE R).ker ≤
    Subgroup.center (FundamentalGroup (independentPlusFiber R) (independentPlusFiberPoint R))
  exact independentPlusFiberToStableE_ker_le_center R

end AlgebraicKTheory.StableGL

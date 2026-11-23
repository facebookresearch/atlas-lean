/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module


public import MathlibExt.Topology.Category.TopPair.NDRCoproduct

@[expose] public section

set_option autoImplicit false
set_option warningAsError true

noncomputable section

open CategoryTheory
open scoped unitInterval

universe v u

namespace MathlibExtTest.Topology.Category.TopPair.NDRCoproduct

variable {i : Type v} {P : i → TopPair.{max v u}}
variable (d : (j : i) → TopPair.NDRData (P j))

example : TopPair.NDRData (TopPair.sigma P) :=
  TopPair.NDRData.sigma d

example (j : i) (x : (P j).fst) :
    (TopPair.NDRData.sigma d).control
        (TopPair.Hom.fst (TopPair.sigmaι P j) x) =
      (d j).control x := by
  exact TopPair.NDRData.sigmaControl_ι d j x

example (j : i) (x : (P j).fst) :
    (TopPair.NDRData.sigma d).endpoint
        (TopPair.Hom.fst (TopPair.sigmaι P j) x) =
      TopPair.Hom.fst (TopPair.sigmaι P j) ((d j).endpoint x) := by
  exact TopPair.NDRData.sigmaEndpoint_ι d j x

example (j : i) (t : unitInterval) (x : (P j).fst) :
    (TopPair.NDRData.sigma d).deformation
        (t, TopPair.Hom.fst (TopPair.sigmaι P j) x) =
      TopPair.Hom.fst (TopPair.sigmaι P j)
        ((d j).deformation (t, x)) := by
  exact TopPair.NDRData.sigmaDeformation_ι d j t x

example (x : (TopPair.sigma P).fst) :
    (TopPair.NDRData.sigma d).control x = 0 ↔
      x ∈ Set.range (TopPair.sigma P).map :=
  (TopPair.NDRData.sigma d).control_eq_zero_iff x

example (t : unitInterval) (x : (TopPair.sigma P).fst) :
    (TopPair.NDRData.sigma d).control
        ((TopPair.NDRData.sigma d).deformation (t, x)) ≤
      (TopPair.NDRData.sigma d).control x :=
  (TopPair.NDRData.sigma d).control_deformation_le t x

example (P : PEmpty.{1} → TopPair.{u})
    (d : (j : PEmpty.{1}) → TopPair.NDRData (P j)) :
    TopPair.NDRData (TopPair.sigma P) :=
  TopPair.NDRData.sigma d

end MathlibExtTest.Topology.Category.TopPair.NDRCoproduct

end

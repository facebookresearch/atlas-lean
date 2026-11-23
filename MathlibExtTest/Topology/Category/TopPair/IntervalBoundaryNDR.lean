/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.Category.TopPair.IntervalBoundaryNDR

@[expose] public section

set_option autoImplicit false
set_option warningAsError true

noncomputable section

open CategoryTheory Topology
open scoped unitInterval

universe u

namespace MathlibExtTest.Topology.Category.TopPair.IntervalBoundaryNDR

private def oneThird : unitInterval :=
  ⟨1 / 3, by norm_num⟩

private def oneHalf : unitInterval :=
  ⟨1 / 2, by norm_num⟩

private def twoThirds : unitInterval :=
  ⟨2 / 3, by norm_num⟩

private def oneSixth : unitInterval :=
  ⟨1 / 6, by norm_num⟩

private def fiveSixths : unitInterval :=
  ⟨5 / 6, by norm_num⟩

example : _root_.TopPair.intervalBoundaryEndpoint 0 = 0 := by simp

example : _root_.TopPair.intervalBoundaryEndpoint 1 = 1 := by simp

example : _root_.TopPair.intervalBoundaryControl 0 = 0 :=
  (_root_.TopPair.intervalBoundaryControl_eq_zero_iff 0).2 (Or.inl rfl)

example : _root_.TopPair.intervalBoundaryControl 1 = 0 :=
  (_root_.TopPair.intervalBoundaryControl_eq_zero_iff 1).2 (Or.inr rfl)

example : _root_.TopPair.intervalBoundaryEndpoint oneThird = 0 :=
  _root_.TopPair.intervalBoundaryEndpoint_eq_zero_of_le oneThird (by norm_num [oneThird])

example : _root_.TopPair.intervalBoundaryEndpoint twoThirds = 1 :=
  _root_.TopPair.intervalBoundaryEndpoint_eq_one_of_le twoThirds (by norm_num [twoThirds])

example : _root_.TopPair.intervalBoundaryEndpoint oneSixth = 0 :=
  _root_.TopPair.intervalBoundaryEndpoint_eq_zero_of_le oneSixth (by norm_num [oneSixth])

example : _root_.TopPair.intervalBoundaryEndpoint fiveSixths = 1 :=
  _root_.TopPair.intervalBoundaryEndpoint_eq_one_of_le fiveSixths (by norm_num [fiveSixths])

example : _root_.TopPair.intervalBoundaryControl oneThird = 1 :=
  _root_.TopPair.intervalBoundaryControl_eq_one oneThird
    (by norm_num [oneThird]) (by norm_num [oneThird])

example : _root_.TopPair.intervalBoundaryControl oneHalf = 1 :=
  _root_.TopPair.intervalBoundaryControl_eq_one oneHalf
    (by norm_num [oneHalf]) (by norm_num [oneHalf])

example : _root_.TopPair.intervalBoundaryControl twoThirds = 1 :=
  _root_.TopPair.intervalBoundaryControl_eq_one twoThirds
    (by norm_num [twoThirds]) (by norm_num [twoThirds])

example (t : unitInterval)
    (ht : _root_.TopPair.intervalBoundaryControl t < 1) :
    _root_.TopPair.intervalBoundaryEndpoint t ∈
      Set.range _root_.TopPair.unitIntervalBoundaryPair.map :=
  _root_.TopPair.intervalBoundaryEndpoint_mem_range t ht

example (s t : unitInterval) :
    _root_.TopPair.intervalBoundaryControl
        (_root_.TopPair.unitIntervalBoundaryNDRData.deformation (s, t)) ≤
      _root_.TopPair.intervalBoundaryControl t :=
  _root_.TopPair.unitIntervalBoundaryNDRData.control_deformation_le s t

example (t : unitInterval) :
    _root_.TopPair.unitIntervalBoundaryNDRData.deformation (0, t) = t :=
  _root_.TopPair.unitIntervalBoundaryNDRData.deformation.apply_zero t

example (t : unitInterval) :
    _root_.TopPair.unitIntervalBoundaryNDRData.deformation (1, t) =
      _root_.TopPair.intervalBoundaryEndpoint t :=
  _root_.TopPair.unitIntervalBoundaryNDRData.deformation.apply_one t

example (s : unitInterval) :
    _root_.TopPair.unitIntervalBoundaryNDRData.deformation
        (s, (0 : unitInterval)) = (0 : unitInterval) :=
  _root_.TopPair.unitIntervalBoundaryNDRData.deformation.eq_fst s
    ((_root_.TopPair.mem_range_unitIntervalBoundaryPair_map_iff 0).2 (Or.inl rfl))

example (s : unitInterval) :
    _root_.TopPair.unitIntervalBoundaryNDRData.deformation
        (s, (1 : unitInterval)) = (1 : unitInterval) :=
  _root_.TopPair.unitIntervalBoundaryNDRData.deformation.eq_fst s
    ((_root_.TopPair.mem_range_unitIntervalBoundaryPair_map_iff 1).2 (Or.inr rfl))

example : _root_.TopPair.NDRData
    (_root_.TopPair.intervalBoundaryPair.{u}) :=
  _root_.TopPair.intervalBoundaryNDRData

example : _root_.TopCat.IsHurewiczCofibration
    (_root_.TopPair.intervalBoundaryPair.{u}).map :=
  _root_.TopPair.intervalBoundary_isHurewiczCofibration

end MathlibExtTest.Topology.Category.TopPair.IntervalBoundaryNDR

end

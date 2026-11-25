/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Topology.HouseWithTwoRooms
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.Tactic.NormNum

/-! # Tests for `MathlibExt.Topology.HouseWithTwoRooms` -/

namespace MathlibExtTest.Topology.HouseWithTwoRooms

open MathlibExt.Topology.HouseWithTwoRoomsWanted.Topology

-- Test section: the house. The southwest corner of the ground floor, a point of the inner wall
-- `x = 1` around the tube from the top floor, a point of the wall `x = 2` between the tube walls
-- and the north outer wall, and a corner of the hole in the middle floor lie in the house.
example : ((0 : ℝ), (0 : ℝ), (0 : ℝ)) ∈ HouseWithTwoRooms := by
  norm_num [HouseWithTwoRooms]

example : ((1 : ℝ), (3 / 2 : ℝ), (3 / 2 : ℝ)) ∈ HouseWithTwoRooms := by
  norm_num [HouseWithTwoRooms]

example : ((2 : ℝ), (5 / 2 : ℝ), (1 / 2 : ℝ)) ∈ HouseWithTwoRooms := by
  norm_num [HouseWithTwoRooms]

example : ((3 : ℝ), (2 : ℝ), (1 : ℝ)) ∈ HouseWithTwoRooms := by
  norm_num [HouseWithTwoRooms]

-- The holes in the ground, middle and top floors are not in the house (the wall `x = 2` splits
-- the hole in the middle floor), nor are points inside the two rooms.
example : ((5 / 2 : ℝ), (3 / 2 : ℝ), (0 : ℝ)) ∉ HouseWithTwoRooms := by
  norm_num [HouseWithTwoRooms]

example : ((3 / 2 : ℝ), (3 / 2 : ℝ), (1 : ℝ)) ∉ HouseWithTwoRooms := by
  norm_num [HouseWithTwoRooms]

example : ((5 / 2 : ℝ), (3 / 2 : ℝ), (1 : ℝ)) ∉ HouseWithTwoRooms := by
  norm_num [HouseWithTwoRooms]

example : ((3 / 2 : ℝ), (3 / 2 : ℝ), (2 : ℝ)) ∉ HouseWithTwoRooms := by
  norm_num [HouseWithTwoRooms]

example : ((1 / 2 : ℝ), (1 / 2 : ℝ), (1 / 2 : ℝ)) ∉ HouseWithTwoRooms := by
  norm_num [HouseWithTwoRooms]

example : ((7 / 2 : ℝ), (5 / 2 : ℝ), (3 / 2 : ℝ)) ∉ HouseWithTwoRooms := by
  norm_num [HouseWithTwoRooms]

-- Test section: contractibility.
example : ContractibleSpace HouseWithTwoRooms := contractibleSpace_houseWithTwoRooms

-- The house is path connected and simply connected.
example : PathConnectedSpace HouseWithTwoRooms := by
  have := contractibleSpace_houseWithTwoRooms
  infer_instance

example : SimplyConnectedSpace HouseWithTwoRooms := by
  have := contractibleSpace_houseWithTwoRooms
  infer_instance

-- Every continuous map into the house is nullhomotopic, so any two are homotopic.
example {X : Type} [TopologicalSpace X] (f : C(X, HouseWithTwoRooms)) : f.Nullhomotopic := by
  have := contractibleSpace_houseWithTwoRooms
  simpa using (id_nullhomotopic HouseWithTwoRooms).comp_left f

example {X : Type} [TopologicalSpace X] (f g : C(X, HouseWithTwoRooms)) : f.Homotopic g := by
  have := contractibleSpace_houseWithTwoRooms
  obtain ⟨y, hy⟩ := id_nullhomotopic HouseWithTwoRooms
  have hf : f.Homotopic (ContinuousMap.const X y) := by
    simpa using hy.comp (ContinuousMap.Homotopic.refl f)
  have hg : g.Homotopic (ContinuousMap.const X y) := by
    simpa using hy.comp (ContinuousMap.Homotopic.refl g)
  exact hf.trans hg.symm

end MathlibExtTest.Topology.HouseWithTwoRooms

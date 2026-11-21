/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.GameTheory.BackwardInductionNormalForm

set_option autoImplicit false

namespace MathlibExtTest.GameTheory.BackwardInductionNormalForm

open MathlibExt.GameTheory
open MathlibExt.GameTheory.PerfectInfoGame

@[expose] public section

/-- Second-level children: leaves with payoffs `(0, 0)` and `(1, 3)`
(the third arm is an unreachable dummy). -/
def testChild2 : Fin (1 + 1) → PerfectInfoGame (Fin 2)
  | ⟨0, _⟩ => leaf (fun i => if i = 0 then 0 else 0)
  | ⟨1, _⟩ => leaf (fun i => if i = 0 then 1 else 3)
  | ⟨Nat.succ (Nat.succ _w), _⟩ => leaf (fun i => if i = 0 then 0 else 0)

/-- First-level children: the leaf `(2, 1)` and the player-1 subtree. -/
def testChild1 : Fin (1 + 1) → PerfectInfoGame (Fin 2)
  | ⟨0, _⟩ => leaf (fun i => if i = 0 then 2 else 1)
  | ⟨1, _⟩ => node 1 testChild2
  | ⟨Nat.succ (Nat.succ _w), _⟩ => leaf (fun i => if i = 0 then 2 else 1)

/-- The test tree: root owned by player 0 with children `(2, 1)` and a
player-1 node over `(0, 0)` and `(1, 3)`. -/
def testTree : PerfectInfoGame (Fin 2) :=
  node 0 testChild1

/-- Subprofiles in the player-1 subtree (leaf profiles). -/
def biSub2 : ∀ k : Fin (1 + 1), Profile (testChild2 k)
  | ⟨0, _⟩ => Profile.leaf (fun i => if i = 0 then 0 else 0)
  | ⟨1, _⟩ => Profile.leaf (fun i => if i = 0 then 1 else 3)
  | ⟨Nat.succ (Nat.succ _w), _⟩ => Profile.leaf (fun i => if i = 0 then 0 else 0)

/-- Subprofiles below the root: leaf `(2, 1)` and the player-1 profile
playing action 1. -/
def biSub : ∀ k : Fin (1 + 1), Profile (testChild1 k)
  | ⟨0, _⟩ => Profile.leaf (fun i => if i = 0 then 2 else 1)
  | ⟨1, _⟩ => Profile.node 1 testChild2 ⟨1, by omega⟩ biSub2
  | ⟨Nat.succ (Nat.succ _w), _⟩ => Profile.leaf (fun i => if i = 0 then 2 else 1)

/-- The backward-induction profile: action 0 at the root, action 1 in
the player-1 subtree. -/
def biProfile : Profile testTree :=
  Profile.node 0 testChild1 ⟨0, by omega⟩ biSub

/-- The two players are distinct. -/
theorem fin2_one_ne_zero : (1 : Fin 2) ≠ 0 := by decide

/-- Outcomes of the backward-induction profile, including the
assemble/restrict round trip. -/
theorem t1_outcomes : biProfile.outcome 0 = 2 ∧ biProfile.outcome 1 = 1 ∧
    (assemble (fun i => restrict biProfile i)).outcome 0 = 2 := by
  have o0 : biProfile.outcome 0 = 2 := by
    simp [biProfile, biSub, Profile.outcome]
  have o1 : biProfile.outcome 1 = 1 := by
    simp [biProfile, biSub, Profile.outcome]
  refine ⟨o0, o1, ?_⟩
  rw [assemble_restrict biProfile]
  exact o0

/-- The backward-induction profile is a backward-induction profile. -/
theorem t3_bi_isBackwardInduction : Profile.IsBackwardInduction biProfile := by
  refine Profile.IsBackwardInduction.node ?_ ?_
  · intro k
    cases k with
    | mk val isLt =>
        cases val with
        | zero =>
            simp [biSub, Profile.outcome]
        | succ v =>
            cases v with
            | zero =>
                simp [biSub, biSub2, Profile.outcome]
            | succ w =>
                simp [biSub, Profile.outcome]
  · intro k
    cases k with
    | mk val isLt =>
        cases val with
        | zero => exact Profile.IsBackwardInduction.leaf _
        | succ v =>
            cases v with
            | zero =>
                refine Profile.IsBackwardInduction.node ?_ ?_
                · intro k2
                  cases k2 with
                  | mk val2 isLt2 =>
                      cases val2 with
                      | zero =>
                          simp [biSub2, Profile.outcome]
                      | succ v2 =>
                          cases v2 with
                          | zero =>
                              simp [biSub2, Profile.outcome]
                          | succ w2 =>
                              simp [biSub2, Profile.outcome]
                · intro k2
                  cases k2 with
                  | mk val2 isLt2 =>
                      cases val2 with
                      | zero => exact Profile.IsBackwardInduction.leaf _
                      | succ v2 =>
                          cases v2 with
                          | zero => exact Profile.IsBackwardInduction.leaf _
                          | succ w2 => exact Profile.IsBackwardInduction.leaf _
            | succ w => exact Profile.IsBackwardInduction.leaf _

/-- The backward-induction profile is a Nash equilibrium of the tree. -/
theorem t2_bi_isNash_tree : biProfile.IsNash :=
  Profile.IsBackwardInduction.isNash t3_bi_isBackwardInduction

end

end MathlibExtTest.GameTheory.BackwardInductionNormalForm

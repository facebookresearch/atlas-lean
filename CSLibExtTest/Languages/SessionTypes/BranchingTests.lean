/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import CSLibExt.Languages.SessionTypes.Branching

/-!
# Branching session type statement tests

Examples over two sorts and two labels for duality, lookup,
well-formedness, advancement, bridges and contexts.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.SessionTypes

namespace BranchingTests

/-- Two payload sorts for examples. -/
inductive TestSort where
  | name : TestSort
  | data : TestSort
deriving DecidableEq

/-- Two branch labels for examples. -/
inductive TestLabel where
  | left : TestLabel
  | right : TestLabel
deriving DecidableEq

example : DecidableEq (BranchingType TestSort TestLabel) := inferInstance
example : DecidableEq (BranchingType.Branches TestSort TestLabel) := inferInstance
/-- Dual swaps select to branch and dualizes continuations. -/
theorem dual_select_example :
    (BranchingType.select (BranchingType.Branches.cons TestLabel.left
      (BranchingType.send TestSort.name BranchingType.end)
      (BranchingType.Branches.cons TestLabel.right BranchingType.end
        BranchingType.Branches.nil))).dual =
    BranchingType.branch (BranchingType.Branches.cons TestLabel.left
      (BranchingType.recv TestSort.name BranchingType.end)
      (BranchingType.Branches.cons TestLabel.right BranchingType.end
        BranchingType.Branches.nil)) := by
  rfl
/-- Lookup finds the left entry. -/
theorem lookup_left :
    BranchingType.Branches.lookup (BranchingType.Branches.cons TestLabel.left
      (BranchingType.send TestSort.name BranchingType.end)
      (BranchingType.Branches.cons TestLabel.right BranchingType.end
        BranchingType.Branches.nil)) TestLabel.left =
    some (BranchingType.send TestSort.name BranchingType.end) := by
  decide
/-- Lookup of an absent label returns none. -/
theorem lookup_right_absent :
    BranchingType.Branches.lookup (BranchingType.Branches.cons TestLabel.left
      BranchingType.end BranchingType.Branches.nil) TestLabel.right =
    (none : Option (BranchingType TestSort TestLabel)) := by
  decide
/-- The two-branch select example is well formed. -/
theorem wellFormed_select_example :
    (BranchingType.select (BranchingType.Branches.cons TestLabel.left
      (BranchingType.send TestSort.name BranchingType.end)
      (BranchingType.Branches.cons TestLabel.right BranchingType.end
        BranchingType.Branches.nil))).WellFormed := by
  exact BranchingType.WellFormed.select
    (BranchingType.Branches.WellFormed.cons (by decide)
      (BranchingType.WellFormed.send BranchingType.WellFormed.end)
      (BranchingType.Branches.WellFormed.cons (by decide)
        BranchingType.WellFormed.end BranchingType.Branches.WellFormed.nil))
/-- Select advances by the left label. -/
theorem advance_select_left :
    BranchingType.Advances (BranchingType.select
      (BranchingType.Branches.cons TestLabel.left
        (BranchingType.send TestSort.name BranchingType.end)
        (BranchingType.Branches.cons TestLabel.right BranchingType.end
          BranchingType.Branches.nil)))
      (BranchingType.Action.select TestLabel.left)
      (BranchingType.send TestSort.name BranchingType.end) := by
  exact BranchingType.Advances.select (by decide)

/-- Dual branch advances by the dual label action. -/
theorem advance_branch_left_dual :
    BranchingType.Advances (BranchingType.select
      (BranchingType.Branches.cons TestLabel.left
        (BranchingType.send TestSort.name BranchingType.end)
        (BranchingType.Branches.cons TestLabel.right BranchingType.end
          BranchingType.Branches.nil))).dual
      (BranchingType.Action.branch TestLabel.left)
      (BranchingType.recv TestSort.name BranchingType.end) := by
  exact BranchingType.Advances.branch (by decide)

/-- Embedding preserves send and receive structure. -/
theorem ofSessionType_example :
    (BranchingType.ofSessionType TestSort.name
      (SessionType.send (SessionType.recv SessionType.end)) :
      BranchingType TestSort TestLabel) =
    BranchingType.send TestSort.name
      (BranchingType.recv TestSort.name BranchingType.end) := by
  rfl

/-- Triangle through `Protocol.ofFinite` on a send example. -/
theorem toProtocol?_triangle_example :
    BranchingType.toProtocol? TestSort.name
      ((BranchingType.ofSessionType TestSort.name
        (SessionType.send SessionType.end)) :
        BranchingType TestSort TestLabel) =
    some (Endpoint.Protocol.ofFinite (SessionType.send SessionType.end)) :=
  by exact BranchingType.toProtocol?_ofSessionType _ _

/-- Protocol map rejects choices. -/
theorem toProtocol?_rejects_choice :
    BranchingType.toProtocol? TestSort.name (BranchingType.select
      (BranchingType.Branches.nil : BranchingType.Branches TestSort TestLabel)) =
    (none : Option Endpoint.Protocol) := by
  rfl

/-- Protocol map rejects non-passive sorts. -/
theorem toProtocol?_rejects_sort :
    BranchingType.toProtocol? TestSort.name
      ((BranchingType.send TestSort.data BranchingType.end) :
        BranchingType TestSort TestLabel) =
    (none : Option Endpoint.Protocol) := by
  rfl

/-- Dual context lookup dualizes the value. -/
theorem context_dual_lookup :
    (BranchingContext.dual ((Finmap.singleton 0
      (BranchingType.send TestSort.name BranchingType.end)) :
      BranchingContext TestSort TestLabel)).lookup 0 =
    some (BranchingType.recv TestSort.name BranchingType.end) := by
  simp [BranchingContext.lookup_dual, Finmap.lookup_singleton_eq, BranchingType.dual]

/-- Singleton select context advances by the left label. -/
theorem context_advance_label :
    BranchingContext.Advances ((Finmap.singleton 0 (BranchingType.select
      (BranchingType.Branches.cons TestLabel.left
        (BranchingType.send TestSort.name BranchingType.end)
        (BranchingType.Branches.cons TestLabel.right BranchingType.end
          BranchingType.Branches.nil)))) :
      BranchingContext TestSort TestLabel) 0
      (BranchingType.Action.select TestLabel.left) ((Finmap.singleton 0
      (BranchingType.send TestSort.name BranchingType.end)) :
      BranchingContext TestSort TestLabel) := by
  exact ⟨_, _, Finmap.lookup_singleton_eq,
    BranchingType.Advances.select (by decide), Finmap.insert_singleton_eq.symm⟩

end BranchingTests

end Cslib.SessionTypes

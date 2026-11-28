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

Examples over two sorts and two labels for duality, lookup, well-formedness,
advancement, bridges, contexts and branch-order equivalence.
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
  refine ⟨BranchingType.select (BranchingType.Branches.cons TestLabel.left
    (BranchingType.send TestSort.name BranchingType.end)
    (BranchingType.Branches.cons TestLabel.right BranchingType.end
      BranchingType.Branches.nil)),
    BranchingType.send TestSort.name BranchingType.end,
    Finmap.lookup_singleton_eq,
    BranchingType.Advances.select (by decide), ?_⟩
  intro b
  by_cases hb : b = 0
  · rw [hb, Finmap.lookup_singleton_eq, Finmap.lookup_insert _]
    exact Option.Rel.some (BranchingType.PermEquiv.refl _)
  · rw [Finmap.lookup_insert_of_ne _ hb]
    have hLnone : ((Finmap.singleton 0
        (BranchingType.send TestSort.name BranchingType.end)) :
        BranchingContext TestSort TestLabel).lookup b = none := by
      have hnot : b ∉ ((Finmap.singleton 0
          (BranchingType.send TestSort.name BranchingType.end)) :
          BranchingContext TestSort TestLabel) := by
        intro hcon
        have heq : b = 0 :=
          (Finmap.mem_singleton _ _ _).mp hcon
        exact hb heq
      exact Finmap.lookup_eq_none.mpr hnot
    have hRnone : ((Finmap.singleton 0 (BranchingType.select
        (BranchingType.Branches.cons TestLabel.left
          (BranchingType.send TestSort.name BranchingType.end)
          (BranchingType.Branches.cons TestLabel.right BranchingType.end
            BranchingType.Branches.nil)))) :
        BranchingContext TestSort TestLabel).lookup b = none := by
      have hnot : b ∉ ((Finmap.singleton 0 (BranchingType.select
          (BranchingType.Branches.cons TestLabel.left
            (BranchingType.send TestSort.name BranchingType.end)
            (BranchingType.Branches.cons TestLabel.right BranchingType.end
              BranchingType.Branches.nil)))) :
          BranchingContext TestSort TestLabel) := by
        intro hcon
        have heq : b = 0 :=
          (Finmap.mem_singleton _ _ _).mp hcon
        exact hb heq
      exact Finmap.lookup_eq_none.mpr hnot
    rw [hLnone, hRnone]
    exact Option.Rel.none

/-- Reversed selects are syntactically unequal. -/
theorem select_reversed_neq :
    BranchingType.select (BranchingType.Branches.cons TestLabel.left
      (BranchingType.send TestSort.name BranchingType.end)
      (BranchingType.Branches.cons TestLabel.right BranchingType.end
        BranchingType.Branches.nil)) ≠
    BranchingType.select (BranchingType.Branches.cons TestLabel.right
      BranchingType.end
      (BranchingType.Branches.cons TestLabel.left
        (BranchingType.send TestSort.name BranchingType.end)
        BranchingType.Branches.nil)) := by decide

/-- Reversed selects are PermEquiv. -/
theorem select_reversed_permEquiv :
    BranchingType.PermEquiv
      (BranchingType.select (BranchingType.Branches.cons TestLabel.left
        (BranchingType.send TestSort.name BranchingType.end)
        (BranchingType.Branches.cons TestLabel.right BranchingType.end
          BranchingType.Branches.nil)))
      (BranchingType.select (BranchingType.Branches.cons TestLabel.right
        BranchingType.end
        (BranchingType.Branches.cons TestLabel.left
          (BranchingType.send TestSort.name BranchingType.end)
          BranchingType.Branches.nil))) := by
  exact Relation.EqvGen.rel _ _
    (BranchingType.SwapStep.select
      (BranchingType.Branches.SwapStep.swap (by decide)))

/-- Both branch orders are well formed. -/
theorem select_reversed_wellFormed :
    (BranchingType.select (BranchingType.Branches.cons TestLabel.left
      (BranchingType.send TestSort.name BranchingType.end)
      (BranchingType.Branches.cons TestLabel.right BranchingType.end
        BranchingType.Branches.nil))).WellFormed ∧
    (BranchingType.select (BranchingType.Branches.cons TestLabel.right
      BranchingType.end
      (BranchingType.Branches.cons TestLabel.left
        (BranchingType.send TestSort.name BranchingType.end)
        BranchingType.Branches.nil))).WellFormed := by
  have hFwd : (BranchingType.select (BranchingType.Branches.cons
      TestLabel.left (BranchingType.send TestSort.name BranchingType.end)
      (BranchingType.Branches.cons TestLabel.right BranchingType.end
        BranchingType.Branches.nil))).WellFormed :=
    BranchingType.WellFormed.select
      (BranchingType.Branches.WellFormed.cons (by decide)
        (BranchingType.WellFormed.send BranchingType.WellFormed.end)
        (BranchingType.Branches.WellFormed.cons (by decide)
          BranchingType.WellFormed.end
          BranchingType.Branches.WellFormed.nil))
  have hRev : (BranchingType.select (BranchingType.Branches.cons
      TestLabel.right BranchingType.end (BranchingType.Branches.cons
        TestLabel.left (BranchingType.send TestSort.name BranchingType.end)
        BranchingType.Branches.nil))).WellFormed :=
    BranchingType.WellFormed.select
      (BranchingType.Branches.WellFormed.cons (by decide)
        BranchingType.WellFormed.end
        (BranchingType.Branches.WellFormed.cons (by decide)
          (BranchingType.WellFormed.send BranchingType.WellFormed.end)
          BranchingType.Branches.WellFormed.nil))
  exact ⟨hFwd, hRev⟩

/-- Duals of the two orders are PermEquiv. -/
theorem select_reversed_dual_permEquiv :
    BranchingType.PermEquiv
      (BranchingType.select (BranchingType.Branches.cons TestLabel.left
        (BranchingType.send TestSort.name BranchingType.end)
        (BranchingType.Branches.cons TestLabel.right BranchingType.end
          BranchingType.Branches.nil))).dual
      (BranchingType.select (BranchingType.Branches.cons TestLabel.right
        BranchingType.end
        (BranchingType.Branches.cons TestLabel.left
          (BranchingType.send TestSort.name BranchingType.end)
          BranchingType.Branches.nil))).dual := by
  exact BranchingType.PermEquiv.dual select_reversed_permEquiv

/-- A depth-two reorder inside a branch continuation is PermEquiv. -/
theorem branch_nested_reorder_permEquiv :
    BranchingType.PermEquiv
      (BranchingType.branch (BranchingType.Branches.cons TestLabel.left
        (BranchingType.select (BranchingType.Branches.cons TestLabel.left
          (BranchingType.send TestSort.name BranchingType.end)
          (BranchingType.Branches.cons TestLabel.right BranchingType.end
            BranchingType.Branches.nil)))
        BranchingType.Branches.nil))
      (BranchingType.branch (BranchingType.Branches.cons TestLabel.left
        (BranchingType.select (BranchingType.Branches.cons TestLabel.right
          BranchingType.end
          (BranchingType.Branches.cons TestLabel.left
            (BranchingType.send TestSort.name BranchingType.end)
            BranchingType.Branches.nil)))
        BranchingType.Branches.nil)) := by
  exact Relation.EqvGen.rel _ _
    (BranchingType.SwapStep.branch
      (BranchingType.Branches.SwapStep.head
        (BranchingType.SwapStep.select
          (BranchingType.Branches.SwapStep.swap (by decide)))))

/-- Lookups on the two orders agree at both labels. -/
theorem select_reversed_lookup :
    Option.Rel BranchingType.PermEquiv
      (BranchingType.Branches.lookup (BranchingType.Branches.cons TestLabel.left
        (BranchingType.send TestSort.name BranchingType.end)
        (BranchingType.Branches.cons TestLabel.right BranchingType.end
          BranchingType.Branches.nil)) TestLabel.left)
      (BranchingType.Branches.lookup
        (BranchingType.Branches.cons TestLabel.right BranchingType.end
          (BranchingType.Branches.cons TestLabel.left
            (BranchingType.send TestSort.name BranchingType.end)
            BranchingType.Branches.nil)) TestLabel.left) ∧
    Option.Rel BranchingType.PermEquiv
      (BranchingType.Branches.lookup (BranchingType.Branches.cons TestLabel.left
        (BranchingType.send TestSort.name BranchingType.end)
        (BranchingType.Branches.cons TestLabel.right BranchingType.end
          BranchingType.Branches.nil)) TestLabel.right)
      (BranchingType.Branches.lookup
        (BranchingType.Branches.cons TestLabel.right BranchingType.end
          (BranchingType.Branches.cons TestLabel.left
            (BranchingType.send TestSort.name BranchingType.end)
            BranchingType.Branches.nil)) TestLabel.right) := by
  have hFL : BranchingType.Branches.lookup (BranchingType.Branches.cons
      TestLabel.left (BranchingType.send TestSort.name BranchingType.end)
      (BranchingType.Branches.cons TestLabel.right BranchingType.end
        BranchingType.Branches.nil)) TestLabel.left =
      some (BranchingType.send TestSort.name BranchingType.end) := by decide
  have hRL : BranchingType.Branches.lookup (BranchingType.Branches.cons
      TestLabel.right BranchingType.end (BranchingType.Branches.cons
        TestLabel.left (BranchingType.send TestSort.name BranchingType.end)
        BranchingType.Branches.nil)) TestLabel.left =
      some (BranchingType.send TestSort.name BranchingType.end) := by decide
  have hFR : BranchingType.Branches.lookup (BranchingType.Branches.cons
      TestLabel.left (BranchingType.send TestSort.name BranchingType.end)
      (BranchingType.Branches.cons TestLabel.right BranchingType.end
        BranchingType.Branches.nil)) TestLabel.right =
      some BranchingType.end := by decide
  have hRR : BranchingType.Branches.lookup (BranchingType.Branches.cons
      TestLabel.right BranchingType.end (BranchingType.Branches.cons
        TestLabel.left (BranchingType.send TestSort.name BranchingType.end)
        BranchingType.Branches.nil)) TestLabel.right =
      some BranchingType.end := by decide
  refine ⟨?_, ?_⟩
  · rw [hFL, hRL]
    exact Option.Rel.some (BranchingType.PermEquiv.refl _)
  · rw [hFR, hRR]
    exact Option.Rel.some (BranchingType.PermEquiv.refl _)

/-- Left advancement transports across the branch reorder. -/
theorem select_reversed_advances (u : BranchingType TestSort TestLabel) :
    BranchingType.Advances (BranchingType.select
      (BranchingType.Branches.cons TestLabel.left
        (BranchingType.send TestSort.name BranchingType.end)
        (BranchingType.Branches.cons TestLabel.right BranchingType.end
          BranchingType.Branches.nil)))
      (BranchingType.Action.select TestLabel.left) u →
    BranchingType.Advances (BranchingType.select
      (BranchingType.Branches.cons TestLabel.right BranchingType.end
        (BranchingType.Branches.cons TestLabel.left
          (BranchingType.send TestSort.name BranchingType.end)
          BranchingType.Branches.nil)))
      (BranchingType.Action.select TestLabel.left) u := by
  intro h
  cases h with
  | select m =>
    have hmem1 : (TestLabel.left, u) = (TestLabel.left,
        BranchingType.send TestSort.name BranchingType.end) ∨
        (TestLabel.left, u) ∈
          [(TestLabel.right, BranchingType.end)] :=
      List.mem_cons.mp m
    cases hmem1 with
    | inl heq =>
      have hu : u =
          BranchingType.send TestSort.name BranchingType.end :=
        congrArg Prod.snd heq
      rw [hu]
      exact BranchingType.Advances.select (by decide)
    | inr hmem2 =>
      have hmem2' : (TestLabel.left, u) =
          (TestLabel.right, BranchingType.end) ∨
          (TestLabel.left, u) ∈
            ([] : List (TestLabel × BranchingType TestSort TestLabel)) :=
        List.mem_cons.mp hmem2
      cases hmem2' with
      | inl heq2 =>
        have hlab : TestLabel.left = TestLabel.right :=
          congrArg Prod.fst heq2
        have hne : TestLabel.left ≠ TestLabel.right := by decide
        exact False.elim (hne hlab)
      | inr hnil =>
        exact False.elim (List.not_mem_nil hnil)

/-- Singleton contexts holding the two orders are PermEquiv. -/
theorem context_reorder_permEquiv :
    BranchingContext.PermEquiv
      ((Finmap.singleton 0 (BranchingType.select
        (BranchingType.Branches.cons TestLabel.left
          (BranchingType.send TestSort.name BranchingType.end)
          (BranchingType.Branches.cons TestLabel.right BranchingType.end
            BranchingType.Branches.nil)))) :
        BranchingContext TestSort TestLabel)
      ((Finmap.singleton 0 (BranchingType.select
        (BranchingType.Branches.cons TestLabel.right BranchingType.end
          (BranchingType.Branches.cons TestLabel.left
            (BranchingType.send TestSort.name BranchingType.end)
            BranchingType.Branches.nil)))) :
        BranchingContext TestSort TestLabel) := by
  intro b
  by_cases hb : b = 0
  · rw [hb, Finmap.lookup_singleton_eq, Finmap.lookup_singleton_eq]
    exact Option.Rel.some select_reversed_permEquiv
  · have hLnone : ((Finmap.singleton 0 (BranchingType.select
        (BranchingType.Branches.cons TestLabel.left
          (BranchingType.send TestSort.name BranchingType.end)
          (BranchingType.Branches.cons TestLabel.right BranchingType.end
            BranchingType.Branches.nil)))) :
        BranchingContext TestSort TestLabel).lookup b = none := by
      have hnot : b ∉ ((Finmap.singleton 0 (BranchingType.select
          (BranchingType.Branches.cons TestLabel.left
            (BranchingType.send TestSort.name BranchingType.end)
            (BranchingType.Branches.cons TestLabel.right BranchingType.end
              BranchingType.Branches.nil)))) :
          BranchingContext TestSort TestLabel) := by
        intro hcon
        have heq : b = 0 :=
          (Finmap.mem_singleton _ _ _).mp hcon
        exact hb heq
      exact Finmap.lookup_eq_none.mpr hnot
    have hRnone : ((Finmap.singleton 0 (BranchingType.select
        (BranchingType.Branches.cons TestLabel.right BranchingType.end
          (BranchingType.Branches.cons TestLabel.left
            (BranchingType.send TestSort.name BranchingType.end)
            BranchingType.Branches.nil)))) :
        BranchingContext TestSort TestLabel).lookup b = none := by
      have hnot : b ∉ ((Finmap.singleton 0 (BranchingType.select
          (BranchingType.Branches.cons TestLabel.right BranchingType.end
            (BranchingType.Branches.cons TestLabel.left
              (BranchingType.send TestSort.name BranchingType.end)
              BranchingType.Branches.nil)))) :
          BranchingContext TestSort TestLabel) := by
        intro hcon
        have heq : b = 0 :=
          (Finmap.mem_singleton _ _ _).mp hcon
        exact hb heq
      exact Finmap.lookup_eq_none.mpr hnot
    rw [hLnone, hRnone]
    exact Option.Rel.none

/-- A split of the forward singleton transports to the reversed one. -/
theorem context_reorder_split (Δ Θ : BranchingContext TestSort TestLabel) :
    BranchingContext.Split ((Finmap.singleton 0 (BranchingType.select
      (BranchingType.Branches.cons TestLabel.left
        (BranchingType.send TestSort.name BranchingType.end)
        (BranchingType.Branches.cons TestLabel.right BranchingType.end
          BranchingType.Branches.nil)))) :
      BranchingContext TestSort TestLabel) Δ Θ →
    BranchingContext.Split ((Finmap.singleton 0 (BranchingType.select
      (BranchingType.Branches.cons TestLabel.right BranchingType.end
        (BranchingType.Branches.cons TestLabel.left
          (BranchingType.send TestSort.name BranchingType.end)
          BranchingType.Branches.nil)))) :
      BranchingContext TestSort TestLabel) Δ Θ := by
  intro h
  exact BranchingContext.Split.permEquiv context_reorder_permEquiv
    (BranchingContext.PermEquiv.refl _) (BranchingContext.PermEquiv.refl _) h

end BranchingTests

end Cslib.SessionTypes

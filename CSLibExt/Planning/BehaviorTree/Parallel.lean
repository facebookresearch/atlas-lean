/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Planning.BehaviorTree.Basic

/-!
# Simultaneous parallel ticks

The two children have disjoint *writes*, not necessarily disjoint reads. Each child is a
full-state tree together with evidence that it preserves the coordinate it does not write.
Both coordinate updates and both return maps inspect the same old pair.

## Reference

Michele Colledanchise and Petter Ögren, *Behavior Trees in Robotics and AI: An Introduction*
(2018), [arXiv:1709.00084v6](https://arxiv.org/abs/1709.00084), 25 October 2022,
§5.1, Assumption 5.2 and Definition 5.4, pp. 65–66, equations (5.19)–(5.24).
-/

@[expose] public section

namespace Cslib.Planning.BehaviorTree

/-- The success threshold for a parallel node with two children. -/
inductive Threshold where
  | one | two
  deriving DecidableEq, Repr

namespace Threshold

/-- At threshold one either success suffices and both failures are necessary. At threshold two
both successes are necessary and either failure suffices. All other pairs return running. -/
def combine : Threshold → Status → Status → Status
  | .one, .success, _ | .one, _, .success => .success
  | .one, .failure, .failure => .failure
  | .two, .failure, _ | .two, _, .failure => .failure
  | .two, .success, .success => .success
  | _, _, _ => .running

variable (a b : Status)

@[simp] theorem one_success_iff : one.combine a b = .success ↔ a = .success ∨ b = .success := by
  cases a <;> cases b <;> decide

@[simp] theorem one_failure_iff : one.combine a b = .failure ↔ a = .failure ∧ b = .failure := by
  cases a <;> cases b <;> decide

theorem one_running_iff : one.combine a b = .running ↔
    a ≠ .success ∧ b ≠ .success ∧ (a = .running ∨ b = .running) := by
  cases a <;> cases b <;> decide

@[simp] theorem two_success_iff : two.combine a b = .success ↔ a = .success ∧ b = .success := by
  cases a <;> cases b <;> decide

@[simp] theorem two_failure_iff : two.combine a b = .failure ↔ a = .failure ∨ b = .failure := by
  cases a <;> cases b <;> decide

theorem two_running_iff : two.combine a b = .running ↔
    a ≠ .failure ∧ b ≠ .failure ∧ (a = .running ∨ b = .running) := by
  cases a <;> cases b <;> decide

end Threshold

/-- A left-writing child preserves the second coordinate of every pair. -/
abbrev LeftChild (X Y : Type*) (δ : TimeStep) :=
  {T : Tree (X × Y) δ // ∀ p, (T.next p).2 = p.2}

/-- A right-writing child preserves the first coordinate of every pair. -/
abbrev RightChild (X Y : Type*) (δ : TimeStep) :=
  {T : Tree (X × Y) δ // ∀ p, (T.next p).1 = p.1}

variable {X Y : Type*} {δ : TimeStep}

/-- Lift a full-state read and a write of the first coordinate to a left child. -/
def leftChild (f : X × Y → X) (r : X × Y → Status) : LeftChild X Y δ :=
  ⟨⟨fun p => (f p, p.2), r⟩, fun _ => rfl⟩

/-- Lift a full-state read and a write of the second coordinate to a right child. -/
def rightChild (f : X × Y → Y) (r : X × Y → Status) : RightChild X Y δ :=
  ⟨⟨fun p => (p.1, f p), r⟩, fun _ => rfl⟩

/-- The lift loses no left child: retaining its written coordinate and its status recovers it. -/
theorem leftChild_eta (a : LeftChild X Y δ) :
    leftChild (fun p => (a.val.next p).1) a.val.status = a := by
  apply Subtype.ext
  apply Tree.ext
  · funext p
    exact Prod.ext rfl (a.property p).symm
  · rfl

/-- Every right child is recovered by lifting its written coordinate and its status. -/
theorem rightChild_eta (b : RightChild X Y δ) :
    rightChild (fun p => (b.val.next p).2) b.val.status = b := by
  apply Subtype.ext
  apply Tree.ext
  · funext p
    exact Prod.ext (b.property p).symm rfl
  · rfl

/-- A parallel tick takes the left output of `a` and the right output of `b` simultaneously;
the threshold combines their returns at the same input pair. -/
def parallel (m : Threshold) (a : LeftChild X Y δ) (b : RightChild X Y δ) : Tree (X × Y) δ where
  next p := ((a.val.next p).1, (b.val.next p).2)
  status p := m.combine (a.val.status p) (b.val.status p)

@[simp] theorem parallel_next (m : Threshold) (a : LeftChild X Y δ) (b : RightChild X Y δ)
    (p : X × Y) : (parallel m a b).next p = ((a.val.next p).1, (b.val.next p).2) := rfl

@[simp] theorem parallel_status (m : Threshold) (a : LeftChild X Y δ) (b : RightChild X Y δ)
    (p : X × Y) : (parallel m a b).status p = m.combine (a.val.status p) (b.val.status p) := rfl

end Cslib.Planning.BehaviorTree

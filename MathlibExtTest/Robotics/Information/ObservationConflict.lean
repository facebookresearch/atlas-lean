/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Robotics.Information.ObservationConflict
import Mathlib.Data.Set.Insert
import Mathlib.Data.Set.Lattice.Disjoint

open Robotics.Information

/-- Two hidden states, both reachable after the empty
history, with necessary action sets the singletons of
their own state. -/
private def hiddenReaches : List Unit → Bool → Prop
  | [], _ => True
  | _ :: _, _ => False

-- No observation-only policy satisfies the specification:
-- at the empty history it must pick one action, necessary
-- at only one of the two hidden states.
example :
    ¬ ∃ π : List Unit → Bool,
      ∀ h' s, hiddenReaches h' s → π h' ∈ ({s} : Set Bool) :=
  fun ⟨π, hsat⟩ =>
    not_satisfies_of_reachable_conflict π hiddenReaches
      (h := []) (s₁ := true) (s₂ := false) trivial trivial
      (fun s => ({s} : Set Bool)) (by
        rw [Set.disjoint_left]
        intro x hx hx2
        simp only [Set.mem_singleton_iff] at hx hx2
        rw [hx] at hx2
        exact Bool.false_ne_true hx2.symm) hsat

-- With overlapping necessary sets, a constant policy does
-- satisfy the specification, so disjointness is essential.
example :
    ∃ π : List Unit → Bool,
      ∀ h' s, hiddenReaches h' s →
        π h' ∈ (if s then ({true, false} : Set Bool) else ({false} : Set Bool)) :=
  ⟨fun _ => false, fun h' s _ => by
    cases s with
    | true => exact Set.mem_insert_of_mem _ (Set.mem_singleton false)
    | false => exact Set.mem_singleton false⟩

-- A conflict at an unreachable state does not contradict
-- satisfaction.
example :
    ∃ π : List Unit → Bool,
      ∀ h' s, (match h' with
        | [] => s = true
        | _ :: _ => False) →
        π h' ∈ ({s} : Set Bool) :=
  ⟨fun _ => true, fun h' s hr => by
    cases h' with
    | nil =>
        rw [hr]
        exact Set.mem_singleton true
    | cons _ _ => exact hr.elim⟩

#print axioms not_satisfies_of_reachable_conflict

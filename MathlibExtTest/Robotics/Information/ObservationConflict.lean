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

-- Two states with disjoint singleton necessary-action
-- sets: a constant policy meeting the requirement at the
-- first state misses it at the second.
example :
    ¬ ((fun _ : List Unit => true) [] ∈ ({true} : Set Bool)
      ∧ (fun _ : List Unit => true) [] ∈ ({false} : Set Bool)) :=
  policyAction_not_mem_of_disjoint (h := ([] : List Unit)) (fun _ : List Unit => true)
    (fun s : Bool => ({s} : Set Bool)) (by
      rw [Set.disjoint_left]
      intro x hx hx2
      simp only [Set.mem_singleton_iff] at hx hx2
      rw [hx] at hx2
      exact Bool.false_ne_true hx2.symm)

-- Overlapping necessary sets: one action meets both
-- requirements, so disjointness is essential.
example :
    (fun _ : List Unit => false) [] ∈ ({true, false} : Set Bool)
      ∧ (fun _ : List Unit => false) [] ∈ ({false} : Set Bool) :=
  ⟨Set.mem_insert_of_mem _ (Set.mem_singleton false), Set.mem_singleton false⟩

#print axioms policyAction_not_mem_of_disjoint

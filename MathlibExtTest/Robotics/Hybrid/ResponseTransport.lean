/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Robotics.Hybrid.ResponseTransport

open Robotics.Hybrid

-- Identity transport: the concrete response property is
-- the abstract one.
example {Req Goal : ℕ → Prop}
    (h : ∀ i, Req i → ∃ j, i ≤ j ∧ Goal j) :
    ∀ i, Req i → ∃ j, i ≤ j ∧ Goal j :=
  response_transport_of_cofinal (f := id) monotone_id
    (fun i hi => ⟨i, by simp, hi⟩) (fun j hj => hj) h

-- Stuttering map `f k = k + k`: requests matched at
-- doubled indices, goals transported back.
example {ReqC GoalC ReqA GoalA : ℕ → Prop}
    (hreq : ∀ i, ReqC i → ∃ k, i ≤ k + k ∧ ReqA k)
    (hgoal : ∀ j, GoalA j → GoalC (j + j))
    (habstract : ∀ i, ReqA i → ∃ j, i ≤ j ∧ GoalA j) :
    ∀ i, ReqC i → ∃ j, i ≤ j ∧ GoalC j :=
  response_transport_of_cofinal (f := fun k => k + k)
    (fun a b hab => Nat.add_le_add hab hab) hreq hgoal habstract

-- A bounded index map cannot match a request past its
-- bound: the matching hypothesis fails for `f = fun _ => 0`
-- and a request at step `1`.
example :
    ¬ ∀ i, (i = 1) → ∃ k : ℕ, i ≤ (fun _ => 0) k ∧ (i = 1) := by
  intro hmatch
  obtain ⟨k, hk, -⟩ := hmatch 1 rfl
  simp at hk

#print axioms response_transport_of_cofinal

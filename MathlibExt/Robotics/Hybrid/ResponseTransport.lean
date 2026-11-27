/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Basic
public import Mathlib.Order.Monotone.Basic

/-!
# Cofinal response transport

Concrete response follows from abstract response along a
monotone index map that matches concrete requests to
abstract ones and transports abstract goals back.
-/

@[expose] public section

namespace Robotics.Hybrid

/-- Cofinal response transport. Concrete requests and
goals are related to abstract ones along a monotone index
map `f`: every concrete request at `i` is matched by an
abstract request at some `k` with `i ≤ f k`, and every
abstract goal at `j` gives a concrete goal at `f j`. If
the abstract run responds to every request with a later
goal, so does the concrete run. -/
theorem response_transport_of_cofinal
    {ReqC GoalC ReqA GoalA : ℕ → Prop} {f : ℕ → ℕ}
    (hf : Monotone f)
    (hreq : ∀ i, ReqC i → ∃ k, i ≤ f k ∧ ReqA k)
    (hgoal : ∀ j, GoalA j → GoalC (f j))
    (habstract : ∀ i, ReqA i → ∃ j, i ≤ j ∧ GoalA j) :
    ∀ i, ReqC i → ∃ j, i ≤ j ∧ GoalC j := by
  intro i hi
  obtain ⟨k, hik, hk⟩ := hreq i hi
  obtain ⟨j, hkj, hj⟩ := habstract k hk
  exact ⟨f j, le_trans hik (hf hkj), hgoal j hj⟩

end Robotics.Hybrid

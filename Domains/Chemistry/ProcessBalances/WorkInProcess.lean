/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs

import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Tactic.Linarith

/-!
# Finite-window work-in-process balance

Window totals, not instantaneous rates, enter the local balances. Each internal
transfer is counted once at its source and once at its destination, including
self-loops. Boundary flows and signed production remain after summing.
-/

open scoped BigOperators

namespace Domains.Chemistry.ProcessBalances.WorkInProcess

private theorem sum_transfer_at {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    (atVertex : E → V) (amount : E → ℝ) :
    (∑ v, ∑ e, if atVertex e = v then amount e else 0) = ∑ e, amount e := by
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun e _ => Fintype.sum_ite_eq (atVertex e) (fun _ => amount e)

/-- Summing local window balances gives total boundary input plus signed net production
as good output plus scrap plus the change in total inventory. A single amount per edge
is used for both its incoming and outgoing contribution. With no boundary output and
no net production, total input is the inventory increase, even with internal rework.

Source for the local accumulation balance: Rawlings and Ekerdt, *Chemical Reactor
Analysis and Design Fundamentals*, second edition, §4.3, Eq. 4.36. -/
public theorem finite_window_balance {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    (send receive : E → V) (amount : E → ℝ)
    (start finish input good scrap production : V → ℝ)
    (hlocal : ∀ v, finish v - start v = input v + production v +
      (∑ e, if receive e = v then amount e else 0) - good v - scrap v -
      (∑ e, if send e = v then amount e else 0)) :
    ((∑ v, input v) + (∑ v, production v) =
      (∑ v, good v) + (∑ v, scrap v) + ((∑ v, finish v) - (∑ v, start v))) ∧
    ((∀ v, good v = 0) → (∀ v, scrap v = 0) → (∀ v, production v = 0) →
      (∑ v, input v) = (∑ v, finish v) - (∑ v, start v)) := by
  have hsum := congrArg (fun q : V → ℝ => ∑ v, q v) (funext hlocal)
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, sum_transfer_at] at hsum
  have h : (∑ v, input v) + (∑ v, production v) =
      (∑ v, good v) + (∑ v, scrap v) + ((∑ v, finish v) - (∑ v, start v)) := by
    linarith only [hsum]
  refine ⟨h, ?_⟩
  intro hg hs hp
  simpa [hg, hs, hp] using h

end Domains.Chemistry.ProcessBalances.WorkInProcess

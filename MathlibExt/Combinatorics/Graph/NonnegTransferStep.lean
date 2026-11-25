/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Combinatorics.Graph.ArcNetwork
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Nonnegative transfer step for arc-network inventories

## i. Overview

One step of the shared stock-level update
`m' = m + B *ᵥ F + s - r` with proportional transfers
`F e = α e * m (tail e)`, `α e ≥ 0`, retirements
`r v = δ v * m v`, and the per-node budget
`(outgoing-α sum) + δ v ≤ 1` keeps every stock nonnegative:
at each node the update is the retained fraction
`(1 - Σα - δ) * m v` plus nonnegative incoming transfers and
the nonnegative source. The sign of `δ` is irrelevant once
the budget holds (a negative retirement only adds stock), so
`δ` carries no nonnegativity hypothesis. A timestep, when
used to form `α` or `δ`, enters only through these
coefficients.

## ii. Key results

- `nonneg_transfer_step`: the budget certificate.

## iii. Table of contents

- A. Transported incidence results
- B. The budget certificate

## iv. References

- `MathlibExt.Combinatorics.Graph.ArcNetwork` for
  `incidence_mulVec` and `stock_level_arc_balance`.
-/

@[expose] public section

open Matrix

namespace MathlibExt.Combinatorics.Graph.ArcNetwork

/-! ## A. Transported incidence results -/

/-- Under the transfer-step budget, every updated stock is
nonnegative. The incidence characterization is supplied as
`hinc`, exactly the canonical `incidence_mulVec` statement. -/
private theorem nonneg_transfer_step_of {V : Type*} [Fintype V]
    [DecidableEq V] {E : Type*} [Fintype E] [DecidableEq E]
    (hinc : ∀ (tail head : E → V) (f : E → ℝ) (v : V),
      ((incidenceMatrix tail head) *ᵥ f) v =
        (∑ e ∈ (Finset.univ : Finset E).filter
            (fun e => head e = v), f e) -
        (∑ e ∈ (Finset.univ : Finset E).filter
            (fun e => tail e = v), f e))
    (tail head : E → V) {α F : E → ℝ} {δ m m' s r : V → ℝ}
    (hm : ∀ v, 0 ≤ m v) (hs : ∀ v, 0 ≤ s v)
    (hα : ∀ e, 0 ≤ α e)
    (hF : ∀ e, F e = α e * m (tail e))
    (hr : ∀ v, r v = δ v * m v)
    (hbudget : ∀ v,
      (∑ e ∈ (Finset.univ : Finset E).filter
          (fun e => tail e = v), α e) + δ v ≤ 1)
    (h : m' = m + (incidenceMatrix tail head) *ᵥ F + s - r) :
    ∀ v, 0 ≤ m' v := by
  intro v
  have hB := hinc tail head F v
  have hout : (∑ e ∈ (Finset.univ : Finset E).filter (fun e => tail e = v), F e)
      = (∑ e ∈ (Finset.univ : Finset E).filter (fun e => tail e = v), α e) * m v := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro e he
    rw [hF e, (Finset.mem_filter.mp he).2]
  have hin : 0 ≤ ∑ e ∈ (Finset.univ : Finset E).filter (fun e => head e = v), F e := by
    apply Finset.sum_nonneg
    intro e _
    rw [hF e]
    exact mul_nonneg (hα e) (hm _)
  have hv : m' v = m v + ((incidenceMatrix tail head) *ᵥ F) v + s v - r v := by
    rw [h]
    rfl
  rw [hv, hB, hout, hr v]
  have hbud := hbudget v
  have hret : 0 ≤ (1 - (∑ e ∈ (Finset.univ : Finset E).filter (fun e => tail e = v), α e)
      - δ v) * m v := by
    apply mul_nonneg _ (hm v)
    linarith
  have hexpand : m v + ((∑ e ∈ (Finset.univ : Finset E).filter (fun e => head e = v), F e)
        - (∑ e ∈ (Finset.univ : Finset E).filter (fun e => tail e = v), α e) * m v)
        + s v - δ v * m v
      = (1 - (∑ e ∈ (Finset.univ : Finset E).filter (fun e => tail e = v), α e)
        - δ v) * m v
        + (∑ e ∈ (Finset.univ : Finset E).filter (fun e => head e = v), F e) + s v := by
    ring
  rw [hexpand]
  exact add_nonneg (add_nonneg hret hin) (hs v)

/-! ## B. The budget certificate -/

/-- Under the transfer-step budget, every updated stock is
nonnegative. -/
theorem nonneg_transfer_step {V : Type*} [Fintype V]
    [DecidableEq V] {E : Type*} [Fintype E] [DecidableEq E]
    (tail head : E → V) {α F : E → ℝ} {δ m m' s r : V → ℝ}
    (hm : ∀ v, 0 ≤ m v) (hs : ∀ v, 0 ≤ s v)
    (hα : ∀ e, 0 ≤ α e)
    (hF : ∀ e, F e = α e * m (tail e))
    (hr : ∀ v, r v = δ v * m v)
    (hbudget : ∀ v,
      (∑ e ∈ (Finset.univ : Finset E).filter
          (fun e => tail e = v), α e) + δ v ≤ 1)
    (h : m' = m + (incidenceMatrix tail head) *ᵥ F + s - r) :
    ∀ v, 0 ≤ m' v :=
  nonneg_transfer_step_of incidence_mulVec tail head hm hs hα
    hF hr hbudget h

end MathlibExt.Combinatorics.Graph.ArcNetwork

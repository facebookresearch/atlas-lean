/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Combinatorics.Graph.ArcNetwork
public import Domains.Economics.Macro.StockFlow

/-!
# Urban stock totals from the shared inventory balance

## i. Overview

An urban stock account in one chosen unit (asset counts in
districts, or pipe length by zone; separate instantiations in
separate units, never added together, since plain reals do
not distinguish units) is read in the shared finite inventory
coordinates of `MathlibExt.Combinatorics.Graph.ArcNetwork`:
compartments are nodes, distinct transfers (relocations,
reclassifications) are arcs, external additions and
retirements are the source and sink vectors. No new balance
operator is introduced. Pure internal relocation keeps the
total, and over several periods the total is the initial
total plus all additions minus all retirements, composing the
one-interval balance with the scalar stock-flow telescoping.
Nonnegativity admission for urban stocks is a separate
certificate and is not part of this identity.

## ii. Key results

- `Urban.urbanStock_total_eq_of_no_external`: relocation
  alone keeps the total stock.
- `Urban.urbanStock_total_multiperiod`: the multi-period
  total.

## iii. Table of contents

- A. Transported balance results
- B. Urban stock totals

## iv. References

- `MathlibExt.Combinatorics.Graph.ArcNetwork` for the shared
  stock-level balance.
- `Domains.Economics.Macro.StockFlow` for the scalar
  multi-period telescoping.
-/

@[expose] public section

open Matrix MathlibExt.Combinatorics.Graph.ArcNetwork
open MathlibExt.Economics.Macro.StockFlow

namespace Urban

/-! ## A. Transported balance results -/

/-- Pure internal relocation (no additions, no retirements)
keeps the total stock. -/
private theorem urbanStock_total_eq_of_no_external_of {V : Type*}
    [Fintype V] [DecidableEq V] {E : Type*} [Fintype E]
    [DecidableEq E]
    (hbalance : ∀ (tail head : E → V) (F : E → ℝ)
        {m m' s r : V → ℝ},
      m' = m + (incidenceMatrix tail head).mulVec F + s - r →
      ∑ v, m' v = ∑ v, m v + ∑ v, s v - ∑ v, r v)
    (tail head : E → V) (F : E → ℝ) {m m' : V → ℝ}
    (h : m' = m + (incidenceMatrix tail head).mulVec F) :
    ∑ v, m' v = ∑ v, m v := by
  have h' : m' = m + (incidenceMatrix tail head).mulVec F + (0 : V → ℝ) - 0 := by
    rw [h]
    simp
  have htot := hbalance tail head F h'
  simpa using htot

/-- Multi-period total: each period's stock trajectory obeys
the one-interval update, so the total after `n` periods is the
initial total plus all additions minus all retirements. -/
private theorem urbanStock_total_multiperiod_of {V : Type*} [Fintype V]
    [DecidableEq V] {E : Type*} [Fintype E] [DecidableEq E]
    (hbalance : ∀ (tail head : E → V) (F : E → ℝ)
        {m m' s r : V → ℝ},
      m' = m + (incidenceMatrix tail head).mulVec F + s - r →
      ∑ v, m' v = ∑ v, m v + ∑ v, s v - ∑ v, r v)
    (hflows : ∀ {K inflow outflow otherChange : ℕ → ℝ} (n : ℕ),
      (∀ t < n, K (t + 1)
          = K t + inflow t - outflow t + otherChange t) →
      K n = K 0 + (∑ t ∈ Finset.range n, inflow t)
        - (∑ t ∈ Finset.range n, outflow t)
        + (∑ t ∈ Finset.range n, otherChange t))
    (tail head : E → V) (F : ℕ → E → ℝ)
    (m s r : ℕ → V → ℝ) (n : ℕ)
    (hstep : ∀ t < n, m (t + 1)
        = m t + (incidenceMatrix tail head).mulVec (F t)
          + s t - r t) :
    ∑ v, m n v = ∑ v, m 0 v
      + (∑ t ∈ Finset.range n, ∑ v, s t v)
      - (∑ t ∈ Finset.range n, ∑ v, r t v) := by
  have hprem : ∀ t < n, (∑ v, m (t + 1) v)
      = (∑ v, m t v) + (∑ v, s t v) - (∑ v, r t v) + (0 : ℕ → ℝ) t := by
    intro t ht
    have h1 := hbalance tail head (F t) (hstep t ht)
    simpa using h1
  have htot := hflows (K := fun t => ∑ v, m t v)
    (inflow := fun t => ∑ v, s t v) (outflow := fun t => ∑ v, r t v)
    (otherChange := 0) n hprem
  simpa using htot

/-! ## B. Urban stock totals -/

/-- Pure internal relocation (no additions, no retirements)
keeps the total stock. -/
theorem urbanStock_total_eq_of_no_external {V : Type*}
    [Fintype V] [DecidableEq V] {E : Type*} [Fintype E]
    [DecidableEq E] (tail head : E → V) (F : E → ℝ)
    {m m' : V → ℝ}
    (h : m' = m + (incidenceMatrix tail head).mulVec F) :
    ∑ v, m' v = ∑ v, m v :=
  urbanStock_total_eq_of_no_external_of stock_level_arc_balance
    tail head F h

/-- Multi-period total: after `n` periods of the one-interval
update, total stock is the initial total plus all additions
minus all retirements. -/
theorem urbanStock_total_multiperiod {V : Type*} [Fintype V]
    [DecidableEq V] {E : Type*} [Fintype E] [DecidableEq E]
    (tail head : E → V) (F : ℕ → E → ℝ)
    (m s r : ℕ → V → ℝ) (n : ℕ)
    (hstep : ∀ t < n, m (t + 1)
        = m t + (incidenceMatrix tail head).mulVec (F t)
          + s t - r t) :
    ∑ v, m n v = ∑ v, m 0 v
      + (∑ t ∈ Finset.range n, ∑ v, s t v)
      - (∑ t ∈ Finset.range n, ∑ v, r t v) :=
  urbanStock_total_multiperiod_of stock_level_arc_balance
    stock_eq_initial_add_flows tail head F m s r n hstep

end Urban

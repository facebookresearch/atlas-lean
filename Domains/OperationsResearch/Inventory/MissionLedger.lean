/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Domains.OperationsResearch.Inventory.StockFlow
public import PhyslibExt.SpaceSystems.MissionLedger
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! # Mission stock accounting via the zero-lead-time inventory model

Compare the prefix stocks in the mission ledger with the backorder recurrence in
P. H. Zipkin, *Foundations of Inventory Management*.
-/

@[expose] public section

namespace MissionLedger

open Finset

variable {ι : Type*}

/-- Every prefix stock is the step-by-step trace of the backlogged stock-flow model with
zero lead time, the gains as receipts and the draws as demands. -/
lemma stock_eq_stockTrace (s₀ : ι → ℝ) (flow : ι → ℕ → ℝ) (i : ι) (t : ℕ) :
    stock s₀ flow i t =
      Inventory.stockTrace (s₀ i) 0 Fin.elim0 (gains flow i) (draws flow i) t := by
  induction t with
  | zero => rw [stock_zero, Inventory.stockTrace_zero]
  | succ t ih =>
    rw [stock_succ, ih, Inventory.stockTrace_succ, Inventory.receipt_zero_lead]
    have h : flow i t = ((gains flow i t : NNReal) : ℝ) - ((draws flow i t : NNReal) : ℝ) := by
      simp only [gains, draws]
      rw [Real.coe_toNNReal', Real.coe_toNNReal']
      rcases le_total 0 (flow i t) with h | h
      · rw [max_eq_left h, max_eq_right (by linarith : -flow i t ≤ 0)]; ring
      · rw [max_eq_right h, max_eq_left (by linarith : 0 ≤ -flow i t)]; ring
    rw [h]
    ring

/-- Terminal accounting: the final stock is the initial stock plus all gains minus all draws
(the conservation identity of the stock-flow model at zero lead time). -/
lemma terminal_accounting (s₀ : ι → ℝ) (flow : ι → ℕ → ℝ) (i : ι) (N : ℕ) :
    stock s₀ flow i N =
      s₀ i + ∑ k ∈ range N, (gains flow i k : ℝ) - ∑ k ∈ range N, (draws flow i k : ℝ) := by
  rw [stock_eq_stockTrace]
  have hcons := Inventory.conservation (s₀ i) 0 Fin.elim0 (gains flow i) (draws flow i) N
  rw [Inventory.pipelineTotal_zero] at hcons
  have huniv : (Finset.univ : Finset (Fin 0)) = ∅ := by simp
  rw [huniv, Finset.sum_empty] at hcons
  simp only [add_zero] at hcons
  linarith

end MissionLedger

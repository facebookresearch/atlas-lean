/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Algebra.BigOperators.Fin
public import MathlibExt.OperationsResearch.Inventory.StockFlow

/-!
# Finite mission ledger checked at every prefix

A finite mission schedule gives, for each resource `i : ι` (for example stored electrical
energy, propellant mass and stored heat), a signed flow `flow i k` at each step `k`: positive
values add to the stock and negative values draw from it. Each resource keeps its own units;
resources are never added to one another.

## i. Overview

`stock s₀ flow i t` is the initial stock `s₀ i` plus the actual cumulative sum of the first `t`
flows of resource `i`. With zero lead time, gains as receipts and draws as demands, the
step-by-step trace of the backlogged stock-flow model `Inventory.stockTrace` reproduces this
stock at every prefix, and the model's conservation identity gives the terminal accounting.
`PrefixFeasible lo hi r s₀ flow N` checks every resource at every prefix `t ≤ N`, start and end
included: the floor raised by the reserve, `lo i + r i ≤ stock`, and the capacity
`stock ≤ hi i`. The reserve is deducted exactly once; deducting it at every step instead
removes it once per step. The schedule and the bounds are model inputs. Pointing and navigation
requirements stay external constraints; nothing here is a mission-success, qualification or
safety claim.

## ii. Key results

- `stock_eq_stockTrace`: prefix stocks are the zero-lead-time stock-flow trace.
- `terminal_accounting`: the final stock is the initial stock plus all gains minus all draws.
- `PrefixFeasible.terminal`: the prefix check contains the terminal check.
- `prefixFeasible_iff_reserve_deducted_once`: the reserve in the floor is one deduction from
  the initial stock.
- `stock_reserve_every_step`: a per-step reserve deduction removes the reserve `t` times.

## iii. Table of contents

- A. Model
- B. Prefix stocks and terminal accounting
- C. Prefix bounds and the reserve

## iv. References

- J. R. Wertz and W. J. Larson (eds.), *Space Mission Analysis and Design*, 3rd edition,
  chapters on mass and power budgets (margins and reserves held back once, every mission phase
  checked).
- P. H. Zipkin, *Foundations of Inventory Management*, backorder model (stock-flow recursion).
- `MathlibExt.OperationsResearch.Inventory.StockFlow`: the stock-flow trace and the
  conservation identity reused here.
-/

@[expose] public section

namespace MissionLedger

open Finset

variable {ι : Type*}

/-! ## A. Model -/

/-- Stock of resource `i` after the first `t` steps of the schedule: the initial stock `s₀ i`
plus the actual cumulative sum of the signed flows of steps `0, …, t - 1`. -/
def stock (s₀ : ι → ℝ) (flow : ι → ℕ → ℝ) (i : ι) (t : ℕ) : ℝ :=
  s₀ i + ∑ k ∈ range t, flow i k

/-- Gains of resource `i` at step `k`: the positive part of its signed flow. -/
noncomputable def gains (flow : ι → ℕ → ℝ) (i : ι) (k : ℕ) : NNReal :=
  (flow i k).toNNReal

/-- Draws of resource `i` at step `k`: the negative part of its signed flow. -/
noncomputable def draws (flow : ι → ℕ → ℝ) (i : ι) (k : ℕ) : NNReal :=
  (-flow i k).toNNReal

/-- Prefix feasibility over a horizon of `N` steps: for every resource `i` and every prefix
`t ≤ N` (the start `t = 0` and the end `t = N` included), the stock is at least the floor
`lo i` plus the reserve `r i` and at most the capacity `hi i`. The reserve is deducted once,
in this lower bound; it is not also a scheduled flow. -/
def PrefixFeasible (lo hi r s₀ : ι → ℝ) (flow : ι → ℕ → ℝ) (N : ℕ) : Prop :=
  ∀ i, ∀ t ≤ N, lo i + r i ≤ stock s₀ flow i t ∧ stock s₀ flow i t ≤ hi i

/-- A finite schedule written as a list of flows, `0` after its end. -/
def listFlow (l : List ℝ) (k : ℕ) : ℝ :=
  l.getD k 0

/-! ## B. Prefix stocks and terminal accounting -/

/-- Before any step the stock is the initial stock. -/
lemma stock_zero (s₀ : ι → ℝ) (flow : ι → ℕ → ℝ) (i : ι) :
    stock s₀ flow i 0 = s₀ i := by
  simp [stock]

/-- One step adds that step's signed flow. -/
lemma stock_succ (s₀ : ι → ℝ) (flow : ι → ℕ → ℝ) (i : ι) (t : ℕ) :
    stock s₀ flow i (t + 1) = stock s₀ flow i t + flow i t := by
  unfold stock
  rw [Finset.sum_range_succ]
  ring

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

/-! ## C. Prefix bounds and the reserve -/

/-- The prefix check contains the terminal check. -/
lemma PrefixFeasible.terminal {lo hi r s₀ : ι → ℝ} {flow : ι → ℕ → ℝ} {N : ℕ}
    (h : PrefixFeasible lo hi r s₀ flow N) (i : ι) :
    lo i + r i ≤ s₀ i + ∑ k ∈ range N, flow i k ∧ s₀ i + ∑ k ∈ range N, flow i k ≤ hi i := by
  exact h i N le_rfl

/-- The reserve is deducted exactly once: raising the floor by `r i` at every prefix is the
same as deducting `r i` once from the initial stock, with the original floor and the capacity
lowered by `r i`. -/
lemma prefixFeasible_iff_reserve_deducted_once (lo hi r s₀ : ι → ℝ) (flow : ι → ℕ → ℝ)
    (N : ℕ) :
    PrefixFeasible lo hi r s₀ flow N ↔ PrefixFeasible lo (hi - r) 0 (s₀ - r) flow N := by
  have hS : ∀ i t, stock (s₀ - r) flow i t = stock s₀ flow i t - r i := by
    intro i t
    unfold stock
    rw [Pi.sub_apply]
    ring
  unfold PrefixFeasible
  constructor
  · intro h i t ht
    obtain ⟨hlo, hhi⟩ := h i t ht
    rw [hS i t]
    simp only [Pi.zero_apply, Pi.sub_apply, add_zero]
    exact ⟨by linarith, by linarith⟩
  · intro h i t ht
    obtain ⟨hlo, hhi⟩ := h i t ht
    rw [hS i t] at hlo hhi
    simp only [Pi.zero_apply, Pi.sub_apply, add_zero] at hlo hhi
    exact ⟨by linarith, by linarith⟩

/-- Deducting the reserve as a flow at every step removes it `t` times by prefix `t`; from the
second step on this differs from the single deduction whenever `r i ≠ 0`. -/
lemma stock_reserve_every_step (s₀ r : ι → ℝ) (flow : ι → ℕ → ℝ) (i : ι) (t : ℕ) :
    stock s₀ (fun j k => flow j k - r j) i t = stock s₀ flow i t - t * r i ∧
      (2 ≤ t → r i ≠ 0 →
        stock s₀ (fun j k => flow j k - r j) i t ≠ stock (s₀ - r) flow i t) := by
  have hsum : (∑ k ∈ range t, (flow i k - r i)) = (∑ k ∈ range t, flow i k) - t * r i := by
    rw [Finset.sum_sub_distrib]
    congr 1
    simp [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hmain : stock s₀ (fun j k => flow j k - r j) i t = stock s₀ flow i t - t * r i := by
    change s₀ i + (∑ k ∈ range t, (flow i k - r i)) = stock s₀ flow i t - t * r i
    rw [hsum]
    unfold stock
    ring
  refine ⟨hmain, fun ht hr he => ?_⟩
  have hS : stock (s₀ - r) flow i t = stock s₀ flow i t - r i := by
    unfold stock
    rw [Pi.sub_apply]
    ring
  rw [hmain, hS] at he
  have ht2 : (2 : ℝ) ≤ (t : ℝ) := by exact_mod_cast ht
  have h1 : (t : ℝ) * r i = 1 * r i := by linarith
  have ht1 : (t : ℝ) = 1 := mul_right_cancel₀ hr h1
  linarith

end MissionLedger

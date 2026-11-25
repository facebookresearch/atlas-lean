/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Basic.NNReal.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.LinearCombination

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section

/-!
# Backlogged stock flow with deterministic delivery conservation

Backlogging inventory dynamics with lead time `L : ℕ` and real-valued net stock.
Initial pipeline, orders and demands are nonnegative (`NNReal`); every equality
involving net stock is in `ℝ` with casts before subtraction (never truncated
`NNReal` subtraction for net stock).

This file covers the backlogging model only: unmet demand accumulates as
negative net stock, never as lost sales. The lost-sales alternative is out
of scope here and is never mixed into this model. It does not extend the
financial `Accounting.InventoryFlow` model.

Section map (labels `C1` to `C7` are defined locally by this overview):
* C1 (event order / receipts): `receipt`, `receipt_of_lt`, `receipt_of_not_lt`,
  `receipt_zero_lead`. Order per period: receive scheduled quantity, place an
  order, receive immediately if `L = 0`, then serve demand. Genuine `Fin L`.
* C2 (trace / on-hand / backlog): `stockTrace`, `stockTrace_zero`,
  `stockTrace_succ`, `onHand`, `backlog`, `onHand_nonneg`, `backlog_nonneg`,
  `onHand_sub_backlog`, `onHand_mul_backlog`.
* C3 (outstanding pipeline): `pipeline`, `pipeline_apply`, `pipeline_apply_init`,
  `pipeline_apply_order`, `pipeline_head`, `pipeline_succ_tail`,
  `pipeline_succ_last`, `pipeline_zero_eq_init`, `pipeline_causal`.
* C4 (cumulative balance): `stockTrace_balance`.
* C5 (conservation + closed form): `pipelineTotal`, `pipelineTotal_zero`,
  `conservation`, `pipelineTotal_closedForm`. Single universal family covering
  `H = 0`, `H < L`, `H = L`, `H > L`; terminal pipeline retained.
* C6 (deterministic transition): `step`, `step_fst`, `step_snd`, `run`,
  `run_zero`, `run_succ`, `run_fst_eq_stockTrace`, `run_snd_eq_pipeline`.
  MDP-ready state/transition interface only; not a finite-state MDP instance,
  no stock cap, no action saturation, no claim that stock alone is Markov for
  `L > 0`. A later consumer may supply a finite closed state subset.
* C7 (tests): separate test file only. Boundary and API fixtures present
  there: main `L = 2, H = 5` stockout fixture (final stock `-2`, pipeline
  `6`, total `4`); immediate `L = 0` delivery; `H = 0`; `H < L` with
  unreceived initial stock; `H = L`; fractional quantities; on-hand/backlog
  pins; and both counterexamples (dropping the terminal pipeline, delaying
  a zero-lead-time receipt).
-/

namespace Inventory

/-- C1: scheduled receipt at period `t`.

Event order per period: receive the scheduled quantity, place an order,
receive that new order immediately if `L = 0`, then serve demand.
Single guarded rule: initial-pipeline coordinate `t` if `t < L`, else
order `t - L`. For `L = 0` this gives order `t` (since `t - 0 = t`).
Uses the genuine `Fin L` type, not a padded length-one vector. -/
def receipt (L : ℕ) (initPipe : Fin L → NNReal) (order : ℕ → NNReal) (t : ℕ) : NNReal :=
  if h : t < L then initPipe ⟨t, h⟩ else order (t - L)

/-- C1: receipt equals the initial-pipeline coordinate when `t < L`. -/
theorem receipt_of_lt (L : ℕ) (initPipe : Fin L → NNReal) (order : ℕ → NNReal) (t : ℕ) (h : t < L) :
    receipt L initPipe order t = initPipe ⟨t, h⟩ := by
  unfold receipt
  exact dite_eq_left h

/-- C1: receipt equals the already-placed order `t - L` when `¬ t < L`. -/
theorem receipt_of_not_lt (L : ℕ) (initPipe : Fin L → NNReal) (order : ℕ → NNReal)
    (t : ℕ) (h : ¬ t < L) :
    receipt L initPipe order t = order (t - L) := by
  unfold receipt
  exact dite_eq_right h

/-- C1: at `L = 0` the receipt is the immediately delivered current order. -/
theorem receipt_zero_lead (initPipe : Fin 0 → NNReal) (order : ℕ → NNReal) (t : ℕ) :
    receipt 0 initPipe order t = order t := by
  have h0 : ¬ t < 0 := Nat.not_lt_zero t
  calc receipt 0 initPipe order t
      = order (t - 0) := receipt_of_not_lt 0 initPipe order t h0
    _ = order t := by rw [Nat.sub_zero]

/-- C2: backlogged net-stock trace. `I 0 = I0` and
`I (t + 1) = I t + receipt t - demand t` in `ℝ`, with `NNReal` casts
before subtraction. `I0` may be negative. -/
def stockTrace (I0 : ℝ) (L : ℕ) (initPipe : Fin L → NNReal) (order : ℕ → NNReal)
    (demand : ℕ → NNReal) : ℕ → ℝ
  | 0 => I0
  | t + 1 => stockTrace I0 L initPipe order demand t
      + (receipt L initPipe order t : ℝ) - (demand t : ℝ)

/-- C2: initial net stock equation. -/
theorem stockTrace_zero (I0 : ℝ) (L : ℕ) (initPipe : Fin L → NNReal)
    (order : ℕ → NNReal) (demand : ℕ → NNReal) :
    stockTrace I0 L initPipe order demand 0 = I0 := by
  rfl

/-- C2: one-step net-stock recurrence in `ℝ`. -/
theorem stockTrace_succ (I0 : ℝ) (L : ℕ) (initPipe : Fin L → NNReal)
    (order : ℕ → NNReal) (demand : ℕ → NNReal) (t : ℕ) :
    stockTrace I0 L initPipe order demand (t + 1)
      = stockTrace I0 L initPipe order demand t
        + (receipt L initPipe order t : ℝ) - (demand t : ℝ) := by
  rfl

/-- C2: on-hand stock `max x 0` for a net level `x` (apply to `stockTrace` at any `t`). -/
noncomputable def onHand (x : ℝ) : ℝ := max x 0

/-- C2: backlog `max (-x) 0` for a net level `x` (apply to `stockTrace` at any `t`). -/
noncomputable def backlog (x : ℝ) : ℝ := max (-x) 0

/-- C2: on-hand nonnegativity. -/
theorem onHand_nonneg (x : ℝ) : 0 ≤ onHand x := by
  unfold onHand
  exact le_max_right x 0

/-- C2: backlog nonnegativity. -/
theorem backlog_nonneg (x : ℝ) : 0 ≤ backlog x := by
  unfold backlog
  exact le_max_right (-x) 0

/-- C2: on-hand minus backlog recovers the net level. -/
theorem onHand_sub_backlog (x : ℝ) : onHand x - backlog x = x := by
  unfold onHand backlog
  rcases le_total 0 x with hx | hx
  · have h1 : max x 0 = x := max_eq_left hx
    have h2 : max (-x) 0 = 0 := max_eq_right (neg_nonpos.mpr hx)
    rw [h1, h2, sub_zero]
  · have h1 : max x 0 = 0 := max_eq_right hx
    have h2 : max (-x) 0 = -x := max_eq_left (neg_nonneg.mpr hx)
    rw [h1, h2, zero_sub, neg_neg]

/-- C2: on-hand and backlog cannot both be positive (product is zero). -/
theorem onHand_mul_backlog (x : ℝ) : onHand x * backlog x = 0 := by
  unfold onHand backlog
  rcases le_total 0 x with hx | hx
  · have h2 : max (-x) 0 = 0 := max_eq_right (neg_nonpos.mpr hx)
    rw [h2, mul_zero]
  · have h1 : max x 0 = 0 := max_eq_right hx
    rw [h1, zero_mul]

/-- C3: length-`L` outstanding pipeline before the receipts of period `t`.
Coordinate `j` is the receipt scheduled at `t + j.val`: initial pipeline at
`t + j.val` when `t + j.val < L`, else the already-placed order
`t + j.val - L`. Empty (no coordinates) at `L = 0`. -/
def pipeline (L : ℕ) (initPipe : Fin L → NNReal) (order : ℕ → NNReal) (t : ℕ) : Fin L → NNReal :=
  fun j : Fin L => receipt L initPipe order (t + j.val)

/-- C3: pipeline coordinate unfolding: scheduled receipt at `t + j.val`. -/
theorem pipeline_apply (L : ℕ) (initPipe : Fin L → NNReal) (order : ℕ → NNReal)
    (t : ℕ) (j : Fin L) :
    pipeline L initPipe order t j = receipt L initPipe order (t + j.val) := by
  rfl

/-- C3: pipeline coordinate from remaining initial stock when `t + j.val < L`. -/
theorem pipeline_apply_init (L : ℕ) (initPipe : Fin L → NNReal) (order : ℕ → NNReal)
    (t : ℕ) (j : Fin L) (h : t + j.val < L) :
    pipeline L initPipe order t j = initPipe ⟨t + j.val, h⟩ := by
  calc pipeline L initPipe order t j
      = receipt L initPipe order (t + j.val) := pipeline_apply L initPipe order t j
    _ = initPipe ⟨t + j.val, h⟩ := receipt_of_lt L initPipe order (t + j.val) h

/-- C3: pipeline coordinate from an already-placed order when `¬ t + j.val < L`. -/
theorem pipeline_apply_order (L : ℕ) (initPipe : Fin L → NNReal) (order : ℕ → NNReal)
    (t : ℕ) (j : Fin L) (h : ¬ t + j.val < L) :
    pipeline L initPipe order t j = order (t + j.val - L) := by
  calc pipeline L initPipe order t j
      = receipt L initPipe order (t + j.val) := pipeline_apply L initPipe order t j
    _ = order (t + j.val - L) := receipt_of_not_lt L initPipe order (t + j.val) h

/-- C3: for `L > 0`, the pipeline head is the current receipt. -/
theorem pipeline_head (L : ℕ) (hL : 0 < L) (initPipe : Fin L → NNReal)
    (order : ℕ → NNReal) (t : ℕ) :
    pipeline L initPipe order t ⟨0, hL⟩ = receipt L initPipe order t := by
  calc pipeline L initPipe order t ⟨0, hL⟩
      = receipt L initPipe order (t + (⟨0, hL⟩ : Fin L).val) :=
        pipeline_apply L initPipe order t ⟨0, hL⟩
    _ = receipt L initPipe order t := by simp

/-- C3: for `L > 0`, successor-pipeline tail: new `j` with `j.val + 1 < L`
equals old `j.val + 1`. -/
theorem pipeline_succ_tail (L : ℕ) (hL : 0 < L) (initPipe : Fin L → NNReal)
    (order : ℕ → NNReal) (t : ℕ) (j : Fin L) (h : j.val + 1 < L) :
    pipeline L initPipe order (t + 1) j = pipeline L initPipe order t ⟨j.val + 1, h⟩ := by
  have _ := hL
  calc pipeline L initPipe order (t + 1) j
      = receipt L initPipe order ((t + 1) + j.val) := pipeline_apply L initPipe order (t + 1) j
    _ = receipt L initPipe order (t + (j.val + 1)) := by congr 1; omega
    _ = pipeline L initPipe order t ⟨j.val + 1, h⟩ :=
        (pipeline_apply L initPipe order t ⟨j.val + 1, h⟩).symm

/-- C3: for `L > 0`, successor-pipeline last coordinate: new `j` with
`j.val + 1 = L` equals the order placed at `t`. With `pipeline_succ_tail`,
the successor is the old tail followed by `order t`. -/
theorem pipeline_succ_last (L : ℕ) (hL : 0 < L) (initPipe : Fin L → NNReal)
    (order : ℕ → NNReal) (t : ℕ) (j : Fin L) (hj : j.val + 1 = L) :
    pipeline L initPipe order (t + 1) j = order t := by
  have _ := hL
  have heq : (t + 1) + j.val = t + L := by omega
  have hnot : ¬ (t + 1) + j.val < L := by omega
  calc pipeline L initPipe order (t + 1) j
      = receipt L initPipe order ((t + 1) + j.val) := pipeline_apply L initPipe order (t + 1) j
    _ = order (((t + 1) + j.val) - L) :=
        receipt_of_not_lt L initPipe order ((t + 1) + j.val) hnot
    _ = order t := by rw [heq, Nat.add_sub_cancel]

/-- C3: at `L = 0` the pipeline is empty; it agrees with the empty initial pipeline. -/
theorem pipeline_zero_eq_init (initPipe : Fin 0 → NNReal) (order : ℕ → NNReal) (t : ℕ) :
    pipeline 0 initPipe order t = initPipe := by
  funext j
  exact Fin.elim0 j

/-- C3: causal meaning for `L > 0`: the pipeline at `t` never depends on orders
placed at `t` or later. Two order streams agreeing on all `s < t` give equal
pipelines at `t`. -/
theorem pipeline_causal (L : ℕ) (hL : 0 < L) (initPipe : Fin L → NNReal)
    (order1 : ℕ → NNReal) (order2 : ℕ → NNReal) (t : ℕ)
    (h : ∀ s : ℕ, s < t → order1 s = order2 s) :
    pipeline L initPipe order1 t = pipeline L initPipe order2 t := by
  have _ := hL
  funext j
  by_cases hj : t + j.val < L
  · calc pipeline L initPipe order1 t j
        = initPipe ⟨t + j.val, hj⟩ := pipeline_apply_init L initPipe order1 t j hj
      _ = pipeline L initPipe order2 t j :=
          (pipeline_apply_init L initPipe order2 t j hj).symm
  · have hjL := j.isLt
    have hlt : t + j.val - L < t := by omega
    calc pipeline L initPipe order1 t j
        = order1 (t + j.val - L) := pipeline_apply_order L initPipe order1 t j hj
      _ = order2 (t + j.val - L) := h _ hlt
      _ = pipeline L initPipe order2 t j :=
          (pipeline_apply_order L initPipe order2 t j hj).symm

/-- C4: cumulative net-stock balance at every `H` in `ℝ`. -/
theorem stockTrace_balance (I0 : ℝ) (L : ℕ) (initPipe : Fin L → NNReal)
    (order : ℕ → NNReal) (demand : ℕ → NNReal) (H : ℕ) :
    stockTrace I0 L initPipe order demand H
      = I0 + Finset.sum (Finset.range H) (fun t : ℕ => (receipt L initPipe order t : ℝ))
        - Finset.sum (Finset.range H) (fun t : ℕ => (demand t : ℝ)) := by
  induction H with
  | zero =>
    simp [stockTrace_zero]
  | succ H IH =>
    simp only [stockTrace_succ, IH, Finset.sum_range_succ]
    ring

/-- C5: total outstanding pipeline quantity at `H` in `ℝ` (sum of casts). -/
def pipelineTotal (L : ℕ) (initPipe : Fin L → NNReal) (order : ℕ → NNReal) (H : ℕ) : ℝ :=
  Finset.sum (Finset.univ : Finset (Fin L)) (fun j : Fin L => (pipeline L initPipe order H j : ℝ))

/-- C5: at `L = 0` the terminal pipeline total is zero (empty sum). -/
theorem pipelineTotal_zero (initPipe : Fin 0 → NNReal) (order : ℕ → NNReal) (H : ℕ) :
    pipelineTotal 0 initPipe order H = 0 := by
  simp [pipelineTotal]

/-- Receipt one lead time ahead is the current order. -/
private theorem receipt_add_lead (L : ℕ) (initPipe : Fin L → NNReal) (order : ℕ → NNReal) (H : ℕ) :
    receipt L initPipe order (H + L) = order H := by
  have hnot : ¬ H + L < L := by omega
  calc receipt L initPipe order (H + L)
      = order ((H + L) - L) := receipt_of_not_lt L initPipe order (H + L) hnot
    _ = order H := by rw [Nat.add_sub_cancel]

/-- The pipeline at time zero is the initial pipeline. -/
private theorem pipeline_at_zero (L : ℕ) (initPipe : Fin L → NNReal) (order : ℕ → NNReal) :
    pipeline L initPipe order 0 = initPipe := by
  funext j
  have hj : 0 + j.val < L := by have hjL := j.isLt; omega
  have e := pipeline_apply_init L initPipe order 0 j hj
  have hjej : (⟨0 + j.val, hj⟩ : Fin L) = j := Fin.ext (by simp)
  calc pipeline L initPipe order 0 j
      = initPipe (⟨0 + j.val, hj⟩ : Fin L) := e
    _ = initPipe j := by rw [hjej]

/-- Pipeline-total one-step shift: the next total drops the current receipt
and adds the current order. -/
private theorem pipelineTotal_succ (L : ℕ) (initPipe : Fin L → NNReal)
    (order : ℕ → NNReal) (H : ℕ) :
    pipelineTotal L initPipe order (H + 1)
      = pipelineTotal L initPipe order H - (receipt L initPipe order H : ℝ) + (order H : ℝ) := by
  cases L with
  | zero =>
    simp [pipelineTotal_zero, receipt_zero_lead]
  | succ n =>
    have hLHS : pipelineTotal (n + 1) initPipe order (H + 1)
        = ∑ j : Fin (n + 1), (receipt (n + 1) initPipe order ((H + 1) + j.val) : ℝ) := by
      unfold pipelineTotal
      apply Finset.sum_congr rfl
      intro j _
      rw [pipeline_apply]
    have hRHS : pipelineTotal (n + 1) initPipe order H
        = ∑ j : Fin (n + 1), (receipt (n + 1) initPipe order (H + j.val) : ℝ) := by
      unfold pipelineTotal
      apply Finset.sum_congr rfl
      intro j _
      rw [pipeline_apply]
    rw [hLHS, hRHS, Fin.sum_univ_castSucc, Fin.sum_univ_succ]
    have hmid : (∑ i : Fin n, (receipt (n + 1) initPipe order ((H + 1) + (i.castSucc).val) : ℝ))
        = ∑ i : Fin n, (receipt (n + 1) initPipe order (H + (i.succ).val) : ℝ) := by
      apply Finset.sum_congr rfl
      intro i _
      have e1 : (i.castSucc).val = i.val := Fin.val_castSucc i
      have e2 : (i.succ).val = i.val + 1 := Fin.val_succ i
      have hidx : (H + 1) + (i.castSucc).val = H + (i.succ).val := by omega
      rw [hidx]
    have hendLast : (receipt (n + 1) initPipe order ((H + 1) + (Fin.last n).val) : ℝ)
        = (order H : ℝ) := by
      have hv : (Fin.last n).val = n := Fin.val_last n
      have hr : receipt (n + 1) initPipe order (H + (n + 1)) = order H :=
        receipt_add_lead (n + 1) initPipe order H
      have hidx : (H + 1) + (Fin.last n).val = H + (n + 1) := by omega
      rw [hidx, hr]
    have hendZero : (receipt (n + 1) initPipe order (H + (0 : Fin (n + 1)).val) : ℝ)
        = (receipt (n + 1) initPipe order H : ℝ) := by
      have hidx : H + (0 : Fin (n + 1)).val = H := by simp
      rw [hidx]
    rw [hmid, hendLast, hendZero]
    ring

/-- C5: stock-plus-pipeline conservation at every `H`, retaining every terminal
outstanding order. Single universal family covering `H = 0`, `H < L`, `H = L`
and `H > L`. -/
theorem conservation (I0 : ℝ) (L : ℕ) (initPipe : Fin L → NNReal)
    (order : ℕ → NNReal) (demand : ℕ → NNReal) (H : ℕ) :
    stockTrace I0 L initPipe order demand H + pipelineTotal L initPipe order H
      = I0 + Finset.sum (Finset.univ : Finset (Fin L)) (fun j : Fin L => (initPipe j : ℝ))
        + Finset.sum (Finset.range H) (fun t : ℕ => (order t : ℝ))
        - Finset.sum (Finset.range H) (fun t : ℕ => (demand t : ℝ)) := by
  induction H with
  | zero =>
    have hP0 : pipelineTotal L initPipe order 0
        = Finset.sum (Finset.univ : Finset (Fin L)) (fun j : Fin L => (initPipe j : ℝ)) := by
      simp only [pipelineTotal, pipeline_at_zero]
    simp [stockTrace_zero, hP0]
  | succ H IH =>
    have hstep := stockTrace_succ I0 L initPipe order demand H
    have hshift := pipelineTotal_succ L initPipe order H
    simp only [hstep, hshift, Finset.sum_range_succ]
    linear_combination IH

/-- C5: closed form of the terminal pipeline total: remaining initial coordinates
`H ≤ j.val` plus orders `H - L ≤ t` with `t < H` (that is,
`max(0, H - L) ≤ t < H`). For `L = 0`, `H - 0 = H` so the order filter over
`range H` is empty. -/
theorem pipelineTotal_closedForm (L : ℕ) (initPipe : Fin L → NNReal) (order : ℕ → NNReal) (H : ℕ) :
    pipelineTotal L initPipe order H
      = Finset.sum
          (Finset.filter (fun j : Fin L => H ≤ j.val) (Finset.univ : Finset (Fin L)))
          (fun j : Fin L => (initPipe j : ℝ))
        + Finset.sum (Finset.filter (fun t : ℕ => H - L ≤ t) (Finset.range H))
          (fun t : ℕ => (order t : ℝ)) := by
  have hsplit := Finset.sum_filter_add_sum_filter_not (Finset.univ : Finset (Fin L))
    (fun j : Fin L => H + j.val < L) (fun j : Fin L => (pipeline L initPipe order H j : ℝ))
  have hLHS : pipelineTotal L initPipe order H
      = Finset.sum (Finset.filter (fun j : Fin L => H + j.val < L) Finset.univ)
          (fun j : Fin L => (pipeline L initPipe order H j : ℝ))
      + Finset.sum (Finset.filter (fun j : Fin L => ¬ H + j.val < L) Finset.univ)
          (fun j : Fin L => (pipeline L initPipe order H j : ℝ)) := by
    unfold pipelineTotal
    exact hsplit.symm
  rw [hLHS]
  have hA : Finset.sum (Finset.filter (fun j : Fin L => H + j.val < L) Finset.univ)
        (fun j : Fin L => (pipeline L initPipe order H j : ℝ))
      = Finset.sum (Finset.filter (fun j : Fin L => H ≤ j.val) Finset.univ)
        (fun j : Fin L => (initPipe j : ℝ)) := by
    refine Finset.sum_bij
      (fun a ha => (⟨H + a.val, (Finset.mem_filter.mp ha).2⟩ : Fin L)) ?_ ?_ ?_ ?_
    · intro a ha
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact Nat.le_add_right H a.val
    · intro a₁ ha₁ a₂ ha₂ heq
      have hval : H + a₁.val = H + a₂.val := Fin.ext_iff.mp heq
      have hveq : a₁.val = a₂.val := by omega
      exact Fin.ext hveq
    · intro b hb
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb
      have hbL := b.isLt
      have ha_mem : (⟨b.val - H, by omega⟩ : Fin L)
          ∈ Finset.filter (fun j : Fin L => H + j.val < L) Finset.univ := by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        show H + (b.val - H) < L
        omega
      refine ⟨⟨b.val - H, by omega⟩, ha_mem, ?_⟩
      apply Fin.ext
      change H + (b.val - H) = b.val
      omega
    · intro a ha
      have hmem : H + a.val < L := (Finset.mem_filter.mp ha).2
      have e1 : pipeline L initPipe order H a = receipt L initPipe order (H + a.val) :=
        pipeline_apply L initPipe order H a
      have e2 : receipt L initPipe order (H + a.val) = initPipe (⟨H + a.val, hmem⟩ : Fin L) :=
        receipt_of_lt L initPipe order (H + a.val) hmem
      rw [e1, e2]
  have hB : Finset.sum (Finset.filter (fun j : Fin L => ¬ H + j.val < L) Finset.univ)
        (fun j : Fin L => (pipeline L initPipe order H j : ℝ))
      = Finset.sum (Finset.filter (fun t : ℕ => H - L ≤ t) (Finset.range H))
        (fun t : ℕ => (order t : ℝ)) := by
    refine Finset.sum_bij (fun a ha => H + a.val - L) ?_ ?_ ?_ ?_
    · intro a ha
      have ha' : ¬ H + a.val < L := (Finset.mem_filter.mp ha).2
      have haL := a.isLt
      simp only [Finset.mem_filter, Finset.mem_range]
      change H + a.val - L < H ∧ H - L ≤ H + a.val - L
      constructor
      · omega
      · omega
    · intro a₁ ha₁ a₂ ha₂ heq
      have ha₁' : ¬ H + a₁.val < L := (Finset.mem_filter.mp ha₁).2
      have ha₂' : ¬ H + a₂.val < L := (Finset.mem_filter.mp ha₂).2
      have heq' : H + a₁.val - L = H + a₂.val - L := heq
      have hval : H + a₁.val = H + a₂.val := by omega
      have hveq : a₁.val = a₂.val := by omega
      exact Fin.ext hveq
    · intro b hb
      simp only [Finset.mem_filter, Finset.mem_range] at hb
      obtain ⟨hbH, hbL⟩ := hb
      have ha_mem : (⟨b + L - H, by omega⟩ : Fin L)
          ∈ Finset.filter (fun j : Fin L => ¬ H + j.val < L) Finset.univ := by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        show ¬ H + (b + L - H) < L
        omega
      refine ⟨⟨b + L - H, by omega⟩, ha_mem, ?_⟩
      change H + (b + L - H) - L = b
      omega
    · intro a ha
      have hmem : ¬ H + a.val < L := (Finset.mem_filter.mp ha).2
      calc ((pipeline L initPipe order H a : ℝ))
          = ((receipt L initPipe order (H + a.val) : ℝ)) := by rw [pipeline_apply]
        _ = ((order (H + a.val - L) : ℝ)) := by
            rw [receipt_of_not_lt L initPipe order (H + a.val) hmem]
  rw [hA, hB]

/-- C6: deterministic backlogging transition on `(net stock, length-L pipeline)`
with order `q` and demand `d` inputs. The receipt is the pipeline head for
`L > 0` and the immediate order `q` for `L = 0`. New stock adds the receipt
and subtracts demand in `ℝ` (no cap, no saturation). The new pipeline is the
old tail followed by `q` (vacuous at `L = 0`). Deterministic by construction;
MDP-ready interface only, not a finite-state MDP instance. -/
def step (L : ℕ) (s : ℝ × (Fin L → NNReal)) (q : NNReal) (d : NNReal) : ℝ × (Fin L → NNReal) :=
  let r : NNReal := if hL : 0 < L then s.2 ⟨0, hL⟩ else q
  let I' : ℝ := s.1 + (r : ℝ) - (d : ℝ)
  let pipe' : Fin L → NNReal := fun j : Fin L => if h : j.val + 1 < L then s.2 ⟨j.val + 1, h⟩ else q
  (I', pipe')

/-- C6: first-component equation for `step` (head receipt for `L > 0`,
immediate `q` for `L = 0`). -/
theorem step_fst (L : ℕ) (s : ℝ × (Fin L → NNReal)) (q : NNReal) (d : NNReal) :
    (step L s q d).1 = s.1 + ↑(if hL : 0 < L then s.2 ⟨0, hL⟩ else q) - (d : ℝ) := by
  rfl

/-- C6: second-component equation for `step` (old tail followed by `q`). -/
theorem step_snd (L : ℕ) (s : ℝ × (Fin L → NNReal)) (q : NNReal) (d : NNReal) (j : Fin L) :
    (step L s q d).2 j = (if h : j.val + 1 < L then s.2 ⟨j.val + 1, h⟩ else q) := by
  rfl

/-- C6: iteration of `step` for `H` periods from `(I0, initPipe)`, using
`order H` and `demand H` at step `H`. No stock cap or action saturation;
no claim that stock alone is a Markov state for `L > 0`. -/
def run (I0 : ℝ) (L : ℕ) (initPipe : Fin L → NNReal) (order : ℕ → NNReal)
    (demand : ℕ → NNReal) : ℕ → ℝ × (Fin L → NNReal)
  | 0 => (I0, initPipe)
  | H + 1 => step L (run I0 L initPipe order demand H) (order H) (demand H)

/-- C6: iteration initial equation. -/
theorem run_zero (I0 : ℝ) (L : ℕ) (initPipe : Fin L → NNReal)
    (order : ℕ → NNReal) (demand : ℕ → NNReal) :
    run I0 L initPipe order demand 0 = (I0, initPipe) := by
  rfl

/-- C6: iteration step equation. -/
theorem run_succ (I0 : ℝ) (L : ℕ) (initPipe : Fin L → NNReal)
    (order : ℕ → NNReal) (demand : ℕ → NNReal) (H : ℕ) :
    run I0 L initPipe order demand (H + 1)
      = step L (run I0 L initPipe order demand H) (order H) (demand H) := by
  rfl

/-- Iteration agrees with the outstanding pipeline (auxiliary form used by
`run_fst_eq_stockTrace`, which needs the second component at the same step). -/
private theorem run_snd_aux (I0 : ℝ) (L : ℕ) (initPipe : Fin L → NNReal)
    (order : ℕ → NNReal) (demand : ℕ → NNReal) (H : ℕ) :
    (run I0 L initPipe order demand H).2 = pipeline L initPipe order H := by
  induction H with
  | zero =>
    rw [run_zero]
    exact (pipeline_at_zero L initPipe order).symm
  | succ H IH =>
    have hrun := run_succ I0 L initPipe order demand H
    rw [hrun]
    funext j
    have hstep := step_snd L (run I0 L initPipe order demand H) (order H) (demand H) j
    rw [hstep, IH]
    by_cases hj : j.val + 1 < L
    · rw [dite_eq_left hj]
      have hL : 0 < L := by omega
      exact (pipeline_succ_tail L hL initPipe order H j hj).symm
    · rw [dite_eq_right hj]
      by_cases hL : 0 < L
      · have hj_eq : j.val + 1 = L := by have hjL := j.isLt; omega
        exact (pipeline_succ_last L hL initPipe order H j hj_eq).symm
      · have hL0 : L = 0 := by omega
        subst hL0
        exact Fin.elim0 j

/-- C6: iteration agrees with the net-stock trace (first component). -/
theorem run_fst_eq_stockTrace (I0 : ℝ) (L : ℕ) (initPipe : Fin L → NNReal)
    (order : ℕ → NNReal) (demand : ℕ → NNReal) (H : ℕ) :
    (run I0 L initPipe order demand H).1 = stockTrace I0 L initPipe order demand H := by
  induction H with
  | zero =>
    rw [run_zero, stockTrace_zero]
  | succ H IH =>
    have hrun := run_succ I0 L initPipe order demand H
    have hstep := step_fst L (run I0 L initPipe order demand H) (order H) (demand H)
    have hsnd := run_snd_aux I0 L initPipe order demand H
    have hstock := stockTrace_succ I0 L initPipe order demand H
    by_cases hL : 0 < L
    · have hhead : (if hL' : 0 < L then (run I0 L initPipe order demand H).2 ⟨0, hL'⟩ else order H)
          = receipt L initPipe order H := by
        rw [dite_eq_left hL, hsnd]
        exact pipeline_head L hL initPipe order H
      rw [hrun, hstep, IH, hstock, hhead]
    · have hL0 : L = 0 := by omega
      subst hL0
      have hhead : (if hL' : 0 < 0 then (run I0 0 initPipe order demand H).2 ⟨0, hL'⟩ else order H)
          = receipt 0 initPipe order H := by
        rw [dite_eq_right hL]
        exact (receipt_zero_lead initPipe order H).symm
      rw [hrun, hstep, IH, hstock, hhead]

/-- C6: iteration agrees with the outstanding pipeline (second component).
The pipeline is independent of `I0` and demands; they appear only via `run`. -/
theorem run_snd_eq_pipeline (I0 : ℝ) (L : ℕ) (initPipe : Fin L → NNReal)
    (order : ℕ → NNReal) (demand : ℕ → NNReal) (H : ℕ) :
    (run I0 L initPipe order demand H).2 = pipeline L initPipe order H := by
  exact run_snd_aux I0 L initPipe order demand H

end Inventory

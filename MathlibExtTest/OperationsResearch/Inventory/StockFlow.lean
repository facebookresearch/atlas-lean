/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.OperationsResearch.Inventory.StockFlow
import Mathlib.Algebra.BigOperators.Fin

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Tests for backlogged stock flow with deterministic delivery conservation

Concrete fixtures exercising every C7 boundary: the main `L = 2, H = 5`
fixture with a stockout and nonzero terminal pipeline, immediate `L = 0`
delivery, `H = 0`, `H < L` with unreceived initial stock, `H = L`,
fractional nonnegative quantities, and both counterexamples (dropping the
terminal pipeline and delaying a zero-lead-time receipt break the balance).

Each fixture has independently reduced value pins alongside applications of
the exported theorems; the two agree on every conservation total.
-/

namespace Inventory

/-- Main orders: `(1, 2, 0, 5, 1)`. -/
def orderMain : ℕ → NNReal
  | 0 => 1
  | 1 => 2
  | 2 => 0
  | 3 => 5
  | 4 => 1
  | _ => 0

/-- Main demands: `(2, 6, 1, 3, 0)`. -/
def demandMain : ℕ → NNReal
  | 0 => 2
  | 1 => 6
  | 2 => 1
  | 3 => 3
  | 4 => 0
  | _ => 0

/-- Main initial pipeline `(4, 0)` at `L = 2`. -/
def initPipeMain : Fin 2 → NNReal := fun j => match j.val with
  | 0 => 4
  | _ => 0

theorem orderMain_0 : orderMain 0 = 1 := rfl
theorem orderMain_1 : orderMain 1 = 2 := rfl
theorem orderMain_2 : orderMain 2 = 0 := rfl
theorem orderMain_3 : orderMain 3 = 5 := rfl
theorem orderMain_4 : orderMain 4 = 1 := rfl
theorem demandMain_0 : demandMain 0 = 2 := rfl
theorem demandMain_1 : demandMain 1 = 6 := rfl
theorem demandMain_2 : demandMain 2 = 1 := rfl
theorem demandMain_3 : demandMain 3 = 3 := rfl
theorem demandMain_4 : demandMain 4 = 0 := rfl
theorem initPipeMain_0 : initPipeMain ⟨0, by omega⟩ = 4 := rfl
theorem initPipeMain_1 : initPipeMain ⟨1, by omega⟩ = 0 := rfl

theorem receiptMain_0 : receipt 2 initPipeMain orderMain 0 = 4 := by
  have h : (0 : ℕ) < 2 := by omega
  rw [receipt_of_lt 2 initPipeMain orderMain 0 h]
  rfl

theorem receiptMain_1 : receipt 2 initPipeMain orderMain 1 = 0 := by
  have h : (1 : ℕ) < 2 := by omega
  rw [receipt_of_lt 2 initPipeMain orderMain 1 h]
  rfl

theorem receiptMain_2 : receipt 2 initPipeMain orderMain 2 = 1 := by
  have h : ¬ (2 : ℕ) < 2 := by omega
  rw [receipt_of_not_lt 2 initPipeMain orderMain 2 h]
  rfl

theorem receiptMain_3 : receipt 2 initPipeMain orderMain 3 = 2 := by
  have h : ¬ (3 : ℕ) < 2 := by omega
  rw [receipt_of_not_lt 2 initPipeMain orderMain 3 h]
  rfl

theorem receiptMain_4 : receipt 2 initPipeMain orderMain 4 = 0 := by
  have h : ¬ (4 : ℕ) < 2 := by omega
  rw [receipt_of_not_lt 2 initPipeMain orderMain 4 h]
  rfl

theorem receiptMain_5 : receipt 2 initPipeMain orderMain 5 = 5 := by
  have h : ¬ (5 : ℕ) < 2 := by omega
  rw [receipt_of_not_lt 2 initPipeMain orderMain 5 h]
  rfl

theorem receiptMain_6 : receipt 2 initPipeMain orderMain 6 = 1 := by
  have h : ¬ (6 : ℕ) < 2 := by omega
  rw [receipt_of_not_lt 2 initPipeMain orderMain 6 h]
  rfl

/-- C7 main fixture: final net stock is `-2` (a stockout). -/
theorem testMainStock : stockTrace 3 2 initPipeMain orderMain demandMain 5 = -2 := by
  simp only [stockTrace_succ, stockTrace_zero, receiptMain_0, receiptMain_1,
    receiptMain_2, receiptMain_3, receiptMain_4,
    demandMain_0, demandMain_1, demandMain_2, demandMain_3, demandMain_4]
  norm_num

/-- C7 main fixture: outstanding pipeline total is `6` (nonzero terminal). -/
theorem testMainPipeline : pipelineTotal 2 initPipeMain orderMain 5 = 6 := by
  simp [pipelineTotal, Fin.sum_univ_two, pipeline_apply, receiptMain_5, receiptMain_6]
  norm_num

/-- C7 main fixture: the conservation total is `4`. -/
theorem testMainTotal :
    stockTrace 3 2 initPipeMain orderMain demandMain 5
      + pipelineTotal 2 initPipeMain orderMain 5 = 4 := by
  rw [testMainStock, testMainPipeline]
  norm_num

/-- C7 main fixture: initial-pipeline sum is `4`. -/
theorem testMainInitSum :
    Finset.sum (Finset.univ : Finset (Fin 2)) (fun j : Fin 2 => (initPipeMain j : ℝ)) = 4 := by
  simp [Fin.sum_univ_two, initPipeMain]

/-- C7 main fixture: order sum over `range 5` is `9`. -/
theorem testMainOrderSum :
    Finset.sum (Finset.range 5) (fun t : ℕ => (orderMain t : ℝ)) = 9 := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero,
    orderMain_0, orderMain_1, orderMain_2, orderMain_3, orderMain_4]
  norm_num

/-- C7 main fixture: demand sum over `range 5` is `12`. -/
theorem testMainDemandSum :
    Finset.sum (Finset.range 5) (fun t : ℕ => (demandMain t : ℝ)) = 12 := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero,
    demandMain_0, demandMain_1, demandMain_2, demandMain_3, demandMain_4]
  norm_num

/-- C7 main fixture: conservation right-hand side is `4`, agreeing with `testMainTotal`. -/
theorem testMainRHS :
    (3 : ℝ) + Finset.sum (Finset.univ : Finset (Fin 2)) (fun j : Fin 2 => (initPipeMain j : ℝ))
      + Finset.sum (Finset.range 5) (fun t : ℕ => (orderMain t : ℝ))
      - Finset.sum (Finset.range 5) (fun t : ℕ => (demandMain t : ℝ)) = 4 := by
  rw [testMainInitSum, testMainOrderSum, testMainDemandSum]
  norm_num

/-- C7 main fixture: `conservation` applied at the fixture. -/
theorem testMainConservation :
    stockTrace 3 2 initPipeMain orderMain demandMain 5
        + pipelineTotal 2 initPipeMain orderMain 5
      = 3 + Finset.sum (Finset.univ : Finset (Fin 2)) (fun j : Fin 2 => (initPipeMain j : ℝ))
        + Finset.sum (Finset.range 5) (fun t : ℕ => (orderMain t : ℝ))
        - Finset.sum (Finset.range 5) (fun t : ℕ => (demandMain t : ℝ)) :=
  conservation 3 2 initPipeMain orderMain demandMain 5

/-- C7 main fixture: `stockTrace_balance` applied at the fixture. -/
theorem testMainBalance :
    stockTrace 3 2 initPipeMain orderMain demandMain 5
      = 3 + Finset.sum (Finset.range 5) (fun t : ℕ => (receipt 2 initPipeMain orderMain t : ℝ))
        - Finset.sum (Finset.range 5) (fun t : ℕ => (demandMain t : ℝ)) :=
  stockTrace_balance 3 2 initPipeMain orderMain demandMain 5

/-- C7 main fixture: `pipelineTotal_closedForm` applied at the fixture. -/
theorem testMainClosedForm :
    pipelineTotal 2 initPipeMain orderMain 5
      = Finset.sum (Finset.filter (fun j : Fin 2 => 5 ≤ j.val) (Finset.univ : Finset (Fin 2)))
          (fun j : Fin 2 => (initPipeMain j : ℝ))
        + Finset.sum (Finset.filter (fun t : ℕ => 5 - 2 ≤ t) (Finset.range 5))
          (fun t : ℕ => (orderMain t : ℝ)) :=
  pipelineTotal_closedForm 2 initPipeMain orderMain 5

/-- C6 on the main fixture: `run` agrees with the stock trace. -/
theorem testRunFstMain :
    (run 3 2 initPipeMain orderMain demandMain 5).1 = -2 := by
  rw [run_fst_eq_stockTrace, testMainStock]

/-- C6 on the main fixture: `run` agrees with the pipeline. -/
theorem testRunSndMain :
    (run 3 2 initPipeMain orderMain demandMain 5).2
      = pipeline 2 initPipeMain orderMain 5 :=
  run_snd_eq_pipeline 3 2 initPipeMain orderMain demandMain 5

/-- Empty initial pipeline at `L = 0`. -/
def initPipeZero : Fin 0 → NNReal := fun j => Fin.elim0 j

/-- Zero-lead-time orders: `(2, 1, 4)`. -/
def orderZero : ℕ → NNReal
  | 0 => 2
  | 1 => 1
  | 2 => 4
  | _ => 0

/-- Zero-lead-time demands: `(1, 1, 1)`. -/
def demandZero : ℕ → NNReal
  | 0 => 1
  | 1 => 1
  | 2 => 1
  | _ => 0

theorem orderZero_0 : orderZero 0 = 2 := rfl
theorem orderZero_1 : orderZero 1 = 1 := rfl
theorem orderZero_2 : orderZero 2 = 4 := rfl
theorem demandZero_0 : demandZero 0 = 1 := rfl
theorem demandZero_1 : demandZero 1 = 1 := rfl
theorem demandZero_2 : demandZero 2 = 1 := rfl

/-- C7 immediate `L = 0` delivery: receipts equal current orders. -/
theorem receiptZero_0 : receipt 0 initPipeZero orderZero 0 = 2 := by
  rw [receipt_zero_lead]
  rfl

theorem receiptZero_1 : receipt 0 initPipeZero orderZero 1 = 1 := by
  rw [receipt_zero_lead]
  rfl

theorem receiptZero_2 : receipt 0 initPipeZero orderZero 2 = 4 := by
  rw [receipt_zero_lead]
  rfl

/-- C7 `L = 0` fixture: final net stock is `4`. -/
theorem testZeroStock : stockTrace 0 0 initPipeZero orderZero demandZero 3 = 4 := by
  simp only [stockTrace_succ, stockTrace_zero, receiptZero_0, receiptZero_1, receiptZero_2,
    demandZero_0, demandZero_1, demandZero_2]
  norm_num

/-- C7 `L = 0` fixture: terminal pipeline is empty. -/
theorem testZeroPipeline : pipelineTotal 0 initPipeZero orderZero 3 = 0 :=
  pipelineTotal_zero initPipeZero orderZero 3

/-- C7 `L = 0` fixture: the conservation total is `4`. -/
theorem testZeroTotal :
    stockTrace 0 0 initPipeZero orderZero demandZero 3
      + pipelineTotal 0 initPipeZero orderZero 3 = 4 := by
  rw [testZeroStock, testZeroPipeline]
  norm_num

/-- C7 `L = 0` fixture: `conservation` applied at the fixture. -/
theorem testZeroConservation :
    stockTrace 0 0 initPipeZero orderZero demandZero 3
        + pipelineTotal 0 initPipeZero orderZero 3
      = 0 + Finset.sum (Finset.univ : Finset (Fin 0)) (fun j : Fin 0 => (initPipeZero j : ℝ))
        + Finset.sum (Finset.range 3) (fun t : ℕ => (orderZero t : ℝ))
        - Finset.sum (Finset.range 3) (fun t : ℕ => (demandZero t : ℝ)) :=
  conservation 0 0 initPipeZero orderZero demandZero 3

/-- C7 `H = 0`: the trace starts at `I0`. -/
theorem testHZeroStock : stockTrace 3 2 initPipeMain orderMain demandMain 0 = 3 :=
  stockTrace_zero 3 2 initPipeMain orderMain demandMain

/-- C7 `H = 0`: the terminal pipeline is the full initial pipeline (`4`). -/
theorem testHZeroPipeline : pipelineTotal 2 initPipeMain orderMain 0 = 4 := by
  rw [pipelineTotal_closedForm]
  simp [Fin.sum_univ_two, initPipeMain]

/-- C7 `H = 0`: `conservation` applied at the fixture. -/
theorem testHZeroConservation :
    stockTrace 3 2 initPipeMain orderMain demandMain 0
        + pipelineTotal 2 initPipeMain orderMain 0
      = 3 + Finset.sum (Finset.univ : Finset (Fin 2)) (fun j : Fin 2 => (initPipeMain j : ℝ))
        + Finset.sum (Finset.range 0) (fun t : ℕ => (orderMain t : ℝ))
        - Finset.sum (Finset.range 0) (fun t : ℕ => (demandMain t : ℝ)) :=
  conservation 3 2 initPipeMain orderMain demandMain 0

/-- `H < L` fixture: initial pipeline `(5, 6, 7)` at `L = 3`. -/
def initPipeU : Fin 3 → NNReal := fun j => match j.val with
  | 0 => 5
  | 1 => 6
  | _ => 7

/-- `H < L` fixture: a single order of `10` at `t = 0`. -/
def orderU : ℕ → NNReal
  | 0 => 10
  | _ => 0

/-- `H < L` fixture: demand `4` at `t = 0`. -/
def demandU : ℕ → NNReal
  | 0 => 4
  | _ => 0

theorem initPipeU_0 : initPipeU ⟨0, by omega⟩ = 5 := rfl
theorem initPipeU_1 : initPipeU ⟨1, by omega⟩ = 6 := rfl
theorem initPipeU_2 : initPipeU ⟨2, by omega⟩ = 7 := rfl
theorem orderU_0 : orderU 0 = 10 := rfl
theorem demandU_0 : demandU 0 = 4 := rfl

theorem receiptU_0 : receipt 3 initPipeU orderU 0 = 5 := by
  have h : (0 : ℕ) < 3 := by omega
  rw [receipt_of_lt 3 initPipeU orderU 0 h]
  rfl

theorem receiptU_1 : receipt 3 initPipeU orderU 1 = 6 := by
  have h : (1 : ℕ) < 3 := by omega
  rw [receipt_of_lt 3 initPipeU orderU 1 h]
  rfl

theorem receiptU_2 : receipt 3 initPipeU orderU 2 = 7 := by
  have h : (2 : ℕ) < 3 := by omega
  rw [receipt_of_lt 3 initPipeU orderU 2 h]
  rfl

theorem receiptU_3 : receipt 3 initPipeU orderU 3 = 10 := by
  have h : ¬ (3 : ℕ) < 3 := by omega
  rw [receipt_of_not_lt 3 initPipeU orderU 3 h]
  rfl

/-- C7 `H < L` with unreceived initial stock: net stock at `H = 1` is `1`. -/
theorem testUStock : stockTrace 0 3 initPipeU orderU demandU 1 = 1 := by
  simp only [stockTrace_succ, stockTrace_zero, receiptU_0, demandU_0]
  norm_num

/-- C7 `H < L`: outstanding pipeline at `H = 1` is `23` (`6 + 7 + 10`). -/
theorem testUPipeline : pipelineTotal 3 initPipeU orderU 1 = 23 := by
  simp [pipelineTotal, Fin.sum_univ_three, pipeline_apply,
    receiptU_1, receiptU_2, receiptU_3]
  norm_num

/-- C7 `H < L`: the conservation total is `24`. -/
theorem testUTotal :
    stockTrace 0 3 initPipeU orderU demandU 1 + pipelineTotal 3 initPipeU orderU 1 = 24 := by
  rw [testUStock, testUPipeline]
  norm_num

/-- C7 `H = L`: net stock at `H = 2` is `-1` (main fixtures). -/
theorem testHEqLStock : stockTrace 3 2 initPipeMain orderMain demandMain 2 = -1 := by
  simp only [stockTrace_succ, stockTrace_zero, receiptMain_0, receiptMain_1,
    demandMain_0, demandMain_1]
  norm_num

/-- C7 `H = L`: outstanding pipeline at `H = 2` is `3` (orders only). -/
theorem testHEqLPipeline : pipelineTotal 2 initPipeMain orderMain 2 = 3 := by
  simp [pipelineTotal, Fin.sum_univ_two, pipeline_apply, receiptMain_2, receiptMain_3]
  norm_num

/-- C7 `H = L`: the conservation total is `2`. -/
theorem testHEqLTotal :
    stockTrace 3 2 initPipeMain orderMain demandMain 2
      + pipelineTotal 2 initPipeMain orderMain 2 = 2 := by
  rw [testHEqLStock, testHEqLPipeline]
  norm_num

/-- C7 stockout: on-hand at net `-2` is `0`. -/
theorem testOnHandNeg : onHand (-2) = 0 := by
  unfold onHand
  rw [max_eq_right (by norm_num : (-2 : ℝ) ≤ 0)]

/-- C7 stockout: backlog at net `-2` is `2`. -/
theorem testBacklogNeg : backlog (-2) = 2 := by
  unfold backlog
  have h : (0 : ℝ) ≤ -(-2) := by norm_num
  rw [max_eq_left h]
  norm_num

/-- C7 stockout: on-hand minus backlog recovers `-2` (theorem application). -/
theorem testOnHandSubNeg : onHand (-2) - backlog (-2) = -2 :=
  onHand_sub_backlog (-2)

/-- C7 stockout: on-hand and backlog are never both positive (theorem application). -/
theorem testOnHandMulNeg : onHand (-2) * backlog (-2) = 0 :=
  onHand_mul_backlog (-2)

/-- C7 stockout: nonnegativity pins (theorem applications). -/
theorem testOnHandNonnegNeg : 0 ≤ onHand (-2) :=
  onHand_nonneg (-2)

theorem testBacklogNonnegNeg : 0 ≤ backlog (-2) :=
  backlog_nonneg (-2)

/-- Fractional fixture: initial pipeline `(1 / 2)` at `L = 1`. -/
noncomputable def initPipeF : Fin 1 → NNReal := fun _ => ⟨1 / 2, by norm_num⟩

/-- Fractional fixture orders: `(3 / 2, 1 / 4)`. -/
noncomputable def orderF : ℕ → NNReal
  | 0 => ⟨3 / 2, by norm_num⟩
  | 1 => ⟨1 / 4, by norm_num⟩
  | _ => 0

/-- Fractional fixture demands: `(1 / 4, 1 / 2)`. -/
noncomputable def demandF : ℕ → NNReal
  | 0 => ⟨1 / 4, by norm_num⟩
  | 1 => ⟨1 / 2, by norm_num⟩
  | _ => 0

theorem orderF_0 : orderF 0 = ⟨3 / 2, by norm_num⟩ := rfl
theorem orderF_1 : orderF 1 = ⟨1 / 4, by norm_num⟩ := rfl
theorem demandF_0 : demandF 0 = ⟨1 / 4, by norm_num⟩ := rfl
theorem demandF_1 : demandF 1 = ⟨1 / 2, by norm_num⟩ := rfl

theorem receiptF_0 : receipt 1 initPipeF orderF 0 = ⟨1 / 2, by norm_num⟩ := by
  have h : (0 : ℕ) < 1 := by omega
  rw [receipt_of_lt 1 initPipeF orderF 0 h]
  rfl

theorem receiptF_1 : receipt 1 initPipeF orderF 1 = ⟨3 / 2, by norm_num⟩ := by
  have h : ¬ (1 : ℕ) < 1 := by omega
  rw [receipt_of_not_lt 1 initPipeF orderF 1 h]
  rfl

theorem receiptF_2 : receipt 1 initPipeF orderF 2 = ⟨1 / 4, by norm_num⟩ := by
  have h : ¬ (2 : ℕ) < 1 := by omega
  rw [receipt_of_not_lt 1 initPipeF orderF 2 h]
  rfl

/-- C7 fractional quantities: final net stock is `5 / 4`. -/
theorem testFStock : stockTrace 0 1 initPipeF orderF demandF 2 = 5 / 4 := by
  simp only [stockTrace_succ, stockTrace_zero, receiptF_0, receiptF_1, demandF_0, demandF_1]
  show (0 : ℝ) + 1 / 2 - 1 / 4 + 3 / 2 - 1 / 2 = 5 / 4
  norm_num

/-- C7 fractional quantities: outstanding pipeline is `1 / 4`. -/
theorem testFPipeline : pipelineTotal 1 initPipeF orderF 2 = 1 / 4 := by
  simp [pipelineTotal, pipeline_apply, receiptF_2]
  rfl

/-- C7 fractional quantities: the conservation total is `3 / 2`. -/
theorem testFTotal :
    stockTrace 0 1 initPipeF orderF demandF 2 + pipelineTotal 1 initPipeF orderF 2 = 3 / 2 := by
  rw [testFStock, testFPipeline]
  norm_num

/-- C7 counterexample: dropping the terminal pipeline breaks the balance
(`-2 ≠ 4` on the main fixture; the valid control `testMainTotal` holds). -/
theorem testDropTerminalFails :
    stockTrace 3 2 initPipeMain orderMain demandMain 5
      ≠ 3 + Finset.sum (Finset.univ : Finset (Fin 2)) (fun j : Fin 2 => (initPipeMain j : ℝ))
        + Finset.sum (Finset.range 5) (fun t : ℕ => (orderMain t : ℝ))
        - Finset.sum (Finset.range 5) (fun t : ℕ => (demandMain t : ℝ)) := by
  rw [testMainStock, testMainRHS]
  norm_num

/-- Counterfactual delayed receipt at zero lead time: `0` at `t = 0`,
otherwise the previous order. -/
def receiptDelayedZero (order : ℕ → NNReal) (t : ℕ) : NNReal :=
  match t with
  | 0 => 0
  | t + 1 => order t

/-- Counterfactual delayed net-stock trace at zero lead time. -/
def stockTraceDelayedZero (I0 : ℝ) (order demand : ℕ → NNReal) : ℕ → ℝ
  | 0 => I0
  | t + 1 => stockTraceDelayedZero I0 order demand t
      + (receiptDelayedZero order t : ℝ) - (demand t : ℝ)

theorem receiptDelayedZero_0 : receiptDelayedZero orderZero 0 = 0 := rfl
theorem receiptDelayedZero_1 : receiptDelayedZero orderZero 1 = 2 := rfl
theorem receiptDelayedZero_2 : receiptDelayedZero orderZero 2 = 1 := rfl

/-- Delayed zero-lead trace reaches `0`, not the balanced `4`. -/
theorem testDelayedZeroStock : stockTraceDelayedZero 0 orderZero demandZero 3 = 0 := by
  simp only [stockTraceDelayedZero, receiptDelayedZero_0, receiptDelayedZero_1,
    receiptDelayedZero_2, demandZero_0, demandZero_1, demandZero_2]
  norm_num

/-- C7 counterexample: delaying a zero-lead-time receipt breaks the balance
(`0 ≠ 4` on the zero fixture; the valid control `testZeroTotal` holds). -/
theorem testDelayedZeroFails :
    stockTraceDelayedZero 0 orderZero demandZero 3
      ≠ 0 + Finset.sum (Finset.univ : Finset (Fin 0)) (fun j : Fin 0 => (initPipeZero j : ℝ))
        + Finset.sum (Finset.range 3) (fun t : ℕ => (orderZero t : ℝ))
        - Finset.sum (Finset.range 3) (fun t : ℕ => (demandZero t : ℝ)) := by
  rw [testDelayedZeroStock]
  have hInit : Finset.sum (Finset.univ : Finset (Fin 0))
      (fun j : Fin 0 => (initPipeZero j : ℝ)) = 0 := by simp
  have hOrder : Finset.sum (Finset.range 3) (fun t : ℕ => (orderZero t : ℝ)) = 7 := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero,
      orderZero_0, orderZero_1, orderZero_2]
    norm_num
  have hDemand : Finset.sum (Finset.range 3) (fun t : ℕ => (demandZero t : ℝ)) = 3 := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero,
      demandZero_0, demandZero_1, demandZero_2]
    norm_num
  rw [hInit, hOrder, hDemand]
  norm_num

end Inventory

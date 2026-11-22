/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.Circuits.DCDispatchCertificate
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.NormNum

/-!
Two-bus fixture: one branch from bus `0` to bus `1` with susceptance
`b = 10`, one generator at bus `0` with limits `0 ≤ pg ≤ 2` and cost `3`,
demand `d = (0, 1)`, reference bus `0`, flow limits `-5 ≤ f ≤ 5`. The
balance forces `pg = 1`, so the optimal cost is `3`. The primal witness
is `pg = 1`, `θ = (0, -1/10)`. The checker is evaluated by the kernel
(`decide +kernel`); the real-side conclusions come from the library
theorems applied to those verdicts.

- Zero gap: prices `lam = (3, 3)`, all other multipliers `0`, accepted at
  `ε = 0`, which certifies global optimality.
- Gap one: prices `lam = (2, 2)`, `μlo = 1`, lower bound `2`, rejected at
  `ε = 0` and accepted at `ε = 1`.
- Invalid dual: prices `lam = (4, 4)`, `μlo = -1`. Both stationarity
  equations hold but the multiplier is negative, so it is rejected at every
  budget; its claimed bound `4` exceeds the optimum `3`.
-/

@[expose] public section

namespace PhyslibExtTest.Circuits.DCDispatchCertificate

open Matrix
open PhyslibExt.Circuits.DCDispatchEncoding
open PhyslibExt.Circuits.DCDispatchCertificate

/-- The branch leaves bus `0`. -/
def tl : Fin 1 → Fin 2 := fun _ => 0

/-- The branch enters bus `1`. -/
def hd : Fin 1 → Fin 2 := fun _ => 1

/-- Branch susceptance `10`. -/
def bq : Fin 1 → ℚ := fun _ => 10

/-- The generator sits at bus `0`. -/
def gb : Fin 1 → Fin 2 := fun _ => 0

/-- Demand `1` at bus `1`. -/
def dq : Fin 2 → ℚ := ![0, 1]

/-- Lower generator limit `0`. -/
def pminq : Fin 1 → ℚ := fun _ => 0

/-- Upper generator limit `2`. -/
def pmaxq : Fin 1 → ℚ := fun _ => 2

/-- Lower flow limit `-5`. -/
def fminq : Fin 1 → ℚ := fun _ => -5

/-- Upper flow limit `5`. -/
def fmaxq : Fin 1 → ℚ := fun _ => 5

/-- Generation cost `3`. -/
def costq : Fin 1 → ℚ := fun _ => 3

/-- Primal generation `1`. -/
def pgq : Fin 1 → ℚ := fun _ => 1

/-- Primal angles with bus `0` as the reference. -/
def θq : Fin 2 → ℚ := ![0, -1 / 10]

lemma witness_cost : dispatchCost 1 (castVec costq) (castVec pgq) = 3 := by
  simp [dispatchCost, dotProduct, castVec, costq, pgq]

/-! ### Zero gap -/

/-- Nodal prices `3` at both buses. -/
def lam1 : Fin 2 → ℚ := ![3, 3]

lemma zero_accepts : checksDispatchCertificate 2 1 1 tl hd bq gb dq 0 pminq pmaxq fminq fmaxq
    costq pgq θq lam1 0 0 0 0 0 0 = true := by
  decide +kernel

lemma zero_bound : dualLowerBound 2 1 1 dq pminq pmaxq fminq fmaxq lam1 0 0 0 0 = 3 := by
  decide +kernel

lemma zero_dualFeasible : IsDualFeasible 2 1 1 tl hd bq gb 0 costq lam1 0 0 0 0 0 :=
  ((checksDispatchCertificate_eq_true_iff 2 1 1 tl hd bq gb dq 0 pminq pmaxq fminq fmaxq
    costq pgq θq lam1 0 0 0 0 0 0).1 zero_accepts).2.1

lemma witness_feasible :
    IsDispatchFeasible 2 1 1 tl hd (castVec bq) gb (castVec dq) 0 (castVec pminq)
      (castVec pmaxq) (castVec fminq) (castVec fmaxq) (castVec pgq) (castVec θq) :=
  (dispatch_optimal_of_checks_zero 2 1 1 tl hd bq gb dq 0 pminq pmaxq fminq fmaxq
    costq pgq θq lam1 0 0 0 0 0 zero_accepts).1

/-- The zero-gap certificate proves that every feasible dispatch costs at
least `3`, the cost of the witness. -/
lemma zero_optimal (pg : Fin 1 → ℝ) (θ : Fin 2 → ℝ)
    (h : IsDispatchFeasible 2 1 1 tl hd (castVec bq) gb (castVec dq) 0 (castVec pminq)
      (castVec pmaxq) (castVec fminq) (castVec fmaxq) pg θ) :
    3 ≤ dispatchCost 1 (castVec costq) pg := by
  rw [← witness_cost]
  exact (dispatch_optimal_of_checks_zero 2 1 1 tl hd bq gb dq 0 pminq pmaxq fminq fmaxq
    costq pgq θq lam1 0 0 0 0 0 zero_accepts).2.1 pg θ h

lemma zero_cost_eq_bound :
    costq ⬝ᵥ pgq = dualLowerBound 2 1 1 dq pminq pmaxq fminq fmaxq lam1 0 0 0 0 :=
  (dispatch_optimal_of_checks_zero 2 1 1 tl hd bq gb dq 0 pminq pmaxq fminq fmaxq
    costq pgq θq lam1 0 0 0 0 0 zero_accepts).2.2

/-! ### Gap one -/

/-- Nodal prices `2` at both buses. -/
def lam2 : Fin 2 → ℚ := ![2, 2]

/-- Lower-limit multiplier `1`. -/
def one1 : Fin 1 → ℚ := fun _ => 1

lemma gap_bound : dualLowerBound 2 1 1 dq pminq pmaxq fminq fmaxq lam2 0 one1 0 0 = 2 := by
  decide +kernel

lemma gap_rejects_at_zero : checksDispatchCertificate 2 1 1 tl hd bq gb dq 0 pminq pmaxq fminq
    fmaxq costq pgq θq lam2 0 0 one1 0 0 0 = false := by
  decide +kernel

/-- The rejection at `ε = 0` is the gap clause: the gap is `1`. -/
lemma gap_rejects_at_zero_of_gap : checksDispatchCertificate 2 1 1 tl hd bq gb dq 0 pminq pmaxq
    fminq fmaxq costq pgq θq lam2 0 0 one1 0 0 0 = false :=
  checks_eq_false_of_lt_gap 2 1 1 tl hd bq gb dq 0 pminq pmaxq fminq fmaxq costq pgq θq
    lam2 0 0 one1 0 0 0 (by rw [gap_bound]; decide +kernel)

lemma gap_accepts_at_one : checksDispatchCertificate 2 1 1 tl hd bq gb dq 0 pminq pmaxq fminq
    fmaxq costq pgq θq lam2 0 0 one1 0 0 1 = true := by
  decide +kernel

lemma gap_dualFeasible : IsDualFeasible 2 1 1 tl hd bq gb 0 costq lam2 0 0 one1 0 0 :=
  ((checksDispatchCertificate_eq_true_iff 2 1 1 tl hd bq gb dq 0 pminq pmaxq fminq fmaxq
    costq pgq θq lam2 0 0 one1 0 0 1).1 gap_accepts_at_one).2.1

/-- At `ε = 1` the certificate gives the lower bound `2` on every feasible
cost and puts the witness within `1` of every feasible cost. -/
lemma gap_headline (pg : Fin 1 → ℝ) (θ : Fin 2 → ℝ)
    (h : IsDispatchFeasible 2 1 1 tl hd (castVec bq) gb (castVec dq) 0 (castVec pminq)
      (castVec pmaxq) (castVec fminq) (castVec fmaxq) pg θ) :
    2 ≤ dispatchCost 1 (castVec costq) pg ∧ 3 ≤ dispatchCost 1 (castVec costq) pg + 1 := by
  obtain ⟨-, hlb, -, -, hopt⟩ := dispatch_certificate_correct 2 1 1 tl hd bq gb dq 0 pminq
    pmaxq fminq fmaxq costq pgq θq lam2 0 0 one1 0 0 1 gap_accepts_at_one
  have h1 := hlb pg θ h
  have h2 := hopt pg θ h
  rw [gap_bound] at h1
  rw [witness_cost] at h2
  exact ⟨by exact_mod_cast h1, by exact_mod_cast h2⟩

/-! ### Invalid dual witness -/

/-- Nodal prices `4` at both buses. -/
def lam3 : Fin 2 → ℚ := ![4, 4]

/-- Negative lower-limit multiplier `-1`. -/
def neg1 : Fin 1 → ℚ := fun _ => -1

lemma invalid_not_dualFeasible : ¬ IsDualFeasible 2 1 1 tl hd bq gb 0 costq lam3 0 0 neg1 0 0 := by
  unfold IsDualFeasible
  decide +kernel

/-- Only the sign test fails: both stationarity equations hold. -/
lemma invalid_stationarity :
    (∀ g, lam3 (gb g) = costq g + (0 : Fin 1 → ℚ) g - neg1 g) ∧
      ∀ v, (Matrix.transpose (ratLaplacian 2 1 tl hd bq) *ᵥ lam3) v +
          (if v = 0 then (0 : ℚ) else 0) +
          (Matrix.transpose (ratBranchFlowMatrix 2 1 tl hd bq) *ᵥ
            ((0 : Fin 1 → ℚ) - 0)) v = 0 := by
  decide +kernel

lemma invalid_rejects_1 : checksDispatchCertificate 2 1 1 tl hd bq gb dq 0 pminq pmaxq fminq
    fmaxq costq pgq θq lam3 0 0 neg1 0 0 1 = false := by
  decide +kernel

lemma invalid_rejects_100 : checksDispatchCertificate 2 1 1 tl hd bq gb dq 0 pminq pmaxq fminq
    fmaxq costq pgq θq lam3 0 0 neg1 0 0 100 = false := by
  decide +kernel

/-- The invalid witness is rejected at every budget. -/
lemma invalid_rejects (ε : ℚ) : checksDispatchCertificate 2 1 1 tl hd bq gb dq 0 pminq pmaxq
    fminq fmaxq costq pgq θq lam3 0 0 neg1 0 0 ε = false :=
  checks_eq_false_of_not_dualFeasible 2 1 1 tl hd bq gb dq 0 pminq pmaxq fminq fmaxq costq pgq
    θq lam3 0 0 neg1 0 0 ε invalid_not_dualFeasible

lemma invalid_bound : dualLowerBound 2 1 1 dq pminq pmaxq fminq fmaxq lam3 0 neg1 0 0 = 4 := by
  decide +kernel

/-- The claimed bound `4` of the invalid witness is not a lower bound: the
feasible witness dispatch costs `3`. -/
lemma invalid_bound_unsound :
    ¬ ∀ pg θ, IsDispatchFeasible 2 1 1 tl hd (castVec bq) gb (castVec dq) 0
        (castVec pminq) (castVec pmaxq) (castVec fminq) (castVec fmaxq) pg θ →
      ((dualLowerBound 2 1 1 dq pminq pmaxq fminq fmaxq lam3 0 neg1 0 0 : ℚ) : ℝ) ≤
        dispatchCost 1 (castVec costq) pg := by
  intro h
  have := h _ _ witness_feasible
  rw [invalid_bound, witness_cost] at this
  norm_num at this

end PhyslibExtTest.Circuits.DCDispatchCertificate

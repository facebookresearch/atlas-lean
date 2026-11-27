/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

import MathlibExt.ControlTheory.LQR.FiniteHorizon

/-!
# The linear quadratic regulator by dynamic programming

For the linear dynamics `x_{t+1} = A x_t + B u_t` and the quadratic stage cost
`x_tᵀ Q x_t + u_tᵀ R u_t`, dynamic programming gives quadratic cost-to-go functions `xᵀ M_t x` and
linear optimal controls `u_t = -K_t x_t`, computed backwards by the Riccati recursion
`M_t = Q + Aᵀ M_{t+1} A - Aᵀ M_{t+1} B (R + Bᵀ M_{t+1} B)⁻¹ Bᵀ M_{t+1} A` with the gain
`K_t = (R + Bᵀ M_{t+1} B)⁻¹ Bᵀ M_{t+1} A` (B. Recht, *A tour of reinforcement learning: the view
from continuous control*, Annual Review of Control, Robotics, and Autonomous Systems 2 (2019),
arXiv:1806.09460, Section 4; the stationary limit is the discrete algebraic Riccati equation
(4.2)). The key step is a completion of squares in the control.

## Main definitions

- `riccatiGain A B R M`, `riccatiMap A B Q R M`: the gain and the Riccati update.
- `bellmanCost A B Q R M x u`: stage cost plus quadratic cost-to-go after one step.
- `lqrCost A B Q R Qf x₀ u T`: the cost of the control sequence `u` over `T` steps.

## Main results

- `bellmanCost_eq_add`: completion of squares,
  `bellmanCost x u = bellmanCost x (-K x) + (u + K x)ᵀ (R + Bᵀ M B) (u + K x)`.
- `bellmanCost_neg_gain`: `bellmanCost x (-K x) = xᵀ riccatiMap x`.
- `bellmanCost_ge`: the linear control `-K x` minimizes `bellmanCost x ·`.
- `lqrCost_ge` and `lqrCost_feedback`: over a finite horizon, every control sequence costs at
  least `x₀ᵀ M₀ x₀`, and the linear feedback `u_t = -K_t x_t` attains it.

## Relation to `MathlibExt.ControlTheory.LQR.FiniteHorizon`

That module treats one stage only: `ControlTheory.riccatiStep A B P Q R` equals
`riccatiMap A B Q R P`, `ControlTheory.complete_square` (for `P, Q ⪰ 0`, `R ≻ 0`) is
`bellmanCost_eq_add` with `bellmanCost_neg_gain` (which need only symmetry and invertibility),
and `ControlTheory.riccatiStep_posSemidef` is `riccatiMap_posSemidef`.
-/

@[expose] public section

open Matrix

namespace CSLibExt.MachineLearning.LinearQuadraticRegulator

variable {σ ι : Type*} [Fintype σ] [Fintype ι] [DecidableEq ι]

/-- **Riccati gain.** `K = (R + Bᵀ M B)⁻¹ Bᵀ M A`, the gain of the optimal linear control
`u = -K x` for the cost-to-go matrix `M`.

Source: B. Recht, *A tour of reinforcement learning: the view from continuous control*,
arXiv:1806.09460, Section 4 (`K = (R + BᵀMB)⁻¹BᵀMA`). -/
noncomputable def riccatiGain (A : Matrix σ σ ℝ) (B : Matrix σ ι ℝ) (R : Matrix ι ι ℝ)
    (M : Matrix σ σ ℝ) : Matrix ι σ ℝ :=
  (R + Bᵀ * M * B)⁻¹ * (Bᵀ * M * A)

/-- **Riccati update.** `Q + Aᵀ M A - (Aᵀ M B) (R + Bᵀ M B)⁻¹ (Bᵀ M A)`, the matrix of the optimal
cost-to-go one step earlier; its fixed points are the solutions of the discrete algebraic Riccati
equation.

Source: B. Recht, *A tour of reinforcement learning: the view from continuous control*,
arXiv:1806.09460, Section 4, equation (4.2). -/
noncomputable def riccatiMap (A : Matrix σ σ ℝ) (B : Matrix σ ι ℝ) (Q : Matrix σ σ ℝ)
    (R : Matrix ι ι ℝ) (M : Matrix σ σ ℝ) : Matrix σ σ ℝ :=
  Q + Aᵀ * M * A - (Aᵀ * M * B) * (R + Bᵀ * M * B)⁻¹ * (Bᵀ * M * A)

/-- **One-step Bellman cost.** `xᵀ Q x + uᵀ R u + (A x + B u)ᵀ M (A x + B u)`: the stage cost of
the control `u` at the state `x` plus the quadratic cost-to-go `M` at the next state.

Source: B. Recht, *A tour of reinforcement learning: the view from continuous control*,
arXiv:1806.09460, Section 4 (the Q-function recursion
`Q_k(x, u) = xᵀQx + uᵀRu + (Ax + Bu)ᵀ M_{k+1} (Ax + Bu) + c_k`, here without noise). -/
def bellmanCost (A : Matrix σ σ ℝ) (B : Matrix σ ι ℝ) (Q : Matrix σ σ ℝ) (R : Matrix ι ι ℝ)
    (M : Matrix σ σ ℝ) (x : σ → ℝ) (u : ι → ℝ) : ℝ :=
  x ⬝ᵥ (Q *ᵥ x) + u ⬝ᵥ (R *ᵥ u) + (A *ᵥ x + B *ᵥ u) ⬝ᵥ (M *ᵥ (A *ᵥ x + B *ᵥ u))

omit [DecidableEq ι] in
private theorem dotProduct_mulVec_symm {κ : Type*} [Fintype κ] {P : Matrix κ κ ℝ} (hP : Pᵀ = P)
    (v w : κ → ℝ) : v ⬝ᵥ (P *ᵥ w) = w ⬝ᵥ (P *ᵥ v) := by
  rw [dotProduct_mulVec, ← mulVec_transpose, hP, dotProduct_comm]

omit [DecidableEq ι] in
private theorem dotProduct_transpose_mulVec {κ τ : Type*} [Fintype κ] [Fintype τ]
    (C : Matrix κ τ ℝ) (v : τ → ℝ) (w : κ → ℝ) : v ⬝ᵥ (Cᵀ *ᵥ w) = (C *ᵥ v) ⬝ᵥ w := by
  rw [mulVec_transpose, dotProduct_comm, ← dotProduct_mulVec, dotProduct_comm]

/-- **Completion of squares in the control.** If `M` and `R` are symmetric and `S = R + Bᵀ M B`
is invertible, then with `K = riccatiGain A B R M`, for every state `x` and control `u`,
`bellmanCost x u = bellmanCost x (-K x) + (u + K x)ᵀ S (u + K x)`.

Source: B. Recht, *A tour of reinforcement learning: the view from continuous control*,
arXiv:1806.09460, Section 4 (the dynamic programming derivation of the linear optimal control;
the completion of squares is the computation behind it). -/
theorem bellmanCost_eq_add {A : Matrix σ σ ℝ} {B : Matrix σ ι ℝ} {Q : Matrix σ σ ℝ}
    {R : Matrix ι ι ℝ} {M : Matrix σ σ ℝ} (hM : Mᵀ = M) (hR : Rᵀ = R)
    (hS : IsUnit (R + Bᵀ * M * B).det) (x : σ → ℝ) (u : ι → ℝ) :
    bellmanCost A B Q R M x u =
      bellmanCost A B Q R M x (-(riccatiGain A B R M *ᵥ x)) +
        (u + riccatiGain A B R M *ᵥ x) ⬝ᵥ
          ((R + Bᵀ * M * B) *ᵥ (u + riccatiGain A B R M *ᵥ x)) := by
  set S := R + Bᵀ * M * B with hSdef
  have hST : Sᵀ = S := by
    rw [hSdef, transpose_add, hR, transpose_mul, transpose_mul, transpose_transpose, hM,
      Matrix.mul_assoc]
  set g : ι → ℝ := (Bᵀ * M * A) *ᵥ x with hg
  set k : ι → ℝ := riccatiGain A B R M *ᵥ x with hk
  have hSk : S *ᵥ k = g := by
    rw [hk, riccatiGain, mulVec_mulVec, ← Matrix.mul_assoc, mul_nonsing_inv _ hS, Matrix.one_mul]
  -- expansion of the cost in the control
  have hexp : ∀ v : ι → ℝ, bellmanCost A B Q R M x v =
      x ⬝ᵥ (Q *ᵥ x) + (A *ᵥ x) ⬝ᵥ (M *ᵥ (A *ᵥ x)) + v ⬝ᵥ (S *ᵥ v) + 2 * (v ⬝ᵥ g) := by
    intro v
    have h1 : (B *ᵥ v) ⬝ᵥ (M *ᵥ (B *ᵥ v)) = v ⬝ᵥ ((Bᵀ * M * B) *ᵥ v) := by
      rw [← mulVec_mulVec, ← mulVec_mulVec, dotProduct_transpose_mulVec]
    have h2 : (B *ᵥ v) ⬝ᵥ (M *ᵥ (A *ᵥ x)) = v ⬝ᵥ g := by
      rw [hg, ← mulVec_mulVec, ← mulVec_mulVec, dotProduct_transpose_mulVec]
    have h3 : (A *ᵥ x) ⬝ᵥ (M *ᵥ (B *ᵥ v)) = (B *ᵥ v) ⬝ᵥ (M *ᵥ (A *ᵥ x)) :=
      dotProduct_mulVec_symm hM _ _
    simp only [bellmanCost, mulVec_add, dotProduct_add, add_dotProduct, hSdef, add_mulVec]
    rw [h3, h2, h1]
    ring
  have hsq : (u + k) ⬝ᵥ (S *ᵥ (u + k)) = u ⬝ᵥ (S *ᵥ u) + 2 * (u ⬝ᵥ g) + k ⬝ᵥ g := by
    have hku : k ⬝ᵥ (S *ᵥ u) = u ⬝ᵥ g := by rw [dotProduct_mulVec_symm hST, hSk]
    simp only [mulVec_add, dotProduct_add, add_dotProduct]
    rw [hSk, hku]
    ring
  have hneg : (-k) ⬝ᵥ (S *ᵥ (-k)) = k ⬝ᵥ g := by
    rw [mulVec_neg, neg_dotProduct, dotProduct_neg, neg_neg, hSk]
  rw [hexp u, hexp (-k), hsq, hneg, neg_dotProduct]
  ring

/-- **The Bellman cost of the linear control.** Under the hypotheses of `bellmanCost_eq_add`,
`bellmanCost x (-K x) = xᵀ (riccatiMap A B Q R M) x`: the optimal one-step cost is the quadratic
form of the Riccati update.

Source: B. Recht, *A tour of reinforcement learning: the view from continuous control*,
arXiv:1806.09460, Section 4 (the recursion for `M_k` whose limit is (4.2)). -/
theorem bellmanCost_neg_gain {A : Matrix σ σ ℝ} {B : Matrix σ ι ℝ} {Q : Matrix σ σ ℝ}
    {R : Matrix ι ι ℝ} {M : Matrix σ σ ℝ} (hM : Mᵀ = M) (hR : Rᵀ = R)
    (hS : IsUnit (R + Bᵀ * M * B).det) (x : σ → ℝ) :
    bellmanCost A B Q R M x (-(riccatiGain A B R M *ᵥ x)) =
      x ⬝ᵥ (riccatiMap A B Q R M *ᵥ x) := by
  have h := bellmanCost_eq_add (A := A) (B := B) (Q := Q) hM hR hS x 0
  set S := R + Bᵀ * M * B with hSdef
  set k : ι → ℝ := riccatiGain A B R M *ᵥ x with hk
  have hS0 : bellmanCost A B Q R M x 0 = x ⬝ᵥ (Q *ᵥ x) + (A *ᵥ x) ⬝ᵥ (M *ᵥ (A *ᵥ x)) := by
    simp [bellmanCost]
  have hSk : S *ᵥ k = (Bᵀ * M * A) *ᵥ x := by
    rw [hk, riccatiGain, mulVec_mulVec, ← Matrix.mul_assoc, mul_nonsing_inv _ hS, Matrix.one_mul]
  have hkk : k ⬝ᵥ (S *ᵥ k) = x ⬝ᵥ (((Aᵀ * M * B) * S⁻¹ * (Bᵀ * M * A)) *ᵥ x) := by
    have hT : (Aᵀ * M * B) = (Bᵀ * M * A)ᵀ := by
      rw [transpose_mul, transpose_mul, transpose_transpose, hM, Matrix.mul_assoc]
    have hkdef : k = S⁻¹ *ᵥ ((Bᵀ * M * A) *ᵥ x) := by
      rw [hk, riccatiGain, ← mulVec_mulVec]
    have hsplit : ((Bᵀ * M * A)ᵀ * S⁻¹ * (Bᵀ * M * A)) *ᵥ x =
        (Bᵀ * M * A)ᵀ *ᵥ (S⁻¹ *ᵥ ((Bᵀ * M * A) *ᵥ x)) := by
      rw [mulVec_mulVec, mulVec_mulVec, Matrix.mul_assoc]
    rw [hSk, hT, hsplit, dotProduct_transpose_mulVec, ← hkdef, dotProduct_comm]
  rw [zero_add] at h
  have hAM : (A *ᵥ x) ⬝ᵥ (M *ᵥ (A *ᵥ x)) = x ⬝ᵥ ((Aᵀ * M * A) *ᵥ x) := by
    rw [← mulVec_mulVec, ← mulVec_mulVec, dotProduct_transpose_mulVec]
  rw [hS0, hkk, hAM] at h
  rw [riccatiMap, sub_mulVec, add_mulVec, dotProduct_sub, dotProduct_add]
  linarith

/-- **The linear control minimizes the one-step Bellman cost.** If `M` and `R` are symmetric and
`R + Bᵀ M B` is positive definite, then for every state `x` and control `u`,
`xᵀ (riccatiMap A B Q R M) x = bellmanCost x (-K x) ≤ bellmanCost x u`.

Source: B. Recht, *A tour of reinforcement learning: the view from continuous control*,
arXiv:1806.09460, Section 4 ("the control action is a linear function of the state
`u_t = -K_t x_t`"). -/
theorem bellmanCost_ge {A : Matrix σ σ ℝ} {B : Matrix σ ι ℝ} {Q : Matrix σ σ ℝ}
    {R : Matrix ι ι ℝ} {M : Matrix σ σ ℝ} (hM : Mᵀ = M) (hR : Rᵀ = R)
    (hS : (R + Bᵀ * M * B).PosDef) (x : σ → ℝ) (u : ι → ℝ) :
    x ⬝ᵥ (riccatiMap A B Q R M *ᵥ x) ≤ bellmanCost A B Q R M x u := by
  have hU : IsUnit (R + Bᵀ * M * B).det := (Matrix.isUnit_iff_isUnit_det _).mp hS.isUnit
  rw [← bellmanCost_neg_gain (A := A) (Q := Q) hM hR hU,
    bellmanCost_eq_add (A := A) (Q := Q) hM hR hU x u]
  have := hS.posSemidef.dotProduct_mulVec_nonneg (u + riccatiGain A B R M *ᵥ x)
  simp only [star_trivial] at this
  linarith

omit [DecidableEq ι] in
private theorem transpose_eq_of_posSemidef {κ : Type*} {P : Matrix κ κ ℝ}
    (hP : P.PosSemidef) : Pᵀ = P := by
  rw [← conjTranspose_eq_transpose_of_trivial]; exact hP.isHermitian

omit [DecidableEq ι] in
private theorem bellmanCost_nonneg {A : Matrix σ σ ℝ} {B : Matrix σ ι ℝ} {Q : Matrix σ σ ℝ}
    {R : Matrix ι ι ℝ} {M : Matrix σ σ ℝ} (hQ : Q.PosSemidef) (hR : R.PosSemidef)
    (hM : M.PosSemidef) (x : σ → ℝ) (u : ι → ℝ) : 0 ≤ bellmanCost A B Q R M x u := by
  have h1 := hQ.dotProduct_mulVec_nonneg x
  have h2 := hR.dotProduct_mulVec_nonneg u
  have h3 := hM.dotProduct_mulVec_nonneg (A *ᵥ x + B *ᵥ u)
  simp only [star_trivial] at h1 h2 h3
  unfold bellmanCost
  linarith

/-- **The Riccati update preserves positive semidefiniteness.** If `Q` and `M` are positive
semidefinite and `R` is positive definite, then `riccatiMap A B Q R M` is positive semidefinite.

Source: B. Recht, *A tour of reinforcement learning: the view from continuous control*,
arXiv:1806.09460, Section 4 (the cost-to-go matrices `M_k` of the recursion are positive
semidefinite). -/
theorem riccatiMap_posSemidef {A : Matrix σ σ ℝ} {B : Matrix σ ι ℝ} {Q : Matrix σ σ ℝ}
    {R : Matrix ι ι ℝ} {M : Matrix σ σ ℝ} (hQ : Q.PosSemidef) (hR : R.PosDef)
    (hM : M.PosSemidef) : (riccatiMap A B Q R M).PosSemidef := by
  have hMT := transpose_eq_of_posSemidef hM
  have hRT := transpose_eq_of_posSemidef hR.posSemidef
  have hQT := transpose_eq_of_posSemidef hQ
  have hBMB : (Bᵀ * M * B).PosSemidef := by
    simpa [conjTranspose_eq_transpose_of_trivial, Matrix.mul_assoc] using
      hM.conjTranspose_mul_mul_same B
  have hS : (R + Bᵀ * M * B).PosDef := hR.add_posSemidef hBMB
  have hU : IsUnit (R + Bᵀ * M * B).det := (Matrix.isUnit_iff_isUnit_det _).mp hS.isUnit
  have hST : (R + Bᵀ * M * B)ᵀ = R + Bᵀ * M * B := by
    rw [transpose_add, hRT, transpose_mul, transpose_mul, transpose_transpose, hMT,
      Matrix.mul_assoc]
  refine PosSemidef.of_dotProduct_mulVec_nonneg ?_ fun x => ?_
  · simp only [IsHermitian, conjTranspose_eq_transpose_of_trivial, riccatiMap, transpose_sub,
      transpose_add, transpose_mul, transpose_transpose, transpose_nonsing_inv, hQT, hRT, hMT,
      Matrix.mul_assoc]
  · rw [star_trivial, ← bellmanCost_neg_gain (A := A) (Q := Q) hMT hRT hU]
    exact bellmanCost_nonneg hQ hR.posSemidef hM _ _

/-- **Riccati recursion.** The cost-to-go matrices of the finite-horizon problem, indexed by the
number of remaining steps: `M₀ = Q_f` and `M_{j+1} = riccatiMap A B Q R M_j`.

Source: B. Recht, *A tour of reinforcement learning: the view from continuous control*,
arXiv:1806.09460, Section 4 (the matrices `K_t` "computed via a simple linear algebraic
recursion"). -/
noncomputable def riccatiCostToGo (A : Matrix σ σ ℝ) (B : Matrix σ ι ℝ) (Q : Matrix σ σ ℝ)
    (R : Matrix ι ι ℝ) (Qf : Matrix σ σ ℝ) : ℕ → Matrix σ σ ℝ
  | 0 => Qf
  | j + 1 => riccatiMap A B Q R (riccatiCostToGo A B Q R Qf j)

omit [DecidableEq ι] in
/-- **States of the linear system.** `x₀` given and `x_{t+1} = A x_t + B u_t`.

Source: B. Recht, *A tour of reinforcement learning: the view from continuous control*,
arXiv:1806.09460, Section 4 (the linear dynamics of LQR, here without noise). -/
def lqrState (A : Matrix σ σ ℝ) (B : Matrix σ ι ℝ) (x₀ : σ → ℝ) (u : ℕ → ι → ℝ) : ℕ → σ → ℝ
  | 0 => x₀
  | t + 1 => A *ᵥ lqrState A B x₀ u t + B *ᵥ u t

omit [DecidableEq ι] in
/-- **Finite-horizon LQR cost.** `∑_{t < T} (x_tᵀ Q x_t + u_tᵀ R u_t) + x_Tᵀ Q_f x_T` along the
states `x_t = lqrState A B x₀ u t`.

Source: B. Recht, *A tour of reinforcement learning: the view from continuous control*,
arXiv:1806.09460, Section 4, problem (4.1) without the noise `e_t` and without the factors `1/2`:
`T = N + 1` stage costs and the terminal cost `Q_f`, which is the source's `S`. -/
def lqrCost (A : Matrix σ σ ℝ) (B : Matrix σ ι ℝ) (Q : Matrix σ σ ℝ) (R : Matrix ι ι ℝ)
    (Qf : Matrix σ σ ℝ) (x₀ : σ → ℝ) (u : ℕ → ι → ℝ) (T : ℕ) : ℝ :=
  ∑ t ∈ Finset.range T, (lqrState A B x₀ u t ⬝ᵥ (Q *ᵥ lqrState A B x₀ u t) + u t ⬝ᵥ (R *ᵥ u t)) +
    lqrState A B x₀ u T ⬝ᵥ (Qf *ᵥ lqrState A B x₀ u T)

omit [DecidableEq ι] in
private theorem lqrState_succ (A : Matrix σ σ ℝ) (B : Matrix σ ι ℝ) (x₀ : σ → ℝ)
    (u : ℕ → ι → ℝ) (t : ℕ) :
    lqrState A B x₀ u (t + 1) = lqrState A B (A *ᵥ x₀ + B *ᵥ u 0) (fun s => u (s + 1)) t := by
  induction t with
  | zero => rfl
  | succ t ih => rw [lqrState, ih]; rfl

omit [DecidableEq ι] in
private theorem lqrCost_succ (A : Matrix σ σ ℝ) (B : Matrix σ ι ℝ) (Q : Matrix σ σ ℝ)
    (R : Matrix ι ι ℝ) (Qf : Matrix σ σ ℝ) (x₀ : σ → ℝ) (u : ℕ → ι → ℝ) (T : ℕ) :
    lqrCost A B Q R Qf x₀ u (T + 1) = x₀ ⬝ᵥ (Q *ᵥ x₀) + u 0 ⬝ᵥ (R *ᵥ u 0) +
      lqrCost A B Q R Qf (A *ᵥ x₀ + B *ᵥ u 0) (fun s => u (s + 1)) T := by
  unfold lqrCost
  rw [Finset.sum_range_succ']
  simp_rw [lqrState_succ A B x₀ u]
  have h0 : lqrState A B x₀ u 0 = x₀ := rfl
  rw [h0]
  ring

/-- **Every control sequence costs at least the Riccati value.** Let `Q` and `Q_f` be positive
semidefinite and `R` positive definite. Then for every horizon `T`, initial state `x₀` and control
sequence `u`, `x₀ᵀ M_T x₀ ≤ lqrCost x₀ u T`, where `M_T = riccatiCostToGo A B Q R Q_f T`.

Source: B. Recht, *A tour of reinforcement learning: the view from continuous control*,
arXiv:1806.09460, Section 4 ("the standard LQR problem admits an elegant dynamic programming
solution"), for the deterministic version of problem (4.1). -/
theorem lqrCost_ge {A : Matrix σ σ ℝ} {B : Matrix σ ι ℝ} {Q : Matrix σ σ ℝ} {R : Matrix ι ι ℝ}
    {Qf : Matrix σ σ ℝ} (hQ : Q.PosSemidef) (hR : R.PosDef) (hQf : Qf.PosSemidef) (T : ℕ) :
    ∀ (x₀ : σ → ℝ) (u : ℕ → ι → ℝ),
      x₀ ⬝ᵥ (riccatiCostToGo A B Q R Qf T *ᵥ x₀) ≤ lqrCost A B Q R Qf x₀ u T := by
  have hP : ∀ j, (riccatiCostToGo A B Q R Qf j).PosSemidef := by
    intro j
    induction j with
    | zero => exact hQf
    | succ j ih => exact riccatiMap_posSemidef hQ hR ih
  induction T with
  | zero => intro x₀ u; simp [riccatiCostToGo, lqrCost, lqrState]
  | succ T ih =>
    intro x₀ u
    set P := riccatiCostToGo A B Q R Qf T
    have hPT := transpose_eq_of_posSemidef (hP T)
    have hRT := transpose_eq_of_posSemidef hR.posSemidef
    have hBMB : (Bᵀ * P * B).PosSemidef := by
      simpa [conjTranspose_eq_transpose_of_trivial, Matrix.mul_assoc] using
        (hP T).conjTranspose_mul_mul_same B
    have hS : (R + Bᵀ * P * B).PosDef := hR.add_posSemidef hBMB
    have hstep := bellmanCost_ge (A := A) (Q := Q) hPT hRT hS x₀ (u 0)
    have hrest := ih (A *ᵥ x₀ + B *ᵥ u 0) (fun s => u (s + 1))
    rw [lqrCost_succ]
    change x₀ ⬝ᵥ (riccatiMap A B Q R P *ᵥ x₀) ≤ _
    unfold bellmanCost at hstep
    linarith

/-- **The linear feedback attains the Riccati value.** Under the hypotheses of `lqrCost_ge`, for
every horizon `T` and initial state `x₀` there is a control sequence `u` with
`lqrCost x₀ u T = x₀ᵀ M_T x₀`, and it is the linear state feedback
`u_t = -K_{T-1-t} x_t` with `K_j = riccatiGain A B R M_j`.

Source: B. Recht, *A tour of reinforcement learning: the view from continuous control*,
arXiv:1806.09460, Section 4 ("the control action is a linear function of the state
`u_t = -K_t x_t` for some matrix `K_t` that can be computed via a simple linear algebraic
recursion"), for the deterministic version of problem (4.1). -/
theorem lqrCost_feedback {A : Matrix σ σ ℝ} {B : Matrix σ ι ℝ} {Q : Matrix σ σ ℝ}
    {R : Matrix ι ι ℝ} {Qf : Matrix σ σ ℝ} (hQ : Q.PosSemidef) (hR : R.PosDef)
    (hQf : Qf.PosSemidef) (T : ℕ) :
    ∀ x₀ : σ → ℝ, ∃ u : ℕ → ι → ℝ,
      lqrCost A B Q R Qf x₀ u T = x₀ ⬝ᵥ (riccatiCostToGo A B Q R Qf T *ᵥ x₀) ∧
      ∀ t < T, u t = -(riccatiGain A B R (riccatiCostToGo A B Q R Qf (T - 1 - t)) *ᵥ
        lqrState A B x₀ u t) := by
  have hP : ∀ j, (riccatiCostToGo A B Q R Qf j).PosSemidef := by
    intro j
    induction j with
    | zero => exact hQf
    | succ j ih => exact riccatiMap_posSemidef hQ hR ih
  induction T with
  | zero => intro x₀; exact ⟨fun _ => 0, by simp [riccatiCostToGo, lqrCost, lqrState], by simp⟩
  | succ T ih =>
    intro x₀
    set P := riccatiCostToGo A B Q R Qf T
    have hPT := transpose_eq_of_posSemidef (hP T)
    have hRT := transpose_eq_of_posSemidef hR.posSemidef
    have hBMB : (Bᵀ * P * B).PosSemidef := by
      simpa [conjTranspose_eq_transpose_of_trivial, Matrix.mul_assoc] using
        (hP T).conjTranspose_mul_mul_same B
    have hS : (R + Bᵀ * P * B).PosDef := hR.add_posSemidef hBMB
    have hU : IsUnit (R + Bᵀ * P * B).det := (Matrix.isUnit_iff_isUnit_det _).mp hS.isUnit
    set u₀ : ι → ℝ := -(riccatiGain A B R P *ᵥ x₀)
    obtain ⟨u', hcost, hfb⟩ := ih (A *ᵥ x₀ + B *ᵥ u₀)
    let u : ℕ → ι → ℝ := fun t => Nat.casesOn t u₀ u'
    refine ⟨u, ?_, ?_⟩
    · rw [lqrCost_succ]
      change x₀ ⬝ᵥ (Q *ᵥ x₀) + u₀ ⬝ᵥ (R *ᵥ u₀) + lqrCost A B Q R Qf (A *ᵥ x₀ + B *ᵥ u₀) u' T = _
      rw [hcost]
      have h := bellmanCost_neg_gain (A := A) (Q := Q) hPT hRT hU x₀
      unfold bellmanCost at h
      change _ = x₀ ⬝ᵥ (riccatiMap A B Q R P *ᵥ x₀)
      rw [← h]
    · intro t ht
      cases t with
      | zero =>
        change u₀ = _
        simp [u₀, P, lqrState]
      | succ t =>
        change u' t = _
        rw [hfb t (by omega), lqrState_succ]
        have h : T + 1 - 1 - (t + 1) = T - 1 - t := by omega
        rw [h]
        rfl

private theorem riccatiCostToGo_posSemidef_aux {A : Matrix σ σ ℝ} {B : Matrix σ ι ℝ}
    {Q : Matrix σ σ ℝ} {R : Matrix ι ι ℝ} {Qf : Matrix σ σ ℝ}
    (hQ : Q.PosSemidef) (hR : R.PosDef) (hQf : Qf.PosSemidef) (j : ℕ) :
    (riccatiCostToGo A B Q R Qf j).PosSemidef := by
  induction j with
  | zero => exact hQf
  | succ _ ih => exact riccatiMap_posSemidef hQ hR ih

/-- **Exact finite-horizon LQR cost decomposition.** Let the state and terminal cost
matrices `Q` and `Qf` be positive semidefinite, and let the control cost matrix `R` be
positive definite. Let `x_t` be the state at time `t` under the control stream `u`, and let `M_j`
be the Riccati cost-to-go matrix with `j` steps remaining (`M_0 = Qf`). Define the gain
`K_j = (R + Bᵀ M_j B)⁻¹ Bᵀ M_j A`. Over `T` steps, the total cost is `x₀ᵀ M_T x₀`
plus `∑_{t<T} e_tᵀ (R + Bᵀ M_{T-1-t} B) e_t`, where `e_t = u_t + K_{T-1-t} x_t`.

See Sontag, *Mathematical Control Theory*, §8.2, Exercise 8.2.7 for the discrete-time
analogue. The identity follows by telescoping the one-step completion of squares. -/
theorem lqrCost_eq_riccati_add_feedback_residual {A : Matrix σ σ ℝ} {B : Matrix σ ι ℝ}
    {Q : Matrix σ σ ℝ} {R : Matrix ι ι ℝ} {Qf : Matrix σ σ ℝ}
    (hQ : Q.PosSemidef) (hR : R.PosDef) (hQf : Qf.PosSemidef)
    (T : ℕ) (x₀ : σ → ℝ) (u : ℕ → ι → ℝ) :
    let x := lqrState A B x₀ u
    let M := riccatiCostToGo A B Q R Qf
    let e := fun t => u t + riccatiGain A B R (M (T - 1 - t)) *ᵥ x t
    lqrCost A B Q R Qf x₀ u T = x₀ ⬝ᵥ (M T *ᵥ x₀) +
      ∑ t ∈ Finset.range T, e t ⬝ᵥ ((R + Bᵀ * M (T - 1 - t) * B) *ᵥ e t) := by
  intro x M e
  let V := fun t => x t ⬝ᵥ (M (T - t) *ᵥ x t)
  let L := fun t => x t ⬝ᵥ (Q *ᵥ x t) + u t ⬝ᵥ (R *ᵥ u t)
  let E := fun t => e t ⬝ᵥ ((R + Bᵀ * M (T - 1 - t) * B) *ᵥ e t)
  have hstep (t : ℕ) (ht : t ∈ Finset.range T) : L t + (V (t + 1) - V t) = E t := by
    have ht' := Finset.mem_range.mp ht
    let j := T - 1 - t
    have h₁ : T - (t + 1) = j := by dsimp [j]; omega
    have h₂ : T - t = j + 1 := by dsimp [j]; omega
    have hP : (M j).PosSemidef := riccatiCostToGo_posSemidef_aux hQ hR hQf j
    have hS : (R + Bᵀ * M j * B).PosDef := by
      classical
      exact ControlTheory.posDef_R_add_transpose_mul_mul hP hR
    have hU := (Matrix.isUnit_iff_isUnit_det _).mp hS.isUnit
    have hPT := transpose_eq_of_posSemidef hP
    have hRT := transpose_eq_of_posSemidef hR.posSemidef
    have hc := bellmanCost_eq_add (A := A) (B := B) (Q := Q) hPT hRT hU (x t) (u t)
    rw [bellmanCost_neg_gain (A := A) (Q := Q) hPT hRT hU] at hc
    have hV₁ : V (t + 1) = (A *ᵥ x t + B *ᵥ u t) ⬝ᵥ (M j *ᵥ (A *ᵥ x t + B *ᵥ u t)) := by
      change x (t + 1) ⬝ᵥ (M (T - (t + 1)) *ᵥ x (t + 1)) = _
      rw [h₁]
      rfl
    have hV₂ : V t = x t ⬝ᵥ (riccatiMap A B Q R (M j) *ᵥ x t) := by
      change x t ⬝ᵥ (M (T - t) *ᵥ x t) = _
      rw [h₂]
      rfl
    change L t + _ = _ + E t at hc
    rw [hV₁, hV₂]
    linarith only [hc]
  have hs : (∑ t ∈ Finset.range T, (L t + (V (t + 1) - V t))) = ∑ t ∈ Finset.range T, E t :=
    Finset.sum_congr rfl hstep
  rw [Finset.sum_add_distrib, Finset.sum_range_sub] at hs
  have hVT : V T = x T ⬝ᵥ (Qf *ᵥ x T) := by simp [V, M, riccatiCostToGo]
  have hV₀ : V 0 = x₀ ⬝ᵥ (M T *ᵥ x₀) := by simp [V, x, lqrState]
  rw [hVT, hV₀] at hs
  change (∑ t ∈ Finset.range T, L t) + x T ⬝ᵥ (Qf *ᵥ x T) =
    x₀ ⬝ᵥ (M T *ᵥ x₀) + ∑ t ∈ Finset.range T, E t
  linarith only [hs]

/-- Let the state and terminal cost matrices `Q` and `Qf` be positive semidefinite and
let the control cost matrix `R` be positive definite. With `j` steps remaining, let
`M_j` be the Riccati cost-to-go matrix (`M_0 = Qf`) and
`K_j = (R + Bᵀ M_j B)⁻¹ Bᵀ M_j A`. A control stream has cost `x₀ᵀ M_T x₀` over `T`
steps if and only if at every time `t < T` it uses `u_t = -K_{T-1-t} x_t`, where `x_t`
is the state reached by that stream. No condition is imposed at or after `T`. -/
theorem lqrCost_eq_riccati_iff_feedback {A : Matrix σ σ ℝ} {B : Matrix σ ι ℝ}
    {Q : Matrix σ σ ℝ} {R : Matrix ι ι ℝ} {Qf : Matrix σ σ ℝ}
    (hQ : Q.PosSemidef) (hR : R.PosDef) (hQf : Qf.PosSemidef)
    (T : ℕ) (x₀ : σ → ℝ) (u : ℕ → ι → ℝ) :
    let M := riccatiCostToGo A B Q R Qf
    lqrCost A B Q R Qf x₀ u T = x₀ ⬝ᵥ (M T *ᵥ x₀) ↔
      ∀ t < T, u t = -(riccatiGain A B R (M (T - 1 - t)) *ᵥ lqrState A B x₀ u t) := by
  intro M
  let e := fun t => u t + riccatiGain A B R (M (T - 1 - t)) *ᵥ lqrState A B x₀ u t
  let S := fun t => R + Bᵀ * M (T - 1 - t) * B
  let E := fun t => e t ⬝ᵥ (S t *ᵥ e t)
  have hdecomp : lqrCost A B Q R Qf x₀ u T =
      x₀ ⬝ᵥ (M T *ᵥ x₀) + ∑ t ∈ Finset.range T, E t :=
    lqrCost_eq_riccati_add_feedback_residual hQ hR hQf T x₀ u
  have hS (t : ℕ) : (S t).PosDef := by
    classical
    exact ControlTheory.posDef_R_add_transpose_mul_mul
      (riccatiCostToGo_posSemidef_aux hQ hR hQf _) hR
  rw [hdecomp, add_eq_left]
  constructor
  · intro h t ht
    have hnonneg (t : ℕ) : 0 ≤ E t := by
      simpa only [star_trivial] using (hS t).posSemidef.dotProduct_mulVec_nonneg (e t)
    have hEt : E t = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun t _ => hnonneg t)).mp h t (Finset.mem_range.mpr ht)
    have he : e t = 0 := by
      by_contra hn
      have hp : 0 < E t := by
        simpa only [star_trivial] using (hS t).dotProduct_mulVec_pos hn
      exact hp.ne' hEt
    exact eq_neg_of_add_eq_zero_left he
  · intro h
    apply Finset.sum_eq_zero
    intro t ht
    have he : e t = 0 := by
      change u t + _ = 0
      exact add_eq_zero_iff_eq_neg.mpr (h t (Finset.mem_range.mp ht))
    simp [E, he]

/-- **Unique finite-horizon LQR control.** Let `Q` and `Qf` be positive semidefinite
and `R` be positive definite. For horizon `T` and initial state `x₀`, some control stream
attains the minimum cost `x₀ᵀ M_T x₀`, where `M_T` is the Riccati cost-to-go matrix
with `T` steps remaining. Every stream attaining that cost agrees with the minimizer
at every time `t < T`. Values at or after `T` do not enter the cost. -/
theorem exists_lqrCost_minimizer_unique_prefix {A : Matrix σ σ ℝ} {B : Matrix σ ι ℝ}
    {Q : Matrix σ σ ℝ} {R : Matrix ι ι ℝ} {Qf : Matrix σ σ ℝ}
    (hQ : Q.PosSemidef) (hR : R.PosDef) (hQf : Qf.PosSemidef) (T : ℕ) (x₀ : σ → ℝ) :
    ∃ u : ℕ → ι → ℝ,
      lqrCost A B Q R Qf x₀ u T = x₀ ⬝ᵥ (riccatiCostToGo A B Q R Qf T *ᵥ x₀) ∧
        ∀ v : ℕ → ι → ℝ, lqrCost A B Q R Qf x₀ u T ≤ lqrCost A B Q R Qf x₀ v T ∧
          (lqrCost A B Q R Qf x₀ v T = lqrCost A B Q R Qf x₀ u T → ∀ t < T, v t = u t) := by
  obtain ⟨u, hu, hfb⟩ := lqrCost_feedback hQ hR hQf T x₀
  refine ⟨u, hu, fun v => ⟨hu.trans_le (lqrCost_ge hQ hR hQf T x₀ v), ?_⟩⟩
  intro hv
  have hvfb := (lqrCost_eq_riccati_iff_feedback hQ hR hQf T x₀ v).mp (hv.trans hu)
  have hstate (t : ℕ) (ht : t ≤ T) : lqrState A B x₀ v t = lqrState A B x₀ u t := by
    induction t with
    | zero => rfl
    | succ t ih =>
      have hlt : t < T := by omega
      rw [lqrState, lqrState, hvfb t hlt, hfb t hlt, ih hlt.le]
  intro t ht
  rw [hvfb t ht, hfb t ht, hstate t ht.le]

end CSLibExt.MachineLearning.LinearQuadraticRegulator

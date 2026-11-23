/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
import MathlibExt.LinearAlgebra.Matrix.DeterminantLemma
import Mathlib.Topology.Algebra.Order.Field

/-!
# Recursive least squares

The recursive least-squares (RLS) algorithm of system identification estimates the parameter
`θ` of the linear regression `y_{k+1} = φ_kᵀ θ + w_{k+1}` from the data `(φ_k, y_{k+1})` by
```
θ_{k+1} = θ_k + P_k φ_k (y_{k+1} - φ_kᵀ θ_k) / (1 + φ_kᵀ P_k φ_k),
P_{k+1} = P_k - P_k φ_k φ_kᵀ P_k / (1 + φ_kᵀ P_k φ_k),
```
started at an initial estimate `θ_0` and a positive definite matrix `P_0` (Xie, Zhang and Guo,
*Convergence of a distributed least squares*, IEEE Trans. Automat. Control, accepted version
2020, DOI 10.1109/TAC.2020.3047989, Algorithm 1, equations (2)–(4), with a single sensor, as in
their Remark 2.1).

## Main results

* `rls_snd_eq_inv`: by the matrix inversion lemma, `P_t = (P_0⁻¹ + ∑_{k<t} φ_k φ_kᵀ)⁻¹`.
* `rlsInformation_mulVec_rls_fst` and `rls_fst_eq`: `θ_t` solves the normal equations
  `(P_0⁻¹ + ∑_{k<t} φ_k φ_kᵀ) θ_t = P_0⁻¹ θ_0 + ∑_{k<t} y_{k+1} φ_k` of the regularised batch
  least-squares problem.
* `sum_rls_gain_le_log_det`: the accumulated gains satisfy
  `∑_{k<t} φ_kᵀ P_k φ_k / (1 + φ_kᵀ P_k φ_k) ≤ log det P_t⁻¹ - log det P_0⁻¹`, the deterministic
  inequality behind the logarithmic rates of least squares.
* `rls_error_sq_le` and `tendsto_rls_fst_of_noiseFree`: in the noise-free case
  `y_{k+1} = φ_kᵀ θ`, the estimation error satisfies `P_t⁻¹ (θ_t - θ) = P_0⁻¹ (θ_0 - θ)`, so it
  tends to zero as soon as the smallest eigenvalue of `∑_{k<t} φ_k φ_kᵀ` tends to infinity.
-/

open Matrix Filter Topology

@[expose] public section

namespace MathlibExt.Analysis.Control.RecursiveLeastSquares

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- **One step of recursive least squares.** From the estimate `θ`, the matrix `P`, the
regressor `φ` and the new observation `y`, it returns
`(θ + P φ (y - φᵀ θ) / (1 + φᵀ P φ), P - P φ φᵀ P / (1 + φᵀ P φ))` (Xie, Zhang and Guo,
IEEE Trans. Automat. Control, DOI 10.1109/TAC.2020.3047989, equations (2)–(4) with one sensor). -/
noncomputable def rlsStep (φ : n → ℝ) (y : ℝ) (θP : (n → ℝ) × Matrix n n ℝ) :
    (n → ℝ) × Matrix n n ℝ :=
  (θP.1 + ((y - φ ⬝ᵥ θP.1) / (1 + φ ⬝ᵥ (θP.2 *ᵥ φ))) • (θP.2 *ᵥ φ),
    θP.2 - (1 + φ ⬝ᵥ (θP.2 *ᵥ φ))⁻¹ • (θP.2 * vecMulVec φ φ * θP.2))

/-- **Recursive least-squares estimates.** For regressors `φ_k`, observations `y_{k+1}`, an
initial estimate `θ_0` and an initial matrix `P_0`, `rls φ y θ₀ P₀ t = (θ_t, P_t)` is obtained by
applying `rlsStep (φ k) (y (k + 1))` for `k = 0, …, t - 1`: the observation `y (k + 1)` follows
the regressor `φ k`, as in the model `y_{k+1} = φ_kᵀ θ + w_{k+1}`. -/
noncomputable def rls (φ : ℕ → n → ℝ) (y : ℕ → ℝ) (θ₀ : n → ℝ) (P₀ : Matrix n n ℝ) :
    ℕ → (n → ℝ) × Matrix n n ℝ
  | 0 => (θ₀, P₀)
  | t + 1 => rlsStep (φ t) (y (t + 1)) (rls φ y θ₀ P₀ t)

/-- **Information matrix of recursive least squares.** `P_0⁻¹ + ∑_{k<t} φ_k φ_kᵀ`, the matrix
whose inverse is the RLS matrix `P_t`. -/
noncomputable def rlsInformation (P₀ : Matrix n n ℝ) (φ : ℕ → n → ℝ) (t : ℕ) : Matrix n n ℝ :=
  P₀⁻¹ + ∑ k ∈ Finset.range t, vecMulVec (φ k) (φ k)

theorem rlsInformation_succ (P₀ : Matrix n n ℝ) (φ : ℕ → n → ℝ) (t : ℕ) :
    rlsInformation P₀ φ (t + 1) = rlsInformation P₀ φ t + vecMulVec (φ t) (φ t) := by
  simp [rlsInformation, Finset.sum_range_succ, add_assoc]

omit [Fintype n] [DecidableEq n] in
private theorem posSemidef_vecMulVec_self [Finite n] (φ : n → ℝ) : (vecMulVec φ φ).PosSemidef := by
  simpa using posSemidef_vecMulVec_self_star φ

/-- **The information matrix is positive definite** when `P_0` is. -/
theorem posDef_rlsInformation {P₀ : Matrix n n ℝ} (hP₀ : P₀.PosDef) (φ : ℕ → n → ℝ) (t : ℕ) :
    (rlsInformation P₀ φ t).PosDef :=
  hP₀.inv.add_posSemidef (posSemidef_sum _ fun k _ => posSemidef_vecMulVec_self (φ k))

omit [DecidableEq n] in
private theorem vecMulVec_mul_mul_vecMulVec (φ : n → ℝ) (P : Matrix n n ℝ) :
    vecMulVec φ φ * P * vecMulVec φ φ = (φ ⬝ᵥ (P *ᵥ φ)) • vecMulVec φ φ := by
  rw [mul_vecMulVec, ← mulVec_mulVec, vecMulVec_mulVec]
  ext i j
  simp [vecMulVec_apply, Matrix.smul_apply, Pi.smul_apply]
  ring

/-- **RLS step and the matrix inversion lemma.** If `R P = 1` with `R` positive definite, then
after one step the new matrix is the inverse of `R + φ φᵀ`. -/
private theorem rlsStep_snd_mul {R P : Matrix n n ℝ} (hR : R.PosDef) (hRP : R * P = 1)
    (φ : n → ℝ) (y : ℝ) (θ : n → ℝ) :
    (R + vecMulVec φ φ) * (rlsStep φ y (θ, P)).2 = 1 := by
  have hP : P = R⁻¹ := (inv_eq_right_inv hRP).symm
  have hq : 0 ≤ φ ⬝ᵥ (P *ᵥ φ) := by
    rw [hP]; exact hR.inv.posSemidef.dotProduct_mulVec_nonneg φ
  set q := φ ⬝ᵥ (P *ᵥ φ)
  have hs : (1 + q) ≠ 0 := by positivity
  have key := vecMulVec_mul_mul_vecMulVec φ P
  simp only [rlsStep]
  have e1 : vecMulVec φ φ * (P * vecMulVec φ φ * P) = q • (vecMulVec φ φ * P) := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, key, Matrix.smul_mul]
  have e2 : R * (P * vecMulVec φ φ * P) = vecMulVec φ φ * P := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hRP, Matrix.one_mul]
  rw [add_mul, mul_sub, mul_sub, Matrix.mul_smul, Matrix.mul_smul, e1, e2, hRP, smul_smul]
  have : (1 + q)⁻¹ * q = 1 - (1 + q)⁻¹ := by field_simp; ring
  rw [this, sub_smul, one_smul]
  abel

omit [DecidableEq n] in
private theorem vecMulVec_self_mulVec (φ x : n → ℝ) : vecMulVec φ φ *ᵥ x = (φ ⬝ᵥ x) • φ := by
  rw [vecMulVec_mulVec, op_smul_eq_smul]

/-- One RLS step adds `y φ` to the right-hand side of the normal equations. -/
private theorem rlsStep_fst_mulVec {R P : Matrix n n ℝ} (hR : R.PosDef) (hRP : R * P = 1)
    (φ : n → ℝ) (y : ℝ) (θ : n → ℝ) :
    (R + vecMulVec φ φ) *ᵥ (rlsStep φ y (θ, P)).1 = R *ᵥ θ + y • φ := by
  have hP : P = R⁻¹ := (inv_eq_right_inv hRP).symm
  have hq : 0 ≤ φ ⬝ᵥ (P *ᵥ φ) := by
    rw [hP]; exact hR.inv.posSemidef.dotProduct_mulVec_nonneg φ
  have hs : (1 + φ ⬝ᵥ (P *ᵥ φ)) ≠ 0 := by positivity
  have hRPφ : R *ᵥ (P *ᵥ φ) = φ := by rw [mulVec_mulVec, hRP, one_mulVec]
  simp only [rlsStep]
  rw [add_mulVec, mulVec_add, mulVec_add, mulVec_smul, mulVec_smul, hRPφ, vecMulVec_self_mulVec,
    vecMulVec_self_mulVec]
  ext i
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  field_simp
  ring

/-- The two RLS invariants, proved together by induction. -/
private theorem rls_invariants {P₀ : Matrix n n ℝ} (hP₀ : P₀.PosDef) (φ : ℕ → n → ℝ)
    (y : ℕ → ℝ) (θ₀ : n → ℝ) (t : ℕ) :
    rlsInformation P₀ φ t * (rls φ y θ₀ P₀ t).2 = 1 ∧
      rlsInformation P₀ φ t *ᵥ (rls φ y θ₀ P₀ t).1 =
        P₀⁻¹ *ᵥ θ₀ + ∑ k ∈ Finset.range t, y (k + 1) • φ k := by
  induction t with
  | zero =>
    simp only [rlsInformation, Finset.range_zero, Finset.sum_empty, add_zero, rls]
    exact ⟨nonsing_inv_mul _ ((isUnit_iff_isUnit_det P₀).mp hP₀.isUnit), trivial⟩
  | succ t ih =>
    have hR := posDef_rlsInformation hP₀ φ t
    simp only [rls]
    rcases h : rls φ y θ₀ P₀ t with ⟨θ, P⟩
    rw [h] at ih
    rw [rlsInformation_succ, rlsStep_snd_mul hR ih.1, rlsStep_fst_mulVec hR ih.1, ih.2,
      Finset.sum_range_succ, add_assoc]
    exact ⟨rfl, rfl⟩

/-- **The RLS matrix is the inverse of the information matrix** (the matrix inversion lemma).
For positive definite `P_0`, every regressor sequence `φ` and every `t`, the RLS matrix is
`P_t = (P_0⁻¹ + ∑_{k<t} φ_k φ_kᵀ)⁻¹`. The update
`P_{k+1} = P_k - P_k φ_k φ_kᵀ P_k / (1 + φ_kᵀ P_k φ_k)` is the Sherman–Morrison form of
`P_{k+1}⁻¹ = P_k⁻¹ + φ_k φ_kᵀ`, the information form in which Liu (arXiv:2609.11831v3,
equation (2.2)) writes the recursion; Mathlib's Woodbury identity is
`Matrix.add_mul_mul_inv_eq_sub`. -/
theorem rls_snd_eq_inv {P₀ : Matrix n n ℝ} (hP₀ : P₀.PosDef) (φ : ℕ → n → ℝ) (y : ℕ → ℝ)
    (θ₀ : n → ℝ) (t : ℕ) : (rls φ y θ₀ P₀ t).2 = (rlsInformation P₀ φ t)⁻¹ :=
  (inv_eq_right_inv (rls_invariants hP₀ φ y θ₀ t).1).symm

/-- **RLS solves the regularised normal equations.** For positive definite `P_0`, the RLS
estimate satisfies `(P_0⁻¹ + ∑_{k<t} φ_k φ_kᵀ) θ_t = P_0⁻¹ θ_0 + ∑_{k<t} y_{k+1} φ_k`, the
normal equations of the batch problem of minimising
`(θ - θ_0)ᵀ P_0⁻¹ (θ - θ_0) + ∑_{k<t} (y_{k+1} - φ_kᵀ θ)²`. -/
theorem rlsInformation_mulVec_rls_fst {P₀ : Matrix n n ℝ} (hP₀ : P₀.PosDef) (φ : ℕ → n → ℝ)
    (y : ℕ → ℝ) (θ₀ : n → ℝ) (t : ℕ) :
    rlsInformation P₀ φ t *ᵥ (rls φ y θ₀ P₀ t).1 =
      P₀⁻¹ *ᵥ θ₀ + ∑ k ∈ Finset.range t, y (k + 1) • φ k :=
  (rls_invariants hP₀ φ y θ₀ t).2

/-- **Recursive least squares equals batch regularised least squares.** For positive definite
`P_0`, `θ_t = (P_0⁻¹ + ∑_{k<t} φ_k φ_kᵀ)⁻¹ (P_0⁻¹ θ_0 + ∑_{k<t} y_{k+1} φ_k)`, the unique
solution of the normal equations of `rlsInformation_mulVec_rls_fst`. -/
theorem rls_fst_eq {P₀ : Matrix n n ℝ} (hP₀ : P₀.PosDef) (φ : ℕ → n → ℝ) (y : ℕ → ℝ)
    (θ₀ : n → ℝ) (t : ℕ) :
    (rls φ y θ₀ P₀ t).1 =
      (rlsInformation P₀ φ t)⁻¹ *ᵥ (P₀⁻¹ *ᵥ θ₀ + ∑ k ∈ Finset.range t, y (k + 1) • φ k) := by
  have hdet : IsUnit (rlsInformation P₀ φ t).det :=
    (isUnit_iff_isUnit_det _).mp (posDef_rlsInformation hP₀ φ t).isUnit
  rw [← rlsInformation_mulVec_rls_fst hP₀ φ y θ₀ t, mulVec_mulVec, nonsing_inv_mul _ hdet,
    one_mulVec]

/-- **Error identity of noise-free RLS.** If `y_{k+1} = φ_kᵀ θ` for every `k < t`, then
`(P_0⁻¹ + ∑_{k<t} φ_k φ_kᵀ)(θ_t - θ) = P_0⁻¹ (θ_0 - θ)`; this is the noise-free case of the error
recursion (9) of Xie, Zhang and Guo (IEEE Trans. Automat. Control,
DOI 10.1109/TAC.2020.3047989) with a single sensor. -/
theorem rlsInformation_mulVec_error_of_noiseFree {P₀ : Matrix n n ℝ} (hP₀ : P₀.PosDef)
    (φ : ℕ → n → ℝ) (y : ℕ → ℝ) (θ₀ θ : n → ℝ) (t : ℕ)
    (hy : ∀ k < t, y (k + 1) = φ k ⬝ᵥ θ) :
    rlsInformation P₀ φ t *ᵥ ((rls φ y θ₀ P₀ t).1 - θ) = P₀⁻¹ *ᵥ (θ₀ - θ) := by
  rw [mulVec_sub, rlsInformation_mulVec_rls_fst hP₀, rlsInformation, add_mulVec, sum_mulVec,
    mulVec_sub]
  have : ∑ k ∈ Finset.range t, y (k + 1) • φ k =
      ∑ k ∈ Finset.range t, vecMulVec (φ k) (φ k) *ᵥ θ :=
    Finset.sum_congr rfl fun k hk => by
      rw [vecMulVec_self_mulVec, hy k (Finset.mem_range.mp hk)]
  rw [this]
  abel

/-- **Error bound of noise-free RLS under excitation.** Let `P_0` be positive definite and
`y_{k+1} = φ_kᵀ θ` for `k < t`. If `M > 0` is a lower bound for the smallest eigenvalue of
`∑_{k<t} φ_k φ_kᵀ`, in the form `M |x|² ≤ xᵀ (∑_{k<t} φ_k φ_kᵀ) x` for all `x`, then
`|θ_t - θ|² ≤ |P_0⁻¹ (θ_0 - θ)|² / M²` (Euclidean norms, written as dot products). -/
theorem rls_error_sq_le {P₀ : Matrix n n ℝ} (hP₀ : P₀.PosDef) (φ : ℕ → n → ℝ) (y : ℕ → ℝ)
    (θ₀ θ : n → ℝ) (t : ℕ) (hy : ∀ k < t, y (k + 1) = φ k ⬝ᵥ θ) {M : ℝ} (hM : 0 < M)
    (hexc : ∀ x : n → ℝ,
      M * (x ⬝ᵥ x) ≤ x ⬝ᵥ ((∑ k ∈ Finset.range t, vecMulVec (φ k) (φ k)) *ᵥ x)) :
    ((rls φ y θ₀ P₀ t).1 - θ) ⬝ᵥ ((rls φ y θ₀ P₀ t).1 - θ) ≤
      (P₀⁻¹ *ᵥ (θ₀ - θ)) ⬝ᵥ (P₀⁻¹ *ᵥ (θ₀ - θ)) / M ^ 2 := by
  set e := (rls φ y θ₀ P₀ t).1 - θ
  set c := P₀⁻¹ *ᵥ (θ₀ - θ)
  have hRe : rlsInformation P₀ φ t *ᵥ e = c :=
    rlsInformation_mulVec_error_of_noiseFree hP₀ φ y θ₀ θ t hy
  have h0 : 0 ≤ e ⬝ᵥ (P₀⁻¹ *ᵥ e) := hP₀.inv.posSemidef.dotProduct_mulVec_nonneg e
  have h1 : M * (e ⬝ᵥ e) ≤ e ⬝ᵥ c := by
    have := hexc e
    rw [← hRe, rlsInformation, add_mulVec, dotProduct_add]
    linarith
  have h2 : 0 ≤ (M • e - c) ⬝ᵥ (M • e - c) := by
    simpa using dotProduct_self_star_nonneg (M • e - c)
  have h3 : (M • e - c) ⬝ᵥ (M • e - c) = M ^ 2 * (e ⬝ᵥ e) - 2 * M * (e ⬝ᵥ c) + c ⬝ᵥ c := by
    simp only [sub_dotProduct, dotProduct_sub, smul_dotProduct, dotProduct_smul, smul_eq_mul,
      dotProduct_comm c e]
    ring
  rw [le_div_iff₀ (by positivity)]
  nlinarith

omit [DecidableEq n] in
/-- **Convergence of noise-free RLS under growing excitation.** Let `P_0` be positive definite
and let the data be noise free, `y_{k+1} = φ_kᵀ θ` for every `k`. If the smallest eigenvalue of
`∑_{k<t} φ_k φ_kᵀ` tends to infinity, written as: for every `M`, eventually
`M |x|² ≤ xᵀ (∑_{k<t} φ_k φ_kᵀ) x` for all `x`, then the RLS estimates `θ_t` converge to `θ`,
whatever the initial estimate `θ_0`. -/
theorem tendsto_rls_fst_of_noiseFree {P₀ : Matrix n n ℝ} (hP₀ : P₀.PosDef) (φ : ℕ → n → ℝ)
    (y : ℕ → ℝ) (θ₀ θ : n → ℝ) (hy : ∀ k, y (k + 1) = φ k ⬝ᵥ θ)
    (hexc : ∀ M : ℝ, ∀ᶠ t in atTop, ∀ x : n → ℝ,
      M * (x ⬝ᵥ x) ≤ x ⬝ᵥ ((∑ k ∈ Finset.range t, vecMulVec (φ k) (φ k)) *ᵥ x)) :
    Tendsto (fun t => (rls φ y θ₀ P₀ t).1) atTop (𝓝 θ) := by
  classical
  set C := (P₀⁻¹ *ᵥ (θ₀ - θ)) ⬝ᵥ (P₀⁻¹ *ᵥ (θ₀ - θ))
  have hC : 0 ≤ C := by simpa using dotProduct_self_star_nonneg (P₀⁻¹ *ᵥ (θ₀ - θ))
  rw [tendsto_pi_nhds]
  intro i
  rw [Metric.tendsto_nhds]
  intro ε hε
  set M := (C + 1) / ε
  have hM : 0 < M := by positivity
  filter_upwards [hexc M] with t ht
  have hbound := rls_error_sq_le hP₀ φ y θ₀ θ t (fun k _ => hy k) hM ht
  set e := (rls φ y θ₀ P₀ t).1 - θ
  have hi : e i * e i ≤ e ⬝ᵥ e :=
    Finset.single_le_sum (f := fun j => e j * e j) (fun j _ => mul_self_nonneg (e j))
      (Finset.mem_univ i)
  have hεM : ε * M = C + 1 := by simp only [M]; field_simp
  have hlt : C / M ^ 2 < ε ^ 2 := by
    rw [div_lt_iff₀ (by positivity)]
    nlinarith
  rw [Real.dist_eq]
  exact abs_lt_of_sq_lt_sq (by simp only [e, Pi.sub_apply] at hi ⊢; nlinarith) hε.le

/-- **Logarithmic bound on the accumulated RLS gains.** For positive definite `P_0`,
`∑_{k<t} φ_kᵀ P_k φ_k / (1 + φ_kᵀ P_k φ_k) ≤ log det (P_0⁻¹ + ∑_{k<t} φ_k φ_kᵀ) - log det P_0⁻¹`,
where `P_k` is the RLS matrix. This is the single-sensor case of inequality (33) of Xie, Zhang and
Guo (IEEE Trans. Automat. Control, DOI 10.1109/TAC.2020.3047989), which follows Lai and Wei: by the
matrix determinant lemma `det P_{k+1}⁻¹ = det P_k⁻¹ (1 + φ_kᵀ P_k φ_k)`, and
`q / (1 + q) ≤ log (1 + q)` for `q ≥ 0`. -/
theorem sum_rls_gain_le_log_det {P₀ : Matrix n n ℝ} (hP₀ : P₀.PosDef) (φ : ℕ → n → ℝ)
    (y : ℕ → ℝ) (θ₀ : n → ℝ) (t : ℕ) :
    ∑ k ∈ Finset.range t, φ k ⬝ᵥ ((rls φ y θ₀ P₀ k).2 *ᵥ φ k) /
        (1 + φ k ⬝ᵥ ((rls φ y θ₀ P₀ k).2 *ᵥ φ k)) ≤
      Real.log (rlsInformation P₀ φ t).det - Real.log P₀⁻¹.det := by
  induction t with
  | zero => simp [rlsInformation]
  | succ t ih =>
    rw [Finset.sum_range_succ]
    have hR := posDef_rlsInformation hP₀ φ t
    have hdetpos : 0 < (rlsInformation P₀ φ t).det := hR.det_pos
    have hP : (rls φ y θ₀ P₀ t).2 = (rlsInformation P₀ φ t)⁻¹ := rls_snd_eq_inv hP₀ φ y θ₀ t
    set q := φ t ⬝ᵥ ((rls φ y θ₀ P₀ t).2 *ᵥ φ t) with hq_def
    have hq : 0 ≤ q := by
      rw [hq_def, hP]; exact hR.inv.posSemidef.dotProduct_mulVec_nonneg (φ t)
    have hdet : (rlsInformation P₀ φ (t + 1)).det = (rlsInformation P₀ φ t).det * (1 + q) := by
      rw [rlsInformation_succ, Matrix.det_add_vecMulVec_of_isUnit_det _ _ _ hdetpos.ne'.isUnit,
        hq_def, hP]
    have hlog : q / (1 + q) ≤ Real.log (1 + q) := by
      have h1 : 0 < 1 + q := by linarith
      have h := Real.log_le_sub_one_of_pos (inv_pos.mpr h1)
      rw [Real.log_inv] at h
      have : (1 + q)⁻¹ - 1 = -(q / (1 + q)) := by field_simp; ring
      linarith
    rw [hdet, Real.log_mul hdetpos.ne' (by positivity)]
    linarith

end MathlibExt.Analysis.Control.RecursiveLeastSquares

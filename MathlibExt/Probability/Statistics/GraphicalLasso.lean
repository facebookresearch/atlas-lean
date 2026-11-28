/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.GaussianGraphicalModel
public import Mathlib.Basic.Real.Sign
public import Mathlib.LinearAlgebra.Matrix.Hadamard
import MathlibExt.Analysis.Matrix.DeterminantDerivative
import MathlibExt.LinearAlgebra.Matrix.LogDetTrace
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Topology.Instances.Matrix

/-!
# The graphical lasso

Let `S` be the empirical covariance matrix of a Gaussian sample with variables indexed by a finite
type `ι` (positive semidefinite, possibly singular). For `ρ > 0` the graphical lasso estimates the
precision matrix `Θ = Σ⁻¹` by

`Θ̂ = argmax_{Θ ≻ 0} {log det Θ - tr (S Θ) - ρ ∑ᵢⱼ |Θᵢⱼ|}`,

the Gaussian log-likelihood `gaussLogLik S Θ = log det Θ - tr (S Θ)` minus an `L¹` penalty: the
problem (1) of Banerjee, El Ghaoui and d'Aspremont and (2.1) of Friedman, Hastie and Tibshirani.
As in the latter's Remark 2.1, each entry may carry its own penalty `Pᵢⱼ`; the constant penalty
matrix `Matrix.of fun _ _ => ρ` is the original problem.

## Main definitions

* `IsGraphicalLassoEstimate P S Θ`: `Θ` is positive definite and maximizes
  `log det Θ' - tr (S Θ') - ∑ᵢⱼ Pᵢⱼ |Θ'ᵢⱼ|` over positive definite `Θ'`.

## Main results

* `existsUnique_isGraphicalLassoEstimate_const`: for `ρ > 0` and positive semidefinite `S` the
  estimate exists and is unique (Banerjee, El Ghaoui and d'Aspremont, Theorem 1);
  `existsUnique_isGraphicalLassoEstimate` allows nonnegative penalties `Pᵢⱼ` with positive
  diagonal.
* `isGraphicalLassoEstimate_const_iff`: **optimality conditions**: for `ρ ≥ 0`, symmetric `S` and
  positive definite `Θ`, `Θ` is the estimate iff `Θ⁻¹ - S - ρ Γ = 0` for some `Γ` with
  `Γᵢⱼ = sign Θᵢⱼ` where `Θᵢⱼ ≠ 0` and `Γᵢⱼ ∈ [-1, 1]` where `Θᵢⱼ = 0`.
  `isGraphicalLassoEstimate_iff` is the same for symmetric nonnegative penalties `P`, with the
  entrywise product `P ⊙ Γ` in place of `ρ Γ`.
* `IsGraphicalLassoEstimate.inv_apply_self_const`: at the estimate, `W = Θ⁻¹` has
  `Wᵢᵢ = Sᵢᵢ + ρ`, with no assumption on `ρ` or `S`; `IsGraphicalLassoEstimate.inv_apply_self`
  gives `Wᵢᵢ = Sᵢᵢ + Pᵢᵢ` for any penalty matrix, so `Wᵢᵢ = Sᵢᵢ` when the diagonal is not
  penalized.

## Implementation notes

The objective is strictly concave: for positive definite `A ≠ B`,
`log det B < log det A + tr (A⁻¹ (B - A))` (`Matrix.PosDef.log_det_mul_le_trace` and its equality
case), which gives uniqueness, and with the subgradient inequality of `|·|` the sufficiency of the
optimality conditions. For existence, a positive definite `Θ` at least as good as `1` has
`tr (S Θ) ≥ 0`, so `log det Θ` is bounded below, while `log det Θ ≤ ∑ᵢ Pᵢᵢ Θᵢᵢ / 2 + c` bounds its
diagonal and hence, by `|Θᵢⱼ| ≤ (Θᵢᵢ + Θⱼⱼ) / 2`, all its entries: such matrices form a compact
set on which the objective is continuous. For necessity, and for the diagonal identities, the
objective is differentiated at the estimate along the symmetric directions `Eₖₗ + Eₗₖ` and `Eₖₖ`,
using `d/dt log det (Θ + t H) = tr (Θ⁻¹ H)` at `t = 0` (`Matrix.hasDerivAt_det_one_add_smul`).

## References

* O. Banerjee, L. El Ghaoui and A. d'Aspremont, *Model selection through sparse maximum likelihood
  estimation for multivariate Gaussian or binary data*, J. Mach. Learn. Res. 9 (2008), 485–516,
  problem (1) and Theorem 1.
* J. Friedman, T. Hastie and R. Tibshirani, *Sparse inverse covariance estimation with the
  graphical lasso*, Biostatistics 9 (2008), 432–441, problem (2.1), equation (2.6), Remarks 2.1
  and 2.2.
-/

@[expose] public section

namespace MathlibExt.Probability.Statistics.GraphicalLasso

open Matrix Real Finset Filter Topology
open MathlibExt.Probability.Statistics.GaussianGraphicalModel (gaussLogLik)

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **The graphical lasso**: `Θ` is the graphical lasso estimate of the precision matrix for the
empirical covariance matrix `S` and the penalty matrix `P` if `Θ` is positive definite and
maximizes the penalized Gaussian log-likelihood

`log det Θ' - tr (S Θ') - ∑ᵢⱼ Pᵢⱼ |Θ'ᵢⱼ|`

(`gaussLogLik S Θ'` minus the penalty) over positive definite `Θ'`. The constant penalty matrix
`Pᵢⱼ = ρ` (`Matrix.of fun _ _ => ρ`) gives the penalty `ρ ∑ᵢⱼ |Θ'ᵢⱼ|`, diagonal included; for
`ρ > 0` and positive semidefinite `S` the estimate exists and is unique
(`existsUnique_isGraphicalLassoEstimate_const`). -/
def IsGraphicalLassoEstimate (P S Θ : Matrix ι ι ℝ) : Prop :=
  Θ.PosDef ∧ ∀ Θ' : Matrix ι ι ℝ, Θ'.PosDef →
    gaussLogLik S Θ' - ∑ i, ∑ j, P i j * |Θ' i j| ≤ gaussLogLik S Θ - ∑ i, ∑ j, P i j * |Θ i j|

/-! ### Strict concavity and uniqueness -/

/-- The objective of `IsGraphicalLassoEstimate`. -/
private noncomputable def obj (P S Θ : Matrix ι ι ℝ) : ℝ :=
  gaussLogLik S Θ - ∑ i, ∑ j, P i j * |Θ i j|

/-- The concavity inequality of `log det` at a positive definite `A`, from
`Matrix.PosDef.log_det_mul_le_trace` applied to `B` and `A⁻¹`. -/
private theorem log_det_le_add_trace {A B : Matrix ι ι ℝ} (hA : A.PosDef) (hB : B.PosDef) :
    log B.det ≤ log A.det + (A⁻¹ * (B - A)).trace := by
  have h := hB.log_det_mul_le_trace hA.inv
  have hAu : IsUnit A.det := isUnit_iff_ne_zero.2 hA.det_pos.ne'
  rw [det_nonsing_inv, Ring.inverse_eq_inv, log_mul hB.det_pos.ne' (inv_ne_zero hA.det_pos.ne'),
    log_inv, trace_mul_comm] at h
  rw [Matrix.mul_sub, nonsing_inv_mul _ hAu, trace_sub, trace_one]
  linarith

/-- The equality case of `log_det_le_add_trace`. -/
private theorem eq_of_log_det_eq_add_trace {A B : Matrix ι ι ℝ} (hA : A.PosDef) (hB : B.PosDef)
    (heq : log B.det = log A.det + (A⁻¹ * (B - A)).trace) : B = A := by
  have hAu : IsUnit A.det := isUnit_iff_ne_zero.2 hA.det_pos.ne'
  have h : log (B.det * A⁻¹.det) = (B * A⁻¹).trace - Fintype.card ι := by
    rw [det_nonsing_inv, Ring.inverse_eq_inv, log_mul hB.det_pos.ne' (inv_ne_zero hA.det_pos.ne'),
      log_inv, trace_mul_comm]
    rw [Matrix.mul_sub, nonsing_inv_mul _ hAu, trace_sub, trace_one] at heq
    linarith
  have hmul : A⁻¹ * B = 1 := hB.mul_eq_one_of_log_det_eq_trace hA.inv h
  calc B = A * (A⁻¹ * B) := by rw [← Matrix.mul_assoc, mul_nonsing_inv _ hAu, Matrix.one_mul]
    _ = A := by rw [hmul, Matrix.mul_one]

/-- Strict midpoint concavity of the objective on positive definite matrices. -/
private theorem obj_midpoint {P S A B : Matrix ι ι ℝ} (hP : ∀ i j, 0 ≤ P i j) (hA : A.PosDef)
    (hB : B.PosDef) (hne : A ≠ B) :
    obj P S A + obj P S B < 2 * obj P S ((1 / 2 : ℝ) • (A + B)) := by
  set M : Matrix ι ι ℝ := (1 / 2 : ℝ) • (A + B) with hMdef
  have hM : M.PosDef := (hA.add hB).smul (by norm_num)
  have hAM : A ≠ M := by
    intro h
    apply hne
    rw [show B = (2 : ℝ) • M - A by rw [hMdef]; module, ← h]
    module
  have h1 : log A.det < log M.det + (M⁻¹ * (A - M)).trace :=
    lt_of_le_of_ne (log_det_le_add_trace hM hA) fun h => hAM (eq_of_log_det_eq_add_trace hM hA h)
  have h2 := log_det_le_add_trace hM hB
  have htr : (M⁻¹ * (A - M)).trace + (M⁻¹ * (B - M)).trace = 0 := by
    rw [← trace_add, ← Matrix.mul_add]
    have : A - M + (B - M) = 0 := by rw [hMdef]; module
    rw [this, Matrix.mul_zero, trace_zero]
  have hS : (S * M).trace = ((S * A).trace + (S * B).trace) / 2 := by
    rw [hMdef, Matrix.mul_smul, Matrix.mul_add, trace_smul, trace_add, smul_eq_mul]
    ring
  have hpen : 2 * ∑ i, ∑ j, P i j * |M i j| ≤
      ∑ i, ∑ j, P i j * |A i j| + ∑ i, ∑ j, P i j * |B i j| := by
    rw [mul_sum, ← sum_add_distrib]
    refine sum_le_sum fun i _ => ?_
    rw [mul_sum, ← sum_add_distrib]
    refine sum_le_sum fun j _ => ?_
    have : |M i j| ≤ (|A i j| + |B i j|) / 2 := by
      rw [hMdef, Matrix.smul_apply, Matrix.add_apply, smul_eq_mul, abs_mul,
        abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
      linarith [abs_add_le (A i j) (B i j)]
    nlinarith [hP i j]
  unfold obj gaussLogLik
  linarith

private theorem eq_of_isGraphicalLassoEstimate {P S Θ₁ Θ₂ : Matrix ι ι ℝ} (hP : ∀ i j, 0 ≤ P i j)
    (h₁ : IsGraphicalLassoEstimate P S Θ₁) (h₂ : IsGraphicalLassoEstimate P S Θ₂) : Θ₁ = Θ₂ := by
  by_contra hne
  have hM : ((1 / 2 : ℝ) • (Θ₁ + Θ₂)).PosDef := (h₁.1.add h₂.1).smul (by norm_num)
  have h := obj_midpoint (S := S) hP h₁.1 h₂.1 hne
  have a : obj P S _ ≤ obj P S Θ₁ := h₁.2 _ hM
  have b : obj P S _ ≤ obj P S Θ₂ := h₂.2 _ hM
  linarith

/-! ### Existence -/

omit [DecidableEq ι] in
open scoped MatrixOrder in
/-- `tr (S Θ) ≥ 0` for positive semidefinite `S` and `Θ`: with `R = √Θ`, `tr (S Θ) = tr (R S R)`. -/
private theorem trace_mul_nonneg {S Θ : Matrix ι ι ℝ} (hS : S.PosSemidef) (hΘ : Θ.PosSemidef) :
    0 ≤ (S * Θ).trace := by
  classical
  set R := CFC.sqrt Θ
  have hR : R.PosSemidef := nonneg_iff_posSemidef.1 (CFC.sqrt_nonneg Θ)
  have hRR : R * R = Θ := CFC.sqrt_mul_sqrt_self Θ (nonneg_iff_posSemidef.2 hΘ)
  have h : (S * Θ).trace = (Rᴴ * S * R).trace := by
    rw [hR.1.eq, ← hRR, ← Matrix.mul_assoc, trace_mul_comm, Matrix.mul_assoc]
  rw [h]
  exact (hS.conjTranspose_mul_mul_same R).trace_nonneg

omit [Fintype ι] [DecidableEq ι] in
/-- The entries of a positive semidefinite matrix are bounded by its diagonal:
`|Θᵢⱼ| ≤ (Θᵢᵢ + Θⱼⱼ) / 2`, from the quadratic form at `eᵢ ± eⱼ`. -/
private theorem abs_apply_le [Finite ι] {Θ : Matrix ι ι ℝ} (hΘ : Θ.PosSemidef) (i j : ι) :
    |Θ i j| ≤ (Θ i i + Θ j j) / 2 := by
  have := Fintype.ofFinite ι
  classical
  have hsym : Θ j i = Θ i j := by simpa using hΘ.1.apply i j
  have key : ∀ s : ℝ, 0 ≤ Θ i i + 2 * s * Θ i j + s ^ 2 * Θ j j := fun s => by
    have := hΘ.dotProduct_mulVec_nonneg (Pi.single i 1 + s • Pi.single j 1)
    simp only [star_trivial, mulVec_add, mulVec_smul, add_dotProduct, dotProduct_add,
      smul_dotProduct, dotProduct_smul, single_dotProduct, mulVec_single_one, smul_eq_mul,
      one_mul, col_apply] at this
    rw [hsym] at this
    nlinarith [this]
  have h1 := key 1
  have h2 := key (-1)
  rw [abs_le]
  constructor <;> nlinarith

/-- A positive definite `Θ` whose objective is at least `c` has `exp c ≤ det Θ` and entries bounded
by a constant depending only on `c`, `P` and the dimension. -/
private theorem bound_of_le_obj {P S : Matrix ι ι ℝ} (hP : ∀ i j, 0 ≤ P i j) (hPd : ∀ i, 0 < P i i)
    (hS : S.PosSemidef) (c : ℝ) :
    ∃ R : ℝ, 1 ≤ R ∧ ∀ Θ : Matrix ι ι ℝ, Θ.PosDef → c ≤ obj P S Θ →
      exp c ≤ Θ.det ∧ ∀ i j, |Θ i j| ≤ R := by
  set C : ℝ := -c - Fintype.card ι - ∑ i, log (P i i / 2)
  refine ⟨1 + ∑ k, |2 * C / P k k|, le_add_of_nonneg_right (sum_nonneg fun _ _ => abs_nonneg _),
    fun Θ hΘ hc => ?_⟩
  have htr := trace_mul_nonneg hS hΘ.posSemidef
  have hdiag : ∀ i, 0 ≤ Θ i i := fun i => hΘ.diag_pos.le
  have hpen : ∑ i, P i i * Θ i i ≤ ∑ i, ∑ j, P i j * |Θ i j| := by
    refine sum_le_sum fun i _ => ?_
    rw [← abs_of_nonneg (hdiag i)]
    exact single_le_sum (f := fun j => P i j * |Θ i j|) (fun j _ => mul_nonneg (hP i j)
      (abs_nonneg _)) (mem_univ i)
  have hlog : c + ∑ i, P i i * Θ i i ≤ log Θ.det := by
    unfold obj gaussLogLik at hc
    linarith
  refine ⟨?_, ?_⟩
  · rw [← exp_log hΘ.det_pos]
    refine exp_le_exp.2 ?_
    have : 0 ≤ ∑ i, P i i * Θ i i := sum_nonneg fun i _ => mul_nonneg (hP i i) (hdiag i)
    linarith
  -- upper bound on `log det Θ` from the log-determinant trace inequality
  have hD : (diagonal fun i => P i i / 2).PosDef :=
    posDef_diagonal_iff.2 fun i => by linarith [hPd i]
  have hup := hΘ.log_det_mul_le_trace hD
  rw [det_diagonal, log_mul hΘ.det_pos.ne' (prod_ne_zero_iff.2 fun i _ => by linarith [hPd i]),
    log_prod fun i _ => by linarith [hPd i]] at hup
  have htrD : (Θ * diagonal fun i => P i i / 2).trace = (∑ i, P i i * Θ i i) / 2 := by
    simp only [trace, diag_apply, mul_diagonal, sum_div]
    exact sum_congr rfl fun i _ => by ring
  rw [htrD] at hup
  have hsum : ∑ i, P i i * Θ i i ≤ 2 * C := by
    simp only [C]
    linarith
  have hkk : ∀ k, Θ k k ≤ ∑ k, |2 * C / P k k| := fun k => by
    have hk : P k k * Θ k k ≤ 2 * C :=
      (single_le_sum (f := fun i => P i i * Θ i i) (fun i _ => mul_nonneg (hP i i) (hdiag i))
        (mem_univ k)).trans hsum
    calc Θ k k ≤ 2 * C / P k k := by
          rw [le_div_iff₀ (hPd k)]
          linarith
      _ ≤ |2 * C / P k k| := le_abs_self _
      _ ≤ _ := single_le_sum (f := fun k => |2 * C / P k k|) (fun _ _ => abs_nonneg _)
          (mem_univ k)
  intro i j
  have := abs_apply_le hΘ.posSemidef i j
  linarith [hkk i, hkk j]

private theorem exists_isGraphicalLassoEstimate {P S : Matrix ι ι ℝ} (hP : ∀ i j, 0 ≤ P i j)
    (hPd : ∀ i, 0 < P i i) (hS : S.PosSemidef) : ∃ Θ, IsGraphicalLassoEstimate P S Θ := by
  set c := obj P S 1
  obtain ⟨R, hR1, hR⟩ := bound_of_le_obj hP hPd hS c
  set K : Set (Matrix ι ι ℝ) := {Θ | Θ.PosSemidef ∧ exp c ≤ Θ.det ∧ ∀ i j, |Θ i j| ≤ R}
  have hKclosed : IsClosed K := by
    simp only [K, Set.ofPred_and, Set.ofPred_forall]
    exact isClosed_setOfPred_posSemidef.inter ((isClosed_le continuous_const
      continuous_id.matrix_det).inter (isClosed_iInter fun i => isClosed_iInter fun j =>
        isClosed_le (continuous_id.matrix_elem i j).abs continuous_const))
  have hKbox : K ⊆ Set.univ.pi fun _ : ι => Set.univ.pi fun _ : ι => Set.Icc (-R) R :=
    fun Θ hΘ i _ j _ => abs_le.1 (hΘ.2.2 i j)
  have hK : IsCompact K :=
    (isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_Icc).of_isClosed_subset
      hKclosed hKbox
  have hc0 : c ≤ 0 := by
    have hpen : 0 ≤ ∑ i, ∑ j, P i j * |(1 : Matrix ι ι ℝ) i j| :=
      sum_nonneg fun i _ => sum_nonneg fun j _ => mul_nonneg (hP i j) (abs_nonneg _)
    simp only [c, obj, gaussLogLik, det_one, log_one, Matrix.mul_one]
    linarith [hS.trace_nonneg]
  have h1K : (1 : Matrix ι ι ℝ) ∈ K := by
    refine ⟨PosSemidef.one, by rw [det_one]; exact exp_le_one_iff.2 hc0, fun i j => ?_⟩
    rw [Matrix.one_apply]
    split_ifs <;> simp [hR1, (zero_le_one.trans hR1)]
  have hcont : ContinuousOn (obj P S) K := by
    have hlog : ContinuousOn (fun Θ : Matrix ι ι ℝ => log Θ.det) K :=
      continuous_id.matrix_det.continuousOn.log fun Θ hΘ =>
        (lt_of_lt_of_le (exp_pos c) hΘ.2.1).ne'
    have hrest : Continuous fun Θ : Matrix ι ι ℝ =>
        (S * Θ).trace + ∑ i, ∑ j, P i j * |Θ i j| :=
      (continuous_const.matrix_mul continuous_id).matrix_trace.add
        (continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ =>
          continuous_const.mul (continuous_id.matrix_elem i j).abs)
    refine (hlog.sub hrest.continuousOn).congr fun Θ _ => ?_
    simp only [obj, gaussLogLik, Pi.sub_apply]
    ring
  obtain ⟨Θ₀, hΘ₀K, hmax⟩ := hK.exists_isMaxOn ⟨1, h1K⟩ hcont
  have hΘ₀ : Θ₀.PosDef := hΘ₀K.1.posDef_iff_det_ne_zero.2
    (lt_of_lt_of_le (exp_pos c) hΘ₀K.2.1).ne'
  refine ⟨Θ₀, hΘ₀, fun Θ hΘ => ?_⟩
  change obj P S Θ ≤ obj P S Θ₀
  by_cases hc : c ≤ obj P S Θ
  · obtain ⟨h1, h2⟩ := hR Θ hΘ hc
    exact hmax ⟨hΘ.posSemidef, h1, h2⟩
  · exact (not_le.1 hc).le.trans (hmax h1K)

/-! ### First-order optimality conditions -/

omit [Fintype ι] [DecidableEq ι] in
open scoped MatrixOrder in
/-- A positive definite matrix stays positive definite under small symmetric perturbations:
`r ≤ A` and `-C ≤ H ≤ C` in the Loewner order give `A + t H ≥ r - |t| C`. -/
private theorem eventually_posDef_add_smul [Finite ι] {A H : Matrix ι ι ℝ} (hA : A.PosDef)
    (hH : H.IsHermitian) : ∀ᶠ t in 𝓝 (0 : ℝ), (A + t • H).PosDef := by
  have := Fintype.ofFinite ι
  classical
  rcases isEmpty_or_nonempty ι with hι | hι
  · exact Eventually.of_forall fun t => (Subsingleton.elim A (A + t • H)) ▸ hA
  have hAsa : IsSelfAdjoint A := isHermitian_iff_isSelfAdjoint.1 hA.1
  have hHsa : IsSelfAdjoint H := isHermitian_iff_isSelfAdjoint.1 hH
  obtain ⟨r, hr, hrA⟩ := (CFC.exists_pos_algebraMap_le_iff A hAsa).2 fun x hx =>
    hA.isStrictlyPositive.spectrum_pos hx
  set C := ∑ i, |hH.eigenvalues i|
  have hC : ∀ x ∈ spectrum ℝ H, |x| ≤ C := by
    intro x hx
    rw [hH.spectrum_real_eq_range_eigenvalues] at hx
    obtain ⟨k, rfl⟩ := hx
    exact single_le_sum (f := fun i => |hH.eigenvalues i|) (fun _ _ => abs_nonneg _) (mem_univ k)
  have hC0 : 0 ≤ C := sum_nonneg fun _ _ => abs_nonneg _
  have hlo : (H - (-C) • (1 : Matrix ι ι ℝ)).PosSemidef := by
    have := (algebraMap_le_iff_le_spectrum (r := -C) (a := H) hHsa).2 fun x hx =>
      neg_le_of_abs_le (hC x hx)
    rwa [Algebra.algebraMap_eq_smul_one, le_iff] at this
  have hhi : (C • (1 : Matrix ι ι ℝ) - H).PosSemidef := by
    have := (le_algebraMap_iff_spectrum_le (r := C) (a := H) hHsa).2 fun x hx =>
      le_of_abs_le (hC x hx)
    rwa [Algebra.algebraMap_eq_smul_one, le_iff] at this
  have hrA' : (A - r • (1 : Matrix ι ι ℝ)).PosSemidef := by
    rwa [Algebra.algebraMap_eq_smul_one, le_iff] at hrA
  have hδ : 0 < r / (C + 1) := div_pos hr (by linarith)
  filter_upwards [Ioo_mem_nhds (neg_neg_of_pos hδ) hδ] with t ht
  have htC : |t| * C < r := by
    have h1 : |t| < r / (C + 1) := abs_lt.2 ⟨ht.1, ht.2⟩
    rw [lt_div_iff₀ (by linarith)] at h1
    nlinarith [abs_nonneg t]
  rcases le_or_gt 0 t with ht0 | ht0
  · rw [abs_of_nonneg ht0] at htC
    have h : A + t • H = (A - r • 1) + t • (H - (-C) • 1) + (r - t * C) • 1 := by module
    rw [h]
    exact PosDef.posSemidef_add (hrA'.add (hlo.smul ht0)) (PosDef.one.smul (by linarith))
  · rw [abs_of_neg ht0] at htC
    have h : A + t • H = (A - r • 1) + (-t) • (C • 1 - H) + (r + t * C) • 1 := by module
    rw [h]
    exact PosDef.posSemidef_add (hrA'.add (hhi.smul (a := -t) (by linarith)))
      (PosDef.one.smul (by linarith))

/-- The derivative of `t ↦ log det (Θ + t H) - tr (S (Θ + t H))` at `0` is
`tr (Θ⁻¹ H) - tr (S H)`. -/
private theorem hasDerivAt_gaussLogLik {S Θ H : Matrix ι ι ℝ} (hΘ : Θ.PosDef) :
    HasDerivAt (fun t : ℝ => gaussLogLik S (Θ + t • H))
      ((Θ⁻¹ * H).trace - (S * H).trace) 0 := by
  have hu : IsUnit Θ.det := isUnit_iff_ne_zero.2 hΘ.det_pos.ne'
  have hfun : (fun t : ℝ => (Θ + t • H).det) = fun t => Θ.det * (1 + t • (Θ⁻¹ * H)).det := by
    funext t
    rw [← det_mul, Matrix.mul_add, Matrix.mul_one, Matrix.mul_smul, ← Matrix.mul_assoc,
      mul_nonsing_inv _ hu, Matrix.one_mul]
  have hdet : HasDerivAt (fun t : ℝ => (Θ + t • H).det) (Θ.det * (Θ⁻¹ * H).trace) 0 := by
    rw [hfun]
    exact (Matrix.hasDerivAt_det_one_add_smul _).const_mul _
  have h0 : (Θ + (0 : ℝ) • H).det ≠ 0 := by simpa using hΘ.det_pos.ne'
  have htr : HasDerivAt (fun t : ℝ => (S * (Θ + t • H)).trace) (S * H).trace 0 := by
    have : (fun t : ℝ => (S * (Θ + t • H)).trace) = fun t => (S * Θ).trace + t * (S * H).trace := by
      funext t
      rw [Matrix.mul_add, Matrix.mul_smul, trace_add, trace_smul, smul_eq_mul]
    rw [this]
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (S * H).trace).const_add (S * Θ).trace
  convert (hdet.log h0).sub htr using 1
  · funext t
    simp only [gaussLogLik, Pi.sub_apply]
  · rw [zero_smul, add_zero]
    field_simp [hΘ.det_pos.ne']

/-- If `h t ≤ h 0 + t c` for small `t > 0`, then `h' 0 ≤ c`. -/
private theorem le_of_hasDerivAt_of_eventually_le {h : ℝ → ℝ} {d c : ℝ} (hd : HasDerivAt h d 0)
    (hle : ∀ᶠ t in 𝓝[>] 0, h t ≤ h 0 + t * c) : d ≤ c := by
  refine le_of_tendsto hd.tendsto_slope_zero_right ?_
  filter_upwards [hle, self_mem_nhdsWithin] with t ht hpos
  rw [zero_add, smul_eq_mul, inv_mul_le_iff₀ hpos]
  linarith

/-- The one-sided derivative of `t ↦ |a + t h|` at `0⁺`. -/
private noncomputable def dirAbs (a h : ℝ) : ℝ := if a = 0 then |h| else Real.sign a * h

private theorem eventually_abs_add_mul (a h : ℝ) :
    ∀ᶠ t in 𝓝[>] (0 : ℝ), |a + t * h| = |a| + t * dirAbs a h := by
  have hc : Tendsto (fun t : ℝ => a + t * h) (𝓝 0) (𝓝 a) := by
    simpa using ((continuous_id.mul continuous_const).const_add a).tendsto (0 : ℝ)
  rcases lt_trichotomy a 0 with ha | rfl | ha
  · filter_upwards [nhdsWithin_le_nhds (hc.eventually_lt_const ha)] with t ht
    simp only [abs_of_neg ht, abs_of_neg ha, dirAbs, ha.ne, ↓reduceIte, Real.sign_of_neg ha]
    ring
  · filter_upwards [self_mem_nhdsWithin] with t ht
    simp only [dirAbs, ↓reduceIte, zero_add, abs_zero, abs_mul, abs_of_pos ht]
  · filter_upwards [nhdsWithin_le_nhds (hc.eventually_const_lt ha)] with t ht
    simp only [abs_of_pos ht, abs_of_pos ha, dirAbs, ha.ne', ↓reduceIte, Real.sign_of_pos ha]
    ring

omit [DecidableEq ι] in
/-- The penalty is affine in `t` along `Θ + t H` for small `t > 0`. -/
private theorem eventually_penalty (P Θ H : Matrix ι ι ℝ) :
    ∀ᶠ t in 𝓝[>] (0 : ℝ), ∑ i, ∑ j, P i j * |(Θ + t • H) i j| =
      ∑ i, ∑ j, P i j * |Θ i j| + t * ∑ i, ∑ j, P i j * dirAbs (Θ i j) (H i j) := by
  have : ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ i j,
      |Θ i j + t * H i j| = |Θ i j| + t * dirAbs (Θ i j) (H i j) := by
    rw [eventually_all]
    exact fun i => eventually_all.2 fun j => eventually_abs_add_mul _ _
  filter_upwards [this] with t ht
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, ht, mul_sum, ← sum_add_distrib]
  exact sum_congr rfl fun i _ => sum_congr rfl fun j _ => by ring

/-- At a graphical lasso estimate, the one-sided directional derivative of the objective along
any symmetric direction is nonpositive. -/
private theorem trace_sub_le {P S Θ H : Matrix ι ι ℝ} (hest : IsGraphicalLassoEstimate P S Θ)
    (hH : H.IsHermitian) :
    (Θ⁻¹ * H).trace - (S * H).trace ≤ ∑ i, ∑ j, P i j * dirAbs (Θ i j) (H i j) := by
  apply le_of_hasDerivAt_of_eventually_le
    (hasDerivAt_gaussLogLik (S := S) (H := H) hest.1)
  filter_upwards [nhdsWithin_le_nhds (eventually_posDef_add_smul hest.1 hH),
    eventually_penalty P Θ H] with t ht hpen
  have := hest.2 _ ht
  rw [hpen] at this
  simp only [zero_smul, add_zero]
  linarith

/-- The diagonal consequence of `trace_sub_le`, along the directions `±Eₖₖ`: since `Θₖₖ > 0`, the
penalty changes by `±t Pₖₖ`, so `(Θ⁻¹)ₖₖ - Sₖₖ = Pₖₖ`. -/
private theorem inv_apply_self_eq {P S Θ : Matrix ι ι ℝ} (hest : IsGraphicalLassoEstimate P S Θ)
    (k : ι) : Θ⁻¹ k k = S k k + P k k := by
  have hpos : 0 < Θ k k := hest.1.diag_pos
  have key : ∀ s : ℝ, s * (Θ⁻¹ k k - S k k) ≤ s * P k k := fun s => by
    have h := trace_sub_le hest (isHermitian_diagonal (Pi.single k s))
    have hdiag : ∀ i j, diagonal (Pi.single k s) i j = if i = k ∧ j = k then s else 0 :=
      fun i j => by
        by_cases hij : i = j
        · subst hij
          by_cases hi : i = k
          · simp [hi]
          · simp [hi]
        · have : ¬ (i = k ∧ j = k) := fun h => hij (h.1.trans h.2.symm)
          simp [diagonal_apply_ne _ hij, this]
    have htr : ∀ M : Matrix ι ι ℝ, (M * diagonal (Pi.single k s)).trace = M k k * s := fun M => by
      simp only [trace, diag_apply, mul_diagonal]
      rw [sum_eq_single k (fun i _ hi => by simp [hi]) (by simp)]
      simp
    have hpen : ∑ i, ∑ j, P i j * dirAbs (Θ i j) (diagonal (Pi.single k s) i j) = P k k * s := by
      rw [sum_eq_single k, sum_eq_single k]
      · simp only [hdiag, and_self, ↓reduceIte, dirAbs, hpos.ne', Real.sign_of_pos hpos, one_mul]
      · intro j _ hj
        simp [hdiag, hj, dirAbs]
      · simp
      · intro i _ hi
        exact sum_eq_zero fun j _ => by simp [hdiag, hi, dirAbs]
      · simp
    rw [htr, htr, hpen] at h
    linarith
  have h₁ := key 1
  have h₂ := key (-1)
  linarith

/-- The entrywise consequence of `trace_sub_le`, along the symmetric direction `s (Eₖₗ + Eₗₖ)`
(`s Eₖₖ` when `k = l`). -/
private theorem mul_apply_le {P S Θ : Matrix ι ι ℝ} (hP : P.IsSymm) (hS : S.IsSymm)
    (hest : IsGraphicalLassoEstimate P S Θ) (k l : ι) (s : ℝ) :
    s * (Θ⁻¹ - S) k l ≤ P k l * dirAbs (Θ k l) s := by
  set D := Θ⁻¹ - S with hDdef
  have hΘs : ∀ i j, Θ j i = Θ i j := fun i j => by simpa using hest.1.1.apply i j
  have hD : ∀ i j, D j i = D i j := fun i j => by
    have h1 : Θ⁻¹ j i = Θ⁻¹ i j := by simpa using hest.1.inv.1.apply i j
    simp only [hDdef, Matrix.sub_apply, h1, hS.apply i j]
  have hPs : ∀ i j, P j i = P i j := fun i j => hP.apply i j
  let supp : ι → ι → Prop := fun i j => (i = k ∧ j = l) ∨ (i = l ∧ j = k)
  have hsupp : ∀ i j, supp j i ↔ supp i j := fun i j => by
    simp only [supp]
    tauto
  let H : Matrix ι ι ℝ := of fun i j => if supp i j then s else 0
  have hH : H.IsHermitian := by
    ext i j
    simp only [H, conjTranspose_apply, of_apply, star_trivial, hsupp]
  have h := trace_sub_le hest hH
  set g := s * D k l - P k l * dirAbs (Θ k l) s
  have hterm : ∀ i j, D i j * H j i - P i j * dirAbs (Θ i j) (H i j) =
      if supp i j then g else 0 := fun i j => by
    by_cases hij : supp i j
    · have hji : supp j i := (hsupp i j).2 hij
      simp only [H, of_apply, hij, hji, ↓reduceIte, g]
      rcases hij with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · ring
      · rw [hD, hPs, hΘs]
        ring
    · have hji : ¬ supp j i := fun h => hij ((hsupp i j).1 h)
      simp only [H, of_apply, hij, hji, ↓reduceIte, dirAbs, abs_zero, mul_zero, ite_self,
        sub_zero]
  have hsum : (Θ⁻¹ * H).trace - (S * H).trace - ∑ i, ∑ j, P i j * dirAbs (Θ i j) (H i j) =
      ∑ i, ∑ j, if supp i j then g else 0 := by
    rw [← trace_sub, ← Matrix.sub_mul]
    simp only [trace, diag_apply, Matrix.mul_apply, ← sum_sub_distrib, ← hDdef]
    exact sum_congr rfl fun i _ => sum_congr rfl fun j _ => hterm i j
  by_contra hlt
  have hg : 0 < g := by simp only [g]; linarith
  have hnonneg : ∀ i j, 0 ≤ if supp i j then g else 0 := fun i j => by
    split_ifs
    exacts [hg.le, le_rfl]
  have hpos : 0 < ∑ i, ∑ j, if supp i j then g else 0 := by
    have hkl : supp k l := Or.inl ⟨rfl, rfl⟩
    calc (0 : ℝ) < if supp k l then g else 0 := by simp only [hkl, ↓reduceIte, hg]
      _ ≤ ∑ j, if supp k j then g else 0 :=
          single_le_sum (f := fun j => if supp k j then g else 0) (fun j _ => hnonneg k j)
            (mem_univ l)
      _ ≤ _ := single_le_sum (f := fun i => ∑ j, if supp i j then g else 0)
          (fun i _ => sum_nonneg fun j _ => hnonneg i j) (mem_univ k)
  linarith

/-- Necessity of the optimality conditions. -/
private theorem exists_subgradient {P S Θ : Matrix ι ι ℝ} (hP0 : ∀ i j, 0 ≤ P i j)
    (hP : P.IsSymm) (hS : S.IsSymm) (hest : IsGraphicalLassoEstimate P S Θ) :
    ∃ Γ : Matrix ι ι ℝ, (∀ i j, Θ i j ≠ 0 → Γ i j = Real.sign (Θ i j)) ∧
      (∀ i j, Θ i j = 0 → Γ i j ∈ Set.Icc (-1) 1) ∧ Θ⁻¹ - S - P ⊙ Γ = 0 := by
  set D := Θ⁻¹ - S with hDdef
  have h1 := fun k l => mul_apply_le hP hS hest k l 1
  have h2 := fun k l => mul_apply_le hP hS hest k l (-1)
  refine ⟨of fun i j => if Θ i j = 0 then (if P i j = 0 then 0 else D i j / P i j)
    else Real.sign (Θ i j), fun i j h => by simp [h], fun i j h => ?_, ?_⟩
  · have a := h1 i j
    have b := h2 i j
    simp only [dirAbs, h, ↓reduceIte, abs_one, abs_neg, mul_one, one_mul, neg_mul] at a b
    simp only [of_apply, h, ↓reduceIte]
    split_ifs with hp
    · simp
    · have hpos : 0 < P i j := lt_of_le_of_ne (hP0 i j) (Ne.symm hp)
      rw [Set.mem_Icc, le_div_iff₀ hpos, div_le_iff₀ hpos]
      constructor <;> linarith
  · ext i j
    have a := h1 i j
    have b := h2 i j
    simp only [Matrix.sub_apply, hadamard_apply, of_apply, Matrix.zero_apply]
    by_cases h : Θ i j = 0
    · simp only [dirAbs, h, ↓reduceIte, abs_one, abs_neg, mul_one, one_mul, neg_mul] at a b
      simp only [h, ↓reduceIte]
      split_ifs with hp
      · rw [hp] at a b
        linarith
      · field_simp
        ring
    · simp only [dirAbs, h, ↓reduceIte, mul_one, one_mul, mul_neg, neg_mul] at a b
      simp only [h, ↓reduceIte]
      linarith

/-- Sufficiency of the optimality conditions. -/
private theorem of_subgradient {P S Θ Γ : Matrix ι ι ℝ} (hP0 : ∀ i j, 0 ≤ P i j)
    (hΘ : Θ.PosDef) (hsign : ∀ i j, Θ i j ≠ 0 → Γ i j = Real.sign (Θ i j))
    (hbox : ∀ i j, Θ i j = 0 → Γ i j ∈ Set.Icc (-1) 1) (hkkt : Θ⁻¹ - S - P ⊙ Γ = 0) :
    IsGraphicalLassoEstimate P S Θ := by
  refine ⟨hΘ, fun Θ' hΘ' => ?_⟩
  have hgrad := log_det_le_add_trace hΘ hΘ'
  have hW : Θ⁻¹ = S + P ⊙ Γ := by
    rw [← sub_eq_zero, ← hkkt]
    abel
  have hΘs : ∀ i j, Θ j i = Θ i j := fun i j => by simpa using hΘ.1.apply i j
  have hΘ's : ∀ i j, Θ' j i = Θ' i j := fun i j => by simpa using hΘ'.1.apply i j
  have htr : (Θ⁻¹ * (Θ' - Θ)).trace = (S * Θ').trace - (S * Θ).trace +
      (∑ i, ∑ j, P i j * (Γ i j * Θ' i j) - ∑ i, ∑ j, P i j * (Γ i j * Θ i j)) := by
    rw [hW, Matrix.add_mul, trace_add, Matrix.mul_sub, trace_sub]
    congr 1
    simp only [trace, diag_apply, Matrix.mul_apply, hadamard_apply, Matrix.sub_apply, hΘs,
      hΘ's, ← sum_sub_distrib]
    exact sum_congr rfl fun i _ => sum_congr rfl fun j _ => by ring
  have hΓ1 : ∀ i j, |Γ i j| ≤ 1 := fun i j => by
    by_cases h : Θ i j = 0
    · exact abs_le.2 (hbox i j h)
    · rw [hsign i j h]
      rcases lt_or_gt_of_ne h with h' | h'
      · simp [Real.sign_of_neg h']
      · simp [Real.sign_of_pos h']
  have hΘpen : ∑ i, ∑ j, P i j * (Γ i j * Θ i j) = ∑ i, ∑ j, P i j * |Θ i j| := by
    refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
    congr 1
    by_cases h : Θ i j = 0
    · simp [h]
    · rw [hsign i j h]
      rcases lt_or_gt_of_ne h with h' | h'
      · rw [Real.sign_of_neg h', abs_of_neg h']
        ring
      · rw [Real.sign_of_pos h', abs_of_pos h']
        ring
  have hΘ'pen : ∑ i, ∑ j, P i j * (Γ i j * Θ' i j) ≤ ∑ i, ∑ j, P i j * |Θ' i j| := by
    refine sum_le_sum fun i _ => sum_le_sum fun j _ => ?_
    refine mul_le_mul_of_nonneg_left ?_ (hP0 i j)
    calc Γ i j * Θ' i j ≤ |Γ i j * Θ' i j| := le_abs_self _
      _ = |Γ i j| * |Θ' i j| := abs_mul _ _
      _ ≤ 1 * |Θ' i j| := mul_le_mul_of_nonneg_right (hΓ1 i j) (abs_nonneg _)
      _ = |Θ' i j| := one_mul _
  unfold gaussLogLik
  linarith

/-! ### Main results -/

/-- **Existence and uniqueness of the weighted graphical lasso estimate**: for a penalty matrix
`P` with nonnegative entries and positive diagonal and a positive semidefinite `S`, there is exactly
one positive definite `Θ` maximizing `log det Θ - tr (S Θ) - ∑ᵢⱼ Pᵢⱼ |Θᵢⱼ|` over positive definite
matrices. This extends Theorem 1 of Banerjee, El Ghaoui and d'Aspremont, the case of a constant
penalty (`existsUnique_isGraphicalLassoEstimate_const`). -/
theorem existsUnique_isGraphicalLassoEstimate {P S : Matrix ι ι ℝ} (hP : ∀ i j, 0 ≤ P i j)
    (hPd : ∀ i, 0 < P i i) (hS : S.PosSemidef) : ∃! Θ, IsGraphicalLassoEstimate P S Θ := by
  obtain ⟨Θ, hΘ⟩ := exists_isGraphicalLassoEstimate hP hPd hS
  exact ⟨Θ, hΘ, fun Θ' hΘ' => eq_of_isGraphicalLassoEstimate hP hΘ' hΘ⟩

/-- **Optimality conditions for the weighted graphical lasso** (Friedman, Hastie and Tibshirani,
equation (2.6) and Remark 2.1): let the penalty matrix `P` be symmetric with nonnegative entries
and `S` be symmetric. A positive definite `Θ` is the estimate iff, with `W = Θ⁻¹`,
`W - S - P ⊙ Γ = 0` for some `Γ` with `Γᵢⱼ = sign Θᵢⱼ` where `Θᵢⱼ ≠ 0` and `Γᵢⱼ ∈ [-1, 1]` where
`Θᵢⱼ = 0`. -/
theorem isGraphicalLassoEstimate_iff {P S Θ : Matrix ι ι ℝ} (hP0 : ∀ i j, 0 ≤ P i j)
    (hP : P.IsSymm) (hS : S.IsSymm) (hΘ : Θ.PosDef) :
    IsGraphicalLassoEstimate P S Θ ↔ ∃ Γ : Matrix ι ι ℝ,
      (∀ i j, Θ i j ≠ 0 → Γ i j = Real.sign (Θ i j)) ∧
      (∀ i j, Θ i j = 0 → Γ i j ∈ Set.Icc (-1) 1) ∧ Θ⁻¹ - S - P ⊙ Γ = 0 :=
  ⟨exists_subgradient hP0 hP hS, fun ⟨_, h₁, h₂, h₃⟩ => of_subgradient hP0 hΘ h₁ h₂ h₃⟩

/-- **The diagonal of the weighted graphical lasso covariance estimate**: the estimate `Θ` has
`(Θ⁻¹)ᵢᵢ = Sᵢᵢ + Pᵢᵢ` for every `i`, since `Θᵢᵢ > 0`. In particular `(Θ⁻¹)ᵢᵢ = Sᵢᵢ` when the
diagonal is not penalized (`Pᵢᵢ = 0`; Friedman, Hastie and Tibshirani, Remark 2.2). -/
theorem IsGraphicalLassoEstimate.inv_apply_self {P S Θ : Matrix ι ι ℝ}
    (h : IsGraphicalLassoEstimate P S Θ) (i : ι) : Θ⁻¹ i i = S i i + P i i :=
  inv_apply_self_eq h i

omit [Fintype ι] [DecidableEq ι] in
private theorem isSymm_const (ρ : ℝ) : (of fun _ _ => ρ : Matrix ι ι ℝ).IsSymm := by
  ext
  simp

/-- **Existence and uniqueness of the graphical lasso estimate** (Banerjee, El Ghaoui and
d'Aspremont, Theorem 1, for their problem (1), which is problem (2.1) of Friedman, Hastie and
Tibshirani): for `ρ > 0` and a positive semidefinite `S`, there is exactly one positive definite `Θ`
maximizing `log det Θ - tr (S Θ) - ρ ∑ᵢⱼ |Θᵢⱼ|` over positive definite matrices. -/
theorem existsUnique_isGraphicalLassoEstimate_const {ρ : ℝ} (hρ : 0 < ρ) {S : Matrix ι ι ℝ}
    (hS : S.PosSemidef) : ∃! Θ, IsGraphicalLassoEstimate (of fun _ _ => ρ) S Θ :=
  existsUnique_isGraphicalLassoEstimate (P := of fun _ _ => ρ) (fun _ _ => hρ.le) (fun _ => hρ) hS

/-- **Optimality conditions for the graphical lasso** (Friedman, Hastie and Tibshirani, equation
(2.6)): for `ρ ≥ 0` and a symmetric `S`, a positive definite `Θ` maximizes
`log det Θ - tr (S Θ) - ρ ∑ᵢⱼ |Θᵢⱼ|` over positive definite matrices iff, with `W = Θ⁻¹`,
`W - S - ρ Γ = 0` for some `Γ` with `Γᵢⱼ = sign Θᵢⱼ` where `Θᵢⱼ ≠ 0` and `Γᵢⱼ ∈ [-1, 1]` where
`Θᵢⱼ = 0`. -/
theorem isGraphicalLassoEstimate_const_iff {ρ : ℝ} (hρ : 0 ≤ ρ) {S Θ : Matrix ι ι ℝ}
    (hS : S.IsSymm) (hΘ : Θ.PosDef) :
    IsGraphicalLassoEstimate (of fun _ _ => ρ) S Θ ↔ ∃ Γ : Matrix ι ι ℝ,
      (∀ i j, Θ i j ≠ 0 → Γ i j = Real.sign (Θ i j)) ∧
      (∀ i j, Θ i j = 0 → Γ i j ∈ Set.Icc (-1) 1) ∧ Θ⁻¹ - S - ρ • Γ = 0 := by
  have h : ∀ Γ : Matrix ι ι ℝ, (of fun _ _ => ρ) ⊙ Γ = ρ • Γ := fun Γ => by
    ext
    simp
  rw [isGraphicalLassoEstimate_iff (P := of fun _ _ => ρ) (fun _ _ => hρ) (isSymm_const ρ) hS hΘ]
  simp only [h]

/-- **The diagonal of the graphical lasso covariance estimate** (Friedman, Hastie and
Tibshirani, Section 2; Banerjee, El Ghaoui and d'Aspremont, Section 2.2): the estimate `Θ` has
`(Θ⁻¹)ᵢᵢ = Sᵢᵢ + ρ` for every `i`, since `Θᵢᵢ > 0`. -/
theorem IsGraphicalLassoEstimate.inv_apply_self_const {ρ : ℝ} {S Θ : Matrix ι ι ℝ}
    (h : IsGraphicalLassoEstimate (of fun _ _ => ρ) S Θ) (i : ι) : Θ⁻¹ i i = S i i + ρ := by
  simpa using h.inv_apply_self i

end MathlibExt.Probability.Statistics.GraphicalLasso

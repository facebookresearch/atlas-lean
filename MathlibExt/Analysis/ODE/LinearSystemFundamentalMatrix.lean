/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.LinearAlgebra.Matrix.Bilinear
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Order.ProjIcc
import MathlibExt.Analysis.ODE.MaximalSolution

/-!
# Fundamental matrices for linear ODE systems

This file proves global existence and uniqueness for continuous linear systems, constructs their
principal matrix solutions, and proves Liouville's determinant formula.
-/

open MeasureTheory

@[expose] public section

namespace MathlibExt.Analysis.ODE.LinearSystemFundamentalMatrixWanted

private lemma fundMatrix_exists_operator_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (B : ℝ → E →L[ℝ] E) (hB : Continuous B) (a b : ℝ) :
    ∃ L : NNReal, ∀ t ∈ Set.Icc a b, ‖B t‖₊ ≤ L := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hB.continuousOn
  refine ⟨⟨max C 0, le_max_right _ _⟩, ?_⟩
  intro t ht
  change ‖B t‖ ≤ max C 0
  exact (hC t ht).trans (le_max_left _ _)

private lemma fundMatrix_linear_uniqueOn
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (B : ℝ → E →L[ℝ] E) (hB : Continuous B) (t₀ r : ℝ) (hr : 0 < r)
    {x y : ℝ → E}
    (hx : ∀ t ∈ Set.Ioo (t₀ - r) (t₀ + r), HasDerivAt x (B t (x t)) t)
    (hy : ∀ t ∈ Set.Ioo (t₀ - r) (t₀ + r), HasDerivAt y (B t (y t)) t)
    (hxy : x t₀ = y t₀) :
    Set.EqOn x y (Set.Ioo (t₀ - r) (t₀ + r)) := by
  obtain ⟨L, hL⟩ := fundMatrix_exists_operator_bound B hB (t₀ - r) (t₀ + r)
  apply ODE_solution_unique_of_mem_Ioo
      (v := fun t z ↦ B t z) (s := fun _ ↦ Set.univ) (K := L) (t₀ := t₀)
  · intro t ht
    exact ((B t).lipschitzWith.weaken (hL t (Set.Ioo_subset_Icc_self ht))).lipschitzOnWith
  · simp [hr]
  · exact fun t ht ↦ ⟨hx t ht, Set.mem_univ _⟩
  · exact fun t ht ↦ ⟨hy t ht, Set.mem_univ _⟩
  · exact hxy

private lemma fundMatrix_clampedSolution
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (B : ℝ → E →L[ℝ] E) (hB : Continuous B) (t₀ : ℝ) (x₀ : E) (N : ℕ) :
    ∃! x : ℝ → E, x t₀ = x₀ ∧ ∀ t,
      HasDerivAt x (B (Set.projIcc (t₀ - N) (t₀ + N) (by
        have := Nat.cast_nonneg (α := ℝ) N
        linarith) t) (x t)) t := by
  let c : ℝ → ℝ := fun t ↦ Set.projIcc (t₀ - N) (t₀ + N) (by
    have := Nat.cast_nonneg (α := ℝ) N
    linarith) t
  have hc : Continuous c := continuous_subtype_val.comp continuous_projIcc
  obtain ⟨L, hL⟩ :=
    fundMatrix_exists_operator_bound B hB (t₀ - N) (t₀ + N)
  apply MathlibExt.Analysis.ODE.MaximalSolutionWanted.ode_global_exists_of_global_lipschitz
      (fun t x ↦ B (c t) x) t₀ x₀ L
  · change Continuous (fun p : ℝ × E ↦ B (c p.1) p.2)
    exact (hB.comp (hc.comp continuous_fst)).clm_apply continuous_snd
  · intro t
    apply (B (c t)).lipschitzWith.weaken
    exact hL _ (Set.projIcc (t₀ - N) (t₀ + N) (by
      have := Nat.cast_nonneg (α := ℝ) N
      linarith) t).property

private lemma fundMatrix_clampedAgree
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (B : ℝ → E →L[ℝ] E) (hB : Continuous B) (t₀ : ℝ)
    {x y : ℝ → E} {N M : ℕ}
    (hx : x t₀ = y t₀ ∧ ∀ t, HasDerivAt x
      (B (Set.projIcc (t₀ - N) (t₀ + N) (by
        have := Nat.cast_nonneg (α := ℝ) N
        linarith) t) (x t)) t)
    (hy : ∀ t, HasDerivAt y
      (B (Set.projIcc (t₀ - M) (t₀ + M) (by
        have := Nat.cast_nonneg (α := ℝ) M
        linarith) t) (y t)) t)
    {t : ℝ} (hN : |t - t₀| < N) (hM : |t - t₀| < M) : x t = y t := by
  let r : ℝ := min N M
  have htr : |t - t₀| < r := lt_min hN hM
  have hr : 0 < r := (abs_nonneg _).trans_lt htr
  apply fundMatrix_linear_uniqueOn B hB t₀ r hr (x := x) (y := y) _ _ hx.1
      (show t ∈ Set.Ioo (t₀ - r) (t₀ + r) by rw [abs_lt] at htr; constructor <;> linarith)
  · intro s hs
    have hsN : s ∈ Set.Icc (t₀ - N) (t₀ + N) := by
      dsimp [r] at hs
      constructor <;> linarith [hs.1, hs.2, min_le_left (N : ℝ) M]
    simpa [Set.projIcc_of_mem _ hsN] using hx.2 s
  · intro s hs
    have hsM : s ∈ Set.Icc (t₀ - M) (t₀ + M) := by
      dsimp [r] at hs
      constructor <;> linarith [hs.1, hs.2, min_le_right (N : ℝ) M]
    simpa [Set.projIcc_of_mem _ hsM] using hy s

/-- **Global existence and uniqueness for homogeneous linear ODEs.** Let $E$ be a real Banach
space, write $L(E)$ for the space of continuous linear maps $E \to E$ with the operator norm,
let $B : \mathbb{R} \to L(E)$ be continuous, and let $t_0 \in \mathbb{R}$ and $x_0 \in E$. Then
there is exactly one function $x : \mathbb{R} \to E$ with $x(t_0) = x_0$ such that $x$ is
differentiable at every $t \in \mathbb{R}$ with $x'(t) = B(t)\,x(t)$. -/
theorem _root_.ODE.existsUnique_hasDerivAt_eq_continuousLinearMap
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (B : ℝ → E →L[ℝ] E) (t₀ : ℝ) (x₀ : E) (hB : Continuous B) :
    ∃! x : ℝ → E, x t₀ = x₀ ∧ ∀ t, HasDerivAt x (B t (x t)) t := by
  classical
  let sol : ℕ → ℝ → E := fun N ↦
    Classical.choose (fundMatrix_clampedSolution B hB t₀ x₀ N).exists
  have hsol (N : ℕ) : sol N t₀ = x₀ ∧ ∀ t, HasDerivAt (sol N)
      (B (Set.projIcc (t₀ - N) (t₀ + N) (by
        have := Nat.cast_nonneg (α := ℝ) N
        linarith) t) (sol N t)) t :=
    Classical.choose_spec (fundMatrix_clampedSolution B hB t₀ x₀ N).exists
  let radius : ℝ → ℕ := fun t ↦ Classical.choose (exists_nat_gt |t - t₀|)
  have hradius (t : ℝ) : |t - t₀| < radius t :=
    Classical.choose_spec (exists_nat_gt |t - t₀|)
  let x : ℝ → E := fun t ↦ sol (radius t) t
  have hx₀ : x t₀ = x₀ := by
    change sol (radius t₀) t₀ = x₀
    exact (hsol _).1
  have hx (t : ℝ) : HasDerivAt x (B t (x t)) t := by
    obtain ⟨N, hN⟩ := exists_nat_gt (|t - t₀| + 1)
    have htN : |t - t₀| < (N : ℝ) := lt_trans (lt_add_one _) hN
    have hevent : ∀ᶠ u in nhds t, |u - t₀| < (N : ℝ) :=
      (continuousAt_id.sub continuousAt_const).abs.eventually_lt continuousAt_const htN
    have heq : x =ᶠ[nhds t] sol N := by
      filter_upwards [hevent] with u hu
      exact fundMatrix_clampedAgree B hB t₀
        ⟨(hsol (radius u)).1.trans (hsol N).1.symm, (hsol (radius u)).2⟩
        (hsol N).2 (hradius u) hu
    have htIcc : t ∈ Set.Icc (t₀ - N) (t₀ + N) := by
      rw [abs_lt] at htN
      constructor <;> linarith
    have hd := (hsol N).2 t
    rw [Set.projIcc_of_mem _ htIcc] at hd
    simpa [heq.eq_of_nhds] using hd.congr_of_eventuallyEq heq
  refine ⟨x, ⟨hx₀, hx⟩, ?_⟩
  intro y hy
  funext t
  obtain ⟨N, hN⟩ := exists_nat_gt |t - t₀|
  have hNpos : 0 < (N : ℝ) := (abs_nonneg _).trans_lt hN
  apply fundMatrix_linear_uniqueOn B hB t₀ N hNpos
      (x := y) (y := x) (fun s _ ↦ hy.2 s) (fun s _ ↦ hx s)
      (hy.1.trans hx₀.symm)
  rw [abs_lt] at hN
  constructor <;> linarith

private noncomputable def fundMatrix_matrixMulCLM {n : ℕ} :
    (Fin n → Fin n → ℝ) →L[ℝ]
      (Fin n → Fin n → ℝ) →L[ℝ] Fin n → Fin n → ℝ :=
  LinearMap.toContinuousLinearMap
    ((LinearMap.toContinuousLinearMap :
      ((Fin n → Fin n → ℝ) →ₗ[ℝ] Fin n → Fin n → ℝ) ≃ₗ[ℝ]
        (Fin n → Fin n → ℝ) →L[ℝ] Fin n → Fin n → ℝ).toLinearMap.comp
      (mulLinearMap ℝ))

@[simp] private lemma fundMatrix_matrixMulCLM_apply {n : ℕ}
    (A X : Matrix (Fin n) (Fin n) ℝ) : fundMatrix_matrixMulCLM A X = A * X := by
  rfl

@[simp] private lemma fundMatrix_matrixMulCLM_apply_entry {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (X : Fin n → Fin n → ℝ) (i j : Fin n) :
    fundMatrix_matrixMulCLM A X i j = (A * Matrix.of X) i j := by
  rfl

private noncomputable def fundMatrix_mulVecCLM {n : ℕ} :
    Matrix (Fin n) (Fin n) ℝ →L[ℝ] (Fin n → ℝ) →L[ℝ] Fin n → ℝ :=
  LinearMap.toContinuousLinearMap
    ((LinearMap.toContinuousLinearMap :
      ((Fin n → ℝ) →ₗ[ℝ] Fin n → ℝ) ≃ₗ[ℝ] (Fin n → ℝ) →L[ℝ] Fin n → ℝ).toLinearMap.comp
      Matrix.toLin'.toLinearMap)

@[simp] private lemma fundMatrix_mulVecCLM_apply {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) :
    fundMatrix_mulVecCLM A x = A.mulVec x := by
  rfl

private noncomputable def fundMatrix_detDifferential {n : ℕ}
    (M N : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  ∑ σ : Equiv.Perm (Fin n), ((Equiv.Perm.sign σ : ℤ) : ℝ) *
    ∑ i : Fin n, (∏ j ∈ Finset.univ.erase i, M (σ j) j) * N (σ i) i

private lemma fundMatrix_hasDerivAt_entry {n : ℕ}
    {Φ : ℝ → Matrix (Fin n) (Fin n) ℝ} {N : Matrix (Fin n) (Fin n) ℝ} {t : ℝ}
    (hΦ : HasDerivAt Φ N t) (i j : Fin n) :
    HasDerivAt (fun s ↦ Φ s i j) (N i j) t := by
  exact (hasDerivAt_pi.mp (hasDerivAt_pi.mp hΦ i)) j

private lemma fundMatrix_hasDerivAt_det {n : ℕ}
    {Φ : ℝ → Matrix (Fin n) (Fin n) ℝ} {N : Matrix (Fin n) (Fin n) ℝ} {t : ℝ}
    (hΦ : HasDerivAt Φ N t) :
    HasDerivAt (fun s ↦ (Φ s).det) (fundMatrix_detDifferential (Φ t) N) t := by
  classical
  have hterm (σ : Equiv.Perm (Fin n)) : HasDerivAt
      (fun s ↦ ((Equiv.Perm.sign σ : ℤ) : ℝ) * ∏ i, Φ s (σ i) i)
      (((Equiv.Perm.sign σ : ℤ) : ℝ) *
        ∑ i, (∏ j ∈ Finset.univ.erase i, Φ t (σ j) j) * N (σ i) i) t := by
    apply HasDerivAt.const_mul
    convert HasDerivAt.fun_finsetProd (u := Finset.univ)
      (fun i _ ↦ fundMatrix_hasDerivAt_entry hΦ (σ i) i) using 1
  simpa only [Matrix.det_apply', fundMatrix_detDifferential] using
    HasDerivAt.fun_sum (u := Finset.univ) (fun σ _ ↦ hterm σ)

private lemma fundMatrix_hasDerivAt_det_one_add_smul {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) :
    HasDerivAt (fun s : ℝ ↦ (1 + s • A).det) A.trace 0 := by
  let p : Polynomial ℝ :=
    (1 + (Polynomial.X : Polynomial ℝ) • A.map (Polynomial.C : ℝ → Polynomial ℝ)).det
  have hp : HasDerivAt (fun s ↦ p.eval s) A.trace 0 :=
    (p.hasDerivAt 0).congr_deriv (Matrix.derivative_det_one_add_X_smul A)
  apply hp.congr_of_eventuallyEq
  filter_upwards with s
  dsimp [p]
  simp [eval_det, ← Matrix.smul_eq_mul_diagonal]

private lemma fundMatrix_detDifferential_mul {n : ℕ}
    (A M : Matrix (Fin n) (Fin n) ℝ) :
    fundMatrix_detDifferential M (A * M) = A.trace * M.det := by
  let ψ : ℝ → Matrix (Fin n) (Fin n) ℝ := fun s ↦ M + s • (A * M)
  have hψ : HasDerivAt ψ (A * M) 0 := by
    apply hasDerivAt_pi.mpr
    intro i
    apply hasDerivAt_pi.mpr
    intro j
    change HasDerivAt (fun s : ℝ ↦ M i j + s * (A * M) i j) ((A * M) i j) 0
    convert ((hasDerivAt_id' (𝕜 := ℝ) 0).mul_const ((A * M) i j)).const_add (M i j) using 1
    ring
  have hleft : HasDerivAt (fun s ↦ (ψ s).det)
      (fundMatrix_detDifferential M (A * M)) 0 := by
    simpa [ψ] using fundMatrix_hasDerivAt_det hψ
  have hright : HasDerivAt (fun s ↦ (ψ s).det) (A.trace * M.det) 0 := by
    apply (fundMatrix_hasDerivAt_det_one_add_smul A).mul_const M.det |>.congr_of_eventuallyEq
    filter_upwards with s
    rw [show ψ s = (1 + s • A) * M by simp [ψ, add_mul], Matrix.det_mul]
  exact hleft.unique hright

/-- **Jacobi's formula when the derivative is a left multiple of the matrix.** Let
$n \in \mathbb{N}$, let $A$ be a real $n \times n$ matrix, let
$\Phi : \mathbb{R} \to \mathbb{R}^{n \times n}$, and let $t \in \mathbb{R}$. If $\Phi$ is
differentiable at $t$ with $\Phi'(t) = A \Phi(t)$, then $s \mapsto \det \Phi(s)$ is
differentiable at $t$ with derivative $\operatorname{tr}(A) \det \Phi(t)$. -/
theorem _root_.HasDerivAt.det_of_mul {n : ℕ}
    {Φ : ℝ → Matrix (Fin n) (Fin n) ℝ} {A : Matrix (Fin n) (Fin n) ℝ} {t : ℝ}
    (hΦ : HasDerivAt Φ (A * Φ t) t) :
    HasDerivAt (fun s ↦ (Φ s).det) (A.trace * (Φ t).det) t := by
  rw [← fundMatrix_detDifferential_mul A (Φ t)]
  exact fundMatrix_hasDerivAt_det hΦ

private lemma fundMatrix_hasDerivAt_mulVec_const {n : ℕ}
    {Φ : ℝ → Matrix (Fin n) (Fin n) ℝ} {N : Matrix (Fin n) (Fin n) ℝ} {t : ℝ}
    (hΦ : HasDerivAt Φ N t) (x : Fin n → ℝ) :
    HasDerivAt (fun s ↦ (Φ s).mulVec x) (N.mulVec x) t := by
  apply hasDerivAt_pi.mpr
  intro i
  simpa only [Matrix.mulVec_apply_eq_sum] using
    HasDerivAt.fun_sum (u := Finset.univ)
      (fun j _ ↦ (fundMatrix_hasDerivAt_entry hΦ i j).mul_const (x j))

private lemma fundMatrix_liouville {n : ℕ}
    (A : ℝ → Matrix (Fin n) (Fin n) ℝ) (t₀ : ℝ) (hA : Continuous A)
    (Φ : ℝ → Matrix (Fin n) (Fin n) ℝ)
    (hΦ : ∀ t, HasDerivAt Φ (A t * Φ t) t) (t : ℝ) :
    (Φ t).det = (Φ t₀).det * Real.exp (∫ s in t₀..t, (A s).trace) := by
  let I : ℝ → ℝ := fun u ↦ ∫ s in t₀..u, (A s).trace
  have htrace : Continuous (fun s ↦ (A s).trace) := hA.matrix_trace
  have hI (u : ℝ) : HasDerivAt I (A u).trace u := by
    exact intervalIntegral.integral_hasDerivAt_right
      (htrace.intervalIntegrable t₀ u)
      (htrace.stronglyMeasurableAtFilter volume (nhds u)) htrace.continuousAt
  let w : ℝ → ℝ := fun u ↦ (Φ u).det * Real.exp (-I u)
  have hw (u : ℝ) : HasDerivAt w 0 u := by
    have hd := HasDerivAt.det_of_mul (hΦ u)
    have he := (hI u).neg.exp
    convert hd.mul he using 1
    ring
  have hw_const : w t = w t₀ :=
    is_const_of_deriv_eq_zero (fun u ↦ (hw u).differentiableAt)
      (fun u ↦ (hw u).deriv) t t₀
  have hw_eq : (Φ t).det * Real.exp (-I t) = (Φ t₀).det := by
    simpa [w, I] using hw_const
  calc
    (Φ t).det = ((Φ t).det * Real.exp (-I t)) * Real.exp (I t) := by
      rw [mul_assoc, ← Real.exp_add]
      simp
    _ = (Φ t₀).det * Real.exp (I t) := by rw [hw_eq]
    _ = (Φ t₀).det * Real.exp (∫ s in t₀..t, (A s).trace) := rfl

/-- **Fundamental matrix of a linear system.** Let $n \in \mathbb{N}$, let
$A : \mathbb{R} \to \mathbb{R}^{n \times n}$ be continuous, let $t_0 \in \mathbb{R}$, and write $I$
for the $n \times n$ identity matrix. Then there is a function
$\Phi : \mathbb{R} \to \mathbb{R}^{n \times n}$ with $\Phi(t_0) = I$, $\Phi'(t) = A(t) \Phi(t)$ and
$\det \Phi(t) \ne 0$ for every $t \in \mathbb{R}$, such that for every $x_0 \in \mathbb{R}^n$
the function $x(t) = \Phi(t) x_0$ satisfies $x(t_0) = x_0$ and $x'(t) = A(t) x(t)$ for every
$t \in \mathbb{R}$, and every $y : \mathbb{R} \to \mathbb{R}^n$ with $y(t_0) = x_0$ and
$y'(t) = A(t) y(t)$ for every $t \in \mathbb{R}$ equals $x$.

Proof: Global solutions are patched from clamped-time systems using Teschl, Theorem 3.9, then
assembled into the principal matrix solution of (3.83) and Theorem 3.10. Liouville's formula gives
invertibility as in (3.88)-(3.89).

Proves `Wanted` entry `fundamental_matrix_linear_system`.

Sources: `Mathlib/docs/undergrad.yaml`, section `Multivariable calculus` /
`Differential equations`, entry `linear differential systems` (unmapped);
G. Teschl, Ordinary Differential Equations and Dynamical Systems, Section 3.4;
stable ref https://en.wikipedia.org/wiki/Fundamental_matrix_(linear_differential_equation).
-/
theorem fundamental_matrix_linear_system
    {n : ℕ} (A : ℝ → Matrix (Fin n) (Fin n) ℝ) (t₀ : ℝ)
    (hA : Continuous A) :
    ∃ Φ : ℝ → Matrix (Fin n) (Fin n) ℝ, Φ t₀ = 1 ∧
      (∀ t, HasDerivAt Φ (A t * Φ t) t) ∧
      (∀ t, IsUnit (Φ t).det) ∧
      ∀ x₀ : Fin n → ℝ, ∃ x : ℝ → (Fin n → ℝ),
        x t₀ = x₀ ∧ (∀ t, HasDerivAt x ((A t).mulVec (x t)) t) ∧
        (∀ t, x t = (Φ t).mulVec x₀) ∧
        ∀ y : ℝ → (Fin n → ℝ), y t₀ = x₀ →
          (∀ t, HasDerivAt y ((A t).mulVec (y t)) t) → y = x := by
  let B : ℝ → (Fin n → Fin n → ℝ) →L[ℝ] Fin n → Fin n → ℝ :=
    fun t ↦ fundMatrix_matrixMulCLM (A t)
  have hB : Continuous B := fundMatrix_matrixMulCLM.continuous.comp hA
  obtain ⟨φ, hφ0, hφ⟩ :=
    (ODE.existsUnique_hasDerivAt_eq_continuousLinearMap B t₀
      (Matrix.of.symm (1 : Matrix (Fin n) (Fin n) ℝ)) hB).exists
  let Φ : ℝ → Matrix (Fin n) (Fin n) ℝ := fun t ↦ Matrix.of (φ t)
  have hΦ0 : Φ t₀ = 1 := by simp [Φ, hφ0]
  have hΦ' (t : ℝ) : HasDerivAt Φ (A t * Φ t) t := by
    apply hasDerivAt_pi.mpr
    intro i
    apply hasDerivAt_pi.mpr
    intro j
    simpa [Φ, B] using (hasDerivAt_pi.mp (hasDerivAt_pi.mp (hφ t) i) j)
  refine ⟨Φ, hΦ0, hΦ', ?_, ?_⟩
  · intro t
    apply isUnit_iff_ne_zero.mpr
    rw [fundMatrix_liouville A t₀ hA Φ hΦ' t, hΦ0]
    simp
  · intro x₀
    let x : ℝ → Fin n → ℝ := fun t ↦ (Φ t).mulVec x₀
    have hx0 : x t₀ = x₀ := by simp [x, hΦ0]
    have hx (t : ℝ) : HasDerivAt x ((A t).mulVec (x t)) t := by
      simpa only [x, Matrix.mulVec_mulVec] using
        fundMatrix_hasDerivAt_mulVec_const (hΦ' t) x₀
    let C : ℝ → (Fin n → ℝ) →L[ℝ] Fin n → ℝ :=
      fun t ↦ fundMatrix_mulVecCLM (A t)
    have hC : Continuous C := fundMatrix_mulVecCLM.continuous.comp hA
    obtain ⟨z, hz, hunique⟩ :=
      ODE.existsUnique_hasDerivAt_eq_continuousLinearMap C t₀ x₀ hC
    have hxz : x = z := hunique x ⟨hx0, fun t ↦ by simpa [C] using hx t⟩
    refine ⟨x, hx0, hx, fun _ ↦ rfl, ?_⟩
    intro y hy0 hy
    exact (hunique y ⟨hy0, fun t ↦ by simpa [C] using hy t⟩).trans hxz.symm

/-- **Liouville's formula for the principal matrix solution.** Let $n \in \mathbb{N}$, let
$A : \mathbb{R} \to \mathbb{R}^{n \times n}$ be continuous, let $t_0 \in \mathbb{R}$, write $I$ for
the $n \times n$ identity matrix, and let $\Phi : \mathbb{R} \to \mathbb{R}^{n \times n}$ satisfy
$\Phi(t_0) = I$ and $\Phi'(t) = A(t) \Phi(t)$ for every $t \in \mathbb{R}$. Then for every
$t \in \mathbb{R}$,
$\det \Phi(t) = \det \Phi(t_0) \exp\left(\int_{t_0}^{t} \operatorname{tr} A(s)\, ds\right)$.

Proof: Jacobi's formula follows from the determinant's first-order term; an integrating factor then
gives Teschl, Lemma 3.11, formula (3.91).

Proves `Wanted` entry `fundamental_matrix_liouville_det`.

Sources: `Mathlib/docs/undergrad.yaml`, section `Multivariable calculus` /
`Differential equations`, entry `linear differential systems` (unmapped);
G. Teschl, Ordinary Differential Equations and Dynamical Systems, Section 3.4;
stable ref https://en.wikipedia.org/wiki/Abel%27s_identity.
-/
theorem fundamental_matrix_liouville_det
    {n : ℕ} (A : ℝ → Matrix (Fin n) (Fin n) ℝ) (t₀ : ℝ)
    (hA : Continuous A)
    (Φ : ℝ → Matrix (Fin n) (Fin n) ℝ)
    (hΦ0 : Φ t₀ = 1) (hΦ : ∀ t, HasDerivAt Φ (A t * Φ t) t) :
    ∀ t, (Φ t).det = (Φ t₀).det * Real.exp (∫ s in t₀..t, (A s).trace) := by
  exact fundMatrix_liouville A t₀ hA Φ hΦ

end MathlibExt.Analysis.ODE.LinearSystemFundamentalMatrixWanted

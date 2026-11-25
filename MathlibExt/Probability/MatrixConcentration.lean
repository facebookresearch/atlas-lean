/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.LinearAlgebra.Matrix.HermitianTraceExp
public import MathlibExt.Probability.MatrixLaplaceTransform
public import Mathlib.Analysis.Matrix.MeasurableSpace
public import Mathlib.Probability.Independence.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Probability.Distributions.Gaussian.Real

import MathlibExt.LinearAlgebra.Matrix.LiebConcavity
import Mathlib.Analysis.Convex.Continuous
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Probability.Moments.Basic

/-!
# Matrix concentration inequalities

For independent random Hermitian `d × d` matrices `X₀, …, X_{N-1}` this file proves the
subadditivity of matrix cumulant generating functions,
`E tr exp(∑ₖ θ Xₖ) ≤ tr exp(∑ₖ log E e^{θ Xₖ})`, and the matrix Gaussian-series, Chernoff,
Bernstein and Hoeffding inequalities for the extreme eigenvalues of `∑ₖ Xₖ` (J. A. Tropp,
*An Introduction to Matrix Concentration Inequalities*, Found. Trends Mach. Learn. 8 (2015),
arXiv:1501.01571v1, Lemma 3.5.1 and Theorems 4.6.1, 5.1.1 and 6.6.1; J. A. Tropp,
*User-friendly tail bounds for sums of random matrices*, Found. Comput. Math. 12 (2012),
arXiv:1004.4389v7, Theorem 1.3). Expectations of random matrices are taken entrywise
(`MathlibExt.Probability.MatrixLaplaceTransform.expect`), `tr` is the real part of the trace and
`log A = cfc Real.log A`.

## Proof

* **Jensen's inequality for Lieb's function** (Tropp, arXiv:1501.01571v1, Corollary 3.4.2). For a
  fixed Hermitian `H`, the map `f(A) = tr exp(H + log A)` is concave on the positive-definite cone
  (`MathlibExt.LinearAlgebra.Matrix.LiebConcavityWanted.lieb_concavity`). Composed with the
  Hermitian part `A ↦ (A + Aᴴ) / 2` it is concave on an open convex set of matrices, since a
  small Hermitian perturbation of a positive-definite matrix stays positive definite; so it is
  continuous there, and the Hahn–Banach separation of a point from the open strict hypograph
  gives an affine function above `f` that touches it at `E e^X`. Integrating this affine bound
  at `A = e^X` gives `E tr exp(H + X) ≤ tr exp(H + log E e^X)`.
* **Iteration** (proof of Lemma 3.5.1). By independence the joint law of `∑_{k ∈ S} Xₖ` and of a
  further summand `Xⱼ` is a product measure, so Tonelli's theorem removes one summand at a time,
  the fixed matrix `H` absorbing the logarithms already produced. Lower Lebesgue integrals are
  used throughout, so no integrability of partial sums is needed, and the final bound shows that
  `tr exp(θ ∑ₖ Xₖ)` is integrable.
* **Semidefinite mgf bounds.** The function `f` is also monotone: a concave function that is
  nonnegative on the cone cannot decrease along a positive-semidefinite direction. So
  `E e^{θX} ≼ e^C` gives `tr exp(H + log E e^{θX}) ≤ tr exp(H + C)`; this replaces Tropp's use of
  the operator monotonicity of the logarithm. The bounds `E e^{θX} ≼ exp(g(θ) E X)` (Lemma 5.4.1,
  from the chord of `x ↦ e^{θx}` on `[0, L]`), `E e^{θX} ≼ exp(g(θ) E X²)` (Lemma 6.6.2, from
  `e^{θx} ≤ 1 + θx + (θ²/2) / (1 - θL/3) x²` for `x ≤ L`) and `E e^{θγA} = exp(θ²A²/2)`
  (Lemma 4.6.2, computed in the spectral decomposition of `A`) come from scalar facts through
  the functional calculus.
* **Hoeffding.** For centred `X` with `X² ≼ A²`, Tropp symmetrizes with the Golden–Thompson
  inequality (arXiv:1004.4389v7, Lemma 7.6). Here an independent copy `X'` enters through
  Jensen's inequality for the convex map `M ↦ tr exp(K - θM)`; pairing `(X, X')` with `(X', X)`
  and the midpoint concavity of `f` then give `tr exp(H + log cosh(θZ))` with `Z = X - X'`, and
  `cosh y ≤ e^{y²/2}` and `Z² ≼ 4A²` give `E tr exp(H + θX) ≤ tr exp(H + 2θ²A²)`, the step that
  Tropp iterates to reach his display (7.5).
* **Tail bounds.** These come from the matrix Laplace transform bounds of
  `MathlibExt.Probability.MatrixLaplaceTransform` and `tr e^{θM} ≤ d e^{θ λmax(M)}`, with
  `θ = log(1 + ε) / L` and `θ = log(1 - ε) / L` (Chernoff), `θ = t / (v + Lt/3)`, or `3 / (2L)`
  when `v = 0` (Bernstein), `θ = t / v` (Gaussian series) and `θ = t / (4σ²)` (Hoeffding). The
  Gaussian expectation bound minimizes `θ⁻¹ log d + θv/2` over `θ > 0`; there `λmax` of the
  series is measurable as the limit of `p⁻¹ log tr e^{pY}`.

The theorems keep the full names they had when they were recorded as wanted, so their namespace
still reads `MatrixConcentrationWanted`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory MathlibExt.Probability.MatrixLaplaceTransform
open scoped ComplexOrder MatrixOrder Matrix

namespace MathlibExt.Probability.MatrixConcentrationWanted

variable {n : Type*} [Fintype n] [DecidableEq n]

omit [Fintype n] [DecidableEq n] in
/-- Matrices over a finite index type form a second-countable space, so the product of two
copies carries the Borel structure and continuous maps on it are measurable. -/
private lemma secondCountableTopology_matrix [Finite n] : SecondCountableTopology (Matrix n n ℂ) :=
  inferInstanceAs (SecondCountableTopology (n → n → ℂ))

attribute [local instance] secondCountableTopology_matrix

/-- The matrix exponential is continuous. -/
private lemma continuous_exp_matrix : Continuous (fun A : Matrix n n ℂ => NormedSpace.exp A) := by
  let _ := Matrix.linftyOpNormedRing (n := n) (α := ℂ)
  let _ := Matrix.linftyOpNormedAlgebra (R := ℂ) (n := n) (α := ℂ)
  let _ : NormedAlgebra ℚ (Matrix n n ℂ) := NormedAlgebra.restrictScalars ℚ ℂ _
  exact NormedSpace.exp_continuous

/-- `M ↦ re tr e^M` is continuous. -/
private lemma continuous_re_trace_exp :
    Continuous (fun A : Matrix n n ℂ => RCLike.re (NormedSpace.exp A).trace) :=
  RCLike.continuous_re.comp (continuous_exp_matrix.matrix_trace)

/-- `re tr e^M ≥ 0` for Hermitian `M`. -/
private lemma re_trace_exp_nonneg_of_isHermitian {M : Matrix n n ℂ} (hM : M.IsHermitian) :
    0 ≤ RCLike.re (NormedSpace.exp M).trace := by
  simpa using hM.re_trace_exp_nonneg 1

/-- For Hermitian `M`, `e^M = cfc Real.exp M`. -/
private lemma exp_eq_cfc_exp {M : Matrix n n ℂ} (hM : M.IsHermitian) :
    NormedSpace.exp M = cfc Real.exp M := by
  simpa only [one_smul, one_mul] using hM.exp_smul_eq_cfc 1

/-- Every real function is continuous on the finite real spectrum of a matrix. -/
private lemma continuousOn_spectrum_real (A : Matrix n n ℂ) (f : ℝ → ℝ) :
    ContinuousOn f (spectrum ℝ A) :=
  (A.finite_real_spectrum.continuousOn _)

/-- For Hermitian `M`, `log e^M = M`. -/
private lemma cfc_log_exp {M : Matrix n n ℂ} (hM : M.IsHermitian) :
    cfc Real.log (NormedSpace.exp M) = M := by
  rw [exp_eq_cfc_exp hM, ← cfc_comp Real.log Real.exp M hM.isSelfAdjoint
    ((M.finite_real_spectrum.image _).continuousOn _) (continuousOn_spectrum_real M _)]
  simp only [Function.comp_def, Real.log_exp]
  exact cfc_id' ℝ M hM.isSelfAdjoint

/-- For Hermitian `M`, `e^M` is positive definite. -/
private lemma posDef_exp {M : Matrix n n ℂ} (hM : M.IsHermitian) :
    (NormedSpace.exp M).PosDef := by
  rw [exp_eq_cfc_exp hM, ← Matrix.isStrictlyPositive_iff_posDef]
  exact (cfc_isStrictlyPositive_iff Real.exp M (continuousOn_spectrum_real M _)
    hM.isSelfAdjoint).mpr fun x _ => Real.exp_pos x

omit [DecidableEq n] in
/-- `0 ≤ re tr (X P)` for positive-semidefinite `X` and `P`. -/
private lemma re_trace_mul_nonneg {X P : Matrix n n ℂ} (hX : X.PosSemidef) (hP : P.PosSemidef) :
    0 ≤ RCLike.re (X * P).trace := by
  classical
  have hX0 : 0 ≤ X := Matrix.nonneg_iff_posSemidef.mpr hX
  set S := CFC.sqrt X
  have hS : S.IsHermitian := (CFC.sqrt_nonneg X).isSelfAdjoint
  have hSS : S * S = X := CFC.sqrt_mul_sqrt_self X hX0
  have hPS : (S * P * S).PosSemidef := by
    simpa [hS.eq] using hP.conjTranspose_mul_mul_same S
  rw [← hSS, Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_assoc, ← Matrix.mul_assoc]
  exact (RCLike.nonneg_iff.1 hPS.trace_nonneg).1

/-- The trace exponential is monotone in the semidefinite order (Tropp, arXiv:1501.01571v1,
display (2.1.16)); here it follows from the variational formula. -/
private lemma re_trace_exp_le_of_posSemidef {M M' : Matrix n n ℂ} (hM : M.IsHermitian)
    (hM' : M'.IsHermitian) (h : (M' - M).PosSemidef) :
    RCLike.re (NormedSpace.exp M).trace ≤ RCLike.re (NormedSpace.exp M').trace := by
  obtain ⟨⟨X, hX, hXe⟩, -⟩ :=
    MathlibExt.LinearAlgebra.Matrix.RelativeEntropy.isGreatest_re_trace_exp hM
  have h2 := (MathlibExt.LinearAlgebra.Matrix.RelativeEntropy.isGreatest_re_trace_exp hM').2
    ⟨X, hX, rfl⟩
  have h3 : 0 ≤ RCLike.re (X * (M' - M)).trace := re_trace_mul_nonneg hX.posSemidef h
  simp only [Matrix.mul_sub, Matrix.trace_sub, map_sub] at h3
  simp only at hXe h2
  linarith

/-- Convexity of the trace exponential on Hermitian matrices. -/
private lemma convexOn_re_trace_exp :
    ConvexOn ℝ {M : Matrix n n ℂ | M.IsHermitian}
      (fun M => RCLike.re (NormedSpace.exp M).trace) := by
  refine ⟨fun M₁ h₁ M₂ h₂ a b _ _ _ => ?_, fun M₁ h₁ M₂ h₂ a b ha hb hab => ?_⟩
  · exact ((IsSelfAdjoint.all a).smul h₁).add ((IsSelfAdjoint.all b).smul h₂)
  have hM : (a • M₁ + b • M₂).IsHermitian :=
    ((IsSelfAdjoint.all a).smul h₁).add ((IsSelfAdjoint.all b).smul h₂)
  obtain ⟨⟨X, hX, hXe⟩, -⟩ :=
    MathlibExt.LinearAlgebra.Matrix.RelativeEntropy.isGreatest_re_trace_exp hM
  have e₁ := (MathlibExt.LinearAlgebra.Matrix.RelativeEntropy.isGreatest_re_trace_exp h₁).2
    ⟨X, hX, rfl⟩
  have e₂ := (MathlibExt.LinearAlgebra.Matrix.RelativeEntropy.isGreatest_re_trace_exp h₂).2
    ⟨X, hX, rfl⟩
  simp only at hXe e₁ e₂ ⊢
  rw [← hXe]
  simp only [Matrix.mul_add, Matrix.mul_smul, Matrix.trace_add, Matrix.trace_smul, map_add,
    RCLike.smul_re, smul_eq_mul]
  have hb' : b = 1 - a := by linarith
  subst hb'
  nlinarith [mul_le_mul_of_nonneg_left e₁ ha, mul_le_mul_of_nonneg_left e₂ hb]

/-- **Lieb's function is monotone.** For Hermitian `H`, positive-definite `A` and `B ≽ A`,
`tr exp(H + log A) ≤ tr exp(H + log B)`: a concave function that is nonnegative on the cone cannot
decrease along the ray from `A` through `B`. -/
private lemma lieb_mono {H A B : Matrix n n ℂ} (hH : H.IsHermitian) (hA : A.PosDef)
    (hAB : (B - A).PosSemidef) :
    RCLike.re (NormedSpace.exp (H + cfc Real.log A)).trace ≤
      RCLike.re (NormedSpace.exp (H + cfc Real.log B)).trace := by
  set f : Matrix n n ℂ → ℝ := fun A => RCLike.re (NormedSpace.exp (H + cfc Real.log A)).trace
  have hf0 : ∀ A, 0 ≤ f A := fun A =>
    re_trace_exp_nonneg_of_isHermitian (hH.add (cfc_predicate Real.log A))
  change f A ≤ f B
  by_contra hlt
  push Not at hlt
  have hfA : 0 < f A := (hf0 B).trans_lt hlt
  set ε : ℝ := (f A - f B) / (2 * f A)
  have hε : 0 < ε := div_pos (by linarith) (by linarith)
  have hε1 : ε ≤ 1 := by
    rw [div_le_one (by linarith)]; linarith [hf0 B]
  set A' : Matrix n n ℂ := A + ε⁻¹ • (B - A)
  have hA' : A'.PosDef := hA.add_posSemidef (hAB.smul (inv_nonneg.mpr hε.le))
  have hcomb : (1 - ε) • A + ε • A' = B := by
    simp only [A', smul_add, smul_smul, mul_inv_cancel₀ hε.ne', one_smul, sub_smul]
    abel
  have hc := (MathlibExt.LinearAlgebra.Matrix.LiebConcavityWanted.lieb_concavity hH).2 hA hA'
    (by linarith : (0 : ℝ) ≤ 1 - ε) hε.le (by ring)
  simp only [smul_eq_mul] at hc
  rw [hcomb] at hc
  change (1 - ε) * f A + ε * f A' ≤ f B at hc
  have h1 : (1 - ε) * f A = f A - (f A - f B) / 2 := by
    simp only [ε]; field_simp
  nlinarith [mul_nonneg hε.le (hf0 A')]

/-- An `ℝ`-linear functional on complex matrices in coordinates. -/
private lemma linearMap_apply_eq_sum (ℓ : Matrix n n ℂ →ₗ[ℝ] ℝ) (M : Matrix n n ℂ) :
    ℓ M = ∑ i, ∑ j, ((M i j).re * ℓ (Matrix.single i j 1) +
      (M i j).im * ℓ (Matrix.single i j Complex.I)) := by
  conv_lhs => rw [Matrix.matrix_eq_sum_single M]
  simp only [map_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  have h : Matrix.single i j (M i j) =
      (M i j).re • Matrix.single i j (1 : ℂ) + (M i j).im • Matrix.single i j Complex.I := by
    rw [Matrix.smul_single, Matrix.smul_single, ← Matrix.single_add]
    congr 1
    apply Complex.ext <;> simp
  rw [h, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]

omit [Fintype n] [DecidableEq n] in
/-- Integrals commute with `ℝ`-linear functionals of a random matrix. -/
private lemma integrable_and_integral_linearMap [Finite n] {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] (ℓ : Matrix n n ℂ →ₗ[ℝ] ℝ) {Y : Ω → Matrix n n ℂ}
    (hY : ∀ i j, Integrable (fun ω => Y ω i j) μ) :
    Integrable (fun ω => ℓ (Y ω)) μ ∧ ∫ ω, ℓ (Y ω) ∂μ = ℓ (expect μ Y) := by
  classical
  have := Fintype.ofFinite n
  have hre : ∀ i j, Integrable (fun ω => (Y ω i j).re) μ := fun i j => (hY i j).re
  have him : ∀ i j, Integrable (fun ω => (Y ω i j).im) μ := fun i j => (hY i j).im
  have hint : ∀ i j, Integrable (fun ω => (Y ω i j).re * ℓ (Matrix.single i j 1) +
      (Y ω i j).im * ℓ (Matrix.single i j Complex.I)) μ := fun i j =>
    ((hre i j).mul_const _).add ((him i j).mul_const _)
  have e : ∀ ω, ℓ (Y ω) = ∑ i, ∑ j, ((Y ω i j).re * ℓ (Matrix.single i j 1) +
      (Y ω i j).im * ℓ (Matrix.single i j Complex.I)) := fun ω => linearMap_apply_eq_sum ℓ (Y ω)
  simp only [e]
  rw [linearMap_apply_eq_sum ℓ (expect μ Y)]
  refine ⟨integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hint i j, ?_⟩
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ fun j _ => hint i j)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_finsetSum _ (fun j _ => hint i j)]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [integral_add ((hre i j).mul_const _) ((him i j).mul_const _), integral_mul_const,
    integral_mul_const]
  simp only [expect, Matrix.of_apply]
  have h1 := integral_re (hY i j)
  have h2 := integral_im (hY i j)
  simp only [RCLike.re_to_complex, RCLike.im_to_complex] at h1 h2
  rw [h1, h2]

/-- Supporting affine function of a concave function on an open convex set. -/
private lemma exists_le_add_of_concaveOn {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {C : Set E} {f : E → ℝ} (hC : IsOpen C) (hf : ConcaveOn ℝ C f)
    {x₀ : E} (hx₀ : x₀ ∈ C) : ∃ ℓ : E →L[ℝ] ℝ, ∀ x ∈ C, f x ≤ f x₀ + ℓ (x - x₀) := by
  have hcont : ContinuousOn f C := hf.continuousOn hC
  set s : Set (E × ℝ) := {p | p.1 ∈ C ∧ p.2 < f p.1}
  have hs_open : IsOpen s := by
    have : s = (C ×ˢ Set.univ) ∩ (fun p : E × ℝ => f p.1 - p.2) ⁻¹' Set.Ioi 0 := by
      ext p; simp [s, sub_pos]
    rw [this]
    refine ContinuousOn.isOpen_inter_preimage ?_ (hC.prod isOpen_univ) isOpen_Ioi
    exact (hcont.comp continuousOn_fst fun p hp => (Set.mem_prod.1 hp).1).sub continuousOn_snd
  have hs_conv : Convex ℝ s := by
    rintro ⟨x, t⟩ ⟨hx, ht⟩ ⟨y, u⟩ ⟨hy, hu⟩ a b ha hb hab
    refine ⟨hf.1 hx hy ha hb hab, ?_⟩
    have h := hf.2 hx hy ha hb hab
    simp only [Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul] at h ⊢
    rcases ha.eq_or_lt with rfl | ha'
    · have hb1 : b = 1 := by linarith
      subst hb1
      simpa using hu
    · nlinarith [mul_lt_mul_of_pos_left ht ha', mul_le_mul_of_nonneg_left hu.le hb]
  have hnot : (x₀, f x₀) ∉ s := fun h => lt_irrefl _ h.2
  obtain ⟨φ, hφ⟩ := geometric_hahn_banach_open_point hs_conv hs_open hnot
  set c := φ (0, 1)
  have hsplit : ∀ x t, φ (x, t) = φ (x, 0) + t * c := by
    intro x t
    have : ((x, t) : E × ℝ) = (x, 0) + t • ((0 : E), (1 : ℝ)) := by simp
    rw [this, map_add, map_smul, smul_eq_mul]
  have hc : 0 < c := by
    have h := hφ (x₀, f x₀ - 1) ⟨hx₀, by linarith⟩
    rw [hsplit, hsplit x₀ (f x₀)] at h
    nlinarith
  refine ⟨-(c⁻¹ • φ.comp (ContinuousLinearMap.inl ℝ E ℝ)), fun x hx => ?_⟩
  have key : φ (x, 0) + f x * c ≤ φ (x₀, 0) + f x₀ * c := by
    by_contra hlt
    push Not at hlt
    set K := φ (x₀, 0) + f x₀ * c
    have h := hφ (x, f x - (φ (x, 0) + f x * c - K) / (2 * c))
      ⟨hx, by
        have : 0 < (φ (x, 0) + f x * c - K) / (2 * c) := div_pos (by linarith) (by linarith)
        linarith⟩
    rw [hsplit, hsplit x₀ (f x₀)] at h
    have e : (f x - (φ (x, 0) + f x * c - K) / (2 * c)) * c =
        f x * c - (φ (x, 0) + f x * c - K) / 2 := by
      field_simp
    linarith
  have e2 : (-(c⁻¹ • φ.comp (ContinuousLinearMap.inl ℝ E ℝ))) (x - x₀) =
      (φ (x₀, 0) - φ (x, 0)) / c := by
    simp only [neg_apply, smul_apply,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.inl_apply, smul_eq_mul]
    have : ((x - x₀, 0) : E × ℝ) = (x, 0) - (x₀, 0) := by simp
    rw [this, map_sub]
    field_simp
    ring
  rw [e2]
  have : f x - f x₀ ≤ (φ (x₀, 0) - φ (x, 0)) / c := by rw [le_div_iff₀ hc]; linarith
  linarith

omit [DecidableEq n] in
/-- `re tr (M M) = ∑ᵢⱼ ‖Mᵢⱼ‖²` for Hermitian `M`. -/
private lemma re_trace_mul_self_eq {M : Matrix n n ℂ} (hM : M.IsHermitian) :
    RCLike.re (M * M).trace = ∑ i, ∑ j, ‖M i j‖ ^ 2 := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, map_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [← hM.apply j i, RCLike.star_def, RCLike.mul_conj]
  norm_cast

/-- `∑ᵢ λᵢ² = ∑ᵢⱼ ‖Mᵢⱼ‖²` for Hermitian `M`. -/
private lemma sum_eigenvalues_sq {M : Matrix n n ℂ} (hM : M.IsHermitian) :
    ∑ i, hM.eigenvalues i ^ 2 = ∑ i, ∑ j, ‖M i j‖ ^ 2 := by
  rw [← re_trace_mul_self_eq hM]
  have h := hM.trace_cfc_eq_sum (𝕜 := ℂ) (fun x => x ^ 2)
  rw [cfc_pow_id M 2 hM.isSelfAdjoint, sq] at h
  rw [h, map_sum]
  exact Finset.sum_congr rfl fun i _ => by norm_cast

/-- Each eigenvalue `λᵢ` of a Hermitian `M` satisfies `λᵢ² ≤ ∑ⱼₖ ‖Mⱼₖ‖²`. -/
private lemma eigenvalues_sq_le {M : Matrix n n ℂ} (hM : M.IsHermitian) (i : n) :
    hM.eigenvalues i ^ 2 ≤ ∑ i, ∑ j, ‖M i j‖ ^ 2 := by
  rw [← sum_eigenvalues_sq hM]
  exact Finset.single_le_sum (f := fun j => hM.eigenvalues j ^ 2) (fun j _ => sq_nonneg _)
    (Finset.mem_univ i)

omit [DecidableEq n] in
/-- Each entry of a Hermitian `M` satisfies `‖Mᵢⱼ‖² ≤ re tr (M M)`. -/
private lemma norm_apply_sq_le {M : Matrix n n ℂ} (hM : M.IsHermitian) (i j : n) :
    ‖M i j‖ ^ 2 ≤ RCLike.re (M * M).trace := by
  rw [re_trace_mul_self_eq hM]
  exact (Finset.single_le_sum (f := fun j => ‖M i j‖ ^ 2) (fun j _ => sq_nonneg _)
    (Finset.mem_univ j)).trans (Finset.single_le_sum (f := fun i => ∑ j, ‖M i j‖ ^ 2)
      (fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _) (Finset.mem_univ i))

omit [DecidableEq n] in
/-- Positive-definite matrices stay positive definite under small Hermitian perturbations. -/
private lemma exists_posDef_add {A : Matrix n n ℂ} (hA : A.PosDef) :
    ∃ ε > 0, ∀ M : Matrix n n ℂ, M.IsHermitian → ∑ i, ∑ j, ‖M i j‖ ^ 2 < ε →
      (A + M).PosDef := by
  classical
  rcases isEmpty_or_nonempty n with hn | hn
  · refine ⟨1, one_pos, fun M hM _ => ⟨hA.isHermitian.add hM, fun x hx => ?_⟩⟩
    exact absurd (Subsingleton.elim x 0) hx
  obtain ⟨r, hr, hrA⟩ := (CFC.exists_pos_algebraMap_le_iff A hA.isHermitian.isSelfAdjoint).2
    fun x hx => (Matrix.isStrictlyPositive_iff_posDef.2 hA).spectrum_pos hx
  refine ⟨(r / 2) ^ 2, by positivity, fun M hM hsmall => ?_⟩
  have hMr : algebraMap ℝ (Matrix n n ℂ) (-(r / 2)) ≤ M := by
    rw [algebraMap_le_iff_le_spectrum (a := M) hM.isSelfAdjoint]
    intro x hx
    rw [hM.spectrum_real_eq_range_eigenvalues] at hx
    obtain ⟨i, rfl⟩ := hx
    have h1 : hM.eigenvalues i ^ 2 < (r / 2) ^ 2 := (eigenvalues_sq_le hM i).trans_lt hsmall
    nlinarith [abs_lt_of_sq_lt_sq' h1 (by positivity)]
  have hsum : algebraMap ℝ (Matrix n n ℂ) (r / 2) ≤ A + M := by
    have := add_le_add hrA hMr
    rwa [← map_add, show r + -(r / 2) = r / 2 by ring] at this
  have hc : (algebraMap ℝ (Matrix n n ℂ) (r / 2)).PosDef := by
    rw [Matrix.algebraMap_eq_diagonal]
    exact Matrix.PosDef.diagonal fun _ => by simpa using (by positivity : (0 : ℝ) < r / 2)
  have := hc.add_posSemidef (Matrix.le_iff.1 hsum)
  rwa [add_sub_cancel] at this

/-- The Hermitian part `A ↦ (A + Aᴴ) / 2` of a matrix, Mathlib's `realPart`, as an `ℝ`-linear
map with values in matrices. -/
private noncomputable abbrev hermPart : Matrix n n ℂ →ₗ[ℝ] Matrix n n ℂ :=
  (selfAdjoint.submodule ℝ (Matrix n n ℂ)).subtype ∘ₗ realPart

omit [Fintype n] [DecidableEq n] in
/-- The entries of the Hermitian part of `N` are bounded by those of `N`. -/
private lemma norm_hermPart_apply_le (N : Matrix n n ℂ) (i j : n) :
    ‖hermPart N i j‖ ≤ (‖N i j‖ + ‖N j i‖) / 2 := by
  have h : hermPart N i j = (2⁻¹ : ℝ) • (N i j + star (N j i)) := by
    change (realPart N : Matrix n n ℂ) i j = _
    rw [realPart_apply_coe]
    rfl
  rw [h, norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 2⁻¹)]
  calc 2⁻¹ * ‖N i j + star (N j i)‖ ≤ 2⁻¹ * (‖N i j‖ + ‖star (N j i)‖) :=
        mul_le_mul_of_nonneg_left (norm_add_le _ _) (by norm_num)
    _ = (‖N i j‖ + ‖N j i‖) / 2 := by rw [norm_star]; ring

omit [Fintype n] [DecidableEq n] in
/-- A concave function on the positive-definite cone lies below an affine function touching it at
a given positive-definite matrix. -/
private lemma exists_affine_majorant_posDef [Finite n] {f : Matrix n n ℂ → ℝ}
    (hf : ConcaveOn ℝ {A : Matrix n n ℂ | A.PosDef} f) {A₀ : Matrix n n ℂ} (hA₀ : A₀.PosDef) :
    ∃ ℓ : Matrix n n ℂ →ₗ[ℝ] ℝ, ∀ A : Matrix n n ℂ, A.PosDef → f A ≤ f A₀ + (ℓ A - ℓ A₀) := by
  classical
  have := Fintype.ofFinite n
  let _ : NormedAddCommGroup (Matrix n n ℂ) := Matrix.normedAddCommGroup
  let _ : NormedSpace ℝ (Matrix n n ℂ) := Matrix.normedSpace
  set U : Set (Matrix n n ℂ) := hermPart ⁻¹' {A | A.PosDef}
  have hU : IsOpen U := by
    refine Metric.isOpen_iff.2 fun A hA => ?_
    obtain ⟨ε, hε, hε'⟩ := exists_posDef_add (show (hermPart A).PosDef from hA)
    set d : ℝ := (Fintype.card n : ℝ)
    refine ⟨Real.sqrt ε / (d + 1), by positivity, fun B hB => ?_⟩
    rw [Metric.mem_ball, dist_eq_norm] at hB
    have hsplit : hermPart B = hermPart A + hermPart (B - A) := by
      rw [map_sub]; abel
    change (hermPart B).PosDef
    rw [hsplit]
    refine hε' _ (realPart (B - A)).2 ?_
    have hentry : ∀ i j, ‖hermPart (B - A) i j‖ ≤ ‖B - A‖ := fun i j =>
      (norm_hermPart_apply_le _ i j).trans (by
        linarith [Matrix.norm_apply_le_norm (B - A) (i := i) (j := j),
          Matrix.norm_apply_le_norm (B - A) (i := j) (j := i)])
    have hsq : ∀ i j, ‖hermPart (B - A) i j‖ ^ 2 ≤ ‖B - A‖ ^ 2 := fun i j =>
      pow_le_pow_left₀ (norm_nonneg _) (hentry i j) 2
    calc ∑ i, ∑ j, ‖hermPart (B - A) i j‖ ^ 2 ≤ ∑ _i : n, ∑ _j : n, ‖B - A‖ ^ 2 :=
          Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hsq i j
      _ = d ^ 2 * ‖B - A‖ ^ 2 := by simp [d]; ring
      _ < ε := by
        have hd : 0 ≤ d := by positivity
        have h1 : ‖B - A‖ * (d + 1) < Real.sqrt ε := (lt_div_iff₀ (by positivity)).1 hB
        have h2 : (‖B - A‖ * (d + 1)) ^ 2 < ε := by
          calc (‖B - A‖ * (d + 1)) ^ 2 < Real.sqrt ε ^ 2 :=
                pow_lt_pow_left₀ h1 (by positivity) two_ne_zero
            _ = ε := Real.sq_sqrt hε.le
        nlinarith [sq_nonneg ‖B - A‖, norm_nonneg (B - A)]
  have hFc : ConcaveOn ℝ U (f ∘ hermPart) := hf.comp_linearMap hermPart
  have hA₀U : A₀ ∈ U := by
    change (realPart A₀ : Matrix n n ℂ).PosDef
    rwa [hA₀.isHermitian.isSelfAdjoint.coe_realPart]
  obtain ⟨ℓ, hℓ⟩ := exists_le_add_of_concaveOn hU hFc hA₀U
  refine ⟨ℓ.toLinearMap, fun A hA => ?_⟩
  have hAU : A ∈ U := by
    change (realPart A : Matrix n n ℂ).PosDef
    rwa [hA.isHermitian.isSelfAdjoint.coe_realPart]
  have := hℓ A hAU
  have hP : ∀ B : Matrix n n ℂ, B.IsHermitian → hermPart B = B := fun B hB =>
    hB.isSelfAdjoint.coe_realPart
  simpa [hP A hA.isHermitian, hP A₀ hA₀.isHermitian, map_sub] using this

/-! ### Expectations -/

section Expect

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

omit [Fintype n] [DecidableEq n] in
/-- The entries of `expect μ M` are the integrals of the entries of `M`. -/
private lemma expect_apply (M : Ω → Matrix n n ℂ) (i j : n) :
    expect μ M i j = ∫ ω, M ω i j ∂μ := rfl

omit [Fintype n] [DecidableEq n] in
/-- The expectation of a Hermitian random matrix is Hermitian. -/
private lemma expect_isHermitian {M : Ω → Matrix n n ℂ} (hM : ∀ ω, (M ω).IsHermitian) :
    (expect μ M).IsHermitian := by
  ext i j
  simp only [Matrix.conjTranspose_apply, expect_apply, RCLike.star_def]
  rw [← integral_conj]
  exact integral_congr_ae (Filter.Eventually.of_forall fun ω => (hM ω).apply i j)

/-- The quadratic form `M ↦ re (x* M x)` as an `ℝ`-linear functional. -/
private noncomputable def quadForm (x : n → ℂ) : Matrix n n ℂ →ₗ[ℝ] ℝ where
  toFun M := RCLike.re (star x ⬝ᵥ (M *ᵥ x))
  map_add' A B := by simp [Matrix.add_mulVec, dotProduct_add]
  map_smul' c A := by
    simp only [RingHom.id_apply, smul_eq_mul]
    rw [Matrix.smul_mulVec, dotProduct_smul]
    simp

omit [DecidableEq n] in
/-- Evaluation of `quadForm`. -/
private lemma quadForm_apply (x : n → ℂ) (M : Matrix n n ℂ) :
    quadForm x M = RCLike.re (star x ⬝ᵥ (M *ᵥ x)) := rfl

omit [DecidableEq n] in
/-- A Hermitian matrix whose quadratic form has positive real part at every nonzero vector is
positive definite. -/
private lemma posDef_of_re_pos {A : Matrix n n ℂ} (hA : A.IsHermitian)
    (h : ∀ x : n → ℂ, x ≠ 0 → 0 < quadForm x A) : A.PosDef :=
  .of_dotProduct_mulVec_pos hA fun x hx =>
    RCLike.pos_iff.2 ⟨h x hx, hA.im_star_dotProduct_mulVec_self x⟩

omit [DecidableEq n] in
/-- A Hermitian matrix whose quadratic form has nonnegative real part is positive semidefinite. -/
private lemma posSemidef_of_re_nonneg {A : Matrix n n ℂ} (hA : A.IsHermitian)
    (h : ∀ x : n → ℂ, 0 ≤ quadForm x A) : A.PosSemidef :=
  .of_dotProduct_mulVec_nonneg hA fun x =>
    RCLike.nonneg_iff.2 ⟨h x, hA.im_star_dotProduct_mulVec_self x⟩

omit [Fintype n] [DecidableEq n] in
/-- The expectation of an integrable positive-definite random matrix is positive definite. -/
private lemma expect_posDef [Finite n] {M : Ω → Matrix n n ℂ}
    (hint : ∀ i j, Integrable (fun ω => M ω i j) μ)
    (hM : ∀ ω, (M ω).PosDef) : (expect μ M).PosDef := by
  have := Fintype.ofFinite n
  refine posDef_of_re_pos (expect_isHermitian fun ω => (hM ω).isHermitian) fun x hx => ?_
  obtain ⟨hi, he⟩ := integrable_and_integral_linearMap (quadForm x) hint
  rw [← he]
  have hpos : ∀ ω, 0 < quadForm x (M ω) := fun ω => by
    rw [quadForm_apply]; exact (hM ω).re_dotProduct_pos hx
  rw [integral_pos_iff_support_of_nonneg (fun ω => (hpos ω).le) hi]
  have : Function.support (fun ω => quadForm x (M ω)) = Set.univ :=
    Set.eq_univ_of_forall fun ω => (hpos ω).ne'
  simp [this]

omit [Fintype n] [DecidableEq n] in
/-- The expectation of an integrable positive-semidefinite random matrix is positive
semidefinite. -/
private lemma expect_posSemidef [Finite n] {M : Ω → Matrix n n ℂ}
    (hint : ∀ i j, Integrable (fun ω => M ω i j) μ)
    (hM : ∀ ω, (M ω).PosSemidef) : (expect μ M).PosSemidef := by
  have := Fintype.ofFinite n
  refine posSemidef_of_re_nonneg (expect_isHermitian fun ω => (hM ω).isHermitian) fun x => ?_
  obtain ⟨hi, he⟩ := integrable_and_integral_linearMap (quadForm x) hint
  rw [← he]
  exact integral_nonneg fun ω => by
    rw [Pi.zero_apply, quadForm_apply]; exact (hM ω).re_dotProduct_nonneg x

omit [Fintype n] [DecidableEq n] in
/-- Expectation is additive on integrable random matrices. -/
private lemma expect_add {M M' : Ω → Matrix n n ℂ} (hM : ∀ i j, Integrable (fun ω => M ω i j) μ)
    (hM' : ∀ i j, Integrable (fun ω => M' ω i j) μ) :
    expect μ (fun ω => M ω + M' ω) = expect μ M + expect μ M' := by
  ext i j
  simp only [expect_apply, Matrix.add_apply]
  exact integral_add (hM i j) (hM' i j)

omit [Fintype n] [DecidableEq n] in
/-- Expectation commutes with subtraction of integrable random matrices. -/
private lemma expect_sub {M M' : Ω → Matrix n n ℂ} (hM : ∀ i j, Integrable (fun ω => M ω i j) μ)
    (hM' : ∀ i j, Integrable (fun ω => M' ω i j) μ) :
    expect μ (fun ω => M ω - M' ω) = expect μ M - expect μ M' := by
  ext i j
  simp only [expect_apply, Matrix.sub_apply]
  exact integral_sub (hM i j) (hM' i j)

omit [Fintype n] [DecidableEq n] in
/-- Expectation commutes with multiplication by a real constant. -/
private lemma expect_smul (c : ℝ) (M : Ω → Matrix n n ℂ) :
    expect μ (fun ω => c • M ω) = c • expect μ M := by
  ext i j
  simp only [expect_apply, Matrix.smul_apply]
  exact integral_smul c _

omit [Fintype n] [DecidableEq n] in
/-- The expectation of a constant random matrix is that matrix. -/
private lemma expect_const (A : Matrix n n ℂ) : expect μ (fun _ => A) = A := by
  ext i j
  simp [expect_apply]

omit [Fintype n] [DecidableEq n] in
/-- Expectation commutes with finite sums of integrable random matrices. -/
private lemma expect_sum {ι : Type*} (s : Finset ι) {M : ι → Ω → Matrix n n ℂ}
    (hM : ∀ k i j, Integrable (fun ω => M k ω i j) μ) :
    expect μ (fun ω => ∑ k ∈ s, M k ω) = ∑ k ∈ s, expect μ (M k) := by
  ext i j
  simp only [expect_apply, Matrix.sum_apply]
  exact integral_finsetSum s fun k _ => hM k i j

omit [Fintype n] [DecidableEq n] in
/-- Expectation preserves the semidefinite order on integrable random matrices. -/
private lemma expect_mono [Finite n] {M M' : Ω → Matrix n n ℂ}
    (hM : ∀ i j, Integrable (fun ω => M ω i j) μ)
    (hM' : ∀ i j, Integrable (fun ω => M' ω i j) μ) (h : ∀ ω, M ω ≤ M' ω) :
    expect μ M ≤ expect μ M' := by
  rw [Matrix.le_iff, ← expect_sub hM' hM]
  exact expect_posSemidef (fun i j => (hM' i j).sub (hM i j)) fun ω => Matrix.le_iff.1 (h ω)

end Expect

/-! ### Jensen's inequality for Lieb's function, and the iteration over independent summands -/

section Iteration

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- Tropp, Corollary 3.4.2, in `lintegral` form. -/
private lemma lintegral_re_trace_exp_add_le {Z : Ω → Matrix n n ℂ} (hZ : ∀ ω, (Z ω).IsHermitian)
    (hint : ∀ i j, Integrable (fun ω => NormedSpace.exp (Z ω) i j) μ)
    {H : Matrix n n ℂ} (hH : H.IsHermitian) :
    ∫⁻ ω, ENNReal.ofReal (RCLike.re (NormedSpace.exp (H + Z ω)).trace) ∂μ ≤
      ENNReal.ofReal (RCLike.re (NormedSpace.exp
        (H + cfc Real.log (expect μ fun ω => NormedSpace.exp (Z ω)))).trace) := by
  set Y : Ω → Matrix n n ℂ := fun ω => NormedSpace.exp (Z ω)
  have hYpd : ∀ ω, (Y ω).PosDef := fun ω => posDef_exp (hZ ω)
  set A₀ := expect μ Y
  have hA₀ : A₀.PosDef := expect_posDef hint hYpd
  set f : Matrix n n ℂ → ℝ := fun A => RCLike.re (NormedSpace.exp (H + cfc Real.log A)).trace
  obtain ⟨ℓ, hℓ⟩ := exists_affine_majorant_posDef
    (MathlibExt.LinearAlgebra.Matrix.LiebConcavityWanted.lieb_concavity hH) hA₀
  obtain ⟨hℓi, hℓe⟩ := integrable_and_integral_linearMap ℓ hint
  have hpt : ∀ ω, RCLike.re (NormedSpace.exp (H + Z ω)).trace ≤ f A₀ + (ℓ (Y ω) - ℓ A₀) := by
    intro ω
    have := hℓ (Y ω) (hYpd ω)
    simpa only [f, Y, cfc_log_exp (hZ ω)] using this
  have hnn : ∀ ω, 0 ≤ f A₀ + (ℓ (Y ω) - ℓ A₀) := fun ω =>
    (re_trace_exp_nonneg_of_isHermitian (hH.add (hZ ω))).trans (hpt ω)
  have h2 : Integrable (fun ω => ℓ (Y ω) - ℓ A₀) μ := hℓi.sub (integrable_const _)
  have hi : Integrable (fun ω => f A₀ + (ℓ (Y ω) - ℓ A₀)) μ := (integrable_const _).add h2
  calc ∫⁻ ω, ENNReal.ofReal (RCLike.re (NormedSpace.exp (H + Z ω)).trace) ∂μ
      ≤ ∫⁻ ω, ENNReal.ofReal (f A₀ + (ℓ (Y ω) - ℓ A₀)) ∂μ :=
        lintegral_mono fun ω => ENNReal.ofReal_le_ofReal (hpt ω)
    _ = ENNReal.ofReal (∫ ω, (f A₀ + (ℓ (Y ω) - ℓ A₀)) ∂μ) :=
        (ofReal_integral_eq_lintegral_ofReal hi (Filter.Eventually.of_forall hnn)).symm
    _ = ENNReal.ofReal (f A₀) := by
        rw [integral_add (integrable_const _) h2, integral_sub hℓi (integrable_const _), hℓe]
        simp only [integral_const, probReal_univ, one_smul]
        change ENNReal.ofReal (f A₀ + (ℓ A₀ - ℓ A₀)) = _
        rw [sub_self, add_zero]

omit [Fintype n] [DecidableEq n] in
/-- The Hermitian part is continuous. -/
private lemma continuous_hermPart : Continuous (hermPart : Matrix n n ℂ → Matrix n n ℂ) :=
  continuous_subtype_val.comp (selfAdjointPartL ℝ (Matrix n n ℂ)).continuous

/-- The iteration over independent summands (Tropp, proof of Lemma 3.5.1). -/
private lemma lintegral_re_trace_exp_add_sum_le {ι : Type*} {Z : ι → Ω → Matrix n n ℂ}
    (hmeas : ∀ k, Measurable (Z k)) (hind : iIndepFun Z μ) (hZ : ∀ k ω, (Z k ω).IsHermitian)
    {C : ι → Matrix n n ℂ} (hC : ∀ k, (C k).IsHermitian)
    (hstep : ∀ k (H : Matrix n n ℂ), H.IsHermitian →
      ∫⁻ ω, ENNReal.ofReal (RCLike.re (NormedSpace.exp (H + Z k ω)).trace) ∂μ ≤
        ENNReal.ofReal (RCLike.re (NormedSpace.exp (H + C k)).trace))
    (S : Finset ι) {H : Matrix n n ℂ} (hH : H.IsHermitian) :
    ∫⁻ ω, ENNReal.ofReal (RCLike.re (NormedSpace.exp (H + ∑ k ∈ S, Z k ω)).trace) ∂μ ≤
      ENNReal.ofReal (RCLike.re (NormedSpace.exp (H + ∑ k ∈ S, C k)).trace) := by
  classical
  induction S using Finset.induction_on generalizing H with
  | empty => simp [lintegral_const, measure_univ]
  | insert j S hj ih =>
    set W : Ω → Matrix n n ℂ := fun ω => ∑ k ∈ S, Z k ω
    have hWm : Measurable W := Finset.measurable_sum S fun k _ => hmeas k
    have hWh : ∀ ω, (W ω).IsHermitian := fun ω => isSelfAdjoint_sum _ fun k _ => hZ k ω
    have hindep : IndepFun W (Z j) μ := by
      have := hind.indepFun_finsetSum_of_notMem hmeas hj
      convert this using 1
      ext ω
      simp [W, Finset.sum_apply]
    have hmap := (indepFun_iff_map_prod_eq_prod_map_map hWm.aemeasurable
      (hmeas j).aemeasurable).1 hindep
    set g : Matrix n n ℂ × Matrix n n ℂ → ENNReal := fun p =>
      ENNReal.ofReal (RCLike.re (NormedSpace.exp (H + hermPart p.1 + p.2)).trace)
    have hgc : Continuous g := ENNReal.continuous_ofReal.comp (continuous_re_trace_exp.comp
      ((continuous_const.add (continuous_hermPart.comp continuous_fst)).add continuous_snd))
    have hg : Measurable g := hgc.measurable
    have hPW : ∀ ω, hermPart (W ω) = W ω := fun ω => (hWh ω).isSelfAdjoint.coe_realPart
    calc ∫⁻ ω, ENNReal.ofReal (RCLike.re (NormedSpace.exp (H + ∑ k ∈ insert j S, Z k ω)).trace) ∂μ
        = ∫⁻ ω, g (W ω, Z j ω) ∂μ := by
          refine lintegral_congr fun ω => ?_
          simp only [g, hPW, W, Finset.sum_insert hj]
          congr 4
          abel
      _ = ∫⁻ p, g p ∂(μ.map fun ω => (W ω, Z j ω)) :=
          (lintegral_map hg (hWm.prodMk (hmeas j))).symm
      _ = ∫⁻ w, ∫⁻ z, g (w, z) ∂(μ.map (Z j)) ∂(μ.map W) := by
          rw [hmap, lintegral_prod _ hg.aemeasurable]
      _ ≤ ∫⁻ w, ENNReal.ofReal (RCLike.re (NormedSpace.exp (H + hermPart w + C j)).trace)
            ∂(μ.map W) := by
          refine lintegral_mono fun w => ?_
          rw [lintegral_map (f := fun z => g (w, z)) (hg.comp measurable_prodMk_left) (hmeas j)]
          exact hstep j (H + hermPart w) (hH.add (realPart w).2)
      _ = ∫⁻ ω, ENNReal.ofReal (RCLike.re (NormedSpace.exp ((H + C j) + W ω)).trace) ∂μ := by
          rw [lintegral_map (f := fun w => ENNReal.ofReal (RCLike.re
            (NormedSpace.exp (H + hermPart w + C j)).trace))
            (ENNReal.continuous_ofReal.comp (continuous_re_trace_exp.comp
            ((continuous_const.add continuous_hermPart).add continuous_const))).measurable hWm]
          refine lintegral_congr fun ω => ?_
          simp only [hPW]
          congr 4
          abel
      _ ≤ ENNReal.ofReal (RCLike.re (NormedSpace.exp (H + C j + ∑ k ∈ S, C k)).trace) :=
          ih (hH.add (hC j))
      _ = ENNReal.ofReal (RCLike.re (NormedSpace.exp (H + ∑ k ∈ insert j S, C k)).trace) := by
          rw [Finset.sum_insert hj, add_assoc]

/-- The master bound: per-summand bounds iterate to a bound on the trace mgf of the sum. -/
private lemma integrable_and_integral_le_of_forall {N : ℕ} {X : Fin N → Ω → Matrix n n ℂ}
    (hmeas : ∀ k, Measurable (X k)) (hind : iIndepFun X μ) (hX : ∀ k ω, (X k ω).IsHermitian)
    {θ : ℝ} {C : Fin N → Matrix n n ℂ} (hC : ∀ k, (C k).IsHermitian)
    (hstep : ∀ k (H : Matrix n n ℂ), H.IsHermitian →
      ∫⁻ ω, ENNReal.ofReal (RCLike.re (NormedSpace.exp (H + θ • X k ω)).trace) ∂μ ≤
        ENNReal.ofReal (RCLike.re (NormedSpace.exp (H + C k)).trace)) :
    Integrable (traceMgf (fun ω => ∑ k, X k ω) θ) μ ∧
      ∫ ω, traceMgf (fun ω => ∑ k, X k ω) θ ω ∂μ ≤
        RCLike.re (NormedSpace.exp (∑ k, C k)).trace := by
  have hsm : Continuous fun M : Matrix n n ℂ => θ • M := continuous_const_smul θ
  have hindZ : iIndepFun (fun k ω => θ • X k ω) μ :=
    hind.comp (fun _ M => θ • M) fun _ => hsm.measurable
  have hlin := lintegral_re_trace_exp_add_sum_le (Z := fun k ω => θ • X k ω)
    (fun k => hsm.measurable.comp (hmeas k)) hindZ
    (fun k ω => (IsSelfAdjoint.all θ).smul (hX k ω)) hC hstep Finset.univ
    (Matrix.isHermitian_zero)
  simp only [zero_add, ← Finset.smul_sum] at hlin
  have hF : Measurable (traceMgf (fun ω => ∑ k, X k ω) θ) :=
    continuous_re_trace_exp.measurable.comp (hsm.measurable.comp
      (Finset.measurable_sum _ fun k _ => hmeas k))
  have hnn : 0 ≤ᵐ[μ] traceMgf (fun ω => ∑ k, X k ω) θ := Filter.Eventually.of_forall fun ω =>
    re_trace_exp_nonneg_of_isHermitian
      ((IsSelfAdjoint.all θ).smul (isSelfAdjoint_sum _ fun k _ => hX k ω))
  refine ⟨⟨hF.aestronglyMeasurable, (hasFiniteIntegral_iff_ofReal hnn).2
    (hlin.trans_lt ENNReal.ofReal_lt_top)⟩, ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae hnn hF.aestronglyMeasurable]
  exact ENNReal.toReal_le_of_le_ofReal (re_trace_exp_nonneg_of_isHermitian (isSelfAdjoint_sum _
    fun k _ => hC k)) hlin

end Iteration

/-! ### Subadditivity of matrix cgfs -/

/-- **Subadditivity of matrix cumulant generating functions** (Tropp, *An Introduction to Matrix
Concentration Inequalities*, arXiv:1501.01571, Lemma 3.5.1, display (3.5.1); Tropp,
*User-friendly tail bounds for sums of random matrices*, Found. Comput. Math. 12 (2012),
Lemma 3.4). For independent random Hermitian matrices `X₀, …, X_{N-1}` with integrable
`e^{θ X_k}` and integrable `tr e^{θ ∑ X_k}`,
`E tr exp(∑ₖ θ X_k) ≤ tr exp(∑ₖ log E e^{θ X_k})`. -/
theorem integral_trace_exp_sum_le {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {N : ℕ} {X : Fin N → Ω → Matrix n n ℂ}
    (hmeas : ∀ k, Measurable (X k)) (hind : iIndepFun X μ)
    (hX : ∀ k ω, (X k ω).IsHermitian) (θ : ℝ)
    (hexp : ∀ k i j, Integrable (fun ω => NormedSpace.exp (θ • X k ω) i j) μ)
    (hsum : Integrable (fun ω => RCLike.re (NormedSpace.exp (θ • ∑ k, X k ω)).trace) μ) :
    ∫ ω, RCLike.re (NormedSpace.exp (θ • ∑ k, X k ω)).trace ∂μ ≤
      RCLike.re (NormedSpace.exp
        (∑ k, cfc Real.log (expect μ fun ω => NormedSpace.exp (θ • X k ω)))).trace := by
  have hsm : Continuous fun M : Matrix n n ℂ => θ • M := continuous_const_smul θ
  have hlin := lintegral_re_trace_exp_add_sum_le (Z := fun k ω => θ • X k ω)
    (fun k => hsm.measurable.comp (hmeas k)) (hind.comp (fun _ M => θ • M) fun _ => hsm.measurable)
    (fun k ω => (IsSelfAdjoint.all θ).smul (hX k ω)) (fun k => cfc_predicate _ _)
    (fun k H hH => lintegral_re_trace_exp_add_le (fun ω => (IsSelfAdjoint.all θ).smul (hX k ω))
      (hexp k) hH) Finset.univ Matrix.isHermitian_zero
  simp only [zero_add, ← Finset.smul_sum] at hlin
  have hnn : 0 ≤ᵐ[μ] fun ω => RCLike.re (NormedSpace.exp (θ • ∑ k, X k ω)).trace :=
    Filter.Eventually.of_forall fun ω => re_trace_exp_nonneg_of_isHermitian
      ((IsSelfAdjoint.all θ).smul (isSelfAdjoint_sum _ fun k _ => hX k ω))
  rw [integral_eq_lintegral_of_nonneg_ae hnn hsum.aestronglyMeasurable]
  exact ENNReal.toReal_le_of_le_ofReal (re_trace_exp_nonneg_of_isHermitian (isSelfAdjoint_sum _
    fun k _ => cfc_predicate _ _)) hlin

/-! ### Tools for the tail bounds -/

section Tools

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- Corollary 3.4.2 followed by the monotonicity of Lieb's function. -/
private lemma lintegral_re_trace_exp_add_le_of_le {Z : Ω → Matrix n n ℂ}
    (hZ : ∀ ω, (Z ω).IsHermitian)
    (hint : ∀ i j, Integrable (fun ω => NormedSpace.exp (Z ω) i j) μ)
    {C : Matrix n n ℂ} (hC : C.IsHermitian)
    (hle : expect μ (fun ω => NormedSpace.exp (Z ω)) ≤ NormedSpace.exp C)
    {H : Matrix n n ℂ} (hH : H.IsHermitian) :
    ∫⁻ ω, ENNReal.ofReal (RCLike.re (NormedSpace.exp (H + Z ω)).trace) ∂μ ≤
      ENNReal.ofReal (RCLike.re (NormedSpace.exp (H + C)).trace) := by
  refine (lintegral_re_trace_exp_add_le hZ hint hH).trans (ENNReal.ofReal_le_ofReal ?_)
  have := lieb_mono hH (expect_posDef hint fun ω => posDef_exp (hZ ω)) (Matrix.le_iff.1 hle)
  rwa [cfc_log_exp hC] at this

/-- For Hermitian `M` and `θ ≥ 0`, `tr e^{θM} ≤ d e^{θ λmax(M)}`. -/
private lemma re_trace_exp_smul_le_lambdaMax [Nonempty n] {M : Matrix n n ℂ} (hM : M.IsHermitian)
    {θ : ℝ} (hθ : 0 ≤ θ) :
    RCLike.re (NormedSpace.exp (θ • M)).trace ≤ Fintype.card n * Real.exp (θ * hM.lambdaMax) := by
  rw [hM.re_trace_exp_smul_eq_sum θ]
  calc ∑ i, Real.exp (θ * hM.eigenvalues i) ≤ ∑ _i : n, Real.exp (θ * hM.lambdaMax) :=
        Finset.sum_le_sum fun i _ => Real.exp_le_exp.mpr
          (mul_le_mul_of_nonneg_left (hM.eigenvalues_le_lambdaMax i) hθ)
    _ = _ := by simp

/-- For Hermitian `M` and `θ ≤ 0`, `tr e^{θM} ≤ d e^{θ λmin(M)}`. -/
private lemma re_trace_exp_smul_le_lambdaMin [Nonempty n] {M : Matrix n n ℂ} (hM : M.IsHermitian)
    {θ : ℝ} (hθ : θ ≤ 0) :
    RCLike.re (NormedSpace.exp (θ • M)).trace ≤ Fintype.card n * Real.exp (θ * hM.lambdaMin) := by
  rw [hM.re_trace_exp_smul_eq_sum θ]
  calc ∑ i, Real.exp (θ * hM.eigenvalues i) ≤ ∑ _i : n, Real.exp (θ * hM.lambdaMin) :=
        Finset.sum_le_sum fun i _ => Real.exp_le_exp.mpr
          (mul_le_mul_of_nonpos_left (hM.lambdaMin_le_eigenvalues i) hθ)
    _ = _ := by simp

/-- The real spectrum of a Hermitian matrix lies in `[λmin, λmax]`. -/
private lemma mem_spectrum_bounds [Nonempty n] {M : Matrix n n ℂ} (hM : M.IsHermitian) {x : ℝ}
    (hx : x ∈ spectrum ℝ M) : hM.lambdaMin ≤ x ∧ x ≤ hM.lambdaMax := by
  rw [hM.spectrum_real_eq_range_eigenvalues] at hx
  obtain ⟨i, rfl⟩ := hx
  exact ⟨hM.lambdaMin_le_eigenvalues i, hM.eigenvalues_le_lambdaMax i⟩

/-- Entries of a Hermitian matrix are bounded through its eigenvalues. -/
private lemma norm_apply_sq_le_of_eigenvalues {M : Matrix n n ℂ} (hM : M.IsHermitian) {R : ℝ}
    (hR : ∀ i, |hM.eigenvalues i| ≤ R) (i j : n) :
    ‖M i j‖ ^ 2 ≤ Fintype.card n * R ^ 2 := by
  have h1 := norm_apply_sq_le hM i j
  rw [re_trace_mul_self_eq hM, ← sum_eigenvalues_sq hM] at h1
  refine h1.trans ?_
  calc ∑ k, hM.eigenvalues k ^ 2 ≤ ∑ _k : n, R ^ 2 := Finset.sum_le_sum fun k _ => by
        rw [← sq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) (hR k) 2
    _ = _ := by simp

/-- Entries of `e^{θM}` are bounded through the eigenvalues of `M`. -/
private lemma norm_exp_smul_apply_sq_le {M : Matrix n n ℂ} (hM : M.IsHermitian) (θ : ℝ) {B : ℝ}
    (hB : ∀ i, Real.exp (2 * θ * hM.eigenvalues i) ≤ B) (i j : n) :
    ‖NormedSpace.exp (θ • M) i j‖ ^ 2 ≤ Fintype.card n * B := by
  have hE : (NormedSpace.exp (θ • M)).IsHermitian := Matrix.IsHermitian.exp
    ((IsSelfAdjoint.all θ).smul hM)
  have h1 := norm_apply_sq_le hE i j
  rw [← Matrix.exp_add_of_commute _ _ (Commute.refl _), ← add_smul, ← two_mul,
    hM.re_trace_exp_smul_eq_sum] at h1
  refine h1.trans ?_
  calc ∑ k, Real.exp (2 * θ * hM.eigenvalues k) ≤ ∑ _k : n, B := Finset.sum_le_sum fun k _ => hB k
    _ = _ := by simp

omit [Fintype n] [DecidableEq n] in
/-- A measurable random matrix with uniformly bounded entries has integrable entries. -/
private lemma integrable_apply_of_bound {M : Ω → Matrix n n ℂ} (hM : Measurable M) {K : ℝ}
    (hK : ∀ ω i j, ‖M ω i j‖ ^ 2 ≤ K) (i j : n) : Integrable (fun ω => M ω i j) μ :=
  Integrable.of_bound (hM.eval_matrix).aestronglyMeasurable (Real.sqrt K)
    (Filter.Eventually.of_forall fun ω => Real.le_sqrt_of_sq_le (hK ω i j))

/-- `ω ↦ e^{θ M(ω)}` is measurable when `M` is. -/
private lemma measurable_exp_smul {M : Ω → Matrix n n ℂ} (hM : Measurable M) (θ : ℝ) :
    Measurable fun ω => NormedSpace.exp (θ • M ω) :=
  continuous_exp_matrix.measurable.comp ((continuous_const_smul θ).measurable.comp hM)

/-- The functional calculus of a quadratic polynomial. -/
private lemma cfc_quadratic {M : Matrix n n ℂ} (hM : M.IsHermitian) (a b c : ℝ) :
    cfc (fun x => a + b * x + c * x ^ 2) M = algebraMap ℝ _ a + b • M + c • (M * M) := by
  rw [cfc_add .., cfc_add .., cfc_const a M, cfc_const_mul_id b M, cfc_const_mul .., cfc_pow_id M 2,
    sq]

/-- Transfer rule: `e^{θx} ≤ g(x)` on the spectrum of a Hermitian `M` gives `e^{θM} ≼ g(M)`. -/
private lemma exp_smul_le_of_forall {M : Matrix n n ℂ} (hM : M.IsHermitian) (θ : ℝ) {g : ℝ → ℝ}
    (hg : Continuous g) (h : ∀ x ∈ spectrum ℝ M, Real.exp (θ * x) ≤ g x) :
    NormedSpace.exp (θ • M) ≤ cfc g M := by
  rw [hM.exp_smul_eq_cfc θ]
  exact cfc_mono h

end Tools

/-! ### Matrix Chernoff -/

section Chernoff

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- The chord bound `e^{θx} ≤ 1 + (e^{θL} - 1) x / L` for `0 ≤ x ≤ L` (Tropp,
arXiv:1501.01571v1, proof of Lemma 5.4.1). -/
private lemma exp_mul_le_chord {θ L x : ℝ} (hL : 0 < L) (hx0 : 0 ≤ x) (hxL : x ≤ L) :
    Real.exp (θ * x) ≤ 1 + (Real.exp (θ * L) - 1) / L * x := by
  have h := convexOn_exp.2 (Set.mem_univ 0) (Set.mem_univ (θ * L))
    (by rw [sub_nonneg, div_le_one hL]; exact hxL : (0 : ℝ) ≤ 1 - x / L)
    (div_nonneg hx0 hL.le) (by ring)
  simp only [smul_eq_mul, mul_zero, zero_add, Real.exp_zero, mul_one] at h
  have e : x / L * (θ * L) = θ * x := by field_simp
  rw [e] at h
  calc Real.exp (θ * x) ≤ 1 - x / L + x / L * Real.exp (θ * L) := h
    _ = 1 + (Real.exp (θ * L) - 1) / L * x := by field_simp; ring

/-- The functional calculus of an affine function. -/
private lemma cfc_affine {M : Matrix n n ℂ} (hM : M.IsHermitian) (a b : ℝ) :
    cfc (fun x => a + b * x) M = algebraMap ℝ _ a + b • M := by
  rw [cfc_add .., cfc_const a M, cfc_const_mul_id b M]

/-- A random Hermitian matrix with eigenvalues in `[-L, L]` has integrable entries. -/
private lemma integrable_apply_of_eigenvalues [Nonempty n] {X : Ω → Matrix n n ℂ}
    (hm : Measurable X)
    (hX : ∀ ω, (X ω).IsHermitian) {L : ℝ} (hlow : ∀ ω, -L ≤ (hX ω).lambdaMin)
    (hup : ∀ ω, (hX ω).lambdaMax ≤ L) (i j : n) : Integrable (fun ω => X ω i j) μ :=
  integrable_apply_of_bound hm (fun ω i j => norm_apply_sq_le_of_eigenvalues (hX ω)
    (fun k => abs_le.2 ⟨(hlow ω).trans ((hX ω).lambdaMin_le_eigenvalues k),
      ((hX ω).eigenvalues_le_lambdaMax k).trans (hup ω)⟩) i j) i j

/-- If `λmax(X) ≤ L` and `θ ≥ 0`, then `e^{θX}` has integrable entries. -/
private lemma integrable_exp_smul_apply_of_le [Nonempty n] {X : Ω → Matrix n n ℂ}
    (hm : Measurable X)
    (hX : ∀ ω, (X ω).IsHermitian) {L : ℝ} (hup : ∀ ω, (hX ω).lambdaMax ≤ L) {θ : ℝ}
    (hθ : 0 ≤ θ) (i j : n) : Integrable (fun ω => NormedSpace.exp (θ • X ω) i j) μ :=
  integrable_apply_of_bound (measurable_exp_smul hm θ) (fun ω i j =>
    norm_exp_smul_apply_sq_le (hX ω) θ (B := Real.exp (2 * θ * L)) (fun k => Real.exp_le_exp.2
      (mul_le_mul_of_nonneg_left (((hX ω).eigenvalues_le_lambdaMax k).trans (hup ω))
        (by positivity))) i j) i j

/-- If the eigenvalues of `X` lie in `[-L, L]`, then `e^{θX}` has integrable entries. -/
private lemma integrable_exp_smul_apply_of_bounded [Nonempty n] {X : Ω → Matrix n n ℂ}
    (hm : Measurable X) (hX : ∀ ω, (X ω).IsHermitian) {L : ℝ}
    (hlow : ∀ ω, -L ≤ (hX ω).lambdaMin) (hup : ∀ ω, (hX ω).lambdaMax ≤ L) (θ : ℝ) (i j : n) :
    Integrable (fun ω => NormedSpace.exp (θ • X ω) i j) μ :=
  integrable_apply_of_bound (measurable_exp_smul hm θ) (fun ω i j =>
    norm_exp_smul_apply_sq_le (hX ω) θ (B := Real.exp (2 * (|θ| * L))) (fun k => by
      refine Real.exp_le_exp.2 ?_
      have hk : |(hX ω).eigenvalues k| ≤ L := abs_le.2
        ⟨(hlow ω).trans ((hX ω).lambdaMin_le_eigenvalues k),
          ((hX ω).eigenvalues_le_lambdaMax k).trans (hup ω)⟩
      have := (le_abs_self (θ * (hX ω).eigenvalues k)).trans
        ((abs_mul θ _).le.trans (mul_le_mul_of_nonneg_left hk (abs_nonneg θ)))
      linarith) i j) i j

/-- The Chernoff mgf bound (Tropp, Lemma 5.4.1): `E e^{θX} ≼ exp(g(θ) E X)`. -/
private lemma expect_exp_smul_le_chernoff [Nonempty n] {X : Ω → Matrix n n ℂ} (hm : Measurable X)
    (hX : ∀ ω, (X ω).IsHermitian) {L : ℝ} (hL : 0 < L) (hlow : ∀ ω, 0 ≤ (hX ω).lambdaMin)
    (hup : ∀ ω, (hX ω).lambdaMax ≤ L) (θ : ℝ) :
    expect μ (fun ω => NormedSpace.exp (θ • X ω)) ≤
      NormedSpace.exp (((Real.exp (θ * L) - 1) / L) • expect μ X) := by
  set g := (Real.exp (θ * L) - 1) / L
  have hlow' : ∀ ω, -L ≤ (hX ω).lambdaMin := fun ω => by linarith [hlow ω]
  have hXi := integrable_apply_of_eigenvalues (μ := μ) hm hX hlow' hup
  have hEi := integrable_exp_smul_apply_of_bounded (μ := μ) hm hX hlow' hup θ
  have hEX : (expect μ X).IsHermitian := expect_isHermitian hX
  have hpt : ∀ ω, NormedSpace.exp (θ • X ω) ≤ algebraMap ℝ _ 1 + g • X ω := fun ω => by
    rw [← cfc_affine (hX ω)]
    refine exp_smul_le_of_forall (hX ω) θ (by fun_prop) fun x hx => ?_
    obtain ⟨h0, h1⟩ := mem_spectrum_bounds (hX ω) hx
    exact exp_mul_le_chord hL ((hlow ω).trans h0) (h1.trans (hup ω))
  have hci : ∀ i j, Integrable (fun ω => (algebraMap ℝ (Matrix n n ℂ) 1 + g • X ω) i j) μ :=
    fun i j => (integrable_const _).add ((hXi i j).smul g)
  refine (expect_mono hEi hci hpt).trans ?_
  rw [expect_add (M := fun _ => algebraMap ℝ (Matrix n n ℂ) 1) (M' := fun ω => g • X ω)
    (fun i j => integrable_const _) (fun i j => (hXi i j).smul g), expect_const,
    expect_smul, ← cfc_affine hEX, hEX.exp_smul_eq_cfc g]
  exact cfc_mono fun x _ => by linarith [Real.add_one_le_exp (g * x)]

/-- **Matrix Chernoff inequality, tail bounds** (Tropp, *An Introduction to Matrix
Concentration Inequalities*, arXiv:1501.01571, Theorem 5.1.1, displays (5.1.5) and (5.1.6);
Tropp, *User-friendly tail bounds for sums of random matrices*, Found. Comput. Math. 12 (2012),
Theorem 1.1). Let `X₀, …, X_{N-1}` be independent random Hermitian `d × d` matrices with
`0 ≤ λmin(X_k)` and `λmax(X_k) ≤ L`, `L > 0`, let `Y = ∑ₖ X_k`, and let
`μmin = λmin(E Y)`, `μmax = λmax(E Y)`. Then for `ε ≥ 0`,
`P{λmax(Y) ≥ (1 + ε) μmax} ≤ d · [e^ε / (1 + ε)^{1+ε}]^{μmax / L}`, and for `0 ≤ ε < 1`,
`P{λmin(Y) ≤ (1 - ε) μmin} ≤ d · [e^{-ε} / (1 - ε)^{1-ε}]^{μmin / L}`. -/
theorem matrix_chernoff [Nonempty n] {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {N : ℕ} {X : Fin N → Ω → Matrix n n ℂ}
    (hmeas : ∀ k, Measurable (X k)) (hind : iIndepFun X μ)
    (hX : ∀ k ω, (X k ω).IsHermitian) {L : ℝ} (hL : 0 < L)
    (hlow : ∀ k ω, 0 ≤ (hX k ω).lambdaMin) (hup : ∀ k ω, (hX k ω).lambdaMax ≤ L)
    (hY : ∀ ω, (∑ k, X k ω).IsHermitian)
    (hEY : (expect μ fun ω => ∑ k, X k ω).IsHermitian) :
    (∀ ε : ℝ, 0 ≤ ε →
      μ.real {ω | (1 + ε) * hEY.lambdaMax ≤ (hY ω).lambdaMax} ≤
        Fintype.card n * (Real.exp ε / (1 + ε) ^ (1 + ε)) ^ (hEY.lambdaMax / L)) ∧
    (∀ ε : ℝ, 0 ≤ ε → ε < 1 →
      μ.real {ω | (hY ω).lambdaMin ≤ (1 - ε) * hEY.lambdaMin} ≤
        Fintype.card n * (Real.exp (-ε) / (1 - ε) ^ (1 - ε)) ^ (hEY.lambdaMin / L)) := by
  set EY := expect μ fun ω => ∑ k, X k ω
  have hlow' : ∀ k ω, -L ≤ (hX k ω).lambdaMin := fun k ω => by linarith [hlow k ω]
  have hXi : ∀ k i j, Integrable (fun ω => X k ω i j) μ := fun k =>
    integrable_apply_of_eigenvalues (hmeas k) (hX k) (hlow' k) (hup k)
  have hEsum : ∑ k, expect μ (X k) = EY := (expect_sum _ hXi).symm
  have hEXh : ∀ k, (expect μ (X k)).IsHermitian := fun k => expect_isHermitian (hX k)
  have hmaster : ∀ θ : ℝ, Integrable (traceMgf (fun ω => ∑ k, X k ω) θ) μ ∧
      ∫ ω, traceMgf (fun ω => ∑ k, X k ω) θ ω ∂μ ≤
        RCLike.re (NormedSpace.exp (((Real.exp (θ * L) - 1) / L) • EY)).trace := by
    intro θ
    have := integrable_and_integral_le_of_forall hmeas hind hX
      (C := fun k => ((Real.exp (θ * L) - 1) / L) • expect μ (X k))
      (fun k => (IsSelfAdjoint.all _).smul (hEXh k)) fun k H hH =>
        lintegral_re_trace_exp_add_le_of_le (fun ω => (IsSelfAdjoint.all θ).smul (hX k ω))
          (integrable_exp_smul_apply_of_bounded (hmeas k) (hX k) (hlow' k) (hup k) θ)
          ((IsSelfAdjoint.all _).smul (hEXh k))
          (expect_exp_smul_le_chernoff (hmeas k) (hX k) hL (hlow k) (hup k) θ) hH
    rwa [← Finset.smul_sum, hEsum] at this
  have hcard : (1 : ℝ) ≤ Fintype.card n := by exact_mod_cast Fintype.card_pos
  refine ⟨fun ε hε => ?_, fun ε hε hε1 => ?_⟩
  · rcases hε.eq_or_lt with rfl | hε'
    · simp only [Real.exp_zero, add_zero, Real.one_rpow, div_one, mul_one]
      exact measureReal_le_one.trans hcard
    set θ := Real.log (1 + ε) / L
    have hθ : 0 < θ := div_pos (Real.log_pos (by linarith)) hL
    obtain ⟨hi, hb⟩ := hmaster θ
    have h1 := measureReal_le_lambdaMax_le hY hθ hi ((1 + ε) * hEY.lambdaMax)
    have hg : (Real.exp (θ * L) - 1) / L = ε / L := by
      simp only [θ, div_mul_cancel₀ _ hL.ne', Real.exp_log (by linarith : (0 : ℝ) < 1 + ε)]
      ring
    have h2 := re_trace_exp_smul_le_lambdaMax hEY (div_nonneg hε hL.le)
    rw [hg] at hb
    calc μ.real {ω | (1 + ε) * hEY.lambdaMax ≤ (hY ω).lambdaMax}
        ≤ Real.exp (-θ * ((1 + ε) * hEY.lambdaMax)) *
            ∫ ω, traceMgf (fun ω => ∑ k, X k ω) θ ω ∂μ := h1
      _ ≤ Real.exp (-θ * ((1 + ε) * hEY.lambdaMax)) *
            (Fintype.card n * Real.exp (ε / L * hEY.lambdaMax)) :=
          mul_le_mul_of_nonneg_left (hb.trans h2) (Real.exp_pos _).le
      _ = Fintype.card n * (Real.exp ε / (1 + ε) ^ (1 + ε)) ^ (hEY.lambdaMax / L) := by
          rw [Real.rpow_def_of_pos (by positivity), Real.log_div (Real.exp_pos _).ne'
            (by positivity), Real.log_exp, Real.log_rpow (by linarith), mul_left_comm,
            ← Real.exp_add]
          congr 2
          simp only [θ]
          field_simp
          ring
  · rcases hε.eq_or_lt with rfl | hε'
    · simp only [Real.exp_zero, neg_zero, sub_zero, Real.one_rpow, div_one, mul_one]
      exact measureReal_le_one.trans hcard
    set θ := Real.log (1 - ε) / L
    have hθ : θ < 0 := div_neg_of_neg_of_pos (Real.log_neg (by linarith) (by linarith)) hL
    obtain ⟨hi, hb⟩ := hmaster θ
    have h1 := measureReal_lambdaMin_le_le hY hθ hi ((1 - ε) * hEY.lambdaMin)
    have hg : (Real.exp (θ * L) - 1) / L = -ε / L := by
      simp only [θ, div_mul_cancel₀ _ hL.ne', Real.exp_log (by linarith : (0 : ℝ) < 1 - ε)]
      ring
    have h2 := re_trace_exp_smul_le_lambdaMin hEY
      (div_nonpos_of_nonpos_of_nonneg (by linarith : -ε ≤ 0) hL.le)
    rw [hg] at hb
    calc μ.real {ω | (hY ω).lambdaMin ≤ (1 - ε) * hEY.lambdaMin}
        ≤ Real.exp (-θ * ((1 - ε) * hEY.lambdaMin)) *
            ∫ ω, traceMgf (fun ω => ∑ k, X k ω) θ ω ∂μ := h1
      _ ≤ Real.exp (-θ * ((1 - ε) * hEY.lambdaMin)) *
            (Fintype.card n * Real.exp (-ε / L * hEY.lambdaMin)) :=
          mul_le_mul_of_nonneg_left (hb.trans h2) (Real.exp_pos _).le
      _ = Fintype.card n * (Real.exp (-ε) / (1 - ε) ^ (1 - ε)) ^ (hEY.lambdaMin / L) := by
          have h1ε : 0 < 1 - ε := by linarith
          rw [Real.rpow_def_of_pos (by positivity),
            Real.log_div (Real.exp_pos _).ne' (by positivity),
            Real.log_exp, Real.log_rpow (by linarith), mul_left_comm, ← Real.exp_add]
          congr 2
          simp only [θ]
          field_simp
          ring

end Chernoff

/-! ### Matrix Bernstein -/

section Bernstein

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- `e^y ≤ 1 + y + y²/2` for `y ≤ 0`. -/
private lemma exp_le_quadratic_of_nonpos {y : ℝ} (hy : y ≤ 0) : Real.exp y ≤ 1 + y + y ^ 2 / 2 := by
  let f : ℝ → ℝ := fun z => Real.exp z * (1 - z + z ^ 2 / 2)
  have hf : ∀ z, HasDerivAt f (Real.exp z * (z ^ 2 / 2)) z := fun z => by
    have := (Real.hasDerivAt_exp z).mul (((hasDerivAt_id' (x := z)).const_sub (1 : ℝ)).add
      ((hasDerivAt_pow 2 z).div_const 2))
    convert this using 1
    norm_num
    ring
  have hmono : Monotone f := monotone_of_deriv_nonneg (fun z => (hf z).differentiableAt)
    fun z => by rw [(hf z).deriv]; positivity
  have h := hmono (neg_nonneg.2 hy)
  simp only [f, Real.exp_zero, sub_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    zero_pow, zero_div, add_zero, mul_one, sub_neg_eq_add, even_two, Even.neg_pow] at h
  have h2 := mul_le_mul_of_nonneg_left h (Real.exp_pos y).le
  rwa [mul_one, ← mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, one_mul] at h2

/-- `2 · 3^k ≤ (k + 2)!`. -/
private lemma two_mul_three_pow_le_factorial (k : ℕ) : 2 * 3 ^ k ≤ (k + 2).factorial := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [show k + 1 + 2 = (k + 2) + 1 by ring, Nat.factorial_succ]
    calc 2 * 3 ^ (k + 1) = 3 * (2 * 3 ^ k) := by ring
      _ ≤ (k + 2 + 1) * (k + 2).factorial := Nat.mul_le_mul (by omega) ih

/-- `e^y ≤ 1 + y + (y²/2) / (1 - y/3)` for `0 ≤ y < 3`, from `q! ≥ 2 · 3^{q-2}` (Tropp,
arXiv:1501.01571v1, proof of Lemma 6.6.2). -/
private lemma exp_le_bernstein_series {y : ℝ} (hy0 : 0 ≤ y) (hy3 : y < 3) :
    Real.exp y ≤ 1 + y + y ^ 2 / 2 / (1 - y / 3) := by
  have hs := Real.summable_pow_div_factorial y
  have hq0 : 0 ≤ y / 3 := by positivity
  have hq1 : y / 3 < 1 := by linarith
  have hg : Summable fun k : ℕ => y ^ 2 / 2 * (y / 3) ^ k :=
    (summable_geometric_of_lt_one hq0 hq1).mul_left _
  have hs2 : Summable fun k : ℕ => y ^ (k + 2) / (k + 2).factorial :=
    (summable_nat_add_iff 2).2 hs
  have he : Real.exp y = ∑' k : ℕ, y ^ k / k.factorial := by
    rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]
  rw [he, ← Summable.sum_add_tsum_nat_add 2 hs]
  have hle : ∑' k : ℕ, y ^ (k + 2) / (k + 2).factorial ≤ ∑' k : ℕ, y ^ 2 / 2 * (y / 3) ^ k := by
    refine Summable.tsum_le_tsum (fun k => ?_) hs2 hg
    rw [div_pow, pow_add, mul_comm (y ^ k), mul_div_assoc]
    have hf : (2 * 3 ^ k : ℝ) ≤ (k + 2).factorial := by
      exact_mod_cast two_mul_three_pow_le_factorial k
    calc y ^ 2 * (y ^ k / (k + 2).factorial) ≤ y ^ 2 * (y ^ k / (2 * 3 ^ k)) :=
          mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_left (by positivity) (by positivity) hf)
            (by positivity)
      _ = y ^ 2 / 2 * (y ^ k / 3 ^ k) := by ring
  rw [tsum_mul_left, tsum_geometric_of_lt_one hq0 hq1] at hle
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, pow_zero, Nat.factorial_zero,
    Nat.cast_one, div_one, zero_add, pow_one, Nat.factorial_one]
  rw [div_eq_mul_inv (y ^ 2 / 2)]
  linarith

/-- The scalar Bernstein bound behind Tropp's Lemma 6.6.2. -/
private lemma exp_mul_le_bernstein {θ L x : ℝ} (hθ : 0 ≤ θ) (hL : 0 ≤ L) (hθL : θ * L < 3)
    (hx : x ≤ L) :
    Real.exp (θ * x) ≤ 1 + θ * x + θ ^ 2 / 2 / (1 - θ * L / 3) * x ^ 2 := by
  have hD : 0 < 1 - θ * L / 3 := by linarith
  have hD1 : 1 - θ * L / 3 ≤ 1 := by nlinarith
  rcases le_or_gt (θ * x) 0 with hy | hy
  · refine (exp_le_quadratic_of_nonpos hy).trans ?_
    have : θ ^ 2 / 2 * x ^ 2 ≤ θ ^ 2 / 2 / (1 - θ * L / 3) * x ^ 2 := by
      refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg x)
      rw [le_div_iff₀ hD]
      nlinarith [sq_nonneg θ]
    nlinarith
  · have hθx : θ * x ≤ θ * L := mul_le_mul_of_nonneg_left hx hθ
    refine (exp_le_bernstein_series hy.le (by linarith)).trans ?_
    have hD' : 1 - θ * L / 3 ≤ 1 - θ * x / 3 := by linarith
    have : (θ * x) ^ 2 / 2 / (1 - θ * x / 3) ≤ θ ^ 2 / 2 / (1 - θ * L / 3) * x ^ 2 := by
      rw [div_mul_eq_mul_div, mul_pow]
      rw [show θ ^ 2 * x ^ 2 / 2 = θ ^ 2 / 2 * x ^ 2 by ring]
      exact div_le_div_of_nonneg_left (by positivity) hD hD'
    linarith

/-- The Bernstein mgf bound (Tropp, Lemma 6.6.2). -/
private lemma expect_exp_smul_le_bernstein [Nonempty n] {X : Ω → Matrix n n ℂ} (hm : Measurable X)
    (hX : ∀ ω, (X ω).IsHermitian) {L : ℝ} (hL : 0 ≤ L) (hup : ∀ ω, (hX ω).lambdaMax ≤ L)
    (hint : ∀ i j, Integrable (fun ω => X ω i j) μ)
    (hint2 : ∀ i j, Integrable (fun ω => (X ω * X ω) i j) μ) (hcenter : expect μ X = 0)
    {θ : ℝ} (hθ : 0 ≤ θ) (hθL : θ * L < 3) :
    expect μ (fun ω => NormedSpace.exp (θ • X ω)) ≤
      NormedSpace.exp ((θ ^ 2 / 2 / (1 - θ * L / 3)) • expect μ fun ω => X ω * X ω) := by
  set g := θ ^ 2 / 2 / (1 - θ * L / 3)
  have hEi := integrable_exp_smul_apply_of_le (μ := μ) hm hX hup hθ
  have hXX : ∀ ω, (X ω * X ω).IsHermitian := fun ω => by simpa [sq] using (hX ω).pow 2
  have hV : (expect μ fun ω => X ω * X ω).IsHermitian := expect_isHermitian hXX
  have hpt : ∀ ω, NormedSpace.exp (θ • X ω) ≤
      algebraMap ℝ _ 1 + θ • X ω + g • (X ω * X ω) := fun ω => by
    rw [← cfc_quadratic (hX ω)]
    refine exp_smul_le_of_forall (hX ω) θ (by fun_prop) fun x hx => ?_
    exact exp_mul_le_bernstein hθ hL hθL ((mem_spectrum_bounds (hX ω) hx).2.trans (hup ω))
  have hci : ∀ i j, Integrable
      (fun ω => (algebraMap ℝ (Matrix n n ℂ) 1 + θ • X ω + g • (X ω * X ω)) i j) μ :=
    fun i j => ((integrable_const _).add ((hint i j).smul θ)).add ((hint2 i j).smul g)
  refine (expect_mono hEi hci hpt).trans ?_
  rw [expect_add (M := fun ω => algebraMap ℝ (Matrix n n ℂ) 1 + θ • X ω)
      (M' := fun ω => g • (X ω * X ω))
      (fun i j => (integrable_const _).add ((hint i j).smul θ)) (fun i j => (hint2 i j).smul g),
    expect_add (M := fun _ => algebraMap ℝ (Matrix n n ℂ) 1) (M' := fun ω => θ • X ω)
      (fun i j => integrable_const _) (fun i j => (hint i j).smul θ),
    expect_const, expect_smul, expect_smul, hcenter, smul_zero, add_zero, ← cfc_affine hV,
    hV.exp_smul_eq_cfc g]
  exact cfc_mono fun x _ => by linarith [Real.add_one_le_exp (g * x)]

/-- **Matrix Bernstein inequality, Hermitian case** (Tropp, *An Introduction to Matrix
Concentration Inequalities*, arXiv:1501.01571, Theorem 6.6.1, display (6.6.3); Tropp,
*User-friendly tail bounds for sums of random matrices*, Found. Comput. Math. 12 (2012),
Theorem 1.4). Let `X₀, …, X_{N-1}` be independent, centered random Hermitian `d × d` matrices with
`λmax(X_k) ≤ L`, let `Y = ∑ₖ X_k` and let `v = ‖∑ₖ E X_k²‖`, which is `λmax(∑ₖ E X_k²)` since
that matrix is positive semidefinite. Then for all `t ≥ 0`,
`P{λmax(Y) ≥ t} ≤ d · exp(-(t²/2) / (v + L t / 3))`. -/
theorem matrix_bernstein [Nonempty n] {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {N : ℕ} {X : Fin N → Ω → Matrix n n ℂ}
    (hmeas : ∀ k, Measurable (X k)) (hind : iIndepFun X μ)
    (hX : ∀ k ω, (X k ω).IsHermitian) {L : ℝ} (hL : 0 ≤ L)
    (hup : ∀ k ω, (hX k ω).lambdaMax ≤ L)
    (hint : ∀ k i j, Integrable (fun ω => X k ω i j) μ)
    (hint2 : ∀ k i j, Integrable (fun ω => (X k ω * X k ω) i j) μ)
    (hcenter : ∀ k, expect μ (X k) = 0)
    (hY : ∀ ω, (∑ k, X k ω).IsHermitian)
    (hV : (∑ k, expect μ fun ω => X k ω * X k ω).IsHermitian) (t : ℝ) (ht : 0 ≤ t) :
    μ.real {ω | t ≤ (hY ω).lambdaMax} ≤
      Fintype.card n * Real.exp (-(t ^ 2 / 2) / (hV.lambdaMax + L * t / 3)) := by
  set V := ∑ k, expect μ fun ω => X k ω * X k ω
  set v := hV.lambdaMax
  have hcard : (1 : ℝ) ≤ Fintype.card n := by exact_mod_cast Fintype.card_pos
  have hXX : ∀ k ω, (X k ω * X k ω).PosSemidef := fun k ω => by
    simpa [(hX k ω).eq] using Matrix.posSemidef_conjTranspose_mul_self (X k ω)
  have hVpsd : V.PosSemidef := Matrix.posSemidef_sum _ fun k _ =>
    expect_posSemidef (hint2 k) (hXX k)
  have hv : 0 ≤ v := (hVpsd.eigenvalues_nonneg (Classical.arbitrary n)).trans
    (hV.eigenvalues_le_lambdaMax _)
  -- the trivial cases
  have htriv : 0 ≤ -(t ^ 2 / 2) / (v + L * t / 3) →
      μ.real {ω | t ≤ (hY ω).lambdaMax} ≤
        Fintype.card n * Real.exp (-(t ^ 2 / 2) / (v + L * t / 3)) := fun h =>
    measureReal_le_one.trans (hcard.trans (le_mul_of_one_le_right (by positivity)
      (Real.one_le_exp h)))
  set D := v + L * t / 3
  have hD0 : 0 ≤ D := by positivity
  rcases ht.eq_or_lt with rfl | ht'
  · exact htriv (by simp)
  rcases hD0.eq_or_lt with hD | hD
  · exact htriv (by rw [← hD, div_zero])
  -- the master bound for an admissible `θ`
  have hmaster : ∀ θ : ℝ, 0 ≤ θ → θ * L < 3 →
      Integrable (traceMgf (fun ω => ∑ k, X k ω) θ) μ ∧
      ∫ ω, traceMgf (fun ω => ∑ k, X k ω) θ ω ∂μ ≤
        Fintype.card n * Real.exp (θ ^ 2 / 2 / (1 - θ * L / 3) * v) := by
    intro θ hθ hθL
    have := integrable_and_integral_le_of_forall hmeas hind hX
      (C := fun k => (θ ^ 2 / 2 / (1 - θ * L / 3)) • expect μ fun ω => X k ω * X k ω)
      (fun k => (IsSelfAdjoint.all _).smul (expect_isHermitian fun ω => (hXX k ω).isHermitian))
      fun k H hH => lintegral_re_trace_exp_add_le_of_le
        (fun ω => (IsSelfAdjoint.all θ).smul (hX k ω))
        (integrable_exp_smul_apply_of_le (hmeas k) (hX k) (hup k) hθ)
        ((IsSelfAdjoint.all _).smul (expect_isHermitian fun ω => (hXX k ω).isHermitian))
        (expect_exp_smul_le_bernstein (hmeas k) (hX k) hL (hup k) (hint k) (hint2 k)
          (hcenter k) hθ hθL) hH
    rw [← Finset.smul_sum] at this
    refine ⟨this.1, this.2.trans (re_trace_exp_smul_le_lambdaMax hV ?_)⟩
    have : 0 < 1 - θ * L / 3 := by linarith
    positivity
  have hfinal : ∀ θ : ℝ, 0 < θ → θ * L < 3 →
      -θ * t + θ ^ 2 / 2 / (1 - θ * L / 3) * v ≤ -(t ^ 2 / 2) / D →
      μ.real {ω | t ≤ (hY ω).lambdaMax} ≤ Fintype.card n * Real.exp (-(t ^ 2 / 2) / D) := by
    intro θ hθ hθL hle
    obtain ⟨hi, hb⟩ := hmaster θ hθ.le hθL
    calc μ.real {ω | t ≤ (hY ω).lambdaMax}
        ≤ Real.exp (-θ * t) * ∫ ω, traceMgf (fun ω => ∑ k, X k ω) θ ω ∂μ :=
          measureReal_le_lambdaMax_le hY hθ hi t
      _ ≤ Real.exp (-θ * t) * (Fintype.card n * Real.exp (θ ^ 2 / 2 / (1 - θ * L / 3) * v)) :=
          mul_le_mul_of_nonneg_left hb (Real.exp_pos _).le
      _ = Fintype.card n * Real.exp (-θ * t + θ ^ 2 / 2 / (1 - θ * L / 3) * v) := by
          rw [Real.exp_add]; ring
      _ ≤ Fintype.card n * Real.exp (-(t ^ 2 / 2) / D) :=
          mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 hle) (by positivity)
  rcases hv.eq_or_lt with hv0 | hvpos
  · -- `v = 0`: then `L > 0`; take `θ = 3 / (2 L)`
    have hLt : 0 < L * t / 3 := by
      have h' : 0 < v + L * t / 3 := hD
      rwa [← hv0, zero_add] at h'
    have hLpos : 0 < L := by
      by_contra h
      push Not at h
      have : L * t ≤ 0 := mul_nonpos_of_nonpos_of_nonneg h ht
      linarith
    refine hfinal (3 / (2 * L)) (by positivity) (by field_simp; norm_num) ?_
    rw [← hv0]
    simp only [D, ← hv0, zero_add, mul_zero, add_zero]
    field_simp
    ring_nf
    rfl
  · -- `v > 0`: take `θ = t / D`
    have hθL : t / D * L < 3 := by
      rw [div_mul_eq_mul_div, div_lt_iff₀ hD]
      simp only [D]
      nlinarith
    refine hfinal (t / D) (div_pos ht' hD) hθL (le_of_eq ?_)
    have h1 : 1 - t / D * L / 3 = v / D := by
      field_simp
      simp only [D]
      ring
    rw [h1]
    field_simp
    ring

end Bernstein

/-! ### Matrix Gaussian series -/

section Gaussian

/-- The spectral projections of a Hermitian matrix. -/
private noncomputable def specProj {A : Matrix n n ℂ} (hA : A.IsHermitian) (l : n) : Matrix n n ℂ :=
  (hA.eigenvectorUnitary : Matrix n n ℂ) * Matrix.single l l 1 *
    star (hA.eigenvectorUnitary : Matrix n n ℂ)

/-- The spectral decomposition `g(A) = ∑ₗ g(λₗ) Pₗ` of the functional calculus. -/
private lemma cfc_eq_sum_smul {A : Matrix n n ℂ} (hA : A.IsHermitian) (g : ℝ → ℝ) :
    cfc g A = ∑ l, g (hA.eigenvalues l) • specProj hA l := by
  rw [hA.cfc_eq, Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply]
  have hd : Matrix.diagonal (RCLike.ofReal ∘ g ∘ hA.eigenvalues) =
      ∑ l, g (hA.eigenvalues l) • Matrix.single l l (1 : ℂ) := by
    ext i j
    simp only [Matrix.diagonal_apply, Matrix.sum_apply, Matrix.smul_apply, Matrix.single_apply,
      Function.comp_apply]
    by_cases hij : i = j
    · subst hij
      simp
    · simp only [hij, ite_false]
      symm
      refine Finset.sum_eq_zero fun x _ => ?_
      split_ifs with h
      · exact absurd (h.1.symm.trans h.2) hij
      · simp
  rw [hd, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun l _ => ?_
  simp only [specProj, Matrix.mul_smul, Matrix.smul_mul]

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

omit [Fintype n] [DecidableEq n] in
/-- `E[c(ω) P] = (E c) P` for a fixed matrix `P`. -/
private lemma expect_real_smul_const (c : Ω → ℝ) (P : Matrix n n ℂ) :
    expect μ (fun ω => c ω • P) = (∫ ω, c ω ∂μ) • P := by
  ext i j
  simp only [expect_apply, Matrix.smul_apply]
  exact integral_smul_const c (P i j)

/-- The matrix mgf of `γ A` for a standard Gaussian coordinate `γ = ω k`. -/
private lemma expect_exp_smul_gaussian {N : ℕ} {A : Matrix n n ℂ} (hA : A.IsHermitian) (k : Fin N)
    (θ : ℝ) :
    (∀ i j, Integrable (fun ω : Fin N → ℝ => NormedSpace.exp (θ • (((ω k : ℝ) : ℂ) • A)) i j)
      (Measure.pi fun _ => gaussianReal 0 1)) ∧
    expect (Measure.pi fun _ : Fin N => gaussianReal 0 1)
        (fun ω => NormedSpace.exp (θ • (((ω k : ℝ) : ℂ) • A))) =
      NormedSpace.exp ((θ ^ 2 / 2) • (A * A)) := by
  set ν := Measure.pi fun _ : Fin N => gaussianReal 0 1
  have hrw : ∀ ω : Fin N → ℝ, NormedSpace.exp (θ • (((ω k : ℝ) : ℂ) • A)) =
      ∑ l, Real.exp (θ * ω k * hA.eigenvalues l) • specProj hA l := by
    intro ω
    rw [Complex.coe_smul, smul_smul, hA.exp_smul_eq_cfc, cfc_eq_sum_smul]
  have hmap := (measurePreserving_eval (fun _ : Fin N => gaussianReal 0 1) k).map_eq
  have hint_l : ∀ l, Integrable (fun ω : Fin N → ℝ => Real.exp (θ * ω k * hA.eigenvalues l)) ν := by
    intro l
    have h1 := integrable_exp_mul_gaussianReal (μ := 0) (v := 1) (θ * hA.eigenvalues l)
    rw [← hmap] at h1
    have h2 := h1.comp_measurable (measurable_pi_apply k)
    refine h2.congr (Filter.Eventually.of_forall fun ω => ?_)
    change Real.exp ((θ * hA.eigenvalues l) * ω k) = Real.exp (θ * ω k * hA.eigenvalues l)
    ring_nf
  have hint_e : ∀ l i j, Integrable (fun ω : Fin N → ℝ =>
      (Real.exp (θ * ω k * hA.eigenvalues l) • specProj hA l) i j) ν := fun l i j => by
    simp only [Matrix.smul_apply, Complex.real_smul]
    exact (hint_l l).ofReal.mul_const _
  have hgauss : ∀ l, ∫ ω : Fin N → ℝ, Real.exp (θ * ω k * hA.eigenvalues l) ∂ν =
      Real.exp (θ ^ 2 / 2 * hA.eigenvalues l ^ 2) := by
    intro l
    have h1 : ∫ ω : Fin N → ℝ, Real.exp (θ * ω k * hA.eigenvalues l) ∂ν =
        ∫ x, Real.exp ((θ * hA.eigenvalues l) * x) ∂(ν.map (Function.eval k)) := by
      rw [integral_map (measurable_pi_apply k).aemeasurable (by fun_prop)]
      congr 1
      ext ω
      show _ = Real.exp ((θ * hA.eigenvalues l) * ω k)
      ring_nf
    rw [h1, hmap]
    have h2 := congrFun (mgf_id_gaussianReal (μ := 0) (v := 1)) (θ * hA.eigenvalues l)
    simp only [mgf, id] at h2
    rw [h2]
    congr 1
    simp only [zero_mul, zero_add, NNReal.coe_one, one_mul]
    ring
  refine ⟨fun i j => ?_, ?_⟩
  · simp only [hrw, Matrix.sum_apply]
    exact integrable_finsetSum _ fun l _ => hint_e l i j
  · simp only [hrw]
    rw [expect_sum _ fun l i j => hint_e l i j]
    simp only [expect_real_smul_const, hgauss]
    have hAA : (A * A).IsHermitian := by simpa [sq] using hA.pow 2
    rw [hAA.exp_smul_eq_cfc, ← sq, ← cfc_comp_pow (fun x => Real.exp (θ ^ 2 / 2 * x)) 2 A,
      cfc_eq_sum_smul]

/-- If `B ≤ a/θ + bθ` for every `θ > 0`, with `a, b ≥ 0`, then `B ≤ 2 √(ab)`. -/
private lemma le_two_mul_sqrt_of_forall {B a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (h : ∀ θ : ℝ, 0 < θ → B ≤ a / θ + b * θ) : B ≤ 2 * Real.sqrt (a * b) := by
  rcases ha.eq_or_lt with rfl | ha'
  · simp only [zero_mul, Real.sqrt_zero, mul_zero]
    by_contra hB
    push Not at hB
    have := h (B / (2 * (b + 1))) (by positivity)
    rw [zero_div, zero_add, mul_div_assoc', le_div_iff₀ (by positivity)] at this
    nlinarith
  rcases hb.eq_or_lt with rfl | hb'
  · simp only [mul_zero, Real.sqrt_zero]
    by_contra hB
    push Not at hB
    have := h (2 * (a + 1) / B) (by positivity)
    rw [zero_mul, add_zero, div_div_eq_mul_div, le_div_iff₀ (by positivity)] at this
    nlinarith
  have hsa := Real.sqrt_pos.2 ha'
  have hsb := Real.sqrt_pos.2 hb'
  have := h (Real.sqrt a / Real.sqrt b) (div_pos hsa hsb)
  rw [Real.sqrt_mul ha]
  have e1 : a / (Real.sqrt a / Real.sqrt b) = Real.sqrt a * Real.sqrt b := by
    field_simp
    rw [Real.sq_sqrt ha]
  have e2 : b * (Real.sqrt a / Real.sqrt b) = Real.sqrt a * Real.sqrt b := by
    field_simp
    rw [Real.sq_sqrt hb]
  linarith

/-- `|λmax(M)| ≤ ∑ᵢⱼ ‖Mᵢⱼ‖` for Hermitian `M`. -/
private lemma abs_lambdaMax_le [Nonempty n] {M : Matrix n n ℂ} (hM : M.IsHermitian) :
    |hM.lambdaMax| ≤ ∑ i, ∑ j, ‖M i j‖ := by
  obtain ⟨i, hi⟩ := hM.exists_eigenvalues_eq_lambdaMax
  rw [← hi]
  have h1 := eigenvalues_sq_le hM i
  have h2 : ∑ i, ∑ j, ‖M i j‖ ^ 2 ≤ (∑ i, ∑ j, ‖M i j‖) ^ 2 :=
    (Finset.sum_le_sum fun i _ => Finset.sum_sq_le_sq_sum_of_nonneg fun j _ => norm_nonneg _).trans
      (Finset.sum_sq_le_sq_sum_of_nonneg fun i _ => Finset.sum_nonneg fun j _ => norm_nonneg _)
  exact abs_le_of_sq_le_sq' (h1.trans h2) (by positivity) |> fun h => abs_le.2 h

/-- `λmax` of a measurable random Hermitian matrix is measurable: it is the limit of
`p⁻¹ log tr e^{pY}` as `p → ∞`. -/
private lemma measurable_lambdaMax [Nonempty n] {Y : Ω → Matrix n n ℂ} (hYm : Measurable Y)
    (hY : ∀ ω, (Y ω).IsHermitian) : Measurable fun ω => (hY ω).lambdaMax := by
  set F : ℕ → Ω → ℝ := fun p ω =>
    ((p : ℝ) + 1)⁻¹ * Real.log (RCLike.re (NormedSpace.exp (((p : ℝ) + 1) • Y ω)).trace)
  have hF : ∀ p, Measurable (F p) := fun p =>
    (Real.measurable_log.comp (continuous_re_trace_exp.measurable.comp
      ((continuous_const_smul _).measurable.comp hYm))).const_mul _
  refine measurable_of_tendsto_metrizable hF (tendsto_pi_nhds.2 fun ω => ?_)
  set lam := (hY ω).lambdaMax
  set d : ℝ := (Fintype.card n : ℝ)
  have hd : 0 < d := by simp only [d]; exact_mod_cast Fintype.card_pos
  have hlow : ∀ p : ℕ, lam ≤ F p ω := fun p => by
    have hq : (0 : ℝ) < p + 1 := by positivity
    have htr := (hY ω).re_trace_exp_pos ((p : ℝ) + 1)
    have h1 := (hY ω).exp_mul_lambdaMax_le_re_trace_exp ((p : ℝ) + 1)
    have h2 : ((p : ℝ) + 1) * lam ≤ Real.log (RCLike.re
        (NormedSpace.exp (((p : ℝ) + 1) • Y ω)).trace) := (Real.le_log_iff_exp_le htr).2 h1
    simp only [F]
    rw [inv_mul_eq_div, le_div_iff₀ hq]
    linarith
  have hup : ∀ p : ℕ, F p ω ≤ lam + Real.log d * (1 / ((p : ℝ) + 1)) := fun p => by
    have hq : (0 : ℝ) < p + 1 := by positivity
    have htr := (hY ω).re_trace_exp_pos ((p : ℝ) + 1)
    have h1 := re_trace_exp_smul_le_lambdaMax (hY ω) hq.le
    have h2 := Real.log_le_log htr h1
    rw [Real.log_mul hd.ne' (Real.exp_pos _).ne', Real.log_exp] at h2
    simp only [F]
    rw [inv_mul_eq_div, div_le_iff₀ hq]
    field_simp
    nlinarith
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ?_ hlow hup
  simpa using (tendsto_const_nhds (x := lam)).add
    ((tendsto_const_nhds (x := Real.log d)).mul tendsto_one_div_add_atTop_nhds_zero_nat)

/-- **Matrix Gaussian series, Hermitian case** (Tropp, *An Introduction to Matrix Concentration
Inequalities*, arXiv:1501.01571, Theorem 4.6.1, displays (4.6.2) and (4.6.3); Tropp,
*User-friendly tail bounds for sums of random matrices*, Found. Comput. Math. 12 (2012),
Theorem 1.2). Let `A₀, …, A_{N-1}` be fixed Hermitian `d × d` matrices, `γ₀, …, γ_{N-1}`
independent standard normal variables, `Y = ∑ₖ γₖ Aₖ` and `v = ‖∑ₖ Aₖ²‖ = λmax(∑ₖ Aₖ²)`. Then
`E λmax(Y) ≤ (2 v log d)^{1/2}` and, for all `t ≥ 0`, `P{λmax(Y) ≥ t} ≤ d e^{-t²/(2v)}`. -/
theorem matrix_gaussian_series [Nonempty n] {N : ℕ} {A : Fin N → Matrix n n ℂ}
    (hA : ∀ k, (A k).IsHermitian) (hY : ∀ ω, (gaussianSeries A ω).IsHermitian)
    (hV : (∑ k, A k * A k).IsHermitian) :
    ∫ ω, (hY ω).lambdaMax ∂(Measure.pi fun _ : Fin N => gaussianReal 0 1) ≤
        Real.sqrt (2 * hV.lambdaMax * Real.log (Fintype.card n)) ∧
      ∀ t : ℝ, 0 ≤ t →
        (Measure.pi fun _ : Fin N => gaussianReal 0 1).real {ω | t ≤ (hY ω).lambdaMax} ≤
          Fintype.card n * Real.exp (-t ^ 2 / (2 * hV.lambdaMax)) := by
  set ν := Measure.pi fun _ : Fin N => gaussianReal 0 1
  set v := hV.lambdaMax
  set d : ℝ := (Fintype.card n : ℝ)
  have hcard : (1 : ℝ) ≤ d := by simp only [d]; exact_mod_cast Fintype.card_pos
  set X : Fin N → (Fin N → ℝ) → Matrix n n ℂ := fun k ω => ((ω k : ℝ) : ℂ) • A k
  have hXc : ∀ k, Continuous (X k) := fun k =>
    (Complex.continuous_ofReal.comp (continuous_apply k)).smul continuous_const
  have hXm : ∀ k, Measurable (X k) := fun k => (hXc k).measurable
  have hXh : ∀ k ω, (X k ω).IsHermitian := fun k ω => by
    simp only [X, Complex.coe_smul]
    exact (IsSelfAdjoint.all _).smul (hA k)
  have hind : iIndepFun X ν :=
    iIndepFun_pi (X := fun k (x : ℝ) => ((x : ℝ) : ℂ) • A k) fun k =>
      ((Complex.continuous_ofReal.smul continuous_const).measurable).aemeasurable
  have hYX : gaussianSeries A = fun ω => ∑ k, X k ω := rfl
  have hAA : ∀ k, (A k * A k).IsHermitian := fun k => by simpa [sq] using (hA k).pow 2
  have hVpsd : (∑ k, A k * A k).PosSemidef := Matrix.posSemidef_sum _ fun k _ => by
    simpa [(hA k).eq] using Matrix.posSemidef_conjTranspose_mul_self (A k)
  have hv : 0 ≤ v := (hVpsd.eigenvalues_nonneg (Classical.arbitrary n)).trans
    (hV.eigenvalues_le_lambdaMax _)
  have hmaster : ∀ θ : ℝ, Integrable (traceMgf (gaussianSeries A) θ) ν ∧
      ∫ ω, traceMgf (gaussianSeries A) θ ω ∂ν ≤ d * Real.exp (θ ^ 2 / 2 * v) := by
    intro θ
    have := integrable_and_integral_le_of_forall hXm hind hXh
      (C := fun k => (θ ^ 2 / 2) • (A k * A k)) (fun k => (IsSelfAdjoint.all _).smul (hAA k))
      fun k H hH => lintegral_re_trace_exp_add_le_of_le
        (fun ω => (IsSelfAdjoint.all θ).smul (hXh k ω)) (expect_exp_smul_gaussian (hA k) k θ).1
        ((IsSelfAdjoint.all _).smul (hAA k)) (expect_exp_smul_gaussian (hA k) k θ).2.le hH
    rw [← Finset.smul_sum, ← hYX] at this
    exact ⟨this.1, this.2.trans (re_trace_exp_smul_le_lambdaMax hV (by positivity))⟩
  refine ⟨?_, fun t ht => ?_⟩
  · -- expectation bound
    have hgi : Integrable (fun ω : Fin N → ℝ => ∑ i, ∑ j, ∑ k, |ω k| * ‖A k i j‖) ν := by
      have hk : ∀ k, Integrable (fun ω : Fin N → ℝ => |ω k|) ν := fun k => by
        have h1 := (memLp_id_gaussianReal (μ := 0) (v := 1) 1).integrable le_rfl
        rw [← (measurePreserving_eval (fun _ : Fin N => gaussianReal 0 1) k).map_eq] at h1
        exact (h1.comp_measurable (measurable_pi_apply k)).abs
      exact integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
        integrable_finsetSum _ fun k _ => (hk k).mul_const _
    have hmax : Integrable (fun ω => (hY ω).lambdaMax) ν := by
      refine hgi.mono' (measurable_lambdaMax (hYX ▸ Finset.measurable_sum _ fun k _ => hXm k)
        hY).aestronglyMeasurable (Filter.Eventually.of_forall fun ω => ?_)
      rw [Real.norm_eq_abs]
      refine (abs_lambdaMax_le (hY ω)).trans (Finset.sum_le_sum fun i _ =>
        Finset.sum_le_sum fun j _ => ?_)
      simp only [gaussianSeries, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
      rw [norm_mul, RCLike.norm_ofReal]
    have hbound : ∀ θ : ℝ, 0 < θ →
        ∫ ω, (hY ω).lambdaMax ∂ν ≤ Real.log d / θ + v / 2 * θ := by
      intro θ hθ
      obtain ⟨hi, hb⟩ := hmaster θ
      have h1 := integral_lambdaMax_le hY hθ hmax hi
      have hpos : 0 < ∫ ω, traceMgf (gaussianSeries A) θ ω ∂ν := by
        rw [integral_pos_iff_support_of_nonneg (f := traceMgf (gaussianSeries A) θ)
          (fun ω => (re_trace_exp_nonneg_of_isHermitian
          ((IsSelfAdjoint.all θ).smul (hY ω)))) hi]
        have : Function.support (traceMgf (gaussianSeries A) θ) = Set.univ :=
          Set.eq_univ_of_forall fun ω => ((hY ω).re_trace_exp_pos θ).ne'
        simp [this]
      have h2 := Real.log_le_log hpos hb
      rw [Real.log_mul (by positivity) (Real.exp_pos _).ne', Real.log_exp] at h2
      calc ∫ ω, (hY ω).lambdaMax ∂ν ≤ θ⁻¹ * Real.log (∫ ω, traceMgf (gaussianSeries A) θ ω ∂ν) :=
            h1
        _ ≤ θ⁻¹ * (Real.log d + θ ^ 2 / 2 * v) :=
            mul_le_mul_of_nonneg_left h2 (inv_nonneg.2 hθ.le)
        _ = Real.log d / θ + v / 2 * θ := by field_simp
    have := le_two_mul_sqrt_of_forall (Real.log_nonneg hcard) (by positivity : 0 ≤ v / 2) hbound
    calc ∫ ω, (hY ω).lambdaMax ∂ν ≤ 2 * Real.sqrt (Real.log d * (v / 2)) := this
      _ = Real.sqrt (2 * v * Real.log d) := by
          rw [show 2 * v * Real.log d = 2 ^ 2 * (Real.log d * (v / 2)) by ring,
            Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2 ^ 2), Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]
  · -- tail bound
    have htriv : 0 ≤ -t ^ 2 / (2 * v) → ν.real {ω | t ≤ (hY ω).lambdaMax} ≤
        d * Real.exp (-t ^ 2 / (2 * v)) := fun h =>
      measureReal_le_one.trans (hcard.trans (le_mul_of_one_le_right (by positivity)
        (Real.one_le_exp h)))
    rcases hv.eq_or_lt with hv0 | hvpos
    · exact htriv (by rw [← hv0, mul_zero, div_zero])
    rcases ht.eq_or_lt with rfl | ht'
    · exact htriv (by simp)
    set θ := t / v
    have hθ : 0 < θ := div_pos ht' hvpos
    obtain ⟨hi, hb⟩ := hmaster θ
    calc ν.real {ω | t ≤ (hY ω).lambdaMax}
        ≤ Real.exp (-θ * t) * ∫ ω, traceMgf (gaussianSeries A) θ ω ∂ν :=
          measureReal_le_lambdaMax_le hY hθ hi t
      _ ≤ Real.exp (-θ * t) * (d * Real.exp (θ ^ 2 / 2 * v)) :=
          mul_le_mul_of_nonneg_left hb (Real.exp_pos _).le
      _ = d * Real.exp (-t ^ 2 / (2 * v)) := by
          rw [mul_left_comm, ← Real.exp_add]
          congr 2
          simp only [θ]
          field_simp
          ring

end Gaussian

/-! ### Matrix Hoeffding -/

section Hoeffding

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

omit [Fintype n] [DecidableEq n] in
/-- A convex function on all matrices lies above an affine function touching it at a point. -/
private lemma exists_affine_minorant [Finite n] {G : Matrix n n ℂ → ℝ} (hG : ConvexOn ℝ Set.univ G)
    (M₀ : Matrix n n ℂ) :
    ∃ ℓ : Matrix n n ℂ →ₗ[ℝ] ℝ, ∀ M : Matrix n n ℂ, G M₀ + (ℓ M - ℓ M₀) ≤ G M := by
  have := Fintype.ofFinite n
  let _ : NormedAddCommGroup (Matrix n n ℂ) := Matrix.normedAddCommGroup
  let _ : NormedSpace ℝ (Matrix n n ℂ) := Matrix.normedSpace
  obtain ⟨ℓ, hℓ⟩ := exists_le_add_of_concaveOn isOpen_univ hG.neg (Set.mem_univ M₀)
  refine ⟨-ℓ.toLinearMap, fun M => ?_⟩
  have := hℓ M (Set.mem_univ M)
  simp only [Pi.neg_apply, map_sub] at this
  simp only [LinearMap.neg_apply, ContinuousLinearMap.coe_coe]
  linarith

/-- Jensen's inequality for the convex map `M ↦ tr exp(K - θ M)` at a centred random matrix. -/
private lemma ofReal_re_trace_exp_le_lintegral {X : Ω → Matrix n n ℂ} (hX : ∀ ω, (X ω).IsHermitian)
    (hint : ∀ i j, Integrable (fun ω => X ω i j) μ) (hcenter : expect μ X = 0)
    {K : Matrix n n ℂ} (hK : K.IsHermitian) (θ : ℝ) :
    ENNReal.ofReal (RCLike.re (NormedSpace.exp K).trace) ≤
      ∫⁻ ω, ENNReal.ofReal (RCLike.re (NormedSpace.exp (K - θ • X ω)).trace) ∂μ := by
  set G : Matrix n n ℂ → ℝ := fun M => RCLike.re (NormedSpace.exp (K - θ • hermPart M)).trace
  have hG : ConvexOn ℝ Set.univ G := by
    refine ⟨convex_univ, fun M₁ _ M₂ _ a b ha hb hab => ?_⟩
    have h₁ : (K - θ • hermPart M₁).IsHermitian :=
      hK.sub ((IsSelfAdjoint.all θ).smul (realPart M₁).2)
    have h₂ : (K - θ • hermPart M₂).IsHermitian :=
      hK.sub ((IsSelfAdjoint.all θ).smul (realPart M₂).2)
    have h := convexOn_re_trace_exp.2 (show _ ∈ {M : Matrix n n ℂ | M.IsHermitian} from h₁)
      (show _ ∈ {M : Matrix n n ℂ | M.IsHermitian} from h₂) ha hb hab
    have e : a • (K - θ • hermPart M₁) + b • (K - θ • hermPart M₂) =
        K - θ • hermPart (a • M₁ + b • M₂) := by
      rw [map_add, map_smul, map_smul]
      conv_rhs => rw [show K = a • K + b • K by rw [← add_smul, hab, one_smul]]
      simp only [smul_sub, smul_add, smul_smul, mul_comm a θ, mul_comm b θ]
      abel
    simp only [G, smul_eq_mul] at h ⊢
    rw [← e]
    exact h
  obtain ⟨ℓ, hℓ⟩ := exists_affine_minorant hG 0
  obtain ⟨hℓi, hℓe⟩ := integrable_and_integral_linearMap ℓ hint
  rw [hcenter] at hℓe
  have hG0 : G 0 = RCLike.re (NormedSpace.exp K).trace := by simp [G]
  have hGX : ∀ ω, G (X ω) = RCLike.re (NormedSpace.exp (K - θ • X ω)).trace := fun ω => by
    have hPX : hermPart (X ω) = X ω := (hX ω).isSelfAdjoint.coe_realPart
    simp only [G, hPX]
  have h2 : Integrable (fun ω => ℓ (X ω) - ℓ 0) μ := hℓi.sub (integrable_const _)
  have hi : Integrable (fun ω => G 0 + (ℓ (X ω) - ℓ 0)) μ := (integrable_const _).add h2
  calc ENNReal.ofReal (RCLike.re (NormedSpace.exp K).trace)
      = ENNReal.ofReal (∫ ω, (G 0 + (ℓ (X ω) - ℓ 0)) ∂μ) := by
        rw [integral_add (integrable_const _) h2, integral_sub hℓi (integrable_const _), hℓe]
        simp [hG0]
    _ ≤ ENNReal.ofReal (∫ ω, max (G 0 + (ℓ (X ω) - ℓ 0)) 0 ∂μ) :=
        ENNReal.ofReal_le_ofReal (integral_mono hi hi.pos_part fun ω => le_max_left _ _)
    _ = ∫⁻ ω, ENNReal.ofReal (max (G 0 + (ℓ (X ω) - ℓ 0)) 0) ∂μ :=
        ofReal_integral_eq_lintegral_ofReal hi.pos_part
          (Filter.Eventually.of_forall fun ω => le_max_right _ _)
    _ ≤ ∫⁻ ω, ENNReal.ofReal (RCLike.re (NormedSpace.exp (K - θ • X ω)).trace) ∂μ :=
        lintegral_mono fun ω => ENNReal.ofReal_le_ofReal (max_le ((hℓ (X ω)).trans (hGX ω).le)
          (re_trace_exp_nonneg_of_isHermitian (hK.sub ((IsSelfAdjoint.all θ).smul (hX ω)))))

/-- The pointwise symmetrized bound behind the matrix Hoeffding inequality. -/
private lemma re_trace_exp_symm_le {H x x' A : Matrix n n ℂ} (hH : H.IsHermitian)
    (hx : x.IsHermitian)
    (hx' : x'.IsHermitian) (hA : A.IsHermitian) (hxA : (A * A - x * x).PosSemidef)
    (hx'A : (A * A - x' * x').PosSemidef) (θ : ℝ) :
    RCLike.re (NormedSpace.exp (H + θ • (x - x'))).trace +
        RCLike.re (NormedSpace.exp (H + θ • (x' - x))).trace ≤
      2 * RCLike.re (NormedSpace.exp (H + (2 * θ ^ 2) • (A * A))).trace := by
  set Z := x - x'
  have hZ : Z.IsHermitian := hx.sub hx'
  have hZZ : (Z * Z).IsHermitian := by simpa [sq] using hZ.pow 2
  have hneg : θ • (x' - x) = (-θ) • Z := by simp only [Z, neg_smul, ← smul_neg, neg_sub]
  set f : Matrix n n ℂ → ℝ := fun B => RCLike.re (NormedSpace.exp (H + cfc Real.log B)).trace
  have hθZ : (θ • Z).IsHermitian := (IsSelfAdjoint.all θ).smul hZ
  have hθZ' : ((-θ) • Z).IsHermitian := (IsSelfAdjoint.all (-θ)).smul hZ
  have hP₁ := posDef_exp hθZ
  have hP₂ := posDef_exp hθZ'
  have hc := (MathlibExt.LinearAlgebra.Matrix.LiebConcavityWanted.lieb_concavity hH).2 hP₁ hP₂
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
  simp only [smul_eq_mul, cfc_log_exp hθZ, cfc_log_exp hθZ'] at hc
  -- the midpoint is dominated by `exp((θ²/2) Z²)`
  have hmid : (1 / 2 : ℝ) • NormedSpace.exp (θ • Z) + (1 / 2 : ℝ) • NormedSpace.exp ((-θ) • Z) ≤
      NormedSpace.exp ((θ ^ 2 / 2) • (Z * Z)) := by
    rw [hZ.exp_smul_eq_cfc, hZ.exp_smul_eq_cfc, ← cfc_smul .., ← cfc_smul .., ← cfc_add ..,
      hZZ.exp_smul_eq_cfc, ← sq, ← cfc_comp_pow (fun y => Real.exp (θ ^ 2 / 2 * y)) 2 Z]
    refine cfc_mono fun y _ => ?_
    have := Real.cosh_le_exp_half_sq (θ * y)
    rw [Real.cosh_eq] at this
    simp only [smul_eq_mul]
    rw [show θ ^ 2 / 2 * y ^ 2 = (θ * y) ^ 2 / 2 by ring, show -θ * y = -(θ * y) by ring]
    linarith
  have hmidpd : ((1 / 2 : ℝ) • NormedSpace.exp (θ • Z) +
      (1 / 2 : ℝ) • NormedSpace.exp ((-θ) • Z)).PosDef :=
    Matrix.convex_setOfPred_posDef hP₁ hP₂ (by norm_num) (by norm_num) (by norm_num)
  have hmono := lieb_mono hH hmidpd (Matrix.le_iff.1 hmid)
  rw [cfc_log_exp ((IsSelfAdjoint.all _).smul hZZ)] at hmono
  -- `Z² ≼ 4 A²`
  have hZA : ((2 * θ ^ 2) • (A * A) - (θ ^ 2 / 2) • (Z * Z)).PosSemidef := by
    have hsum : (x + x') * (x + x') = (x + x').conjTranspose * (x + x') := by
      rw [(hx.add hx').eq]
    have hpsd : ((x + x') * (x + x')).PosSemidef := by
      rw [hsum]; exact Matrix.posSemidef_conjTranspose_mul_self _
    have key : Z * Z = x * x + x * x + (x' * x' + x' * x') - (x + x') * (x + x') := by
      simp only [Z]
      noncomm_ring
    have h4 : (2 * θ ^ 2) • (A * A) = (θ ^ 2 / 2) • (A * A) + (θ ^ 2 / 2) • (A * A) +
        ((θ ^ 2 / 2) • (A * A) + (θ ^ 2 / 2) • (A * A)) := by
      simp only [← add_smul]
      congr 1
      ring
    have e : (2 * θ ^ 2) • (A * A) - (θ ^ 2 / 2) • (Z * Z) =
        (θ ^ 2 / 2) • ((A * A - x * x) + (A * A - x * x) + ((A * A - x' * x') +
          (A * A - x' * x')) + (x + x') * (x + x')) := by
      rw [key, h4]
      simp only [smul_add, smul_sub]
      abel
    rw [e]
    exact ((((hxA.add hxA).add (hx'A.add hx'A)).add hpsd).smul (by positivity))
  have hAA : (A * A).IsHermitian := by simpa [sq] using hA.pow 2
  have htr := re_trace_exp_le_of_posSemidef (hH.add ((IsSelfAdjoint.all (θ ^ 2 / 2)).smul hZZ))
    (hH.add ((IsSelfAdjoint.all (2 * θ ^ 2)).smul hAA)) (by simpa using hZA)
  rw [hneg]
  linarith

/-- The Hoeffding per-summand bound `E tr exp(H + θX) ≤ tr exp(H + 2θ² A²)`. -/
private lemma lintegral_re_trace_exp_add_le_hoeffding {X : Ω → Matrix n n ℂ} (hm : Measurable X)
    (hX : ∀ ω, (X ω).IsHermitian) {A : Matrix n n ℂ} (hA : A.IsHermitian)
    (hdom : ∀ ω, (A * A - X ω * X ω).PosSemidef)
    (hint : ∀ i j, Integrable (fun ω => X ω i j) μ) (hcenter : expect μ X = 0)
    (θ : ℝ) {H : Matrix n n ℂ} (hH : H.IsHermitian) :
    ∫⁻ ω, ENNReal.ofReal (RCLike.re (NormedSpace.exp (H + θ • X ω)).trace) ∂μ ≤
      ENNReal.ofReal (RCLike.re (NormedSpace.exp (H + (2 * θ ^ 2) • (A * A))).trace) := by
  set F : Ω × Ω → ENNReal := fun p =>
    ENNReal.ofReal (RCLike.re (NormedSpace.exp (H + θ • (X p.1 - X p.2))).trace)
  have hΦ : Continuous fun q : Matrix n n ℂ × Matrix n n ℂ =>
      ENNReal.ofReal (RCLike.re (NormedSpace.exp (H + θ • (q.1 - q.2))).trace) :=
    ENNReal.continuous_ofReal.comp (continuous_re_trace_exp.comp
      (continuous_const.add ((continuous_fst.sub continuous_snd).const_smul θ)))
  have hF : Measurable F := by
    have hXX : Measurable fun p : Ω × Ω => (X p.1, X p.2) :=
      (hm.comp measurable_fst).prodMk (hm.comp measurable_snd)
    have h2 := hΦ.measurable.comp hXX
    exact h2
  set T := ENNReal.ofReal (RCLike.re (NormedSpace.exp (H + (2 * θ ^ 2) • (A * A))).trace)
  have hstep1 : ∫⁻ ω, ENNReal.ofReal (RCLike.re (NormedSpace.exp (H + θ • X ω)).trace) ∂μ ≤
      ∫⁻ p, F p ∂(μ.prod μ) := by
    rw [lintegral_prod _ hF.aemeasurable]
    refine lintegral_mono fun ω => ?_
    refine (ofReal_re_trace_exp_le_lintegral (μ := μ) hX hint hcenter
      (hH.add ((IsSelfAdjoint.all θ).smul (hX ω))) θ).trans
      (le_of_eq (lintegral_congr fun ω' => ?_))
    simp only [F, smul_sub, add_sub_assoc]
  have hswap : ∫⁻ p, F p.swap ∂(μ.prod μ) = ∫⁻ p, F p ∂(μ.prod μ) := lintegral_prod_swap F
  have hnn : ∀ M : Matrix n n ℂ, M.IsHermitian → 0 ≤ RCLike.re (NormedSpace.exp M).trace :=
    fun M hM => re_trace_exp_nonneg_of_isHermitian hM
  have hAA : (A * A).IsHermitian := by simpa [sq] using hA.pow 2
  have hT : (H + (2 * θ ^ 2) • (A * A)).IsHermitian := hH.add ((IsSelfAdjoint.all _).smul hAA)
  have hpt : ∀ p, F p + F p.swap ≤ T + T := fun p => by
    simp only [F, T, Prod.fst_swap, Prod.snd_swap]
    rw [← ENNReal.ofReal_add (hnn _ (hH.add ((IsSelfAdjoint.all θ).smul ((hX _).sub (hX _)))))
      (hnn _ (hH.add ((IsSelfAdjoint.all θ).smul ((hX _).sub (hX _))))),
      ← ENNReal.ofReal_add (hnn _ hT) (hnn _ hT)]
    refine ENNReal.ofReal_le_ofReal ?_
    have := re_trace_exp_symm_le hH (hX p.1) (hX p.2) hA (hdom p.1) (hdom p.2) θ
    linarith
  have h2 : ∫⁻ p, F p ∂(μ.prod μ) + ∫⁻ p, F p ∂(μ.prod μ) ≤ T + T := by
    calc ∫⁻ p, F p ∂(μ.prod μ) + ∫⁻ p, F p ∂(μ.prod μ)
        = ∫⁻ p, F p ∂(μ.prod μ) + ∫⁻ p, F p.swap ∂(μ.prod μ) := by rw [hswap]
      _ = ∫⁻ p, (F p + F p.swap) ∂(μ.prod μ) := (lintegral_add_left hF _).symm
      _ ≤ ∫⁻ _p, (T + T) ∂(μ.prod μ) := lintegral_mono hpt
      _ = T + T := by simp [lintegral_const, measure_univ]
  have h3 : ∫⁻ p, F p ∂(μ.prod μ) ≤ T := by
    by_contra h
    push Not at h
    exact absurd h2 (not_le.2 (ENNReal.add_lt_add h h))
  exact hstep1.trans h3

/-- **Matrix Hoeffding inequality** (Tropp, *User-friendly tail bounds for sums of random
matrices*, Found. Comput. Math. 12 (2012), Theorem 1.3). Let `X₀, …, X_{N-1}` be independent,
centered random Hermitian `d × d` matrices and `A₀, …, A_{N-1}` fixed Hermitian matrices with
`X_k² ⪯ A_k²` (that is, `A_k² - X_k²` positive semidefinite) for every outcome. Let
`σ² = ‖∑ₖ Aₖ²‖ = λmax(∑ₖ Aₖ²)`. Then for all `t ≥ 0`,
`P{λmax(∑ₖ X_k) ≥ t} ≤ d e^{-t²/(8σ²)}`. -/
theorem matrix_hoeffding [Nonempty n] {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {N : ℕ} {X : Fin N → Ω → Matrix n n ℂ}
    (hmeas : ∀ k, Measurable (X k)) (hind : iIndepFun X μ)
    (hX : ∀ k ω, (X k ω).IsHermitian) {A : Fin N → Matrix n n ℂ} (hA : ∀ k, (A k).IsHermitian)
    (hdom : ∀ k ω, (A k * A k - X k ω * X k ω).PosSemidef)
    (hint : ∀ k i j, Integrable (fun ω => X k ω i j) μ) (hcenter : ∀ k, expect μ (X k) = 0)
    (hY : ∀ ω, (∑ k, X k ω).IsHermitian) (hσ : (∑ k, A k * A k).IsHermitian)
    (t : ℝ) (ht : 0 ≤ t) :
    μ.real {ω | t ≤ (hY ω).lambdaMax} ≤
      Fintype.card n * Real.exp (-t ^ 2 / (8 * hσ.lambdaMax)) := by
  set s := hσ.lambdaMax
  have hcard : (1 : ℝ) ≤ Fintype.card n := by exact_mod_cast Fintype.card_pos
  have hAA : ∀ k, (A k * A k).IsHermitian := fun k => by simpa [sq] using (hA k).pow 2
  have hmaster : ∀ θ : ℝ, Integrable (traceMgf (fun ω => ∑ k, X k ω) θ) μ ∧
      ∫ ω, traceMgf (fun ω => ∑ k, X k ω) θ ω ∂μ ≤
        Fintype.card n * Real.exp (2 * θ ^ 2 * s) := by
    intro θ
    have := integrable_and_integral_le_of_forall hmeas hind hX
      (C := fun k => (2 * θ ^ 2) • (A k * A k)) (fun k => (IsSelfAdjoint.all _).smul (hAA k))
      fun k H hH => lintegral_re_trace_exp_add_le_hoeffding (hmeas k) (hX k) (hA k) (hdom k)
        (hint k) (hcenter k) θ hH
    rw [← Finset.smul_sum] at this
    exact ⟨this.1, this.2.trans (re_trace_exp_smul_le_lambdaMax hσ (by positivity))⟩
  have htriv : 0 ≤ -t ^ 2 / (8 * s) → μ.real {ω | t ≤ (hY ω).lambdaMax} ≤
      Fintype.card n * Real.exp (-t ^ 2 / (8 * s)) := fun h =>
    measureReal_le_one.trans (hcard.trans (le_mul_of_one_le_right (by positivity)
      (Real.one_le_exp h)))
  rcases le_or_gt s 0 with hs | hs
  · exact htriv (div_nonneg_of_nonpos (neg_nonpos.2 (sq_nonneg t)) (by linarith))
  rcases ht.eq_or_lt with rfl | ht'
  · exact htriv (by simp)
  set θ := t / (4 * s)
  have hθ : 0 < θ := by positivity
  obtain ⟨hi, hb⟩ := hmaster θ
  calc μ.real {ω | t ≤ (hY ω).lambdaMax}
      ≤ Real.exp (-θ * t) * ∫ ω, traceMgf (fun ω => ∑ k, X k ω) θ ω ∂μ :=
        measureReal_le_lambdaMax_le hY hθ hi t
    _ ≤ Real.exp (-θ * t) * (Fintype.card n * Real.exp (2 * θ ^ 2 * s)) :=
        mul_le_mul_of_nonneg_left hb (Real.exp_pos _).le
    _ = Fintype.card n * Real.exp (-t ^ 2 / (8 * s)) := by
        rw [mul_left_comm, ← Real.exp_add]
        congr 2
        simp only [θ]
        field_simp
        ring

end Hoeffding

end MathlibExt.Probability.MatrixConcentrationWanted

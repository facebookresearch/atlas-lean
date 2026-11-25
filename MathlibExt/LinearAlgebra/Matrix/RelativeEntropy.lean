/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.Analysis.Normed.Algebra.MatrixExponential
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.Matrix.Order
import MathlibExt.LinearAlgebra.Matrix.HermitianTraceExp
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Klein's inequality and the joint convexity of matrix relative entropy

For positive-definite matrices `X` and `Y` write `log X = cfc Real.log X` for the matrix logarithm
and `D(X, Y) = re tr (X log X) - re tr (X log Y)` for the relative entropy of `X` with respect to
`Y`. It differs from the matrix relative entropy of J. A. Tropp, *An Introduction to Matrix
Concentration Inequalities*, Found. Trends Mach. Learn. 8 (2015), arXiv:1501.01571v1,
Definition 8.1.2, by the linear term `tr (Y - X)`, which does not affect convexity.

## Main declarations

* `Matrix.convex_setOfPred_posDef`: positive-definite matrices form a convex set.
* `trace_cfc_mul_cfc`: for Hermitian `A = U diag(λ) U*` and `B = V diag(μ) V*` and any
  `f g : ℝ → ℝ`, `tr (f(A) g(B)) = ∑ᵢ ∑ⱼ f(λᵢ) g(μⱼ) |(U* V)ᵢⱼ|²`, the computation in the proof
  of Tropp, Proposition 8.3.5.
* `re_trace_mul_cfc_log_sub_le`: Klein's inequality `tr (X log X - X log Y - X + Y) ≥ 0`
  (Tropp, Proposition 8.1.3).
* `isGreatest_re_trace_exp`: the variational formula
  `tr e^M = max_{X ≻ 0} tr (X M - X log X + X)` for Hermitian `M` (Tropp, Lemma 8.1.6).
* `convexOn_relativeEntropy`: `D` is jointly convex (Tropp, Theorem 8.1.4).

Klein's inequality also appears, for operators on an inner product space and written in the
eigenbasis of one of them, as `MathlibExt.Analysis.InnerProductSpace.PeierlsKlein.klein_entropy`;
here it follows in a few lines from `trace_cfc_mul_cfc`, in the trace form used below.

## Proof of the joint convexity

Tropp derives the joint convexity from the operator convexity of matrix perspectives (Sections
8.4 to 8.8). The proof here keeps two of his ingredients, the integral representation of the
logarithm (Proposition 8.4.1) and the operator `W ↦ X W + s W Y` on matrices, and replaces the
operator convexity of perspectives by a supremum of linear functionals. For `s > 0` let
`φ_s(X, Y) = sup_W [2 re tr (W* Y) - re tr (W* X W) - s re tr (W Y W*)]`, the supremum over all
matrices `W`. Each functional in the supremum is linear in `(X, Y)`, so `φ_s` is jointly convex.
In the eigenbases `X = U diag(x) U*` and `Y = V diag(y) V*`, write `W = U W' V*` and `B = U* V`:
the functional becomes `∑ᵢ ∑ⱼ (2 yⱼ re (conj W'ᵢⱼ Bᵢⱼ) - (xᵢ + s yⱼ) |W'ᵢⱼ|²)`, whose supremum is
attained entrywise at `W'ᵢⱼ = yⱼ Bᵢⱼ / (xᵢ + s yⱼ)`. With `tr X = ∑ᵢ ∑ⱼ |Bᵢⱼ|² xᵢ` and
`tr Y = ∑ᵢ ∑ⱼ |Bᵢⱼ|² yⱼ` this gives
`re tr X / (1 + s) - re tr Y + s φ_s(X, Y) = ∑ᵢ ∑ⱼ |Bᵢⱼ|² xᵢ (xᵢ - yⱼ) / ((1 + s) (xᵢ + s yⱼ))`.
Since `∫₀^∞ x (x - y) / ((1 + s) (x + s y)) ds = x log x - x log y` for `x, y > 0`, the relative
entropy `D(X, Y)` is the integral over `s ∈ (0, ∞)` of the jointly convex functions
`re tr X / (1 + s) - re tr Y + s φ_s(X, Y)`, hence jointly convex.
-/

@[expose] public section

open scoped ComplexOrder

/-! ### Convexity of the positive-definite cone -/

/-- **Positive-definite matrices form a convex set.** For any index type `n` and `𝕜 = ℝ` or `ℂ`,
the set of positive-definite `n × n` matrices over `𝕜` is convex: if `A` and `B` are positive
definite and `a, b` are nonnegative reals with `a + b = 1`, then `a • A + b • B` is positive
definite. -/
theorem Matrix.convex_setOfPred_posDef {n 𝕜 : Type*} [RCLike 𝕜] :
    Convex ℝ {A : Matrix n n 𝕜 | A.PosDef} := by
  intro A hA B hB a b ha hb hab
  rcases ha.eq_or_lt with rfl | ha'
  · simp only [zero_add] at hab
    simpa [hab] using hB
  · exact (hA.smul (by exact_mod_cast ha')).add_posSemidef
      (hB.posSemidef.smul (by exact_mod_cast hb))

namespace MathlibExt.LinearAlgebra.Matrix.RelativeEntropy

variable {n 𝕜 : Type*} [Fintype n] [DecidableEq n] [RCLike 𝕜]

/-! ### Traces of products of matrix functions -/

/-- **Trace of a product of two matrix functions.** Let `A` and `B` be Hermitian matrices over
`ℝ` or `ℂ`, with spectral decompositions `A = U diag(λ) U*` and `B = V diag(μ) V*` given by
Mathlib's `Matrix.IsHermitian.eigenvalues` and `Matrix.IsHermitian.eigenvectorUnitary`. For all
functions `f g : ℝ → ℝ`, `tr (f(A) g(B)) = ∑ᵢ ∑ⱼ f(λᵢ) g(μⱼ) |(U* V)ᵢⱼ|²`, where `f(A) = cfc f A`
and `g(B) = cfc g B` are the standard matrix functions (the computation in the proof of
J. A. Tropp, *An Introduction to Matrix Concentration Inequalities*, arXiv:1501.01571v1,
Proposition 8.3.5). -/
theorem trace_cfc_mul_cfc {A B : Matrix n n 𝕜} (hA : A.IsHermitian) (hB : B.IsHermitian)
    (f g : ℝ → ℝ) :
    (cfc f A * cfc g B).trace = ∑ i, ∑ j,
      ((f (hA.eigenvalues i) * g (hB.eigenvalues j) *
        ‖(star (hA.eigenvectorUnitary : Matrix n n 𝕜) * hB.eigenvectorUnitary) i j‖ ^ 2 : ℝ) :
          𝕜) := by
  set U : Matrix n n 𝕜 := ↑hA.eigenvectorUnitary with hU
  set V : Matrix n n 𝕜 := ↑hB.eigenvectorUnitary with hV
  set W : Matrix n n 𝕜 := star U * V with hW
  rw [hA.cfc_eq, hB.cfc_eq, Matrix.IsHermitian.cfc, Matrix.IsHermitian.cfc,
    Unitary.conjStarAlgAut_apply, Unitary.conjStarAlgAut_apply]
  set Df : Matrix n n 𝕜 := Matrix.diagonal (RCLike.ofReal ∘ f ∘ hA.eigenvalues)
  set Dg : Matrix n n 𝕜 := Matrix.diagonal (RCLike.ofReal ∘ g ∘ hB.eigenvalues)
  have hcyc : (U * Df * star U * (V * Dg * star V)).trace = (Df * W * Dg * star W).trace := by
    rw [hW, star_mul, star_star]
    simp only [Matrix.mul_assoc]
    rw [Matrix.trace_mul_comm]
    simp only [Matrix.mul_assoc]
  rw [hcyc, Matrix.trace]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.diag_apply, Matrix.mul_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.star_apply]
  have h := RCLike.mul_conj (W i j)
  simp only [Function.comp_apply, RCLike.star_def] at *
  push_cast
  linear_combination (f (hA.eigenvalues i) : 𝕜) * (g (hB.eigenvalues j) : 𝕜) * h

/-- The real part of `trace_cfc_mul_cfc`. -/
private lemma re_trace_cfc_mul_cfc {A B : Matrix n n 𝕜} (hA : A.IsHermitian) (hB : B.IsHermitian)
    (f g : ℝ → ℝ) :
    RCLike.re (cfc f A * cfc g B).trace = ∑ i, ∑ j,
      f (hA.eigenvalues i) * g (hB.eigenvalues j) *
        ‖(star (hA.eigenvectorUnitary : Matrix n n 𝕜) * hB.eigenvectorUnitary) i j‖ ^ 2 := by
  rw [trace_cfc_mul_cfc hA hB f g]
  simp only [map_sum, RCLike.ofReal_re]

/-- Every function is continuous on the finite spectrum of a matrix. -/
private lemma continuousOn_spectrum (A : Matrix n n 𝕜) (f : ℝ → ℝ) :
    ContinuousOn f (spectrum ℝ A) :=
  A.finite_real_spectrum.continuousOn f

section Coordinates

variable {X Y : Matrix n n 𝕜}

/-- The overlap matrix `U* V` of the eigenbases of two Hermitian matrices. -/
private noncomputable abbrev ov (hX : X.IsHermitian) (hY : Y.IsHermitian) : Matrix n n 𝕜 :=
  star (hX.eigenvectorUnitary : Matrix n n 𝕜) * hY.eigenvectorUnitary

private lemma re_trace_eq_sum_left (hX : X.IsHermitian) (hY : Y.IsHermitian) :
    RCLike.re X.trace = ∑ i, ∑ j, hX.eigenvalues i * ‖ov hX hY i j‖ ^ 2 := by
  have h := re_trace_cfc_mul_cfc hX hY id (fun _ => 1)
  rw [cfc_id ℝ X hX.isSelfAdjoint, cfc_const_one ℝ Y, Matrix.mul_one] at h
  simpa using h

private lemma re_trace_eq_sum_right (hX : X.IsHermitian) (hY : Y.IsHermitian) :
    RCLike.re Y.trace = ∑ i, ∑ j, hY.eigenvalues j * ‖ov hX hY i j‖ ^ 2 := by
  have h := re_trace_cfc_mul_cfc hX hY (fun _ => 1) id
  rw [cfc_id ℝ Y hY.isSelfAdjoint, cfc_const_one ℝ X, Matrix.one_mul] at h
  simpa using h

private lemma re_trace_mul_cfc_log_eq_sum (hX : X.IsHermitian) (hY : Y.IsHermitian) :
    RCLike.re (X * cfc Real.log Y).trace =
      ∑ i, ∑ j, hX.eigenvalues i * Real.log (hY.eigenvalues j) * ‖ov hX hY i j‖ ^ 2 := by
  have h := re_trace_cfc_mul_cfc hX hY id Real.log
  rwa [cfc_id ℝ X hX.isSelfAdjoint] at h

private lemma re_trace_mul_cfc_log_self_eq_sum (hX : X.IsHermitian) (hY : Y.IsHermitian) :
    RCLike.re (X * cfc Real.log X).trace =
      ∑ i, ∑ j, hX.eigenvalues i * Real.log (hX.eigenvalues i) * ‖ov hX hY i j‖ ^ 2 := by
  have h := re_trace_cfc_mul_cfc hX hY (fun x => x * Real.log x) (fun _ => 1)
  rw [cfc_const_one ℝ Y, Matrix.mul_one, cfc_mul (fun x : ℝ => x) Real.log X
    (continuousOn_spectrum X _) (continuousOn_spectrum X _), cfc_id' ℝ X hX.isSelfAdjoint] at h
  simpa using h

end Coordinates

/-! ### Klein's inequality and the variational formula for the trace exponential -/

/-- The scalar Klein inequality `x (log y - log x) ≤ y - x` for `x, y > 0`. -/
private lemma log_mul_sub_le {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    x * (Real.log y - Real.log x) ≤ y - x := by
  have h := Real.log_le_sub_one_of_pos (div_pos hy hx)
  rw [Real.log_div hy.ne' hx.ne'] at h
  calc x * (Real.log y - Real.log x) ≤ x * (y / x - 1) := mul_le_mul_of_nonneg_left h hx.le
    _ = y - x := by field_simp

/-- **Klein's inequality for the matrix relative entropy**: the matrix relative entropy is
nonnegative (J. A. Tropp, *An Introduction to Matrix Concentration Inequalities*,
arXiv:1501.01571v1, Proposition 8.1.3; Tropp, *From joint convexity of quantum relative entropy
to a concavity theorem of Lieb*, arXiv:1101.1070v1, Fact 3). For positive-definite matrices `X`
and `Y` over `ℝ` or `ℂ`,
`re tr (X log Y) - re tr (X log X) ≤ re tr Y - re tr X`, where `log` is the matrix function
`cfc Real.log`; that is, `tr (X log X - X log Y - X + Y) ≥ 0`. -/
theorem re_trace_mul_cfc_log_sub_le {X Y : Matrix n n 𝕜} (hX : X.PosDef) (hY : Y.PosDef) :
    RCLike.re (X * cfc Real.log Y).trace - RCLike.re (X * cfc Real.log X).trace ≤
      RCLike.re Y.trace - RCLike.re X.trace := by
  have hX' := hX.isHermitian
  have hY' := hY.isHermitian
  rw [re_trace_mul_cfc_log_eq_sum hX' hY', re_trace_mul_cfc_log_self_eq_sum hX' hY',
    re_trace_eq_sum_left hX' hY', re_trace_eq_sum_right hX' hY', ← Finset.sum_sub_distrib,
    ← Finset.sum_sub_distrib]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_le_sum fun j _ => ?_
  have hx : 0 < hX'.eigenvalues i := hX.eigenvalues_pos i
  have hy : 0 < hY'.eigenvalues j := hY.eigenvalues_pos j
  have hw : 0 ≤ ‖ov hX' hY' i j‖ ^ 2 := by positivity
  have hlog := log_mul_sub_le hx hy
  nlinarith

/-- The matrix exponential of a Hermitian matrix is the matrix function of `Real.exp`. -/
private lemma exp_eq_cfc {M : Matrix n n 𝕜} (hM : M.IsHermitian) :
    NormedSpace.exp M = cfc Real.exp M := by
  simpa only [one_smul, one_mul] using hM.exp_smul_eq_cfc 1

/-- The matrix logarithm inverts the matrix exponential on Hermitian matrices. -/
private lemma cfc_log_exp {M : Matrix n n 𝕜} (hM : M.IsHermitian) :
    cfc Real.log (NormedSpace.exp M) = M := by
  rw [exp_eq_cfc hM, ← cfc_comp Real.log Real.exp M hM.isSelfAdjoint
    ((M.finite_real_spectrum.image _).continuousOn _) (continuousOn_spectrum M _)]
  simp only [Function.comp_def, Real.log_exp]
  exact cfc_id' ℝ M hM.isSelfAdjoint

open scoped MatrixOrder in
/-- The matrix exponential of a Hermitian matrix is positive definite. -/
private lemma posDef_exp {M : Matrix n n 𝕜} (hM : M.IsHermitian) :
    (NormedSpace.exp M).PosDef := by
  rw [exp_eq_cfc hM, ← Matrix.isStrictlyPositive_iff_posDef]
  exact (cfc_isStrictlyPositive_iff Real.exp M (continuousOn_spectrum M _) hM.isSelfAdjoint).mpr
    fun x _ => Real.exp_pos x

/-- The inequality half of `isGreatest_re_trace_exp`, from Klein's inequality. -/
private lemma gibbs_le {M X : Matrix n n 𝕜} (hM : M.IsHermitian) (hX : X.PosDef) :
    RCLike.re (X * M).trace - RCLike.re (X * cfc Real.log X).trace + RCLike.re X.trace ≤
      RCLike.re (NormedSpace.exp M).trace := by
  have h := re_trace_mul_cfc_log_sub_le hX (posDef_exp hM)
  rw [cfc_log_exp hM] at h
  linarith

/-- **Variational formula for the trace exponential** (J. A. Tropp, *An Introduction to Matrix
Concentration Inequalities*, arXiv:1501.01571v1, Lemma 8.1.6 applied to `e^M`; Tropp, *From joint
convexity of quantum relative entropy to a concavity theorem of Lieb*, arXiv:1101.1070v1,
Lemma 6). For a Hermitian matrix `M` over `ℝ` or `ℂ`, `re tr e^M` is the greatest value of
`re tr (X M) - re tr (X log X) + re tr X` over positive-definite matrices `X`, attained at
`X = e^M`. Here `e^M` is the matrix exponential and `log X = cfc Real.log X`. -/
theorem isGreatest_re_trace_exp {M : Matrix n n 𝕜} (hM : M.IsHermitian) :
    IsGreatest ((fun X : Matrix n n 𝕜 => RCLike.re (X * M).trace -
        RCLike.re (X * cfc Real.log X).trace + RCLike.re X.trace) '' {X | X.PosDef})
      (RCLike.re (NormedSpace.exp M).trace) := by
  refine ⟨⟨NormedSpace.exp M, posDef_exp hM, ?_⟩, ?_⟩
  · simp only [cfc_log_exp hM, sub_self, zero_add]
  · rintro _ ⟨X, hX, rfl⟩
    exact gibbs_le hM hX

/-! ### An integral representation of `x log x - x log y` -/

open Filter Topology MeasureTheory in
/-- For `x, y > 0`, `x log x - x log y = ∫₀^∞ x (x - y) / ((1 + s) (x + s y)) ds`, and the
integrand is integrable on `(0, ∞)`. Since the integrand is `x (1 / (1 + s) - 1 / (x / y + s))`,
this is `x` times the integral representation `log a = ∫₀^∞ (1 / (1 + s) - 1 / (a + s)) ds` at
`a = x / y` (J. A. Tropp, *An Introduction to Matrix Concentration Inequalities*,
arXiv:1501.01571v1, Proposition 8.4.1). An antiderivative is `x log (1 + s) - x log (x + s y)`. -/
private lemma integral_scalar {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    IntegrableOn (fun s => x * (x - y) / ((1 + s) * (x + s * y))) (Set.Ioi 0) ∧
      ∫ s in Set.Ioi (0 : ℝ), x * (x - y) / ((1 + s) * (x + s * y)) =
        x * Real.log x - x * Real.log y := by
  set F : ℝ → ℝ := fun s => x * Real.log (1 + s) - x * Real.log (x + s * y) with hF
  have hderiv : ∀ s ∈ Set.Ici (0 : ℝ),
      HasDerivAt F (x * (x - y) / ((1 + s) * (x + s * y))) s := by
    intro s hs
    have hs : 0 ≤ s := hs
    have h1 : 0 < 1 + s := by linarith
    have h2 : 0 < x + s * y := by positivity
    have d1 : HasDerivAt (fun s => Real.log (1 + s)) (1 / (1 + s)) s := by
      simpa using ((hasDerivAt_id s).const_add 1).log h1.ne'
    have d2 : HasDerivAt (fun s => Real.log (x + s * y)) (y / (x + s * y)) s := by
      simpa using (((hasDerivAt_id s).mul_const y).const_add x).log h2.ne'
    convert (d1.const_mul x).sub (d2.const_mul x) using 1
    field_simp
    ring
  have hlim : Tendsto F atTop (𝓝 (-(x * Real.log y))) := by
    have hden : Tendsto (fun s : ℝ => y * (x + s * y)) atTop atTop :=
      Tendsto.const_mul_atTop hy
        (tendsto_atTop_add_const_left _ x (tendsto_id.atTop_mul_const hy))
    have hq : Tendsto (fun s : ℝ => 1 / y + (y - x) / (y * (x + s * y))) atTop (𝓝 (1 / y)) := by
      simpa using (tendsto_const_nhds (x := 1 / y)).add (tendsto_const_nhds.div_atTop hden)
    have hlog := (hq.log (by positivity)).const_mul x
    rw [one_div, Real.log_inv, mul_neg] at hlog
    refine hlog.congr' ?_
    filter_upwards [eventually_ge_atTop 0] with s hs
    have h1 : 0 < 1 + s := by linarith
    have h2 : 0 < x + s * y := by positivity
    have : y⁻¹ + (y - x) / (y * (x + s * y)) = (1 + s) / (x + s * y) := by
      field_simp
      ring
    rw [this, Real.log_div h1.ne' h2.ne', hF, mul_sub]
  have hint : IntegrableOn (fun s => x * (x - y) / ((1 + s) * (x + s * y))) (Set.Ioi 0) := by
    rcases le_total y x with hyx | hxy
    · refine integrableOn_Ioi_deriv_of_nonneg' hderiv (fun s hs => ?_) hlim
      have hs : 0 < s := hs
      have : 0 ≤ x - y := by linarith
      positivity
    · refine integrableOn_Ioi_deriv_of_nonpos' hderiv (fun s hs => ?_) hlim
      have hs : 0 < s := hs
      have h1 : 0 < (1 + s) * (x + s * y) := by positivity
      exact div_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonneg_of_nonpos hx.le (by linarith)) h1.le
  refine ⟨hint, ?_⟩
  rw [integral_Ioi_of_hasDerivAt_of_tendsto' hderiv hint hlim]
  simp only [hF, add_zero, zero_mul, Real.log_one, mul_zero]
  ring

/-! ### The functionals in the eigenbases -/

section CoordinatesW

variable {X Y : Matrix n n 𝕜}

/-- Conjugation by a unitary preserves the trace. -/
private lemma trace_conj_unitary {V : Matrix n n 𝕜} (hV : star V * V = 1) (M : Matrix n n 𝕜) :
    (V * M * star V).trace = M.trace := by
  rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, hV, Matrix.one_mul]

private lemma re_trace_star_mul_right (hX : X.IsHermitian) (hY : Y.IsHermitian)
    (W' : Matrix n n 𝕜) :
    RCLike.re (star ((hX.eigenvectorUnitary : Matrix n n 𝕜) * W' *
        star (hY.eigenvectorUnitary : Matrix n n 𝕜)) * Y).trace =
      ∑ i, ∑ j, hY.eigenvalues j * RCLike.re (star (W' i j) * ov hX hY i j) := by
  set U : Matrix n n 𝕜 := ↑hX.eigenvectorUnitary
  set V : Matrix n n 𝕜 := ↑hY.eigenvectorUnitary
  have hV : star V * V = 1 := Unitary.coe_star_mul_self _
  set Dy : Matrix n n 𝕜 := Matrix.diagonal (RCLike.ofReal ∘ hY.eigenvalues)
  have hY' : Y = V * Dy * star V := by
    conv_lhs => rw [hY.spectral_theorem]
    rfl
  have e : star (U * W' * star V) * Y = V * (star W' * (star U * V) * Dy) * star V := by
    rw [hY', star_mul, star_mul, star_star]
    simp only [Matrix.mul_assoc]
  rw [e, trace_conj_unitary hV, Matrix.trace, map_sum, Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Matrix.diag_apply, Matrix.mul_diagonal, Matrix.mul_apply, Finset.sum_mul, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.star_apply, Function.comp_apply, mul_comm, RCLike.re_ofReal_mul]

private lemma re_trace_star_mul_left_mul (hX : X.IsHermitian) (hY : Y.IsHermitian)
    (W' : Matrix n n 𝕜) :
    RCLike.re (star ((hX.eigenvectorUnitary : Matrix n n 𝕜) * W' *
        star (hY.eigenvectorUnitary : Matrix n n 𝕜)) * X *
        ((hX.eigenvectorUnitary : Matrix n n 𝕜) * W' *
        star (hY.eigenvectorUnitary : Matrix n n 𝕜))).trace =
      ∑ i, ∑ j, hX.eigenvalues i * ‖W' i j‖ ^ 2 := by
  set U : Matrix n n 𝕜 := ↑hX.eigenvectorUnitary
  set V : Matrix n n 𝕜 := ↑hY.eigenvectorUnitary
  have hU : ∀ M : Matrix n n 𝕜, star U * (U * M) = M := fun M => by
    rw [← Matrix.mul_assoc, Unitary.coe_star_mul_self, Matrix.one_mul]
  have hV : star V * V = 1 := Unitary.coe_star_mul_self _
  set Dx : Matrix n n 𝕜 := Matrix.diagonal (RCLike.ofReal ∘ hX.eigenvalues)
  have hX' : X = U * Dx * star U := by
    conv_lhs => rw [hX.spectral_theorem]
    rfl
  have e : star (U * W' * star V) * X * (U * W' * star V) = V * (star W' * Dx * W') * star V := by
    rw [hX', star_mul, star_mul, star_star]
    simp only [Matrix.mul_assoc, hU]
  rw [e, trace_conj_unitary hV, Matrix.trace, map_sum, Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Matrix.diag_apply, Matrix.mul_apply, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.mul_diagonal, Matrix.star_apply, Function.comp_apply, RCLike.star_def,
    mul_comm (starRingEnd 𝕜 (W' i j)), mul_assoc, RCLike.conj_mul, RCLike.re_ofReal_mul]
  norm_cast

private lemma re_trace_mul_right_mul_star (hX : X.IsHermitian) (hY : Y.IsHermitian)
    (W' : Matrix n n 𝕜) :
    RCLike.re ((hX.eigenvectorUnitary : Matrix n n 𝕜) * W' *
        star (hY.eigenvectorUnitary : Matrix n n 𝕜) * Y *
        star ((hX.eigenvectorUnitary : Matrix n n 𝕜) * W' *
        star (hY.eigenvectorUnitary : Matrix n n 𝕜))).trace =
      ∑ i, ∑ j, hY.eigenvalues j * ‖W' i j‖ ^ 2 := by
  set U : Matrix n n 𝕜 := ↑hX.eigenvectorUnitary
  set V : Matrix n n 𝕜 := ↑hY.eigenvectorUnitary
  have hU : star U * U = 1 := Unitary.coe_star_mul_self _
  have hV : ∀ M : Matrix n n 𝕜, star V * (V * M) = M := fun M => by
    rw [← Matrix.mul_assoc, Unitary.coe_star_mul_self, Matrix.one_mul]
  set Dy : Matrix n n 𝕜 := Matrix.diagonal (RCLike.ofReal ∘ hY.eigenvalues)
  have hY' : Y = V * Dy * star V := by
    conv_lhs => rw [hY.spectral_theorem]
    rfl
  have e : U * W' * star V * Y * star (U * W' * star V) = U * (W' * Dy * star W') * star U := by
    rw [hY', star_mul, star_mul, star_star]
    simp only [Matrix.mul_assoc, hV]
  rw [e, trace_conj_unitary hU, Matrix.trace, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.diag_apply, Matrix.mul_apply, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Matrix.mul_diagonal, Matrix.star_apply, Function.comp_apply, RCLike.star_def,
    mul_comm (W' i j), mul_assoc, RCLike.mul_conj, RCLike.re_ofReal_mul]
  norm_cast

end CoordinatesW

/-! ### The integrand as a supremum of linear functionals -/

section Integrand

variable {X Y : Matrix n n 𝕜}

/-- For `s > 0` and a matrix `W`, the functional
`re tr X / (1 + s) - re tr Y + s (2 re tr (W* Y) - re tr (W* X W) - s re tr (W Y W*))`, linear in
`(X, Y)`. For positive-definite `X` and `Y` its supremum over `W` is `integrand` (see
`testFunctional_le` and `exists_testFunctional_eq`). -/
private noncomputable def testFunctional (s : ℝ) (W X Y : Matrix n n 𝕜) : ℝ :=
  RCLike.re X.trace / (1 + s) - RCLike.re Y.trace +
    s * (2 * RCLike.re (star W * Y).trace - RCLike.re (star W * X * W).trace -
      s * RCLike.re (W * Y * star W).trace)

omit [DecidableEq n] in
private lemma testFunctional_add_smul (s a b : ℝ) (W X₁ Y₁ X₂ Y₂ : Matrix n n 𝕜) :
    testFunctional s W (a • X₁ + b • X₂) (a • Y₁ + b • Y₂) =
      a * testFunctional s W X₁ Y₁ + b * testFunctional s W X₂ Y₂ := by
  simp only [testFunctional, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.trace_add, Matrix.trace_smul, map_add, RCLike.smul_re]
  ring

/-- The integrand of the integral representation of the relative entropy, written in the
eigenbases of `X` and `Y`. -/
private noncomputable def integrand (hX : X.IsHermitian) (hY : Y.IsHermitian) (s : ℝ) : ℝ :=
  ∑ i, ∑ j, ‖ov hX hY i j‖ ^ 2 * (hX.eigenvalues i * (hX.eigenvalues i - hY.eigenvalues j) /
    ((1 + s) * (hX.eigenvalues i + s * hY.eigenvalues j)))

private lemma testFunctional_eq_sum (hX : X.IsHermitian) (hY : Y.IsHermitian) (s : ℝ)
    (W' : Matrix n n 𝕜) :
    testFunctional s ((hX.eigenvectorUnitary : Matrix n n 𝕜) * W' *
        star (hY.eigenvectorUnitary : Matrix n n 𝕜)) X Y =
      ∑ i, ∑ j, (‖ov hX hY i j‖ ^ 2 * hX.eigenvalues i / (1 + s) -
        ‖ov hX hY i j‖ ^ 2 * hY.eigenvalues j +
        s * (2 * hY.eigenvalues j * RCLike.re (star (W' i j) * ov hX hY i j) -
          (hX.eigenvalues i + s * hY.eigenvalues j) * ‖W' i j‖ ^ 2)) := by
  rw [testFunctional, re_trace_eq_sum_left hX hY, re_trace_eq_sum_right hX hY,
    re_trace_star_mul_right hX hY, re_trace_star_mul_left_mul hX hY,
    re_trace_mul_right_mul_star hX hY]
  simp only [Finset.mul_sum, Finset.sum_div, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

/-- The pointwise bound behind `testFunctional_le`: for `c = x + s y > 0`,
`2 y re (w̄ b) - c |w|² ≤ y² |b|² / c`, since the difference is `|c w - y b|² / c`. -/
private lemma two_mul_re_sub_le {c y : ℝ} (hc : 0 < c) (w b : 𝕜) :
    2 * y * RCLike.re (star w * b) - c * ‖w‖ ^ 2 ≤ y ^ 2 * ‖b‖ ^ 2 / c := by
  rw [le_div_iff₀ hc, RCLike.norm_sq_eq_def, RCLike.norm_sq_eq_def, RCLike.star_def,
    RCLike.mul_re, RCLike.conj_re, RCLike.conj_im]
  nlinarith [sq_nonneg (c * RCLike.re w - y * RCLike.re b),
    sq_nonneg (c * RCLike.im w - y * RCLike.im b)]

private lemma term_le {x y s : ℝ} (hx : 0 < x) (hy : 0 < y) (hs : 0 < s) (b w : 𝕜) :
    ‖b‖ ^ 2 * x / (1 + s) - ‖b‖ ^ 2 * y +
        s * (2 * y * RCLike.re (star w * b) - (x + s * y) * ‖w‖ ^ 2) ≤
      ‖b‖ ^ 2 * (x * (x - y) / ((1 + s) * (x + s * y))) := by
  have hc : 0 < x + s * y := by positivity
  have h1 : 0 < 1 + s := by linarith
  have key := mul_le_mul_of_nonneg_left (two_mul_re_sub_le (y := y) hc w b) hs.le
  have e : ‖b‖ ^ 2 * x / (1 + s) - ‖b‖ ^ 2 * y =
      ‖b‖ ^ 2 * (x * (x - y) / ((1 + s) * (x + s * y))) - s * (y ^ 2 * ‖b‖ ^ 2 / (x + s * y)) := by
    field_simp
    ring
  rw [e]
  linarith

private lemma term_eq {x y s : ℝ} (hx : 0 < x) (hy : 0 < y) (hs : 0 < s) (b : 𝕜) :
    ‖b‖ ^ 2 * x / (1 + s) - ‖b‖ ^ 2 * y +
        s * (2 * y * RCLike.re (star (((y / (x + s * y) : ℝ) : 𝕜) * b) * b) -
          (x + s * y) * ‖((y / (x + s * y) : ℝ) : 𝕜) * b‖ ^ 2) =
      ‖b‖ ^ 2 * (x * (x - y) / ((1 + s) * (x + s * y))) := by
  have hc : 0 < x + s * y := by positivity
  have h1 : 0 < 1 + s := by linarith
  rw [star_mul, RCLike.star_def, RCLike.conj_ofReal, mul_comm (starRingEnd 𝕜 b),
    mul_assoc (((y / (x + s * y) : ℝ) : 𝕜)), RCLike.conj_mul, norm_mul, RCLike.norm_ofReal,
    abs_of_nonneg (by positivity)]
  norm_cast
  field_simp
  ring

private lemma testFunctional_le (hX : X.PosDef) (hY : Y.PosDef) {s : ℝ} (hs : 0 < s)
    (W : Matrix n n 𝕜) :
    testFunctional s W X Y ≤ integrand hX.isHermitian hY.isHermitian s := by
  set U : Matrix n n 𝕜 := ↑hX.isHermitian.eigenvectorUnitary
  set V : Matrix n n 𝕜 := ↑hY.isHermitian.eigenvectorUnitary
  have hUU : U * star U = 1 := Unitary.coe_mul_star_self _
  have hVV : V * star V = 1 := Unitary.coe_mul_star_self _
  have hW : W = U * (star U * W * V) * star V := by
    calc W = U * star U * W * (V * star V) := by rw [hUU, hVV, Matrix.one_mul, Matrix.mul_one]
      _ = U * (star U * W * V) * star V := by simp only [Matrix.mul_assoc]
  rw [hW, testFunctional_eq_sum, integrand]
  refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
  exact term_le (hX.eigenvalues_pos i) (hY.eigenvalues_pos j) hs _ _

private lemma exists_testFunctional_eq (hX : X.PosDef) (hY : Y.PosDef) {s : ℝ} (hs : 0 < s) :
    ∃ W, testFunctional s W X Y = integrand hX.isHermitian hY.isHermitian s := by
  set x := hX.isHermitian.eigenvalues
  set y := hY.isHermitian.eigenvalues
  refine ⟨(hX.isHermitian.eigenvectorUnitary : Matrix n n 𝕜) *
      Matrix.of (fun i j => ((y j / (x i + s * y j) : ℝ) : 𝕜) *
        ov hX.isHermitian hY.isHermitian i j) *
      star (hY.isHermitian.eigenvectorUnitary : Matrix n n 𝕜), ?_⟩
  rw [testFunctional_eq_sum, integrand]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  exact term_eq (hX.eigenvalues_pos i) (hY.eigenvalues_pos j) hs _

end Integrand

/-! ### Joint convexity of the relative entropy -/

section JointConvexity

open MeasureTheory

variable {X Y : Matrix n n 𝕜}

private lemma integrableOn_integrand (hX : X.PosDef) (hY : Y.PosDef) :
    IntegrableOn (integrand hX.isHermitian hY.isHermitian) (Set.Ioi 0) := by
  refine integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => ?_
  exact (integral_scalar (hX.eigenvalues_pos i) (hY.eigenvalues_pos j)).1.const_mul _

private lemma integral_integrand (hX : X.PosDef) (hY : Y.PosDef) :
    ∫ s in Set.Ioi (0 : ℝ), integrand hX.isHermitian hY.isHermitian s =
      RCLike.re (X * cfc Real.log X).trace - RCLike.re (X * cfc Real.log Y).trace := by
  have hint : ∀ i j, IntegrableOn (fun s => ‖ov hX.isHermitian hY.isHermitian i j‖ ^ 2 *
      (hX.isHermitian.eigenvalues i * (hX.isHermitian.eigenvalues i -
        hY.isHermitian.eigenvalues j) / ((1 + s) * (hX.isHermitian.eigenvalues i +
          s * hY.isHermitian.eigenvalues j)))) (Set.Ioi 0) := fun i j =>
    (integral_scalar (hX.eigenvalues_pos i) (hY.eigenvalues_pos j)).1.const_mul _
  rw [re_trace_mul_cfc_log_self_eq_sum hX.isHermitian hY.isHermitian,
    re_trace_mul_cfc_log_eq_sum hX.isHermitian hY.isHermitian, ← Finset.sum_sub_distrib]
  simp only [integrand]
  rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hint i j]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_finsetSum _ fun j _ => hint i j, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [integral_const_mul, (integral_scalar (hX.eigenvalues_pos i) (hY.eigenvalues_pos j)).2]
  ring

/-- **Joint convexity of the matrix relative entropy** (J. A. Tropp, *An Introduction to Matrix
Concentration Inequalities*, arXiv:1501.01571v1, Theorem 8.1.4; Tropp, *From joint convexity of
quantum relative entropy to a concavity theorem of Lieb*, arXiv:1101.1070v1, Fact 4, which
attributes it to Lindblad). The map `(X, Y) ↦ re tr (X log X) - re tr (X log Y)` is jointly convex
on the set of pairs of positive-definite matrices over `ℝ` or `ℂ`, where `log` is the matrix
function `cfc Real.log`. Tropp's relative entropy `tr (X log X - X log Y - X + Y)` differs from
it by a linear function of `(X, Y)`, so it is jointly convex as well. -/
theorem convexOn_relativeEntropy :
    ConvexOn ℝ {p : Matrix n n 𝕜 × Matrix n n 𝕜 | p.1.PosDef ∧ p.2.PosDef}
      (fun p => RCLike.re (p.1 * cfc Real.log p.1).trace -
        RCLike.re (p.1 * cfc Real.log p.2).trace) := by
  refine ⟨fun x hx y hy a b ha hb hab =>
    ⟨Matrix.convex_setOfPred_posDef hx.1 hy.1 ha hb hab,
    Matrix.convex_setOfPred_posDef hx.2 hy.2 ha hb hab⟩, ?_⟩
  rintro ⟨X₁, Y₁⟩ ⟨hX₁, hY₁⟩ ⟨X₂, Y₂⟩ ⟨hX₂, hY₂⟩ a b ha hb hab
  have hX : (a • X₁ + b • X₂).PosDef := Matrix.convex_setOfPred_posDef hX₁ hX₂ ha hb hab
  have hY : (a • Y₁ + b • Y₂).PosDef := Matrix.convex_setOfPred_posDef hY₁ hY₂ ha hb hab
  have h₁ := (integrableOn_integrand hX₁ hY₁).const_mul a
  have h₂ := (integrableOn_integrand hX₂ hY₂).const_mul b
  simp only [Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul]
  rw [← integral_integrand hX hY, ← integral_integrand hX₁ hY₁, ← integral_integrand hX₂ hY₂,
    ← integral_const_mul, ← integral_const_mul, ← integral_add h₁ h₂]
  refine setIntegral_mono_on (integrableOn_integrand hX hY) (h₁.add h₂) measurableSet_Ioi
    fun s hs => ?_
  obtain ⟨W, hW⟩ := exists_testFunctional_eq hX hY hs
  rw [← hW, testFunctional_add_smul]
  exact add_le_add (mul_le_mul_of_nonneg_left (testFunctional_le hX₁ hY₁ hs W) ha)
    (mul_le_mul_of_nonneg_left (testFunctional_le hX₂ hY₂ hs W) hb)

end JointConvexity

end MathlibExt.LinearAlgebra.Matrix.RelativeEntropy

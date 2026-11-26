/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import MathlibExt.Analysis.Fourier.CircleFejer
public import MathlibExt.Analysis.Fourier.AddCircle.CesaroMean
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
public import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm

/-!
# Fejér polynomials and their uniform norm bound

Let 𝕋=UnitAddCircle=ℝ/ℤ, with normalized Haar probability measure μ=AddCircle.haarAddCircle.
Write e_k(x)=fourier k x and f̂(k)=∫ x:𝕋, f(x)e_(-k)(x) ∂μ for k∈ℤ. For f∈L∞(𝕋,μ) and N∈ℕ, let
F_N(f)=circleFejerPolynomial f N be the continuous Fejér polynomial (N+1)⁻¹∑_{0≤i,j≤N}
f̂(i-j)e_(i-j). The normalized Fejér kernel is K_N(x)=circleFejerKernel N x=(N+1)⁻¹|∑_{j=0}^N
e_j(x)|², viewed in ℂ. The polynomial satisfies F_N(f)(x)=∫ t, f(t)K_N(x-t) ∂μ. Since K_N is
nonnegative with unit mass, ‖F_N(f)‖∞≤‖f‖L∞.
-/

@[expose] public section
noncomputable section
open Filter MeasureTheory Set Topology
open scoped BigOperators ENNReal InnerProductSpace
namespace MathlibExt.Analysis.Fourier

/-- **Continuous Fejér polynomial of an L∞ function.**

Let 𝕋=UnitAddCircle=ℝ/ℤ, with normalized Haar probability measure μ=AddCircle.haarAddCircle.
Write e_k(x)=fourier k x and f̂(k)=∫ x:𝕋, f(x)e_(-k)(x) ∂μ for k∈ℤ. For f∈L∞(𝕋,μ) and N∈ℕ, let
F_N(f)=circleFejerPolynomial f N be the continuous Fejér polynomial (N+1)⁻¹∑_{0≤i,j≤N}
f̂(i-j)e_(i-j). This defines circleFejerPolynomial f N∈C(𝕋,ℂ) for every L∞ class f and N∈ℕ.
-/
def circleFejerPolynomial (f : Lp ℂ ∞ (AddCircle.haarAddCircle : Measure UnitAddCircle))
    (N : ℕ) : C(UnitAddCircle, ℂ) :=
  (N + 1 : ℂ)⁻¹ • ∑ i ∈ Finset.range (N + 1), ∑ j ∈ Finset.range (N + 1),
    fourierCoeff (f : UnitAddCircle → ℂ) ((i : ℤ) - j) • fourier ((i : ℤ) - j)

/-- **Circle Fourier character on a difference.**

Let 𝕋=UnitAddCircle=ℝ/ℤ, with normalized Haar probability measure μ=AddCircle.haarAddCircle.
Write e_k(x)=fourier k x and f̂(k)=∫ x:𝕋, f(x)e_(-k)(x) ∂μ for k∈ℤ. For n∈ℤ and x,t∈𝕋,
e_n(x-t)=e_n(x)e_(-n)(t).
-/
theorem circleFourier_apply_sub (n : ℤ) (x t : UnitAddCircle) :
    fourier n (x - t) = fourier n x * fourier (-n) t := by
  exact (AddCircle.fourier_sub_eq (T := (1 : ℝ)) n x t).trans (mul_comm _ _)

/-- **Finite Fourier expansion of the Fejér kernel.**

Let 𝕋=UnitAddCircle=ℝ/ℤ, with normalized Haar probability measure μ=AddCircle.haarAddCircle.
Write e_k(x)=fourier k x and f̂(k)=∫ x:𝕋, f(x)e_(-k)(x) ∂μ for k∈ℤ. The normalized Fejér
kernel is K_N(x)=circleFejerKernel N x=(N+1)⁻¹|∑_{j=0}^N e_j(x)|², viewed in ℂ. For N∈ℕ and
x∈𝕋, K_N(x)=(N+1)⁻¹∑_{0≤i,j≤N} e_(i-j)(x).
-/
theorem circleFejerKernel_fourier (N : ℕ) (x : UnitAddCircle) :
    circleFejerKernel N x = (N + 1 : ℂ)⁻¹ *
      ∑ i ∈ Finset.range (N + 1), ∑ j ∈ Finset.range (N + 1), fourier ((i : ℤ) - j) x := by
  have hstar :
      Star.star (circleDirichletPolynomial N x) * circleDirichletPolynomial N x =
        ((‖circleDirichletPolynomial N x‖ ^ 2 : ℝ) : ℂ) := by
    simpa only [RCLike.star_def, Complex.ofReal_pow] using
      Complex.conj_mul' (circleDirichletPolynomial N x)
  rw [circleFejerKernel_apply, Complex.ofReal_div, ← hstar]
  simp only [Complex.ofReal_add, Complex.ofReal_natCast, Complex.ofReal_one,
    div_eq_mul_inv]
  rw [mul_comm]
  change (N + 1 : ℂ)⁻¹ *
    (Star.star (circleDirichletPolynomial N x) * circleDirichletPolynomial N x) = _
  rw [circleDirichletPolynomial_apply]
  have hs : Star.star (∑ j ∈ Finset.range (N + 1), fourier (j : ℤ) x) =
      ∑ j ∈ Finset.range (N + 1), Star.star (fourier (j : ℤ) x) := by
    simpa only [starRingEnd_apply] using
      map_sum (starRingEnd ℂ) (fun j : ℕ => fourier (j : ℤ) x) (Finset.range (N + 1))
  rw [hs, Finset.sum_mul]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  congr 1
  funext i
  apply Finset.sum_congr rfl
  intro j hj
  apply congrArg (fun z : ℂ => (N + 1 : ℂ)⁻¹ * z)
  have hjstar : Star.star (fourier (j : ℤ) x) = fourier (-(j : ℤ)) x := by
    simpa only [RCLike.star_def] using (fourier_neg (n := (j : ℤ)) (x := x)).symm
  rw [hjstar, mul_comm, ← fourier_add, sub_eq_add_neg]

/-- **Integral of a translated Fourier character.**

Let 𝕋=UnitAddCircle=ℝ/ℤ, with normalized Haar probability measure μ=AddCircle.haarAddCircle.
Write e_k(x)=fourier k x and f̂(k)=∫ x:𝕋, f(x)e_(-k)(x) ∂μ for k∈ℤ. For f∈L∞(𝕋,μ), n∈ℤ and
x∈𝕋, ∫ t, f(t)e_n(x-t) ∂μ=f̂(n)e_n(x).
-/
theorem circleFourier_integral_translate
    (f : Lp ℂ ∞ (AddCircle.haarAddCircle : Measure UnitAddCircle)) (n : ℤ) (x : UnitAddCircle) :
    (∫ t, f t * fourier n (x - t) ∂AddCircle.haarAddCircle) =
      fourierCoeff (f : UnitAddCircle → ℂ) n * fourier n x := by
  have he : (fun t : UnitAddCircle => f t * fourier n (x - t)) =
      fun t => (fourier n x) * (fourier (-n) t • f t) := by
    funext t
    rw [circleFourier_apply_sub, smul_eq_mul]
    ring
  rw [he, integral_const_mul]
  change fourier n x * fourierCoeff (f : UnitAddCircle → ℂ) n = _
  exact mul_comm _ _

/-- **Integrability of a translated Fourier term.**

Let 𝕋=UnitAddCircle=ℝ/ℤ, with normalized Haar probability measure μ=AddCircle.haarAddCircle.
Write e_k(x)=fourier k x and f̂(k)=∫ x:𝕋, f(x)e_(-k)(x) ∂μ for k∈ℤ. For f∈L∞(𝕋,μ), n∈ℤ and
x∈𝕋, the function t↦f(t)e_n(x-t) is μ-integrable.
-/
theorem circleFourier_translate_integrable
    (f : Lp ℂ ∞ (AddCircle.haarAddCircle : Measure UnitAddCircle)) (n : ℤ) (x : UnitAddCircle) :
    Integrable (fun t => f t * fourier n (x - t)) AddCircle.haarAddCircle := by
  have hf : Integrable (f : UnitAddCircle → ℂ) AddCircle.haarAddCircle :=
    memLp_one_iff_integrable.mp ((Lp.memLp f).mono_exponent (by simp : (1 : ℝ≥0∞) ≤ ∞))
  have h := (hf.fourier_smul (-n)).const_mul (fourier n x)
  apply h.congr
  exact Filter.Eventually.of_forall (fun t => by
    change fourier n x * (fourier (-n) t • f t) = f t * fourier n (x - t)
    rw [circleFourier_apply_sub, smul_eq_mul]
    ring)

/-- **Fejér polynomial as convolution with the Fejér kernel.**

Let 𝕋=UnitAddCircle=ℝ/ℤ, with normalized Haar probability measure μ=AddCircle.haarAddCircle.
Write e_k(x)=fourier k x and f̂(k)=∫ x:𝕋, f(x)e_(-k)(x) ∂μ for k∈ℤ. For f∈L∞(𝕋,μ) and N∈ℕ, let
F_N(f)=circleFejerPolynomial f N be the continuous Fejér polynomial (N+1)⁻¹∑_{0≤i,j≤N}
f̂(i-j)e_(i-j). The normalized Fejér kernel is K_N(x)=circleFejerKernel N x=(N+1)⁻¹|∑_{j=0}^N
e_j(x)|², viewed in ℂ. For x∈𝕋, circleFejerPolynomial f N x=∫ t, f(t)K_N(x-t) ∂μ.
-/
theorem circleFejerPolynomial_eq_integral
    (f : Lp ℂ ∞ (AddCircle.haarAddCircle : Measure UnitAddCircle)) (N : ℕ) (x : UnitAddCircle) :
    circleFejerPolynomial f N x =
      ∫ t, f t * circleFejerKernel N (x - t) ∂AddCircle.haarAddCircle := by
  have he : (fun t : UnitAddCircle => f t * circleFejerKernel N (x - t)) =
      (fun t : UnitAddCircle => (N + 1 : ℂ)⁻¹ •
        (∑ i ∈ Finset.range (N + 1), ∑ j ∈ Finset.range (N + 1),
          f t * fourier ((i : ℤ) - j) (x - t))) := by
    funext t
    rw [circleFejerKernel_fourier]
    simp only [smul_eq_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    ring
  rw [he, integral_smul]
  rw [integral_finsetSum (Finset.range (N + 1)) (fun (i : ℕ) hi =>
    integrable_finsetSum (Finset.range (N + 1))
      (fun (j : ℕ) hj => circleFourier_translate_integrable f ((i : ℤ) - (j : ℤ)) x))]
  have hInner (i : ℕ) :
      (∫ t : UnitAddCircle, ∑ j ∈ Finset.range (N + 1),
        f t * fourier ((i : ℤ) - (j : ℤ)) (x - t) ∂AddCircle.haarAddCircle) =
        ∑ j ∈ Finset.range (N + 1),
          ∫ t : UnitAddCircle, f t * fourier ((i : ℤ) - (j : ℤ)) (x - t)
            ∂AddCircle.haarAddCircle := by
    exact integral_finsetSum (Finset.range (N + 1))
      (fun (j : ℕ) hj => circleFourier_translate_integrable f ((i : ℤ) - (j : ℤ)) x)
  simp_rw [hInner, circleFourier_integral_translate]
  simp only [circleFejerPolynomial, ContinuousMap.smul_apply, ContinuousMap.sum_apply,
    smul_eq_mul]

/-- **Translated Fejér kernel has unit mass.**

Let 𝕋=UnitAddCircle=ℝ/ℤ, with normalized Haar probability measure μ=AddCircle.haarAddCircle.
Write e_k(x)=fourier k x and f̂(k)=∫ x:𝕋, f(x)e_(-k)(x) ∂μ for k∈ℤ. The normalized Fejér
kernel is K_N(x)=circleFejerKernel N x=(N+1)⁻¹|∑_{j=0}^N e_j(x)|², viewed in ℂ. For N∈ℕ and
x∈𝕋, ∫ t, Re(K_N(x-t)) ∂μ=1.
-/
theorem circleFejerKernel_integral_re_sub (N : ℕ) (x : UnitAddCircle) :
    (∫ t, (circleFejerKernel N (x - t)).re
      ∂(AddCircle.haarAddCircle : Measure UnitAddCircle)) = 1 := by
  have hI : Integrable (fun t => circleFejerKernel N (x - t))
      (AddCircle.haarAddCircle : Measure UnitAddCircle) :=
    memLp_one_iff_integrable.mp (ContinuousMap.memLp (p := (1 : ℝ≥0∞))
      (μ := (AddCircle.haarAddCircle : Measure UnitAddCircle)) ℂ
      (⟨fun t => circleFejerKernel N (x - t),
        (circleFejerKernel N).continuous.comp
          (continuous_const.sub continuous_id)⟩ : C(UnitAddCircle, ℂ)))
  have hRe := (Complex.reCLM : ℂ →L[ℝ] ℝ).integral_comp_comm hI
  simp only [Complex.reCLM_apply] at hRe
  rw [hRe, circleFejerKernel_integral_sub]
  rfl

/-- **Uniform norm bound for a Fejér polynomial.**

Let 𝕋=UnitAddCircle=ℝ/ℤ, with normalized Haar probability measure μ=AddCircle.haarAddCircle.
Write e_k(x)=fourier k x and f̂(k)=∫ x:𝕋, f(x)e_(-k)(x) ∂μ for k∈ℤ. For f∈L∞(𝕋,μ) and N∈ℕ, let
F_N(f)=circleFejerPolynomial f N be the continuous Fejér polynomial (N+1)⁻¹∑_{0≤i,j≤N}
f̂(i-j)e_(i-j). For f∈L∞(𝕋,μ) and N∈ℕ, ‖circleFejerPolynomial f N‖∞≤‖f‖L∞; the polynomial norm
is its continuous supremum norm and the input norm is the essential supremum.
-/
theorem circleFejerPolynomial_norm_le
    (f : Lp ℂ ∞ (AddCircle.haarAddCircle : Measure UnitAddCircle)) (N : ℕ) :
    ‖circleFejerPolynomial f N‖ ≤ ‖f‖ := by
  apply (ContinuousMap.norm_le (f := circleFejerPolynomial f N) (norm_nonneg f)).mpr
  intro x
  rw [circleFejerPolynomial_eq_integral]
  have hI : Integrable (fun t => ‖f‖ * (circleFejerKernel N (x - t)).re)
      (AddCircle.haarAddCircle : Measure UnitAddCircle) :=
    (memLp_one_iff_integrable.mp (ContinuousMap.memLp (p := (1 : ℝ≥0∞))
      (μ := (AddCircle.haarAddCircle : Measure UnitAddCircle)) ℝ
      (⟨fun t => (circleFejerKernel N (x - t)).re,
        Complex.continuous_re.comp
          ((circleFejerKernel N).continuous.comp
            (continuous_const.sub continuous_id))⟩ : C(UnitAddCircle,
    ℝ)))).const_mul _
  have hbound : ∀ᵐ t ∂AddCircle.haarAddCircle,
      ‖f t * circleFejerKernel N (x - t)‖ ≤ ‖f‖ * (circleFejerKernel N (x - t)).re := by
    filter_upwards [MeasureTheory.ae_le_lpNorm_exponent_top (Lp.memLp f)] with t ht
    have htf : ‖f t‖ ≤ ‖f‖ := by
      simpa only [← toReal_eLpNorm, Lp.norm_def] using ht
    rw [norm_mul, circleFejerKernel_norm]
    exact mul_le_mul_of_nonneg_right htf (circleFejerKernel_re_nonneg _ _)
  have he := norm_integral_le_of_norm_le hI hbound
  rw [integral_const_mul, circleFejerKernel_integral_re_sub, mul_one] at he
  exact he

end MathlibExt.Analysis.Fourier

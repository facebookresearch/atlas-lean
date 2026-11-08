/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.InnerProductSpace.l2Space
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Measure.Haar.Unique

@[expose] public section

namespace MathlibExt.Analysis.ODE.GreensOperator

open MeasureTheory

/-!
# The Green's operator for the Dirichlet Laplacian on `[0, 1]`

The Green's kernel for `-d²/dx²` with Dirichlet boundary conditions on
`[0, 1]` is `G(x, t) = min(x, t) * (1 - max(x, t))`, so the Green's operator
is `Af(x) = ∫₀¹ G(x, t) f(t) dt`. Its eigenfunctions are the sine functions
`u_k(x) = √2 sin(kπx)` with eigenvalues `λ_k = 1 / (k²π²)`, and every
`f ∈ L²([0, 1])` has the expansion `Af = ∑' k, λ_k ⟨b_k, f⟩ b_k` in the
sine basis. The key computation is the kernel integral
`∫₀¹ G(x, t) u_k(t) dt = λ_k u_k(x)`, proved by splitting the integral at `t = x`
and integrating `t ↦ t sin(at)` and `t ↦ (1 - t) sin(at)` by parts.

Source: `v1/Atlas/IntroductionToFunctionalAnalysis/code/SpectralTheory.lean`,
`SpectralTheory` (GreensSqrt section): `greensKernel`, `sineBasisFun`,
`greensEigenvalue`, `greensEigenvalueSqrt`, `greensOperatorSqrt`,
`greens_kernel_integral_sine_eq`, and `greens_operator_eigendecomposition`
(Theorem, May 13, 2021 section). The Sturm–Liouville existence theorem that
uses this operator in v1 is not proved in v1 and is not ported here.
-/

/-- The Hilbert space `L²([0, 1])` of square-integrable real-valued functions
on the unit interval, equipped with the restriction of Lebesgue measure to
`[0, 1]`. -/
noncomputable abbrev L2UnitInterval :=
  Lp ℝ 2 (volume.restrict (Set.Icc (0 : ℝ) 1))

/-- The `k`-th orthonormal sine basis function on `[0, 1]`:
`u_k(x) = √2 sin(kπx)`.
These form an orthonormal eigenbasis of the Green's operator with Dirichlet
boundary conditions on the unit interval. -/
noncomputable def sineBasisFun (k : ℕ+) : ℝ → ℝ :=
  fun x => Real.sqrt 2 * Real.sin (↑k * Real.pi * x)

/-- The `k`-th eigenvalue of the Green's operator on `[0, 1]` with Dirichlet
boundary conditions: `λ_k = 1 / (k²π²)`. -/
noncomputable def greensEigenvalue (k : ℕ+) : ℝ := 1 / ((k : ℝ) ^ 2 * Real.pi ^ 2)

/-- The square root of the `k`-th eigenvalue of the Green's operator,
`√λ_k = 1 / (kπ)`. This is the `k`-th eigenvalue of `A^{1/2}`. -/
noncomputable def greensEigenvalueSqrt (k : ℕ+) : ℝ := 1 / ((k : ℝ) * Real.pi)

/-- The square root `A^{1/2}` of the Green's operator, defined via its action
on the indexed sine eigenbasis `{b_k}`. Require `b_k = u_k` almost everywhere,
as in `greens_operator_eigendecomposition`. If `f = ∑' k, c_k b_k` where
`c_k = ⟨b_k, f⟩`, then `A^{1/2} f = ∑' k, (1 / (kπ)) c_k b_k`. -/
noncomputable def greensOperatorSqrt (b : HilbertBasis ℕ+ ℝ L2UnitInterval)
    (_hb : ∀ k : ℕ+, (b k : L2UnitInterval) =ᵐ[volume.restrict (Set.Icc (0 : ℝ) 1)]
      (sineBasisFun k : ℝ → ℝ)) :
    L2UnitInterval → L2UnitInterval :=
  fun f => ∑' (k : ℕ+), (greensEigenvalueSqrt k * inner (𝕜 := ℝ) (b k) f) • b k

/-- The Green's kernel for the Dirichlet Laplacian on `[0, 1]`:
`G(x, t) = min(x, t) * (1 - max(x, t))`.
The Green's operator `f ↦ ∫₀¹ G(x, t) f(t) dt` is the inverse of
`-d²/dx²` subject to `u(0) = u(1) = 0`. -/
noncomputable def greensKernel (x t : ℝ) : ℝ :=
  min x t * (1 - max x t)

/-- Key computation showing that the sine basis functions are eigenfunctions
of the Green's operator: for `x ∈ [0, 1]`,
`∫₀¹ G(x, t) u_k(t) dt = λ_k u_k(x)`,
where `G` is the Green's kernel, `u_k(x) = √2 sin(kπx)` and
`λ_k = 1 / (k²π²)`. -/
lemma greens_kernel_integral_sine_eq (k : ℕ+) (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    ∫ t in (0 : ℝ)..1, (greensKernel x t) * (sineBasisFun k t) =
      greensEigenvalue k * sineBasisFun k x := by
  simp only [greensKernel, sineBasisFun, greensEigenvalue]
  set a := (↑k : ℝ) * Real.pi with ha_def
  have ha : a ≠ 0 := mul_ne_zero (Nat.cast_pos.mpr k.pos).ne' Real.pi_ne_zero
  have hcont : Continuous (fun t => min x t * (1 - max x t) * (Real.sqrt 2 * Real.sin (a * t))) :=
    ((continuous_const.min continuous_id).mul
      (continuous_const.sub (continuous_const.max continuous_id))).mul
      (continuous_const.mul (Real.continuous_sin.comp (continuous_const.mul continuous_id)))
  rw [show (↑k : ℝ) * Real.pi * x = a * x from by rw [ha_def]]
  rw [show (fun t => min x t * (1 - max x t) * (Real.sqrt 2 * Real.sin ((↑k : ℝ) * Real.pi * t))) =
      (fun t => min x t * (1 - max x t) * (Real.sqrt 2 * Real.sin (a * t))) from by
    ext t; rw [ha_def]]
  rw [(intervalIntegral.integral_add_adjacent_intervals
    (hcont.intervalIntegrable 0 x) (hcont.intervalIntegrable x 1)).symm]
  have hleft_congr : Set.EqOn (fun t => min x t * (1 - max x t) * (Real.sqrt 2 * Real.sin (a * t)))
      (fun t => (1 - x) * Real.sqrt 2 * (t * Real.sin (a * t))) (Set.uIcc 0 x) := by
    intro t ht; simp only [Set.uIcc_of_le hx0] at ht
    simp [min_eq_right ht.2, max_eq_left ht.2]; ring
  have hright_congr : Set.EqOn (fun t => min x t * (1 - max x t) * (Real.sqrt 2 * Real.sin (a * t)))
      (fun t => x * Real.sqrt 2 * ((1 - t) * Real.sin (a * t))) (Set.uIcc x 1) := by
    intro t ht; simp only [Set.uIcc_of_le hx1] at ht
    simp [min_eq_left ht.1, max_eq_right ht.1]; ring
  rw [intervalIntegral.integral_congr hleft_congr, intervalIntegral.integral_congr hright_congr]
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  have hI1 : ∫ t in (0 : ℝ)..x, t * Real.sin (a * t) =
      Real.sin (a * x) / a ^ 2 - x * Real.cos (a * x) / a := by
    have hasD : ∀ t ∈ Set.uIcc 0 x, HasDerivAt
        (fun t => Real.sin (a * t) / a ^ 2 - t * Real.cos (a * t) / a)
        (t * Real.sin (a * t)) t := by
      intro t _
      have hd : HasDerivAt (fun t => a * t) a t := by
        have := (hasDerivAt_id t).const_mul a; simp only [mul_one] at this; exact this
      have hh1 : HasDerivAt (fun t => Real.sin (a * t) / a ^ 2) (Real.cos (a * t) / a) t := by
        convert hd.sin.div_const (a ^ 2) using 1; field_simp
      have hh2 : HasDerivAt (fun t => t * Real.cos (a * t) / a)
          (Real.cos (a * t) / a - t * Real.sin (a * t)) t := by
        have h2s : HasDerivAt (fun t => t * Real.cos (a * t) / a)
            ((Real.cos (a * t) + -(t * (Real.sin (a * t) * a))) / a) t := by
          simpa [id_eq, Pi.mul_apply] using ((hasDerivAt_id t).mul hd.cos).div_const a
        convert h2s using 1
        field_simp; ring
      convert hh1.sub hh2 using 1; ring
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hasD
      ((continuous_id.mul (Real.continuous_sin.comp
        (continuous_const.mul continuous_id))).intervalIntegrable 0 x)]
    simp [Real.sin_zero, Real.cos_zero]
  have hI2 : ∫ t in x..(1 : ℝ), (1 - t) * Real.sin (a * t) =
      -Real.sin a / a ^ 2 + Real.cos (a * x) / a +
        Real.sin (a * x) / a ^ 2 - x * Real.cos (a * x) / a := by
    have hasD : ∀ t ∈ Set.uIcc x 1, HasDerivAt
        (fun t => -Real.cos (a * t) / a - Real.sin (a * t) / a ^ 2 + t * Real.cos (a * t) / a)
        ((1 - t) * Real.sin (a * t)) t := by
      intro t _
      have hd : HasDerivAt (fun t => a * t) a t := by
        have := (hasDerivAt_id t).const_mul a; simp only [mul_one] at this; exact this
      have h1 : HasDerivAt (fun t => -Real.cos (a * t) / a) (Real.sin (a * t)) t := by
        convert (hd.cos.neg).div_const a using 1; field_simp
      have h2 : HasDerivAt (fun t => Real.sin (a * t) / a ^ 2) (Real.cos (a * t) / a) t := by
        convert hd.sin.div_const (a ^ 2) using 1; field_simp
      have h3 : HasDerivAt (fun t => t * Real.cos (a * t) / a)
          (Real.cos (a * t) / a - t * Real.sin (a * t)) t := by
        have h3s : HasDerivAt (fun t => t * Real.cos (a * t) / a)
            ((Real.cos (a * t) + -(t * (Real.sin (a * t) * a))) / a) t := by
          simpa [id_eq, Pi.mul_apply] using ((hasDerivAt_id t).mul hd.cos).div_const a
        convert h3s using 1
        field_simp; ring
      convert (h1.sub h2).add h3 using 1; ring
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hasD
      (((continuous_const.sub continuous_id).mul (Real.continuous_sin.comp
        (continuous_const.mul continuous_id))).intervalIntegrable x 1)]
    ring_nf
  rw [hI1, hI2]
  have hsin_a : Real.sin a = 0 := by
    rw [ha_def]; exact_mod_cast Real.sin_nat_mul_pi ↑k
  rw [hsin_a, neg_zero, zero_div, zero_add]
  field_simp
  ring

/-- Spectral decomposition of the Green's operator on `L²([0, 1])`.
If `A` is a symmetric operator on `L²([0, 1])` given by the Green's kernel
`Af(x) = ∫₀¹ G(x, t) f(t) dt`, and `{b_k}` is a Hilbert basis of sine
functions `b_k(x) = √2 sin(kπx)` (in the a.e. sense), then:
* ` ker A = ⊥`;
* each `b_k` is an eigenvector with eigenvalue `λ_k = 1 / (k²π²)`;
* every `f ∈ L²([0, 1])` satisfies
  `Af = ∑' k, λ_k ⟨b_k, f⟩ b_k`. -/
theorem greens_operator_eigendecomposition
    (A : Module.End ℝ L2UnitInterval)
    (b : HilbertBasis ℕ+ ℝ L2UnitInterval)
    (hA_sa : ∀ f g : L2UnitInterval,
      inner (𝕜 := ℝ) (A f) g = inner (𝕜 := ℝ) f (A g))
    (hb : ∀ k : ℕ+, (b k : L2UnitInterval) =ᵐ[volume.restrict (Set.Icc (0 : ℝ) 1)]
      (sineBasisFun k : ℝ → ℝ))
    (hA_greens : ∀ f : L2UnitInterval,
      (A f : L2UnitInterval) =ᵐ[volume.restrict (Set.Icc (0 : ℝ) 1)]
      (fun x => ∫ t in Set.Icc (0 : ℝ) 1, greensKernel x t * (f : ℝ → ℝ) t)) :
    LinearMap.ker A = ⊥ ∧
    (∀ k : ℕ+, A.HasEigenvector (greensEigenvalue k) (b k)) ∧
    ∀ f : L2UnitInterval,
      A f = ∑' k : ℕ+, (greensEigenvalue k * @inner ℝ _ _ (b k) f) • (b k) := by
  have heig : ∀ k : ℕ+, A (b k) = greensEigenvalue k • (b k) := by
    intro k
    apply Lp.ext
    set μ := volume.restrict (Set.Icc (0 : ℝ) 1)
    have hIntEq : ∀ x : ℝ, 0 ≤ x → x ≤ 1 →
        ∫ t in Set.Icc (0 : ℝ) 1, greensKernel x t * sineBasisFun k t =
        greensEigenvalue k * sineBasisFun k x := by
      intro x hx0 hx1
      have hconv : ∫ t in Set.Icc (0 : ℝ) 1, greensKernel x t * sineBasisFun k t =
          ∫ t in (0 : ℝ)..1, greensKernel x t * sineBasisFun k t := by
        rw [intervalIntegral.integral_of_le (by linarith : (0 : ℝ) ≤ 1)]
        exact (setIntegral_congr_set Ioc_ae_eq_Icc).symm
      rw [hconv]
      exact greens_kernel_integral_sine_eq k x hx0 hx1
    have hAeq := hA_greens (b k)
    have hb_ae := hb k
    have hintegral_eq : ∀ᵐ x ∂μ,
        (fun x => ∫ t in Set.Icc (0 : ℝ) 1, greensKernel x t * (↑↑(b k) : ℝ → ℝ) t) x =
        (fun x => ∫ t in Set.Icc (0 : ℝ) 1, greensKernel x t * sineBasisFun k t) x := by
      have hae_vol : ∀ᵐ t ∂volume, t ∈ Set.Icc (0 : ℝ) 1 →
          (↑↑(b k) : ℝ → ℝ) t = sineBasisFun k t := by
        rw [← ae_restrict_iff' measurableSet_Icc]; exact hb_ae
      exact Filter.Eventually.of_forall fun x =>
        setIntegral_congr_ae measurableSet_Icc
          (hae_vol.mono fun t ht hmem => by rw [ht hmem])
    have heigval_eq : ∀ᵐ x ∂μ,
        (fun x => ∫ t in Set.Icc (0 : ℝ) 1, greensKernel x t * sineBasisFun k t) x =
        (fun x => greensEigenvalue k * sineBasisFun k x) x := by
      rw [ae_restrict_iff' measurableSet_Icc]
      exact Filter.Eventually.of_forall fun x hx => hIntEq x hx.1 hx.2
    have hsmul_eq : ∀ᵐ x ∂μ,
        (fun x => greensEigenvalue k * sineBasisFun k x) x =
        (fun x => greensEigenvalue k * (↑↑(b k) : ℝ → ℝ) x) x := by
      exact hb_ae.symm.mono fun x hx => by simp [hx]
    have hsmul_coeFn : (↑↑(greensEigenvalue k • b k) : ℝ → ℝ) =ᶠ[ae μ]
        fun x => greensEigenvalue k * (↑↑(b k) : ℝ → ℝ) x := by
      exact (Lp.coeFn_smul (greensEigenvalue k) (b k)).mono fun x hx => by
        simp [Pi.smul_apply, smul_eq_mul] at hx; exact hx
    calc (↑↑(A (b k)) : ℝ → ℝ)
        =ᶠ[ae μ] fun x => ∫ t in Set.Icc (0 : ℝ) 1, greensKernel x t * (↑↑(b k) : ℝ → ℝ) t := hAeq
      _ =ᶠ[ae μ] fun x => ∫ t in Set.Icc (0 : ℝ) 1, greensKernel x t * sineBasisFun k t := hintegral_eq
      _ =ᶠ[ae μ] fun x => greensEigenvalue k * sineBasisFun k x := heigval_eq
      _ =ᶠ[ae μ] fun x => greensEigenvalue k * (↑↑(b k) : ℝ → ℝ) x := hsmul_eq
      _ =ᶠ[ae μ] ↑↑(greensEigenvalue k • b k) := hsmul_coeFn.symm
  refine ⟨?_, ?_, ?_⟩
  · rw [LinearMap.ker_eq_bot']
    intro f hf
    have hcoeff : ∀ k : ℕ+, @inner ℝ _ _ (b k) f = (0 : ℝ) := by
      intro k
      have hne : greensEigenvalue k ≠ 0 := by
        unfold greensEigenvalue; apply div_ne_zero one_ne_zero
        apply mul_ne_zero; positivity; positivity
      have h1 : @inner ℝ _ _ (A f) (b k) = @inner ℝ _ _ f (A (b k)) := hA_sa f (b k)
      rw [hf, heig k] at h1
      simp only [inner_zero_left, inner_smul_right] at h1
      have h2 : @inner ℝ _ _ f (b k) = 0 := by
        rcases mul_eq_zero.mp h1.symm with h | h
        · exact absurd h hne
        · exact h
      rw [real_inner_comm] at h2; exact h2
    have hinj := b.repr.injective
    apply hinj; ext k
    simp only [HilbertBasis.repr_apply_apply, hcoeff k, map_zero]; rfl
  · intro k
    rw [Module.End.hasEigenvector_iff]
    exact ⟨Module.End.mem_eigenspace_iff.mpr (heig k), b.orthonormal.ne_zero k⟩
  · intro f
    have hcoeff : ∀ j : ℕ+,
        @inner ℝ _ _ (b j) (A f) = greensEigenvalue j * @inner ℝ _ _ (b j) f := by
      intro j
      have h1 : @inner ℝ _ _ (b j) (A f) = @inner ℝ _ _ (A f) (b j) := real_inner_comm _ _
      rw [h1, hA_sa f (b j), heig j, real_inner_smul_right, real_inner_comm]
    have hexpand : HasSum (fun j => @inner ℝ _ _ (b j) (A f) • b j) (A f) := by
      have h := b.hasSum_repr (A f)
      simp_rw [HilbertBasis.repr_apply_apply] at h
      exact h
    rw [hexpand.tsum_eq.symm]
    congr 1
    ext j
    rw [hcoeff j]

private lemma sine_memLp (k : ℕ+) :
    MemLp (sineBasisFun k) 2 (volume.restrict (Set.Icc (0 : ℝ) 1)) := by
  have hc : Continuous (sineBasisFun k) := by
    unfold sineBasisFun
    fun_prop
  refine MemLp.of_bound hc.aestronglyMeasurable (Real.sqrt 2) ?_
  filter_upwards with x
  change |Real.sqrt 2 * Real.sin ((k : ℝ) * Real.pi * x)| ≤ Real.sqrt 2
  rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg 2)]
  simpa only [mul_one] using mul_le_mul_of_nonneg_left
    (Real.abs_sin_le_one ((k : ℝ) * Real.pi * x)) (Real.sqrt_nonneg 2)

private noncomputable def sineL2 (k : ℕ+) : L2UnitInterval :=
  MemLp.toLp (sineBasisFun k) (sine_memLp k)

private lemma sineL2_coe (k : ℕ+) :
    (sineL2 k : ℝ → ℝ) =ᵐ[volume.restrict (Set.Icc (0 : ℝ) 1)] sineBasisFun k := by
  exact (sine_memLp k).coeFn_toLp

private lemma sine_sq_integral (k : ℕ+) :
    (∫ x in (0 : ℝ)..1, (sineBasisFun k x) ^ 2) = 1 := by
  let a : ℝ := (k : ℝ) * Real.pi
  have ha : a ≠ 0 := by dsimp [a]; positivity
  have hs : Real.sin a = 0 := by
    dsimp [a]
    exact_mod_cast Real.sin_nat_mul_pi (k : ℕ)
  have hf : (fun x : ℝ => (sineBasisFun k x) ^ 2) =
      (fun x : ℝ => 2 * Real.sin (a * x) ^ 2) := by
    funext x
    simp only [sineBasisFun, mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    rfl
  rw [hf, intervalIntegral.integral_const_mul]
  rw [intervalIntegral.integral_comp_mul_left (fun x : ℝ => Real.sin x ^ 2) ha]
  simp only [mul_zero, mul_one, integral_sin_sq, Real.sin_zero, Real.cos_zero,
    hs, zero_mul, zero_add, sub_zero, smul_eq_mul]
  field_simp [ha]



private lemma cos_int_mul_pi_integral (n : ℤ) (hn : n ≠ 0) :
    (∫ x in (0 : ℝ)..1, Real.cos ((n : ℝ) * Real.pi * x)) = 0 := by
  have ha : (n : ℝ) * Real.pi ≠ 0 :=
    mul_ne_zero (by exact_mod_cast hn) Real.pi_ne_zero
  rw [intervalIntegral.integral_comp_mul_left Real.cos ha]
  simp only [mul_zero, mul_one, integral_cos, Real.sin_int_mul_pi,
    Real.sin_zero, sub_self, smul_zero]

private lemma sine_product_integral_of_ne (k j : ℕ+) (hkj : k ≠ j) :
    (∫ x in (0 : ℝ)..1, sineBasisFun k x * sineBasisFun j x) = 0 := by
  have hdiff : (k : ℤ) - (j : ℤ) ≠ 0 := by
    intro h
    apply hkj
    exact_mod_cast sub_eq_zero.mp h
  have hsum : (k : ℤ) + (j : ℤ) ≠ 0 := by positivity
  have hf : (fun x : ℝ => sineBasisFun k x * sineBasisFun j x) =
      (fun x : ℝ =>
        Real.cos ((((k : ℤ) - (j : ℤ) : ℤ) : ℝ) * Real.pi * x) -
        Real.cos ((((k : ℤ) + (j : ℤ) : ℤ) : ℝ) * Real.pi * x)) := by
    funext x
    calc
      sineBasisFun k x * sineBasisFun j x =
          (Real.sqrt 2) ^ 2 * Real.sin ((k : ℝ) * Real.pi * x) *
            Real.sin ((j : ℝ) * Real.pi * x) := by
              dsimp only [sineBasisFun]
              ring
      _ = 2 * Real.sin ((k : ℝ) * Real.pi * x) *
          Real.sin ((j : ℝ) * Real.pi * x) := by
            rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
      _ = Real.cos ((k : ℝ) * Real.pi * x - (j : ℝ) * Real.pi * x) -
          Real.cos ((k : ℝ) * Real.pi * x + (j : ℝ) * Real.pi * x) :=
            Real.two_mul_sin_mul_sin _ _
      _ = _ := by
        congr 2 <;> push_cast <;> ring
  have hc₁ : Continuous (fun x : ℝ =>
      Real.cos ((((k : ℤ) - (j : ℤ) : ℤ) : ℝ) * Real.pi * x)) := by fun_prop
  have hc₂ : Continuous (fun x : ℝ =>
      Real.cos ((((k : ℤ) + (j : ℤ) : ℤ) : ℝ) * Real.pi * x)) := by fun_prop
  rw [hf, intervalIntegral.integral_sub
    (hc₁.intervalIntegrable 0 1) (hc₂.intervalIntegrable 0 1),
    cos_int_mul_pi_integral _ hdiff, cos_int_mul_pi_integral _ hsum, sub_self]

/-- The canonical sine basis is orthonormal on the unit interval, in product-integral form. -/
lemma sine_product_integral (k j : ℕ+) :
    (∫ x in (0 : ℝ)..1, sineBasisFun k x * sineBasisFun j x) =
      if k = j then 1 else 0 := by
  classical
  by_cases hkj : k = j
  · subst j
    simpa [pow_two] using sine_sq_integral k
  · simpa [hkj] using sine_product_integral_of_ne k j hkj

private lemma sineL2_inner (k j : ℕ+) :
    inner (𝕜 := ℝ) (sineL2 k) (sineL2 j) = if k = j then 1 else 0 := by
  rw [L2.inner_def]
  calc
    (∫ x, inner (𝕜 := ℝ) (sineL2 k x) (sineL2 j x)
        ∂volume.restrict (Set.Icc (0 : ℝ) 1)) =
        ∫ x, sineBasisFun k x * sineBasisFun j x
          ∂volume.restrict (Set.Icc (0 : ℝ) 1) := by
            apply integral_congr_ae
            filter_upwards [sineL2_coe k, sineL2_coe j] with x hx hy
            simp only [hx, hy, RCLike.inner_apply]
            simp [mul_comm]
    _ = ∫ x in (0 : ℝ)..1, sineBasisFun k x * sineBasisFun j x := by
      rw [intervalIntegral.integral_of_le zero_le_one]
      exact (setIntegral_congr_set Ioc_ae_eq_Icc).symm
    _ = if k = j then 1 else 0 := sine_product_integral k j

private lemma orthonormal_sineL2 : Orthonormal ℝ sineL2 := by
  classical
  exact orthonormal_iff_ite.mpr sineL2_inner




private noncomputable def oddExtension (f : ℝ → ℝ) : ℝ → ℂ :=
  fun x => (((Set.Icc (0 : ℝ) 1).indicator f x : ℝ) : ℂ) -
    (((Set.Icc (0 : ℝ) 1).indicator f (-x) : ℝ) : ℂ)

private lemma oddExtension_memLp {p : ENNReal} {f : ℝ → ℝ}
    (hf : MemLp f p (volume.restrict (Set.Icc (0 : ℝ) 1))) :
    MemLp (oddExtension f) p volume := by
  have hi : MemLp ((Set.Icc (0 : ℝ) 1).indicator f) p volume :=
    (memLp_indicator_iff_restrict measurableSet_Icc.nullMeasurableSet).mpr hf
  have hc : MemLp (fun x : ℝ =>
      (((Set.Icc (0 : ℝ) 1).indicator f x : ℝ) : ℂ)) p volume := by
    simpa only [Complex.ofRealCLM_apply] using
      hi.continuousLinearMap_comp Complex.ofRealCLM
  exact hc.sub (hc.comp_measurePreserving volume.measurePreserving_neg)

private lemma oddExtension_neg (f : ℝ → ℝ) (x : ℝ) :
    oddExtension f (-x) = -oddExtension f x := by
  simp only [oddExtension, neg_neg]
  ring

private lemma oddExtension_pos (f : ℝ → ℝ) {x : ℝ}
    (hx : x ∈ Set.Ioo (0 : ℝ) 1) : oddExtension f x = (f x : ℂ) := by
  have hxp : x ∈ Set.Icc (0 : ℝ) 1 := Set.Ioo_subset_Icc_self hx
  have hxn : -x ∉ Set.Icc (0 : ℝ) 1 := by
    intro h
    linarith [hx.1, h.1]
  simp [oddExtension, hxp, hxn]

private lemma oddExtension_integrable {f : ℝ → ℝ}
    (hf : MemLp f 2 (volume.restrict (Set.Icc (0 : ℝ) 1))) :
    Integrable (oddExtension f) volume := by
  exact memLp_one_iff_integrable.mp
    (oddExtension_memLp (hf.mono_exponent (by norm_num : (1 : ENNReal) ≤ 2)))

private lemma fourier_two (n : ℤ) (x : ℝ) :
    @fourier (2 : ℝ) n (x : AddCircle (2 : ℝ)) =
      (Real.cos ((n : ℝ) * Real.pi * x) : ℂ) +
        (Real.sin ((n : ℝ) * Real.pi * x) : ℂ) * Complex.I := by
  rw [fourier_coe_apply]
  calc
    Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * (x : ℂ) / (2 : ℂ)) =
        Complex.exp ((((n : ℝ) * Real.pi * x : ℝ) : ℂ) * Complex.I) := by
          congr 1
          push_cast
          ring
    _ = _ := by
      rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]

private lemma fourier_reflect (n : ℤ) (x : ℝ) :
    @fourier (2 : ℝ) (-n) ((-x : ℝ) : AddCircle (2 : ℝ)) =
      @fourier (2 : ℝ) n (x : AddCircle (2 : ℝ)) := by
  rw [fourier_coe_apply, fourier_coe_apply]
  congr 1
  push_cast
  ring

private lemma oddExtension_fourierCoeff {f : ℝ → ℝ}
    (hf : MemLp f 2 (volume.restrict (Set.Icc (0 : ℝ) 1))) (n : ℤ) :
    fourierCoeffOn (by norm_num : (-1 : ℝ) < 1) (oddExtension f) n =
      -Complex.I *
        ((∫ x in (0 : ℝ)..1, Real.sin ((n : ℝ) * Real.pi * x) * f x : ℝ) : ℂ) := by
  let : NormedSpace ℝ ℂ := NormedSpace.complexToReal (E := ℂ)
  let F : ℤ → ℝ → ℂ := fun m x =>
    @fourier (2 : ℝ) m (x : AddCircle (2 : ℝ)) * oddExtension f x
  have hc (m : ℤ) : Continuous (fun x : ℝ =>
      @fourier (2 : ℝ) m (x : AddCircle (2 : ℝ))) := by fun_prop
  have hFi (m : ℤ) (a b : ℝ) : IntervalIntegrable (F m) volume a b :=
    (oddExtension_integrable hf).intervalIntegrable.continuousOn_mul (hc m).continuousOn
  have hFm (x : ℝ) : F (-n) (-x) = -(F n x) := by
    dsimp only [F]
    rw [fourier_reflect n x, oddExtension_neg, mul_neg]
  have hneg : (∫ x in (-1 : ℝ)..0, F (-n) x) =
      -(∫ x in (0 : ℝ)..1, F n x) := by
    calc
      (∫ x in (-1 : ℝ)..0, F (-n) x) =
          ∫ x in (0 : ℝ)..1, F (-n) (-x) := by
            symm
            simpa only [neg_zero] using
              (intervalIntegral.integral_comp_neg (F (-n)) (a := 0) (b := 1))
      _ = _ := by
        simp_rw [hFm]
        rw [intervalIntegral.integral_neg]
  have hwhole : (∫ x in (-1 : ℝ)..1, F (-n) x) =
      (-2 * Complex.I) *
        ((∫ x in (0 : ℝ)..1, Real.sin ((n : ℝ) * Real.pi * x) * f x : ℝ) : ℂ) := by
    calc
      (∫ x in (-1 : ℝ)..1, F (-n) x) =
          -(∫ x in (0 : ℝ)..1, F n x) + (∫ x in (0 : ℝ)..1, F (-n) x) := by
            rw [← intervalIntegral.integral_add_adjacent_intervals
              (hFi (-n) (-1) 0) (hFi (-n) 0 1), hneg]
      _ = ∫ x in (0 : ℝ)..1, F (-n) x - F n x := by
        rw [intervalIntegral.integral_sub (hFi (-n) 0 1) (hFi n 0 1)]
        ring
      _ = ∫ x in (0 : ℝ)..1,
          (-2 * Complex.I) * ((Real.sin ((n : ℝ) * Real.pi * x) * f x : ℝ) : ℂ) := by
        apply intervalIntegral.integral_congr_Ioo_of_le (by norm_num)
        intro x hx
        simp only [F, oddExtension_pos f hx, fourier_two, Int.cast_neg,
          neg_mul, Real.cos_neg, Real.sin_neg]
        push_cast
        ring
      _ = _ := by
        rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_ofReal]
  rw [fourierCoeffOn_eq_integral]
  simp only [smul_eq_mul, Complex.real_smul, fourier_coe_apply]
  norm_num only
  dsimp only [F] at hwhole
  simp only [fourier_coe_apply] at hwhole
  rw [hwhole]
  push_cast
  ring

private lemma sineL2_inner_function (k : ℕ+) (f : L2UnitInterval) :
    inner (𝕜 := ℝ) (sineL2 k) f = Real.sqrt 2 *
      ∫ x in (0 : ℝ)..1, Real.sin ((k : ℝ) * Real.pi * x) * f x := by
  rw [L2.inner_def]
  calc
    (∫ x, inner (𝕜 := ℝ) (sineL2 k x) (f x)
        ∂volume.restrict (Set.Icc (0 : ℝ) 1)) =
        ∫ x, Real.sqrt 2 * (Real.sin ((k : ℝ) * Real.pi * x) * f x)
          ∂volume.restrict (Set.Icc (0 : ℝ) 1) := by
      apply integral_congr_ae
      filter_upwards [sineL2_coe k] with x hx
      simp [hx, RCLike.inner_apply, sineBasisFun, mul_comm, mul_left_comm, mul_assoc]
    _ = Real.sqrt 2 *
        ∫ x, Real.sin ((k : ℝ) * Real.pi * x) * f x
          ∂volume.restrict (Set.Icc (0 : ℝ) 1) := integral_const_mul _ _
    _ = _ := by
      congr 1
      rw [intervalIntegral.integral_of_le zero_le_one]
      exact (setIntegral_congr_set Ioc_ae_eq_Icc).symm

private lemma sineIntegral_int_eq_zero (f : L2UnitInterval)
    (hf : ∀ k : ℕ+, inner (𝕜 := ℝ) (sineL2 k) f = 0) (n : ℤ) :
    (∫ x in (0 : ℝ)..1, Real.sin ((n : ℝ) * Real.pi * x) * f x) = 0 := by
  have hs (k : ℕ+) :
      (∫ x in (0 : ℝ)..1, Real.sin ((k : ℝ) * Real.pi * x) * f x) = 0 := by
    have h := hf k
    rw [sineL2_inner_function] at h
    exact (mul_eq_zero.mp h).resolve_left
      (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)).ne'
  cases n with
  | ofNat m =>
      cases m with
      | zero => simp
      | succ m => simpa using hs ⟨m + 1, Nat.succ_pos m⟩
  | negSucc m =>
      have h : (∫ x in (0 : ℝ)..1,
          Real.sin (((m + 1 : ℕ) : ℝ) * Real.pi * x) * f x) = 0 := by
        simpa using hs ⟨m + 1, Nat.succ_pos m⟩
      simp only [Int.cast_negSucc, neg_mul, Real.sin_neg, intervalIntegral.integral_neg]
      simpa only [neg_zero] using congrArg Neg.neg h

private lemma sineL2_orthogonal_eq_zero (f : L2UnitInterval)
    (hf : ∀ k : ℕ+, inner (𝕜 := ℝ) (sineL2 k) f = 0) : f = 0 := by
  have hfLp : MemLp (f : ℝ → ℝ) 2 (volume.restrict (Set.Icc (0 : ℝ) 1)) := Lp.memLp f
  have hFC (n : ℤ) :
      fourierCoeffOn (by norm_num : (-1 : ℝ) < 1) (oddExtension (f : ℝ → ℝ)) n = 0 := by
    rw [oddExtension_fourierCoeff hfLp n, sineIntegral_int_eq_zero f hf n]
    simp
  have hLp : MemLp (oddExtension (f : ℝ → ℝ)) 2
      (volume.restrict (Set.Ioc (-1 : ℝ) 1)) :=
    (oddExtension_memLp hfLp).restrict _
  have hi : (∫ x in (-1 : ℝ)..1, ‖oddExtension (f : ℝ → ℝ) x‖ ^ 2) = 0 := by
    have hp := tsum_sq_fourierCoeffOn (by norm_num : (-1 : ℝ) < 1) hLp
    simp [hFC] at hp
    linarith
  rw [intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1)] at hi
  have hsq : (fun x => ‖oddExtension (f : ℝ → ℝ) x‖ ^ 2) =ᵐ[
      volume.restrict (Set.Ioc (-1 : ℝ) 1)] (0 : ℝ → ℝ) :=
    (integral_eq_zero_iff_of_nonneg (fun _ => sq_nonneg _)
      (hLp.integrable_norm_pow (p := 2) (by norm_num))).mp hi
  have hg : oddExtension (f : ℝ → ℝ) =ᵐ[
      volume.restrict (Set.Ioc (-1 : ℝ) 1)] (0 : ℝ → ℂ) := by
    filter_upwards [hsq] with x hx
    change ‖oddExtension (f : ℝ → ℝ) x‖ ^ 2 = 0 at hx
    apply norm_eq_zero.mp
    nlinarith [norm_nonneg (oddExtension (f : ℝ → ℝ) x)]
  have hμ : volume.restrict (Set.Ioo (0 : ℝ) 1) ≤
      volume.restrict (Set.Ioc (-1 : ℝ) 1) := by
    apply Measure.restrict_mono _ le_rfl
    intro x hx
    exact ⟨by linarith [hx.1], hx.2.le⟩
  have hgp := Filter.Eventually.filter_mono (ae_mono hμ) hg
  have hf0 : (f : ℝ → ℝ) =ᵐ[volume.restrict (Set.Ioo (0 : ℝ) 1)] (0 : ℝ → ℝ) := by
    change ∀ᵐ x ∂volume.restrict (Set.Ioo (0 : ℝ) 1), f x = (0 : ℝ)
    rw [ae_restrict_iff' measurableSet_Ioo] at hgp ⊢
    filter_upwards [hgp] with x hx
    intro hmem
    have hz := hx hmem
    rw [oddExtension_pos (f : ℝ → ℝ) hmem] at hz
    change (f x : ℂ) = 0 at hz
    exact_mod_cast hz
  have hsets : volume.restrict (Set.Ioo (0 : ℝ) 1) =
      volume.restrict (Set.Icc (0 : ℝ) 1) := Measure.restrict_congr_set Ioo_ae_eq_Icc
  apply Lp.eq_zero_iff_ae_eq_zero.mpr
  rwa [hsets] at hf0

private lemma span_sineL2_orthogonal_eq_bot :
    (Submodule.span ℝ (Set.range sineL2))ᗮ = ⊥ := by
  apply (Submodule.eq_bot_iff _).mpr
  intro f hf
  apply sineL2_orthogonal_eq_zero f
  intro k
  exact (Submodule.mem_orthogonal _ _).mp hf (sineL2 k)
    (Submodule.subset_span ⟨k, rfl⟩)

private lemma exists_sineHilbertBasis : ∃ b : HilbertBasis ℕ+ ℝ L2UnitInterval,
    ∀ k : ℕ+, (b k : L2UnitInterval) =ᵐ[volume.restrict (Set.Icc (0 : ℝ) 1)]
      (sineBasisFun k : ℝ → ℝ) := by
  let b := HilbertBasis.mkOfOrthogonalEqBot
    orthonormal_sineL2 span_sineL2_orthogonal_eq_bot
  refine ⟨b, ?_⟩
  intro k
  have hk : b k = sineL2 k := congrFun (HilbertBasis.coe_mkOfOrthogonalEqBot
    orthonormal_sineL2 span_sineL2_orthogonal_eq_bot) k
  rw [hk]
  exact sineL2_coe k

/-- The sine Hilbert basis of real `L²([0,1])`, indexed by positive integers. -/
noncomputable def sineHilbertBasis : HilbertBasis ℕ+ ℝ L2UnitInterval :=
  Classical.choose (p := fun b : HilbertBasis ℕ+ ℝ L2UnitInterval =>
    ∀ k : ℕ+, (b k : L2UnitInterval) =ᵐ[volume.restrict (Set.Icc (0 : ℝ) 1)]
      (sineBasisFun k : ℝ → ℝ)) (by exact exists_sineHilbertBasis)

/-- The representatives of the sine Hilbert basis are exactly the source sine functions. -/
lemma sineHilbertBasis_coe (k : ℕ+) :
    (sineHilbertBasis k : L2UnitInterval) =ᵐ[volume.restrict (Set.Icc (0 : ℝ) 1)]
      (sineBasisFun k : ℝ → ℝ) := by
  exact Classical.choose_spec exists_sineHilbertBasis k

end MathlibExt.Analysis.ODE.GreensOperator

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
on the orthonormal eigenbasis `{b_k}`: if `f = ∑' k, c_k b_k` where
`c_k = ⟨b_k, f⟩`, then `A^{1/2} f = ∑' k, (1 / (kπ)) c_k b_k`. -/
noncomputable def greensOperatorSqrt (b : HilbertBasis ℕ+ ℝ L2UnitInterval) :
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

end MathlibExt.Analysis.ODE.GreensOperator

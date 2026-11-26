/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`benchmark/level2/ma_proofbench_l2_27.lean` (MA-ProofBench, openbmb/ma-proofbench):
Copyright (c) 2026 OpenBMB. Licensed under the MIT License.
Authors: L. Pu et al.

The adapted portions are the Airy solution and the Kato smoothing statement. The Fourier
normalization in the solution has been adjusted as described in the theorem's docstring.

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
-/

module

public import Mathlib.Analysis.Fourier.LpSpace
public import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.FieldTheory.IsRealClosed.Real
import Mathlib.MeasureTheory.Function.JacobianOneDim

/-!
# Kato smoothing for the Airy equation

At every spatial point the time integral of the squared spatial derivative of the Airy
solution equals one third of the squared $L^2$ norm of the initial datum.
-/

@[expose] public section

open MeasureTheory Filter
open scoped SchwartzMap ComplexInnerProductSpace
open scoped FourierTransform

namespace MathlibExt.Analysis.Fourier.AiryKatoSmoothingIdentityWanted

/-- **Fourier solution of the Airy equation.** For $u_0 : \mathbb{R} \to \mathbb{C}$, let
$\widehat{u_0}(\xi) = (2\pi)^{-1/2} \int_{\mathbb{R}} u_0(y) e^{-iy\xi}\,dy$ be its unitary
Fourier transform. The Airy solution with initial datum $u_0$ is the function
$u : \mathbb{R}^2 \to \mathbb{C}$ given by
$$u(t, x) = (2\pi)^{-1/2} \int_{\mathbb{R}} e^{i(t\xi^3 + x\xi)}\, \widehat{u_0}(\xi)\,d\xi,$$
where an integral whose integrand is not integrable is taken to be $0$.

For $u_0 \in C_c^\infty(\mathbb{R})$ this function solves the Airy equation
$\partial_t u + \partial_x^3 u = 0$ with $u(0, \cdot) = u_0$. -/
noncomputable def AirySolution (u0 : ℝ → ℂ) (t x : ℝ) : ℂ :=
  (Real.sqrt (2 * Real.pi))⁻¹ *
    ∫ ξ : ℝ,
      Complex.exp (Complex.I * (t * ξ ^ (3 : ℕ) + x * ξ)) *
        ((Real.sqrt (2 * Real.pi))⁻¹ * (𝓕 u0) (ξ / (2 * Real.pi)))

-- Identify the classical transform of an integrable L² function with its L² transform
-- by pairing both with compactly supported smooth test functions.
private theorem fourier_plancherel {f : ℝ → ℂ} (h₁ : Integrable f) (h₂ : MemLp f 2) :
    MemLp (𝓕 f) 2 ∧ ∫ t, ‖𝓕 f t‖ ^ 2 = ∫ y, ‖f y‖ ^ 2 := by
  let F : Lp ℂ 2 (volume : Measure ℝ) := h₂.toLp f
  have heq : 𝓕 f =ᵐ[volume] (𝓕 F : Lp ℂ 2 volume) := by
    apply ae_eq_of_integral_contDiff_smul_eq
    · rw [← Real.fourierTransform_toLp (memLp_one_iff_integrable.mpr h₁)]
      exact (BoundedContinuousFunction.continuous _).locallyIntegrable
    · exact (Lp.memLp _).locallyIntegrable (by norm_num)
    intro g hg hc
    have hc' : HasCompactSupport (Complex.ofRealCLM ∘ g) := hc.comp_left rfl
    let φ := hc'.toSchwartzMap (show ContDiff ℝ (⊤ : ℕ∞) (Complex.ofRealCLM ∘ g) by fun_prop)
    change ∫ t, φ t * 𝓕 f t = ∫ t, φ t * (𝓕 F) t
    calc
      _ = ∫ y, (𝓕 φ) y * f y := by
        symm
        simpa using! VectorFourier.integral_bilin_fourierIntegral_eq_flip
          (ContinuousLinearMap.mul ℂ ℂ) (L := innerₗ ℝ)
          Real.continuous_fourierChar continuous_inner φ.integrable h₁
      _ = (F : 𝓢'(ℝ, ℂ)) (𝓕 φ) := by
        rw [Lp.toTemperedDistribution_apply]
        apply integral_congr_ae
        filter_upwards [h₂.coeFn_toLp] with y hy
        rw [show F y = f y from hy, smul_eq_mul]
      _ = _ := by
        rw [← TemperedDistribution.fourier_apply, Lp.fourier_toTemperedDistribution_eq,
          Lp.toTemperedDistribution_apply]
        rfl
  refine ⟨(memLp_congr_ae heq).2 (Lp.memLp _), ?_⟩
  have hinner := Lp.inner_fourier_eq F F
  rw [L2.inner_def, L2.inner_def] at hinner
  apply Complex.ofReal_injective
  rw [← integral_complex_ofReal, ← integral_complex_ofReal]
  calc
    _ = ∫ t, ⟪(𝓕 F) t, (𝓕 F) t⟫ := by
      apply integral_congr_ae
      filter_upwards [heq] with t ht
      simp [ht, inner_self_eq_norm_sq_to_K]
    _ = _ := hinner
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [h₂.coeFn_toLp] with y hy
      simp [F, hy, inner_self_eq_norm_sq_to_K]

private noncomputable abbrev scale : ℝ := 2 * Real.pi

private theorem scale_pos : 0 < scale := mul_pos zero_lt_two Real.pi_pos

private noncomputable def phase (s : ℝ) : ℂ := Complex.exp ((s : ℂ) * Complex.I)

private theorem norm_phase (s : ℝ) : ‖phase s‖ = 1 := Complex.norm_exp_ofReal_mul_I s

private noncomputable def wave (t x k : ℝ) : ℂ := phase (t * k ^ 3 + x * k)

private theorem airy_eq (u : ℝ → ℂ) (t x : ℝ) :
    AirySolution u t x = ∫ y, wave t x (scale * y) * 𝓕 u y := by
  let g (y : ℝ) := wave t x (scale * y) * 𝓕 u y
  have h (ξ : ℝ) : scale * (ξ / scale) = ξ := by field_simp [scale_pos.ne']
  have hphase (ξ : ℝ) : Complex.exp (Complex.I * (t * ξ ^ 3 + x * ξ)) = wave t x ξ := by
    simp [wave, phase, mul_comm Complex.I]
  have hs : (Real.sqrt scale : ℂ) ^ 2 = (scale : ℂ) := by
    exact_mod_cast Real.sq_sqrt scale_pos.le
  have hs' : (Real.sqrt scale : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.2 scale_pos).ne'
  unfold AirySolution
  simp_rw [hphase]
  change _ = ∫ y, g y
  have hfactor : (∫ ξ : ℝ, wave t x ξ * ((Real.sqrt scale : ℂ)⁻¹ * 𝓕 u (ξ / scale))) =
      (Real.sqrt scale : ℂ)⁻¹ * ∫ ξ : ℝ, g (ξ / scale) := by
    rw [← integral_const_mul]
    congr 1
    ext ξ
    simp [g, h, mul_left_comm]
  simp only [Complex.ofReal_inv]
  rw [hfactor, Measure.integral_comp_div, abs_of_pos scale_pos, Complex.real_smul]
  field_simp
  linear_combination -(∫ y, g y) * hs

private theorem hasDerivAt_wave (t x k : ℝ) :
    HasDerivAt (fun z => wave t z k) (wave t x k * (k * Complex.I)) x := by
  have h := (((hasDerivAt_id x).mul_const k).const_add (t * k ^ 3)).ofReal_comp
  simpa [wave, phase] using (h.mul_const Complex.I).cexp

private theorem deriv_airy_eq (u : 𝓢(ℝ, ℂ)) (t x : ℝ) :
    deriv (fun z => AirySolution u t z) x =
      ∫ y, wave t x (scale * y) * ((scale * y : ℝ) * Complex.I) * 𝓕 u y := by
  let f := 𝓕 u
  let K (z y : ℝ) := wave t z (scale * y) * f y
  let D (z y : ℝ) := wave t z (scale * y) * ((scale * y : ℝ) * Complex.I) * f y
  have hK (z : ℝ) : Continuous (K z) := by unfold K wave phase; fun_prop
  have hD (z : ℝ) : Continuous (D z) := by unfold D wave phase; fun_prop
  have hb (z y : ℝ) : ‖D z y‖ = scale * (‖y‖ * ‖f y‖) := by
    simp [D, wave, norm_phase, mul_assoc, Real.norm_eq_abs]
  have hi : Integrable (K x) := by
    apply f.integrable.norm.mono' (hK x).aestronglyMeasurable
    exact .of_forall fun y => by simp [K, wave, norm_phase]
  have hd := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume)
    (s := Set.univ) (x₀ := x) (F := K) (F' := D) Filter.univ_mem
    (.of_forall fun z => (hK z).aestronglyMeasurable) hi (hD x).aestronglyMeasurable
    (.of_forall fun y z _ => (hb z y).le)
    (by simpa using (f.integrable_pow_mul volume 1).const_mul scale)
    (.of_forall fun y z _ => (hasDerivAt_wave t z (scale * y)).mul_const (f y))
  simp_rw [airy_eq]
  exact hd.2.deriv

-- With y measured in cycles per unit length, the time frequency is -scale² y³.
private noncomputable def frequency (y : ℝ) := -(scale ^ 2 * y ^ 3)

private noncomputable def jacobian (y : ℝ) := 3 * (scale * y) ^ 2

private theorem jacobian_nonneg (y : ℝ) : 0 ≤ jacobian y := by unfold jacobian; positivity

private theorem frequency_bijective : Function.Bijective frequency := by
  have h₃ : Odd 3 := by decide
  have hc := pow_ne_zero 2 scale_pos.ne'
  constructor
  · intro a b h
    exact h₃.pow_injective (mul_left_cancel₀ hc (neg_injective h))
  · intro z
    obtain ⟨y, hy⟩ := IsRealClosed.exists_eq_pow_of_odd (-z / scale ^ 2) h₃
    exact ⟨y, by unfold frequency; rw [← hy]; field_simp⟩

private theorem hasDerivAt_frequency (y : ℝ) : HasDerivAt frequency (-(jacobian y)) y := by
  have h : -(jacobian y) = -(scale ^ 2 * (3 * y ^ 2)) := by unfold jacobian; ring
  rw [h]
  exact ((hasDerivAt_pow 3 y).const_mul (scale ^ 2)).neg

private theorem integral_frequency {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (g : ℝ → E) :
    ∫ t, g t = ∫ y, jacobian y • g (frequency y) := by
  simpa [Set.image_univ, frequency_bijective.surjective.range_eq, abs_of_nonneg (jacobian_nonneg _)]
    using integral_image_eq_integral_abs_deriv_smul .univ
      (fun y _ => (hasDerivAt_frequency y).hasDerivWithinAt) frequency_bijective.1.injOn g

private theorem integrable_frequency {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (g : ℝ → E) :
    Integrable g ↔ Integrable (fun y => jacobian y • g (frequency y)) := by
  simpa [Set.image_univ, frequency_bijective.surjective.range_eq, abs_of_nonneg (jacobian_nonneg _)]
    using integrableOn_image_iff_integrableOn_abs_deriv_smul .univ
      (fun y _ => (hasDerivAt_frequency y).hasDerivWithinAt) frequency_bijective.1.injOn g

private noncomputable def amplitude (f : ℝ → ℂ) (x y : ℝ) : ℂ :=
  phase (x * (scale * y)) * ((scale * y : ℝ) * Complex.I) * f y

private theorem norm_amplitude (f : ℝ → ℂ) (x y : ℝ) :
    ‖amplitude f x y‖ = |scale * y| * ‖f y‖ := by
  simp [amplitude, norm_phase, Real.norm_eq_abs]

private theorem integrable_amplitude (f : 𝓢(ℝ, ℂ)) (x : ℝ) : Integrable (amplitude f x) := by
  have hc : Continuous (amplitude f x) := by unfold amplitude phase; fun_prop
  apply Integrable.mono' (g := fun y => scale * (‖y‖ * ‖f y‖)) _ hc.aestronglyMeasurable
  · exact .of_forall fun y => by
      rw [norm_amplitude, abs_mul, abs_of_pos scale_pos, Real.norm_eq_abs, mul_assoc]
  · simpa using (f.integrable_pow_mul volume 1).const_mul scale

-- The transformed density has a singularity at frequency zero. Its value there contributes
-- nothing to the integral, and multiplication by the Jacobian recovers the amplitude everywhere.
private noncomputable def timeDensity (f : ℝ → ℂ) (x t : ℝ) : ℂ :=
  let y := Function.invFun frequency t
  (jacobian y)⁻¹ • amplitude f x y

private theorem jacobian_smul_density (f : ℝ → ℂ) (x y : ℝ) :
    jacobian y • timeDensity f x (frequency y) = amplitude f x y := by
  rw [timeDensity, Function.leftInverse_invFun frequency_bijective.1 y]
  by_cases h : y = 0
  · simp [h, jacobian, amplitude]
  · have hj : jacobian y ≠ 0 := by unfold jacobian; positivity
    rw [smul_smul, mul_inv_cancel₀ hj, one_smul]

private theorem jacobian_density_sq (f : ℝ → ℂ) (x : ℝ) :
    (fun y => jacobian y • ‖timeDensity f x (frequency y)‖ ^ 2) =ᵐ[volume]
      fun y => (1 / 3 : ℝ) * ‖f y‖ ^ 2 := by
  filter_upwards [volume.ae_ne (0 : ℝ)] with y hy
  have hk : scale * y ≠ 0 := mul_ne_zero scale_pos.ne' hy
  have h := congrArg norm (jacobian_smul_density f x y)
  rw [norm_smul, norm_amplitude, Real.norm_eq_abs, abs_of_nonneg (jacobian_nonneg y)] at h
  have hs := congrArg (· ^ 2) h
  simp only [mul_pow, sq_abs] at hs
  change 3 * (scale * y) ^ 2 * _ = _
  unfold jacobian at hs
  apply mul_left_cancel₀ (pow_ne_zero 2 hk)
  linear_combination hs / 3

private theorem deriv_airy_fourier (u : 𝓢(ℝ, ℂ)) (x : ℝ) :
    (fun t => deriv (fun z => AirySolution u t z) x) = 𝓕 (timeDensity (𝓕 u : 𝓢(ℝ, ℂ)) x) := by
  ext t
  rw [deriv_airy_eq, Real.fourier_real_eq_integral_exp_smul, integral_frequency
    (fun s => Complex.exp (↑(-2 * Real.pi * s * t) * Complex.I) • timeDensity (𝓕 u : 𝓢(ℝ, ℂ)) x s)]
  apply integral_congr_ae
  refine .of_forall fun y => ?_
  dsimp only
  rw [smul_comm (jacobian y), jacobian_smul_density, smul_eq_mul]
  have h : -2 * Real.pi * frequency y * t + x * (scale * y) =
      t * (scale * y) ^ 3 + x * (scale * y) := by unfold frequency scale; ring
  unfold wave amplitude
  rw [← h]
  simp only [phase, Complex.ofReal_add, add_mul, Complex.exp_add]
  ring

/-- **Sharp Kato smoothing identity for Schwartz data.** For a Schwartz initial datum $u_0$,
the spatial derivative of the Airy solution belongs to $L^2$ in time at every spatial point.
Its squared $L^2$ norm is one third of the squared $L^2$ norm of $u_0$. The factor $1/3$ follows
from Plancherel's identity in time after the substitution $\tau = \xi^3$.

Source: J. E. Colliander and C. E. Kenig, *The generalized Korteweg-de Vries equation on the
half line*, Lemma 4.1, proof of (4.6), p. 16, with $s = -1$ and $\phi = \partial_x u_0$
([arXiv:math/0111294v3](https://arxiv.org/pdf/math/0111294v3#page=16)). -/
public theorem integral_norm_deriv_airySolution_sq_eq (u : 𝓢(ℝ, ℂ)) (x : ℝ) :
    MemLp (fun t => deriv (fun z => AirySolution u t z) x) 2 ∧
    (∫ t, ‖deriv (fun z => AirySolution u t z) x‖ ^ 2) = (1 / 3 : ℝ) * ∫ y, ‖u y‖ ^ 2 := by
  let f := 𝓕 u
  let g := timeDensity f x
  have h₁ : Integrable g := by
    rw [integrable_frequency]
    simpa only [g, jacobian_smul_density] using integrable_amplitude f x
  have h₂ : MemLp g 2 := by
    rw [memLp_two_iff_integrable_sq_norm h₁.aestronglyMeasurable, integrable_frequency]
    apply (integrable_congr (jacobian_density_sq f x)).2
    exact (f.memLp 2 volume).norm.integrable_sq.const_mul _
  obtain ⟨hm, hnorm⟩ := fourier_plancherel h₁ h₂
  have heq := congrFun (deriv_airy_fourier u x)
  refine ⟨(deriv_airy_fourier u x) ▸ hm, ?_⟩
  simp only [heq]
  calc
    _ = ∫ s, ‖g s‖ ^ 2 := hnorm
    _ = ∫ y, (1 / 3 : ℝ) * ‖f y‖ ^ 2 :=
      (integral_frequency _).trans (integral_congr_ae (jacobian_density_sq f x))
    _ = _ := by rw [integral_const_mul, SchwartzMap.integral_norm_sq_fourier]

/-- **Kato smoothing identity for the Airy equation.** For $u_0 : \mathbb{R} \to \mathbb{C}$ let
$\widehat{u_0}(\xi) = (2\pi)^{-1/2} \int_{\mathbb{R}} u_0(y) e^{-iy\xi}\,dy$ be its unitary
Fourier transform, and let
$u(t, x) = (2\pi)^{-1/2} \int_{\mathbb{R}} e^{i(t\xi^3 + x\xi)}\, \widehat{u_0}(\xi)\,d\xi$ be
the Airy solution with initial datum $u_0$. There is a constant $c_0 > 0$ such that for every
smooth compactly supported $u_0 : \mathbb{R} \to \mathbb{C}$ and every $x_0 \in \mathbb{R}$, the
function $t \mapsto \partial_x u(t, x_0)$ belongs to $L^2(\mathbb{R})$ and
$$\int_{\mathbb{R}} |\partial_x u(t, x_0)|^2\,dt = c_0 \int_{\mathbb{R}} |u_0(x)|^2\,dx.$$

The source's formalization used the transform $\int u_0(y) e^{-2\pi i y\xi}\,dy$ together with
the unitary phase and prefactor, so its initial datum was not $u_0$ but the $L^2$-isometric
rescaling $x \mapsto (2\pi)^{-1/2} u_0(x / 2\pi)$; the identity holds for both with the same
$c_0$.

Source: MA-ProofBench (L. Pu et al., arXiv:2606.13782), Level II (Functional analysis;
Distributions, generalized functions, distribution spaces),
`benchmark/level2/ma_proofbench_l2_27.lean` at openbmb/ma-proofbench@31bab4c, with the change
above.
-/
public theorem exists_pos_const_integral_norm_deriv_airySolution_sq_eq :
  ∃ c0 : ℝ, 0 < c0 ∧
    ∀ (u0 : ℝ → ℂ),
      ContDiff ℝ (⊤ : ℕ∞) u0 →
      HasCompactSupport u0 →
      (∀ x0 : ℝ,
          MemLp (fun t : ℝ => deriv (fun x : ℝ => AirySolution u0 t x) x0)
            (2 : ENNReal) volume) ∧
        ∀ x0 : ℝ,
          ∫ t : ℝ, ‖deriv (fun x : ℝ => AirySolution u0 t x) x0‖ ^ (2 : ℕ) =
            c0 * ∫ x : ℝ, ‖u0 x‖ ^ (2 : ℕ) := by
  refine ⟨1 / 3, by norm_num, ?_⟩
  intro u0 hu hc
  let u := hc.toSchwartzMap hu
  exact ⟨fun x => (integral_norm_deriv_airySolution_sq_eq u x).1,
    fun x => (integral_norm_deriv_airySolution_sq_eq u x).2⟩

end MathlibExt.Analysis.Fourier.AiryKatoSmoothingIdentityWanted

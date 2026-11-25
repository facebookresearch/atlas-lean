/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`benchmark/level2/ma_proofbench_l2_54.lean` (openbmb/ma-proofbench, commit 31bab4c).
The statement and its description are adapted from MA-ProofBench by L. Pu et al.
Licensed under the MIT License.

Copyright (c) 2026 OpenBMB

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

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import MathlibExt.Analysis.Distribution.GaussianSchwartz

/-!
# The commutant of coordinate multiplication and differentiation on Schwartz space

Every complex-linear endomorphism of Schwartz space on the real line that commutes with both
operators is scalar. Division by the shifted coordinate identifies the kernel of evaluation
at each point, and differentiation forces the resulting pointwise multiplier to be constant.
-/

public section

open scoped ContDiff SchwartzMap

namespace MathlibExt.Analysis.Distribution.SchwartzCommutantMulDerivWanted

/-- If multiplying a smooth function by the shifted coordinate gives a Schwartz function,
then each of its derivatives is Schwartz after multiplication by a suitable coordinate power. -/
private theorem exists_weighted_deriv (a : ℝ) (g : ℝ → ℂ) (hg : ContDiff ℝ ∞ g)
    (f : 𝓢(ℝ, ℂ)) (hf : ∀ x : ℝ, f x = (x - a : ℂ) * g x) (n : ℕ) :
    ∃ F : 𝓢(ℝ, ℂ), ∀ x : ℝ, F x = (x - a : ℂ) ^ (n + 1) * iteratedDeriv n g x := by
  let u : ℝ → ℂ := fun x ↦ (x - a : ℂ)
  have hu : u.HasTemperateGrowth :=
    Complex.hasTemperateGrowth_ofReal.sub (Function.HasTemperateGrowth.const _)
  induction n with
  | zero => exact ⟨f, fun x ↦ by simpa using hf x⟩
  | succ n ih =>
    obtain ⟨F, hF⟩ := ih
    -- Differentiate F = u^(n+1) g⁽ⁿ⁾ and clear one more factor of u.
    refine ⟨SchwartzMap.smulLeftCLM ℂ u (SchwartzMap.derivCLM ℂ ℂ F) -
      ((n + 1 : ℕ) : ℂ) • F, fun x ↦ ?_⟩
    have hu' : HasDerivAt u 1 x := by
      simpa [u] using ((hasDerivAt_id x).ofReal_comp.sub_const (a : ℂ))
    have hdiff := hg.differentiable_iteratedDeriv n (by exact_mod_cast ENat.natCast_lt_top n)
    have hd := ((hu'.fun_pow (n + 1)).fun_mul (hdiff x).hasDerivAt).deriv
    change deriv (fun y ↦ u y ^ (n + 1) * iteratedDeriv n g y) x = _ at hd
    rw [show (fun y ↦ u y ^ (n + 1) * iteratedDeriv n g y) = ⇑F from
      (funext hF).symm] at hd
    simp only [sub_apply, SchwartzMap.smulLeftCLM_apply_apply hu,
      SchwartzMap.derivCLM_apply, smul_apply, smul_eq_mul]
    rw [hd, hF x, iteratedDeriv_succ]
    dsimp [u]
    simp only [pow_succ]
    ring

/-- A Schwartz function vanishing at a point is divisible in Schwartz space by the
coordinate minus that point. -/
private theorem exists_factor (f : 𝓢(ℝ, ℂ)) (a : ℝ) (ha : f a = 0) :
    ∃ G : 𝓢(ℝ, ℂ), ∀ x : ℝ, f x = (x - a : ℂ) * G x := by
  let g : ℝ → ℂ := fun x ↦ ∫ t in (0 : ℝ)..1, deriv f ((x - a) * t + a)
  have hd : ContDiff ℝ ∞ (deriv f) := (SchwartzMap.derivCLM ℂ ℂ f).smooth _
  have hg : ContDiff ℝ ∞ g :=
    (hd.comp (show ContDiff ℝ ∞ (fun p : ℝ × ℝ ↦ (p.1 - a) * p.2 + a) by
      fun_prop)).parametric_intervalIntegral
  have hfg (x : ℝ) : f x = (x - a : ℂ) * g x := by
    have h := intervalIntegral.smul_integral_comp_mul_add (deriv f) (a := 0) (b := 1) (x - a) a
    rw [mul_zero, zero_add, mul_one, sub_add_cancel,
      intervalIntegral.integral_deriv_eq_sub (fun _ _ ↦ f.differentiableAt)
        (hd.continuous.intervalIntegrable _ _), ha, sub_zero] at h
    simpa only [g, Complex.real_smul, Complex.ofReal_sub] using h.symm
  refine ⟨⟨g, hg, ?_⟩, hfg⟩
  intro k n
  obtain ⟨F, hF⟩ := exists_weighted_deriv a g hg f hfg n
  -- On the unit ball use compactness. Outside it the coordinate power has norm at least one.
  have hc := (continuous_norm.pow k).mul
    (hg.continuous_iteratedDeriv n (by simp)).norm
  obtain ⟨C, hC⟩ := (isCompact_closedBall a 1).exists_bound_of_continuousOn hc.continuousOn
  refine ⟨max C (SchwartzMap.seminorm ℂ k 0 F), fun x ↦ ?_⟩
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]
  by_cases hx : x ∈ Metric.closedBall a 1
  · exact (le_abs_self _).trans ((hC x hx).trans (le_max_left _ _))
  · have hu : 1 ≤ ‖(x - a : ℂ)‖ := by
      simpa [Metric.mem_closedBall, Real.dist_eq, ← Complex.ofReal_sub] using
        (le_of_lt (lt_of_not_ge hx) : 1 ≤ dist x a)
    refine le_trans ?_ ((F.norm_pow_mul_le_seminorm ℂ k x).trans (le_max_right _ _))
    rw [hF, norm_mul, norm_pow]
    gcongr
    exact le_mul_of_one_le_left (norm_nonneg _) (one_le_pow₀ hu)

/-- **Linear maps on Schwartz space commuting with $x$ and $d/dx$ are scalars.** Let
$\mathcal{S}(\mathbb{R})$ be the space of complex-valued Schwartz functions on $\mathbb{R}$, and
let $M:\mathcal{S}(\mathbb{R})\to\mathcal{S}(\mathbb{R})$ be a $\mathbb{C}$-linear map with
$(Mf)(x)=x f(x)$ for all $f\in\mathcal{S}(\mathbb{R})$ and $x\in\mathbb{R}$. If
$T:\mathcal{S}(\mathbb{R})\to\mathcal{S}(\mathbb{R})$ is a $\mathbb{C}$-linear map (not assumed
continuous) with $TM=MT$ and $T\frac{d}{dx}=\frac{d}{dx}T$, then there exists $c\in\mathbb{C}$
such that $Tf=cf$ for all $f\in\mathcal{S}(\mathbb{R})$.

Source: MA-ProofBench (L. Pu et al., arXiv:2606.13782), Level II (Operator theory; General
theory of linear operators), `benchmark/level2/ma_proofbench_l2_54.lean` at
openbmb/ma-proofbench@31bab4c.
-/
public theorem exists_eq_smul_of_comp_mul_eq_of_comp_deriv_eq
    (T : SchwartzMap ℝ ℂ →ₗ[ℂ] SchwartzMap ℝ ℂ)
    (M : SchwartzMap ℝ ℂ →ₗ[ℂ] SchwartzMap ℝ ℂ)
    (hM : ∀ f : SchwartzMap ℝ ℂ, ∀ x : ℝ, M f x = (x : ℂ) * f x)
    (hTM : T.comp M = M.comp T)
    (hTd :
      T.comp (SchwartzMap.derivCLM ℂ ℂ).toLinearMap =
        (SchwartzMap.derivCLM ℂ ℂ).toLinearMap.comp T) :
    ∃ c : ℂ, ∀ f : SchwartzMap ℝ ℂ, T f = c • f := by
  -- Commutation with the coordinate preserves the kernel of evaluation at a.
  have hker (a : ℝ) (f : 𝓢(ℝ, ℂ)) (ha : f a = 0) : T f a = 0 := by
    obtain ⟨G, hG⟩ := exists_factor f a ha
    have hf : f = M G - (a : ℂ) • G := by
      ext x
      rw [hG, sub_apply, hM, smul_apply, smul_eq_mul]
      ring
    have hcomm : T (M G) = M (T G) := LinearMap.congr_fun hTM G
    rw [hf, map_sub, map_smul, hcomm, sub_apply, hM,
      smul_apply, smul_eq_mul, sub_self]
  obtain ⟨q, hq⟩ := GaussianSchwartzWanted.gaussian_mem_schwartz (E := ℝ)
  let G := q.postcompCLM Complex.ofRealCLM
  have hG (x : ℝ) : G x ≠ 0 := by simp [G, hq]
  have hcross (x : ℝ) (f : 𝓢(ℝ, ℂ)) : G x * T f x = f x * T G x := by
    have h := hker x (G x • f - f x • G) (by simp [mul_comm])
    simpa [sub_eq_zero] using h
  -- The multiplier T G / G has zero derivative by commutation with differentiation.
  let c : ℝ → ℂ := fun x ↦ T G x / G x
  have hc (x : ℝ) : HasDerivAt c 0 x := by
    have hd : T (SchwartzMap.derivCLM ℂ ℂ G) = SchwartzMap.derivCLM ℂ ℂ (T G) :=
      LinearMap.congr_fun hTd G
    have h := hcross x (SchwartzMap.derivCLM ℂ ℂ G)
    simp only [hd, SchwartzMap.derivCLM_apply] at h
    have hz : deriv (T G) x * G x - T G x * deriv G x = 0 := by
      linear_combination h
    simpa only [c, hz, zero_div] using!
      (((T G).hasDerivAt x).fun_div (G.hasDerivAt x) (hG x))
  refine ⟨c 0, fun f ↦ SchwartzMap.ext fun x ↦ ?_⟩
  have heq := is_const_of_deriv_eq_zero (fun x ↦ (hc x).differentiableAt)
    (fun x ↦ (hc x).deriv) x 0
  change T f x = c 0 * f x
  rw [← heq]
  dsimp [c]
  field_simp [hG]
  linear_combination hcross x f

end MathlibExt.Analysis.Distribution.SchwartzCommutantMulDerivWanted

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
import Mathlib.Analysis.Calculus.TaylorIntegral
import Mathlib.Analysis.Normed.Module.Completion
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Positivity

/-! # Taylor's theorem with little-o remainder

The integral remainder along the segment from the base point to `x` is split into its value
with the highest derivative frozen at the base point and an error controlled by continuity.
The theorem holds for a normed codomain without assuming completeness, by working in its
completion and using the isometric embedding to transfer the bound back.
-/

public section

open Filter Set Asymptotics MeasureTheory
open scoped Topology Interval BigOperators

namespace MathlibExt.Analysis.Calculus.TaylorLittleoRemainderWanted

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

private noncomputable def taylorPolynomial (f : E → F) (a : E) (n : ℕ) (y : E) : F :=
  ∑ k ∈ Finset.range (n + 1), (Nat.factorial k : ℝ)⁻¹ •
    iteratedFDeriv ℝ k f a (fun _ => y)

private theorem integral_taylorKernel (n : ℕ) :
    (∫ t in (0 : ℝ)..1, (1 - t) ^ n) = ((n : ℝ) + 1)⁻¹ := by
  calc
    _ = ∫ t in (0 : ℝ)..1, t ^ n := by
      simpa only [sub_self, sub_zero] using
        intervalIntegral.integral_comp_sub_left (a := (0 : ℝ)) (b := 1)
          (fun t : ℝ => t ^ n) 1
    _ = _ := by simp [integral_pow, div_eq_mul_inv]

private theorem taylor_isLittleO_of_completeSpace [CompleteSpace F] {f : E → F} {a : E} {n : ℕ}
    (hf : ContDiffAt ℝ n f a) :
    (fun x => f x - taylorPolynomial f a n (x - a)) =o[𝓝 a] fun x => ‖x - a‖ ^ n := by
  cases n with
  | zero =>
    simp only [taylorPolynomial, Nat.zero_add, Finset.range_one, Finset.sum_singleton,
      Nat.factorial_zero, Nat.cast_one, inv_one, one_smul, iteratedFDeriv_zero_apply, pow_zero]
    rw [Asymptotics.isLittleO_one_iff ℝ]
    simpa only [sub_self] using hf.continuousAt.tendsto.sub (tendsto_const_nhds (x := f a))
  | succ n =>
    rw [Asymptotics.isLittleO_iff]
    intro c hc
    -- Choose one ball where the highest derivative varies by less than `c`.
    let D := iteratedFDeriv ℝ (n + 1) f
    have hcont : ContinuousAt D a := hf.continuousAt_iteratedFDeriv (k := n + 1) le_rfl
    have hclose : ∀ᶠ z in 𝓝 a, ‖D z - D a‖ < c := by
      filter_upwards [hcont.tendsto.eventually_mem (Metric.ball_mem_nhds (D a) hc)] with z hz
      simpa only [Metric.mem_ball, dist_eq_norm] using hz
    obtain ⟨δ, hδ, hlocal⟩ := Metric.eventually_nhds_iff.mp ((hf.eventually (by simp)).and hclose)
    filter_upwards [Metric.ball_mem_nhds a hδ] with x hx
    let y := x - a
    have hxy : a + y = x := by simp [y]
    have hsegment (t : ℝ) (ht : t ∈ Icc 0 1) : dist (a + t • y) a < δ := by
      rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1]
      exact (mul_le_of_le_one_left (norm_nonneg y) ht.2).trans_lt (by
        simpa only [Metric.mem_ball, dist_eq_norm, y] using hx)
    have hs (t : ℝ) (ht : t ∈ Icc 0 1) : ContDiffAt ℝ (↑n + 1) f (a + t • y) := by
      simpa only [Nat.cast_succ] using (hlocal (hsegment t ht)).1
    let A (t : ℝ) := D (a + t • y) (fun _ => y)
    let B := D a (fun _ => y)
    let K (t : ℝ) : ℝ := (1 - t) ^ n
    have hK : Continuous K := by fun_prop
    have hA : ContinuousOn A (Icc 0 1) := by
      intro t ht
      have htD : ContinuousAt D (a + t • y) :=
        (hlocal (hsegment t ht)).1.continuousAt_iteratedFDeriv (k := n + 1) le_rfl
      have hline : ContinuousAt (fun s : ℝ => a + s • y) t := by fun_prop
      have hpath : ContinuousAt (fun s : ℝ => D (a + s • y)) t :=
        htD.comp (f := fun s : ℝ => a + s • y) hline
      exact (hpath.eval_const (fun _ => y)).continuousWithinAt
    have hIA : IntervalIntegrable (fun t => K t • A t) volume 0 1 := by
      apply ContinuousOn.intervalIntegrable
      rw [uIcc_of_le zero_le_one]
      exact hK.continuousOn.smul hA
    have hIB : IntervalIntegrable (fun t => K t • B) volume 0 1 := by
      apply Continuous.intervalIntegrable
      exact hK.smul continuous_const
    -- The kernel has integral `1 / (n + 1)`, giving the last Taylor coefficient.
    have hfact : (Nat.factorial n : ℝ)⁻¹ * ((n : ℝ) + 1)⁻¹ =
        (Nat.factorial (n + 1) : ℝ)⁻¹ := by
      rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_succ, mul_inv_rev]
    have hIBval : (Nat.factorial n : ℝ)⁻¹ • (∫ t in (0 : ℝ)..1, K t • B) =
        (Nat.factorial (n + 1) : ℝ)⁻¹ • B := by
      rw [intervalIntegral.integral_smul_const, smul_smul]
      change ((Nat.factorial n : ℝ)⁻¹ * (∫ t in (0 : ℝ)..1, (1 - t) ^ n)) • B = _
      rw [integral_taylorKernel, hfact]
    have hsum := map_add_eq_sum_add_integral_iteratedFDeriv (f := f) (x := a) (y := y) (n := n) hs
    rw [hxy] at hsum
    change f x = taylorPolynomial f a n y + (Nat.factorial n : ℝ)⁻¹ •
      (∫ t in (0 : ℝ)..1, K t • A t) at hsum
    have hpoly : taylorPolynomial f a (n + 1) y =
        taylorPolynomial f a n y + (Nat.factorial (n + 1) : ℝ)⁻¹ • B := by
      unfold taylorPolynomial
      rw [Finset.sum_range_succ]
    -- Subtract the integral with the highest derivative frozen at the base point.
    have herr : f x - taylorPolynomial f a (n + 1) y = (Nat.factorial n : ℝ)⁻¹ •
        (∫ t in (0 : ℝ)..1, K t • (A t - B)) := by
      simp_rw [smul_sub]
      rw [intervalIntegral.integral_sub hIA hIB, smul_sub, hIBval, hpoly, hsum]
      abel
    have hnormI : ‖∫ t in (0 : ℝ)..1, K t • (A t - B)‖ ≤ c * ‖y‖ ^ (n + 1) := by
      have hest (t : ℝ) (ht : t ∈ Ι (0 : ℝ) 1) :
          ‖K t • (A t - B)‖ ≤ c * ‖y‖ ^ (n + 1) := by
        have ht' : t ∈ Icc (0 : ℝ) 1 := by
          rw [uIoc_of_le zero_le_one] at ht
          exact Ioc_subset_Icc_self ht
        have hKn : ‖K t‖ ≤ 1 := by
          change ‖(1 - t) ^ n‖ ≤ 1
          rw [norm_pow, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr ht'.2)]
          exact pow_le_one₀ (sub_nonneg.mpr ht'.2) (sub_le_self _ ht'.1)
        have hAn : ‖A t - B‖ ≤ c * ‖y‖ ^ (n + 1) := calc
          _ = ‖(D (a + t • y) - D a) (fun _ => y)‖ := rfl
          _ ≤ ‖D (a + t • y) - D a‖ * ‖y‖ ^ (n + 1) := by
            simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] using
              (D (a + t • y) - D a).le_opNorm (fun _ => y)
          _ ≤ _ := mul_le_mul_of_nonneg_right (hlocal (hsegment t ht')).2.le (by positivity)
        rw [norm_smul]
        exact (mul_le_of_le_one_left (norm_nonneg _) hKn).trans hAn
      simpa only [sub_zero, abs_one, mul_one] using
        intervalIntegral.norm_integral_le_of_norm_le_const hest
    have hfac : ‖(Nat.factorial n : ℝ)⁻¹‖ ≤ 1 := by
      rw [Real.norm_of_nonneg (by positivity), inv_eq_one_div, div_le_iff₀ (by positivity), one_mul]
      exact_mod_cast Nat.factorial_pos n
    change ‖f x - taylorPolynomial f a (n + 1) y‖ ≤ c * ‖‖y‖ ^ (n + 1)‖
    rw [norm_pow, norm_norm, herr, norm_smul]
    exact (mul_le_of_le_one_left (norm_nonneg _) hfac).trans hnormI

/-- **Taylor's theorem with little-o remainder in several variables.** Let $E$ and $F$ be normed
vector spaces over $\mathbb{R}$, let $n$ be a natural number, and let $f : E \to F$ be $n$ times
continuously differentiable on a neighbourhood of a point $x_0 \in E$. Write $D^k f(x_0)$ for the
$k$-th Fréchet derivative of $f$ at $x_0$, a continuous $k$-linear map from $E^k$ to $F$. Then, as
$x$ tends to $x_0$,
$$f(x) - \sum_{k=0}^{n} \frac{1}{k!}\, D^k f(x_0)(x - x_0, \ldots, x - x_0) =
o\bigl(\|x - x_0\|^n\bigr).$$

Sources:
- Mathlib `docs/undergrad.yaml`, section "Multivariable calculus / Differential
  calculus", entry "Taylor's theorem with little-o remainder" (currently missing:
  empty entry, no Mathlib declaration). The integral-remainder form exists as
  `map_add_eq_sum_add_integral_iteratedFDeriv`.
- H. Cartan, *Differential Calculus*, Ch. III, Taylor's formula with remainder.
- https://en.wikipedia.org/wiki/Taylor%27s_theorem#Taylor's_theorem_in_several_variables
-/
theorem taylor_isLittleO_multivariable
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E → F} {x₀ : E} {n : ℕ} (hf : ContDiffAt ℝ n f x₀) :
    (fun x ↦ f x - ∑ k ∈ Finset.range (n + 1),
      ((Nat.factorial k : ℝ))⁻¹ •
        iteratedFDeriv ℝ k f x₀ (fun _ ↦ x - x₀)) =o[nhds x₀]
      fun x ↦ ‖x - x₀‖ ^ n := by
  -- Work in the completion, then transfer the estimate back by isometry.
  let j : F →ₗᵢ[ℝ] UniformSpace.Completion F := UniformSpace.Completion.toComplₗᵢ
  let J := j.toContinuousLinearMap
  have hcomp : ContDiffAt ℝ n (J ∘ f) x₀ := J.contDiff.contDiffAt.comp x₀ hf
  have h := taylor_isLittleO_of_completeSpace hcomp
  change (fun x => f x - taylorPolynomial f x₀ n (x - x₀)) =o[𝓝 x₀] fun x => ‖x - x₀‖ ^ n
  have hpoly (y : E) : taylorPolynomial (J ∘ f) x₀ n y = J (taylorPolynomial f x₀ n y) := by
    unfold taylorPolynomial
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro k hk
    rw [J.iteratedFDeriv_comp_left hf (by exact_mod_cast Finset.mem_range_succ_iff.mp hk)]
    simp only [ContinuousLinearMap.compContinuousMultilinearMap_coe, Function.comp_apply, map_smul]
  rw [Asymptotics.isLittleO_iff] at h ⊢
  intro c hc
  filter_upwards [h hc] with x hx
  change ‖J (f x) - taylorPolynomial (J ∘ f) x₀ n (x - x₀)‖ ≤ _ at hx
  rw [hpoly, ← map_sub] at hx
  simpa only [J, LinearIsometry.coe_toContinuousLinearMap, j.norm_map] using hx

end MathlibExt.Analysis.Calculus.TaylorLittleoRemainderWanted

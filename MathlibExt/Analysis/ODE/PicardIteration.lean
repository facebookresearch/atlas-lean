/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Topology.MetricSpace.Lipschitz

import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Picard iteration

This file proves the factorial estimate for successive Picard iterates and their locally uniform
convergence to a solution for a globally Lipschitz vector field, given a sequence satisfying
the Picard recursion. Global existence from the Lipschitz hypothesis alone is proved separately
as `MathlibExt.Analysis.ODE.MaximalSolutionWanted.ode_global_exists_of_global_lipschitz`.
-/

open MeasureTheory

@[expose] public section

namespace MathlibExt.Analysis.ODE.PicardIterationWanted

private theorem picard_iterate_continuous
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℝ → E → E) (t₀ : ℝ) (x₀ : E)
    (hfcont : Continuous (Function.uncurry f))
    (u : ℕ → ℝ → E) (hu0 : u 0 = fun _ => x₀)
    (hu : ∀ n t, u (n + 1) t = x₀ + ∫ s in t₀..t, f s (u n s)) :
    ∀ n, Continuous (u n) := by
  intro n
  induction n with
  | zero => simpa only [hu0] using continuous_const
  | succ n hn =>
      rw [show u (n + 1) = fun t => x₀ + ∫ s in t₀..t, f s (u n s) from funext (hu n)]
      have hcomp : Continuous (fun s => f s (u n s)) := by
        change Continuous (Function.uncurry f ∘ fun s => (s, u n s))
        exact hfcont.comp (continuous_id.prodMk hn)
      exact continuous_const.add
        (intervalIntegral.continuous_primitive (fun a b => hcomp.intervalIntegrable a b) t₀)

private theorem picard_integral_majorant (t₀ t C : ℝ) (hC : 0 ≤ C) (n : ℕ) :
    ∫ s in Set.uIoc t₀ t, C * |s - t₀| ^ n / (Nat.factorial n : ℝ) =
      C * |t - t₀| ^ (n + 1) / (Nat.factorial (n + 1) : ℝ) := by
  have hnonneg : 0 ≤ ∫ s in Set.uIoc t₀ t,
      C * |s - t₀| ^ n / (Nat.factorial n : ℝ) := by
    apply MeasureTheory.integral_nonneg
    intro s
    positivity
  rw [← abs_of_nonneg hnonneg, ← intervalIntegral.abs_intervalIntegral_eq,
    intervalIntegral.integral_div,
    intervalIntegral.integral_const_mul, abs_div, abs_mul, abs_of_nonneg hC,
    intervalIntegral.abs_intervalIntegral_eq, integral_pow_abs_sub_uIoc]
  rw [abs_of_nonneg (by positivity :
    0 ≤ |t - t₀| ^ (n + 1) / (n + 1 : ℝ)),
    Nat.abs_cast, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  field_simp

private theorem picard_step_estimate_on_ball
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℝ → E → E) (t₀ : ℝ) (x₀ : E) (L : NNReal)
    (hfcont : Continuous (Function.uncurry f))
    (hlip : ∀ t, LipschitzWith L (f t))
    (u : ℕ → ℝ → E) (hu0 : u 0 = fun _ => x₀)
    (hu : ∀ n t, u (n + 1) t = x₀ + ∫ s in t₀..t, f s (u n s))
    (R M : ℝ) (hR : 0 ≤ R) (hM : ∀ s, |s - t₀| ≤ R → ‖f s x₀‖ ≤ M) :
    ∀ n t, |t - t₀| ≤ R → ‖u (n + 1) t - u n t‖ ≤
      M * (L : ℝ) ^ n * |t - t₀| ^ (n + 1) / (Nat.factorial (n + 1) : ℝ) := by
  have hM0 : 0 ≤ M :=
    (norm_nonneg (f t₀ x₀)).trans (hM t₀ (by simpa using hR))
  have hcont := picard_iterate_continuous f t₀ x₀ hfcont u hu0 hu
  have hcomp (n : ℕ) : Continuous (fun s => f s (u n s)) := by
    change Continuous (Function.uncurry f ∘ fun s => (s, u n s))
    exact hfcont.comp (continuous_id.prodMk (hcont n))
  intro n
  induction n with
  | zero =>
      intro t ht
      rw [hu 0 t, hu0, add_sub_cancel_left]
      simpa using intervalIntegral.norm_integral_le_of_norm_le_const (fun s hs =>
        hM s ((Set.abs_sub_left_of_mem_uIcc (Set.uIoc_subset_uIcc hs)).trans ht))
  | succ n hn =>
      intro t ht
      rw [hu (n + 1) t, hu n t, add_sub_add_left_eq_sub,
        ← intervalIntegral.integral_sub ((hcomp (n + 1)).intervalIntegrable t₀ t)
          ((hcomp n).intervalIntegrable t₀ t)]
      calc
        ‖∫ s in t₀..t, f s (u (n + 1) s) - f s (u n s)‖ ≤
            ∫ s in Set.uIoc t₀ t,
              (M * (L : ℝ) ^ (n + 1)) * |s - t₀| ^ (n + 1) /
                (Nat.factorial (n + 1) : ℝ) := by
          rw [intervalIntegral.norm_intervalIntegral_eq]
          apply MeasureTheory.norm_integral_le_of_norm_le
          · exact Continuous.integrableOn_uIoc (by fun_prop)
          · apply ae_restrict_mem measurableSet_Ioc |>.mono
            intro s hs
            have hsR := (Set.abs_sub_left_of_mem_uIcc
              (Set.uIoc_subset_uIcc hs)).trans ht
            rw [← dist_eq_norm]
            calc
              dist (f s (u (n + 1) s)) (f s (u n s)) ≤
                  (L : ℝ) * dist (u (n + 1) s) (u n s) :=
                (hlip s).dist_le_mul _ _
              _ ≤ (L : ℝ) *
                    (M * (L : ℝ) ^ n * |s - t₀| ^ (n + 1) /
                      (Nat.factorial (n + 1) : ℝ)) := by
                gcongr
                simpa only [dist_eq_norm] using hn s hsR
              _ = (M * (L : ℝ) ^ (n + 1)) * |s - t₀| ^ (n + 1) /
                    (Nat.factorial (n + 1) : ℝ) := by ring
        _ = M * (L : ℝ) ^ (n + 1) * |t - t₀| ^ (n + 2) /
              (Nat.factorial (n + 2) : ℝ) := by
          simpa only [mul_assoc] using picard_integral_majorant t₀ t
            (M * (L : ℝ) ^ (n + 1)) (by positivity) (n + 1)

private theorem picard_exists_bound_on_ball
    {E : Type*} [NormedAddCommGroup E]
    (f : ℝ → E → E) (t₀ : ℝ) (x₀ : E)
    (hfcont : Continuous (Function.uncurry f)) (R : ℝ) (hR : 0 ≤ R) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ s, |s - t₀| ≤ R → ‖f s x₀‖ ≤ M := by
  have hfx : Continuous (fun s => f s x₀) := by
    change Continuous (Function.uncurry f ∘ fun s => (s, x₀))
    exact hfcont.comp (continuous_id.prodMk continuous_const)
  obtain ⟨M, hM⟩ :=
    (isCompact_closedBall t₀ R).exists_bound_of_continuousOn hfx.continuousOn
  refine ⟨M, (norm_nonneg (f t₀ x₀)).trans (hM t₀ (Metric.mem_closedBall_self hR)), ?_⟩
  intro s hs
  apply hM s
  rw [Metric.mem_closedBall, Real.dist_eq]
  exact hs

private theorem picard_majorant_summable (M K R : ℝ) :
    Summable (fun n => M * R * (K * R) ^ n / (Nat.factorial n : ℝ)) := by
  simpa only [mul_div_assoc] using
    (Real.summable_pow_div_factorial (K * R)).mul_left (M * R)

private theorem picard_estimate_le_majorant
    (M K R r : ℝ) (hM : 0 ≤ M) (hK : 0 ≤ K) (hR : 0 ≤ R) (hr : |r| ≤ R) (n : ℕ) :
    M * K ^ n * |r| ^ (n + 1) / (Nat.factorial (n + 1) : ℝ) ≤
      M * R * (K * R) ^ n / (Nat.factorial n : ℝ) := by
  calc
    M * K ^ n * |r| ^ (n + 1) / (Nat.factorial (n + 1) : ℝ) ≤
        M * K ^ n * R ^ (n + 1) / (Nat.factorial (n + 1) : ℝ) := by
      gcongr
    _ ≤ M * K ^ n * R ^ (n + 1) / (Nat.factorial n : ℝ) := by
      apply div_le_div_of_nonneg_left (by positivity) (by positivity)
      exact_mod_cast Nat.factorial_le (Nat.le_succ n)
    _ = M * R * (K * R) ^ n / (Nat.factorial n : ℝ) := by ring

private theorem picard_tendstoUniformlyOn_ball
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (f : ℝ → E → E) (t₀ : ℝ) (x₀ : E) (L : NNReal)
    (hfcont : Continuous (Function.uncurry f))
    (hlip : ∀ t, LipschitzWith L (f t))
    (u : ℕ → ℝ → E) (hu0 : u 0 = fun _ => x₀)
    (hu : ∀ n t, u (n + 1) t = x₀ + ∫ s in t₀..t, f s (u n s))
    (R : ℝ) (hR : 0 ≤ R) :
    TendstoUniformlyOn u
      (fun t => x₀ + ∑' n, (u (n + 1) t - u n t)) Filter.atTop
      (Metric.closedBall t₀ R) := by
  obtain ⟨M, hM0, hM⟩ := picard_exists_bound_on_ball f t₀ x₀ hfcont R hR
  have hstep := picard_step_estimate_on_ball f t₀ x₀ L hfcont hlip u hu0 hu
    R M hR hM
  have hseries : TendstoUniformlyOn
      (fun N t => ∑ n ∈ Finset.range N, (u (n + 1) t - u n t))
      (fun t => ∑' n, (u (n + 1) t - u n t)) Filter.atTop
      (Metric.closedBall t₀ R) := by
    apply tendstoUniformlyOn_tsum_nat (picard_majorant_summable M L R)
    intro n t ht
    have htR : |t - t₀| ≤ R := by
      simpa only [Metric.mem_closedBall, Real.dist_eq] using ht
    exact (hstep n t htR).trans
      (picard_estimate_le_majorant M L R (t - t₀) hM0 L.coe_nonneg hR htR n)
  have hadd : TendstoUniformlyOn
      (fun N t => x₀ + ∑ n ∈ Finset.range N, (u (n + 1) t - u n t))
      (fun t => x₀ + ∑' n, (u (n + 1) t - u n t)) Filter.atTop
      (Metric.closedBall t₀ R) := by
    simpa only [Function.comp_def, vadd_eq_add] using
      (uniformContinuous_const_vadd x₀).comp_tendstoUniformlyOn hseries
  apply hadd.congr
  filter_upwards [] with N t ht
  change x₀ + ∑ n ∈ Finset.range N, (u (n + 1) t - u n t) = u N t
  have htel : ∑ n ∈ Finset.range N, (u (n + 1) t - u n t) = u N t - u 0 t :=
    Finset.sum_range_sub (fun n => u n t) N
  rw [htel, congrFun hu0 t]
  abel

private theorem picard_limit_continuous
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (f : ℝ → E → E) (t₀ : ℝ) (x₀ : E) (L : NNReal)
    (hfcont : Continuous (Function.uncurry f))
    (hlip : ∀ t, LipschitzWith L (f t))
    (u : ℕ → ℝ → E) (hu0 : u 0 = fun _ => x₀)
    (hu : ∀ n t, u (n + 1) t = x₀ + ∫ s in t₀..t, f s (u n s)) :
    Continuous (fun t => x₀ + ∑' n, (u (n + 1) t - u n t)) := by
  rw [continuous_iff_continuousAt]
  intro t
  let R := |t - t₀| + 1
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hconv := picard_tendstoUniformlyOn_ball f t₀ x₀ L hfcont hlip u hu0 hu R hR
  have hcontOn := hconv.continuousOn (Filter.Frequently.of_forall fun n =>
    (picard_iterate_continuous f t₀ x₀ hfcont u hu0 hu n).continuousOn)
  apply hcontOn.continuousAt
  apply Metric.closedBall_mem_nhds_of_mem
  rw [Metric.mem_ball, Real.dist_eq]
  dsimp [R]
  linarith

private theorem picard_integrands_tendstoUniformlyOn
    {E : Type*} [NormedAddCommGroup E]
    (f : ℝ → E → E) (L : NNReal) (hlip : ∀ t, LipschitzWith L (f t))
    (u : ℕ → ℝ → E) (x : ℝ → E) (s : Set ℝ)
    (hconv : TendstoUniformlyOn u x Filter.atTop s) :
    TendstoUniformlyOn (fun n t => f t (u n t)) (fun t => f t (x t))
      Filter.atTop s := by
  rw [Metric.tendstoUniformlyOn_iff] at hconv ⊢
  intro ε hε
  filter_upwards [hconv (ε / ((L : ℝ) + 1)) (by positivity)] with n hn t ht
  calc
    dist (f t (x t)) (f t (u n t)) ≤ (L : ℝ) * dist (x t) (u n t) :=
      (hlip t).dist_le_mul _ _
    _ ≤ ((L : ℝ) + 1) * dist (x t) (u n t) := by
      gcongr
      norm_num
    _ < ((L : ℝ) + 1) * (ε / ((L : ℝ) + 1)) :=
      mul_lt_mul_of_pos_left (hn t ht) (by positivity)
    _ = ε := by field_simp

/-- **Picard iterates converge.** Let $E$ be a real Banach space, let
$f : \mathbb{R} \times E \to E$ be continuous, and let $L \ge 0$ be such that $f(t, \cdot)$ is
$L$-Lipschitz for every $t \in \mathbb{R}$. Fix $t_0 \in \mathbb{R}$ and $x_0 \in E$, and let
$(u_n)_{n \ge 0}$ be maps $\mathbb{R} \to E$ with $u_0(t) = x_0$ and
$u_{n+1}(t) = x_0 + \int_{t_0}^{t} f(s, u_n(s))\,ds$ for all $n$ and $t$. Then there is a map
$x : \mathbb{R} \to E$ with $x(t_0) = x_0$ and $x'(t) = f(t, x(t))$ for every $t \in \mathbb{R}$,
such that $u_n(t) \to x(t)$ as $n \to \infty$ for every $t \in \mathbb{R}$.

Proof: Sum the factorially bounded successive differences, obtaining locally uniform convergence
on every compact time interval. Pass the recursion through the integral and apply the fundamental
theorem of calculus. This is the argument of Teschl, Theorem 2.5 and Corollary 2.6 (Section 2.3),
for the Picard iterates (2.13) of Section 2.2, with a constant global Lipschitz constant.

Proves `Wanted` entry `picard_iterates_converge`.

Sources: `Mathlib/docs/undergrad.yaml`, section `Numerical Analysis` /
`Iterative methods of solving systems of real and vector-valued equations`,
entry `Picard method` (unmapped);
G. Teschl, Ordinary Differential Equations and Dynamical Systems, Section 2.3;
stable ref https://en.wikipedia.org/wiki/Picard%E2%80%93Lindel%C3%B6f_theorem.
-/
theorem picard_iterates_converge
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (f : ℝ → E → E) (t₀ : ℝ) (x₀ : E) (L : NNReal)
    (hfcont : Continuous (Function.uncurry f))
    (hlip : ∀ t, LipschitzWith L (f t))
    (u : ℕ → ℝ → E) (hu0 : u 0 = fun _ => x₀)
    (hu : ∀ n t, u (n + 1) t = x₀ + ∫ s in t₀..t, f s (u n s)) :
    ∃ x : ℝ → E, x t₀ = x₀ ∧ (∀ t, HasDerivAt x (f t (x t)) t) ∧
      ∀ t, Filter.Tendsto (fun n => u n t) Filter.atTop (nhds (x t)) := by
  let x : ℝ → E := fun t => x₀ + ∑' n, (u (n + 1) t - u n t)
  have hucont := picard_iterate_continuous f t₀ x₀ hfcont u hu0 hu
  have hcomp (n : ℕ) : Continuous (fun s => f s (u n s)) := by
    change Continuous (Function.uncurry f ∘ fun s => (s, u n s))
    exact hfcont.comp (continuous_id.prodMk (hucont n))
  have hconv_ball (R : ℝ) (hR : 0 ≤ R) :
      TendstoUniformlyOn u x Filter.atTop (Metric.closedBall t₀ R) := by
    simpa only [x] using
      picard_tendstoUniformlyOn_ball f t₀ x₀ L hfcont hlip u hu0 hu R hR
  have hconv (t : ℝ) : Filter.Tendsto (fun n => u n t) Filter.atTop (nhds (x t)) := by
    apply (hconv_ball |t - t₀| (abs_nonneg _)).tendsto_at
    rw [Metric.mem_closedBall, Real.dist_eq]
  have hxcont : Continuous x := by
    simpa only [x] using picard_limit_continuous f t₀ x₀ L hfcont hlip u hu0 hu
  have heq (t : ℝ) : x t = x₀ + ∫ s in t₀..t, f s (x s) := by
    have hsub : Set.uIcc t₀ t ⊆ Metric.closedBall t₀ |t - t₀| := by
      intro s hs
      rw [Metric.mem_closedBall, Real.dist_eq]
      exact Set.abs_sub_left_of_mem_uIcc hs
    have hconvIcc := (hconv_ball |t - t₀| (abs_nonneg _)).mono hsub
    have hconvf := picard_integrands_tendstoUniformlyOn f L hlip u x (Set.uIcc t₀ t) hconvIcc
    have hint := hconvf.tendsto_intervalIntegral_of_continuousOn (μ := volume)
      (Filter.Eventually.of_forall fun n => (hcomp n).continuousOn)
    have hleft : Filter.Tendsto (fun n => u (n + 1) t) Filter.atTop (nhds (x t)) :=
      (Filter.tendsto_add_atTop_iff_nat 1).2 (hconvIcc.tendsto_at (by simp))
    have hright : Filter.Tendsto (fun n => u (n + 1) t) Filter.atTop
        (nhds (x₀ + ∫ s in t₀..t, f s (x s))) := by
      apply (tendsto_const_nhds.add hint).congr'
      filter_upwards [] with n
      exact (hu n t).symm
    exact tendsto_nhds_unique hleft hright
  have hfx : Continuous (fun t => f t (x t)) := by
    change Continuous (Function.uncurry f ∘ fun t => (t, x t))
    exact hfcont.comp (continuous_id.prodMk hxcont)
  have hderiv (t : ℝ) : HasDerivAt x (f t (x t)) t := by
    have hprim := (intervalIntegral.integral_hasDerivAt_right
      (hfx.intervalIntegrable t₀ t)
      hfx.aestronglyMeasurable.stronglyMeasurableAtFilter hfx.continuousAt).const_add x₀
    apply hprim.congr_of_eventuallyEq
    exact Filter.Eventually.of_forall heq
  refine ⟨x, ?_, hderiv, hconv⟩
  simpa using heq t₀

/-- **Picard iterates converge to every global solution of the initial value problem.** Let $E$
be a real Banach space, let $f : \mathbb{R} \times E \to E$ be continuous, and let $L \ge 0$ be
such that $f(t, \cdot)$ is $L$-Lipschitz for every $t \in \mathbb{R}$. Fix $t_0 \in \mathbb{R}$
and $x_0 \in E$, and let $(u_n)_{n \ge 0}$ be maps $\mathbb{R} \to E$ with $u_0(t) = x_0$ and
$u_{n+1}(t) = x_0 + \int_{t_0}^{t} f(s, u_n(s))\,ds$ for all $n$ and $t$. If $y : \mathbb{R} \to E$
satisfies $y(t_0) = x_0$ and $y'(t) = f(t, y(t))$ for every $t \in \mathbb{R}$, then
$u_n(t) \to y(t)$ as $n \to \infty$ for every $t \in \mathbb{R}$.

Proof: By the convergence of Picard iterates, the iterates converge pointwise to a global solution
through $x_0$ at $t_0$; by uniqueness of solutions for a Lipschitz right-hand side, it equals $y$.
-/
theorem picard_iterates_tendsto_of_hasDerivAt
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (f : ℝ → E → E) (t₀ : ℝ) (x₀ : E) (L : NNReal)
    (hfcont : Continuous (Function.uncurry f))
    (hlip : ∀ t, LipschitzWith L (f t))
    (u : ℕ → ℝ → E) (hu0 : u 0 = fun _ => x₀)
    (hu : ∀ n t, u (n + 1) t = x₀ + ∫ s in t₀..t, f s (u n s))
    (y : ℝ → E) (hy₀ : y t₀ = x₀) (hy : ∀ t, HasDerivAt y (f t (y t)) t) :
    ∀ t, Filter.Tendsto (fun n => u n t) Filter.atTop (nhds (y t)) := by
  obtain ⟨x, hx₀, hx, hconv⟩ :=
    picard_iterates_converge f t₀ x₀ L hfcont hlip u hu0 hu
  have hxy : x = y := ODE_solution_unique_univ
    (s := fun _ => Set.univ) (fun t => (hlip t).lipschitzOnWith)
    (fun t => ⟨hx t, Set.mem_univ _⟩) (fun t => ⟨hy t, Set.mem_univ _⟩)
    (hx₀.trans hy₀.symm)
  simpa only [hxy] using hconv

/-- **Step estimate for Picard iterates.** Let $E$ be a real normed space, let
$f : \mathbb{R} \times E \to E$ be continuous, and let $L \ge 0$ be such that $f(t, \cdot)$ is
$L$-Lipschitz for every $t \in \mathbb{R}$. Fix $t_0 \in \mathbb{R}$ and $x_0 \in E$, and let
$(u_n)_{n \ge 0}$ be maps $\mathbb{R} \to E$ with $u_0(t) = x_0$ and
$u_{n+1}(t) = x_0 + \int_{t_0}^{t} f(s, u_n(s))\,ds$ for all $n$ and $t$. If $M$ is a real number
with $\|f(s, x_0)\| \le M$ for every $s \in \mathbb{R}$, then for every $n \ge 0$ and every
$t \in \mathbb{R}$, $\|u_{n+1}(t) - u_n(t)\| \le M L^n |t - t_0|^{n+1} / (n+1)!$.

The integral is the Bochner integral, which is taken to be $0$ when $E$ is not complete.

Proof: Induct on the iterate index, apply the Lipschitz bound under the interval integral, and
integrate the absolute-power majorant exactly, as in the induction for estimate (2.29) in the proof
of Teschl, Theorem 2.5 (Section 2.3).

Proves `Wanted` entry `picard_iterates_step_estimate`.

Sources: `Mathlib/docs/undergrad.yaml`, section `Numerical Analysis` /
`Iterative methods of solving systems of real and vector-valued equations`,
entries `Picard method` and `rate of convergence and estimation of error`
(unmapped); G. Teschl, Ordinary Differential Equations and Dynamical Systems,
Section 2.3.
-/
theorem picard_iterates_step_estimate
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℝ → E → E) (t₀ : ℝ) (x₀ : E) (L : NNReal)
    (hfcont : Continuous (Function.uncurry f))
    (hlip : ∀ t, LipschitzWith L (f t))
    (u : ℕ → ℝ → E) (hu0 : u 0 = fun _ => x₀)
    (hu : ∀ n t, u (n + 1) t = x₀ + ∫ s in t₀..t, f s (u n s))
    (M : ℝ) (hM : ∀ s, ‖f s x₀‖ ≤ M) :
    ∀ n t, ‖u (n + 1) t - u n t‖ ≤
      M * (L : ℝ) ^ n * |t - t₀| ^ (n + 1) / (Nat.factorial (n + 1) : ℝ) := by
  intro n t
  exact picard_step_estimate_on_ball f t₀ x₀ L hfcont hlip u hu0 hu |t - t₀| M
    (abs_nonneg _) (fun s _ => hM s) n t le_rfl

end MathlibExt.Analysis.ODE.PicardIterationWanted

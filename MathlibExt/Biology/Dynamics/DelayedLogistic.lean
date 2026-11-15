/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Biology.Dynamics.Logistic
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Topology.Order.IntermediateValue

/-!
# The Hutchinson delayed logistic equation

Hutchinson's delayed logistic equation is the delay differential equation

  `x'(t) = r x(t) (1 - x(t - τ) / K)`,  `t ≥ 0`,

with growth rate `r`, carrying capacity `K`, delay `τ ≥ 0` and history (initial data)
`x(t) = φ(t)` for `t ∈ [-τ, 0]`. A solution (`IsSolution`) is a function continuous on
`[-τ, ∞)`, equal to `φ` on `[-τ, 0]`, with right derivative given by the equation at every
`t ≥ 0`.

## Main results

Well-posedness.
* `IsSolution.eq_mul_exp_integral`: every solution satisfies
  `x(t) = x(0) exp (r ∫₀ᵗ (1 - x(s - τ) / K) ds)` for `t ≥ 0`.
* `IsSolution.pos`: positive history value `φ 0 > 0` gives `x(t) > 0` for all `t ≥ 0`.
* `isSolution_solution`, `exists_isSolution`: global existence for `τ > 0` and every history
  continuous on `[-τ, 0]` (method of steps; all real `r`, `K`).
* `IsSolution.eqOn`: uniqueness on `[-τ, ∞)` for `τ > 0`.
* `isSolution_logistic`, `IsSolution.eqOn_logistic`: for `τ = 0` the equation is the logistic
  ODE and its unique solution is `Logistic.logistic`.
* `exists_isSolution_pos`: global existence of a positive solution for every `τ ≥ 0`
  (`r ≥ 0`, `K > 0`, positive continuous history).

Linearized stability of the positive equilibrium `K`.
* `const_isSolution_iff`: the constant solutions are exactly `0` and `K`.
* `IsSolution.hasDerivWithinAt_deviation`: the relative deviation `u = x / K - 1` satisfies
  `u'(t) = -r u(t - τ) (1 + u(t))`, whose linear part is `u'(t) = -r u(t - τ)`.
* `charFun`, `hasDerivAt_cexp_iff_charFun_eq_zero`: `t ↦ e^{z t}` solves the linearized
  equation iff `z` is a root of the characteristic function `z + r e^{-z τ}`.
* `re_neg_of_charFun_eq_zero`: for `0 ≤ τ < τ_c = π / (2 r)` every characteristic root has
  negative real part (linearized asymptotic stability).
* `re_nonpos_of_charFun_eq_zero`, `charFun_criticalDelay_I_mul`: at `τ = τ_c` all roots have
  nonpositive real part and `± i r` are roots (loss of stability through a purely imaginary
  pair).
* `exists_charFun_eq_zero_re_pos`: for `τ > τ_c` there is a root with positive real part
  (linearized instability).
* `exists_linearized_oscillation`: for `τ > τ_c` the linearized equation has a real solution
  oscillating about `0` with unbounded amplitude.

Local asymptotic stability of the nonlinear equation.
* `IsSolution.isWrightSolution_log`: `y = log (x / K)` solves Wright's equation
  `y'(t) = -r (e^{y(t - τ)} - 1)`.
* `IsWrightSolution.abs_le_step`: the Razumikhin-type window contraction
  `|y t| ≤ ρ(rτ, M) M` from `|y| ≤ M` on `[t - 3τ, t - τ]`.
* `IsWrightSolution.abs_le_of_initial`, `IsWrightSolution.abs_le_pow`,
  `IsWrightSolution.tendsto_zero`: stability, geometric decay and attractivity of Wright's
  equation when `ρ(rτ, M) < 1`.
* `localAsymptoticStability`: for `r, K, τ > 0` with `r τ < √5 - 1`, the equilibrium `K` of the
  nonlinear delayed logistic equation is locally asymptotically stable.
* `sqrt_five_sub_one_div_lt_criticalDelay`: this range `τ < (√5 - 1) / r` lies strictly inside
  `τ < τ_c`.

## Scope

The characteristic-root results are *linearized* statements about `u' = -r u(t - τ)`.
Local asymptotic stability of the nonlinear equation is proved directly, by a Razumikhin-type
window estimate on Wright's form, for `0 < r τ < √5 - 1 ≈ 1.236`. `√5 - 1` is where this
one-window estimate stops (`|1 - a| + a² / 2 < 1`), not the limit of the method: Yorke-type
refinements reach `r τ < 3 / 2` (Yorke 1970; Wright 1955), and `3 / 2` is the best possible
bound for any estimate that also holds with time-varying coefficients. Only
`3 / 2 ≤ r τ < π / 2` needs the principle of linearized stability for delay equations
(variation of constants and exponential decay of the fundamental solution). Neither the
refinement to `3 / 2` nor that principle is formalized here, so `√5 - 1 ≤ r τ < π / 2` is not
covered. The Hopf normal form at `τ_c` is not formalized either.

## References

* G. E. Hutchinson, *Circular causal systems in ecology*, Ann. N. Y. Acad. Sci. 50 (1948)
  221–246.
* J. K. Hale, S. M. Verduyn Lunel, *Introduction to Functional Differential Equations*,
  Springer (1993), §5.2 (method of steps) and §11.4.
* H. Smith, *An Introduction to Delay Differential Equations with Applications to the Life
  Sciences*, Springer (2011), §3.4 and §4.4.
* E. M. Wright, *A non-linear difference-differential equation*, J. Reine Angew. Math. 194
  (1955) 66–87.
* J. A. Yorke, *Asymptotic stability for one dimensional differential-delay equations*,
  J. Differential Equations 7 (1970) 189–202.
* B. S. Razumikhin, *On the stability of systems with a delay*, Prikl. Mat. Mekh. 20 (1956)
  500–512.
-/

@[expose] public section

open Real Filter Set
open scoped Topology

namespace MathlibExt.Biology.Dynamics.DelayedLogistic

/-! ### Solutions -/

/-- `x` solves Hutchinson's delayed logistic equation `x'(t) = r x(t) (1 - x(t - τ) / K)` with
history `φ` on `[-τ, 0]`: `x = φ` on `[-τ, 0]`, `x` is continuous on `[-τ, ∞)`, and at every
`t ≥ 0` the right derivative of `x` is `r x(t) (1 - x(t - τ) / K)`. -/
structure IsSolution (r K τ : ℝ) (φ x : ℝ → ℝ) : Prop where
  eqOn_history : EqOn x φ (Icc (-τ) 0)
  continuousOn : ContinuousOn x (Ici (-τ))
  hasDerivWithinAt : ∀ t, 0 ≤ t →
    HasDerivWithinAt x (r * x t * (1 - x (t - τ) / K)) (Ici t) t

/-- **Integral representation**: a solution satisfies
`x(t) = x(0) exp (r ∫₀ᵗ (1 - x(s - τ) / K) ds)` for every `t ≥ 0`. -/
theorem IsSolution.eq_mul_exp_integral {r K τ : ℝ} {φ x : ℝ → ℝ} (hτ : 0 ≤ τ)
    (hx : IsSolution r K τ φ x) {t : ℝ} (ht : 0 ≤ t) :
    x t = x 0 * exp (r * ∫ s in (0 : ℝ)..t, (1 - x (s - τ) / K)) := by
  set g : ℝ → ℝ := fun s => 1 - x (max s 0 - τ) / K with hg
  have hgc : Continuous g := by
    have h1 : Continuous fun s : ℝ => max s 0 - τ := by fun_prop
    have h2 : ContinuousOn (fun y => 1 - x y / K) (Ici (-τ)) :=
      continuousOn_const.sub (hx.continuousOn.div_const K)
    exact h2.comp_continuous h1 fun s => by simp
  have hint : ∀ u, 0 ≤ u →
      ∫ s in (0 : ℝ)..u, (1 - x (s - τ) / K) = ∫ s in (0 : ℝ)..u, g s := by
    intro u hu
    refine intervalIntegral.integral_congr fun s hs => ?_
    rw [uIcc_of_le hu] at hs
    simp [hg, max_eq_left hs.1]
  set G : ℝ → ℝ := fun u => ∫ s in (0 : ℝ)..u, g s with hGdef
  have hG : ∀ u, HasDerivAt G (g u) u := fun u => (hgc.integral_hasStrictDerivAt 0 u).hasDerivAt
  set h : ℝ → ℝ := fun u => x u * exp (-(r * G u)) with hh
  have hcont : ContinuousOn h (Icc 0 t) := by
    refine (hx.continuousOn.mono fun u hu => ?_).mul ?_
    · simp only [mem_Ici, mem_Icc] at hu ⊢; linarith [hu.1]
    · exact (continuous_iff_continuousAt.2 fun u => ((hG u).const_mul r).neg.exp.continuousAt)
        |>.continuousOn
  have hderiv : ∀ u ∈ Ico 0 t, HasDerivWithinAt h 0 (Ici u) u := by
    intro u hu
    have h1 := hx.hasDerivWithinAt u hu.1
    have h2 := ((hG u).const_mul r).neg.exp
    convert h1.mul h2.hasDerivWithinAt using 1
    simp only [hg, max_eq_left hu.1]
    ring
  have hconst := constant_of_has_deriv_right_zero hcont hderiv t ⟨ht, le_rfl⟩
  simp only [hh, hGdef, intervalIntegral.integral_same, mul_zero, neg_zero, exp_zero,
    mul_one] at hconst
  rw [hint t ht, ← hconst, mul_assoc, ← exp_add]
  simp

/-- **Positivity**: a solution with positive history value `φ 0` stays positive for `t ≥ 0`. -/
theorem IsSolution.pos {r K τ : ℝ} {φ x : ℝ → ℝ} (hτ : 0 ≤ τ) (hx : IsSolution r K τ φ x)
    (hφ0 : 0 < φ 0) {t : ℝ} (ht : 0 ≤ t) : 0 < x t := by
  rw [hx.eq_mul_exp_integral hτ ht, hx.eqOn_history ⟨by linarith, le_rfl⟩]
  positivity

/-- **Uniqueness** for a positive delay: two solutions with the same history agree on
`[-τ, ∞)`. -/
theorem IsSolution.eqOn {r K τ : ℝ} {φ x y : ℝ → ℝ} (hτ : 0 < τ) (hx : IsSolution r K τ φ x)
    (hy : IsSolution r K τ φ y) : EqOn x y (Ici (-τ)) := by
  have key : ∀ n : ℕ, ∀ t ∈ Icc (-τ) (n * τ), x t = y t := by
    intro n
    induction n with
    | zero =>
      intro t ht
      rw [Nat.cast_zero, zero_mul] at ht
      rw [hx.eqOn_history ht, hy.eqOn_history ht]
    | succ n ih =>
      intro t ht
      by_cases htn : t ≤ n * τ
      · exact ih t ⟨ht.1, htn⟩
      push Not at htn
      have ht0 : 0 ≤ t := le_trans (by positivity) htn.le
      have h0 : (0 : ℝ) ∈ Icc (-τ) 0 := ⟨by linarith, le_rfl⟩
      rw [hx.eq_mul_exp_integral hτ.le ht0, hy.eq_mul_exp_integral hτ.le ht0,
        hx.eqOn_history h0, hy.eqOn_history h0]
      congr 3
      refine intervalIntegral.integral_congr fun s hs => ?_
      rw [uIcc_of_le ht0] at hs
      have hn : t ≤ (n + 1 : ℕ) * τ := ht.2
      push_cast at hn
      rw [ih (s - τ) ⟨by linarith [hs.1], by linarith [hs.2]⟩]
  intro t ht
  obtain ⟨n, hn⟩ := exists_nat_ge (t / τ)
  exact key n t ⟨ht, by rwa [div_le_iff₀ hτ] at hn⟩

/-! ### Existence by the method of steps -/

/-- One step of the method of steps: given the history extension `ψ` and a candidate `x`, the
function equal to `ψ` on `(-∞, 0]` and to `ψ(0) exp (r ∫₀ᵗ (1 - x(s - τ) / K) ds)` for
`t > 0`. A solution is a fixed point; on `[0, τ]` the right side only uses the history. -/
noncomputable def stepMap (r K τ : ℝ) (ψ x : ℝ → ℝ) : ℝ → ℝ := fun t =>
  if t ≤ 0 then ψ t else ψ 0 * exp (r * ∫ s in (0 : ℝ)..t, (1 - x (s - τ) / K))

/-- The `n`-th iterate of `stepMap` started at the history; it is exact on `(-∞, n τ]`. -/
noncomputable def stepIter (r K τ : ℝ) (ψ : ℝ → ℝ) (n : ℕ) : ℝ → ℝ :=
  (stepMap r K τ ψ)^[n] ψ

/-- Continuous extension of a history given on `[-τ, 0]` to the whole line (constant outside). -/
noncomputable def historyExt (τ : ℝ) (φ : ℝ → ℝ) : ℝ → ℝ := fun t => φ (max (-τ) (min t 0))

/-- The solution of the delayed logistic equation built by the method of steps from the
history `φ` on `[-τ, 0]` (meaningful for `τ > 0`). -/
noncomputable def solution (r K τ : ℝ) (φ : ℝ → ℝ) : ℝ → ℝ := fun t =>
  stepIter r K τ (historyExt τ φ) ⌈t / τ⌉₊ t

theorem stepMap_of_le {r K τ : ℝ} {ψ x : ℝ → ℝ} {t : ℝ} (ht : t ≤ 0) :
    stepMap r K τ ψ x t = ψ t := by
  simp [stepMap, ht]

theorem stepMap_of_nonneg {r K τ : ℝ} {ψ x : ℝ → ℝ} {t : ℝ} (ht : 0 ≤ t) :
    stepMap r K τ ψ x t = ψ 0 * exp (r * ∫ s in (0 : ℝ)..t, (1 - x (s - τ) / K)) := by
  rcases ht.eq_or_lt with rfl | ht
  · simp [stepMap]
  · simp [stepMap, not_le.2 ht]

/-- `stepMap x` on `(-∞, a + τ]` depends only on `x` on `(-∞, a]`. -/
theorem stepMap_congr {r K τ a : ℝ} {ψ x y : ℝ → ℝ} (hxy : ∀ s ≤ a, x s = y s) {t : ℝ}
    (ht : t ≤ a + τ) : stepMap r K τ ψ x t = stepMap r K τ ψ y t := by
  by_cases ht0 : t ≤ 0
  · simp [stepMap, ht0]
  push Not at ht0
  rw [stepMap_of_nonneg ht0.le, stepMap_of_nonneg ht0.le]
  congr 3
  refine intervalIntegral.integral_congr fun s hs => ?_
  rw [uIcc_of_le ht0.le] at hs
  rw [hxy (s - τ) (by linarith [hs.2])]

theorem stepIter_succ_eq {r K τ : ℝ} {ψ : ℝ → ℝ} (n : ℕ) :
    stepIter r K τ ψ (n + 1) = stepMap r K τ ψ (stepIter r K τ ψ n) :=
  Function.iterate_succ_apply' _ _ _

theorem stepIter_succ_agree {r K τ : ℝ} {ψ : ℝ → ℝ} (n : ℕ) :
    ∀ s ≤ n * τ, stepIter r K τ ψ (n + 1) s = stepIter r K τ ψ n s := by
  induction n with
  | zero =>
    intro s hs
    rw [Nat.cast_zero, zero_mul] at hs
    rw [stepIter_succ_eq, stepMap_of_le hs]
    rfl
  | succ n ih =>
    intro s hs
    have hs' : s ≤ (n : ℝ) * τ + τ := by
      have := hs
      push_cast at this
      linarith
    rw [stepIter_succ_eq (n + 1)]
    conv_rhs => rw [stepIter_succ_eq n]
    exact stepMap_congr (a := n * τ) ih hs'

theorem stepIter_agree_of_le {r K τ : ℝ} (hτ : 0 ≤ τ) {ψ : ℝ → ℝ} {n m : ℕ} (hnm : n ≤ m) :
    ∀ s ≤ n * τ, stepIter r K τ ψ m s = stepIter r K τ ψ n s := by
  induction m, hnm using Nat.le_induction with
  | base => exact fun s _ => rfl
  | succ m hnm ih =>
    intro s hs
    have hmn : (n : ℝ) * τ ≤ m * τ := by gcongr
    rw [stepIter_succ_agree m s (hs.trans hmn), ih s hs]

theorem solution_eq_stepIter {r K τ : ℝ} (hτ : 0 < τ) {φ : ℝ → ℝ} {n : ℕ} {t : ℝ}
    (ht : t ≤ n * τ) : solution r K τ φ t = stepIter r K τ (historyExt τ φ) n t := by
  have hN : t ≤ (⌈t / τ⌉₊ : ℝ) * τ := by
    rw [← div_le_iff₀ hτ]; exact Nat.le_ceil _
  simp only [solution]
  rw [← stepIter_agree_of_le hτ.le (le_max_left _ n) t hN,
    stepIter_agree_of_le hτ.le (le_max_right _ n) t ht]

theorem continuous_stepMap {r K τ : ℝ} {ψ x : ℝ → ℝ} (hψ : Continuous ψ) (hx : Continuous x) :
    Continuous (stepMap r K τ ψ x) := by
  have hg : Continuous fun s => 1 - x (s - τ) / K := by fun_prop
  have hG : Continuous fun t => ∫ s in (0 : ℝ)..t, (1 - x (s - τ) / K) :=
    intervalIntegral.continuous_primitive (fun a b => hg.intervalIntegrable a b) 0
  refine Continuous.if_le hψ (continuous_const.mul (continuous_const.mul hG).rexp)
    continuous_id continuous_const fun t ht => ?_
  simp [ht]

theorem continuous_stepIter {r K τ : ℝ} {ψ : ℝ → ℝ} (hψ : Continuous ψ) (n : ℕ) :
    Continuous (stepIter r K τ ψ n) := by
  induction n with
  | zero => exact hψ
  | succ n ih => rw [stepIter_succ_eq]; exact continuous_stepMap hψ ih

theorem continuous_historyExt {τ : ℝ} (hτ : 0 ≤ τ) {φ : ℝ → ℝ}
    (hφ : ContinuousOn φ (Icc (-τ) 0)) : Continuous (historyExt τ φ) :=
  hφ.comp_continuous (by fun_prop) fun t =>
    ⟨le_max_left _ _, max_le (by linarith) (min_le_right _ _)⟩

theorem historyExt_eqOn {τ : ℝ} {φ : ℝ → ℝ} : EqOn (historyExt τ φ) φ (Icc (-τ) 0) := by
  intro t ht
  simp [historyExt, min_eq_left ht.2, max_eq_right ht.1]

theorem continuous_solution {r K τ : ℝ} (hτ : 0 < τ) {φ : ℝ → ℝ}
    (hφ : ContinuousOn φ (Icc (-τ) 0)) : Continuous (solution r K τ φ) := by
  refine continuous_iff_continuousAt.2 fun t => ?_
  obtain ⟨n, hn⟩ := exists_nat_gt (t / τ)
  rw [div_lt_iff₀ hτ] at hn
  refine ContinuousAt.congr
    (continuous_stepIter (r := r) (K := K) (τ := τ) (continuous_historyExt hτ.le hφ) n).continuousAt
    ?_
  filter_upwards [Iio_mem_nhds hn] with s hs
  exact (solution_eq_stepIter hτ (le_of_lt hs)).symm

/-- The constructed solution is a fixed point of the step map. -/
theorem stepMap_solution {r K τ : ℝ} (hτ : 0 < τ) {φ : ℝ → ℝ} :
    stepMap r K τ (historyExt τ φ) (solution r K τ φ) = solution r K τ φ := by
  funext t
  obtain ⟨n, hn⟩ := exists_nat_ge (t / τ)
  rw [div_le_iff₀ hτ] at hn
  have h1 : ∀ s ≤ n * τ, solution r K τ φ s = stepIter r K τ (historyExt τ φ) n s :=
    fun s hs => solution_eq_stepIter hτ hs
  rw [stepMap_congr h1 (by linarith : t ≤ n * τ + τ), ← stepIter_succ_eq,
    solution_eq_stepIter hτ (by push_cast; linarith : t ≤ ((n + 1 : ℕ) : ℝ) * τ)]

/-- **Global existence** (method of steps): for `τ > 0` and a history continuous on `[-τ, 0]`,
`solution r K τ φ` solves the delayed logistic equation on `[-τ, ∞)` (all real `r`, `K`). -/
theorem isSolution_solution {r K τ : ℝ} (hτ : 0 < τ) {φ : ℝ → ℝ}
    (hφ : ContinuousOn φ (Icc (-τ) 0)) : IsSolution r K τ φ (solution r K τ φ) where
  eqOn_history t ht := by
    rw [solution_eq_stepIter hτ (n := 0) (by simpa using ht.2)]
    exact historyExt_eqOn ht
  continuousOn := (continuous_solution hτ hφ).continuousOn
  hasDerivWithinAt t ht := by
    set x := solution r K τ φ
    set ψ := historyExt τ φ
    set g : ℝ → ℝ := fun s => 1 - x (s - τ) / K
    have hgc : Continuous g := by
      have := continuous_solution (r := r) (K := K) hτ hφ
      fun_prop
    set F : ℝ → ℝ := fun u => ψ 0 * exp (r * ∫ s in (0 : ℝ)..u, g s) with hF
    have hFd : HasDerivAt F (F t * (r * g t)) t := by
      have := (((hgc.integral_hasStrictDerivAt 0 t).hasDerivAt.const_mul r).exp).const_mul (ψ 0)
      convert this using 1
      simp only [hF]; ring
    have hxF : EqOn x F (Ici t) := by
      intro u hu
      have hu0 : 0 ≤ u := ht.trans hu
      have hfix := congrFun (stepMap_solution (r := r) (K := K) (φ := φ) hτ) u
      exact hfix.symm.trans (stepMap_of_nonneg hu0)
    have hxt : x t = F t := hxF (mem_Ici.2 le_rfl)
    refine hFd.hasDerivWithinAt.congr hxF hxt |>.congr_deriv ?_
    rw [hxt]; ring

/-- **Global existence** for a positive delay and continuous history. -/
theorem exists_isSolution {r K τ : ℝ} (hτ : 0 < τ) {φ : ℝ → ℝ}
    (hφ : ContinuousOn φ (Icc (-τ) 0)) : ∃ x, IsSolution r K τ φ x :=
  ⟨_, isSolution_solution hτ hφ⟩

/-! ### Zero delay: the logistic ODE -/

/-- For `τ = 0` the logistic solution `Logistic.logistic r K (φ 0)` is a solution
(`r ≥ 0`, `K > 0`, `φ 0 > 0`). -/
theorem isSolution_logistic {r K : ℝ} (hr : 0 ≤ r) (hK : 0 < K) {φ : ℝ → ℝ} (hφ0 : 0 < φ 0) :
    IsSolution r K 0 φ (Logistic.logistic r K (φ 0)) := by
  have hd : ∀ t, 0 ≤ t → HasDerivAt (Logistic.logistic r K (φ 0))
      (r * Logistic.logistic r K (φ 0) t * (1 - Logistic.logistic r K (φ 0) t / K)) t :=
    fun t ht => Logistic.hasDerivAt_logistic hK.ne'
      (Logistic.logistic_denom_pos hK hφ0 (Or.inl (mul_nonneg hr ht))).ne'
  refine ⟨fun t ht => ?_, fun t ht => ?_, fun t ht => ?_⟩
  · have : t = 0 := le_antisymm ht.2 (by simpa using ht.1)
    subst this
    exact Logistic.logistic_zero _ hK.ne'
  · exact (hd t (by simpa using ht)).continuousAt.continuousWithinAt
  · simpa using (hd t ht).hasDerivWithinAt

/-- **Zero delay reduces to the logistic ODE**: for `τ = 0`, every solution equals the
explicit logistic solution on `[0, ∞)`. -/
theorem IsSolution.eqOn_logistic {r K : ℝ} (hr : 0 ≤ r) (hK : 0 < K) {φ x : ℝ → ℝ}
    (hφ0 : 0 < φ 0) (hx : IsSolution r K 0 φ x) :
    EqOn x (Logistic.logistic r K (φ 0)) (Ici 0) := by
  intro t ht
  refine Logistic.eqOn_logistic_of_hasDerivWithinAt hK hφ0 hr
    (hx.continuousOn.mono fun u hu => by simpa using hu.1) (fun u hu => ?_)
    (hx.eqOn_history ⟨by simp, le_rfl⟩) ⟨ht, le_rfl⟩
  simpa using hx.hasDerivWithinAt u hu.1

/-- **Global existence of a positive solution** for every delay `τ ≥ 0`, growth rate
`r ≥ 0`, carrying capacity `K > 0` and continuous history with `φ 0 > 0`. -/
theorem exists_isSolution_pos {r K τ : ℝ} (hτ : 0 ≤ τ) (hr : 0 ≤ r) (hK : 0 < K)
    {φ : ℝ → ℝ} (hφ : ContinuousOn φ (Icc (-τ) 0)) (hφ0 : 0 < φ 0) :
    ∃ x, IsSolution r K τ φ x ∧ ∀ t, 0 ≤ t → 0 < x t := by
  obtain ⟨x, hx⟩ : ∃ x, IsSolution r K τ φ x := by
    rcases hτ.eq_or_lt with rfl | hτ'
    · exact ⟨_, isSolution_logistic hr hK hφ0⟩
    · exact exists_isSolution hτ' hφ
  exact ⟨x, hx, fun t ht => hx.pos hτ hφ0 ht⟩

/-! ### Equilibria and linearization -/

/-- The constant solutions are exactly `0` and the carrying capacity `K` (`r ≠ 0`, `K ≠ 0`). -/
theorem const_isSolution_iff {r K τ c : ℝ} (hr : r ≠ 0) (hK : K ≠ 0) :
    IsSolution r K τ (fun _ => c) (fun _ => c) ↔ c = 0 ∨ c = K := by
  constructor
  · intro h
    have h0 := (uniqueDiffWithinAt_Ici (0 : ℝ)).eq_deriv _ (h.hasDerivWithinAt 0 le_rfl)
      (hasDerivWithinAt_const 0 _ c)
    rcases mul_eq_zero.1 h0 with h1 | h1
    · exact Or.inl ((mul_eq_zero.1 h1).resolve_left hr)
    · right; field_simp at h1; linarith
  · intro h
    refine ⟨fun _ _ => rfl, continuousOn_const, fun t _ => ?_⟩
    convert hasDerivWithinAt_const t (Ici t) c using 1
    rcases h with rfl | rfl
    · ring
    · field_simp; ring

/-- **Deviation equation**: the relative deviation `u = x / K - 1` from the positive
equilibrium satisfies `u'(t) = -r u(t - τ) (1 + u(t))` (right derivative, `t ≥ 0`). Its linear
part is the linearized equation `u'(t) = -r u(t - τ)`. -/
theorem IsSolution.hasDerivWithinAt_deviation {r K τ : ℝ} {φ x : ℝ → ℝ} (hK : K ≠ 0)
    (hx : IsSolution r K τ φ x) {t : ℝ} (ht : 0 ≤ t) :
    HasDerivWithinAt (fun s => x s / K - 1)
      (-(r * (x (t - τ) / K - 1)) * (1 + (x t / K - 1))) (Ici t) t := by
  convert ((hx.hasDerivWithinAt t ht).div_const K).sub_const 1 using 1
  field_simp
  ring

/-- The characteristic function `z + r e^{-z τ}` of the linearized equation
`u'(t) = -r u(t - τ)`. -/
noncomputable def charFun (r τ : ℝ) (z : ℂ) : ℂ := z + r * Complex.exp (-(z * τ))

/-- The critical delay `τ_c = π / (2 r)`. -/
noncomputable def criticalDelay (r : ℝ) : ℝ := π / (2 * r)

/-- Real and imaginary parts of the characteristic equation: with `z = a + b i`,
`a + r e^{-a τ} cos (b τ) = 0` and `b - r e^{-a τ} sin (b τ) = 0`. -/
theorem charFun_eq_zero_iff {r τ : ℝ} {z : ℂ} :
    charFun r τ z = 0 ↔ z.re + r * exp (-(z.re * τ)) * cos (z.im * τ) = 0 ∧
      z.im - r * exp (-(z.re * τ)) * sin (z.im * τ) = 0 := by
  rw [charFun, Complex.ext_iff]
  simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.exp_re, Complex.exp_im, Complex.neg_re, Complex.neg_im,
    Complex.zero_re, Complex.zero_im, mul_zero, zero_mul, sub_zero, add_zero, zero_add,
    cos_neg, sin_neg]
  constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith

/-- **Characteristic equation**: `t ↦ e^{z t}` solves the linearized equation
`u'(t) = -r u(t - τ)` on all of `ℝ` iff `z` is a root of `charFun r τ`. -/
theorem hasDerivAt_cexp_iff_charFun_eq_zero {r τ : ℝ} {z : ℂ} :
    (∀ t : ℝ, HasDerivAt (fun s : ℝ => Complex.exp (z * s))
      (-(r * Complex.exp (z * ↑(t - τ)))) t) ↔ charFun r τ z = 0 := by
  have hd : ∀ t : ℝ, HasDerivAt (fun s : ℝ => Complex.exp (z * s))
      (Complex.exp (z * t) * z) t := fun t => by
    simpa using (((hasDerivAt_id (t : ℂ)).const_mul z).comp_ofReal).cexp
  have hsplit : ∀ t : ℝ, Complex.exp (z * ↑(t - τ)) =
      Complex.exp (z * t) * Complex.exp (-(z * τ)) := fun t => by
    rw [← Complex.exp_add]; push_cast; ring_nf
  constructor
  · intro h
    have := (hd 0).unique (h 0)
    rw [hsplit] at this
    simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero, one_mul] at this
    rw [charFun]
    linear_combination this
  · intro h t
    convert hd t using 1
    rw [hsplit]
    rw [charFun] at h
    linear_combination (-(Complex.exp (z * t))) * h

/-- Auxiliary: a characteristic root with `Re z ≥ 0` has `cos (Im z · τ) ≤ 0` and
`|Im z| ≤ r` (`r > 0`, `τ ≥ 0`). -/
theorem cos_nonpos_and_abs_im_le {r τ : ℝ} {z : ℂ} (hr : 0 < r) (hτ : 0 ≤ τ)
    (hz : charFun r τ z = 0) (hre : 0 ≤ z.re) :
    cos (z.im * τ) ≤ 0 ∧ |z.im| ≤ r := by
  obtain ⟨h1, h2⟩ := charFun_eq_zero_iff.1 hz
  have he : 0 < exp (-(z.re * τ)) := exp_pos _
  have he1 : exp (-(z.re * τ)) ≤ 1 := exp_le_one_iff.2 (by nlinarith)
  refine ⟨?_, ?_⟩
  · by_contra hc
    push Not at hc
    have : 0 < r * exp (-(z.re * τ)) * cos (z.im * τ) := by positivity
    linarith
  · have him : z.im = r * exp (-(z.re * τ)) * sin (z.im * τ) := by linarith
    rw [him, abs_mul, abs_of_pos (by positivity : 0 < r * exp (-(z.re * τ)))]
    calc r * exp (-(z.re * τ)) * |sin (z.im * τ)| ≤ r * 1 * 1 := by
          gcongr
          exact abs_sin_le_one _
      _ = r := by ring

/-- **Linearized asymptotic stability below the critical delay**: for `r > 0` and
`0 ≤ τ < τ_c = π / (2 r)`, every root of the characteristic equation `z + r e^{-z τ} = 0` has
negative real part. -/
theorem re_neg_of_charFun_eq_zero {r τ : ℝ} {z : ℂ} (hr : 0 < r) (hτ : 0 ≤ τ)
    (hτc : τ < criticalDelay r) (hz : charFun r τ z = 0) : z.re < 0 := by
  by_contra hre
  push Not at hre
  obtain ⟨hcos, him⟩ := cos_nonpos_and_abs_im_le hr hτ hz hre
  have hrτ : r * τ < π / 2 := by
    rw [criticalDelay, lt_div_iff₀ (by positivity)] at hτc; linarith
  have hb : |z.im * τ| < π / 2 := by
    rw [abs_mul, abs_of_nonneg hτ]
    calc |z.im| * τ ≤ r * τ := by gcongr
      _ < π / 2 := hrτ
  have := cos_pos_of_mem_Ioo ⟨(abs_lt.1 hb).1, (abs_lt.1 hb).2⟩
  linarith

/-- **At and below the critical delay** every characteristic root has nonpositive real part. -/
theorem re_nonpos_of_charFun_eq_zero {r τ : ℝ} {z : ℂ} (hr : 0 < r) (hτ : 0 ≤ τ)
    (hτc : τ ≤ criticalDelay r) (hz : charFun r τ z = 0) : z.re ≤ 0 := by
  by_contra hre
  push Not at hre
  obtain ⟨hcos, him⟩ := cos_nonpos_and_abs_im_le hr hτ hz hre.le
  have hrτ : r * τ ≤ π / 2 := by
    rw [criticalDelay, le_div_iff₀ (by positivity)] at hτc; linarith
  have hb : |z.im * τ| ≤ π / 2 := by
    rw [abs_mul, abs_of_nonneg hτ]
    calc |z.im| * τ ≤ r * τ := by gcongr
      _ ≤ π / 2 := hrτ
  have hcos' := cos_nonneg_of_mem_Icc ⟨(abs_le.1 hb).1, (abs_le.1 hb).2⟩
  obtain ⟨h1, -⟩ := charFun_eq_zero_iff.1 hz
  have : r * exp (-(z.re * τ)) * cos (z.im * τ) = 0 := by
    have : cos (z.im * τ) = 0 := le_antisymm hcos hcos'
    rw [this, mul_zero]
  linarith

/-- **Loss of stability at the critical delay**: at `τ = τ_c` the purely imaginary number
`i r` is a characteristic root. -/
theorem charFun_criticalDelay_I_mul {r : ℝ} (hr : 0 < r) :
    charFun r (criticalDelay r) (Complex.I * r) = 0 := by
  have hrτ : r * criticalDelay r = π / 2 := by rw [criticalDelay]; field_simp
  rw [charFun_eq_zero_iff]
  simp [hrτ]

/-- The conjugate root `-i r` at the critical delay. -/
theorem charFun_criticalDelay_neg_I_mul {r : ℝ} (hr : 0 < r) :
    charFun r (criticalDelay r) (-(Complex.I * r)) = 0 := by
  have hrτ : r * criticalDelay r = π / 2 := by rw [criticalDelay]; field_simp
  rw [charFun_eq_zero_iff]
  simp [hrτ]

/-- **Linearized instability above the critical delay**: for `r > 0` and `τ > τ_c`, the
characteristic equation has a root with positive real part (and positive imaginary part
below `π / τ`). -/
theorem exists_charFun_eq_zero_re_pos {r τ : ℝ} (hr : 0 < r) (hτc : criticalDelay r < τ) :
    ∃ z : ℂ, charFun r τ z = 0 ∧ 0 < z.re ∧ 0 < z.im ∧ z.im < π / τ := by
  have hτ : 0 < τ := lt_trans (by unfold criticalDelay; positivity) hτc
  have hrτ : π / 2 < r * τ := by
    rw [criticalDelay, div_lt_iff₀ (by positivity)] at hτc; linarith
  -- `f θ = θ e^{-θ cot θ} / sin θ`; a root `θ ∈ (π/2, π)` of `f θ = r τ` gives the eigenvalue.
  set f : ℝ → ℝ := fun θ => θ * exp (-(θ * cos θ / sin θ)) / sin θ with hf
  set δ : ℝ := π / (4 * (r * τ)) with hδ
  have hδpos : 0 < δ := by positivity
  have hδlt : δ < π / 2 := by
    rw [hδ, div_lt_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [pi_pos, two_le_pi]
  set θ₁ := π - δ with hθ₁
  have hsinθ₁ : sin θ₁ = sin δ := by rw [hθ₁, sin_pi_sub]
  have hsinδ : 0 < sin δ := sin_pos_of_pos_of_lt_pi hδpos (by linarith [pi_pos])
  have hsinδ_le : sin δ < δ := sin_lt hδpos
  have hsin_pos : ∀ θ ∈ Icc (π / 2) θ₁, 0 < sin θ := fun θ hθ =>
    sin_pos_of_pos_of_lt_pi (by linarith [hθ.1, pi_pos]) (by linarith [hθ.2])
  have hcont : ContinuousOn f (Icc (π / 2) θ₁) := by
    refine ContinuousOn.div ?_ continuous_sin.continuousOn fun θ hθ => (hsin_pos θ hθ).ne'
    refine continuousOn_id.mul (ContinuousOn.rexp (ContinuousOn.neg ?_))
    exact (continuousOn_id.mul continuous_cos.continuousOn).div continuous_sin.continuousOn
      fun θ hθ => (hsin_pos θ hθ).ne'
  have hfa : f (π / 2) = π / 2 := by simp [hf]
  have hfb : r * τ ≤ f θ₁ := by
    have hcos : cos θ₁ ≤ 0 := by
      rw [hθ₁, cos_pi_sub]; linarith [cos_nonneg_of_mem_Icc ⟨by linarith, hδlt.le⟩]
    have hθ₁pos : π / 2 ≤ θ₁ := by linarith
    have hexp : 1 ≤ exp (-(θ₁ * cos θ₁ / sin θ₁)) := by
      rw [one_le_exp_iff, neg_nonneg]
      exact div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos (by linarith) hcos)
        (hsinθ₁ ▸ hsinδ.le)
    simp only [hf]
    rw [hsinθ₁, le_div_iff₀ hsinδ]
    calc r * τ * sin δ ≤ r * τ * δ := by gcongr
      _ = π / 4 := by rw [hδ]; field_simp
      _ ≤ θ₁ * 1 := by linarith
      _ ≤ θ₁ * exp (-(θ₁ * cos θ₁ / sin δ)) := by
          rw [← hsinθ₁]
          exact mul_le_mul_of_nonneg_left hexp (by linarith [pi_pos])
  obtain ⟨θ, hθ, hfθ⟩ := intermediate_value_Icc (by linarith) hcont
    ⟨hfa.symm ▸ hrτ.le, hfb⟩
  have hθ1 : π / 2 < θ := by
    rcases hθ.1.eq_or_lt with h | h
    · rw [← h, hfa] at hfθ; linarith
    · exact h
  have hθ2 : θ < π := by linarith [hθ.2]
  have hs : 0 < sin θ := sin_pos_of_pos_of_lt_pi (by linarith [pi_pos]) hθ2
  have hc : cos θ < 0 := cos_neg_of_pi_div_two_lt_of_lt hθ1 (by linarith [pi_pos])
  set b : ℝ := θ / τ with hb
  set a : ℝ := -(b * cos θ / sin θ) with ha
  refine ⟨⟨a, b⟩, ?_, ?_, div_pos (by linarith [pi_pos]) hτ, ?_⟩
  · rw [charFun_eq_zero_iff]
    simp only
    have hbτ : b * τ = θ := by rw [hb]; field_simp
    have haτ : -(a * τ) = θ * cos θ / sin θ := by rw [ha, ← hbτ]; ring
    rw [hbτ, haτ]
    -- `f θ = r τ` gives `r e^{θ cot θ} sin θ = θ / τ = b`.
    have hE : r * exp (θ * cos θ / sin θ) * sin θ = b := by
      have h1 : θ * exp (-(θ * cos θ / sin θ)) / sin θ = r * τ := hfθ
      have h2 : exp (-(θ * cos θ / sin θ)) * exp (θ * cos θ / sin θ) = 1 := by
        rw [← exp_add]; simp
      have h1' : θ * exp (-(θ * cos θ / sin θ)) = r * τ * sin θ := by
        rw [div_eq_iff hs.ne'] at h1; linarith
      rw [hb, eq_div_iff hτ.ne']
      calc r * exp (θ * cos θ / sin θ) * sin θ * τ
          = (r * τ * sin θ) * exp (θ * cos θ / sin θ) := by ring
        _ = θ * exp (-(θ * cos θ / sin θ)) * exp (θ * cos θ / sin θ) := by rw [h1']
        _ = θ := by rw [mul_assoc, h2, mul_one]
    constructor
    · have : r * exp (θ * cos θ / sin θ) * cos θ = b * cos θ / sin θ := by
        rw [← hE]; field_simp
      rw [this, ha]; ring
    · linarith
  · rw [ha, neg_pos]
    exact div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg (div_pos (by linarith [pi_pos]) hτ) hc) hs
  · exact div_lt_div_of_pos_right hθ2 hτ

/-- **Growing oscillation of the linearized equation above the critical delay**: for `r > 0`
and `τ > τ_c`, the linearized equation `u'(t) = -r u(t - τ)` has a real solution taking values
`≥ M` and `≤ -M` after every time `T`, for every `M`. -/
theorem exists_linearized_oscillation {r τ : ℝ} (hr : 0 < r) (hτc : criticalDelay r < τ) :
    ∃ u : ℝ → ℝ, (∀ t, HasDerivAt u (-(r * u (t - τ))) t) ∧
      ∀ M T : ℝ, (∃ t ≥ T, M ≤ u t) ∧ ∃ t ≥ T, u t ≤ -M := by
  obtain ⟨z, hz, hre, him, -⟩ := exists_charFun_eq_zero_re_pos hr hτc
  have hd := hasDerivAt_cexp_iff_charFun_eq_zero.2 hz
  set a := z.re
  set b := z.im
  have hu : ∀ t : ℝ, (Complex.exp (z * t)).re = exp (a * t) * cos (b * t) := fun t => by
    simp [Complex.exp_re, a, b]
  refine ⟨fun t => exp (a * t) * cos (b * t), fun t => ?_, fun M T => ?_⟩
  · have := Complex.reCLM.hasFDerivAt.comp_hasDerivAt t (hd t)
    simp only [Function.comp_def, Complex.reCLM_apply] at this
    convert this using 1
    · funext s; rw [hu]
    · rw [Complex.neg_re, Complex.re_ofReal_mul, hu]
  · obtain ⟨k, hk⟩ := exists_nat_ge (b * max T (max (M / a) 0) / (2 * π))
    set t : ℝ := k * (2 * π) / b with ht
    have htge : max T (max (M / a) 0) ≤ t := by
      rw [ht, le_div_iff₀ him]
      rw [div_le_iff₀ (by positivity)] at hk
      linarith
    have hT : T ≤ t := le_trans (le_max_left _ _) htge
    have hM : M ≤ a * t := by
      have := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) htge
      rwa [div_le_iff₀ hre, mul_comm] at this
    have ht0 : 0 ≤ t := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) htge
    have hbt : b * t = k * (2 * π) := by rw [ht]; field_simp
    have hexp : M ≤ exp (a * t) := by linarith [add_one_le_exp (a * t)]
    refine ⟨⟨t, hT, ?_⟩, ⟨t + π / b, by linarith [div_pos pi_pos him], ?_⟩⟩
    · beta_reduce
      rw [hbt, cos_nat_mul_two_pi, mul_one]; exact hexp
    · have hbt' : b * (t + π / b) = k * (2 * π) + π := by
        rw [mul_add, hbt]; field_simp
      beta_reduce
      rw [hbt', cos_nat_mul_two_pi_add_pi, mul_neg_one, neg_le_neg_iff]
      calc M ≤ exp (a * t) := hexp
        _ ≤ exp (a * (t + π / b)) := by
          gcongr; linarith [div_pos pi_pos him]

/-! ### Local asymptotic stability of the nonlinear equation

With `y = log (x / K)` Hutchinson's equation becomes Wright's equation
`y'(t) = -r (e^{y(t - τ)} - 1)`, whose right side depends on the delayed value only. Writing
`y(t) = y(t - τ) - r ∫_{t-τ}^t (e^{y(s - τ)} - 1) ds` and expanding about `y(t - τ)` gives, for
`t ≥ 2τ`, the window estimate `|y t| ≤ ρ(M) M` whenever `|y| ≤ M ≤ 1` on `[t - 3τ, t - τ]`, where
`ρ(M) = |1 - rτ| + (rτ)² (1 + M) / 2 + rτ M` (`contractionFactor`). This is a Razumikhin-type
argument: the bound on the past window controls the present value. `ρ(0) < 1` exactly when
`0 < rτ < √5 - 1`, and then the window bound propagates forward (stability) and improves by the
factor `ρ` every `3τ` (geometric decay). -/

/-- `y` solves Wright's equation `y'(t) = -r (e^{y(t - τ)} - 1)`: `y` is continuous on
`[-τ, ∞)` and at every `t ≥ 0` its right derivative is `-r (e^{y(t - τ)} - 1)`. -/
structure IsWrightSolution (r τ : ℝ) (y : ℝ → ℝ) : Prop where
  continuousOn : ContinuousOn y (Ici (-τ))
  hasDerivWithinAt : ∀ t, 0 ≤ t →
    HasDerivWithinAt y (-(r * (exp (y (t - τ)) - 1))) (Ici t) t

/-- The window contraction factor `ρ(a, m) = |1 - a| + a² (1 + m) / 2 + a m`, used with
`a = r τ` and `m` a bound on `|y|` over the past window. -/
noncomputable def contractionFactor (a m : ℝ) : ℝ := |1 - a| + a ^ 2 * (1 + m) / 2 + a * m

/-- `|e^z - 1| ≤ M (1 + M)` for `|z| ≤ M ≤ 1`. -/
theorem abs_exp_sub_one_le_mul {z M : ℝ} (hz : |z| ≤ M) (hM : M ≤ 1) :
    |exp z - 1| ≤ M * (1 + M) := by
  have h1 := Real.abs_exp_sub_one_sub_id_le (hz.trans hM)
  have h2 : z ^ 2 ≤ M ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg z) hz 2
  calc |exp z - 1| = |(exp z - 1 - z) + z| := by ring_nf
    _ ≤ |exp z - 1 - z| + |z| := abs_add_le _ _
    _ ≤ M * (1 + M) := by nlinarith

/-- **Lipschitz bound on a window**: if `|y| ≤ M ≤ 1` on `[c - τ, d - τ]` with `0 ≤ c ≤ d`,
then `|y d - y c| ≤ r M (1 + M) (d - c)`. -/
theorem IsWrightSolution.abs_sub_le {r τ M c d : ℝ} {y : ℝ → ℝ} (hy : IsWrightSolution r τ y)
    (hr : 0 ≤ r) (hτ : 0 ≤ τ) (hM : M ≤ 1) (hc : 0 ≤ c) (hcd : c ≤ d)
    (hb : ∀ s ∈ Icc (c - τ) (d - τ), |y s| ≤ M) :
    |y d - y c| ≤ r * (M * (1 + M)) * (d - c) := by
  have := norm_image_sub_le_of_norm_deriv_right_le_segment (f := y) (a := c) (b := d)
    (C := r * (M * (1 + M)))
    (hy.continuousOn.mono fun s hs => by simp only [mem_Ici]; linarith [hs.1])
    (fun s hs => hy.hasDerivWithinAt s (hc.trans hs.1))
    (fun s hs => by
      rw [Real.norm_eq_abs, abs_neg, abs_mul, abs_of_nonneg hr]
      gcongr
      exact abs_exp_sub_one_le_mul (hb _ ⟨by linarith [hs.1], by linarith [hs.2]⟩) hM)
    d ⟨hcd, le_rfl⟩
  simpa [Real.norm_eq_abs] using this

/-- **Window contraction** (Razumikhin step): for `t ≥ 2τ`, if `|y| ≤ M ≤ 1` on
`[t - 3τ, t - τ]` then `|y t| ≤ ρ(rτ, M) M`. -/
theorem IsWrightSolution.abs_le_step {r τ M t : ℝ} {y : ℝ → ℝ} (hy : IsWrightSolution r τ y)
    (hr : 0 ≤ r) (hτ : 0 ≤ τ) (ht : 2 * τ ≤ t) (hM : M ≤ 1)
    (hb : ∀ s ∈ Icc (t - 3 * τ) (t - τ), |y s| ≤ M) :
    |y t| ≤ contractionFactor (r * τ) M * M := by
  set a := t - τ with ha
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hb a ⟨by linarith, le_rfl⟩)
  have hya : |y a| ≤ M := hb a ⟨by linarith, le_rfl⟩
  set F : ℝ → ℝ := fun s => y s - y a + r * (s - a) * y a with hF
  set B : ℝ → ℝ := fun s => r * M ^ 2 * (s - a) + r ^ 2 * (M * (1 + M)) * (τ ^ 2 - (t - s) ^ 2) / 2
    with hB
  have hBd : ∀ s, HasDerivAt B (r * M ^ 2 + r ^ 2 * (M * (1 + M)) * (t - s)) s := by
    intro s
    have h1 := ((hasDerivAt_id s).sub_const a).const_mul (r * M ^ 2)
    have h2 := (((hasDerivAt_const s t).sub (hasDerivAt_id s)).pow 2).const_sub (τ ^ 2)
    have h3 := (h2.const_mul (r ^ 2 * (M * (1 + M)))).div_const 2
    convert h1.add h3 using 1
    · funext s; simp [hB, mul_div_assoc]
    · simp; ring
  have key := image_norm_le_of_norm_deriv_right_le_deriv_boundary (f := F) (a := a) (b := t)
    (f' := fun s => -(r * (exp (y (s - τ)) - 1)) + r * y a) (B := B)
    (B' := fun s => r * M ^ 2 + r ^ 2 * (M * (1 + M)) * (t - s))
    (by
      refine ((hy.continuousOn.mono fun s hs => ?_).sub continuousOn_const).add
        (ContinuousOn.mul (by fun_prop) continuousOn_const)
      simp only [mem_Ici]; linarith [hs.1])
    (fun s hs => by
      have h := hy.hasDerivWithinAt s (by linarith [hs.1])
      convert (h.sub_const (y a)).add
        ((((hasDerivWithinAt_id s _).sub_const a).const_mul r).mul_const (y a)) using 1
      · funext x; simp [hF]
      · ring)
    (by simp [hF, hB, ha]) hBd
    (fun s hs => by
      have hs1 : |y (s - τ)| ≤ M := hb _ ⟨by linarith [hs.1], by linarith [hs.2]⟩
      have hdiff : |y a - y (s - τ)| ≤ r * (M * (1 + M)) * (a - (s - τ)) :=
        hy.abs_sub_le hr hτ hM (by linarith [hs.1]) (by linarith [hs.2])
          (fun σ hσ => hb σ ⟨by linarith [hσ.1, hs.1], by linarith [hσ.2]⟩)
      have hq := Real.abs_exp_sub_one_sub_id_le (hs1.trans hM)
      have hq' : y (s - τ) ^ 2 ≤ M ^ 2 := by
        rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hs1 2
      have heq : -(r * (exp (y (s - τ)) - 1)) + r * y a =
          r * ((y a - y (s - τ)) - (exp (y (s - τ)) - 1 - y (s - τ))) := by ring
      rw [Real.norm_eq_abs, heq, abs_mul, abs_of_nonneg hr]
      have habs := abs_sub (y a - y (s - τ)) (exp (y (s - τ)) - 1 - y (s - τ))
      have : a - (s - τ) = t - s := by rw [ha]; ring
      rw [this] at hdiff
      nlinarith)
    (x := t) ⟨by linarith, le_rfl⟩
  have hFt : y t = F t + (1 - r * τ) * y a := by simp only [hF, ha]; ring
  have hBt : B t = r * M ^ 2 * τ + r ^ 2 * (M * (1 + M)) * τ ^ 2 / 2 := by
    simp only [hB, ha]; ring
  rw [Real.norm_eq_abs, hBt] at key
  rw [hFt, contractionFactor]
  calc |F t + (1 - r * τ) * y a| ≤ |F t| + |1 - r * τ| * |y a| := by
        rw [← abs_mul]; exact abs_add_le _ _
    _ ≤ (r * M ^ 2 * τ + r ^ 2 * (M * (1 + M)) * τ ^ 2 / 2) + |1 - r * τ| * M := by
        gcongr
    _ = (|1 - r * τ| + (r * τ) ^ 2 * (1 + M) / 2 + r * τ * M) * M := by ring


/-- `ρ(a, m)` is monotone in `m` for `a ≥ 0`. -/
theorem contractionFactor_mono {a m m' : ℝ} (ha : 0 ≤ a) (h : m ≤ m') :
    contractionFactor a m ≤ contractionFactor a m' := by
  unfold contractionFactor; gcongr

/-- `ρ(a, m) ≥ 0` for `a, m ≥ 0`. -/
theorem contractionFactor_nonneg {a m : ℝ} (ha : 0 ≤ a) (hm : 0 ≤ m) :
    0 ≤ contractionFactor a m := by
  unfold contractionFactor; positivity

/-- **First two windows**: a history bound `|y| ≤ δ` on `[-τ, 0]` gives
`|y| ≤ δ (1 + 2 r τ)²` on `[-τ, 2τ]`, provided the latter is at most `1`. -/
theorem IsWrightSolution.abs_le_initial {r τ δ : ℝ} {y : ℝ → ℝ} (hy : IsWrightSolution r τ y)
    (hr : 0 ≤ r) (hτ : 0 < τ) (hδ : ∀ s ∈ Icc (-τ) 0, |y s| ≤ δ)
    (hδ1 : δ * (1 + 2 * (r * τ)) ^ 2 ≤ 1) :
    ∀ s ∈ Icc (-τ) (2 * τ), |y s| ≤ δ * (1 + 2 * (r * τ)) ^ 2 := by
  have hδ0 : 0 ≤ δ := (abs_nonneg _).trans (hδ (-τ) ⟨le_rfl, by linarith⟩)
  have hg : 1 ≤ 1 + 2 * (r * τ) := by nlinarith
  set δ₁ := δ * (1 + 2 * (r * τ)) with hδ₁
  have hδδ₁ : δ ≤ δ₁ := le_mul_of_one_le_right hδ0 hg
  have hδ₁0 : 0 ≤ δ₁ := hδ0.trans hδδ₁
  have hδ₁1 : δ₁ ≤ 1 := by
    calc δ₁ ≤ δ₁ * (1 + 2 * (r * τ)) := le_mul_of_one_le_right hδ₁0 hg
      _ = δ * (1 + 2 * (r * τ)) ^ 2 := by rw [hδ₁]; ring
      _ ≤ 1 := hδ1
  have hδ1' : δ ≤ 1 := hδδ₁.trans hδ₁1
  -- first window `[0, τ]`
  have h1 : ∀ s ∈ Icc (-τ) τ, |y s| ≤ δ₁ := by
    intro s hs
    rcases le_or_gt s 0 with h | h
    · exact (hδ s ⟨hs.1, h⟩).trans hδδ₁
    · have hd := hy.abs_sub_le hr hτ.le hδ1' le_rfl h.le
        (fun σ hσ => hδ σ ⟨by linarith [hσ.1], by linarith [hσ.2, hs.2]⟩)
      have hy0 := hδ 0 ⟨by linarith, le_rfl⟩
      have : r * (δ * (1 + δ)) * (s - 0) ≤ r * (δ * 2) * τ := by
        gcongr <;> linarith [hs.2]
      calc |y s| = |(y s - y 0) + y 0| := by ring_nf
        _ ≤ |y s - y 0| + |y 0| := abs_add_le _ _
        _ ≤ δ₁ := by rw [hδ₁]; nlinarith
  intro s hs
  rcases le_or_gt s τ with h | h
  · exact (h1 s ⟨hs.1, h⟩).trans (le_mul_of_one_le_right hδ₁0 hg |>.trans_eq (by rw [hδ₁]; ring))
  · have hd := hy.abs_sub_le hr hτ.le hδ₁1 hτ.le h.le
      (fun σ hσ => h1 σ ⟨by linarith [hσ.1], by linarith [hσ.2, hs.2]⟩)
    have hyτ := h1 τ ⟨by linarith, le_rfl⟩
    have : r * (δ₁ * (1 + δ₁)) * (s - τ) ≤ r * (δ₁ * 2) * τ := by
      gcongr <;> linarith [hs.2]
    calc |y s| = |(y s - y τ) + y τ| := by ring_nf
      _ ≤ |y s - y τ| + |y τ| := abs_add_le _ _
      _ ≤ δ₁ * (1 + 2 * (r * τ)) := by nlinarith
      _ = δ * (1 + 2 * (r * τ)) ^ 2 := by rw [hδ₁]; ring

/-- **Stability of Wright's equation**: if `|y| ≤ M ≤ 1` on `[-τ, 2τ]` and `ρ(rτ, M) ≤ 1`, then
`|y| ≤ M` on all of `[-τ, ∞)`. -/
theorem IsWrightSolution.abs_le_of_initial {r τ M : ℝ} {y : ℝ → ℝ} (hy : IsWrightSolution r τ y)
    (hr : 0 ≤ r) (hτ : 0 < τ) (hM : M ≤ 1) (hρ : contractionFactor (r * τ) M ≤ 1)
    (hinit : ∀ s ∈ Icc (-τ) (2 * τ), |y s| ≤ M) : ∀ t, -τ ≤ t → |y t| ≤ M := by
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hinit (-τ) ⟨le_rfl, by linarith⟩)
  have key : ∀ n : ℕ, ∀ t ∈ Icc (-τ) (2 * τ + n * τ), |y t| ≤ M := by
    intro n
    induction n with
    | zero => simpa using hinit
    | succ n ih =>
      intro t ht
      rcases le_or_gt t (2 * τ + n * τ) with h | h
      · exact ih t ⟨ht.1, h⟩
      · have hn : (0 : ℝ) ≤ n * τ := by positivity
        have ht2 : (t : ℝ) ≤ 2 * τ + n * τ + τ := by
          have := ht.2; push_cast at this; linarith
        have := hy.abs_le_step hr hτ.le (t := t) (M := M) (by linarith) hM
          (fun s hs => ih s ⟨by linarith [hs.1], by linarith [hs.2]⟩)
        calc |y t| ≤ contractionFactor (r * τ) M * M := this
          _ ≤ 1 * M := by gcongr
          _ = M := one_mul M
  intro t ht
  obtain ⟨n, hn⟩ := exists_nat_ge (t / τ)
  refine key n t ⟨ht, ?_⟩
  rw [div_le_iff₀ hτ] at hn
  linarith

/-- **Geometric decay**: under the hypotheses of `abs_le_of_initial`, `|y t| ≤ ρ(rτ, M)ⁿ M`
for `t ≥ -τ + 3τ n`. -/
theorem IsWrightSolution.abs_le_pow {r τ M : ℝ} {y : ℝ → ℝ} (hy : IsWrightSolution r τ y)
    (hr : 0 ≤ r) (hτ : 0 < τ) (hM : M ≤ 1) (hρ : contractionFactor (r * τ) M ≤ 1)
    (hinit : ∀ s ∈ Icc (-τ) (2 * τ), |y s| ≤ M) :
    ∀ n : ℕ, ∀ t, -τ + 3 * τ * n ≤ t → |y t| ≤ contractionFactor (r * τ) M ^ n * M := by
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hinit (-τ) ⟨le_rfl, by linarith⟩)
  have ha : 0 ≤ r * τ := mul_nonneg hr hτ.le
  set ρ := contractionFactor (r * τ) M with hρdef
  have hρ0 : 0 ≤ ρ := contractionFactor_nonneg ha hM0
  intro n
  induction n with
  | zero =>
    intro t ht
    simpa using hy.abs_le_of_initial hr hτ hM hρ hinit t (by simpa using ht)
  | succ n ih =>
    intro t ht
    push_cast at ht
    have hpn : ρ ^ n ≤ 1 := pow_le_one₀ hρ0 hρ
    have hMn0 : 0 ≤ ρ ^ n * M := by positivity
    have hMn : ρ ^ n * M ≤ M := by
      calc ρ ^ n * M ≤ 1 * M := by gcongr
        _ = M := one_mul M
    have hn : (0 : ℝ) ≤ 3 * τ * n := by positivity
    have := hy.abs_le_step hr hτ.le (t := t) (M := ρ ^ n * M) (by linarith) (hMn.trans hM)
      (fun s hs => ih s (by linarith [hs.1]))
    calc |y t| ≤ contractionFactor (r * τ) (ρ ^ n * M) * (ρ ^ n * M) := this
      _ ≤ ρ * (ρ ^ n * M) := by gcongr; exact contractionFactor_mono ha hMn
      _ = ρ ^ (n + 1) * M := by ring

/-- **Attractivity of Wright's equation**: if `|y| ≤ M ≤ 1` on `[-τ, 2τ]` and `ρ(rτ, M) < 1`,
then `y t → 0`. -/
theorem IsWrightSolution.tendsto_zero {r τ M : ℝ} {y : ℝ → ℝ} (hy : IsWrightSolution r τ y)
    (hr : 0 ≤ r) (hτ : 0 < τ) (hM : M ≤ 1) (hρ : contractionFactor (r * τ) M < 1)
    (hinit : ∀ s ∈ Icc (-τ) (2 * τ), |y s| ≤ M) : Tendsto y atTop (𝓝 0) := by
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hinit (-τ) ⟨le_rfl, by linarith⟩)
  have ha : 0 ≤ r * τ := mul_nonneg hr hτ.le
  have hρ0 := contractionFactor_nonneg ha hM0
  have hp := (tendsto_pow_atTop_nhds_zero_of_lt_one hρ0 hρ).mul_const M
  rw [zero_mul] at hp
  rw [Metric.tendsto_atTop] at hp ⊢
  intro ε hε
  obtain ⟨N, hN⟩ := hp ε hε
  refine ⟨-τ + 3 * τ * N, fun t ht => ?_⟩
  have h1 := hy.abs_le_pow hr hτ hM hρ.le hinit N t ht
  have h2 := hN N le_rfl
  rw [Real.dist_eq, sub_zero] at h2 ⊢
  exact lt_of_le_of_lt h1 (le_abs_self _ |>.trans_lt h2)

/-- `|1 - a| + a² / 2 < 1` for `0 < a < √5 - 1`. -/
theorem contractionFactor_zero_lt_one {a : ℝ} (ha : 0 < a) (ha' : a < √5 - 1) :
    contractionFactor a 0 < 1 := by
  unfold contractionFactor
  have h5 := Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)
  have hs := Real.sqrt_nonneg 5
  rcases le_or_gt a 1 with h | h
  · rw [abs_of_nonneg (by linarith)]; nlinarith
  · rw [abs_of_neg (by linarith)]; nlinarith

/-- If `ρ(a, 0) < 1` then some window bound `0 < m ≤ 1` still has `ρ(a, m) < 1`. -/
theorem exists_contractionFactor_lt_one {a : ℝ} (ha : 0 ≤ a) (h0 : contractionFactor a 0 < 1) :
    ∃ m, 0 < m ∧ m ≤ 1 ∧ contractionFactor a m < 1 := by
  set g := 1 - contractionFactor a 0 with hg
  set c := a ^ 2 / 2 + a with hc
  have hg0 : 0 < g := by linarith
  have hc0 : 0 ≤ c := by positivity
  refine ⟨min 1 (g / (2 * (c + 1))), lt_min one_pos (by positivity), min_le_left _ _, ?_⟩
  set m := min 1 (g / (2 * (c + 1)))
  have hm0 : 0 ≤ m := le_min zero_le_one (by positivity)
  have heq : contractionFactor a m = contractionFactor a 0 + m * c := by
    simp only [contractionFactor, hc]; ring
  have : m * c ≤ g / 2 := by
    calc m * c ≤ m * (c + 1) := by nlinarith
      _ ≤ g / (2 * (c + 1)) * (c + 1) := by gcongr; exact min_le_right _ _
      _ = g / 2 := by field_simp
  linarith

/-- `|x - K| ≤ δ ≤ K / 2` gives `|log (x / K)| ≤ 2 δ / K`. -/
theorem abs_log_div_le {x K δ : ℝ} (hK : 0 < K) (hδ : δ ≤ K / 2) (hx : |x - K| ≤ δ) :
    |log (x / K)| ≤ 2 * δ / K := by
  have hδ0 : 0 ≤ δ := (abs_nonneg _).trans hx
  obtain ⟨hx1, hx2⟩ := abs_le.mp hx
  have hxK : K / 2 ≤ x := by linarith
  have hx0 : 0 < x := by linarith
  rw [abs_le]
  constructor
  · have h := Real.one_sub_inv_le_log_of_pos (div_pos hx0 hK)
    have he : 1 - (x / K)⁻¹ = (x - K) / x := by field_simp
    rw [he] at h
    refine le_trans ?_ h
    rw [le_div_iff₀ hx0]
    have h1 : δ ≤ 2 * δ / K * x := by
      calc δ = 2 * δ / K * (K / 2) := by field_simp
        _ ≤ 2 * δ / K * x := by gcongr
    nlinarith
  · calc log (x / K) ≤ x / K - 1 := Real.log_le_sub_one_of_pos (div_pos hx0 hK)
      _ = (x - K) / K := by field_simp
      _ ≤ δ / K := by gcongr
      _ ≤ 2 * δ / K := by gcongr; linarith

/-- A positive solution of Hutchinson's equation gives a solution `log (x / K)` of Wright's
equation. -/
theorem IsSolution.isWrightSolution_log {r K τ : ℝ} {φ x : ℝ → ℝ} (hK : 0 < K) (hτ : 0 ≤ τ)
    (hx : IsSolution r K τ φ x) (hpos : ∀ t, -τ ≤ t → 0 < x t) :
    IsWrightSolution r τ (fun t => log (x t / K)) where
  continuousOn := (hx.continuousOn.div_const K).log fun t ht => (div_pos (hpos t ht) hK).ne'
  hasDerivWithinAt t ht := by
    have hxt := hpos t (by linarith)
    have hxd := hpos (t - τ) (by linarith)
    have h := ((hx.hasDerivWithinAt t ht).div_const K).log (div_pos hxt hK).ne'
    convert h using 1
    rw [exp_log (div_pos hxd hK)]
    field_simp
    ring

/-- **Local asymptotic stability of the nonlinear equation** for `0 < r τ < √5 - 1`: the
positive equilibrium `K` is stable (every `ε` has a `δ` such that histories within `δ` of `K`
give solutions within `ε` of `K` on all of `[-τ, ∞)`) and attracting (those solutions converge
to `K`). The bound `√5 - 1` lies below `π / 2`, so this covers `0 < τ < (√5 - 1) / r`, a
proper part of the linearly stable range `τ < τ_c` (`sqrt_five_sub_one_lt_pi_div_two`). -/
theorem localAsymptoticStability {r K τ : ℝ} (hr : 0 < r) (hK : 0 < K) (hτ : 0 < τ)
    (hrτ : r * τ < √5 - 1) :
    ∀ ε > 0, ∃ δ > 0, ∀ φ x : ℝ → ℝ, IsSolution r K τ φ x →
      (∀ s ∈ Icc (-τ) 0, |φ s - K| ≤ δ) →
      (∀ t, -τ ≤ t → |x t - K| ≤ ε) ∧ Tendsto x atTop (𝓝 K) := by
  intro ε hε
  have ha : 0 < r * τ := mul_pos hr hτ
  obtain ⟨m, hm0, hm1, hρm⟩ :=
    exists_contractionFactor_lt_one ha.le (contractionFactor_zero_lt_one ha hrτ)
  set G := (1 + 2 * (r * τ)) ^ 2 with hG
  have hG1 : 1 ≤ G := one_le_pow₀ (by linarith)
  have hG0 : 0 < G := by linarith
  set M := min m (ε / (2 * K)) with hMdef
  have hM0 : 0 < M := lt_min hm0 (by positivity)
  have hMm : M ≤ m := min_le_left _ _
  have hMε : M ≤ ε / (2 * K) := min_le_right _ _
  set δ := min (K / 2) (K * (M / G) / 2) with hδdef
  have hδ0 : 0 < δ := lt_min (by positivity) (by positivity)
  refine ⟨δ, hδ0, fun φ x hx hφ => ?_⟩
  have hφx : ∀ s ∈ Icc (-τ) 0, |x s - K| ≤ δ := fun s hs => by
    rw [hx.eqOn_history hs]; exact hφ s hs
  have hhist : ∀ s ∈ Icc (-τ) 0, K / 2 ≤ x s := by
    intro s hs
    have := (abs_le.mp ((hφx s hs).trans (min_le_left _ _))).1
    linarith
  have hpos : ∀ t, -τ ≤ t → 0 < x t := by
    intro t ht
    rcases le_or_gt t 0 with h | h
    · linarith [hhist t ⟨ht, h⟩]
    · have h0 : 0 < φ 0 := by
        rw [← hx.eqOn_history ⟨by linarith, le_rfl⟩]; linarith [hhist 0 ⟨by linarith, le_rfl⟩]
      exact hx.pos hτ.le h0 h.le
  set y : ℝ → ℝ := fun t => log (x t / K) with hy
  have hW : IsWrightSolution r τ y := hx.isWrightSolution_log hK hτ.le hpos
  have hxy : ∀ t, -τ ≤ t → x t = K * exp (y t) := by
    intro t ht
    simp only [hy]
    rw [exp_log (div_pos (hpos t ht) hK)]
    field_simp
  have hyδ : ∀ s ∈ Icc (-τ) 0, |y s| ≤ M / G := by
    intro s hs
    have h := abs_log_div_le hK (min_le_left _ _) (hφx s hs)
    calc |y s| ≤ 2 * δ / K := h
      _ ≤ 2 * (K * (M / G) / 2) / K := by gcongr; exact min_le_right _ _
      _ = M / G := by field_simp
  have hMG : M / G * G = M := by field_simp
  have hM1 : M ≤ 1 := hMm.trans hm1
  have hinit := hW.abs_le_initial hr.le hτ hyδ (by rw [← hG, hMG]; exact hM1)
  rw [← hG, hMG] at hinit
  have hρ : contractionFactor (r * τ) M < 1 := (contractionFactor_mono ha.le hMm).trans_lt hρm
  have hglob := hW.abs_le_of_initial hr.le hτ hM1 hρ.le hinit
  refine ⟨fun t ht => ?_, ?_⟩
  · have hyt := hglob t ht
    rw [hxy t ht]
    have he := Real.abs_exp_sub_one_le (hyt.trans hM1)
    calc |K * exp (y t) - K| = K * |exp (y t) - 1| := by
          rw [← abs_of_pos hK, ← abs_mul, abs_of_pos hK]; ring_nf
      _ ≤ K * (2 * M) := by gcongr; linarith
      _ ≤ K * (2 * (ε / (2 * K))) := by gcongr
      _ = ε := by field_simp
  · have hyl := hW.tendsto_zero hr.le hτ hM1 hρ hinit
    have hl : Tendsto (fun t => K * exp (y t)) atTop (𝓝 K) := by
      simpa using ((continuous_exp.tendsto 0).comp hyl).const_mul K
    refine hl.congr' ?_
    filter_upwards [eventually_ge_atTop (-τ)] with t ht
    exact (hxy t ht).symm

/-- The nonlinear stability bound lies strictly below the critical one: `√5 - 1 < π / 2`, so
`(√5 - 1) / r < τ_c` for `r > 0`. -/
theorem sqrt_five_sub_one_lt_pi_div_two : √5 - 1 < π / 2 := by
  have h : √5 < 9 / 4 := by
    rw [Real.sqrt_lt' (by norm_num)]; norm_num
  linarith [pi_gt_three]

/-- The delay range of `localAsymptoticStability` in terms of `τ`: `r τ < √5 - 1` iff
`τ < (√5 - 1) / r`. That this bound is below `criticalDelay r` is
`sqrt_five_sub_one_div_lt_criticalDelay`. -/
theorem mul_lt_sqrt_five_sub_one_iff {r τ : ℝ} (hr : 0 < r) :
    r * τ < √5 - 1 ↔ τ < (√5 - 1) / r := by
  rw [lt_div_iff₀ hr, mul_comm]

/-- `(√5 - 1) / r < τ_c = π / (2 r)` for `r > 0`. -/
theorem sqrt_five_sub_one_div_lt_criticalDelay {r : ℝ} (hr : 0 < r) :
    (√5 - 1) / r < criticalDelay r := by
  rw [criticalDelay, div_lt_div_iff₀ hr (by positivity)]
  nlinarith [sqrt_five_sub_one_lt_pi_div_two]

end MathlibExt.Biology.Dynamics.DelayedLogistic

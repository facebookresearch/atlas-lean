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
import Mathlib.Analysis.Calculus.MeanValue
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

## Scope

Stability is the *linearized* statement: it concerns the characteristic roots of the linear
delay equation `u' = -r u(t - τ)`. Transferring it to local asymptotic stability of the
nonlinear equation (the principle of linearized stability for delay equations), and the Hopf
normal form at `τ_c`, are not formalized here.

## References

* G. E. Hutchinson, *Circular causal systems in ecology*, Ann. N. Y. Acad. Sci. 50 (1948)
  221–246.
* J. K. Hale, S. M. Verduyn Lunel, *Introduction to Functional Differential Equations*,
  Springer (1993), §5.2 (method of steps) and §11.4.
* H. Smith, *An Introduction to Delay Differential Equations with Applications to the Life
  Sciences*, Springer (2011), §3.4 and §4.4.
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

end MathlibExt.Biology.Dynamics.DelayedLogistic

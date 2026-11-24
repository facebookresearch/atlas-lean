/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# The θ-rule for exponential decay

For `u' = -a u`, `u(0) = I`, with a constant time step `Δt > 0` and `t_n = n Δt`, the θ-rule is
`(u^{n+1} - u^n) / Δt = -a (θ u^{n+1} + (1 - θ) u^n)`: `θ = 0` is the Forward Euler scheme,
`θ = 1` the Backward Euler scheme and `θ = 1 / 2` the Crank–Nicolson scheme. When
`1 + θ a Δt ≠ 0`, each step multiplies the numerical solution by the amplification factor
`A = (1 - (1 - θ) a Δt) / (1 + θ a Δt)`, so `u^n = I A^n`, while the exact solution is
`I e^{-a t_n} = I (e^{-a Δt})^n`. The other results assume `θ ≥ 0`, `a ≥ 0` and `Δt ≥ 0`, with
`Δt > 0` for the results on solutions, and `a > 0`, `Δt > 0` for the strict criteria.

## Main results

* `isSolution_iff`: `u` solves the scheme iff `u^n = u^0 A^n`.
* `amplificationFactor_neg_iff`, `IsSolution.sign_of_one_lt`, `IsSolution.antitone_of_le_one`,
  `IsSolution.strictAnti_iff_lt_one`: `A < 0` iff `(1 - θ) a Δt > 1`. For `I > 0`, the numerical
  solution then changes sign at every step. If `(1 - θ) a Δt ≤ 1` and `I ≥ 0`, it is nonnegative
  and nonincreasing. For `a > 0` and `I > 0`, it is positive and strictly decreasing iff
  `(1 - θ) a Δt < 1`.
* `abs_amplificationFactor_le_one_iff`, `abs_amplificationFactor_lt_one_iff`,
  `IsSolution.abs_le_iff`, `IsSolution.tendsto_zero_iff`, `IsSolution.tendsto_abs_atTop`:
  `|A| ≤ 1` iff `(1 - 2θ) a Δt ≤ 2`, which always holds for `θ ≥ 1 / 2`, and `|A| < 1` iff
  `(1 - 2θ) a Δt < 2` when `a, Δt > 0`. For `I ≠ 0`, the numerical solution never exceeds `|I|`
  in absolute value iff `(1 - 2θ) a Δt ≤ 2`; for `a > 0` and `I ≠ 0`, it tends to `0` iff
  `(1 - 2θ) a Δt < 2`; for `I ≠ 0` and `(1 - 2θ) a Δt > 2`, its absolute value tends to infinity.
* `abs_amplificationFactor_sub_exp_le`, `abs_amplificationFactor_half_sub_exp_le`:
  `|A - e^{-a Δt}| ≤ max (θ - 1/2) (1/2) * (a Δt)^2`, and `≤ (a Δt)^3 / 12` for Crank–Nicolson.
* `IsSolution.abs_sub_exp_le`, `IsSolution.abs_sub_exp_le_of_half`, `tendsto_of_isSolution`:
  the global error `|u^n - I e^{-a t_n}|` is at most `max (θ - 1/2) (1/2) * |I| a^2 t_n Δt` if
  `(1 - 2θ) a Δt ≤ 2`, and at most `|I| a^3 t_n Δt^2 / 12` for Crank–Nicolson, so the numerical
  solution at a fixed time `t > 0` tends to `I e^{-a t}` as the number of steps tends to infinity,
  using step `t / n` and initial value `I` for every `n ≥ 1`.

The error bounds are upper bounds with the source's leading coefficients `1/2` and `1/12`, not
its signed leading terms.

## References

* H. P. Langtangen, *Finite Difference Computing with Exponential Decay Models*, Springer,
  2016: Sections 1.1.5 and 1.1.6 (the θ-rule on a uniform grid), Sections 2.2.1 and 2.2.2 (exact
  numerical solution and stability), Sections 2.3.1, 2.3.2 and 2.3.4 (amplification factors and
  global error).
-/

@[expose] public section

open Filter Topology

namespace MathlibExt.Analysis.ODE.TimeStepping.ThetaRule

/-- **Amplification factor of the θ-rule.** The number
$A = \frac{1 - (1 - \theta) a \Delta t}{1 + \theta a \Delta t}$, read as $0$ when
$1 + \theta a \Delta t = 0$. When $\Delta t \ne 0$ and $1 + \theta a \Delta t \ne 0$, one step
of the θ-rule for $u' = -a u$ multiplies the numerical solution by $A$. -/
noncomputable def amplificationFactor (θ a Δt : ℝ) : ℝ :=
  (1 - (1 - θ) * a * Δt) / (1 + θ * a * Δt)

/-- **Solution of the θ-rule.** A sequence $(u^n)_{n \ge 0}$ solves the θ-rule for $u' = -a u$ with
constant time step $\Delta t$ if
$\frac{u^{n+1} - u^n}{\Delta t} = -a (\theta u^{n+1} + (1 - \theta) u^n)$ for every $n \ge 0$,
the quotient being read as $0$ when $\Delta t = 0$. No initial value is imposed. -/
def IsSolution (θ a Δt : ℝ) (u : ℕ → ℝ) : Prop :=
  ∀ n, (u (n + 1) - u n) / Δt = -a * (θ * u (n + 1) + (1 - θ) * u n)

private lemma one_add_pos {θ a Δt : ℝ} (hθ : 0 ≤ θ) (ha : 0 ≤ a) (hΔt : 0 ≤ Δt) :
    0 < 1 + θ * a * Δt := by
  positivity

private lemma step_iff {θ a Δt x y : ℝ} (hΔt : Δt ≠ 0) (hden : 1 + θ * a * Δt ≠ 0) :
    (x - y) / Δt = -a * (θ * x + (1 - θ) * y) ↔ x = amplificationFactor θ a Δt * y := by
  rw [amplificationFactor, div_mul_eq_mul_div, eq_div_iff hden, div_eq_iff hΔt]
  constructor <;> intro h <;> linear_combination h

/-- **Exact numerical solution of the θ-rule.** If $\Delta t \ne 0$ and
$1 + \theta a \Delta t \ne 0$, then $u$ solves the θ-rule iff $u^n = u^0 A^n$ for every $n$, where
$A$ is the amplification factor. -/
theorem isSolution_iff {θ a Δt : ℝ} {u : ℕ → ℝ} (hΔt : Δt ≠ 0) (hden : 1 + θ * a * Δt ≠ 0) :
    IsSolution θ a Δt u ↔ ∀ n, u n = u 0 * amplificationFactor θ a Δt ^ n := by
  simp only [IsSolution, step_iff hΔt hden]
  constructor
  · intro h n
    induction n with
    | zero => simp
    | succ n ih => rw [h n, ih, pow_succ]; ring
  · intro h n
    rw [h (n + 1), h n, pow_succ]
    ring

private lemma IsSolution.eq {θ a Δt : ℝ} {u : ℕ → ℝ} (hu : IsSolution θ a Δt u) (hθ : 0 ≤ θ)
    (ha : 0 ≤ a) (hΔt : 0 < Δt) (n : ℕ) : u n = u 0 * amplificationFactor θ a Δt ^ n :=
  (isSolution_iff hΔt.ne' (one_add_pos hθ ha hΔt.le).ne').mp hu n

private lemma amplificationFactor_eq (θ a Δt : ℝ) :
    amplificationFactor θ a Δt = (1 - (1 - θ) * (a * Δt)) / (1 + θ * (a * Δt)) := by
  simp only [amplificationFactor, mul_assoc]

private lemma amplificationFactor_le_one {θ a Δt : ℝ} (hθ : 0 ≤ θ) (ha : 0 ≤ a)
    (hΔt : 0 ≤ Δt) : amplificationFactor θ a Δt ≤ 1 := by
  rw [amplificationFactor, div_le_one (one_add_pos hθ ha hΔt)]
  nlinarith [mul_nonneg ha hΔt]

/-- **Negative amplification factor of the θ-rule.** For $\theta, a, \Delta t \ge 0$, the
amplification factor $A$ is negative iff $(1 - \theta) a \Delta t > 1$. -/
theorem amplificationFactor_neg_iff {θ a Δt : ℝ} (hθ : 0 ≤ θ) (ha : 0 ≤ a) (hΔt : 0 ≤ Δt) :
    amplificationFactor θ a Δt < 0 ↔ 1 < (1 - θ) * a * Δt := by
  rw [amplificationFactor, div_lt_iff₀ (one_add_pos hθ ha hΔt), zero_mul, sub_neg]

/-- **Oscillation of the θ-rule.** Let $u$ solve the θ-rule with $\theta, a \ge 0$ and
$\Delta t > 0$. If $(1 - \theta) a \Delta t > 1$ and $u^0 > 0$, then $u^n > 0$ for every even $n$
and $u^n < 0$ for every odd $n$. -/
theorem IsSolution.sign_of_one_lt {θ a Δt : ℝ} {u : ℕ → ℝ} (hu : IsSolution θ a Δt u)
    (hθ : 0 ≤ θ) (ha : 0 ≤ a) (hΔt : 0 < Δt) (h : 1 < (1 - θ) * a * Δt) (hu0 : 0 < u 0)
    (k : ℕ) : 0 < u (2 * k) ∧ u (2 * k + 1) < 0 := by
  have hA := (amplificationFactor_neg_iff hθ ha hΔt.le).mpr h
  rw [hu.eq hθ ha hΔt (2 * k), hu.eq hθ ha hΔt (2 * k + 1)]
  exact ⟨mul_pos hu0 (Even.pow_pos (even_two_mul k) hA.ne),
    mul_neg_of_pos_of_neg hu0 ((Odd.pow_neg_iff (odd_two_mul_add_one k)).mpr hA)⟩

/-- **Monotonicity of the θ-rule.** Let $u$ solve the θ-rule with $\theta, a \ge 0$ and
$\Delta t > 0$. If $(1 - \theta) a \Delta t \le 1$ and $u^0 \ge 0$, then $u^n \ge 0$ and
$u^{n+1} \le u^n$ for every $n$. -/
theorem IsSolution.antitone_of_le_one {θ a Δt : ℝ} {u : ℕ → ℝ} (hu : IsSolution θ a Δt u)
    (hθ : 0 ≤ θ) (ha : 0 ≤ a) (hΔt : 0 < Δt) (h : (1 - θ) * a * Δt ≤ 1) (hu0 : 0 ≤ u 0) :
    (∀ n, 0 ≤ u n) ∧ Antitone u := by
  have hA : 0 ≤ amplificationFactor θ a Δt :=
    not_lt.mp fun hneg ↦ (not_lt.mpr h) ((amplificationFactor_neg_iff hθ ha hΔt.le).mp hneg)
  have hA1 := amplificationFactor_le_one hθ ha hΔt.le
  refine ⟨fun n ↦ by rw [hu.eq hθ ha hΔt n]; positivity, antitone_nat_of_succ_le fun n ↦ ?_⟩
  rw [hu.eq hθ ha hΔt (n + 1), hu.eq hθ ha hΔt n, pow_succ, ← mul_assoc]
  exact mul_le_of_le_one_right (by positivity) hA1

/-- **Strict monotonicity of the θ-rule.** Let $u$ solve the θ-rule with $\theta \ge 0$, $a > 0$,
$\Delta t > 0$ and $u^0 > 0$. Then $u^n > 0$ and $u^{n+1} < u^n$ for every $n$ iff
$(1 - \theta) a \Delta t < 1$. -/
theorem IsSolution.strictAnti_iff_lt_one {θ a Δt : ℝ} {u : ℕ → ℝ} (hu : IsSolution θ a Δt u)
    (hθ : 0 ≤ θ) (ha : 0 < a) (hΔt : 0 < Δt) (hu0 : 0 < u 0) :
    ((∀ n, 0 < u n) ∧ StrictAnti u) ↔ (1 - θ) * a * Δt < 1 := by
  have hden := one_add_pos hθ ha.le hΔt.le
  have hA1 : amplificationFactor θ a Δt < 1 := by
    rw [amplificationFactor, div_lt_one hden]
    nlinarith [mul_pos ha hΔt]
  have hA0 : 0 < amplificationFactor θ a Δt ↔ (1 - θ) * a * Δt < 1 := by
    rw [amplificationFactor, lt_div_iff₀ hden, zero_mul, sub_pos]
  constructor
  · rintro ⟨hpos, -⟩
    have h1 := hpos 1
    rw [hu.eq hθ ha.le hΔt 1, pow_one] at h1
    exact hA0.mp (pos_of_mul_pos_right h1 hu0.le)
  · intro h
    have hA := hA0.mpr h
    refine ⟨fun n ↦ by rw [hu.eq hθ ha.le hΔt n]; positivity, strictAnti_nat_of_succ_lt fun n ↦ ?_⟩
    rw [hu.eq hθ ha.le hΔt (n + 1), hu.eq hθ ha.le hΔt n, pow_succ, ← mul_assoc]
    exact mul_lt_of_lt_one_right (by positivity) hA1

/-- **Bounded amplification factor of the θ-rule.** For $\theta, a, \Delta t \ge 0$, the
amplification factor satisfies $|A| \le 1$ iff $(1 - 2 \theta) a \Delta t \le 2$. -/
theorem abs_amplificationFactor_le_one_iff {θ a Δt : ℝ} (hθ : 0 ≤ θ) (ha : 0 ≤ a)
    (hΔt : 0 ≤ Δt) : |amplificationFactor θ a Δt| ≤ 1 ↔ (1 - 2 * θ) * a * Δt ≤ 2 := by
  have hden := one_add_pos hθ ha hΔt
  rw [abs_le, and_iff_left (amplificationFactor_le_one hθ ha hΔt), amplificationFactor,
    le_div_iff₀ hden]
  constructor <;> intro h <;> linarith

/-- **Contracting amplification factor of the θ-rule.** For $\theta \ge 0$, $a > 0$ and
$\Delta t > 0$, the amplification factor satisfies $|A| < 1$ iff $(1 - 2 \theta) a \Delta t < 2$. -/
theorem abs_amplificationFactor_lt_one_iff {θ a Δt : ℝ} (hθ : 0 ≤ θ) (ha : 0 < a)
    (hΔt : 0 < Δt) : |amplificationFactor θ a Δt| < 1 ↔ (1 - 2 * θ) * a * Δt < 2 := by
  have hden := one_add_pos hθ ha.le hΔt.le
  have hp := mul_pos ha hΔt
  rw [abs_lt, amplificationFactor, lt_div_iff₀ hden, div_lt_one hden]
  constructor
  · rintro ⟨h, -⟩
    linarith
  · intro h
    constructor <;> nlinarith

/-- **Stability of the θ-rule.** Let $u$ solve the θ-rule with $\theta, a \ge 0$, $\Delta t > 0$ and
$u^0 \ne 0$. Then $|u^n| \le |u^0|$ for every $n$ iff $(1 - 2 \theta) a \Delta t \le 2$. -/
theorem IsSolution.abs_le_iff {θ a Δt : ℝ} {u : ℕ → ℝ} (hu : IsSolution θ a Δt u)
    (hθ : 0 ≤ θ) (ha : 0 ≤ a) (hΔt : 0 < Δt) (hu0 : u 0 ≠ 0) :
    (∀ n, |u n| ≤ |u 0|) ↔ (1 - 2 * θ) * a * Δt ≤ 2 := by
  rw [← abs_amplificationFactor_le_one_iff hθ ha hΔt.le]
  have h0 : 0 < |u 0| := abs_pos.mpr hu0
  constructor
  · intro h
    have h1 := h 1
    rw [hu.eq hθ ha hΔt 1, pow_one, abs_mul] at h1
    exact (mul_le_iff_le_one_right h0).mp h1
  · intro hA n
    rw [hu.eq hθ ha hΔt n, abs_mul, abs_pow]
    exact mul_le_of_le_one_right h0.le (pow_le_one₀ (abs_nonneg _) hA)

/-- **Decay of the θ-rule.** Let $u$ solve the θ-rule with $\theta \ge 0$, $a > 0$, $\Delta t > 0$
and $u^0 \ne 0$. Then $u^n \to 0$ as $n \to \infty$ iff $(1 - 2 \theta) a \Delta t < 2$. -/
theorem IsSolution.tendsto_zero_iff {θ a Δt : ℝ} {u : ℕ → ℝ} (hu : IsSolution θ a Δt u)
    (hθ : 0 ≤ θ) (ha : 0 < a) (hΔt : 0 < Δt) (hu0 : u 0 ≠ 0) :
    Tendsto u atTop (𝓝 0) ↔ (1 - 2 * θ) * a * Δt < 2 := by
  rw [← abs_amplificationFactor_lt_one_iff hθ ha hΔt, ← tendsto_pow_atTop_nhds_zero_iff]
  have hu' : u = fun n ↦ u 0 * amplificationFactor θ a Δt ^ n :=
    funext (hu.eq hθ ha.le hΔt)
  constructor
  · intro h
    have := h.const_mul (u 0)⁻¹
    rw [mul_zero] at this
    refine this.congr fun n ↦ ?_
    rw [hu.eq hθ ha.le hΔt n, inv_mul_cancel_left₀ hu0]
  · intro h
    rw [hu']
    simpa using h.const_mul (u 0)

/-- **Growth of the θ-rule.** Let $u$ solve the θ-rule with $\theta, a \ge 0$ and $\Delta t > 0$. If
$(1 - 2 \theta) a \Delta t > 2$ and $u^0 \ne 0$, then $|u^n| \to \infty$ as $n \to \infty$. -/
theorem IsSolution.tendsto_abs_atTop {θ a Δt : ℝ} {u : ℕ → ℝ} (hu : IsSolution θ a Δt u)
    (hθ : 0 ≤ θ) (ha : 0 ≤ a) (hΔt : 0 < Δt) (h : 2 < (1 - 2 * θ) * a * Δt) (hu0 : u 0 ≠ 0) :
    Tendsto (fun n ↦ |u n|) atTop atTop := by
  have hA : 1 < |amplificationFactor θ a Δt| :=
    not_le.mp fun hle ↦ (not_le.mpr h) ((abs_amplificationFactor_le_one_iff hθ ha hΔt.le).mp hle)
  have hlim := (tendsto_pow_atTop_atTop_of_one_lt hA).const_mul_atTop (abs_pos.mpr hu0)
  refine hlim.congr fun n ↦ ?_
  rw [hu.eq hθ ha hΔt n, abs_mul, abs_pow]

private lemma one_add_mul_exp_neg_le_one (p : ℝ) :
    (1 + p) * Real.exp (-p) ≤ 1 := by
  have hexp : 1 + p ≤ Real.exp p := by linarith [Real.add_one_le_exp p]
  calc (1 + p) * Real.exp (-p) ≤ Real.exp p * Real.exp (-p) := by gcongr
    _ = 1 := by rw [← Real.exp_add]; simp

private lemma one_sub_one_add_mul_exp_neg_le {p : ℝ} (hp : 0 ≤ p) :
    1 - (1 + p) * Real.exp (-p) ≤ p ^ 2 / 2 := by
  have hderiv : ∀ x ∈ Set.Icc 0 p,
      HasDerivAt (fun t ↦ (1 + t) * Real.exp (-t) - (1 - t ^ 2 / 2))
        (x * (1 - Real.exp (-x))) x := by
    intro x _
    have h1 : HasDerivAt (fun t : ℝ ↦ 1 + t) 1 x := (hasDerivAt_id x).const_add 1
    have h2 : HasDerivAt (fun t : ℝ ↦ Real.exp (-t)) (Real.exp (-x) * (-1)) x :=
      (hasDerivAt_id x).neg.exp
    have h3 : HasDerivAt (fun t : ℝ ↦ 1 - t ^ 2 / 2) (-x) x := by
      have := ((hasDerivAt_pow 2 x).div_const 2).const_sub 1
      convert this using 1; ring
    convert (h1.mul h2).sub h3 using 1; ring
  have hmono : MonotoneOn (fun t ↦ (1 + t) * Real.exp (-t) - (1 - t ^ 2 / 2)) (Set.Icc 0 p) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc 0 p)
    · exact fun x hx ↦ (hderiv x hx).continuousAt.continuousWithinAt
    · exact fun x hx ↦ (hderiv x (interior_subset hx)).differentiableAt.differentiableWithinAt
    · intro x hx
      have hx0 : 0 ≤ x := (interior_subset hx).1
      rw [(hderiv x (interior_subset hx)).deriv]
      have : Real.exp (-x) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
      nlinarith
  have := hmono ⟨le_rfl, hp⟩ ⟨hp, le_rfl⟩ hp
  simp at this
  linarith

private lemma exp_neg_le_quadratic {p : ℝ} (hp : 0 ≤ p) :
    Real.exp (-p) ≤ 1 - p + p ^ 2 / 2 := by
  have h := Real.quadratic_le_exp_of_nonneg hp
  have hexp : Real.exp (-p) * Real.exp p = 1 := by
    rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  nlinarith [Real.exp_pos (-p), pow_nonneg hp 4]

/-- **Accuracy of the θ-rule amplification factor.** For $\theta, a, \Delta t \ge 0$, the
amplification factor satisfies $|A - e^{-a \Delta t}| \le \max(\theta - 1/2, 1/2) (a \Delta t)^2$.
The constant is $1/2$ for $\theta \in [0, 1]$. -/
theorem abs_amplificationFactor_sub_exp_le {θ a Δt : ℝ} (hθ : 0 ≤ θ) (ha : 0 ≤ a)
    (hΔt : 0 ≤ Δt) :
    |amplificationFactor θ a Δt - Real.exp (-(a * Δt))| ≤
      max (θ - 1 / 2) (1 / 2) * (a * Δt) ^ 2 := by
  rw [amplificationFactor_eq]
  have hp : 0 ≤ a * Δt := mul_nonneg ha hΔt
  generalize a * Δt = p at hp ⊢
  have hden : 0 < 1 + θ * p := by positivity
  have hden1 : 0 < 1 + p := by positivity
  have hA_ge : 1 - p ≤ (1 - (1 - θ) * p) / (1 + θ * p) := by
    rw [le_div_iff₀ hden]
    nlinarith [mul_nonneg hθ (sq_nonneg p)]
  have hexp_le := exp_neg_le_quadratic hp
  have hlower : -(max (θ - 1 / 2) (1 / 2) * p ^ 2) ≤
      (1 - (1 - θ) * p) / (1 + θ * p) - Real.exp (-p) := by
    have : 1 / 2 * p ^ 2 ≤ max (θ - 1 / 2) (1 / 2) * p ^ 2 :=
      mul_le_mul_of_nonneg_right (le_max_right _ _) (sq_nonneg p)
    linarith
  have hBE : 1 / (1 + p) - Real.exp (-p) ≤ p ^ 2 / 2 := by
    have hdiff : 1 / (1 + p) - Real.exp (-p) = (1 - (1 + p) * Real.exp (-p)) / (1 + p) := by
      field_simp
    have hnn : 0 ≤ 1 - (1 + p) * Real.exp (-p) := sub_nonneg.mpr (one_add_mul_exp_neg_le_one p)
    rw [hdiff]
    exact (div_le_self hnn (by linarith)).trans (one_sub_one_add_mul_exp_neg_le hp)
  have hupper : (1 - (1 - θ) * p) / (1 + θ * p) - Real.exp (-p) ≤
      max (θ - 1 / 2) (1 / 2) * p ^ 2 := by
    by_cases hθ1 : θ ≤ 1
    · have hle : (1 - (1 - θ) * p) / (1 + θ * p) ≤ 1 / (1 + p) := by
        rw [div_le_div_iff₀ hden hden1]
        nlinarith [sq_nonneg p]
      have : 1 / 2 * p ^ 2 ≤ max (θ - 1 / 2) (1 / 2) * p ^ 2 :=
        mul_le_mul_of_nonneg_right (le_max_right _ _) (sq_nonneg p)
      linarith
    · push Not at hθ1
      have hdiff : (1 - (1 - θ) * p) / (1 + θ * p) - 1 / (1 + p) =
          (θ - 1) * p ^ 2 / ((1 + θ * p) * (1 + p)) := by
        field_simp
        ring
      have hle : (θ - 1) * p ^ 2 / ((1 + θ * p) * (1 + p)) ≤ (θ - 1) * p ^ 2 := by
        apply div_le_self (by positivity)
        nlinarith [mul_nonneg hθ hp]
      have : (θ - 1 / 2) * p ^ 2 ≤ max (θ - 1 / 2) (1 / 2) * p ^ 2 :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (sq_nonneg p)
      linarith
  exact abs_le.mpr ⟨hlower, hupper⟩

/-- **Accuracy of the Crank–Nicolson amplification factor.** For $\theta = 1/2$ and
$a, \Delta t \ge 0$, the amplification factor satisfies
$|A - e^{-a \Delta t}| \le (a \Delta t)^3 / 12$. -/
theorem abs_amplificationFactor_half_sub_exp_le {a Δt : ℝ} (ha : 0 ≤ a) (hΔt : 0 ≤ Δt) :
    |amplificationFactor (1 / 2) a Δt - Real.exp (-(a * Δt))| ≤ (a * Δt) ^ 3 / 12 := by
  rw [amplificationFactor_eq]
  have hp : 0 ≤ a * Δt := mul_nonneg ha hΔt
  generalize a * Δt = p at hp ⊢
  have hden : 0 < 1 + 1 / 2 * p := by positivity
  have hderiv : ∀ x ∈ Set.Icc 0 p,
      HasDerivAt (fun t ↦ (1 + t / 2) * Real.exp (-t) - (1 - t / 2))
        ((1 - (1 + x) * Real.exp (-x)) / 2) x := by
    intro x _
    have h1 : HasDerivAt (fun t : ℝ ↦ 1 + t / 2) (1 / 2) x :=
      ((hasDerivAt_id x).div_const 2).const_add 1
    have h2 : HasDerivAt (fun t : ℝ ↦ Real.exp (-t)) (Real.exp (-x) * (-1)) x :=
      (hasDerivAt_id x).neg.exp
    have h3 : HasDerivAt (fun t : ℝ ↦ 1 - t / 2) (-(1 / 2)) x :=
      ((hasDerivAt_id x).div_const 2).const_sub 1
    convert (h1.mul h2).sub h3 using 1; ring
  have hnonneg : 0 ≤ (1 + p / 2) * Real.exp (-p) - (1 - p / 2) := by
    have hmono : MonotoneOn (fun t ↦ (1 + t / 2) * Real.exp (-t) - (1 - t / 2)) (Set.Icc 0 p) := by
      apply monotoneOn_of_deriv_nonneg (convex_Icc 0 p)
      · exact fun x hx ↦ (hderiv x hx).continuousAt.continuousWithinAt
      · exact fun x hx ↦ (hderiv x (interior_subset hx)).differentiableAt.differentiableWithinAt
      · intro x hx
        rw [(hderiv x (interior_subset hx)).deriv]
        linarith [one_add_mul_exp_neg_le_one x]
    have := hmono ⟨le_rfl, hp⟩ ⟨hp, le_rfl⟩ hp
    simp at this
    linarith
  have hupper : (1 + p / 2) * Real.exp (-p) - (1 - p / 2) ≤ p ^ 3 / 12 := by
    have hd2 : ∀ x ∈ Set.Icc 0 p,
        HasDerivAt (fun t ↦ t ^ 3 / 12 - ((1 + t / 2) * Real.exp (-t) - (1 - t / 2)))
          (x ^ 2 / 4 - (1 - (1 + x) * Real.exp (-x)) / 2) x := by
      intro x hx
      have hcube : HasDerivAt (fun t : ℝ ↦ t ^ 3 / 12) (x ^ 2 / 4) x := by
        convert (hasDerivAt_pow 3 x).div_const 12 using 1; ring
      exact hcube.sub (hderiv x hx)
    have hmono : MonotoneOn (fun t ↦ t ^ 3 / 12 - ((1 + t / 2) * Real.exp (-t) - (1 - t / 2)))
        (Set.Icc 0 p) := by
      apply monotoneOn_of_deriv_nonneg (convex_Icc 0 p)
      · exact fun x hx ↦ (hd2 x hx).continuousAt.continuousWithinAt
      · exact fun x hx ↦ (hd2 x (interior_subset hx)).differentiableAt.differentiableWithinAt
      · intro x hx
        have hx0 : 0 ≤ x := (interior_subset hx).1
        rw [(hd2 x (interior_subset hx)).deriv]
        linarith [one_sub_one_add_mul_exp_neg_le hx0]
    have := hmono ⟨le_rfl, hp⟩ ⟨hp, le_rfl⟩ hp
    simp at this
    linarith
  have hdiff : Real.exp (-p) - (1 - (1 - 1 / 2) * p) / (1 + 1 / 2 * p) =
      ((1 + p / 2) * Real.exp (-p) - (1 - p / 2)) / (1 + 1 / 2 * p) := by
    field_simp
    ring
  rw [abs_sub_comm, hdiff, abs_of_nonneg (div_nonneg hnonneg hden.le)]
  exact (div_le_self hnonneg (by linarith)).trans hupper

private lemma abs_pow_sub_pow_le_of_le_one {x y : ℝ} (hx : |x| ≤ 1) (hy : |y| ≤ 1) (n : ℕ) :
    |x ^ n - y ^ n| ≤ n * |x - y| := by
  refine (abs_pow_sub_pow_le x y n).trans ?_
  rw [mul_comm (|x - y|)]
  exact mul_le_of_le_one_right (by positivity) (pow_le_one₀ (le_max_iff.mpr (Or.inl
    (abs_nonneg x))) (max_le hx hy))

private lemma abs_sub_exp_le_aux {θ a Δt : ℝ} {u : ℕ → ℝ} (hu : IsSolution θ a Δt u)
    (hθ : 0 ≤ θ) (ha : 0 ≤ a) (hΔt : 0 < Δt) (hstab : (1 - 2 * θ) * a * Δt ≤ 2) (n : ℕ) :
    |u n - u 0 * Real.exp (-a * (n * Δt))| ≤
      |u 0| * (n * |amplificationFactor θ a Δt - Real.exp (-(a * Δt))|) := by
  have hexp : Real.exp (-a * (n * Δt)) = Real.exp (-(a * Δt)) ^ n := by
    rw [← Real.exp_nat_mul]
    ring_nf
  rw [hu.eq hθ ha hΔt, hexp, ← mul_sub, abs_mul]
  refine mul_le_mul_of_nonneg_left (abs_pow_sub_pow_le_of_le_one
    ((abs_amplificationFactor_le_one_iff hθ ha hΔt.le).mpr hstab) ?_ n) (abs_nonneg _)
  rw [abs_of_pos (Real.exp_pos _)]
  exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr (mul_nonneg ha hΔt.le))

/-- **Global error of the θ-rule.** Let $u$ solve the θ-rule with $\theta, a \ge 0$, $\Delta t > 0$
and $(1 - 2 \theta) a \Delta t \le 2$, and let $t_n = n \Delta t$. Then
$|u^n - u^0 e^{-a t_n}| \le \max(\theta - 1/2, 1/2) |u^0| a^2 t_n \Delta t$ for every $n$. -/
theorem IsSolution.abs_sub_exp_le {θ a Δt : ℝ} {u : ℕ → ℝ} (hu : IsSolution θ a Δt u)
    (hθ : 0 ≤ θ) (ha : 0 ≤ a) (hΔt : 0 < Δt) (hstab : (1 - 2 * θ) * a * Δt ≤ 2) (n : ℕ) :
    |u n - u 0 * Real.exp (-a * (n * Δt))| ≤
      max (θ - 1 / 2) (1 / 2) * |u 0| * a ^ 2 * (n * Δt) * Δt := by
  refine (abs_sub_exp_le_aux hu hθ ha hΔt hstab n).trans ?_
  have := abs_amplificationFactor_sub_exp_le hθ ha hΔt.le
  calc |u 0| * (n * |amplificationFactor θ a Δt - Real.exp (-(a * Δt))|)
      ≤ |u 0| * (n * (max (θ - 1 / 2) (1 / 2) * (a * Δt) ^ 2)) := by gcongr
    _ = max (θ - 1 / 2) (1 / 2) * |u 0| * a ^ 2 * (n * Δt) * Δt := by ring

/-- **Global error of the Crank–Nicolson scheme.** Let $u$ solve the θ-rule with $\theta = 1/2$,
$a \ge 0$ and $\Delta t > 0$, and let $t_n = n \Delta t$. Then
$|u^n - u^0 e^{-a t_n}| \le |u^0| a^3 t_n \Delta t^2 / 12$ for every $n$. -/
theorem IsSolution.abs_sub_exp_le_of_half {a Δt : ℝ} {u : ℕ → ℝ} (hu : IsSolution (1 / 2) a Δt u)
    (ha : 0 ≤ a) (hΔt : 0 < Δt) (n : ℕ) :
    |u n - u 0 * Real.exp (-a * (n * Δt))| ≤ |u 0| * a ^ 3 * (n * Δt) * Δt ^ 2 / 12 := by
  refine (abs_sub_exp_le_aux hu (by norm_num) ha hΔt (by norm_num) n).trans ?_
  have := abs_amplificationFactor_half_sub_exp_le ha hΔt.le
  calc |u 0| * (n * |amplificationFactor (1 / 2) a Δt - Real.exp (-(a * Δt))|)
      ≤ |u 0| * (n * ((a * Δt) ^ 3 / 12)) := by gcongr
    _ = |u 0| * a ^ 3 * (n * Δt) * Δt ^ 2 / 12 := by ring

/-- **Convergence of the θ-rule.** Let $\theta, a \ge 0$ and $t > 0$. If, for every $n \ge 1$, $u_n$
solves the θ-rule with time step $t / n$ and $u_n^0 = I$, then $u_n^n \to I e^{-a t}$ as
$n \to \infty$. -/
theorem tendsto_of_isSolution {θ a t I : ℝ} {u : ℕ → ℕ → ℝ} (hθ : 0 ≤ θ) (ha : 0 ≤ a)
    (ht : 0 < t) (hu : ∀ n : ℕ, 0 < n → IsSolution θ a (t / n) (u n))
    (hI : ∀ n : ℕ, 0 < n → u n 0 = I) :
    Tendsto (fun n ↦ u n n) atTop (𝓝 (I * Real.exp (-a * t))) := by
  have hstab : ∀ᶠ n : ℕ in atTop, (1 - 2 * θ) * a * (t / n) ≤ 2 := by
    have := (tendsto_const_div_atTop_nhds_zero_nat ((1 - 2 * θ) * a * t)).eventually
      (ge_mem_nhds (by norm_num : (0 : ℝ) < 2))
    filter_upwards [this] with n hn
    rwa [mul_div_assoc] at hn
  have hbound : ∀ᶠ n : ℕ in atTop,
      |u n n - I * Real.exp (-a * t)| ≤ max (θ - 1 / 2) (1 / 2) * |I| * a ^ 2 * t * t / n := by
    filter_upwards [hstab, eventually_gt_atTop 0] with n hn hn0
    have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn0.ne'
    have hΔt : 0 < t / n := div_pos ht (Nat.cast_pos.mpr hn0)
    have h := (hu n hn0).abs_sub_exp_le hθ ha hΔt hn n
    rw [hI n hn0, mul_div_cancel₀ t hn'] at h
    exact h.trans_eq (by ring)
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun _ ↦ norm_nonneg _) ?_
    (tendsto_const_div_atTop_nhds_zero_nat (max (θ - 1 / 2) (1 / 2) * |I| * a ^ 2 * t * t))
  filter_upwards [hbound] with n hn
  rwa [Real.norm_eq_abs]

end MathlibExt.Analysis.ODE.TimeStepping.ThetaRule

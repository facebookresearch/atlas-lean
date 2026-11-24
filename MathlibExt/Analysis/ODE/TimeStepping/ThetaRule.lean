/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Mul
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
`I e^{-a t_n} = I (e^{-a Δt})^n`. Apart from the algebraic solution formula, the results below
assume `θ ≥ 0` and `a ≥ 0` (strictly positive `a` for the decay criterion).

## Main results

* `ThetaRule.isSolution_iff`: `u` solves the scheme iff `u^n = u^0 A^n`.
* `ThetaRule.amplificationFactor_neg_iff`, `ThetaRule.IsSolution.sign_of_one_lt`,
  `ThetaRule.IsSolution.antitone_of_le_one`: `A < 0` iff `(1 - θ) a Δt > 1`. For `I > 0`, the
  numerical solution then changes sign at every step; if `(1 - θ) a Δt ≤ 1`, it is nonnegative
  and nonincreasing.
* `ThetaRule.abs_amplificationFactor_le_one_iff`, `ThetaRule.abs_amplificationFactor_lt_one_iff`,
  `ThetaRule.IsSolution.abs_le_iff`, `ThetaRule.IsSolution.tendsto_zero_iff`,
  `ThetaRule.IsSolution.tendsto_abs_atTop`: `|A| ≤ 1` iff `(1 - 2θ) a Δt ≤ 2`, which always holds
  for `θ ≥ 1 / 2`. For `I ≠ 0`, the numerical solution never exceeds `|I|` in absolute value iff
  this holds. For `a > 0` and `I ≠ 0`, it tends to `0` iff `(1 - 2θ) a Δt < 2`. For `I ≠ 0` and
  `(1 - 2θ) a Δt > 2`, its absolute value tends to infinity.
* `ThetaRule.abs_amplificationFactor_sub_exp_le`,
  `ThetaRule.abs_amplificationFactor_half_sub_exp_le`: `|A - e^{-a Δt}|` is at most
  `max θ (1/2) (a Δt)^2`, and at most `(a Δt)^3 / 4` for Crank–Nicolson.
* `ThetaRule.IsSolution.abs_sub_exp_le`, `ThetaRule.IsSolution.abs_sub_exp_le_of_half`,
  `ThetaRule.tendsto_of_isSolution`: the global error `|u^n - I e^{-a t_n}|` is at most
  `max θ (1/2) |I| a^2 t_n Δt` if `(1 - 2θ) a Δt ≤ 2`, and at most `|I| a^3 t_n Δt^2 / 4` for
  Crank–Nicolson, so the numerical solution at a fixed time `t > 0` tends to `I e^{-a t}` as the
  number of steps tends to infinity, using step `t / n` and initial value `I` for every `n ≥ 1`.

The error bounds give upper rates, not signed asymptotics or leading coefficients.

## References

* H. P. Langtangen, *Finite Difference Computing with Exponential Decay Models*, Springer,
  2016: Sections 1.1.5 and 1.1.6 (the θ-rule on a uniform grid), Sections 2.2.1 and 2.2.2 (exact
  numerical solution and stability), Sections 2.3.2 and 2.3.4 (amplification factors and global
  error).
-/

@[expose] public section

open Filter Topology

namespace ThetaRule

/-- **Amplification factor of the θ-rule.** For real $\theta, a, \Delta t$, set
$A = \frac{1 - (1 - \theta) a \Delta t}{1 + \theta a \Delta t}$, with division by zero defined to
be zero. If $\Delta t \ne 0$ and $1 + \theta a \Delta t \ne 0$, one step of the θ-rule for
$u' = -a u$ multiplies the numerical solution by $A$. -/
noncomputable def amplificationFactor (θ a Δt : ℝ) : ℝ :=
  (1 - (1 - θ) * a * Δt) / (1 + θ * a * Δt)

/-- **Solution of the θ-rule.** For real $\theta, a, \Delta t$, a sequence $u$ indexed by the
natural numbers solves the θ-rule if and only if
$\frac{u^{n+1} - u^n}{\Delta t} = -a (\theta u^{n+1} + (1 - \theta) u^n)$ for every $n \ge 0$.
The step is constant, and the quotient is zero if $\Delta t = 0$. The predicate does not impose an
initial value. -/
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

private lemma exp_neg_le {p : ℝ} (hp : 0 ≤ p) : Real.exp (-p) ≤ 1 - p + p ^ 2 / 2 := by
  have hd : ∀ x : ℝ, HasDerivAt (fun x ↦ Real.exp x * (1 - x + x ^ 2 / 2))
      (Real.exp x * (x ^ 2 / 2)) x := by
    intro x
    have h1 : HasDerivAt (fun x : ℝ ↦ 1 - x + x ^ 2 / 2) (-1 + x) x :=
      HasDerivAt.congr_deriv (HasDerivAt.add (HasDerivAt.const_sub 1 (hasDerivAt_id' x))
        (HasDerivAt.div_const (hasDerivAt_pow 2 x) 2)) (by norm_num)
    convert (Real.hasDerivAt_exp x).mul h1 using 1
    ring
  have hmono : Monotone fun x ↦ Real.exp x * (1 - x + x ^ 2 / 2) :=
    monotone_of_deriv_nonneg (fun x ↦ (hd x).differentiableAt) fun x ↦ by
      rw [(hd x).deriv]
      positivity
  have h := hmono hp
  simp only [Real.exp_zero, one_mul] at h
  have hexp : Real.exp (-p) * Real.exp p = 1 := by
    rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  nlinarith [Real.exp_pos (-p)]

private lemma le_exp_neg {p : ℝ} (hp : 0 ≤ p) :
    1 - p + p ^ 2 / 2 - p ^ 3 / 6 ≤ Real.exp (-p) := by
  have hd : ∀ x : ℝ, HasDerivAt (fun x ↦ Real.exp x * (1 - x + x ^ 2 / 2 - x ^ 3 / 6))
      (-(Real.exp x * (x ^ 3 / 6))) x := by
    intro x
    have h1 : HasDerivAt (fun x : ℝ ↦ 1 - x + x ^ 2 / 2 - x ^ 3 / 6) (-1 + x - x ^ 2 / 2) x :=
      HasDerivAt.congr_deriv (HasDerivAt.sub (HasDerivAt.add (HasDerivAt.const_sub 1
        (hasDerivAt_id' x)) (HasDerivAt.div_const (hasDerivAt_pow 2 x) 2))
        (HasDerivAt.div_const (hasDerivAt_pow 3 x) 6)) (by norm_num; ring)
    convert (Real.hasDerivAt_exp x).mul h1 using 1
    ring
  have hanti : AntitoneOn (fun x ↦ Real.exp x * (1 - x + x ^ 2 / 2 - x ^ 3 / 6)) (Set.Ici 0) :=
    antitoneOn_of_deriv_nonpos (convex_Ici 0)
      (fun x _ ↦ (hd x).continuousAt.continuousWithinAt)
      (fun x _ ↦ (hd x).differentiableAt.differentiableWithinAt) fun x hx ↦ by
        rw [interior_Ici] at hx
        rw [(hd x).deriv, neg_nonpos]
        have : 0 < x := hx
        positivity
  have h := hanti Set.self_mem_Ici hp hp
  simp only [Real.exp_zero, one_mul] at h
  have hexp : Real.exp (-p) * Real.exp p = 1 := by
    rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  nlinarith [Real.exp_pos (-p), Real.exp_pos p]

private lemma abs_sub_le_of_nonneg {x y c : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hxc : x ≤ c)
    (hyc : y ≤ c) : |x - y| ≤ c := by
  rw [abs_sub_le_iff]
  constructor <;> linarith

/-- **Accuracy of the θ-rule amplification factor.** For $\theta, a, \Delta t \ge 0$, the
amplification factor satisfies $|A - e^{-a \Delta t}| \le \max(\theta, 1/2) (a \Delta t)^2$. -/
theorem abs_amplificationFactor_sub_exp_le {θ a Δt : ℝ} (hθ : 0 ≤ θ) (ha : 0 ≤ a)
    (hΔt : 0 ≤ Δt) :
    |amplificationFactor θ a Δt - Real.exp (-(a * Δt))| ≤ max θ (1 / 2) * (a * Δt) ^ 2 := by
  rw [amplificationFactor_eq]
  have hp : 0 ≤ a * Δt := mul_nonneg ha hΔt
  generalize a * Δt = p at hp ⊢
  have hden : 0 < 1 + θ * p := by positivity
  have hA : (1 - (1 - θ) * p) / (1 + θ * p) - (1 - p) = θ * p ^ 2 / (1 + θ * p) := by
    field_simp
    ring
  have hx0 : 0 ≤ θ * p ^ 2 / (1 + θ * p) := by positivity
  have hx : θ * p ^ 2 / (1 + θ * p) ≤ max θ (1 / 2) * p ^ 2 :=
    (div_le_self (by positivity) (by nlinarith [mul_nonneg hθ hp])).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
  have hy0 : 0 ≤ Real.exp (-p) - (1 - p) := by linarith [Real.one_sub_le_exp_neg p]
  have hy : Real.exp (-p) - (1 - p) ≤ max θ (1 / 2) * p ^ 2 := by
    have := exp_neg_le hp
    have := mul_le_mul_of_nonneg_right (le_max_right θ (1 / 2)) (sq_nonneg p)
    linarith
  have := abs_sub_le_of_nonneg hx0 hy0 hx hy
  rwa [← hA, sub_sub_sub_cancel_right] at this

/-- **Accuracy of the Crank–Nicolson amplification factor.** For $\theta = 1/2$ and
$a, \Delta t \ge 0$, the amplification factor satisfies
$|A - e^{-a \Delta t}| \le (a \Delta t)^3 / 4$. -/
theorem abs_amplificationFactor_half_sub_exp_le {a Δt : ℝ} (ha : 0 ≤ a) (hΔt : 0 ≤ Δt) :
    |amplificationFactor (1 / 2) a Δt - Real.exp (-(a * Δt))| ≤ (a * Δt) ^ 3 / 4 := by
  rw [amplificationFactor_eq]
  have hp : 0 ≤ a * Δt := mul_nonneg ha hΔt
  generalize a * Δt = p at hp ⊢
  have hden : 0 < 1 + 1 / 2 * p := by positivity
  have hA : (1 - p + p ^ 2 / 2) - (1 - (1 - 1 / 2) * p) / (1 + 1 / 2 * p) =
      p ^ 3 / 4 / (1 + 1 / 2 * p) := by
    field_simp
    ring
  have hw0 : 0 ≤ p ^ 3 / 4 / (1 + 1 / 2 * p) := by positivity
  have hw : p ^ 3 / 4 / (1 + 1 / 2 * p) ≤ p ^ 3 / 4 :=
    div_le_self (by positivity) (by linarith)
  have hz0 : 0 ≤ (1 - p + p ^ 2 / 2) - Real.exp (-p) := by linarith [exp_neg_le hp]
  have hz : (1 - p + p ^ 2 / 2) - Real.exp (-p) ≤ p ^ 3 / 4 := by
    linarith [le_exp_neg hp, pow_nonneg hp 3]
  have := abs_sub_le_of_nonneg hz0 hw0 hz hw
  rwa [← hA, sub_sub_sub_cancel_left] at this

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
$|u^n - u^0 e^{-a t_n}| \le \max(\theta, 1/2) |u^0| a^2 t_n \Delta t$ for every $n$. -/
theorem IsSolution.abs_sub_exp_le {θ a Δt : ℝ} {u : ℕ → ℝ} (hu : IsSolution θ a Δt u)
    (hθ : 0 ≤ θ) (ha : 0 ≤ a) (hΔt : 0 < Δt) (hstab : (1 - 2 * θ) * a * Δt ≤ 2) (n : ℕ) :
    |u n - u 0 * Real.exp (-a * (n * Δt))| ≤
      max θ (1 / 2) * |u 0| * a ^ 2 * (n * Δt) * Δt := by
  refine (abs_sub_exp_le_aux hu hθ ha hΔt hstab n).trans ?_
  have := abs_amplificationFactor_sub_exp_le hθ ha hΔt.le
  calc |u 0| * (n * |amplificationFactor θ a Δt - Real.exp (-(a * Δt))|)
      ≤ |u 0| * (n * (max θ (1 / 2) * (a * Δt) ^ 2)) := by gcongr
    _ = max θ (1 / 2) * |u 0| * a ^ 2 * (n * Δt) * Δt := by ring

/-- **Global error of the Crank–Nicolson scheme.** Let $u$ solve the θ-rule with $\theta = 1/2$,
$a \ge 0$ and $\Delta t > 0$, and let $t_n = n \Delta t$. Then
$|u^n - u^0 e^{-a t_n}| \le |u^0| a^3 t_n \Delta t^2 / 4$ for every $n$. -/
theorem IsSolution.abs_sub_exp_le_of_half {a Δt : ℝ} {u : ℕ → ℝ} (hu : IsSolution (1 / 2) a Δt u)
    (ha : 0 ≤ a) (hΔt : 0 < Δt) (n : ℕ) :
    |u n - u 0 * Real.exp (-a * (n * Δt))| ≤ |u 0| * a ^ 3 * (n * Δt) * Δt ^ 2 / 4 := by
  refine (abs_sub_exp_le_aux hu (by norm_num) ha hΔt (by norm_num) n).trans ?_
  have := abs_amplificationFactor_half_sub_exp_le ha hΔt.le
  calc |u 0| * (n * |amplificationFactor (1 / 2) a Δt - Real.exp (-(a * Δt))|)
      ≤ |u 0| * (n * ((a * Δt) ^ 3 / 4)) := by gcongr
    _ = |u 0| * a ^ 3 * (n * Δt) * Δt ^ 2 / 4 := by ring

/-- **Convergence of the θ-rule.** Let $\theta, a \ge 0$ and $t > 0$. If, for every $n \ge 1$, $u_n$
solves the θ-rule with time step $t / n$ and $u_n^0 = I$, then $u_n^n \to I e^{-a t}$ as
$n \to \infty$. No condition is imposed on $u_0$. -/
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
      |u n n - I * Real.exp (-a * t)| ≤ max θ (1 / 2) * |I| * a ^ 2 * t * t / n := by
    filter_upwards [hstab, eventually_gt_atTop 0] with n hn hn0
    have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn0.ne'
    have hΔt : 0 < t / n := div_pos ht (Nat.cast_pos.mpr hn0)
    have h := (hu n hn0).abs_sub_exp_le hθ ha hΔt hn n
    rw [hI n hn0, mul_div_cancel₀ t hn'] at h
    exact h.trans_eq (by ring)
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun _ ↦ norm_nonneg _) ?_
    (tendsto_const_div_atTop_nhds_zero_nat (max θ (1 / 2) * |I| * a ^ 2 * t * t))
  filter_upwards [hbound] with n hn
  rwa [Real.norm_eq_abs]

end ThetaRule

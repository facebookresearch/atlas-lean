/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Biology.Dynamics.Logistic
public import MathlibExt.Biology.Epidemiology.NextGenerationMatrix
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.FinCases

/-!
# The closed-population SIS epidemic model

A closed population of size `N` (no births, deaths or migration) is split into susceptible `S`
and infectious `I` individuals. Infectives recover at rate `γ` without immunity and return to the
susceptible class; with transmission rate `β` the SIS model is

  `S' = -β S I / N + γ I`,   `I' = β S I / N - γ I`.

The epidemiological parameter domain is `β ≥ 0`, `γ > 0`, `N > 0`, with `S + I = N`. The basic
reproduction number is `R₀ = β / γ` and, for `β > γ`, the endemic level is
`I* = N (1 - γ / β)`.

With `S = N - I` the infected class obeys the logistic (Bernoulli) equation
`I' = (β - γ) I - (β / N) I²`, whose solution is explicit. Writing `r = β - γ` and
`φ_r(t) = ∫₀ᵗ e^{r s} ds` (`= (e^{r t} - 1) / r` for `r ≠ 0`, `= t` for `r = 0`),

  `I(t) = I₀ e^{r t} / (1 + (β I₀ / N) φ_r(t))`.

Since `φ_r(t) ≥ 0` for `t ≥ 0` whatever the sign of `r`, the denominator is at least `1` on
`[0, ∞)`; one formula covers `β > γ`, `β < γ`, `β = γ` and `β = 0`. For `β ≠ 0` and `β ≠ γ`
it is the logistic solution `MathlibExt.Biology.Dynamics.Logistic.logistic` with carrying
capacity `K = N (β - γ) / β` (negative when `β < γ`); the two degenerate cases `β = γ`
(`K = 0`) and `β = 0` (`K` undefined) are outside that parametrization, which is why the
formula here is stated through `φ_r`.

## Main results

* `IsSolution β γ N S I`: `(S, I)` solves the SIS system for `t ≥ 0`.
* `IsSolution.total_eq`: `S + I` is constant.
* `IsSolution.deriv_infected_pos_iff`: the threshold `I'(0) > 0 ↔ R₀ S(0) / N > 1`.
* `IsSolution.hasDerivAt_infected_logistic`: reduction to the logistic equation.
* `sisInfected`, `hasDerivAt_sisInfected`, `sisInfected_mem_Icc`: the explicit solution.
* `exists_isSolution`: global existence for every `I₀ ∈ [0, N]`, with `I(t) ∈ [0, N]`.
* `IsSolution.infected_eq_sisInfected`: forward uniqueness; every solution with
  `S(0) + I(0) = N` is the explicit one.
* `tendsto_sisInfected_endemic`, `tendsto_sisInfected_zero` and their `IsSolution` versions:
  `I(t) → N (1 - γ / β)` if `β > γ` and `I(0) > 0`; `I(t) → 0` if `β ≤ γ`.
* `isSolution_const_zero`, `isSolution_const_endemic`: the two equilibria.
* `R0_eq`, `isHurwitz_iff`, `exists_re_pos_iff`: the next-generation matrix `F = (β)`,
  `V = (γ)` gives `R₀ = β / γ`, and the linearized threshold `β < γ` / `β > γ`.

## References

* H. W. Hethcote, *The mathematics of infectious diseases*, SIAM Review 42 (2000) 599–653, §3.
* P. van den Driessche and J. Watmough, *Reproduction numbers and sub-threshold endemic
  equilibria for compartmental models of disease transmission*, Math. Biosci. 180 (2002)
  29–48.
-/

@[expose] public section

open Real Filter Set Matrix
open scoped Topology

namespace MathlibExt.Biology.Epidemiology.SIS

/-- `(S, I)` solves the closed-population SIS system with transmission rate `β`, recovery rate
`γ` and population size `N` for all times `t ≥ 0`:
`S' = -β S I / N + γ I`, `I' = β S I / N - γ I`. -/
structure IsSolution (β γ N : ℝ) (S I : ℝ → ℝ) : Prop where
  /-- Susceptibles are infected at rate `β S I / N` and regained by recovery at rate `γ I`. -/
  hasDerivAt_susceptible : ∀ t, 0 ≤ t → HasDerivAt S (-(β * S t * I t / N) + γ * I t) t
  /-- Infectives gain new infections and recover at rate `γ`. -/
  hasDerivAt_infected : ∀ t, 0 ≤ t → HasDerivAt I (β * S t * I t / N - γ * I t) t

/-- A function with zero derivative on `[0, ∞)` is constant there. -/
private theorem eq_zero_of_hasDerivAt {F : ℝ → ℝ} (hF : ∀ t, 0 ≤ t → HasDerivAt F 0 t)
    {t : ℝ} (ht : 0 ≤ t) : F t = F 0 :=
  constant_of_has_deriv_right_zero (b := t)
    (fun s hs => (hF s hs.1).continuousAt.continuousWithinAt)
    (fun s hs => (hF s hs.1).hasDerivWithinAt) t ⟨ht, le_rfl⟩

namespace IsSolution

variable {β γ N : ℝ} {S I : ℝ → ℝ}

/-- **Conservation of the population.** Along a solution, `S + I` is constant on `[0, ∞)`. -/
theorem total_eq (h : IsSolution β γ N S I) {t : ℝ} (ht : 0 ≤ t) :
    S t + I t = S 0 + I 0 :=
  eq_zero_of_hasDerivAt (F := fun s => S s + I s) (fun s hs => by
    convert (h.hasDerivAt_susceptible s hs).add (h.hasDerivAt_infected s hs) using 1
    ring) ht

/-- **Threshold theorem.** If initially `I(0) > 0`, with `γ > 0` and `N > 0`, the number of
infectives initially increases, `I'(0) > 0`, iff `R₀ S(0) / N > 1` with `R₀ = β / γ`. -/
theorem deriv_infected_pos_iff (h : IsSolution β γ N S I) (hγ : 0 < γ) (hN : 0 < N)
    (hI : 0 < I 0) : 0 < deriv I 0 ↔ 1 < β / γ * S 0 / N := by
  rw [(h.hasDerivAt_infected 0 le_rfl).deriv]
  have hfac : β * S 0 * I 0 / N - γ * I 0 = γ * I 0 * (β / γ * S 0 / N - 1) := by
    field_simp
  rw [hfac, mul_pos_iff_of_pos_left (mul_pos hγ hI), sub_pos]

/-- **Reduction to the logistic equation.** If the population is `N = S(0) + I(0)` with
`N ≠ 0`, then `I' = (β - γ) I - (β / N) I²` on `[0, ∞)`. -/
theorem hasDerivAt_infected_logistic (h : IsSolution β γ N S I) (hN0 : N ≠ 0)
    (hN : S 0 + I 0 = N) {t : ℝ} (ht : 0 ≤ t) :
    HasDerivAt I ((β - γ) * I t - β / N * I t ^ 2) t := by
  have hS : S t = N - I t := by linarith [h.total_eq ht]
  convert h.hasDerivAt_infected t ht using 1
  rw [hS]
  field_simp
  ring

end IsSolution

/-! ### The explicit solution -/

/-- `φ_r(t) = ∫₀ᵗ e^{r s} ds` in closed form: `(e^{r t} - 1) / r` for `r ≠ 0` and `t` for
`r = 0`. It is the time variable of the explicit SIS solution `sisInfected`. -/
noncomputable def growthIntegral (r t : ℝ) : ℝ :=
  if r = 0 then t else (exp (r * t) - 1) / r

@[simp]
theorem growthIntegral_zero_left (t : ℝ) : growthIntegral 0 t = t := ite_eq_left rfl

theorem growthIntegral_of_ne_zero {r : ℝ} (hr : r ≠ 0) (t : ℝ) :
    growthIntegral r t = (exp (r * t) - 1) / r := ite_eq_right hr

@[simp]
theorem growthIntegral_zero_right (r : ℝ) : growthIntegral r 0 = 0 := by
  unfold growthIntegral; split_ifs <;> simp

/-- `e^{r t} = 1 + r φ_r(t)`. -/
theorem exp_eq_one_add_mul_growthIntegral (r t : ℝ) :
    exp (r * t) = 1 + r * growthIntegral r t := by
  rcases eq_or_ne r 0 with rfl | hr
  · simp
  · rw [growthIntegral_of_ne_zero hr]
    field_simp
    ring

/-- `φ_r' = e^{r t}`. -/
theorem hasDerivAt_growthIntegral (r t : ℝ) :
    HasDerivAt (growthIntegral r) (exp (r * t)) t := by
  rcases eq_or_ne r 0 with rfl | hr
  · have : growthIntegral 0 = id := funext growthIntegral_zero_left
    simpa [this] using hasDerivAt_id t
  · have he : HasDerivAt (fun s => exp (r * s)) (exp (r * t) * r) t := by
      simpa using ((hasDerivAt_id t).const_mul r).exp
    have : growthIntegral r = fun s => (exp (r * s) - 1) / r :=
      funext (growthIntegral_of_ne_zero hr)
    rw [this]
    convert (he.sub_const 1).div_const r using 1
    field_simp

/-- `φ_r(t) ≥ 0` for `t ≥ 0`, for either sign of `r`. -/
theorem growthIntegral_nonneg (r : ℝ) {t : ℝ} (ht : 0 ≤ t) : 0 ≤ growthIntegral r t := by
  rcases lt_trichotomy r 0 with hr | rfl | hr
  · rw [growthIntegral_of_ne_zero hr.ne]
    refine div_nonneg_of_nonpos ?_ hr.le
    rw [sub_nonpos, exp_le_one_iff]
    exact mul_nonpos_of_nonpos_of_nonneg hr.le ht
  · simpa using ht
  · rw [growthIntegral_of_ne_zero hr.ne']
    refine div_nonneg ?_ hr.le
    rw [sub_nonneg, one_le_exp_iff]
    positivity

/-- The **explicit SIS solution** for the infectives with initial value `I₀`:
`I(t) = I₀ e^{r t} / (1 + (β I₀ / N) φ_r(t))`, `r = β - γ`, `φ_r = growthIntegral r`.
For `r ≠ 0` this is `I₀ e^{r t} / (1 + (β I₀ / (N r)) (e^{r t} - 1))`; for `β = γ` it is
`I₀ / (1 + β I₀ t / N)`; for `β = 0` it is `I₀ e^{-γ t}`; for `I₀ = 0` it is `0`. -/
noncomputable def sisInfected (β γ N I₀ t : ℝ) : ℝ :=
  I₀ * exp ((β - γ) * t) / (1 + β * I₀ / N * growthIntegral (β - γ) t)

/-- The explicit solution starts at `I₀`. -/
@[simp]
theorem sisInfected_zero (β γ N I₀ : ℝ) : sisInfected β γ N I₀ 0 = I₀ := by
  simp [sisInfected]

/-- With no infectives the explicit solution is identically `0`. -/
@[simp]
theorem sisInfected_zero_left (β γ N t : ℝ) : sisInfected β γ N 0 t = 0 := by
  simp [sisInfected]

/-- **Denominator bound.** For `β, I₀ ≥ 0`, `N > 0` and `t ≥ 0` the denominator of
`sisInfected` is at least `1`, whatever the sign of `β - γ`, because `φ_r(t) ≥ 0`. -/
theorem one_le_sisDenom {β γ N I₀ t : ℝ} (hβ : 0 ≤ β) (hN : 0 < N) (hI₀ : 0 ≤ I₀)
    (ht : 0 ≤ t) : 1 ≤ 1 + β * I₀ / N * growthIntegral (β - γ) t := by
  have := growthIntegral_nonneg (β - γ) ht
  have : 0 ≤ β * I₀ / N := by positivity
  nlinarith

/-- **The explicit solution solves the reduced (logistic) equation**
`I' = (β - γ) I - (β / N) I²` wherever its denominator is nonzero (`N ≠ 0`). -/
theorem hasDerivAt_sisInfected {β γ N I₀ t : ℝ} (hN : N ≠ 0)
    (hden : 1 + β * I₀ / N * growthIntegral (β - γ) t ≠ 0) :
    HasDerivAt (sisInfected β γ N I₀)
      ((β - γ) * sisInfected β γ N I₀ t - β / N * sisInfected β γ N I₀ t ^ 2) t := by
  have he : HasDerivAt (fun s => exp ((β - γ) * s)) (exp ((β - γ) * t) * (β - γ)) t := by
    simpa using ((hasDerivAt_id t).const_mul (β - γ)).exp
  have hd : HasDerivAt (fun s => 1 + β * I₀ / N * growthIntegral (β - γ) s)
      (β * I₀ / N * exp ((β - γ) * t)) t := by
    simpa using ((hasDerivAt_growthIntegral (β - γ) t).const_mul (β * I₀ / N)).const_add 1
  refine ((he.const_mul I₀).div hd hden).congr_deriv ?_
  simp only [sisInfected]
  field_simp

/-- **Invariance of `[0, N]`.** For `β ≥ 0`, `γ ≥ 0`, `N > 0`, `I₀ ∈ [0, N]` and `t ≥ 0`, the
explicit solution stays in `[0, N]`. Upper bound: with `e^{r t} = 1 + r φ_r(t)`,
`I₀ e^{r t} ≤ N (1 + (β I₀ / N) φ_r(t))` reduces to `I₀ - N ≤ γ I₀ φ_r(t)`. -/
theorem sisInfected_mem_Icc {β γ N I₀ t : ℝ} (hβ : 0 ≤ β) (hγ : 0 ≤ γ) (hN : 0 < N)
    (hI₀ : I₀ ∈ Icc 0 N) (ht : 0 ≤ t) : sisInfected β γ N I₀ t ∈ Icc 0 N := by
  have hD := one_le_sisDenom (γ := γ) hβ hN hI₀.1 ht
  have hφ := growthIntegral_nonneg (β - γ) ht
  have he := exp_eq_one_add_mul_growthIntegral (β - γ) t
  refine ⟨div_nonneg (mul_nonneg hI₀.1 (exp_pos _).le) (by linarith), ?_⟩
  rw [sisInfected, div_le_iff₀ (by linarith), mul_add, mul_one, he]
  have hNβ : N * (β * I₀ / N * growthIntegral (β - γ) t) = β * I₀ * growthIntegral (β - γ) t := by
    field_simp
  rw [hNβ]
  nlinarith [mul_nonneg (mul_nonneg hγ hI₀.1) hφ, hI₀.2]

/-- `S = N - I` for the explicit solution. -/
noncomputable def sisSusceptible (β γ N I₀ t : ℝ) : ℝ :=
  N - sisInfected β γ N I₀ t

/-- **Global existence.** For `β ≥ 0`, `γ ≥ 0`, `N > 0` and every `I₀ ∈ [0, N]`, the explicit
pair `(N - I, I)` with `I = sisInfected β γ N I₀` solves the SIS system on `[0, ∞)`, starts at
`(N - I₀, I₀)`, and keeps `I(t) ∈ [0, N]`. -/
theorem isSolution_sis {β γ N I₀ : ℝ} (hβ : 0 ≤ β) (hN : 0 < N) (hI₀ : 0 ≤ I₀) :
    IsSolution β γ N (sisSusceptible β γ N I₀) (sisInfected β γ N I₀) := by
  have hd : ∀ t, 0 ≤ t → HasDerivAt (sisInfected β γ N I₀)
      ((β - γ) * sisInfected β γ N I₀ t - β / N * sisInfected β γ N I₀ t ^ 2) t :=
    fun t ht => hasDerivAt_sisInfected hN.ne'
      (by linarith [one_le_sisDenom (γ := γ) hβ hN hI₀ ht])
  refine ⟨fun t ht => ?_, fun t ht => ?_⟩
  · convert (hd t ht).const_sub N using 1
    · rfl
    · simp only [sisSusceptible]
      field_simp
      ring
  · convert hd t ht using 1
    simp only [sisSusceptible]
    field_simp
    ring

/-- **Global existence with invariance.** For `β ≥ 0`, `γ ≥ 0`, `N > 0` and every
`I₀ ∈ [0, N]` there is a solution `(S, I)` of the SIS system on `[0, ∞)` with `I(0) = I₀`,
`S(0) = N - I₀` and `I(t) ∈ [0, N]` for all `t ≥ 0` (explicitly, `I = sisInfected β γ N I₀`
and `S = N - I`). -/
theorem exists_isSolution {β γ N : ℝ} (hβ : 0 ≤ β) (hγ : 0 ≤ γ) (hN : 0 < N) {I₀ : ℝ}
    (hI₀ : I₀ ∈ Icc 0 N) :
    ∃ S I : ℝ → ℝ, IsSolution β γ N S I ∧ I 0 = I₀ ∧ S 0 = N - I₀ ∧
      ∀ t, 0 ≤ t → I t ∈ Icc 0 N :=
  ⟨_, _, isSolution_sis hβ hN hI₀.1, sisInfected_zero _ _ _ _,
    by simp [sisSusceptible], fun _ ht => sisInfected_mem_Icc hβ hγ hN hI₀ ht⟩

/-- The explicit solution is nonnegative on `[0, ∞)` for `β, I₀ ≥ 0`, `N > 0`. -/
theorem sisInfected_nonneg {β γ N I₀ t : ℝ} (hβ : 0 ≤ β) (hN : 0 < N) (hI₀ : 0 ≤ I₀)
    (ht : 0 ≤ t) : 0 ≤ sisInfected β γ N I₀ t :=
  div_nonneg (mul_nonneg hI₀ (exp_pos _).le)
    (by linarith [one_le_sisDenom (γ := γ) hβ hN hI₀ ht])

/-- The explicit solution is bounded by the linear solution `I₀ e^{(β - γ) t}` on `[0, ∞)`. -/
theorem sisInfected_le_mul_exp {β γ N I₀ t : ℝ} (hβ : 0 ≤ β) (hN : 0 < N) (hI₀ : 0 ≤ I₀)
    (ht : 0 ≤ t) : sisInfected β γ N I₀ t ≤ I₀ * exp ((β - γ) * t) :=
  div_le_self (mul_nonneg hI₀ (exp_pos _).le) (one_le_sisDenom hβ hN hI₀ ht)

/-- **Bridge to the logistic solution.** For `β ≠ 0`, `β ≠ γ` and `N ≠ 0` the explicit SIS
solution is the logistic solution with rate `r = β - γ` and carrying capacity
`K = N (β - γ) / β` (`= N (1 - γ / β)`, negative when `β < γ`). -/
theorem sisInfected_eq_logistic {β γ N : ℝ} (hβ : β ≠ 0) (hr : β - γ ≠ 0) (hN : N ≠ 0)
    (I₀ t : ℝ) :
    sisInfected β γ N I₀ t = Dynamics.Logistic.logistic (β - γ) (N * (β - γ) / β) I₀ t := by
  have hK : N * (β - γ) / β ≠ 0 := div_ne_zero (mul_ne_zero hN hr) hβ
  have hden : N * (β - γ) / β + I₀ * (exp ((β - γ) * t) - 1) =
      N * (β - γ) / β * (1 + β * I₀ / N * ((exp ((β - γ) * t) - 1) / (β - γ))) := by
    field_simp
  rw [Dynamics.Logistic.logistic, sisInfected, growthIntegral_of_ne_zero hr, hden, mul_assoc,
    mul_div_mul_left _ _ hK]

/-! ### Uniqueness -/

namespace IsSolution

variable {β γ N : ℝ} {S I : ℝ → ℝ}

/-- **Forward uniqueness of the infectives.** Two solutions with the same population
`S(0) + I(0) = N ≠ 0` and the same `I(0)` have the same `I` on `[0, ∞)`.

Proof: both `I`s solve the scalar equation `x' = (β - γ) x - (β / N) x²`
(`hasDerivAt_infected_logistic`); on `[0, t]` they are bounded, and the polynomial field is
Lipschitz on a closed ball containing both; apply `ODE_solution_unique_of_mem_Icc_right`. -/
theorem infected_eq_of_initial {S' I' : ℝ → ℝ} (h : IsSolution β γ N S I)
    (h' : IsSolution β γ N S' I') (hN0 : N ≠ 0) (hN : S 0 + I 0 = N) (hN' : S' 0 + I' 0 = N)
    (hI : I 0 = I' 0) {t : ℝ} (ht : 0 ≤ t) : I t = I' t := by
  have hd := fun s (hs : 0 ≤ s) => h.hasDerivAt_infected_logistic hN0 hN hs
  have hd' := fun s (hs : 0 ≤ s) => h'.hasDerivAt_infected_logistic hN0 hN' hs
  have hc : ContinuousOn I (Icc 0 t) := fun s hs => (hd s hs.1).continuousAt.continuousWithinAt
  have hc' : ContinuousOn I' (Icc 0 t) :=
    fun s hs => (hd' s hs.1).continuousAt.continuousWithinAt
  obtain ⟨C₁, hC₁⟩ := isCompact_Icc.exists_bound_of_continuousOn hc
  obtain ⟨C₂, hC₂⟩ := isCompact_Icc.exists_bound_of_continuousOn hc'
  have hf : ContDiff ℝ 1 (fun x : ℝ => (β - γ) * x - β / N * x ^ 2) := by fun_prop
  obtain ⟨K, hK⟩ := (hf.contDiffOn (s := Metric.closedBall 0 (max C₁ C₂))).exists_lipschitzOnWith
    one_ne_zero (convex_closedBall _ _) (isCompact_closedBall _ _)
  have heq := ODE_solution_unique_of_mem_Icc_right
    (v := fun _ x => (β - γ) * x - β / N * x ^ 2) (s := fun _ => Metric.closedBall 0 (max C₁ C₂))
    (fun _ _ => hK) hc (fun s hs => (hd s hs.1).hasDerivWithinAt)
    (fun s hs => mem_closedBall_zero_iff.2
      ((hC₁ s (Ico_subset_Icc_self hs)).trans (le_max_left _ _)))
    hc' (fun s hs => (hd' s hs.1).hasDerivWithinAt)
    (fun s hs => mem_closedBall_zero_iff.2
      ((hC₂ s (Ico_subset_Icc_self hs)).trans (le_max_right _ _)))
    hI ⟨ht, le_rfl⟩
  exact heq

/-- **Every solution is the explicit one.** For `β ≥ 0`, `N > 0`, `S(0) + I(0) = N` and
`I(0) ≥ 0`, `I(t) = sisInfected β γ N (I 0) t` for all `t ≥ 0`. -/
theorem infected_eq_sisInfected (h : IsSolution β γ N S I) (hβ : 0 ≤ β) (hN : 0 < N)
    (hS : S 0 + I 0 = N) (hI0 : 0 ≤ I 0) {t : ℝ} (ht : 0 ≤ t) :
    I t = sisInfected β γ N (I 0) t :=
  h.infected_eq_of_initial (isSolution_sis hβ hN hI0) hN.ne' hS (by simp [sisSusceptible])
    (sisInfected_zero _ _ _ _).symm ht

end IsSolution

/-! ### Long-time behaviour -/

/-- **Endemic limit of the explicit solution.** If `0 ≤ γ < β` (`R₀ > 1`), `N ≠ 0` and
`I₀ > 0`, then `I(t) → I* = N (1 - γ / β)`. Via the logistic bridge and
`Dynamics.Logistic.tendsto_logistic_atTop`. -/
theorem tendsto_sisInfected_endemic {β γ N I₀ : ℝ} (hγ : 0 ≤ γ) (hγβ : γ < β) (hN : N ≠ 0)
    (hI₀ : 0 < I₀) : Tendsto (sisInfected β γ N I₀) atTop (𝓝 (N * (1 - γ / β))) := by
  have hβ : β ≠ 0 := by linarith
  have hr : 0 < β - γ := sub_pos.2 hγβ
  rw [funext (sisInfected_eq_logistic hβ hr.ne' hN I₀),
    show N * (1 - γ / β) = N * (β - γ) / β by field_simp]
  exact Dynamics.Logistic.tendsto_logistic_atTop hr hI₀

/-- **Extinction for the explicit solution.** If `0 ≤ β ≤ γ`, `γ > 0` (`R₀ ≤ 1`), `N > 0` and
`I₀ ≥ 0`, then `I(t) → 0`. For `β < γ`, `0 ≤ I(t) ≤ I₀ e^{(β - γ) t}`; for `β = γ`,
`0 ≤ I(t) = I₀ / (1 + β I₀ t / N) ≤ N / (β t)` (algebraic decay). This includes `β = 0`, where
`I(t) = I₀ e^{-γ t}`. -/
theorem tendsto_sisInfected_zero {β γ N I₀ : ℝ} (hβ : 0 ≤ β) (hγ : 0 < γ) (hβγ : β ≤ γ)
    (hN : 0 < N) (hI₀ : 0 ≤ I₀) : Tendsto (sisInfected β γ N I₀) atTop (𝓝 0) := by
  rcases hβγ.lt_or_eq with hlt | rfl
  · have he : Tendsto (fun t => exp (-((γ - β) * t))) atTop (𝓝 0) :=
      tendsto_exp_neg_atTop_nhds_zero.comp (tendsto_id.const_mul_atTop (sub_pos.2 hlt))
    have h1 : Tendsto (fun t => I₀ * exp ((β - γ) * t)) atTop (𝓝 0) := by
      have h := he.const_mul I₀
      rw [mul_zero] at h
      refine h.congr fun t => ?_
      rw [show -((γ - β) * t) = (β - γ) * t by ring]
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h1 ?_ ?_
    · filter_upwards [eventually_ge_atTop 0] with t ht using sisInfected_nonneg hβ hN hI₀ ht
    · filter_upwards [eventually_ge_atTop 0] with t ht using sisInfected_le_mul_exp hβ hN hI₀ ht
  · have h1 : Tendsto (fun t : ℝ => N / β * t⁻¹) atTop (𝓝 0) := by
      simpa using tendsto_inv_atTop_zero.const_mul (N / β)
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h1 ?_ ?_
    · filter_upwards [eventually_ge_atTop 0] with t ht using sisInfected_nonneg hβ hN hI₀ ht
    · filter_upwards [eventually_gt_atTop 0] with t ht
      have hD := one_le_sisDenom (γ := β) hβ hN hI₀ ht.le
      simp only [sisInfected, sub_self, zero_mul, exp_zero, mul_one,
        growthIntegral_zero_left] at hD ⊢
      rw [div_le_iff₀ (by linarith)]
      have key : N / β * t⁻¹ * (1 + β * I₀ / N * t) = N / β * t⁻¹ + I₀ := by
        field_simp
      have : 0 ≤ N / β * t⁻¹ := by positivity
      linarith

namespace IsSolution

variable {β γ N : ℝ} {S I : ℝ → ℝ}

/-- **Endemic limit (all solutions).** If `0 ≤ γ < β` (`R₀ > 1`), `N > 0`, `S(0) + I(0) = N`
and `I(0) > 0`, then `I(t) → I* = N (1 - γ / β)`. -/
theorem tendsto_infected_endemic (h : IsSolution β γ N S I) (hγ : 0 ≤ γ) (hγβ : γ < β)
    (hN : 0 < N) (hS : S 0 + I 0 = N) (hI0 : 0 < I 0) :
    Tendsto I atTop (𝓝 (N * (1 - γ / β))) :=
  (tendsto_sisInfected_endemic hγ hγβ hN.ne' hI0).congr' <| by
    filter_upwards [eventually_ge_atTop 0] with t ht
    exact (h.infected_eq_sisInfected (by linarith) hN hS hI0.le ht).symm

/-- **Extinction (all solutions).** If `0 ≤ β ≤ γ`, `γ > 0` (`R₀ ≤ 1`), `N > 0`,
`S(0) + I(0) = N` and `I(0) ≥ 0`, then `I(t) → 0`. -/
theorem tendsto_infected_zero (h : IsSolution β γ N S I) (hβ : 0 ≤ β) (hγ : 0 < γ)
    (hβγ : β ≤ γ) (hN : 0 < N) (hS : S 0 + I 0 = N) (hI0 : 0 ≤ I 0) :
    Tendsto I atTop (𝓝 0) :=
  (tendsto_sisInfected_zero hβ hγ hβγ hN hI0).congr' <| by
    filter_upwards [eventually_ge_atTop 0] with t ht
    exact (h.infected_eq_sisInfected hβ hN hS hI0 ht).symm

end IsSolution

/-! ### Equilibria -/

/-- The **disease-free equilibrium** `(S, I) ≡ (N, 0)` is a solution. -/
theorem isSolution_const_zero (β γ N : ℝ) : IsSolution β γ N (fun _ => N) (fun _ => 0) :=
  ⟨fun t _ => by simpa using hasDerivAt_const t N,
    fun t _ => by simpa using hasDerivAt_const t (0 : ℝ)⟩

/-- The **endemic equilibrium** `(S, I) ≡ (N γ / β, N (1 - γ / β))` is a solution for every
`β ≠ 0`; for `N > 0` it is biologically meaningful (`0 < I* < N`) exactly when `β > γ > 0`. -/
theorem isSolution_const_endemic {β γ N : ℝ} (hβ : β ≠ 0) :
    IsSolution β γ N (fun _ => N * γ / β) (fun _ => N * (1 - γ / β)) := by
  refine ⟨fun t _ => ?_, fun t _ => ?_⟩ <;> convert hasDerivAt_const t _ using 1 <;>
    field_simp <;> ring

/-! ### The next-generation matrix at the disease-free equilibrium

SIS has one infected compartment. At the disease-free equilibrium `(S, I) = (N, 0)` the rate of
new infections is `ℱ = β S I / N`, with `∂ℱ/∂I = β S / N = β` at `S = N`, and the other
transfers are `𝒱 = γ I`, `∂𝒱/∂I = γ`; so `F = (β)` and `V = (γ)`. The results below are the
**local, linearized** threshold of van den Driessche–Watmough: the sign of the single
eigenvalue `β - γ` of `F - V`. The **global** threshold behaviour of SIS (convergence to `0`
for `R₀ ≤ 1`, to `I*` for `R₀ > 1` and `I(0) > 0`) is proved separately above from the explicit
solution; it is specific to this scalar model and is not a consequence of the spectral
statements. -/

/-- A `1 × 1` matrix `!![c]` is the scalar matrix `c • 1`. -/
private theorem of_one_by_one (c : ℝ) : !![c] = c • (1 : Matrix (Fin 1) (Fin 1) ℝ) := by
  ext i j
  fin_cases i; fin_cases j
  simp

/-- The complex spectrum of a real scalar `1 × 1` matrix `c • 1` is `{c}`. -/
private theorem spectrum_smul_one (c : ℝ) :
    spectrum ℂ ((c • (1 : Matrix (Fin 1) (Fin 1) ℝ)).map (algebraMap ℝ ℂ)) = {(c : ℂ)} := by
  have : (c • (1 : Matrix (Fin 1) (Fin 1) ℝ)).map (algebraMap ℝ ℂ) =
      algebraMap ℂ (Matrix (Fin 1) (Fin 1) ℂ) (c : ℂ) := by
    ext i j
    fin_cases i; fin_cases j
    simp [Matrix.algebraMap_matrix_apply]
  rw [this, spectrum.scalar_eq]

/-- The complex spectrum of `!![c]` is `{c}`. -/
theorem spectrum_one_by_one (c : ℝ) :
    spectrum ℂ ((!![c] : Matrix (Fin 1) (Fin 1) ℝ).map (algebraMap ℝ ℂ)) = {(c : ℂ)} := by
  rw [of_one_by_one, spectrum_smul_one]

/-- `F = (β)` is entrywise nonnegative for `β ≥ 0`. -/
theorem ngmF_nonneg {β : ℝ} (hβ : 0 ≤ β) (i j : Fin 1) : 0 ≤ (!![β] : Matrix _ _ ℝ) i j := by
  fin_cases i; fin_cases j; simpa using hβ

/-- `V = (γ)` is a nonsingular M-matrix for `γ > 0`. -/
theorem ngmV_isNonsingularMMatrix {γ : ℝ} (hγ : 0 < γ) :
    (!![γ] : Matrix (Fin 1) (Fin 1) ℝ).IsNonsingularMMatrix := by
  refine ⟨fun i j hij => absurd (Subsingleton.elim i j) hij, fun μ hμ => ?_⟩
  rw [show -(!![γ] : Matrix (Fin 1) (Fin 1) ℝ) = !![-γ] by rw [of_one_by_one, of_one_by_one,
    neg_smul], spectrum_one_by_one, Set.mem_singleton_iff] at hμ
  simp [hμ, hγ]

/-- **`R₀ = β / γ` for SIS**: the spectral radius of the `1 × 1` next-generation matrix
`F V⁻¹ = (β / γ)` (`β ≥ 0`, `γ > 0`). Route: `F V⁻¹ = (β / γ) • 1` is a scalar matrix, its
spectrum is `{β / γ}` (`spectrum.scalar_eq`), and the spectral radius is the supremum of
`‖·‖` over `{β / γ} ∪ {0}`. -/
theorem R0_eq {β γ : ℝ} (hβ : 0 ≤ β) (hγ : 0 < γ) :
    NextGenerationMatrix.R0 !![β] !![γ] = β / γ := by
  have hinv : (γ • (1 : Matrix (Fin 1) (Fin 1) ℝ))⁻¹ = γ⁻¹ • 1 := by
    refine Matrix.inv_eq_left_inv ?_
    rw [smul_mul_smul, mul_one, inv_mul_cancel₀ hγ.ne', one_smul]
  have hK : β • (1 : Matrix (Fin 1) (Fin 1) ℝ) * (γ • 1)⁻¹ = (β / γ) • 1 := by
    rw [hinv, smul_mul_smul, mul_one, div_eq_mul_inv]
  rw [NextGenerationMatrix.R0, of_one_by_one, of_one_by_one, hK, spectralRadius,
    quasispectrum_eq_spectrum_union_zero, spectrum_smul_one, Set.union_singleton, iSup_insert,
    iSup_singleton]
  simp [abs_of_nonneg hβ, abs_of_pos hγ]

/-- **The infected-block Jacobian is `F - V`.** The reduced infected equation
`I' = (β - γ) I - (β / N) I²` has derivative `β - γ = (F - V)₀₀` at the disease-free state
`I = 0`. -/
theorem hasDerivAt_infectedField_zero (β γ N : ℝ) :
    HasDerivAt (fun x : ℝ => (β - γ) * x - β / N * x ^ 2)
      ((!![β] - !![γ] : Matrix (Fin 1) (Fin 1) ℝ) 0 0) 0 := by
  convert ((hasDerivAt_id (0 : ℝ)).const_mul (β - γ)).sub
    ((hasDerivAt_pow 2 (0 : ℝ)).const_mul (β / N)) using 1
  · funext x
    simp only [Pi.sub_apply, id]
  · simp

/-- **Linearized threshold, stable side.** For `β ≥ 0`, `γ > 0`, the eigenvalue `β - γ` of
`F - V` has negative real part iff `β < γ`, i.e. iff `R₀ < 1`
(`NextGenerationMatrix.isHurwitz_sub_iff_R0_lt_one` with `R0_eq`). This is the local spectral
statement only; global extinction is `IsSolution.tendsto_infected_zero`. -/
theorem isHurwitz_iff {β γ : ℝ} (hβ : 0 ≤ β) (hγ : 0 < γ) :
    (!![β] - !![γ] : Matrix (Fin 1) (Fin 1) ℝ).IsHurwitz ↔ β < γ := by
  rw [NextGenerationMatrix.isHurwitz_sub_iff_R0_lt_one (ngmF_nonneg hβ)
    (ngmV_isNonsingularMMatrix hγ), R0_eq hβ hγ, div_lt_one hγ]

/-- **Linearized threshold, unstable side.** For `β ≥ 0`, `γ > 0`, `F - V` has an eigenvalue
with positive real part iff `γ < β`, i.e. iff `R₀ > 1`
(`NextGenerationMatrix.exists_re_pos_iff_one_lt_R0` with `R0_eq`). This is the local spectral
statement only; global convergence to the endemic level is
`IsSolution.tendsto_infected_endemic`. -/
theorem exists_re_pos_iff {β γ : ℝ} (hβ : 0 ≤ β) (hγ : 0 < γ) :
    (∃ μ ∈ spectrum ℂ ((!![β] - !![γ] : Matrix (Fin 1) (Fin 1) ℝ).map (algebraMap ℝ ℂ)),
      0 < μ.re) ↔ γ < β := by
  rw [NextGenerationMatrix.exists_re_pos_iff_one_lt_R0 (ngmF_nonneg hβ)
    (ngmV_isNonsingularMMatrix hγ), R0_eq hβ hγ, one_lt_div hγ]

end MathlibExt.Biology.Epidemiology.SIS

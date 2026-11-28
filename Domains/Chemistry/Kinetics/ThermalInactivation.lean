/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Log-linear thermal inactivation under a time-varying temperature

In the log-linear model of thermal inactivation, the concentration `N` of a microbial
population decays at the first-order rate
`k(θ) = (ln 10 / D_ref) 10^((θ - T_ref)/z)` at temperature `θ`, where `D_ref` is the decimal
reduction time at the reference temperature `T_ref` and `z` is the `z`-value: the temperature
rise that divides the decimal reduction time by ten. Along a temperature history `T`, the
F-value `F(t) = ∫₀ᵗ 10^((T(s) - T_ref)/z) ds` is the time at `T_ref` with the same lethal
effect.

For a temperature history continuous on `[0, t_f]` and `N₀ > 0`, the function
`N(t) = N₀ exp(-∫₀ᵗ k(T(s)) ds)` is the unique solution on `[0, t_f]` of `N' = -k(T(t)) N` with
`N(0) = N₀`, it is positive, and `log₁₀(N₀ / N(t)) = F(t) / D_ref`. Derivatives on `[0, t_f]` are
taken within the interval, so they are one-sided at its endpoints when `0 < t_f`. When `t_f = 0`,
every value is a derivative within `{0}`, so the equation imposes no condition and uniqueness rests
on the initial value alone; when `t_f < 0` the interval is empty and only `N(0) = N₀` remains.

## Main definitions

* `Chemistry.Kinetics.ThermalInactivation.rate`: the inactivation rate `k(θ)`.
* `Chemistry.Kinetics.ThermalInactivation.fValue`: the F-value `F(t)` of a temperature history.

## Main results

* `Chemistry.Kinetics.ThermalInactivation.log_linear_inactivation`: existence, uniqueness and
  positivity of the solution, and the decimal reduction `log₁₀(N₀ / N(t)) = F(t) / D_ref`.

No sign condition on `D_ref` or `z` is needed (in the model both are positive), reading `x / 0`
as `0`. Uniqueness uses the integrating factor `exp(∫₀ᵗ k(T(s)) ds)`.
-/

@[expose] public section

open Real Set Filter

namespace Chemistry.Kinetics.ThermalInactivation

/-- **Log-linear inactivation rate.** The first-order inactivation rate at temperature $\theta$,
$k(\theta) = \frac{\ln 10}{D_{\mathrm{ref}}}\,10^{(\theta - T_{\mathrm{ref}})/z}$, for the decimal
reduction time $D_{\mathrm{ref}}$ at the reference temperature $T_{\mathrm{ref}}$ and the $z$-value
$z$. The parameters are real numbers, with $D_{\mathrm{ref}}, z > 0$ in the model; a division by
zero is read as $0$. -/
noncomputable def rate (Dref Tref z θ : ℝ) : ℝ :=
  Real.log 10 / Dref * (10 : ℝ) ^ ((θ - Tref) / z)

/-- **F-value of a temperature history.** For a temperature history $T$, the F-value up to time
$t$ is $F(t) = \int_0^t 10^{(T(s) - T_{\mathrm{ref}})/z}\,ds$: the time at the reference
temperature $T_{\mathrm{ref}}$ with the same lethal effect in the log-linear model with $z$-value
$z$. The integral is oriented, $F(t) = -\int_t^0 10^{(T(s) - T_{\mathrm{ref}})/z}\,ds$ for $t < 0$,
and it is $0$ when the integrand is not integrable between $0$ and $t$; a division by zero is read
as $0$. -/
noncomputable def fValue (Tref z : ℝ) (T : ℝ → ℝ) (t : ℝ) : ℝ :=
  ∫ s in (0 : ℝ)..t, (10 : ℝ) ^ ((T s - Tref) / z)

private theorem continuous_rate (Dref Tref z : ℝ) : Continuous (rate Dref Tref z) := by
  unfold rate
  fun_prop

/-- On `[0, t_f]`, the cumulative rate `∫₀ᵗ k(T(s)) ds` agrees with a primitive `G` of a
continuous function `k'` equal to `k ∘ T` there. -/
private theorem exists_primitive {Dref Tref z tf : ℝ} {T : ℝ → ℝ}
    (hT : ContinuousOn T (Icc 0 tf)) (htf : 0 ≤ tf) :
    ∃ k' G : ℝ → ℝ, (∀ t, HasDerivAt G (k' t) t) ∧ G 0 = 0 ∧
      ∀ t ∈ Icc 0 tf, k' t = rate Dref Tref z (T t) ∧
        G t = ∫ s in (0 : ℝ)..t, rate Dref Tref z (T s) := by
  set c : ℝ → ℝ := fun s => max 0 (min tf s)
  have hc : Continuous c := by fun_prop
  have hcmem : ∀ s, c s ∈ Icc 0 tf := fun s => ⟨le_max_left _ _, max_le htf (min_le_left _ _)⟩
  have hceq : ∀ s ∈ Icc 0 tf, c s = s := fun s hs => by
    simp only [c, min_eq_right hs.2, max_eq_right hs.1]
  set k' : ℝ → ℝ := fun s => rate Dref Tref z (T (c s))
  have hk' : Continuous k' := (continuous_rate Dref Tref z).comp (hT.comp_continuous hc hcmem)
  refine ⟨k', fun t => ∫ s in (0 : ℝ)..t, k' s,
    fun t => (hk'.integral_hasStrictDerivAt 0 t).hasDerivAt, intervalIntegral.integral_same,
    fun t ht => ⟨by simp only [k', hceq t ht], intervalIntegral.integral_congr fun s hs => ?_⟩⟩
  rw [uIcc_of_le ht.1] at hs
  simp only [k', hceq s ⟨hs.1, hs.2.trans ht.2⟩]

/-- **Log-linear inactivation under time-varying temperature.** Let $D_{\mathrm{ref}}$,
$T_{\mathrm{ref}}$ and $z$ be real numbers and
$k(\theta) = \frac{\ln 10}{D_{\mathrm{ref}}}\,10^{(\theta - T_{\mathrm{ref}})/z}$ (`rate`). Let the
temperature history $T$ be continuous on $[0, t_f]$ and let $N_0 > 0$. Then the function
$N(t) = N_0 \exp\bigl(-\int_0^t k(T(s))\,ds\bigr)$

* satisfies $N(0) = N_0$ and $N'(t) = -k(T(t))\,N(t)$ for $t \in [0, t_f]$, the derivative being
  taken within $[0, t_f]$;
* is the only such function on $[0, t_f]$: every $M$ with $M(0) = N_0$ and derivative
  $-k(T(t))\,M(t)$ within $[0, t_f]$ at each $t \in [0, t_f]$ equals $N$ on $[0, t_f]$;
* is positive on $[0, t_f]$;
* satisfies $\log_{10}(N_0 / N(t)) = F(t) / D_{\mathrm{ref}}$ for $t \in [0, t_f]$, where
  $F(t) = \int_0^t 10^{(T(s) - T_{\mathrm{ref}})/z}\,ds$ is the F-value (`fValue`).

For $t_f > 0$ the derivatives within $[0, t_f]$ are one-sided at the endpoints. For $t_f = 0$
every number is a derivative within $\{0\}$, so the equation imposes no condition and uniqueness
rests on $M(0) = N_0$ alone; for $t_f < 0$ the interval is empty and only $N(0) = N_0$ remains.
No sign condition on $D_{\mathrm{ref}}$ or $z$ is needed, reading a division by zero as $0$; in
the model both are positive. -/
theorem log_linear_inactivation (Dref Tref z : ℝ) {N₀ tf : ℝ} {T : ℝ → ℝ}
    (hT : ContinuousOn T (Icc 0 tf)) (hN₀ : 0 < N₀) :
    let N : ℝ → ℝ := fun t => N₀ * exp (-∫ s in (0 : ℝ)..t, rate Dref Tref z (T s))
    (N 0 = N₀ ∧
      ∀ t ∈ Icc 0 tf, HasDerivWithinAt N (-rate Dref Tref z (T t) * N t) (Icc 0 tf) t) ∧
    (∀ M : ℝ → ℝ, M 0 = N₀ →
      (∀ t ∈ Icc 0 tf, HasDerivWithinAt M (-rate Dref Tref z (T t) * M t) (Icc 0 tf) t) →
      EqOn M N (Icc 0 tf)) ∧
    (∀ t ∈ Icc 0 tf, 0 < N t) ∧
    ∀ t ∈ Icc 0 tf, logb 10 (N₀ / N t) = fValue Tref z T t / Dref := by
  intro N
  have hN0 : N 0 = N₀ := by simp [N]
  refine ⟨⟨hN0, fun t ht => ?_⟩, fun M hM0 hM => ?_, fun t _ => mul_pos hN₀ (exp_pos _),
    fun t _ => ?_⟩
  · -- The explicit solution solves the equation.
    obtain ⟨k', G, hG, -, hGk⟩ := exists_primitive (Dref := Dref) (Tref := Tref) (z := z) hT
      (ht.1.trans ht.2)
    have hd : HasDerivAt (fun s => N₀ * exp (-G s)) (N₀ * (exp (-G t) * -k' t)) t :=
      ((hG t).neg.exp).const_mul N₀
    refine (hd.hasDerivWithinAt.congr_of_mem (fun s hs => ?_) ht).congr_deriv ?_
    · simp only [N, (hGk s hs).2]
    · simp only [N, (hGk t ht).1, (hGk t ht).2]
      ring
  · -- Any solution has a constant product with the integrating factor `exp(∫₀ᵗ k(T(s)) ds)`.
    intro t ht
    obtain ⟨k', G, hG, hG0, hGk⟩ := exists_primitive (Dref := Dref) (Tref := Tref) (z := z) hT
      (ht.1.trans ht.2)
    have hd : ∀ s ∈ Icc 0 tf, HasDerivWithinAt (fun s => M s * exp (G s)) 0 (Icc 0 tf) s := by
      intro s hs
      convert (hM s hs).mul ((hG s).exp.hasDerivWithinAt) using 1
      rw [(hGk s hs).1]
      ring
    have hconst := constant_of_has_deriv_right_zero (fun s hs => (hd s hs).continuousWithinAt)
      (fun s hs => (hd s (Ico_subset_Icc_self hs)).mono_of_mem_nhdsWithin
        (mem_of_superset (Icc_mem_nhdsGE hs.2) (Icc_subset_Icc_left hs.1))) t ht
    simp only [hM0, hG0, exp_zero, mul_one] at hconst
    simp only [N, ← (hGk t ht).2, ← hconst, mul_assoc, ← exp_add, add_neg_cancel, exp_zero,
      mul_one]
  · -- The decimal reduction.
    have hlog : Real.log 10 ≠ 0 := (Real.log_pos (by norm_num)).ne'
    have hint : (∫ s in (0 : ℝ)..t, rate Dref Tref z (T s)) =
        Real.log 10 / Dref * fValue Tref z T t :=
      intervalIntegral.integral_const_mul _ _
    simp only [N, logb, hint]
    rw [div_mul_eq_div_div, div_self hN₀.ne', one_div, ← exp_neg, neg_neg, log_exp,
      div_mul_eq_mul_div, div_right_comm, mul_div_cancel_left₀ _ hlog]

end Chemistry.Kinetics.ThermalInactivation

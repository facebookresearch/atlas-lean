/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-!
# Time-dependent passive cable with sealed ends

The membrane potential `V t x` (measured from rest) of a passive cylindrical cable `[0, L]`
obeys the cable equation

  `τ ∂ₜV = ℓ² ∂ₓ²V - V`,

with membrane time constant `τ` and length constant `ℓ`, both kept as parameters (no length
constant is derived from membrane and axial resistances here). Sealed ends carry no axial
current: `∂ₓV(t, 0) = ∂ₓV(t, L) = 0` (`SealedEnds`). `IsCableSolution τ ℓ L T V` is a classical
solution at the times of `T`.

## Main results

* Modes. The sealed-end modes `cosMode L n x = cos (n π x / L)` satisfy
  `(cosMode L n)'' = -(n π / L)² cosMode L n` (`deriv_deriv_cosMode`), have zero slope at both
  ends (`deriv_cosMode_zero`, `deriv_cosMode_length`) and are orthogonal on `[0, L]` with
  norms `L` (`n = 0`) and `L / 2` (`n ≥ 1`) (`integral_cosMode_mul_cosMode`).
* Decay rates. Mode `n` decays at `k_n = (1 + ℓ² (n π / L)²) / τ` (`decayRate`):
  `k_0 = 1 / τ` (`decayRate_zero`), `1 / τ ≤ k_n` (`one_div_le_decayRate`), `k_n` strictly
  increasing for `ℓ, L ≠ 0` (`decayRate_strictMono`), Rall's ratio
  `k_n / k_0 = 1 + (n π ℓ / L)²` (`decayRate_div_decayRate_zero`), and Rall's
  electrotonic-length formula `L / ℓ = π / √(k₁ / k₀ - 1)`
  (`div_eq_pi_div_sqrt_decayRate`).
* Finite expansion `cableSum`: `∑_{n ∈ s} a n e^{-k_n t} cos (n π x / L)` solves the equation
  at all times (`isCableSolution_cableSum`) with sealed ends (`sealedEnds_cableSum`); its
  coefficients decay mode by mode (`integral_cableSum_mul_cosMode`); it obeys the bound
  `e^{-t/τ} ∑ |a n|`, uniform in `x` (`abs_cableSum_le`), and tends to `0` at every position
  (`tendsto_cableSum`); without the uniform mode the bound improves to rate `k₁`
  (`abs_cableSum_le_of_zero_notMem`), and equalizes: `e^{t/τ} V t x → a₀`
  (`tendsto_exp_mul_cableSum`).
* Infinite expansion `cableSeries` with `∑ |a n| < ∞` and `ℓ ≠ 0`: termwise differentiable
  for `t > 0`, solves the equation on `t > 0` (`isCableSolution_cableSeries`) with sealed ends
  (`sealedEnds_cableSeries`), initial profile `∑ a n cos (n π x / L)`
  (`cableSeries_time_zero`), the bound `e^{-t/τ} ∑ |a n|`, uniform in `x`
  (`abs_cableSeries_le`), convergence to `0` at every position (`tendsto_cableSeries`) and
  mode-by-mode coefficients `a n e^{-k_n t}` (`integral_cableSeries_mul_cosMode`).
* Arbitrary sealed solutions (`modeCoeff_eq_mul_exp`): for every classical sealed solution on an
  open preconnected time set `T` with `∂ₜV` jointly continuous and `∂ₓ²V` continuous in `x`,
  each cosine coefficient `c_n(t) = ∫₀ᴸ V t x cos (n π x / L) dx` (`modeCoeff`) satisfies
  `c_n(t) = c_n(t₀) e^{-k_n (t - t₀)}`. Hence `c_n → 0` (`tendsto_modeCoeff`), and the total
  potential `∫₀ᴸ V t` decays at exactly `1 / τ` (`integral_eq_mul_exp`).
* Steady state, minimally restated. `sealedSteady ℓ L x = cosh ((L - x) / ℓ)` solves
  `ℓ² W'' = W` (`sealedSteady_steady`), is sealed at `L`, and has slope `-sinh (L / ℓ) / ℓ` at
  `0`. The charging transient `chargingSum` (steady profile plus a finite expansion) solves the
  cable equation (`isCableSolution_chargingSum`), has a sealed far end and a constant gradient
  at `x = 0` (`deriv_chargingSum_ends`), and converges to the steady profile
  (`tendsto_chargingSum`).

## Scope

* Completeness of the cosine system is not formalized, so a sealed solution is not identified
  with its expansion; `modeCoeff_eq_mul_exp` gives the decay of every coefficient instead.
* The infinite expansion assumes absolutely summable coefficients (not merely square-summable
  ones), and its continuity at `t = 0` is not stated.
* `modeCoeff_eq_mul_exp` needs `t, t₀` in the open set `T`, so the initial time itself is
  excluded unless `T` contains it.
* Spatial derivatives at the ends are two-sided: profiles are functions on `ℝ`, differentiable
  across `0` and `L`. The even reflection of a sealed `C²` profile on `[0, L]` qualifies.
* Axial current appears only as the gradient `∂ₓV`; the axial resistance, the length constant
  `√(r_m / r_i)` and the semi-infinite and steady-state input-resistance facts are not
  restated here.

## References

* W. Rall, *Time constants and electrotonic length of membrane cylinders and neurons*,
  Biophys. J. 9 (1969), 1483–1508: the sealed-end cosine series
  `V = ∑ B_n cos (n π X / L) e^{-(1 + (n π / L)²) T}` and `L = n π / √(τ₀ / τ_n - 1)`.
* J. Keener and J. Sneyd, *Mathematical Physiology I*, 2nd ed., Springer (2009), §4.1 (the
  cable equation).
* C. Koch, *Biophysics of Computation*, Oxford University Press (1999), ch. 2.

Section and chapter labels above are not checked against the texts.
-/

@[expose] public section

open Real Set Filter Topology intervalIntegral MeasureTheory
open scoped Interval

namespace MathlibExt.Biology.Biophysics.CableTimeDependent

/-! ### Sealed-end (Neumann) cosine modes -/

/-- The `n`-th sealed-end mode `x ↦ cos (n π x / L)` of a cable of length `L`. -/
noncomputable def cosMode (L : ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  cos (n * π / L * x)

/-- Slope of the `n`-th mode: `(cos (n π x / L))' = -(n π / L) sin (n π x / L)`. -/
theorem hasDerivAt_cosMode (L : ℝ) (n : ℕ) (x : ℝ) :
    HasDerivAt (cosMode L n) (-(n * π / L) * sin (n * π / L * x)) x := by
  have h := ((hasDerivAt_id x).const_mul (n * π / L)).cos
  simp only [mul_one, id] at h
  unfold cosMode
  convert h using 1
  ring

/-- The derivative of the `n`-th mode, as a function. -/
theorem deriv_cosMode (L : ℝ) (n : ℕ) :
    deriv (cosMode L n) = fun x => -(n * π / L) * sin (n * π / L * x) :=
  funext fun x => (hasDerivAt_cosMode L n x).deriv

/-- The slope of the `n`-th mode has derivative `-(n π / L)²` times the mode. -/
theorem hasDerivAt_deriv_cosMode (L : ℝ) (n : ℕ) (x : ℝ) :
    HasDerivAt (deriv (cosMode L n)) (-(n * π / L) ^ 2 * cosMode L n x) x := by
  rw [deriv_cosMode]
  have h := (((hasDerivAt_id x).const_mul (n * π / L)).sin).const_mul (-(n * π / L))
  simp only [mul_one, id] at h
  convert h using 1
  simp only [cosMode]
  ring

/-- Eigenvalue equation: `(cos (n π x / L))'' = -(n π / L)² cos (n π x / L)`. -/
theorem deriv_deriv_cosMode (L : ℝ) (n : ℕ) (x : ℝ) :
    deriv (deriv (cosMode L n)) x = -(n * π / L) ^ 2 * cosMode L n x :=
  (hasDerivAt_deriv_cosMode L n x).deriv

/-- Sealed left end: the mode has zero slope (zero axial current) at `x = 0`. -/
theorem deriv_cosMode_zero (L : ℝ) (n : ℕ) : deriv (cosMode L n) 0 = 0 := by
  simp [deriv_cosMode]

/-- Sealed right end: the mode has zero slope (zero axial current) at `x = L`. -/
theorem deriv_cosMode_length {L : ℝ} (hL : L ≠ 0) (n : ℕ) : deriv (cosMode L n) L = 0 := by
  rw [deriv_cosMode]
  simp only
  rw [div_mul_cancel₀ _ hL, sin_nat_mul_pi, mul_zero]

/-- The `0`-th mode is the uniform profile `1`. -/
theorem cosMode_zero_mode (L x : ℝ) : cosMode L 0 x = 1 := by simp [cosMode]

/-- Every mode is bounded by `1` in absolute value. -/
theorem abs_cosMode_le (L : ℝ) (n : ℕ) (x : ℝ) : |cosMode L n x| ≤ 1 := abs_cos_le_one _

/-- Every mode is continuous. -/
theorem continuous_cosMode (L : ℝ) (n : ℕ) : Continuous (cosMode L n) := by
  unfold cosMode; fun_prop

private theorem integral_cos_int {L : ℝ} (hL : L ≠ 0) (k : ℤ) :
    ∫ x in (0 : ℝ)..L, cos (k * π / L * x) = if k = 0 then L else 0 := by
  split_ifs with hk
  · simp [hk]
  · have hc : (k : ℝ) * π / L ≠ 0 :=
      div_ne_zero (mul_ne_zero (by exact_mod_cast hk) pi_ne_zero) hL
    rw [integral_comp_mul_left (fun x => cos x) hc, integral_cos]
    rw [mul_zero, div_mul_cancel₀ _ hL, sin_int_mul_pi, sin_zero, sub_zero, smul_zero]

/-- Orthogonality of the sealed-end modes on `[0, L]`:
`∫₀ᴸ cos (m π x / L) cos (n π x / L) dx` is `0` for `m ≠ n`, `L / 2` for `m = n ≥ 1`, and `L`
for `m = n = 0`. -/
theorem integral_cosMode_mul_cosMode {L : ℝ} (hL : L ≠ 0) (m n : ℕ) :
    ∫ x in (0 : ℝ)..L, cosMode L m x * cosMode L n x =
      if m = n then (if n = 0 then L else L / 2) else 0 := by
  have hf : (fun x => cosMode L m x * cosMode L n x) = fun x =>
      (cos ((((m : ℤ) - n : ℤ) : ℝ) * π / L * x) +
        cos ((((m : ℤ) + n : ℤ) : ℝ) * π / L * x)) / 2 := by
    funext x
    simp only [cosMode]
    rw [eq_div_iff two_ne_zero, mul_comm _ (2 : ℝ), ← mul_assoc, two_mul_cos_mul_cos]
    congr 2 <;> push_cast <;> ring
  have hc : ∀ k : ℤ, IntervalIntegrable (fun x : ℝ => cos (k * π / L * x)) volume 0 L :=
    fun k => (by fun_prop : Continuous fun x : ℝ => cos (k * π / L * x)).intervalIntegrable _ _
  rw [hf, intervalIntegral.integral_div, intervalIntegral.integral_add (hc _) (hc _),
    integral_cos_int hL, integral_cos_int hL]
  by_cases hmn : m = n
  · subst hmn
    by_cases hm0 : m = 0
    · subst hm0; simp
    · have : ((m : ℤ) + m) ≠ 0 := by omega
      simp [this, hm0]
  · have h1 : ((m : ℤ) - n) ≠ 0 := by omega
    have h2 : ((m : ℤ) + n) ≠ 0 := by omega
    simp [h1, h2, hmn]

/-! ### Decay rates -/

/-- Decay rate of the `n`-th sealed-end mode of the cable equation `τ V_t = ℓ² V_xx - V` on
`[0, L]`: `k_n = (1 + ℓ² (n π / L)²) / τ`, the reciprocal of Rall's `n`-th equalizing time
constant. -/
noncomputable def decayRate (τ ℓ L : ℝ) (n : ℕ) : ℝ :=
  (1 + ℓ ^ 2 * (n * π / L) ^ 2) / τ

/-- The uniform mode decays at the membrane rate `1 / τ`. -/
theorem decayRate_zero (τ ℓ L : ℝ) : decayRate τ ℓ L 0 = 1 / τ := by simp [decayRate]

/-- No mode decays more slowly than the membrane rate: `1 / τ ≤ k_n`. -/
theorem one_div_le_decayRate {τ : ℝ} (hτ : 0 < τ) (ℓ L : ℝ) (n : ℕ) :
    1 / τ ≤ decayRate τ ℓ L n := by
  unfold decayRate
  gcongr
  nlinarith [sq_nonneg ℓ, sq_nonneg (n * π / L), mul_nonneg (sq_nonneg ℓ) (sq_nonneg (n * π / L))]

/-- Every mode decays: `0 < k_n` for `τ > 0`. -/
theorem decayRate_pos {τ : ℝ} (hτ : 0 < τ) (ℓ L : ℝ) (n : ℕ) : 0 < decayRate τ ℓ L n :=
  (one_div_pos.mpr hτ).trans_le (one_div_le_decayRate hτ ℓ L n)

/-- Higher modes decay strictly faster. -/
theorem decayRate_strictMono {τ ℓ L : ℝ} (hτ : 0 < τ) (hℓ : ℓ ≠ 0) (hL : L ≠ 0) :
    StrictMono (decayRate τ ℓ L) := by
  intro m n hmn
  unfold decayRate
  have hmn' : (m : ℝ) ^ 2 < (n : ℝ) ^ 2 := by
    have : (m : ℝ) < n := by exact_mod_cast hmn
    gcongr
  have hc : 0 < ℓ ^ 2 * π ^ 2 / L ^ 2 := by positivity
  have key : ∀ k : ℕ, 1 + ℓ ^ 2 * (k * π / L) ^ 2 = 1 + ℓ ^ 2 * π ^ 2 / L ^ 2 * (k : ℝ) ^ 2 :=
    fun k => by ring
  rw [key, key]
  gcongr

/-- Rall's ratio: `k_n / k_0 = τ₀ / τ_n = 1 + (n π ℓ / L)²`. -/
theorem decayRate_div_decayRate_zero {τ : ℝ} (hτ : τ ≠ 0) (ℓ L : ℝ) (n : ℕ) :
    decayRate τ ℓ L n / decayRate τ ℓ L 0 = 1 + (n * π * ℓ / L) ^ 2 := by
  rw [decayRate_zero]
  unfold decayRate
  field_simp

/-- Rall's electrotonic-length formula: the cable length in units of the length constant is
recovered from the two slowest decay rates, `L / ℓ = π / √(k₁ / k₀ - 1)`. -/
theorem div_eq_pi_div_sqrt_decayRate {τ ℓ L : ℝ} (hτ : τ ≠ 0) (hℓ : 0 < ℓ) (hL : 0 < L) :
    L / ℓ = π / √(decayRate τ ℓ L 1 / decayRate τ ℓ L 0 - 1) := by
  rw [decayRate_div_decayRate_zero hτ, add_sub_cancel_left, Nat.cast_one, one_mul,
    sqrt_sq (by positivity)]
  field_simp

/-! ### The cable equation and its separated solutions -/

/-- `V t x` is a classical solution of the passive cable equation `τ ∂ₜV = ℓ² ∂ₓ²V - V` on the
cable `[0, L]` at the times in `T`: `V (·) x` is differentiable at `t`, `V t` is twice
differentiable at `x`, and the equation holds pointwise. -/
structure IsCableSolution (τ ℓ L : ℝ) (T : Set ℝ) (V : ℝ → ℝ → ℝ) : Prop where
  /-- `V (·) x` is differentiable in time. -/
  differentiableAt_time : ∀ t ∈ T, ∀ x ∈ Icc 0 L, DifferentiableAt ℝ (fun s => V s x) t
  /-- `V t` is differentiable in space on the closed cable (two-sided at the ends). -/
  differentiableAt_space : ∀ t ∈ T, ∀ x ∈ Icc 0 L, DifferentiableAt ℝ (V t) x
  /-- `∂ₓV t` is differentiable in space on the closed cable (two-sided at the ends). -/
  differentiableAt_deriv_space : ∀ t ∈ T, ∀ x ∈ Icc 0 L, DifferentiableAt ℝ (deriv (V t)) x
  /-- The cable equation `τ ∂ₜV = ℓ² ∂ₓ²V - V`. -/
  cable : ∀ t ∈ T, ∀ x ∈ Icc 0 L,
    τ * deriv (fun s => V s x) t = ℓ ^ 2 * deriv (deriv (V t)) x - V t x

/-- Sealed ends at `0` and `L` at the times in `T`: zero axial current, i.e. `∂ₓV = 0`.
`deriv` is `0` at points of non-differentiability, so this is meant together with
`IsCableSolution`, which makes `V t` differentiable at both ends. -/
def SealedEnds (L : ℝ) (T : Set ℝ) (V : ℝ → ℝ → ℝ) : Prop :=
  ∀ t ∈ T, deriv (V t) 0 = 0 ∧ deriv (V t) L = 0

/-- The finite sealed-end eigenfunction expansion
`V t x = ∑_{n ∈ s} a n e^{-k_n t} cos (n π x / L)`. -/
noncomputable def cableSum (τ ℓ L : ℝ) (s : Finset ℕ) (a : ℕ → ℝ) (t x : ℝ) : ℝ :=
  ∑ n ∈ s, a n * (exp (-decayRate τ ℓ L n * t) * cosMode L n x)

/-- Time derivative of the finite expansion, term by term. -/
theorem hasDerivAt_cableSum_time (τ ℓ L : ℝ) (s : Finset ℕ) (a : ℕ → ℝ) (t x : ℝ) :
    HasDerivAt (fun r => cableSum τ ℓ L s a r x)
      (∑ n ∈ s, a n * (-decayRate τ ℓ L n * exp (-decayRate τ ℓ L n * t) * cosMode L n x)) t := by
  unfold cableSum
  refine HasDerivAt.fun_sum fun n _ => ?_
  have h := (((hasDerivAt_id t).const_mul (-decayRate τ ℓ L n)).exp).mul_const (cosMode L n x)
  simp only [mul_one, id] at h
  convert h.const_mul (a n) using 1
  ring

/-- Spatial derivative of the finite expansion, term by term. -/
theorem hasDerivAt_cableSum_space (τ ℓ L : ℝ) (s : Finset ℕ) (a : ℕ → ℝ) (t x : ℝ) :
    HasDerivAt (cableSum τ ℓ L s a t)
      (∑ n ∈ s, a n * (exp (-decayRate τ ℓ L n * t) * deriv (cosMode L n) x)) x := by
  have : cableSum τ ℓ L s a t = fun y => ∑ n ∈ s, a n * (exp (-decayRate τ ℓ L n * t) *
      cosMode L n y) := rfl
  rw [this]
  exact HasDerivAt.fun_sum fun n _ =>
    (((hasDerivAt_cosMode L n x).const_mul _).const_mul _).congr_deriv (by rw [deriv_cosMode])

/-- The spatial derivative of the finite expansion, as a function. -/
theorem deriv_cableSum_space (τ ℓ L : ℝ) (s : Finset ℕ) (a : ℕ → ℝ) (t : ℝ) :
    deriv (cableSum τ ℓ L s a t) = fun x =>
      ∑ n ∈ s, a n * (exp (-decayRate τ ℓ L n * t) * deriv (cosMode L n) x) :=
  funext fun x => (hasDerivAt_cableSum_space τ ℓ L s a t x).deriv

/-- Second spatial derivative of the finite expansion, term by term. -/
theorem hasDerivAt_deriv_cableSum_space (τ ℓ L : ℝ) (s : Finset ℕ) (a : ℕ → ℝ) (t x : ℝ) :
    HasDerivAt (deriv (cableSum τ ℓ L s a t))
      (∑ n ∈ s, a n * (exp (-decayRate τ ℓ L n * t) * (-(n * π / L) ^ 2 * cosMode L n x))) x := by
  rw [deriv_cableSum_space]
  exact HasDerivAt.fun_sum fun n _ =>
    ((hasDerivAt_deriv_cosMode L n x).const_mul _).const_mul _

/-- The finite expansion solves the cable equation at every time and position. -/
theorem isCableSolution_cableSum {τ : ℝ} (hτ : τ ≠ 0) (ℓ L : ℝ) (s : Finset ℕ) (a : ℕ → ℝ) :
    IsCableSolution τ ℓ L univ (cableSum τ ℓ L s a) where
  differentiableAt_time t _ x _ := (hasDerivAt_cableSum_time τ ℓ L s a t x).differentiableAt
  differentiableAt_space t _ x _ := (hasDerivAt_cableSum_space τ ℓ L s a t x).differentiableAt
  differentiableAt_deriv_space t _ x _ :=
    (hasDerivAt_deriv_cableSum_space τ ℓ L s a t x).differentiableAt
  cable t _ x _ := by
    rw [(hasDerivAt_cableSum_time τ ℓ L s a t x).deriv,
      (hasDerivAt_deriv_cableSum_space τ ℓ L s a t x).deriv]
    unfold cableSum
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun n _ => ?_
    unfold decayRate
    field_simp
    ring

/-- The finite expansion has sealed ends at every time. -/
theorem sealedEnds_cableSum {L : ℝ} (hL : L ≠ 0) (τ ℓ : ℝ) (s : Finset ℕ) (a : ℕ → ℝ) :
    SealedEnds L univ (cableSum τ ℓ L s a) := fun t _ => by
  rw [deriv_cableSum_space]
  simp [deriv_cosMode_zero, deriv_cosMode_length hL]

/-- Initial profile of the finite expansion: `V 0 x = ∑_{n ∈ s} a n cos (n π x / L)`. -/
theorem cableSum_time_zero (τ ℓ L : ℝ) (s : Finset ℕ) (a : ℕ → ℝ) (x : ℝ) :
    cableSum τ ℓ L s a 0 x = ∑ n ∈ s, a n * cosMode L n x := by
  simp [cableSum]

/-- Decay rates are monotone in the mode number (no nondegeneracy needed). -/
theorem decayRate_mono {τ : ℝ} (hτ : 0 < τ) (ℓ L : ℝ) : Monotone (decayRate τ ℓ L) := by
  intro m n hmn
  unfold decayRate
  have hmn' : (m : ℝ) ^ 2 ≤ (n : ℝ) ^ 2 := by
    have : (m : ℝ) ≤ n := by exact_mod_cast hmn
    gcongr
  have key : ∀ k : ℕ, 1 + ℓ ^ 2 * (k * π / L) ^ 2 = 1 + ℓ ^ 2 * π ^ 2 / L ^ 2 * (k : ℝ) ^ 2 :=
    fun k => by ring
  rw [key, key]
  gcongr

/-- Uniform decay of the finite expansion at the membrane rate: for `t ≥ 0`,
`|V t x| ≤ e^{-t/τ} ∑ |a n|`. -/
theorem abs_cableSum_le {τ : ℝ} (hτ : 0 < τ) (ℓ L : ℝ) (s : Finset ℕ) (a : ℕ → ℝ) {t : ℝ}
    (ht : 0 ≤ t) (x : ℝ) :
    |cableSum τ ℓ L s a t x| ≤ exp (-t / τ) * ∑ n ∈ s, |a n| := by
  unfold cableSum
  rw [Finset.mul_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun n _ => ?_)
  rw [abs_mul, abs_mul, abs_exp]
  have h1 : exp (-decayRate τ ℓ L n * t) ≤ exp (-t / τ) := by
    rw [exp_le_exp]
    have := mul_le_mul_of_nonneg_right (one_div_le_decayRate hτ ℓ L n) ht
    have e : -t / τ = -(1 / τ * t) := by ring
    linarith
  have h2 := abs_cosMode_le L n x
  calc |a n| * (exp (-decayRate τ ℓ L n * t) * |cosMode L n x|)
      ≤ |a n| * (exp (-t / τ) * 1) := by gcongr
    _ = exp (-t / τ) * |a n| := by ring

/-- Without the uniform mode, the finite expansion decays at least at the first nonuniform rate
`k₁`: for `t ≥ 0`, `|V t x| ≤ e^{-k₁ t} ∑ |a n|`. -/
theorem abs_cableSum_le_of_zero_notMem {τ : ℝ} (hτ : 0 < τ) (ℓ L : ℝ) {s : Finset ℕ}
    (hs : 0 ∉ s) (a : ℕ → ℝ) {t : ℝ} (ht : 0 ≤ t) (x : ℝ) :
    |cableSum τ ℓ L s a t x| ≤ exp (-decayRate τ ℓ L 1 * t) * ∑ n ∈ s, |a n| := by
  unfold cableSum
  rw [Finset.mul_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun n hn => ?_)
  rw [abs_mul, abs_mul, abs_exp]
  have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr fun h => hs (h ▸ hn)
  have h1 : exp (-decayRate τ ℓ L n * t) ≤ exp (-decayRate τ ℓ L 1 * t) := by
    rw [exp_le_exp, neg_mul, neg_mul, neg_le_neg_iff]
    exact mul_le_mul_of_nonneg_right (decayRate_mono hτ ℓ L hn1) ht
  have h2 := abs_cosMode_le L n x
  calc |a n| * (exp (-decayRate τ ℓ L n * t) * |cosMode L n x|)
      ≤ |a n| * (exp (-decayRate τ ℓ L 1 * t) * 1) := by gcongr
    _ = exp (-decayRate τ ℓ L 1 * t) * |a n| := by ring

/-- Splitting off the uniform mode: `V = a₀ e^{-t/τ} + (nonuniform part)`. -/
theorem cableSum_insert_zero (τ ℓ L : ℝ) {s : Finset ℕ} (hs : 0 ∉ s) (a : ℕ → ℝ) (t x : ℝ) :
    cableSum τ ℓ L (insert 0 s) a t x = a 0 * exp (-t / τ) + cableSum τ ℓ L s a t x := by
  unfold cableSum
  rw [Finset.sum_insert hs, decayRate_zero, cosMode_zero_mode, mul_one]
  have e : -(1 / τ) * t = -t / τ := by ring
  rw [e]

/-- The finite expansion decays to rest at every position (the bound `abs_cableSum_le` is
uniform in `x`). -/
theorem tendsto_cableSum {τ : ℝ} (hτ : 0 < τ) (ℓ L : ℝ) (s : Finset ℕ) (a : ℕ → ℝ) (x : ℝ) :
    Tendsto (fun t => cableSum τ ℓ L s a t x) atTop (𝓝 0) := by
  have hexp : Tendsto (fun t => exp (-t / τ) * ∑ n ∈ s, |a n|) atTop (𝓝 0) := by
    have : Tendsto (fun t : ℝ => -t / τ) atTop atBot := by
      simp_rw [neg_div]
      exact tendsto_neg_atTop_atBot.comp (tendsto_id.atTop_div_const hτ)
    simpa using (tendsto_exp_atBot.comp this).mul_const (∑ n ∈ s, |a n|)
  refine squeeze_zero_norm' ?_ hexp
  filter_upwards [eventually_ge_atTop 0] with t ht
  exact abs_cableSum_le hτ ℓ L s a ht x

/-- Equalization (Rall): after rescaling by the membrane decay `e^{t/τ}`, the potential tends
to the uniform-mode coefficient `a₀` at every position, because every nonuniform mode decays
strictly faster than `1 / τ`. -/
theorem tendsto_exp_mul_cableSum {τ ℓ L : ℝ} (hτ : 0 < τ) (hℓ : ℓ ≠ 0) (hL : L ≠ 0)
    {s : Finset ℕ} (hs : 0 ∉ s) (a : ℕ → ℝ) (x : ℝ) :
    Tendsto (fun t => exp (t / τ) * cableSum τ ℓ L (insert 0 s) a t x) atTop (𝓝 (a 0)) := by
  have hgap : 1 / τ < decayRate τ ℓ L 1 := by
    rw [← decayRate_zero τ ℓ L]
    exact decayRate_strictMono hτ hℓ hL zero_lt_one
  have hrest : Tendsto (fun t => exp (t / τ) * cableSum τ ℓ L s a t x) atTop (𝓝 0) := by
    have hlim : Tendsto (fun t => exp ((1 / τ - decayRate τ ℓ L 1) * t) * ∑ n ∈ s, |a n|)
        atTop (𝓝 0) := by
      have : Tendsto (fun t : ℝ => (1 / τ - decayRate τ ℓ L 1) * t) atTop atBot :=
        tendsto_id.const_mul_atTop_of_neg (by linarith)
      simpa using (tendsto_exp_atBot.comp this).mul_const (∑ n ∈ s, |a n|)
    refine squeeze_zero_norm' ?_ hlim
    filter_upwards [eventually_ge_atTop 0] with t ht
    rw [Real.norm_eq_abs, abs_mul, abs_exp]
    calc exp (t / τ) * |cableSum τ ℓ L s a t x|
        ≤ exp (t / τ) * (exp (-decayRate τ ℓ L 1 * t) * ∑ n ∈ s, |a n|) := by
          gcongr; exact abs_cableSum_le_of_zero_notMem hτ ℓ L hs a ht x
      _ = exp ((1 / τ - decayRate τ ℓ L 1) * t) * ∑ n ∈ s, |a n| := by
          rw [← mul_assoc, ← exp_add]; congr 2; ring
  have hsplit : (fun t => exp (t / τ) * cableSum τ ℓ L (insert 0 s) a t x) =
      fun t => a 0 + exp (t / τ) * cableSum τ ℓ L s a t x := by
    funext t
    rw [cableSum_insert_zero τ ℓ L hs, mul_add, ← mul_assoc, mul_comm (exp _) (a 0), mul_assoc,
      ← exp_add, neg_div, add_neg_cancel, exp_zero, mul_one]
  rw [hsplit]
  simpa using hrest.const_add (a 0)

/-- Mode-by-mode decay of the expansion coefficients: the `n`-th cosine coefficient of the
finite expansion at time `t` is `a n e^{-k_n t}` times the mode norm (`L` for `n = 0`,
`L / 2` otherwise). -/
theorem integral_cableSum_mul_cosMode {L : ℝ} (hL : L ≠ 0) (τ ℓ : ℝ) (s : Finset ℕ)
    (a : ℕ → ℝ) (t : ℝ) (n : ℕ) :
    ∫ x in (0 : ℝ)..L, cableSum τ ℓ L s a t x * cosMode L n x =
      if n ∈ s then a n * exp (-decayRate τ ℓ L n * t) * (if n = 0 then L else L / 2)
      else 0 := by
  unfold cableSum
  simp_rw [Finset.sum_mul]
  rw [intervalIntegral.integral_finsetSum fun m _ =>
    (by unfold cosMode; fun_prop : Continuous fun x =>
      a m * (exp (-decayRate τ ℓ L m * t) * cosMode L m x) * cosMode L n x).intervalIntegrable _ _]
  have : ∀ m ∈ s, ∫ x in (0 : ℝ)..L,
      a m * (exp (-decayRate τ ℓ L m * t) * cosMode L m x) * cosMode L n x =
      if n = m then a m * exp (-decayRate τ ℓ L m * t) * (if n = 0 then L else L / 2)
      else 0 := by
    intro m _
    have h : (fun x => a m * (exp (-decayRate τ ℓ L m * t) * cosMode L m x) * cosMode L n x) =
        fun x => (a m * exp (-decayRate τ ℓ L m * t)) * (cosMode L m x * cosMode L n x) := by
      funext x; ring
    rw [h, intervalIntegral.integral_const_mul, integral_cosMode_mul_cosMode hL]
    by_cases hmn : n = m
    · subst hmn; simp
    · simp [hmn, Ne.symm hmn]
  rw [Finset.sum_congr rfl this, Finset.sum_ite_eq]

/-! ### Mode coefficients of an arbitrary sealed solution -/

/-- The `n`-th cosine coefficient `∫₀ᴸ V t x cos (n π x / L) dx` of the profile `V t`. -/
noncomputable def modeCoeff (L : ℝ) (V : ℝ → ℝ → ℝ) (n : ℕ) (t : ℝ) : ℝ :=
  ∫ x in (0 : ℝ)..L, V t x * cosMode L n x

/-- Two integrations by parts against a sealed-end mode: if `f` is twice differentiable on
`[0, L]` with continuous `f''` and `f'(0) = f'(L) = 0`, then
`∫₀ᴸ f'' cos (n π x / L) = -(n π / L)² ∫₀ᴸ f cos (n π x / L)`. -/
theorem integral_deriv_deriv_mul_cosMode {L : ℝ} (hL : 0 < L) {f : ℝ → ℝ}
    (hf : ∀ x ∈ Icc 0 L, DifferentiableAt ℝ f x)
    (hf' : ∀ x ∈ Icc 0 L, DifferentiableAt ℝ (deriv f) x)
    (hf'' : ContinuousOn (deriv (deriv f)) (Icc 0 L))
    (h0 : deriv f 0 = 0) (hLend : deriv f L = 0) (n : ℕ) :
    ∫ x in (0 : ℝ)..L, deriv (deriv f) x * cosMode L n x =
      -(n * π / L) ^ 2 * ∫ x in (0 : ℝ)..L, f x * cosMode L n x := by
  have hI : uIcc 0 L = Icc 0 L := uIcc_of_le hL.le
  have hcont' : ContinuousOn (deriv f) (uIcc 0 L) := by
    rw [hI]; exact fun x hx => (hf' x hx).continuousAt.continuousWithinAt
  -- first integration by parts: move one derivative from `f'` onto the mode
  have h1 := intervalIntegral.integral_mul_deriv_eq_deriv_mul (a := 0) (b := L)
    (u := cosMode L n) (u' := deriv (cosMode L n)) (v := deriv f) (v' := deriv (deriv f))
    (fun x _ => (hasDerivAt_cosMode L n x).congr_deriv (by rw [deriv_cosMode]))
    (fun x hx => (hf' x (hI ▸ hx)).hasDerivAt)
    ((by rw [deriv_cosMode]; fun_prop : Continuous (deriv (cosMode L n))).intervalIntegrable _ _)
    ((hI ▸ hf'').intervalIntegrable)
  -- second integration by parts: move the remaining derivative from `f` onto the mode
  have h2 := intervalIntegral.integral_mul_deriv_eq_deriv_mul (a := 0) (b := L)
    (u := deriv (cosMode L n)) (u' := fun x => -(n * π / L) ^ 2 * cosMode L n x)
    (v := f) (v' := deriv f)
    (fun x _ => hasDerivAt_deriv_cosMode L n x)
    (fun x hx => (hf x (hI ▸ hx)).hasDerivAt)
    ((by unfold cosMode; fun_prop : Continuous fun x => -(n * π / L) ^ 2 * cosMode L n x
      ).intervalIntegrable _ _)
    (hcont'.intervalIntegrable)
  rw [h0, hLend, mul_zero, mul_zero, sub_zero, zero_sub] at h1
  rw [deriv_cosMode_zero, deriv_cosMode_length hL.ne', zero_mul, zero_mul, sub_zero,
    zero_sub] at h2
  have hc : (fun x => deriv (deriv f) x * cosMode L n x) =
      fun x => cosMode L n x * deriv (deriv f) x := funext fun x => mul_comm _ _
  rw [hc, h1, h2]
  simp_rw [mul_assoc]
  rw [intervalIntegral.integral_const_mul]
  simp_rw [mul_comm (cosMode L n _) (f _)]
  ring

/-- Differentiation of a mode coefficient under the integral sign, for a profile whose time
derivative is jointly continuous on `T × [0, L]` (`T` open). -/
theorem hasDerivAt_modeCoeff {L : ℝ} (hL : 0 < L) {T : Set ℝ} (hT : IsOpen T)
    {V : ℝ → ℝ → ℝ} (hdiff : ∀ t ∈ T, ∀ x ∈ Icc 0 L, DifferentiableAt ℝ (fun s => V s x) t)
    (hcont : ∀ t ∈ T, ContinuousOn (V t) (Icc 0 L))
    (hVt : ContinuousOn (fun p : ℝ × ℝ => deriv (fun s => V s p.2) p.1) (T ×ˢ Icc 0 L))
    (n : ℕ) {t : ℝ} (ht : t ∈ T) :
    HasDerivAt (modeCoeff L V n)
      (∫ x in (0 : ℝ)..L, deriv (fun s => V s x) t * cosMode L n x) t := by
  have hI : uIcc 0 L = Icc 0 L := uIcc_of_le hL.le
  have hIoc : Ι (0 : ℝ) L ⊆ Icc 0 L := hI ▸ uIoc_subset_uIcc
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hT t ht
  have hδ : 0 < ε / 2 := half_pos hε
  have hcb : Metric.closedBall t (ε / 2) ⊆ T :=
    (Metric.closedBall_subset_ball (half_lt_self hε)).trans hball
  obtain ⟨C, hC⟩ := ((isCompact_closedBall t (ε / 2)).prod
    isCompact_Icc).exists_bound_of_continuousOn (hVt.mono (prod_mono hcb subset_rfl))
  have hmodecont := continuous_cosMode L n
  have hcontF : ∀ s ∈ T, ContinuousOn (fun x => V s x * cosMode L n x) (Icc 0 L) :=
    fun s hs => (hcont s hs).mul hmodecont.continuousOn
  have hVt_slice : ContinuousOn (fun x => deriv (fun s => V s x) t) (Icc 0 L) :=
    hVt.comp (by fun_prop : Continuous fun x : ℝ => (t, x)).continuousOn
      (fun x hx => ⟨ht, hx⟩)
  refine (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun s x => V s x * cosMode L n x)
    (F' := fun s x => deriv (fun r => V r x) s * cosMode L n x)
    (bound := fun _ => C) (s := Metric.ball t (ε / 2)) (Metric.ball_mem_nhds t hδ) ?_ ?_ ?_ ?_
    intervalIntegrable_const ?_).2
  · filter_upwards [Metric.ball_mem_nhds t hε] with s hs
    exact ((hcontF s (hball hs)).mono hIoc).aestronglyMeasurable measurableSet_uIoc
  · exact (hI ▸ hcontF t ht).intervalIntegrable
  · exact ((hVt_slice.mul hmodecont.continuousOn).mono hIoc).aestronglyMeasurable
      measurableSet_uIoc
  · refine Eventually.of_forall fun x hx s hs => ?_
    have hmem : (s, x) ∈ Metric.closedBall t (ε / 2) ×ˢ Icc 0 L :=
      ⟨Metric.ball_subset_closedBall hs, hIoc hx⟩
    have hb := hC (s, x) hmem
    rw [norm_mul]
    calc ‖deriv (fun r => V r x) s‖ * ‖cosMode L n x‖ ≤ C * 1 := by
          gcongr
          · exact (norm_nonneg _).trans hb
          · exact abs_cosMode_le L n x
      _ = C := mul_one C
  · refine Eventually.of_forall fun x hx s hs => ?_
    exact (hdiff s (hball (Metric.ball_subset_ball (half_le_self hε.le) hs)) x
      (hIoc hx)).hasDerivAt.mul_const _

/-- **Mode-by-mode decay of an arbitrary sealed solution.** Let `V` be a classical solution of
`τ ∂ₜV = ℓ² ∂ₓ²V - V` on `[0, L]` with sealed ends, at the times of an open interval-like
(open, preconnected) set `T`, with `∂ₜV` jointly continuous on `T × [0, L]` and `∂ₓ²V`
continuous in `x`. Then every cosine coefficient decays at exactly its rate `k_n`:
`c_n(t) = c_n(t₀) e^{-k_n (t - t₀)}` for `t, t₀ ∈ T`. -/
theorem modeCoeff_eq_mul_exp {τ ℓ L : ℝ} (hτ : τ ≠ 0) (hL : 0 < L) {T : Set ℝ}
    (hT : IsOpen T) (hT' : IsPreconnected T) {V : ℝ → ℝ → ℝ}
    (hV : IsCableSolution τ ℓ L T V) (hsealed : SealedEnds L T V)
    (hVt : ContinuousOn (fun p : ℝ × ℝ => deriv (fun s => V s p.2) p.1) (T ×ˢ Icc 0 L))
    (hVxx : ∀ t ∈ T, ContinuousOn (deriv (deriv (V t))) (Icc 0 L)) (n : ℕ) {t₀ t : ℝ}
    (ht₀ : t₀ ∈ T) (ht : t ∈ T) :
    modeCoeff L V n t = modeCoeff L V n t₀ * exp (-decayRate τ ℓ L n * (t - t₀)) := by
  set k := decayRate τ ℓ L n
  have hI : uIcc 0 L = Icc 0 L := uIcc_of_le hL.le
  have hcont : ∀ t ∈ T, ContinuousOn (V t) (Icc 0 L) := fun t ht x hx =>
    (hV.differentiableAt_space t ht x hx).continuousAt.continuousWithinAt
  -- the coefficient ODE `c_n' = -k_n c_n`
  have hderiv : ∀ s ∈ T, HasDerivAt (modeCoeff L V n) (-k * modeCoeff L V n s) s := by
    intro s hs
    have h := hasDerivAt_modeCoeff hL hT hV.differentiableAt_time hcont hVt n hs
    convert h using 1
    have hpt : EqOn (fun x => deriv (fun r => V r x) s * cosMode L n x)
        (fun x => τ⁻¹ * ℓ ^ 2 * (deriv (deriv (V s)) x * cosMode L n x) -
          τ⁻¹ * (V s x * cosMode L n x)) (uIcc 0 L) := by
      intro x hx
      have hc := hV.cable s hs x (hI ▸ hx)
      simp only
      rw [show deriv (fun r => V r x) s = τ⁻¹ * (τ * deriv (fun r => V r x) s) by
        field_simp, hc]
      ring
    rw [intervalIntegral.integral_congr hpt, intervalIntegral.integral_sub,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      integral_deriv_deriv_mul_cosMode hL (hV.differentiableAt_space s hs)
        (hV.differentiableAt_deriv_space s hs) (hVxx s hs) (hsealed s hs).1 (hsealed s hs).2]
    · simp only [modeCoeff, k, decayRate]
      field_simp
      ring
    · exact (hI ▸ ((hVxx s hs).mul (continuous_cosMode L n).continuousOn).const_smul
        (τ⁻¹ * ℓ ^ 2)).intervalIntegrable
    · exact (hI ▸ ((hcont s hs).mul (continuous_cosMode L n).continuousOn).const_smul
        τ⁻¹).intervalIntegrable
  -- `c_n(t) e^{k t}` is constant on `T`
  set g : ℝ → ℝ := fun s => modeCoeff L V n s * exp (k * s)
  have hg : ∀ s ∈ T, HasDerivAt g 0 s := by
    intro s hs
    have he := ((hasDerivAt_id s).const_mul k).exp
    simp only [mul_one, id] at he
    convert (hderiv s hs).mul he using 1
    ring
  have hconst := hT.is_const_of_deriv_eq_zero hT'
    (fun s hs => (hg s hs).differentiableAt.differentiableWithinAt)
    (fun s hs => (hg s hs).deriv) ht ht₀
  simp only [g] at hconst
  have : exp (-k * (t - t₀)) = exp (k * t₀) / exp (k * t) := by
    rw [← exp_sub]; ring_nf
  rw [this, mul_div_assoc', ← hconst, mul_div_assoc, div_self (exp_pos _).ne', mul_one]

/-! ### The infinite eigenfunction expansion -/

/-- The sealed-end eigenfunction expansion
`V t x = ∑_{n ≥ 0} a n e^{-k_n t} cos (n π x / L)`. -/
noncomputable def cableSeries (τ ℓ L : ℝ) (a : ℕ → ℝ) (t x : ℝ) : ℝ :=
  ∑' n, a n * (exp (-decayRate τ ℓ L n * t) * cosMode L n x)

private theorem mul_exp_neg_mul_le {k s : ℝ} (hs : 0 < s) : k * exp (-k * s) ≤ 1 / s := by
  rw [le_div_iff₀ hs]
  have h := add_one_le_exp (k * s)
  calc k * exp (-k * s) * s = (k * s) * exp (-(k * s)) := by ring_nf
    _ ≤ exp (k * s) * exp (-(k * s)) := by gcongr; linarith
    _ = 1 := by rw [← exp_add, add_neg_cancel, exp_zero]

private theorem exp_neg_decayRate_le_one {τ : ℝ} (hτ : 0 < τ) (ℓ L : ℝ) (n : ℕ) {t : ℝ}
    (ht : 0 ≤ t) : exp (-decayRate τ ℓ L n * t) ≤ 1 := by
  rw [exp_le_one_iff, neg_mul, neg_nonpos]
  exact mul_nonneg (decayRate_pos hτ ℓ L n).le ht

private theorem sq_mul_exp_le {τ ℓ : ℝ} (hτ : 0 < τ) (hℓ : ℓ ≠ 0) (L : ℝ) (n : ℕ) {t : ℝ}
    (ht : 0 < t) : (n * π / L) ^ 2 * exp (-decayRate τ ℓ L n * t) ≤ τ / (ℓ ^ 2 * t) := by
  have hℓ2 : 0 < ℓ ^ 2 := by positivity
  have hk : (n * π / L) ^ 2 = τ / ℓ ^ 2 * decayRate τ ℓ L n - 1 / ℓ ^ 2 := by
    unfold decayRate; field_simp; ring
  have h1 := mul_exp_neg_mul_le (k := decayRate τ ℓ L n) ht
  have h2 := exp_pos (-decayRate τ ℓ L n * t)
  rw [hk, sub_mul, mul_assoc]
  have : τ / ℓ ^ 2 * (decayRate τ ℓ L n * exp (-decayRate τ ℓ L n * t)) ≤ τ / ℓ ^ 2 * (1 / t) :=
    mul_le_mul_of_nonneg_left h1 (by positivity)
  have e : τ / ℓ ^ 2 * (1 / t) = τ / (ℓ ^ 2 * t) := by field_simp
  have : 0 ≤ 1 / ℓ ^ 2 * exp (-decayRate τ ℓ L n * t) := by positivity
  linarith

/-- The common bound `1 + τ / (ℓ² t)` on the spatial derivative factors at time `t > 0`. -/
private theorem abs_deriv_term_le {τ ℓ : ℝ} (hτ : 0 < τ) (hℓ : ℓ ≠ 0) (L : ℝ) (n : ℕ) {t : ℝ}
    (ht : 0 < t) (y : ℝ) :
    |exp (-decayRate τ ℓ L n * t) * deriv (cosMode L n) y| ≤ 1 + τ / (ℓ ^ 2 * t) := by
  rw [deriv_cosMode]
  simp only
  have he := exp_neg_decayRate_le_one hτ ℓ L n ht.le
  have hsq := sq_mul_exp_le hτ hℓ L n ht
  have hw : |n * π / L| ≤ 1 + (n * π / L) ^ 2 := by
    nlinarith [sq_abs (n * π / L), abs_nonneg (n * π / L), sq_nonneg (|n * π / L| - 1)]
  have hep := exp_pos (-decayRate τ ℓ L n * t)
  rw [abs_mul, abs_mul, abs_neg, abs_exp]
  calc exp (-decayRate τ ℓ L n * t) * (|n * π / L| * |sin (n * π / L * y)|)
      ≤ exp (-decayRate τ ℓ L n * t) * ((1 + (n * π / L) ^ 2) * 1) := by
        gcongr; exact abs_sin_le_one _
    _ = exp (-decayRate τ ℓ L n * t) + (n * π / L) ^ 2 * exp (-decayRate τ ℓ L n * t) := by ring
    _ ≤ 1 + τ / (ℓ ^ 2 * t) := add_le_add he hsq

private theorem abs_deriv2_term_le {τ ℓ : ℝ} (hτ : 0 < τ) (hℓ : ℓ ≠ 0) (L : ℝ) (n : ℕ) {t : ℝ}
    (ht : 0 < t) (y : ℝ) :
    |exp (-decayRate τ ℓ L n * t) * (-(n * π / L) ^ 2 * cosMode L n y)| ≤
      1 + τ / (ℓ ^ 2 * t) := by
  have hsq := sq_mul_exp_le hτ hℓ L n ht
  rw [abs_mul, abs_mul, abs_neg, abs_exp, abs_of_nonneg (sq_nonneg _)]
  calc exp (-decayRate τ ℓ L n * t) * ((n * π / L) ^ 2 * |cosMode L n y|)
      ≤ exp (-decayRate τ ℓ L n * t) * ((n * π / L) ^ 2 * 1) := by
        gcongr; exact abs_cosMode_le L n y
    _ = (n * π / L) ^ 2 * exp (-decayRate τ ℓ L n * t) := by ring
    _ ≤ τ / (ℓ ^ 2 * t) := hsq
    _ ≤ 1 + τ / (ℓ ^ 2 * t) := by linarith

private theorem summable_mul_of_abs_le {a : ℕ → ℝ} (ha : Summable fun n => |a n|) {B : ℝ}
    {g : ℕ → ℝ} (hg : ∀ n, |g n| ≤ B) : Summable fun n => a n * g n := by
  refine Summable.of_norm_bounded (g := fun n => |a n| * B) (ha.mul_right B) fun n => ?_
  rw [Real.norm_eq_abs, abs_mul]
  exact mul_le_mul_of_nonneg_left (hg n) (abs_nonneg _)

private theorem abs_term_le {τ : ℝ} (hτ : 0 < τ) (ℓ L : ℝ) (n : ℕ) {t : ℝ} (ht : 0 ≤ t)
    (x : ℝ) : |exp (-decayRate τ ℓ L n * t) * cosMode L n x| ≤ exp (-t / τ) := by
  rw [abs_mul, abs_exp]
  have h1 : exp (-decayRate τ ℓ L n * t) ≤ exp (-t / τ) := by
    rw [exp_le_exp]
    have := mul_le_mul_of_nonneg_right (one_div_le_decayRate hτ ℓ L n) ht
    have e : -t / τ = -(1 / τ * t) := by ring
    linarith
  calc exp (-decayRate τ ℓ L n * t) * |cosMode L n x| ≤ exp (-t / τ) * 1 := by
        gcongr; exact abs_cosMode_le L n x
    _ = exp (-t / τ) := mul_one _

/-- For `t ≥ 0` and absolutely summable coefficients the expansion converges absolutely. -/
theorem summable_cableSeries {τ : ℝ} (hτ : 0 < τ) (ℓ L : ℝ) {a : ℕ → ℝ}
    (ha : Summable fun n => |a n|) {t : ℝ} (ht : 0 ≤ t) (x : ℝ) :
    Summable fun n => a n * (exp (-decayRate τ ℓ L n * t) * cosMode L n x) :=
  summable_mul_of_abs_le ha fun n => abs_term_le hτ ℓ L n ht x

/-- Initial profile of the expansion: the cosine series `∑ a n cos (n π x / L)`. -/
theorem cableSeries_time_zero (τ ℓ L : ℝ) (a : ℕ → ℝ) (x : ℝ) :
    cableSeries τ ℓ L a 0 x = ∑' n, a n * cosMode L n x := by
  simp [cableSeries]

/-- Uniform decay of the expansion at the membrane rate: for `t ≥ 0`,
`|V t x| ≤ e^{-t/τ} ∑ |a n|`. -/
theorem abs_cableSeries_le {τ : ℝ} (hτ : 0 < τ) (ℓ L : ℝ) {a : ℕ → ℝ}
    (ha : Summable fun n => |a n|) {t : ℝ} (ht : 0 ≤ t) (x : ℝ) :
    |cableSeries τ ℓ L a t x| ≤ exp (-t / τ) * ∑' n, |a n| := by
  rw [← Real.norm_eq_abs, ← tsum_mul_left]
  refine tsum_of_norm_bounded (ha.mul_left (exp (-t / τ))).hasSum fun n => ?_
  rw [Real.norm_eq_abs, abs_mul, mul_comm]
  exact mul_le_mul_of_nonneg_right (abs_term_le hτ ℓ L n ht x) (abs_nonneg _)

/-- The expansion decays to rest at every position (the bound `abs_cableSeries_le` is uniform
in `x`). -/
theorem tendsto_cableSeries {τ : ℝ} (hτ : 0 < τ) (ℓ L : ℝ) {a : ℕ → ℝ}
    (ha : Summable fun n => |a n|) (x : ℝ) :
    Tendsto (fun t => cableSeries τ ℓ L a t x) atTop (𝓝 0) := by
  have hexp : Tendsto (fun t => exp (-t / τ) * ∑' n, |a n|) atTop (𝓝 0) := by
    have : Tendsto (fun t : ℝ => -t / τ) atTop atBot := by
      simp_rw [neg_div]
      exact tendsto_neg_atTop_atBot.comp (tendsto_id.atTop_div_const hτ)
    simpa using (tendsto_exp_atBot.comp this).mul_const (∑' n, |a n|)
  refine squeeze_zero_norm' ?_ hexp
  filter_upwards [eventually_ge_atTop 0] with t ht
  exact abs_cableSeries_le hτ ℓ L ha ht x

/-- Termwise spatial differentiation of the expansion at a positive time (`ℓ ≠ 0`). -/
theorem hasDerivAt_cableSeries_space {τ ℓ : ℝ} (hτ : 0 < τ) (hℓ : ℓ ≠ 0) (L : ℝ)
    {a : ℕ → ℝ} (ha : Summable fun n => |a n|) {t : ℝ} (ht : 0 < t) (x : ℝ) :
    HasDerivAt (cableSeries τ ℓ L a t)
      (∑' n, a n * (exp (-decayRate τ ℓ L n * t) * deriv (cosMode L n) x)) x := by
  have := hasDerivAt_tsum (u := fun n => |a n| * (1 + τ / (ℓ ^ 2 * t))) (y₀ := 0)
    (g := fun n y => a n * (exp (-decayRate τ ℓ L n * t) * cosMode L n y))
    (g' := fun n y => a n * (exp (-decayRate τ ℓ L n * t) * deriv (cosMode L n) y))
    (ha.mul_right _) (fun n y => ?_) (fun n y => ?_) (summable_cableSeries hτ ℓ L ha ht.le 0) x
  · exact this
  · exact (((hasDerivAt_cosMode L n y).const_mul _).const_mul _).congr_deriv
      (by rw [deriv_cosMode])
  · rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_left (abs_deriv_term_le hτ hℓ L n ht y) (abs_nonneg _)

/-- The spatial derivative of the expansion at a positive time, as a function. -/
theorem deriv_cableSeries_space {τ ℓ : ℝ} (hτ : 0 < τ) (hℓ : ℓ ≠ 0) (L : ℝ) {a : ℕ → ℝ}
    (ha : Summable fun n => |a n|) {t : ℝ} (ht : 0 < t) :
    deriv (cableSeries τ ℓ L a t) = fun x =>
      ∑' n, a n * (exp (-decayRate τ ℓ L n * t) * deriv (cosMode L n) x) :=
  funext fun x => (hasDerivAt_cableSeries_space hτ hℓ L ha ht x).deriv

/-- Termwise second spatial differentiation of the expansion at a positive time. -/
theorem hasDerivAt_deriv_cableSeries_space {τ ℓ : ℝ} (hτ : 0 < τ) (hℓ : ℓ ≠ 0) (L : ℝ)
    {a : ℕ → ℝ} (ha : Summable fun n => |a n|) {t : ℝ} (ht : 0 < t) (x : ℝ) :
    HasDerivAt (deriv (cableSeries τ ℓ L a t))
      (∑' n, a n * (exp (-decayRate τ ℓ L n * t) * (-(n * π / L) ^ 2 * cosMode L n x))) x := by
  rw [deriv_cableSeries_space hτ hℓ L ha ht]
  have := hasDerivAt_tsum (u := fun n => |a n| * (1 + τ / (ℓ ^ 2 * t))) (y₀ := 0)
    (g := fun n y => a n * (exp (-decayRate τ ℓ L n * t) * deriv (cosMode L n) y))
    (g' := fun n y => a n * (exp (-decayRate τ ℓ L n * t) * (-(n * π / L) ^ 2 * cosMode L n y)))
    (ha.mul_right _) (fun n y => ?_) (fun n y => ?_)
    (summable_mul_of_abs_le (g := fun n => exp (-decayRate τ ℓ L n * t) * deriv (cosMode L n) 0)
      ha fun n => abs_deriv_term_le hτ hℓ L n ht 0) x
  · exact this
  · exact ((hasDerivAt_deriv_cosMode L n y).const_mul _).const_mul _
  · rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_left (abs_deriv2_term_le hτ hℓ L n ht y) (abs_nonneg _)

/-- Termwise time differentiation of the expansion at a positive time. -/
theorem hasDerivAt_cableSeries_time {τ : ℝ} (hτ : 0 < τ) (ℓ L : ℝ) {a : ℕ → ℝ}
    (ha : Summable fun n => |a n|) {t : ℝ} (ht : 0 < t) (x : ℝ) :
    HasDerivAt (fun r => cableSeries τ ℓ L a r x)
      (∑' n, a n * (-decayRate τ ℓ L n * exp (-decayRate τ ℓ L n * t) * cosMode L n x)) t := by
  have ht2 : 0 < t / 2 := half_pos ht
  have := hasDerivAt_tsum_of_isPreconnected (u := fun n => |a n| * (1 / (t / 2)))
    (g := fun n r => a n * (exp (-decayRate τ ℓ L n * r) * cosMode L n x))
    (g' := fun n r => a n * (-decayRate τ ℓ L n * exp (-decayRate τ ℓ L n * r) * cosMode L n x))
    (t := Ioi (t / 2)) (y₀ := t) (ha.mul_right _) isOpen_Ioi isPreconnected_Ioi
    (fun n r _ => ?_) (fun n r hr => ?_) (half_lt_self ht)
    (summable_cableSeries hτ ℓ L ha ht.le x) (half_lt_self ht)
  · exact this
  · have h := (((hasDerivAt_id r).const_mul (-decayRate τ ℓ L n)).exp).mul_const (cosMode L n x)
    simp only [mul_one, id] at h
    convert h.const_mul (a n) using 1
    ring
  · have hr0 : 0 < r := ht2.trans hr
    have hk := (decayRate_pos hτ ℓ L n).le
    rw [Real.norm_eq_abs, abs_mul]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    rw [abs_mul, abs_mul, abs_neg, abs_exp, abs_of_nonneg hk]
    calc decayRate τ ℓ L n * exp (-decayRate τ ℓ L n * r) * |cosMode L n x|
        ≤ decayRate τ ℓ L n * exp (-decayRate τ ℓ L n * r) * 1 := by
          gcongr; exact abs_cosMode_le L n x
      _ ≤ 1 / r := by rw [mul_one]; exact mul_exp_neg_mul_le hr0
      _ ≤ 1 / (t / 2) := one_div_le_one_div_of_le ht2 hr.le

/-- The infinite expansion with absolutely summable coefficients solves the cable equation at
every positive time. -/
theorem isCableSolution_cableSeries {τ ℓ : ℝ} (hτ : 0 < τ) (hℓ : ℓ ≠ 0) (L : ℝ) {a : ℕ → ℝ}
    (ha : Summable fun n => |a n|) :
    IsCableSolution τ ℓ L (Ioi 0) (cableSeries τ ℓ L a) where
  differentiableAt_time t ht x _ := (hasDerivAt_cableSeries_time hτ ℓ L ha ht x).differentiableAt
  differentiableAt_space t ht x _ :=
    (hasDerivAt_cableSeries_space hτ hℓ L ha ht x).differentiableAt
  differentiableAt_deriv_space t ht x _ :=
    (hasDerivAt_deriv_cableSeries_space hτ hℓ L ha ht x).differentiableAt
  cable t ht x _ := by
    have ht' : 0 < t := ht
    rw [(hasDerivAt_cableSeries_time hτ ℓ L ha ht' x).deriv,
      (hasDerivAt_deriv_cableSeries_space hτ hℓ L ha ht' x).deriv]
    have hs1 := summable_mul_of_abs_le ha fun n => abs_deriv2_term_le hτ hℓ L n ht' x
    have hs2 := summable_cableSeries hτ ℓ L ha ht'.le x
    unfold cableSeries
    rw [← tsum_mul_left, ← tsum_mul_left, ← (hs1.mul_left _).tsum_sub hs2]
    refine tsum_congr fun n => ?_
    unfold decayRate
    field_simp
    ring

/-- The infinite expansion has sealed ends at every positive time. -/
theorem sealedEnds_cableSeries {τ ℓ L : ℝ} (hτ : 0 < τ) (hℓ : ℓ ≠ 0) (hL : L ≠ 0)
    {a : ℕ → ℝ} (ha : Summable fun n => |a n|) :
    SealedEnds L (Ioi 0) (cableSeries τ ℓ L a) := fun t ht => by
  rw [deriv_cableSeries_space hτ hℓ L ha ht]
  simp [deriv_cosMode_zero, deriv_cosMode_length hL]

/-- Coefficients of the infinite expansion: for `t ≥ 0`, its `n`-th cosine coefficient is
`a n e^{-k_n t}` times the mode norm (`L` for `n = 0`, `L / 2` otherwise). -/
theorem integral_cableSeries_mul_cosMode {τ L : ℝ} (hτ : 0 < τ) (hL : L ≠ 0) (ℓ : ℝ)
    {a : ℕ → ℝ} (ha : Summable fun n => |a n|) {t : ℝ} (ht : 0 ≤ t) (m : ℕ) :
    ∫ x in (0 : ℝ)..L, cableSeries τ ℓ L a t x * cosMode L m x =
      a m * exp (-decayRate τ ℓ L m * t) * (if m = 0 then L else L / 2) := by
  have hsum : HasSum (fun n => ∫ x in (0 : ℝ)..L,
      a n * (exp (-decayRate τ ℓ L n * t) * cosMode L n x) * cosMode L m x)
      (∫ x in (0 : ℝ)..L, cableSeries τ ℓ L a t x * cosMode L m x) := by
    refine intervalIntegral.hasSum_integral_of_dominated_convergence (fun n _ => |a n|)
      (fun n => ?_) (fun n => ?_) ?_ ?_ ?_
    · exact (by unfold cosMode; fun_prop : Continuous fun x =>
        a n * (exp (-decayRate τ ℓ L n * t) * cosMode L n x) * cosMode L m x).aestronglyMeasurable
    · refine Eventually.of_forall fun x _ => ?_
      rw [Real.norm_eq_abs, abs_mul, abs_mul]
      have h1 := abs_term_le hτ ℓ L n ht x
      have h2 : exp (-t / τ) ≤ 1 := by
        rw [exp_le_one_iff, neg_div, neg_nonpos]; exact div_nonneg ht hτ.le
      have h3 := abs_cosMode_le L m x
      calc |a n| * |exp (-decayRate τ ℓ L n * t) * cosMode L n x| * |cosMode L m x|
          ≤ |a n| * 1 * 1 := by gcongr; exact h1.trans h2
        _ = |a n| := by ring
    · exact Eventually.of_forall fun _ _ => ha
    · exact intervalIntegrable_const
    · refine Eventually.of_forall fun x _ => ?_
      unfold cableSeries
      exact (summable_cableSeries hτ ℓ L ha ht x).hasSum.mul_right (cosMode L m x)
  have hterm : ∀ n, ∫ x in (0 : ℝ)..L,
      a n * (exp (-decayRate τ ℓ L n * t) * cosMode L n x) * cosMode L m x =
      if m = n then a n * exp (-decayRate τ ℓ L n * t) * (if m = 0 then L else L / 2)
      else 0 := by
    intro n
    have h : (fun x => a n * (exp (-decayRate τ ℓ L n * t) * cosMode L n x) * cosMode L m x) =
        fun x => (a n * exp (-decayRate τ ℓ L n * t)) * (cosMode L n x * cosMode L m x) := by
      funext x; ring
    rw [h, intervalIntegral.integral_const_mul, integral_cosMode_mul_cosMode hL]
    by_cases hmn : m = n
    · subst hmn; simp
    · simp [hmn, Ne.symm hmn]
  simp_rw [hterm] at hsum
  rw [← hsum.tsum_eq, tsum_eq_single m (fun n hn => by simp [Ne.symm hn])]
  simp

/-! ### Consequences of mode-by-mode decay -/

/-- Every cosine coefficient of a sealed solution on `t > 0` decays to `0`. -/
theorem tendsto_modeCoeff {τ ℓ L : ℝ} (hτ : 0 < τ) (hL : 0 < L) {V : ℝ → ℝ → ℝ}
    (hV : IsCableSolution τ ℓ L (Ioi 0) V) (hsealed : SealedEnds L (Ioi 0) V)
    (hVt : ContinuousOn (fun p : ℝ × ℝ => deriv (fun s => V s p.2) p.1) (Ioi 0 ×ˢ Icc 0 L))
    (hVxx : ∀ t ∈ Ioi (0 : ℝ), ContinuousOn (deriv (deriv (V t))) (Icc 0 L)) (n : ℕ) :
    Tendsto (modeCoeff L V n) atTop (𝓝 0) := by
  have heq : ∀ᶠ t in atTop, modeCoeff L V n 1 * exp (-decayRate τ ℓ L n * (t - 1)) =
      modeCoeff L V n t := by
    filter_upwards [eventually_gt_atTop 0] with t ht
    exact (modeCoeff_eq_mul_exp hτ.ne' hL isOpen_Ioi isPreconnected_Ioi hV hsealed hVt hVxx n
      (mem_Ioi.mpr one_pos) ht).symm
  refine Tendsto.congr' heq ?_
  have hk := decayRate_pos hτ ℓ L n
  have : Tendsto (fun t : ℝ => -decayRate τ ℓ L n * (t - 1)) atTop atBot :=
    (tendsto_atTop_add_const_right _ (-1) tendsto_id).const_mul_atTop_of_neg (by linarith)
  simpa using (tendsto_exp_atBot.comp this).const_mul (modeCoeff L V n 1)

/-- The total (integrated) potential of a sealed solution decays at exactly the membrane rate:
`∫₀ᴸ V t = (∫₀ᴸ V t₀) e^{-(t - t₀)/τ}`. -/
theorem integral_eq_mul_exp {τ ℓ L : ℝ} (hτ : τ ≠ 0) (hL : 0 < L) {T : Set ℝ}
    (hT : IsOpen T) (hT' : IsPreconnected T) {V : ℝ → ℝ → ℝ}
    (hV : IsCableSolution τ ℓ L T V) (hsealed : SealedEnds L T V)
    (hVt : ContinuousOn (fun p : ℝ × ℝ => deriv (fun s => V s p.2) p.1) (T ×ˢ Icc 0 L))
    (hVxx : ∀ t ∈ T, ContinuousOn (deriv (deriv (V t))) (Icc 0 L)) {t₀ t : ℝ}
    (ht₀ : t₀ ∈ T) (ht : t ∈ T) :
    ∫ x in (0 : ℝ)..L, V t x = (∫ x in (0 : ℝ)..L, V t₀ x) * exp (-(t - t₀) / τ) := by
  have h := modeCoeff_eq_mul_exp hτ hL hT hT' hV hsealed hVt hVxx 0 ht₀ ht
  simp only [modeCoeff, cosMode_zero_mode, mul_one, decayRate_zero] at h
  rw [h]
  congr 2
  ring

/-! ### Steady state with a sealed far end, and the charging transient -/

/-- Steady profile `x ↦ cosh ((L - x) / ℓ)` of a cable sealed at `x = L`. -/
noncomputable def sealedSteady (ℓ L : ℝ) (x : ℝ) : ℝ :=
  cosh ((L - x) / ℓ)

/-- Slope of the steady profile: `W'(x) = -sinh ((L - x)/ℓ) / ℓ`. -/
theorem hasDerivAt_sealedSteady (ℓ L x : ℝ) :
    HasDerivAt (sealedSteady ℓ L) (-sinh ((L - x) / ℓ) / ℓ) x := by
  have h1 : HasDerivAt (fun y => (L - y) / ℓ) (-1 / ℓ) x := by
    simpa using ((hasDerivAt_id x).const_sub L).div_const ℓ
  unfold sealedSteady
  convert h1.cosh using 1
  ring

/-- The slope of the steady profile, as a function. -/
theorem deriv_sealedSteady (ℓ L : ℝ) :
    deriv (sealedSteady ℓ L) = fun x => -sinh ((L - x) / ℓ) / ℓ :=
  funext fun x => (hasDerivAt_sealedSteady ℓ L x).deriv

/-- Curvature of the steady profile: `W''(x) = cosh ((L - x)/ℓ) / ℓ²`. -/
theorem hasDerivAt_deriv_sealedSteady (ℓ L x : ℝ) :
    HasDerivAt (deriv (sealedSteady ℓ L)) (cosh ((L - x) / ℓ) / ℓ ^ 2) x := by
  rw [deriv_sealedSteady]
  have h1 : HasDerivAt (fun y => (L - y) / ℓ) (-1 / ℓ) x := by
    simpa using ((hasDerivAt_id x).const_sub L).div_const ℓ
  convert h1.sinh.const_mul (-1 / ℓ) using 1
  · funext y; ring
  · ring

/-- The steady profile solves the steady cable equation `ℓ² W'' = W`. -/
theorem sealedSteady_steady {ℓ : ℝ} (hℓ : ℓ ≠ 0) (L x : ℝ) :
    ℓ ^ 2 * deriv (deriv (sealedSteady ℓ L)) x = sealedSteady ℓ L x := by
  rw [(hasDerivAt_deriv_sealedSteady ℓ L x).deriv, sealedSteady]
  field_simp

/-- Sealed far end: `W'(L) = 0`. -/
theorem deriv_sealedSteady_length (ℓ L : ℝ) : deriv (sealedSteady ℓ L) L = 0 := by
  simp [deriv_sealedSteady]

/-- Slope at the injection end: `W'(0) = -sinh (L / ℓ) / ℓ`. -/
theorem deriv_sealedSteady_zero (ℓ L : ℝ) :
    deriv (sealedSteady ℓ L) 0 = -sinh (L / ℓ) / ℓ := by
  simp [deriv_sealedSteady]

/-- Charging transient `V t x = c cosh ((L - x)/ℓ) + ∑_{n ∈ s} a n e^{-k_n t} cos (n π x / L)`:
steady response to a constant injected current at `x = 0` plus a decaying sealed-end
expansion. -/
noncomputable def chargingSum (τ ℓ L c : ℝ) (s : Finset ℕ) (a : ℕ → ℝ) (t x : ℝ) : ℝ :=
  c * sealedSteady ℓ L x + cableSum τ ℓ L s a t x

/-- The charging transient solves the cable equation at every time and position. -/
theorem isCableSolution_chargingSum {τ ℓ : ℝ} (hτ : τ ≠ 0) (hℓ : ℓ ≠ 0) (L c : ℝ)
    (s : Finset ℕ) (a : ℕ → ℝ) :
    IsCableSolution τ ℓ L univ (chargingSum τ ℓ L c s a) := by
  have htime : ∀ t x, HasDerivAt (fun r => chargingSum τ ℓ L c s a r x)
      (∑ n ∈ s, a n * (-decayRate τ ℓ L n * exp (-decayRate τ ℓ L n * t) * cosMode L n x)) t :=
    fun t x => by
      unfold chargingSum
      exact (hasDerivAt_cableSum_time τ ℓ L s a t x).const_add (c * sealedSteady ℓ L x)
  have hspace : ∀ t x, HasDerivAt (chargingSum τ ℓ L c s a t)
      (c * deriv (sealedSteady ℓ L) x +
        ∑ n ∈ s, a n * (exp (-decayRate τ ℓ L n * t) * deriv (cosMode L n) x)) x := fun t x =>
    (((hasDerivAt_sealedSteady ℓ L x).const_mul c).congr_deriv
      (by rw [deriv_sealedSteady])).add (hasDerivAt_cableSum_space τ ℓ L s a t x)
  have hderiv : ∀ t, deriv (chargingSum τ ℓ L c s a t) = fun x =>
      c * deriv (sealedSteady ℓ L) x +
        ∑ n ∈ s, a n * (exp (-decayRate τ ℓ L n * t) * deriv (cosMode L n) x) :=
    fun t => funext fun x => (hspace t x).deriv
  have hspace2 : ∀ t x, HasDerivAt (deriv (chargingSum τ ℓ L c s a t))
      (c * deriv (deriv (sealedSteady ℓ L)) x + ∑ n ∈ s, a n *
        (exp (-decayRate τ ℓ L n * t) * (-(n * π / L) ^ 2 * cosMode L n x))) x := fun t x => by
    rw [hderiv]
    refine (((hasDerivAt_deriv_sealedSteady ℓ L x).const_mul c).congr_deriv ?_).add ?_
    · rw [(hasDerivAt_deriv_sealedSteady ℓ L x).deriv]
    · rw [← deriv_cableSum_space]; exact hasDerivAt_deriv_cableSum_space τ ℓ L s a t x
  refine ⟨fun t _ x _ => (htime t x).differentiableAt,
    fun t _ x _ => (hspace t x).differentiableAt,
    fun t _ x _ => (hspace2 t x).differentiableAt, fun t _ x hx => ?_⟩
  rw [(htime t x).deriv, (hspace2 t x).deriv]
  have hcable := (isCableSolution_cableSum hτ ℓ L s a).cable t (mem_univ _) x hx
  rw [(hasDerivAt_cableSum_time τ ℓ L s a t x).deriv,
    (hasDerivAt_deriv_cableSum_space τ ℓ L s a t x).deriv] at hcable
  have hW := sealedSteady_steady hℓ L x
  unfold chargingSum
  linear_combination hcable - c * hW

/-- The charging transient keeps the far end sealed, `∂ₓV(t, L) = 0`, and carries a constant
axial gradient `∂ₓV(t, 0) = -c sinh (L / ℓ) / ℓ` (constant injected current) at `x = 0`. -/
theorem deriv_chargingSum_ends {L : ℝ} (hL : L ≠ 0) (τ ℓ c : ℝ) (s : Finset ℕ) (a : ℕ → ℝ)
    (t : ℝ) :
    deriv (chargingSum τ ℓ L c s a t) L = 0 ∧
      deriv (chargingSum τ ℓ L c s a t) 0 = -c * sinh (L / ℓ) / ℓ := by
  have hd : deriv (chargingSum τ ℓ L c s a t) = fun x =>
      c * deriv (sealedSteady ℓ L) x + deriv (cableSum τ ℓ L s a t) x := by
    funext x
    rw [show chargingSum τ ℓ L c s a t = fun y => c * sealedSteady ℓ L y + cableSum τ ℓ L s a t y
      from rfl, deriv_fun_add ((hasDerivAt_sealedSteady ℓ L x).differentiableAt.const_mul c)
      (hasDerivAt_cableSum_space τ ℓ L s a t x).differentiableAt,
      deriv_const_mul _ (hasDerivAt_sealedSteady ℓ L x).differentiableAt]
  have hs := sealedEnds_cableSum hL τ ℓ s a t (mem_univ _)
  rw [hd]
  refine ⟨?_, ?_⟩
  · simp only
    rw [deriv_sealedSteady_length, hs.2, mul_zero, add_zero]
  · simp only
    rw [deriv_sealedSteady_zero, hs.1, add_zero]
    ring

/-- The charging transient converges to the steady profile `c cosh ((L - x)/ℓ)`. -/
theorem tendsto_chargingSum {τ : ℝ} (hτ : 0 < τ) (ℓ L c : ℝ) (s : Finset ℕ) (a : ℕ → ℝ)
    (x : ℝ) :
    Tendsto (fun t => chargingSum τ ℓ L c s a t x) atTop (𝓝 (c * sealedSteady ℓ L x)) := by
  unfold chargingSum
  simpa only [add_zero] using (tendsto_cableSum hτ ℓ L s a x).const_add (c * sealedSteady ℓ L x)

end MathlibExt.Biology.Biophysics.CableTimeDependent

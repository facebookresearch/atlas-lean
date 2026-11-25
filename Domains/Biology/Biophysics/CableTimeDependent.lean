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
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-!
# Time-dependent passive cable with sealed ends, and its response to localized input

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
  self-inner-products `∫₀ᴸ cos (n π x / L)² dx` equal to `L` (`n = 0`) and `L / 2` (`n ≥ 1`),
  the squared `L²` norms when `L > 0` (`integral_cosMode_mul_cosMode`).
* Rates. Mode `n` evolves as `e^{-k_n t}` with `k_n = (1 + ℓ² (n π / L)²) / τ` (`decayRate`),
  and `k_0 = 1 / τ` (`decayRate_zero`). For `τ > 0` these are decay rates: `1 / τ ≤ k_n`
  (`one_div_le_decayRate`) and `k_n` is strictly increasing for `ℓ, L ≠ 0`
  (`decayRate_strictMono`). For `τ ≠ 0`: Rall's ratio `k_n / k_0 = 1 + (n π ℓ / L)²`
  (`decayRate_div_decayRate_zero`) and Rall's electrotonic-length formula
  `L / ℓ = π / √(k₁ / k₀ - 1)` (`div_eq_pi_div_sqrt_decayRate`).
* Finite expansion `cableSum`: `∑_{n ∈ s} a n e^{-k_n t} cos (n π x / L)` solves the equation
  at all times (`isCableSolution_cableSum`) with sealed ends (`sealedEnds_cableSum`); its
  `n`-th coefficient is `a n e^{-k_n t}` times the mode's self-inner-product
  (`integral_cableSum_mul_cosMode`); for `τ > 0` it obeys the bound
  `e^{-t/τ} ∑ |a n|`, uniform in `x` (`abs_cableSum_le`), and tends to `0` at every position
  (`tendsto_cableSum`); without the uniform mode the bound improves to rate `k₁`
  (`abs_cableSum_le_of_zero_notMem`), and equalizes: `e^{t/τ} V t x → a₀`
  (`tendsto_exp_mul_cableSum`).
* Infinite expansion `cableSeries` with `τ > 0`, `∑ |a n| < ∞` and `ℓ ≠ 0`: termwise
  differentiable for `t > 0`, solves the equation on `t > 0` (`isCableSolution_cableSeries`) with
  sealed ends (`sealedEnds_cableSeries`), initial profile `∑ a n cos (n π x / L)`
  (`cableSeries_time_zero`), the bound `e^{-t/τ} ∑ |a n|`, uniform in `x`
  (`abs_cableSeries_le`), convergence to `0` at every position (`tendsto_cableSeries`) and
  mode-by-mode coefficients `a n e^{-k_n t}` (`integral_cableSeries_mul_cosMode`).
* Arbitrary sealed solutions (`modeCoeff_eq_mul_exp`): for every classical sealed solution on an
  open preconnected time set `T` with `∂ₜV` jointly continuous and `∂ₓ²V` continuous in `x`,
  each cosine coefficient `c_n(t) = ∫₀ᴸ V t x cos (n π x / L) dx` (`modeCoeff`) obeys the
  exponential evolution law `c_n(t) = c_n(t₀) e^{-k_n (t - t₀)}`, and the total potential obeys
  `∫₀ᴸ V t = (∫₀ᴸ V t₀) e^{-(t - t₀) / τ}` (`integral_eq_mul_exp`). These need only `τ ≠ 0`, so
  they include growth when `τ < 0`. For `τ > 0` they are decay laws: `c_n → 0`
  (`tendsto_modeCoeff`), and the total potential decays at exactly the membrane rate `1 / τ`.
* Steady state, minimally restated. `sealedSteady ℓ L x = cosh ((L - x) / ℓ)` solves
  `ℓ² W'' = W` (`sealedSteady_steady`), is sealed at `L`, and has slope `-sinh (L / ℓ) / ℓ` at
  `0`. The charging transient `chargingSum` (steady profile plus a finite expansion) solves the
  cable equation (`isCableSolution_chargingSum`), has a sealed far end and a constant gradient
  at `x = 0` (`deriv_chargingSum_ends`), and converges to the steady profile
  (`tendsto_chargingSum`).
* Bounded coefficients. A time shift (`cableSeries_eq_shift`) and the summability of
  `e^{-k_n ε}` for `ε > 0` (`summable_exp_neg_decayRate`) extend the infinite expansion to
  coefficients that are only bounded: it solves the equation on `t > 0`
  (`isCableSolution_cableSeries_of_bounded`), has sealed ends
  (`sealedEnds_cableSeries_of_bounded`), coefficients `a n e^{-k_n t}`
  (`integral_cableSeries_mul_cosMode_of_bounded`) and decays (`tendsto_cableSeries_of_bounded`).
* Green's function of the sealed cable (`sealedGreen τ ℓ L x₀`): for `τ > 0`, `ℓ ≠ 0`, `0 < L`
  and `x₀ ∈ [0, L]`, the response at times `t > 0` to a unit charge injected at `x₀` at time `0`,
  an instantaneous spatially localized synaptic input, with coefficients `greenCoeff L x₀ n`
  (`1 / L`, then `(2 / L) cos (n π x₀ / L)`). The series is defined for all real inputs (it is `0`
  when `L = 0`). The results below assume `τ > 0` and `ℓ, L ≠ 0` and accept every real `x₀`,
  except the symmetries, which hold for all real inputs; outside the physical range it is the
  even, `2L`-periodic extension in `x₀` (`sealedGreen_neg_source`,
  `sealedGreen_add_two_mul_source`), so a source outside `[0, L]` is its image inside, and `L < 0`
  negates the kernel (`sealedGreen_neg_length`). For `t > 0` it solves the equation with sealed
  ends (`isCableSolution_sealedGreen`, `sealedEnds_sealedGreen`), its
  `n`-th cosine coefficient is `e^{-k_n t} cos (n π x₀ / L)`, the pairing of `δ_{x₀}` with the
  mode decayed at rate `k_n` (`integral_sealedGreen_mul_cosMode`), its total potential is
  `e^{-t/τ}` (`integral_sealedGreen`), it is reciprocal, `G(t, x; x₀) = G(t, x₀; x)`
  (`sealedGreen_comm`), and it decays (`tendsto_sealedGreen`). Superposing responses reproduces the
  expansion of every absolutely convergent cosine profile (`integral_sealedGreen_mul_cosSeries`),
  and the Green's function satisfies the semigroup law
  `∫₀ᴸ G(s, x; y) G(t, y; z) dy = G(t + s, x; z)` (`integral_sealedGreen_mul_sealedGreen`).
* Green's function of the infinite cable (`infiniteGreen τ ℓ x₀`):
  `e^{-t/τ} / √(4 π D t) · exp (-(x - x₀)² / (4 D t))` with `D = ℓ² / τ`. It solves the equation
  at every `t > 0` and every `x ∈ ℝ` (`infiniteGreen_cable`; restricted to a segment `[0, L]`,
  `isCableSolution_infiniteGreen`), is positive (`infiniteGreen_pos`), has total charge
  `e^{-t/τ}` (`integral_infiniteGreen`), is symmetric (`infiniteGreen_comm`), peaks at the input
  site (`infiniteGreen_le`), and vanishes away from it as `t → 0⁺`
  (`tendsto_infiniteGreen_of_ne`).

## Scope

* Completeness of the cosine system is not formalized, so a sealed solution is not identified
  with its expansion; `modeCoeff_eq_mul_exp` gives the exponential evolution of every
  coefficient instead.
* The infinite expansion assumes absolutely summable coefficients (not merely square-summable
  ones), and its continuity at `t = 0` is not stated.
* `modeCoeff_eq_mul_exp` needs `t, t₀` in the open set `T`, so the initial time itself is
  excluded unless `T` contains it.
* Spatial derivatives at the ends are two-sided: profiles are functions on `ℝ`, differentiable
  across `0` and `L`. The even reflection of a sealed `C²` profile on `[0, L]` qualifies.
* Axial current appears only as the gradient `∂ₓV`; the axial resistance, the length constant
  `√(r_m / r_i)` and the semi-infinite and steady-state input-resistance facts are not
  restated here.
* A synaptic input is modeled as an instantaneous unit charge. Responses to time-varying synaptic
  currents (Duhamel's integral of the Green's function) are not stated.
* The sealed Green's function is characterized through its cosine coefficients. Its convergence to
  `δ_{x₀}` as `t → 0⁺`, its positivity and its method-of-images form are not formalized. For the
  infinite cable, the input's localization is stated pointwise away from `x₀` together with the
  total charge, not as weak convergence against test functions.

## References

* W. Rall, *Time constants and electrotonic length of membrane cylinders and neurons*,
  Biophys. J. 9 (1969), 1483–1508: the sealed-end cosine series
  `V = ∑ B_n cos (n π X / L) e^{-(1 + (n π / L)²) T}` and `L = n π / √(τ₀ / τ_n - 1)`.
* J. Keener and J. Sneyd, *Mathematical Physiology I*, 2nd ed., Springer (2009), §4.1 (the
  cable equation).
* C. Koch, *Biophysics of Computation*, Oxford University Press (1999), ch. 2.
* H. C. Tuckwell, *Introduction to Theoretical Neurobiology, Vol. 1*, Cambridge University Press
  (1988): Green's functions of the cable equation.

Section and chapter labels above are not checked against the texts.
-/

@[expose] public section

open Real Set Filter Topology intervalIntegral MeasureTheory
open scoped Interval

namespace MathlibExt.Biology.Biophysics.CableTimeDependent

/-! ### Sealed-end (Neumann) cosine modes -/

/-- The `n`-th sealed-end mode `x ↦ cos (n π x / L)` of a cable of length `L`. With `u / 0 = 0`
every mode is the constant `1` when `L = 0`. -/
noncomputable def cosMode (L : ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  cos (n * π / L * x)

/-- Slope of the `n`-th mode: `(cos (n π x / L))' = -(n π / L) sin (n π x / L)` (both `0` when
`L = 0`, by `u / 0 = 0`). -/
theorem hasDerivAt_cosMode (L : ℝ) (n : ℕ) (x : ℝ) :
    HasDerivAt (cosMode L n) (-(n * π / L) * sin (n * π / L * x)) x := by
  have h := ((hasDerivAt_id x).const_mul (n * π / L)).cos
  simp only [mul_one, id] at h
  unfold cosMode
  convert h using 1
  ring

/-- The derivative of the `n`-th mode, as a function: `x ↦ -(n π / L) sin (n π x / L)`. -/
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

/-- Eigenvalue equation: `(cos (n π x / L))'' = -(n π / L)² cos (n π x / L)`, a classical second
derivative (the eigenvalue is `0` when `L = 0`, by `u / 0 = 0`). -/
theorem deriv_deriv_cosMode (L : ℝ) (n : ℕ) (x : ℝ) :
    deriv (deriv (cosMode L n)) x = -(n * π / L) ^ 2 * cosMode L n x :=
  (hasDerivAt_deriv_cosMode L n x).deriv

/-- Sealed left end: the mode has zero slope (zero axial current) at `x = 0`. -/
theorem deriv_cosMode_zero (L : ℝ) (n : ℕ) : deriv (cosMode L n) 0 = 0 := by
  simp [deriv_cosMode]

/-- Sealed right end: for `L ≠ 0`, the mode has zero slope (zero axial current) at `x = L`. -/
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

/-- Orthogonality of the sealed-end modes on `[0, L]`, for `L ≠ 0`:
`∫₀ᴸ cos (m π x / L) cos (n π x / L) dx` is `0` for `m ≠ n`, `L / 2` for `m = n ≥ 1`, and `L`
for `m = n = 0`. The integral is oriented: for `L < 0` the values `L` and `L / 2` are negative. -/
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

/-- Rate of the `n`-th sealed-end mode of the cable equation `τ V_t = ℓ² V_xx - V` on
`[0, L]`: for `τ ≠ 0` the mode evolves as `e^{-k_n t}` with `k_n = (1 + ℓ² (n π / L)²) / τ`, the
reciprocal of Rall's `n`-th equalizing time constant. It is a decay rate (`0 < k_n`,
`decayRate_pos`) when `τ > 0`. With `u / 0 = 0`, `k_n = 0` when `τ = 0` and `k_n = 1 / τ` when
`L = 0`. -/
noncomputable def decayRate (τ ℓ L : ℝ) (n : ℕ) : ℝ :=
  (1 + ℓ ^ 2 * (n * π / L) ^ 2) / τ

/-- The uniform mode's rate is the membrane rate `1 / τ` (both `0` when `τ = 0`). -/
theorem decayRate_zero (τ ℓ L : ℝ) : decayRate τ ℓ L 0 = 1 / τ := by simp [decayRate]

/-- For `τ > 0`, no mode decays more slowly than the membrane rate: `1 / τ ≤ k_n`. -/
theorem one_div_le_decayRate {τ : ℝ} (hτ : 0 < τ) (ℓ L : ℝ) (n : ℕ) :
    1 / τ ≤ decayRate τ ℓ L n := by
  unfold decayRate
  gcongr
  nlinarith [sq_nonneg ℓ, sq_nonneg (n * π / L), mul_nonneg (sq_nonneg ℓ) (sq_nonneg (n * π / L))]

/-- Every mode decays: `0 < k_n` for `τ > 0`. -/
theorem decayRate_pos {τ : ℝ} (hτ : 0 < τ) (ℓ L : ℝ) (n : ℕ) : 0 < decayRate τ ℓ L n :=
  (one_div_pos.mpr hτ).trans_le (one_div_le_decayRate hτ ℓ L n)

/-- For `τ > 0`, `ℓ ≠ 0` and `L ≠ 0`, higher modes decay strictly faster: `k_m < k_n` for
`m < n`. -/
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

/-- Rall's ratio, for `τ ≠ 0`: `k_n / k_0 = τ₀ / τ_n = 1 + (n π ℓ / L)²` (the right side is `1`
when `L = 0`, by `u / 0 = 0`). -/
theorem decayRate_div_decayRate_zero {τ : ℝ} (hτ : τ ≠ 0) (ℓ L : ℝ) (n : ℕ) :
    decayRate τ ℓ L n / decayRate τ ℓ L 0 = 1 + (n * π * ℓ / L) ^ 2 := by
  rw [decayRate_zero]
  unfold decayRate
  field_simp

/-- Rall's electrotonic-length formula, for `τ ≠ 0`, `ℓ > 0` and `L > 0`: the cable length in
units of the length constant is
recovered from the rates `k₀` and `k₁` (the two slowest decay rates when `τ > 0`),
`L / ℓ = π / √(k₁ / k₀ - 1)`. -/
theorem div_eq_pi_div_sqrt_decayRate {τ ℓ L : ℝ} (hτ : τ ≠ 0) (hℓ : 0 < ℓ) (hL : 0 < L) :
    L / ℓ = π / √(decayRate τ ℓ L 1 / decayRate τ ℓ L 0 - 1) := by
  rw [decayRate_div_decayRate_zero hτ, add_sub_cancel_left, Nat.cast_one, one_mul,
    sqrt_sq (by positivity)]
  field_simp

/-! ### The cable equation and its separated solutions -/

/-- `V t x` is a classical solution of the passive cable equation `τ ∂ₜV = ℓ² ∂ₓ²V - V` on the
cable `[0, L]` at the times in `T`: `V (·) x` is differentiable at `t`, `V t` is twice
differentiable at `x`, and the equation holds pointwise. No initial or boundary condition is
included; when `L < 0` the interval is empty and every `V` qualifies. -/
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
`IsCableSolution` on `[0, L]` with `L ≥ 0`, which then makes `V t` differentiable at both
ends. -/
def SealedEnds (L : ℝ) (T : Set ℝ) (V : ℝ → ℝ → ℝ) : Prop :=
  ∀ t ∈ T, deriv (V t) 0 = 0 ∧ deriv (V t) L = 0

/-- The finite sealed-end eigenfunction expansion
`V t x = ∑_{n ∈ s} a n e^{-k_n t} cos (n π x / L)`, defined for all real inputs with the
conventions of `decayRate` and `cosMode` (every `k_n = 0` when `τ = 0`, every mode `1` when
`L = 0`). -/
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

/-- For `τ ≠ 0`, the finite expansion solves the cable equation at every time and position. -/
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

/-- For `L ≠ 0`, the finite expansion has sealed ends at every time. -/
theorem sealedEnds_cableSum {L : ℝ} (hL : L ≠ 0) (τ ℓ : ℝ) (s : Finset ℕ) (a : ℕ → ℝ) :
    SealedEnds L univ (cableSum τ ℓ L s a) := fun t _ => by
  rw [deriv_cableSum_space]
  simp [deriv_cosMode_zero, deriv_cosMode_length hL]

/-- Initial profile of the finite expansion: `V 0 x = ∑_{n ∈ s} a n cos (n π x / L)`. -/
theorem cableSum_time_zero (τ ℓ L : ℝ) (s : Finset ℕ) (a : ℕ → ℝ) (x : ℝ) :
    cableSum τ ℓ L s a 0 x = ∑ n ∈ s, a n * cosMode L n x := by
  simp [cableSum]

/-- For `τ > 0`, decay rates are monotone in the mode number (no nondegeneracy needed: when
`ℓ = 0` or `L = 0` every rate is `1 / τ`). -/
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

/-- Uniform decay of the finite expansion at the membrane rate: for `τ > 0` and `t ≥ 0`,
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

/-- For `τ > 0`, without the uniform mode (`0 ∉ s`), the finite expansion decays at least at the
first nonuniform rate `k₁`: for `t ≥ 0`, `|V t x| ≤ e^{-k₁ t} ∑ |a n|`. -/
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

/-- Splitting off the uniform mode: for `0 ∉ s`, the expansion over `insert 0 s` is
`a₀ e^{-t/τ}` plus the expansion over `s`, for every real `τ` (at `τ = 0`, `e^{-t/τ} = 1`). -/
theorem cableSum_insert_zero (τ ℓ L : ℝ) {s : Finset ℕ} (hs : 0 ∉ s) (a : ℕ → ℝ) (t x : ℝ) :
    cableSum τ ℓ L (insert 0 s) a t x = a 0 * exp (-t / τ) + cableSum τ ℓ L s a t x := by
  unfold cableSum
  rw [Finset.sum_insert hs, decayRate_zero, cosMode_zero_mode, mul_one]
  have e : -(1 / τ) * t = -t / τ := by ring
  rw [e]

/-- For `τ > 0`, the finite expansion decays to rest at every position (the bound
`abs_cableSum_le` is uniform in `x`). -/
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

/-- Equalization (Rall): for `τ > 0`, `ℓ ≠ 0`, `L ≠ 0` and the expansion over `insert 0 s` with
`0 ∉ s`, after rescaling by the membrane decay `e^{t/τ}` the potential tends to the uniform-mode
coefficient `a₀` at every position, because every nonuniform mode decays strictly faster than
`1 / τ`. -/
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

/-- Mode-by-mode coefficients of the finite expansion, for `L ≠ 0`: the `n`-th cosine coefficient
at time `t` is `a n e^{-k_n t}` times the mode's self-inner-product `∫₀ᴸ cos (n π x / L)² dx` (`L`
for `n = 0`, `L / 2` otherwise) if `n ∈ s`, and `0` otherwise; the integral is oriented. -/
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

/-- The `n`-th cosine coefficient `∫₀ᴸ V t x cos (n π x / L) dx` of the profile `V t`. The
integral is oriented, and it is `0` when the integrand is not integrable on the interval. -/
noncomputable def modeCoeff (L : ℝ) (V : ℝ → ℝ → ℝ) (n : ℕ) (t : ℝ) : ℝ :=
  ∫ x in (0 : ℝ)..L, V t x * cosMode L n x

/-- Two integrations by parts against a sealed-end mode: for `L > 0`, if `f` and `f'` are
differentiable at every point of `[0, L]` (two-sided), `f''` is continuous on `[0, L]` and
`f'(0) = f'(L) = 0`, then
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

/-- Differentiation of a mode coefficient under the integral sign, for `L > 0`, `T` open and a
profile that is differentiable in time at the times of `T`, continuous in `x` on `[0, L]`, and
whose time derivative is jointly continuous on `T × [0, L]`. -/
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

/-- **Mode-by-mode exponential evolution of an arbitrary sealed solution.** Let `V` be a
classical solution of `τ ∂ₜV = ℓ² ∂ₓ²V - V` (`τ ≠ 0`) on `[0, L]`, `L > 0`, with sealed ends,
at the times of an open interval-like (open, preconnected) set `T`, with `∂ₜV` jointly continuous
on `T × [0, L]` and `∂ₓ²V` continuous in `x`. Then every cosine coefficient evolves exactly as
`c_n(t) = c_n(t₀) e^{-k_n (t - t₀)}` for `t, t₀ ∈ T`. This is decay at rate `k_n > 0` when
`τ > 0` (`tendsto_modeCoeff`); for `τ < 0`, `k_0 = 1 / τ < 0` and a nonzero uniform coefficient
grows. -/
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
`V t x = ∑_{n ≥ 0} a n e^{-k_n t} cos (n π x / L)`, with the convention that a non-summable series
has sum `0`. -/
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

/-- For `τ > 0`, `t ≥ 0` and absolutely summable coefficients the expansion converges
absolutely. -/
theorem summable_cableSeries {τ : ℝ} (hτ : 0 < τ) (ℓ L : ℝ) {a : ℕ → ℝ}
    (ha : Summable fun n => |a n|) {t : ℝ} (ht : 0 ≤ t) (x : ℝ) :
    Summable fun n => a n * (exp (-decayRate τ ℓ L n * t) * cosMode L n x) :=
  summable_mul_of_abs_le ha fun n => abs_term_le hτ ℓ L n ht x

/-- Initial profile of the expansion: the cosine series `∑ a n cos (n π x / L)`. No summability
is needed: the two series have the same terms. -/
theorem cableSeries_time_zero (τ ℓ L : ℝ) (a : ℕ → ℝ) (x : ℝ) :
    cableSeries τ ℓ L a 0 x = ∑' n, a n * cosMode L n x := by
  simp [cableSeries]

/-- Uniform decay of the expansion at the membrane rate: for `τ > 0`, absolutely summable
coefficients and `t ≥ 0`, `|V t x| ≤ e^{-t/τ} ∑ |a n|`. -/
theorem abs_cableSeries_le {τ : ℝ} (hτ : 0 < τ) (ℓ L : ℝ) {a : ℕ → ℝ}
    (ha : Summable fun n => |a n|) {t : ℝ} (ht : 0 ≤ t) (x : ℝ) :
    |cableSeries τ ℓ L a t x| ≤ exp (-t / τ) * ∑' n, |a n| := by
  rw [← Real.norm_eq_abs, ← tsum_mul_left]
  refine tsum_of_norm_bounded (ha.mul_left (exp (-t / τ))).hasSum fun n => ?_
  rw [Real.norm_eq_abs, abs_mul, mul_comm]
  exact mul_le_mul_of_nonneg_right (abs_term_le hτ ℓ L n ht x) (abs_nonneg _)

/-- For `τ > 0` and absolutely summable coefficients, the expansion decays to rest at every
position (the bound `abs_cableSeries_le` is uniform in `x`). -/
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

/-- Termwise spatial differentiation of the expansion at a positive time (`τ > 0`, `ℓ ≠ 0`,
absolutely summable coefficients). -/
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

/-- The spatial derivative of the expansion at a positive time, as a function (`τ > 0`,
`ℓ ≠ 0`, absolutely summable coefficients). -/
theorem deriv_cableSeries_space {τ ℓ : ℝ} (hτ : 0 < τ) (hℓ : ℓ ≠ 0) (L : ℝ) {a : ℕ → ℝ}
    (ha : Summable fun n => |a n|) {t : ℝ} (ht : 0 < t) :
    deriv (cableSeries τ ℓ L a t) = fun x =>
      ∑' n, a n * (exp (-decayRate τ ℓ L n * t) * deriv (cosMode L n) x) :=
  funext fun x => (hasDerivAt_cableSeries_space hτ hℓ L ha ht x).deriv

/-- Termwise second spatial differentiation of the expansion at a positive time (`τ > 0`,
`ℓ ≠ 0`, absolutely summable coefficients). -/
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

/-- Termwise time differentiation of the expansion at a positive time (`τ > 0`, absolutely
summable coefficients). -/
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

/-- For `τ > 0` and `ℓ ≠ 0`, the infinite expansion with absolutely summable coefficients solves
the cable equation at every positive time. -/
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

/-- For `τ > 0`, `ℓ ≠ 0`, `L ≠ 0` and absolutely summable coefficients, the infinite expansion
has sealed ends at every positive time. -/
theorem sealedEnds_cableSeries {τ ℓ L : ℝ} (hτ : 0 < τ) (hℓ : ℓ ≠ 0) (hL : L ≠ 0)
    {a : ℕ → ℝ} (ha : Summable fun n => |a n|) :
    SealedEnds L (Ioi 0) (cableSeries τ ℓ L a) := fun t ht => by
  rw [deriv_cableSeries_space hτ hℓ L ha ht]
  simp [deriv_cosMode_zero, deriv_cosMode_length hL]

/-- Coefficients of the infinite expansion: for `τ > 0`, `L ≠ 0`, absolutely summable
coefficients and `t ≥ 0`, its `n`-th cosine coefficient (an oriented integral) is
`a n e^{-k_n t}` times the mode's self-inner-product `∫₀ᴸ cos (n π x / L)² dx` (`L` for `n = 0`,
`L / 2` otherwise). -/
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

/-! ### Consequences of the exponential evolution law -/

/-- For `τ > 0` and `L > 0`, every cosine coefficient of a sealed solution on `t > 0`, with
`∂ₜV` jointly continuous and `∂ₓ²V` continuous in `x`, decays to `0`. -/
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

/-- Exponential evolution of the total (integrated) potential of a sealed solution on `[0, L]`,
`L > 0`, at the times of an open preconnected set `T`, with `∂ₜV` jointly continuous and `∂ₓ²V`
continuous in `x`: `∫₀ᴸ V t = (∫₀ᴸ V t₀) e^{-(t - t₀)/τ}` for `τ ≠ 0` and `t, t₀ ∈ T`. For `τ > 0`
this is decay at exactly the membrane rate `1 / τ`; for `τ < 0` it is growth. -/
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

/-- Steady profile `x ↦ cosh ((L - x) / ℓ)` of a cable sealed at `x = L`. With `u / 0 = 0` it is
the constant `1` when `ℓ = 0`. -/
noncomputable def sealedSteady (ℓ L : ℝ) (x : ℝ) : ℝ :=
  cosh ((L - x) / ℓ)

/-- Slope of the steady profile: `W'(x) = -sinh ((L - x)/ℓ) / ℓ` (both `0` when `ℓ = 0`). -/
theorem hasDerivAt_sealedSteady (ℓ L x : ℝ) :
    HasDerivAt (sealedSteady ℓ L) (-sinh ((L - x) / ℓ) / ℓ) x := by
  have h1 : HasDerivAt (fun y => (L - y) / ℓ) (-1 / ℓ) x := by
    simpa using ((hasDerivAt_id x).const_sub L).div_const ℓ
  unfold sealedSteady
  convert h1.cosh using 1
  ring

/-- The slope of the steady profile, as a function: `x ↦ -sinh ((L - x)/ℓ) / ℓ`. -/
theorem deriv_sealedSteady (ℓ L : ℝ) :
    deriv (sealedSteady ℓ L) = fun x => -sinh ((L - x) / ℓ) / ℓ :=
  funext fun x => (hasDerivAt_sealedSteady ℓ L x).deriv

/-- Curvature of the steady profile: `W''(x) = cosh ((L - x)/ℓ) / ℓ²` (both `0` when `ℓ = 0`). -/
theorem hasDerivAt_deriv_sealedSteady (ℓ L x : ℝ) :
    HasDerivAt (deriv (sealedSteady ℓ L)) (cosh ((L - x) / ℓ) / ℓ ^ 2) x := by
  rw [deriv_sealedSteady]
  have h1 : HasDerivAt (fun y => (L - y) / ℓ) (-1 / ℓ) x := by
    simpa using ((hasDerivAt_id x).const_sub L).div_const ℓ
  convert h1.sinh.const_mul (-1 / ℓ) using 1
  · funext y; ring
  · ring

/-- For `ℓ ≠ 0`, the steady profile solves the steady cable equation `ℓ² W'' = W`. -/
theorem sealedSteady_steady {ℓ : ℝ} (hℓ : ℓ ≠ 0) (L x : ℝ) :
    ℓ ^ 2 * deriv (deriv (sealedSteady ℓ L)) x = sealedSteady ℓ L x := by
  rw [(hasDerivAt_deriv_sealedSteady ℓ L x).deriv, sealedSteady]
  field_simp

/-- Sealed far end: `W'(L) = 0`. -/
theorem deriv_sealedSteady_length (ℓ L : ℝ) : deriv (sealedSteady ℓ L) L = 0 := by
  simp [deriv_sealedSteady]

/-- Slope at the injection end: `W'(0) = -sinh (L / ℓ) / ℓ` (both `0` when `ℓ = 0`). -/
theorem deriv_sealedSteady_zero (ℓ L : ℝ) :
    deriv (sealedSteady ℓ L) 0 = -sinh (L / ℓ) / ℓ := by
  simp [deriv_sealedSteady]

/-- Charging transient `V t x = c cosh ((L - x)/ℓ) + ∑_{n ∈ s} a n e^{-k_n t} cos (n π x / L)`:
steady response to a constant injected current at `x = 0` plus a sealed-end expansion, which
decays when `τ > 0` (`tendsto_chargingSum`). -/
noncomputable def chargingSum (τ ℓ L c : ℝ) (s : Finset ℕ) (a : ℕ → ℝ) (t x : ℝ) : ℝ :=
  c * sealedSteady ℓ L x + cableSum τ ℓ L s a t x

/-- For `τ ≠ 0` and `ℓ ≠ 0`, the charging transient solves the cable equation at every time and
position. -/
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

/-- For `L ≠ 0`, the charging transient keeps the far end sealed, `∂ₓV(t, L) = 0`, and carries a
constant axial gradient `∂ₓV(t, 0) = -c sinh (L / ℓ) / ℓ` (constant injected current) at `x = 0`
(`0` when `ℓ = 0`). -/
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

/-- For `τ > 0`, the charging transient converges to the steady profile `c cosh ((L - x)/ℓ)`. -/
theorem tendsto_chargingSum {τ : ℝ} (hτ : 0 < τ) (ℓ L c : ℝ) (s : Finset ℕ) (a : ℕ → ℝ)
    (x : ℝ) :
    Tendsto (fun t => chargingSum τ ℓ L c s a t x) atTop (𝓝 (c * sealedSteady ℓ L x)) := by
  unfold chargingSum
  simpa only [add_zero] using (tendsto_cableSum hτ ℓ L s a x).const_add (c * sealedSteady ℓ L x)

/-! ### Bounded coefficients at positive times -/

/-- Time shift of the expansion: `V t x = ∑ (a n e^{-k_n ε}) e^{-k_n (t - ε)} cos (n π x / L)`.
No summability is needed: the two series agree term by term. -/
theorem cableSeries_eq_shift (τ ℓ L : ℝ) (a : ℕ → ℝ) (ε t : ℝ) :
    cableSeries τ ℓ L a t =
      cableSeries τ ℓ L (fun n => a n * exp (-decayRate τ ℓ L n * ε)) (t - ε) := by
  funext x
  unfold cableSeries
  refine tsum_congr fun n => ?_
  rw [show -decayRate τ ℓ L n * t = -decayRate τ ℓ L n * ε + -decayRate τ ℓ L n * (t - ε) by ring,
    exp_add]
  ring

/-- For `ε > 0` (and `τ > 0`, `ℓ, L ≠ 0`) the mode factors `e^{-k_n ε}` are summable: they are
dominated by the geometric sequence `e^{-c n}` with `c = ℓ² π² ε / (L² τ)`. -/
theorem summable_exp_neg_decayRate {τ ℓ L : ℝ} (hτ : 0 < τ) (hℓ : ℓ ≠ 0) (hL : L ≠ 0) {ε : ℝ}
    (hε : 0 < ε) : Summable fun n : ℕ => exp (-decayRate τ ℓ L n * ε) := by
  have hc : 0 < ℓ ^ 2 * π ^ 2 / L ^ 2 / τ * ε := by positivity
  refine Summable.of_nonneg_of_le (fun n => (exp_pos _).le) (fun n => ?_)
    (summable_geometric_of_lt_one (exp_pos (-(ℓ ^ 2 * π ^ 2 / L ^ 2 / τ * ε))).le
      (exp_lt_one_iff.mpr (by linarith)))
  rw [← exp_nat_mul, exp_le_exp]
  have hk : decayRate τ ℓ L n * ε = ε / τ + ℓ ^ 2 * π ^ 2 / L ^ 2 / τ * ε * (n : ℝ) ^ 2 := by
    unfold decayRate; field_simp
  have hn : (n : ℝ) ≤ (n : ℝ) ^ 2 := by
    exact_mod_cast (Nat.le_mul_self n).trans_eq (sq n).symm
  have h1 := mul_le_mul_of_nonneg_left hn hc.le
  have h2 : 0 ≤ ε / τ := by positivity
  rw [neg_mul, hk]
  nlinarith

private theorem summable_abs_mul_exp {τ ℓ L : ℝ} (hτ : 0 < τ) (hℓ : ℓ ≠ 0) (hL : L ≠ 0)
    {a : ℕ → ℝ} {B : ℝ} (hB : ∀ n, |a n| ≤ B) {ε : ℝ} (hε : 0 < ε) :
    Summable fun n => |a n * exp (-decayRate τ ℓ L n * ε)| := by
  refine Summable.of_nonneg_of_le (fun n => abs_nonneg _) (fun n => ?_)
    ((summable_exp_neg_decayRate hτ hℓ hL hε).mul_left B)
  rw [abs_mul, abs_exp]
  exact mul_le_mul_of_nonneg_right (hB n) (exp_pos _).le

/-- With merely bounded coefficients (`|a n| ≤ B`, e.g. those of a point charge), the expansion
solves the cable equation at every positive time (`τ > 0`, `ℓ, L ≠ 0`). -/
theorem isCableSolution_cableSeries_of_bounded {τ ℓ L : ℝ} (hτ : 0 < τ) (hℓ : ℓ ≠ 0)
    (hL : L ≠ 0) {a : ℕ → ℝ} {B : ℝ} (hB : ∀ n, |a n| ≤ B) :
    IsCableSolution τ ℓ L (Ioi 0) (cableSeries τ ℓ L a) := by
  -- at time `t`, compare with the expansion shifted by `t / 2`, whose coefficients are summable
  have hW : ∀ t ∈ Ioi (0 : ℝ), IsCableSolution τ ℓ L (Ioi 0)
      (cableSeries τ ℓ L fun n => a n * exp (-decayRate τ ℓ L n * (t / 2))) := fun t ht =>
    isCableSolution_cableSeries hτ hℓ L (summable_abs_mul_exp hτ hℓ hL hB (half_pos ht))
  have hpos : ∀ t ∈ Ioi (0 : ℝ), t - t / 2 ∈ Ioi (0 : ℝ) := fun t ht => by
    simp only [mem_Ioi] at ht ⊢; linarith
  have htime : ∀ t x : ℝ, (fun s => cableSeries τ ℓ L a s x) = fun s =>
      cableSeries τ ℓ L (fun n => a n * exp (-decayRate τ ℓ L n * (t / 2))) (s - t / 2) x :=
    fun t x => funext fun s => by rw [cableSeries_eq_shift τ ℓ L a (t / 2) s]
  refine ⟨fun t ht x hx => ?_, fun t ht x hx => ?_, fun t ht x hx => ?_, fun t ht x hx => ?_⟩
  · rw [htime t x]
    exact (((hW t ht).differentiableAt_time _ (hpos t ht) x hx).hasDerivAt.comp_sub_const t
      (t / 2)).differentiableAt
  · rw [cableSeries_eq_shift τ ℓ L a (t / 2) t]
    exact (hW t ht).differentiableAt_space _ (hpos t ht) x hx
  · rw [cableSeries_eq_shift τ ℓ L a (t / 2) t]
    exact (hW t ht).differentiableAt_deriv_space _ (hpos t ht) x hx
  · have hc := (hW t ht).cable _ (hpos t ht) x hx
    have hd : deriv (fun s => cableSeries τ ℓ L a s x) t = deriv (fun s =>
        cableSeries τ ℓ L (fun n => a n * exp (-decayRate τ ℓ L n * (t / 2))) s x) (t - t / 2) := by
      rw [htime t x]
      exact deriv_comp_sub_const (f := fun s =>
        cableSeries τ ℓ L (fun n => a n * exp (-decayRate τ ℓ L n * (t / 2))) s x) (t / 2) t
    rw [hd, cableSeries_eq_shift τ ℓ L a (t / 2) t]
    exact hc

/-- With bounded coefficients the expansion has sealed ends at every positive time (`τ > 0`,
`ℓ, L ≠ 0`). -/
theorem sealedEnds_cableSeries_of_bounded {τ ℓ L : ℝ} (hτ : 0 < τ) (hℓ : ℓ ≠ 0) (hL : L ≠ 0)
    {a : ℕ → ℝ} {B : ℝ} (hB : ∀ n, |a n| ≤ B) :
    SealedEnds L (Ioi 0) (cableSeries τ ℓ L a) := fun t ht => by
  rw [cableSeries_eq_shift τ ℓ L a (t / 2) t]
  exact sealedEnds_cableSeries hτ hℓ hL (summable_abs_mul_exp hτ hℓ hL hB (half_pos ht)) _
    (by simp only [mem_Ioi] at ht ⊢; linarith)

/-- With bounded coefficients the profile at a positive time is continuous in `x` (`τ > 0`,
`ℓ, L ≠ 0`). -/
theorem continuous_cableSeries_of_bounded {τ ℓ L : ℝ} (hτ : 0 < τ) (hℓ : ℓ ≠ 0) (hL : L ≠ 0)
    {a : ℕ → ℝ} {B : ℝ} (hB : ∀ n, |a n| ≤ B) {t : ℝ} (ht : 0 < t) :
    Continuous (cableSeries τ ℓ L a t) := by
  rw [cableSeries_eq_shift τ ℓ L a (t / 2) t]
  exact continuous_iff_continuousAt.2 fun x => (hasDerivAt_cableSeries_space hτ hℓ L
    (summable_abs_mul_exp hτ hℓ hL hB (half_pos ht)) (by linarith) x).continuousAt

/-- With bounded coefficients (`τ > 0`, `ℓ, L ≠ 0`), the `n`-th cosine coefficient at a positive
time is `a n e^{-k_n t}` times the mode's self-inner-product (`L` for `n = 0`, `L / 2` otherwise);
the integral is oriented. -/
theorem integral_cableSeries_mul_cosMode_of_bounded {τ ℓ L : ℝ} (hτ : 0 < τ) (hℓ : ℓ ≠ 0)
    (hL : L ≠ 0) {a : ℕ → ℝ} {B : ℝ} (hB : ∀ n, |a n| ≤ B) {t : ℝ} (ht : 0 < t) (m : ℕ) :
    ∫ x in (0 : ℝ)..L, cableSeries τ ℓ L a t x * cosMode L m x =
      a m * exp (-decayRate τ ℓ L m * t) * (if m = 0 then L else L / 2) := by
  rw [cableSeries_eq_shift τ ℓ L a t t, sub_self,
    integral_cableSeries_mul_cosMode hτ hL ℓ (summable_abs_mul_exp hτ hℓ hL hB ht) le_rfl m]
  simp

/-- With bounded coefficients the expansion decays to rest at every position (`τ > 0`,
`ℓ, L ≠ 0`). -/
theorem tendsto_cableSeries_of_bounded {τ ℓ L : ℝ} (hτ : 0 < τ) (hℓ : ℓ ≠ 0) (hL : L ≠ 0)
    {a : ℕ → ℝ} {B : ℝ} (hB : ∀ n, |a n| ≤ B) (x : ℝ) :
    Tendsto (fun t => cableSeries τ ℓ L a t x) atTop (𝓝 0) := by
  have h := (tendsto_cableSeries hτ ℓ L (summable_abs_mul_exp hτ hℓ hL hB one_pos) x).comp
    (tendsto_atTop_add_const_right atTop (-1) tendsto_id)
  refine h.congr fun t => ?_
  change cableSeries τ ℓ L (fun n => a n * exp (-decayRate τ ℓ L n * 1)) (t + -1) x =
    cableSeries τ ℓ L a t x
  rw [cableSeries_eq_shift τ ℓ L a 1 t, sub_eq_add_neg]

/-- Integrating an absolutely convergent cosine series against a continuous weight, term by term.
-/
private theorem hasSum_integral_cosSeries_mul {L : ℝ} {b : ℕ → ℝ}
    (hb : Summable fun n => |b n|) {g : ℝ → ℝ} (hg : Continuous g) :
    HasSum (fun n => b n * ∫ y in (0 : ℝ)..L, cosMode L n y * g y)
      (∫ y in (0 : ℝ)..L, (∑' n, b n * cosMode L n y) * g y) := by
  obtain ⟨C, hC⟩ := (isCompact_uIcc (a := (0 : ℝ)) (b := L)).exists_bound_of_continuousOn
    hg.continuousOn
  have heq : (fun n => b n * ∫ y in (0 : ℝ)..L, cosMode L n y * g y) =
      fun n => ∫ y in (0 : ℝ)..L, b n * (cosMode L n y * g y) :=
    funext fun n => (intervalIntegral.integral_const_mul _ _).symm
  rw [heq]
  refine intervalIntegral.hasSum_integral_of_dominated_convergence (fun n _ => |b n| * C)
    (fun n => ?_) (fun n => ?_) ?_ intervalIntegrable_const ?_
  · exact (continuous_const.mul ((continuous_cosMode L n).mul hg)).aestronglyMeasurable
  · refine Eventually.of_forall fun y hy => ?_
    have h2 : |g y| ≤ C := by
      have := hC y (uIoc_subset_uIcc hy); rwa [Real.norm_eq_abs] at this
    have h1 := abs_cosMode_le L n y
    rw [Real.norm_eq_abs, abs_mul, abs_mul]
    calc |b n| * (|cosMode L n y| * |g y|) ≤ |b n| * (1 * C) := by gcongr
      _ = |b n| * C := by ring
  · exact Eventually.of_forall fun _ _ => hb.mul_right C
  · refine Eventually.of_forall fun y _ => ?_
    simpa only [mul_assoc] using
      (summable_mul_of_abs_le hb fun n => abs_cosMode_le L n y).hasSum.mul_right (g y)

/-! ### Green's function of the sealed cable: response to a localized input -/

/-- Cosine coefficients `1 / L` for the uniform mode and `(2 / L) cos (n π x₀ / L)` for `n ≥ 1`.
For `0 < L` and `x₀ ∈ [0, L]` these are the coefficients of a unit point charge at `x₀` on the
sealed cable `[0, L]`: the pairings `cos (n π x₀ / L)` of `δ_{x₀}` with the modes, divided by the
self-inner-products `L` and `L / 2`. The formula is used for every real `x₀` and `L`; it is even
and `2L`-periodic in `x₀` (`greenCoeff_neg_source`, `greenCoeff_add_two_mul_source`), so it does
not single out a source outside `[0, L]` from its image inside. They are bounded
(`abs_greenCoeff_le`), and for `L ≠ 0` not summable (at `L = 0` division by zero makes every
coefficient `0`). -/
noncomputable def greenCoeff (L x₀ : ℝ) (n : ℕ) : ℝ :=
  (if n = 0 then 1 / L else 2 / L) * cosMode L n x₀

/-- The point-charge coefficients are bounded by `2 / |L|` (both sides `0` when `L = 0`). -/
theorem abs_greenCoeff_le (L x₀ : ℝ) (n : ℕ) : |greenCoeff L x₀ n| ≤ 2 / |L| := by
  unfold greenCoeff
  rw [abs_mul]
  have h1 : |(if n = 0 then 1 / L else 2 / L)| ≤ 2 / |L| := by
    split_ifs
    · rw [abs_div, abs_one]; gcongr; norm_num
    · rw [abs_div, abs_two]
  calc _ ≤ 2 / |L| * 1 := mul_le_mul h1 (abs_cosMode_le L n x₀) (abs_nonneg _) (by positivity)
    _ = 2 / |L| := mul_one _

/-- **Green's function of the sealed cable.** The cosine series
`G(t, x; x₀) = e^{-t/τ} / L + (2 / L) ∑_{n ≥ 1} e^{-k_n t} cos (n π x₀ / L) cos (n π x / L)`,
the whole series over `n ≥ 0` (whose `n = 0` term is `e^{-t/τ} / L`) being taken with the
convention that a non-summable series has sum `0`, not the `n ≥ 1` sum alone. With `u / 0 = 0` every
coefficient is `0` when `L = 0`, so `G ≡ 0` there. For `τ > 0` and `ℓ, L ≠ 0` the series
converges absolutely at every `t > 0`. The solution, sealed-end, continuity, coefficient,
total-charge, superposition, semigroup and decay theorems assume these three conditions and
accept every real `x₀`; the symmetries (`sealedGreen_comm`, `sealedGreen_neg_source`,
`sealedGreen_add_two_mul_source`, `sealedGreen_neg_length`) hold for all real inputs.
For `τ > 0`, `ℓ ≠ 0`, `0 < L` and `x₀ ∈ [0, L]` it is the potential at position `x ∈ [0, L]` and
time `t > 0` after a unit charge is injected at `x₀` at time `0` (an instantaneous, spatially
localized synaptic input). Outside that range it is an algebraic extension, not the response to a
point charge at `x₀`: it is even and `2L`-periodic in `x₀`, so a source outside `[0, L]` gives the
kernel of its reflected image inside, and replacing `L` by `-L` negates it. -/
noncomputable def sealedGreen (τ ℓ L x₀ : ℝ) : ℝ → ℝ → ℝ :=
  cableSeries τ ℓ L (greenCoeff L x₀)

/-- For `τ > 0` and `ℓ, L ≠ 0`, the Green's function solves the cable equation at every positive
time. -/
theorem isCableSolution_sealedGreen {τ ℓ L : ℝ} (hτ : 0 < τ) (hℓ : ℓ ≠ 0) (hL : L ≠ 0)
    (x₀ : ℝ) : IsCableSolution τ ℓ L (Ioi 0) (sealedGreen τ ℓ L x₀) :=
  isCableSolution_cableSeries_of_bounded hτ hℓ hL (abs_greenCoeff_le L x₀)

/-- For `τ > 0` and `ℓ, L ≠ 0`, the Green's function has sealed ends at every positive time. -/
theorem sealedEnds_sealedGreen {τ ℓ L : ℝ} (hτ : 0 < τ) (hℓ : ℓ ≠ 0) (hL : L ≠ 0) (x₀ : ℝ) :
    SealedEnds L (Ioi 0) (sealedGreen τ ℓ L x₀) :=
  sealedEnds_cableSeries_of_bounded hτ hℓ hL (abs_greenCoeff_le L x₀)

/-- For `τ > 0` and `ℓ, L ≠ 0`, at a positive time the Green's function is continuous in
position. -/
theorem continuous_sealedGreen {τ ℓ L : ℝ} (hτ : 0 < τ) (hℓ : ℓ ≠ 0) (hL : L ≠ 0) (x₀ : ℝ)
    {t : ℝ} (ht : 0 < t) : Continuous (sealedGreen τ ℓ L x₀ t) :=
  continuous_cableSeries_of_bounded hτ hℓ hL (abs_greenCoeff_le L x₀) ht

/-- **Mode coefficients of the Green's function.** For `τ > 0` and `ℓ, L ≠ 0` (oriented integral),
at every positive time its `n`-th cosine
coefficient is `e^{-k_n t} cos (n π x₀ / L)`: the pairing of `δ_{x₀}` with the `n`-th mode,
decayed at the mode's rate. -/
theorem integral_sealedGreen_mul_cosMode {τ ℓ L : ℝ} (hτ : 0 < τ) (hℓ : ℓ ≠ 0) (hL : L ≠ 0)
    (x₀ : ℝ) {t : ℝ} (ht : 0 < t) (n : ℕ) :
    ∫ x in (0 : ℝ)..L, sealedGreen τ ℓ L x₀ t x * cosMode L n x =
      exp (-decayRate τ ℓ L n * t) * cosMode L n x₀ := by
  rw [sealedGreen, integral_cableSeries_mul_cosMode_of_bounded hτ hℓ hL (abs_greenCoeff_le L x₀)
    ht n]
  unfold greenCoeff
  split_ifs <;> field_simp

/-- **Charge conservation up to membrane leak.** For `τ > 0` and `ℓ, L ≠ 0`, the total potential
after a unit charge decays at exactly the membrane rate: `∫₀ᴸ G(t, x; x₀) dx = e^{-t/τ}` for
`t > 0`, wherever the input is.
For `L < 0` the integral is oriented, which compensates for the sign of the kernel
(`sealedGreen_neg_length`); the physical statement is the case `0 < L`, `x₀ ∈ [0, L]`. -/
theorem integral_sealedGreen {τ ℓ L : ℝ} (hτ : 0 < τ) (hℓ : ℓ ≠ 0) (hL : L ≠ 0) (x₀ : ℝ)
    {t : ℝ} (ht : 0 < t) : ∫ x in (0 : ℝ)..L, sealedGreen τ ℓ L x₀ t x = exp (-t / τ) := by
  have h := integral_sealedGreen_mul_cosMode hτ hℓ hL x₀ ht 0
  simp only [cosMode_zero_mode, mul_one, decayRate_zero] at h
  rw [h]
  congr 1
  ring

/-- **Reciprocity.** The response at `x` to an input at `x₀` equals the response at `x₀` to an
input at `x`, for all real arguments (the two series have the same terms). -/
theorem sealedGreen_comm (τ ℓ L x₀ t x : ℝ) :
    sealedGreen τ ℓ L x₀ t x = sealedGreen τ ℓ L x t x₀ := by
  unfold sealedGreen cableSeries greenCoeff
  exact tsum_congr fun n => by ring

/-- The coefficients are even in the source position. -/
theorem greenCoeff_neg_source (L x₀ : ℝ) : greenCoeff L (-x₀) = greenCoeff L x₀ := by
  funext n
  simp [greenCoeff, cosMode]

/-- The coefficients are `2L`-periodic in the source position (both `0` when `L = 0`). -/
theorem greenCoeff_add_two_mul_source (L x₀ : ℝ) :
    greenCoeff L (x₀ + 2 * L) = greenCoeff L x₀ := by
  funext n
  unfold greenCoeff cosMode
  rcases eq_or_ne L 0 with rfl | hL
  · simp
  · rw [mul_add, show (n : ℝ) * π / L * (2 * L) = n * (2 * π) by field_simp,
      cos_add_nat_mul_two_pi]

/-- **Even extension.** A source at `-x₀` gives the same kernel as one at `x₀`. -/
theorem sealedGreen_neg_source (τ ℓ L x₀ : ℝ) :
    sealedGreen τ ℓ L (-x₀) = sealedGreen τ ℓ L x₀ := by
  rw [sealedGreen, greenCoeff_neg_source, sealedGreen]

/-- **Periodic extension.** A source at `x₀ + 2L` gives the same kernel as one at `x₀`. -/
theorem sealedGreen_add_two_mul_source (τ ℓ L x₀ : ℝ) :
    sealedGreen τ ℓ L (x₀ + 2 * L) = sealedGreen τ ℓ L x₀ := by
  rw [sealedGreen, greenCoeff_add_two_mul_source, sealedGreen]

/-- Replacing `L` by `-L` leaves the modes and decay rates unchanged and negates every
coefficient, so it negates the kernel. -/
theorem sealedGreen_neg_length (τ ℓ L x₀ t x : ℝ) :
    sealedGreen τ ℓ (-L) x₀ t x = -sealedGreen τ ℓ L x₀ t x := by
  unfold sealedGreen cableSeries
  rw [← tsum_neg]
  refine tsum_congr fun n => ?_
  simp only [greenCoeff, cosMode, decayRate, div_neg, neg_mul, cos_neg, neg_sq]
  split_ifs <;> ring

/-- For `τ > 0` and `ℓ, L ≠ 0`, the response to a localized input decays to rest at every
position. -/
theorem tendsto_sealedGreen {τ ℓ L : ℝ} (hτ : 0 < τ) (hℓ : ℓ ≠ 0) (hL : L ≠ 0) (x₀ x : ℝ) :
    Tendsto (fun t => sealedGreen τ ℓ L x₀ t x) atTop (𝓝 0) :=
  tendsto_cableSeries_of_bounded hτ hℓ hL (abs_greenCoeff_le L x₀) x

/-- **Superposition of localized inputs.** Let `τ > 0` and `ℓ, L ≠ 0`. For an initial profile
given by an absolutely convergent cosine series `f y = ∑ a n cos (n π y / L)` and a time `t > 0`,
`∫₀ᴸ G(t, x; y) f y dy = ∑ a n e^{-k_n t} cos (n π x / L)`, the expansion at time `t`. For
`L > 0` this superposes the responses to the charges `f y dy` placed at every `y ∈ [0, L]`; for
`L < 0` the integral is oriented. -/
theorem integral_sealedGreen_mul_cosSeries {τ ℓ L : ℝ} (hτ : 0 < τ) (hℓ : ℓ ≠ 0) (hL : L ≠ 0)
    {a : ℕ → ℝ} (ha : Summable fun n => |a n|) {t : ℝ} (ht : 0 < t) (x : ℝ) :
    ∫ y in (0 : ℝ)..L, sealedGreen τ ℓ L y t x * ∑' n, a n * cosMode L n y =
      cableSeries τ ℓ L a t x := by
  have h := hasSum_integral_cosSeries_mul (L := L) ha (continuous_sealedGreen hτ hℓ hL x ht)
  have hterm : ∀ n, ∫ y in (0 : ℝ)..L, cosMode L n y * sealedGreen τ ℓ L x t y =
      exp (-decayRate τ ℓ L n * t) * cosMode L n x := fun n => by
    have hc : (fun y => cosMode L n y * sealedGreen τ ℓ L x t y) =
        fun y => sealedGreen τ ℓ L x t y * cosMode L n y := funext fun y => mul_comm _ _
    rw [hc]
    exact integral_sealedGreen_mul_cosMode hτ hℓ hL x ht n
  simp_rw [hterm] at h
  have hf : (fun y => sealedGreen τ ℓ L y t x * ∑' n, a n * cosMode L n y) =
      fun y => (∑' n, a n * cosMode L n y) * sealedGreen τ ℓ L x t y :=
    funext fun y => by rw [sealedGreen_comm τ ℓ L y t x, mul_comm]
  rw [hf, ← h.tsum_eq]
  rfl

/-- **Semigroup (Chapman–Kolmogorov) law.** For `τ > 0`, `ℓ, L ≠ 0` and `s, t > 0`,
`∫₀ᴸ G(s, x; y) G(t, y; z) dy = G(t + s, x; z)`. For `L > 0` and `z ∈ [0, L]`, propagating the
response to a unit charge at `z` for time `t` and then for time `s` gives the response at time
`t + s`; for `L < 0` the integral is oriented. -/
theorem integral_sealedGreen_mul_sealedGreen {τ ℓ L : ℝ} (hτ : 0 < τ) (hℓ : ℓ ≠ 0) (hL : L ≠ 0)
    {s t : ℝ} (hs : 0 < s) (ht : 0 < t) (x z : ℝ) :
    ∫ y in (0 : ℝ)..L, sealedGreen τ ℓ L y s x * sealedGreen τ ℓ L z t y =
      sealedGreen τ ℓ L z (t + s) x := by
  have hb : Summable fun n => |greenCoeff L z n * exp (-decayRate τ ℓ L n * t)| :=
    summable_abs_mul_exp hτ hℓ hL (abs_greenCoeff_le L z) ht
  have hG : ∀ y, sealedGreen τ ℓ L z t y =
      ∑' n, greenCoeff L z n * exp (-decayRate τ ℓ L n * t) * cosMode L n y := fun y => by
    unfold sealedGreen cableSeries
    exact tsum_congr fun n => by ring
  simp_rw [hG]
  rw [integral_sealedGreen_mul_cosSeries hτ hℓ hL hb hs x]
  unfold sealedGreen cableSeries
  refine tsum_congr fun n => ?_
  rw [show -decayRate τ ℓ L n * (t + s) = -decayRate τ ℓ L n * t + -decayRate τ ℓ L n * s by ring,
    exp_add]
  ring

/-! ### Green's function of the infinite cable -/

/-- **Green's function of the infinite cable** `ℝ`: the potential at position `x` and time `t > 0`
after a unit charge is injected at `x₀` at time `0`,
`G(t, x; x₀) = e^{-t/τ} / √(4 π D t) · exp (-(x - x₀)² / (4 D t))` with `D = ℓ² / τ`: a heat kernel
damped by the membrane leak (for `τ > 0` and `ℓ ≠ 0`). With `u / 0 = 0` and `√u = 0` for `u < 0`,
`G = 0` whenever `4 π D t ≤ 0`. -/
noncomputable def infiniteGreen (τ ℓ x₀ t x : ℝ) : ℝ :=
  exp (-t / τ) / √(4 * π * (ℓ ^ 2 / τ) * t) * exp (-(x - x₀) ^ 2 / (4 * (ℓ ^ 2 / τ) * t))

private theorem hasDerivAt_gauss (c x₀ x : ℝ) :
    HasDerivAt (fun y => exp (-(y - x₀) ^ 2 / c))
      (-(2 * (x - x₀)) / c * exp (-(x - x₀) ^ 2 / c)) x := by
  have h : HasDerivAt (fun y => -(y - x₀) ^ 2 / c) (-(2 * (x - x₀)) / c) x := by
    simpa using (((hasDerivAt_id' x).sub_const x₀).pow 2).neg.div_const c
  convert h.exp using 1
  ring

private theorem hasDerivAt_deriv_gauss (c x₀ x : ℝ) :
    HasDerivAt (fun y => -(2 * (y - x₀)) / c * exp (-(y - x₀) ^ 2 / c))
      (((2 * (x - x₀) / c) ^ 2 - 2 / c) * exp (-(x - x₀) ^ 2 / c)) x := by
  have h1 : HasDerivAt (fun y => -(2 * (y - x₀)) / c) (-2 / c) x := by
    simpa using (((hasDerivAt_id' x).sub_const x₀).const_mul 2).neg.div_const c
  convert h1.mul (hasDerivAt_gauss c x₀ x) using 1
  ring

private theorem hasDerivAt_infiniteGreen_space (τ ℓ x₀ t x : ℝ) :
    HasDerivAt (infiniteGreen τ ℓ x₀ t) (exp (-t / τ) / √(4 * π * (ℓ ^ 2 / τ) * t) *
      (-(2 * (x - x₀)) / (4 * (ℓ ^ 2 / τ) * t) *
        exp (-(x - x₀) ^ 2 / (4 * (ℓ ^ 2 / τ) * t)))) x :=
  (hasDerivAt_gauss _ x₀ x).const_mul _

private theorem deriv_infiniteGreen_space (τ ℓ x₀ t : ℝ) :
    deriv (infiniteGreen τ ℓ x₀ t) = fun x => exp (-t / τ) / √(4 * π * (ℓ ^ 2 / τ) * t) *
      (-(2 * (x - x₀)) / (4 * (ℓ ^ 2 / τ) * t) *
        exp (-(x - x₀) ^ 2 / (4 * (ℓ ^ 2 / τ) * t))) :=
  funext fun x => (hasDerivAt_infiniteGreen_space τ ℓ x₀ t x).deriv

private theorem hasDerivAt_deriv_infiniteGreen_space (τ ℓ x₀ t x : ℝ) :
    HasDerivAt (deriv (infiniteGreen τ ℓ x₀ t)) (exp (-t / τ) / √(4 * π * (ℓ ^ 2 / τ) * t) *
      (((2 * (x - x₀) / (4 * (ℓ ^ 2 / τ) * t)) ^ 2 - 2 / (4 * (ℓ ^ 2 / τ) * t)) *
        exp (-(x - x₀) ^ 2 / (4 * (ℓ ^ 2 / τ) * t)))) x := by
  rw [deriv_infiniteGreen_space]
  exact (hasDerivAt_deriv_gauss _ x₀ x).const_mul _

private theorem hasDerivAt_one_div_sqrt {c t : ℝ} (hc : 0 < c) (ht : 0 < t) :
    HasDerivAt (fun s => 1 / √(c * s)) (-(1 / √(c * t)) / (2 * t)) t := by
  have hpos : 0 < c * t := mul_pos hc ht
  have hs : √(c * t) ≠ 0 := (sqrt_pos.mpr hpos).ne'
  have h := (((hasDerivAt_id' t).const_mul c).sqrt hpos.ne').inv hs
  simp only [one_div]
  convert h using 1
  rw [sq_sqrt hpos.le]
  field_simp

private theorem hasDerivAt_gauss_time {D : ℝ} (hD : D ≠ 0) (u : ℝ) {t : ℝ} (ht : t ≠ 0) :
    HasDerivAt (fun s => exp (-u ^ 2 / (4 * D * s)))
      (u ^ 2 / (4 * D * t ^ 2) * exp (-u ^ 2 / (4 * D * t))) t := by
  have h : HasDerivAt (fun s => -u ^ 2 / (4 * D * s))
      ((0 * (4 * D * t) - -u ^ 2 * (4 * D * 1)) / (4 * D * t) ^ 2) t :=
    (hasDerivAt_const t (-u ^ 2)).fun_div ((hasDerivAt_id' t).const_mul (4 * D))
      (mul_ne_zero (mul_ne_zero four_ne_zero hD) ht)
  convert h.exp using 1
  field_simp
  ring

private theorem hasDerivAt_infiniteGreen_time {τ ℓ : ℝ} (hτ : 0 < τ) (hℓ : ℓ ≠ 0) (x₀ x : ℝ)
    {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s => infiniteGreen τ ℓ x₀ s x) (infiniteGreen τ ℓ x₀ t x *
      (-1 / τ - 1 / (2 * t) + (x - x₀) ^ 2 / (4 * (ℓ ^ 2 / τ) * t ^ 2))) t := by
  have hD : 0 < ℓ ^ 2 / τ := by positivity
  have hE : HasDerivAt (fun s => exp (-s / τ)) (-1 / τ * exp (-t / τ)) t := by
    have h0 : HasDerivAt (fun s => -s / τ) (-1 / τ) t := (hasDerivAt_id' t).fun_neg.div_const τ
    convert h0.exp using 1; ring
  have hP := hasDerivAt_one_div_sqrt (c := 4 * π * (ℓ ^ 2 / τ)) (by positivity) ht
  have hF := hasDerivAt_gauss_time hD.ne' (x - x₀) ht.ne'
  have hfun : (fun s => infiniteGreen τ ℓ x₀ s x) = fun s => exp (-s / τ) *
      (1 / √(4 * π * (ℓ ^ 2 / τ) * s)) * exp (-(x - x₀) ^ 2 / (4 * (ℓ ^ 2 / τ) * s)) := by
    funext s; unfold infiniteGreen; ring
  rw [hfun]
  convert (hE.fun_mul hP).fun_mul hF using 1
  unfold infiniteGreen
  ring

/-- **The cable equation on all of `ℝ`.** For `τ > 0` and `ℓ ≠ 0`, at every positive time `t`
and every position `x : ℝ`
(including `x < 0`), the infinite-cable Green's function is differentiable in time, twice
differentiable in space, and satisfies `τ ∂ₜG = ℓ² ∂ₓ²G - G`. -/
theorem infiniteGreen_cable {τ ℓ : ℝ} (hτ : 0 < τ) (hℓ : ℓ ≠ 0) (x₀ : ℝ) {t : ℝ} (ht : 0 < t)
    (x : ℝ) :
    DifferentiableAt ℝ (fun s => infiniteGreen τ ℓ x₀ s x) t ∧
      DifferentiableAt ℝ (infiniteGreen τ ℓ x₀ t) x ∧
      DifferentiableAt ℝ (deriv (infiniteGreen τ ℓ x₀ t)) x ∧
      τ * deriv (fun s => infiniteGreen τ ℓ x₀ s x) t =
        ℓ ^ 2 * deriv (deriv (infiniteGreen τ ℓ x₀ t)) x - infiniteGreen τ ℓ x₀ t x := by
  refine ⟨(hasDerivAt_infiniteGreen_time hτ hℓ x₀ x ht).differentiableAt,
    (hasDerivAt_infiniteGreen_space τ ℓ x₀ t x).differentiableAt,
    (hasDerivAt_deriv_infiniteGreen_space τ ℓ x₀ t x).differentiableAt, ?_⟩
  have hτ' := hτ.ne'
  have ht' := ht.ne'
  rw [(hasDerivAt_infiniteGreen_time hτ hℓ x₀ x ht).deriv,
    (hasDerivAt_deriv_infiniteGreen_space τ ℓ x₀ t x).deriv]
  unfold infiniteGreen
  field_simp
  ring

/-- For `τ > 0` and `ℓ ≠ 0`, the restriction of `infiniteGreen_cable` to a finite segment
`[0, L]`, in the form of
`IsCableSolution` (any `L`; the segment is empty for `L < 0`). For positions outside `[0, L]`,
including `x < 0`, use `infiniteGreen_cable`. -/
theorem isCableSolution_infiniteGreen {τ ℓ : ℝ} (hτ : 0 < τ) (hℓ : ℓ ≠ 0) (L x₀ : ℝ) :
    IsCableSolution τ ℓ L (Ioi 0) (infiniteGreen τ ℓ x₀) where
  differentiableAt_time _ ht x _ := (infiniteGreen_cable hτ hℓ x₀ ht x).1
  differentiableAt_space _ ht x _ := (infiniteGreen_cable hτ hℓ x₀ ht x).2.1
  differentiableAt_deriv_space _ ht x _ := (infiniteGreen_cable hτ hℓ x₀ ht x).2.2.1
  cable _ ht x _ := (infiniteGreen_cable hτ hℓ x₀ ht x).2.2.2

/-- For `τ > 0` and `ℓ ≠ 0`, the infinite-cable Green's function is positive at positive
times. -/
theorem infiniteGreen_pos {τ ℓ : ℝ} (hτ : 0 < τ) (hℓ : ℓ ≠ 0) (x₀ : ℝ) {t : ℝ} (ht : 0 < t)
    (x : ℝ) : 0 < infiniteGreen τ ℓ x₀ t x := by
  unfold infiniteGreen
  positivity

/-- **Total charge.** For `τ > 0` and `ℓ ≠ 0`, `∫_ℝ G(t, x; x₀) dx = e^{-t/τ}` for `t > 0`: the
injected unit charge
leaks through the membrane at exactly the rate `1 / τ`. -/
theorem integral_infiniteGreen {τ ℓ : ℝ} (hτ : 0 < τ) (hℓ : ℓ ≠ 0) (x₀ : ℝ) {t : ℝ}
    (ht : 0 < t) : ∫ x, infiniteGreen τ ℓ x₀ t x = exp (-t / τ) := by
  have hc : 0 < 4 * (ℓ ^ 2 / τ) * t := by positivity
  have hs : √(4 * π * (ℓ ^ 2 / τ) * t) ≠ 0 := (sqrt_pos.mpr (by positivity)).ne'
  unfold infiniteGreen
  rw [MeasureTheory.integral_const_mul]
  have hshift := integral_sub_right_eq_self (μ := volume)
    (fun x => exp (-(1 / (4 * (ℓ ^ 2 / τ) * t)) * x ^ 2)) x₀
  have hcongr : (fun x => exp (-(x - x₀) ^ 2 / (4 * (ℓ ^ 2 / τ) * t))) =
      fun x => exp (-(1 / (4 * (ℓ ^ 2 / τ) * t)) * (x - x₀) ^ 2) := by
    funext x; congr 1; ring
  rw [hcongr, hshift, integral_gaussian,
    show π / (1 / (4 * (ℓ ^ 2 / τ) * t)) = 4 * π * (ℓ ^ 2 / τ) * t by field_simp,
    div_mul_cancel₀ _ hs]

/-- **Symmetry.** The infinite-cable response at `x` to an input at `x₀` equals the response at
`x₀` to an input at `x`. -/
theorem infiniteGreen_comm (τ ℓ x₀ t x : ℝ) :
    infiniteGreen τ ℓ x₀ t x = infiniteGreen τ ℓ x t x₀ := by
  unfold infiniteGreen
  rw [show (x₀ - x) ^ 2 = (x - x₀) ^ 2 by ring]

/-- **Peak at the input site.** For `τ > 0`, at every positive time the infinite-cable response
is largest at the input site `x₀` (for `ℓ = 0` both sides are `0`). -/
theorem infiniteGreen_le {τ ℓ : ℝ} (hτ : 0 < τ) (x₀ : ℝ) {t : ℝ} (ht : 0 < t) (x : ℝ) :
    infiniteGreen τ ℓ x₀ t x ≤ infiniteGreen τ ℓ x₀ t x₀ := by
  unfold infiniteGreen
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  have : 0 ≤ (x - x₀) ^ 2 / (4 * (ℓ ^ 2 / τ) * t) := by positivity
  rw [exp_le_exp, sub_self, zero_pow two_ne_zero, neg_zero, zero_div, neg_div]
  exact neg_nonpos.mpr this

/-- **Localization.** For `τ > 0` and `ℓ ≠ 0`, away from the input site the infinite-cable
response vanishes as `t → 0⁺`, pointwise in `x ≠ x₀`. Together with `integral_infiniteGreen`
(total charge `e^{-t/τ} → 1`) this is the pointwise form of the localization of the input at
`x₀`; it does not by itself give convergence to a unit point charge at `x₀` against test
functions. -/
theorem tendsto_infiniteGreen_of_ne {τ ℓ : ℝ} (hτ : 0 < τ) (hℓ : ℓ ≠ 0) {x₀ x : ℝ}
    (hx : x ≠ x₀) : Tendsto (fun t => infiniteGreen τ ℓ x₀ t x) (𝓝[>] 0) (𝓝 0) := by
  have hb : 0 < (x - x₀) ^ 2 / (4 * (ℓ ^ 2 / τ)) := by
    have := sub_ne_zero.mpr hx; positivity
  have h1 : Tendsto (fun t : ℝ => (t⁻¹) ^ (1 / 2 : ℝ) *
      exp (-((x - x₀) ^ 2 / (4 * (ℓ ^ 2 / τ))) * t⁻¹)) (𝓝[>] 0) (𝓝 0) :=
    (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (1 / 2) _ hb).comp tendsto_inv_nhdsGT_zero
  have h2 : Tendsto (fun t : ℝ => exp (-t / τ) / √(4 * π * (ℓ ^ 2 / τ))) (𝓝[>] 0)
      (𝓝 (exp (-0 / τ) / √(4 * π * (ℓ ^ 2 / τ)))) :=
    ((by fun_prop : Continuous fun t : ℝ => exp (-t / τ) / √(4 * π * (ℓ ^ 2 / τ))).tendsto
      0).mono_left nhdsWithin_le_nhds
  have h3 := h2.mul h1
  rw [mul_zero] at h3
  refine Tendsto.congr' ?_ h3
  filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
  unfold infiniteGreen
  rw [← sqrt_eq_rpow, sqrt_inv, sqrt_mul (by positivity : (0 : ℝ) ≤ 4 * π * (ℓ ^ 2 / τ)) t,
    show -(x - x₀) ^ 2 / (4 * (ℓ ^ 2 / τ) * t) = -((x - x₀) ^ 2 / (4 * (ℓ ^ 2 / τ))) * t⁻¹ by
      ring]
  ring

end MathlibExt.Biology.Biophysics.CableTimeDependent

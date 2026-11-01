/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Probability.BrownianMotion.Basic
public import Mathlib.Probability.Kernel.CondDistrib
public import Mathlib.Probability.Process.Filtration
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Basic
import Mathlib.Probability.ConditionalExpectation
import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Independence
import MathlibExt.Probability.KolmogorovExtension
import MathlibExt.Probability.Distributions.GaussianConditioning

/-!
# The Ornstein–Uhlenbeck process

The **Ornstein–Uhlenbeck (OU) process** with mean-reversion rate `θ > 0` and noise amplitude
`σ` is the Gaussian process solving the Langevin equation `dX = -θ X dt + σ dW`
(Uhlenbeck–Ornstein 1930). This file treats it as a Gaussian process indexed by time
`t : ℝ≥0`, using Mathlib's `IsGaussianProcess` and pre-Brownian motion `IsPreBrownianReal`, and
proves the pathwise form of the Langevin equation for a continuous driving path.

Pinned Mathlib has Brownian motion (finite-dimensional laws, `IsPreBrownianReal`) but no
stochastic integral and no SDE theory, so the Itô-integral form of the solution, the Itô isometry
and Itô's formula are recorded as wanted statements in
`WantedExt.Probability.ItoCalculusWanted`.

## Main definitions

* `ouCovariance θ σ s t = (σ² / (2θ)) (e^{-θ|t-s|} - e^{-θ(t+s)})`, the covariance of the OU
  process started at `0`; `ouStationaryCovariance θ σ s t = (σ² / (2θ)) e^{-θ|t-s|}`.
* `IsOrnsteinUhlenbeckFromZero θ σ X P`: `X` is a centered Gaussian process with covariance
  `ouCovariance θ σ` (the OU process started at `X 0 = 0`), and `0 < θ`.
* `IsStationaryOrnsteinUhlenbeck θ σ X P`: the same with covariance `ouStationaryCovariance θ σ`.
* `ouOfBrownian θ σ B t = σ e^{-θt} B((e^{2θt} - 1)/(2θ))` and
  `ouStationaryOfBrownian θ σ B t = σ e^{-θt} B(e^{2θt}/(2θ))`: Doob's time changes.
* `ouPathSolution θ σ x₀ w`: the explicit solution of the pathwise Langevin equation.

## Main results

* `IsPreBrownianReal.isOrnsteinUhlenbeckFromZero_ouOfBrownian`,
  `IsPreBrownianReal.isStationaryOrnsteinUhlenbeck_ouStationaryOfBrownian`: **construction**
  of both processes from a pre-Brownian motion by Doob's time change; with
  `exists_isPreBrownianReal_eval` (Kolmogorov extension of the Brownian finite-dimensional laws)
  this gives `exists_isOrnsteinUhlenbeckFromZero` and `exists_isStationaryOrnsteinUhlenbeck`.
* `IsOrnsteinUhlenbeckFromZero.hasLaw_eval`: `X t ~ N(0, (σ² / (2θ)) (1 - e^{-2θt}))`;
  `IsOrnsteinUhlenbeckFromZero.eval_zero_ae_eq_zero`: `X 0 = 0` almost surely.
* `IsStationaryOrnsteinUhlenbeck.hasLaw_eval`: the **stationary law** `X t ~ N(0, σ² / (2θ))`;
  `IsStationaryOrnsteinUhlenbeck.map_restrict_shift`: **strict stationarity** (every
  finite-dimensional law is invariant under time shifts), via
  `IsGaussianProcess.map_restrict_eq_of_covariance_eq` (finite-dimensional laws of a Gaussian
  process are determined by its mean and covariance).
* `IsOrnsteinUhlenbeckFromZero.tendsto_covariance_add`: the covariance of the process started at
  `0`, shifted by `h`, tends to the stationary covariance as `h → ∞`.
* `IsOrnsteinUhlenbeckFromZero.condExp_natural`, `IsStationaryOrnsteinUhlenbeck.condExp_natural`:
  **mean reversion** `E[X t | F s] = e^{-θ(t-s)} X s` for the natural filtration `F`
  (so the conditional mean given the whole past depends only on `X s`).
* `IsOrnsteinUhlenbeckFromZero.condDistrib_eval`, `IsStationaryOrnsteinUhlenbeck.condDistrib_eval`:
  the **transition law** `X t | X s = x ~ N(e^{-θ(t-s)} x, (σ² / (2θ)) (1 - e^{-2θ(t-s)}))`.
* `ouPathSolution_integral_eq`, `eq_ouPathSolution_of_integral_eq`: for a continuous path `w`,
  `ouPathSolution θ σ x₀ w` is the unique continuous solution of
  `x t = x₀ - θ ∫_0^t x + σ (w t - w 0)` on `t ≥ 0`.

## Implementation notes

* Only `σ²` enters the covariances, so the results hold for every real `σ` (the convention is
  `σ ≥ 0`). The rate condition `0 < θ` is a field of both predicates: for `θ = 0`, Lean's
  `x / 0 = 0` would make the covariance formulas vanish identically.
* Variances are passed to `gaussianReal` through `Real.toNNReal`; the arguments are nonnegative
  on the domain `θ > 0`, `0 ≤ s ≤ t`.
* The predicates fix the finite-dimensional laws only (as `IsPreBrownianReal` does); path
  continuity is not part of them.
* Not covered: the Itô-integral solution formula `X t = e^{-θt} X 0 + σ ∫_0^t e^{-θ(t-s)} dW_s`,
  and the fact that `ouPathSolution` driven by a Brownian path is an OU process (it needs the
  Gaussianity of pathwise integrals of a Gaussian process); both are stated in
  `WantedExt.Probability.ItoCalculusWanted`.

## References

* G. E. Uhlenbeck and L. S. Ornstein, *On the theory of the Brownian motion*, Phys. Rev. 36
  (1930), 823–841.
* J. L. Doob, *The Brownian movement and stochastic equations*, Ann. of Math. 43 (1942),
  351–369.
* I. Karatzas and S. E. Shreve, *Brownian Motion and Stochastic Calculus*, 2nd ed., Springer,
  1991, Chapters 2, 3 and 5 (Section 5.6).
* B. Øksendal, *Stochastic Differential Equations*, 6th ed., Springer, 2003, Chapter 5.
-/

@[expose] public section

open MeasureTheory Filter Topology Real
open scoped NNReal ProbabilityTheory

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}

/-! ### Covariance functions -/

/-- The covariance function of the Ornstein–Uhlenbeck process started at `0`:
`(σ² / (2θ)) (e^{-θ|t-s|} - e^{-θ(t+s)})` (Karatzas–Shreve 1991, Section 5.6). It is meant
for `θ > 0` and times `s, t ≥ 0`; at `θ = 0` the division by zero makes it `0`. -/
noncomputable def ouCovariance (θ σ s t : ℝ) : ℝ :=
  σ ^ 2 / (2 * θ) * (exp (-θ * |t - s|) - exp (-θ * (t + s)))

/-- The covariance function of the stationary Ornstein–Uhlenbeck process:
`(σ² / (2θ)) e^{-θ|t-s|}` (Uhlenbeck–Ornstein 1930). It is meant for `θ > 0`. -/
noncomputable def ouStationaryCovariance (θ σ s t : ℝ) : ℝ :=
  σ ^ 2 / (2 * θ) * exp (-θ * |t - s|)

/-- The OU covariance is symmetric. -/
theorem ouCovariance_comm (θ σ s t : ℝ) : ouCovariance θ σ s t = ouCovariance θ σ t s := by
  simp only [ouCovariance, abs_sub_comm t s, add_comm t s]

/-- The variance of the OU process started at `0`: `(σ² / (2θ)) (1 - e^{-2θt})`. -/
theorem ouCovariance_self (θ σ t : ℝ) :
    ouCovariance θ σ t t = σ ^ 2 / (2 * θ) * (1 - exp (-2 * θ * t)) := by
  rw [ouCovariance, sub_self, abs_zero, mul_zero, exp_zero, show -θ * (t + t) = -2 * θ * t by ring]

/-- The stationary variance `σ² / (2θ)`. -/
theorem ouStationaryCovariance_self (θ σ t : ℝ) :
    ouStationaryCovariance θ σ t t = σ ^ 2 / (2 * θ) := by
  simp [ouStationaryCovariance]

/-- Shifting both times by `h → ∞` turns `ouCovariance` into `ouStationaryCovariance`. -/
theorem tendsto_ouCovariance_add {θ : ℝ} (hθ : 0 < θ) (σ s t : ℝ) :
    Tendsto (fun h : ℝ ↦ ouCovariance θ σ (s + h) (t + h)) atTop
      (𝓝 (ouStationaryCovariance θ σ s t)) := by
  have h1 : Tendsto (fun h : ℝ ↦ exp (-θ * (t + s)) * exp (-(2 * θ) * h)) atTop (𝓝 0) := by
    have : Tendsto (fun h : ℝ ↦ -(2 * θ) * h) atTop atBot :=
      tendsto_id.const_mul_atTop_of_neg (by linarith)
    simpa using (Real.tendsto_exp_atBot.comp this).const_mul (exp (-θ * (t + s)))
  have h2 := (h1.const_sub (exp (-θ * |t - s|))).const_mul (σ ^ 2 / (2 * θ))
  rw [sub_zero] at h2
  refine h2.congr fun h ↦ ?_
  rw [ouCovariance, show t + h - (s + h) = t - s by ring, ← exp_add]
  congr 3
  ring

/-! ### The processes -/

/-- `X` is an **Ornstein–Uhlenbeck process started at `0`** with rate `θ > 0` and noise
amplitude `σ` under `P`: a centered Gaussian process with covariance `ouCovariance θ σ`.
Only the finite-dimensional laws are fixed (no path regularity). -/
structure IsOrnsteinUhlenbeckFromZero (θ σ : ℝ) (X : ℝ≥0 → Ω → ℝ) (P : Measure Ω := by volume_tac) :
    Prop where
  rate_pos : 0 < θ
  isGaussianProcess : IsGaussianProcess X P
  integral_eval : ∀ t, P[X t] = 0
  covariance_eval : ∀ s t, cov[X s, X t; P] = ouCovariance θ σ s t

/-- `X` is a **stationary Ornstein–Uhlenbeck process** with rate `θ > 0` and noise
amplitude `σ` under `P`: a centered Gaussian process with covariance
`ouStationaryCovariance θ σ`. Only the finite-dimensional laws are fixed. -/
structure IsStationaryOrnsteinUhlenbeck (θ σ : ℝ) (X : ℝ≥0 → Ω → ℝ)
    (P : Measure Ω := by volume_tac) : Prop where
  rate_pos : 0 < θ
  isGaussianProcess : IsGaussianProcess X P
  integral_eval : ∀ t, P[X t] = 0
  covariance_eval : ∀ s t, cov[X s, X t; P] = ouStationaryCovariance θ σ s t

/-- Doob's clock `τ t = (e^{2θt} - 1)/(2θ)` for the process started at `0`. The value is
nonnegative for every real `θ`, so `Real.toNNReal` only changes its type. -/
noncomputable def ouClock (θ : ℝ) (t : ℝ≥0) : ℝ≥0 :=
  Real.toNNReal ((exp (2 * θ * t) - 1) / (2 * θ))

/-- Doob's clock `t ↦ e^{2θt}/(2θ)` for the stationary process (positive for `θ > 0`). -/
noncomputable def ouStationaryClock (θ : ℝ) (t : ℝ≥0) : ℝ≥0 :=
  Real.toNNReal (exp (2 * θ * t) / (2 * θ))

/-- Doob's time change `t ↦ σ e^{-θt} B(τ t)` of a process `B`, with `τ = ouClock θ`. -/
noncomputable def ouOfBrownian (θ σ : ℝ) (B : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  σ * exp (-θ * t) * B (ouClock θ t) ω

/-- Doob's stationary time change `t ↦ σ e^{-θt} B(e^{2θt}/(2θ))` of a process `B`. -/
noncomputable def ouStationaryOfBrownian (θ σ : ℝ) (B : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  σ * exp (-θ * t) * B (ouStationaryClock θ t) ω

private lemma ouClock_coe {θ : ℝ} (hθ : 0 < θ) (t : ℝ≥0) :
    (ouClock θ t : ℝ) = (exp (2 * θ * t) - 1) / (2 * θ) := by
  apply Real.coe_toNNReal
  apply div_nonneg _ (by positivity)
  exact sub_nonneg.mpr (Real.one_le_exp (by positivity))

private lemma ouStationaryClock_coe {θ : ℝ} (hθ : 0 < θ) (t : ℝ≥0) :
    (ouStationaryClock θ t : ℝ) = exp (2 * θ * t) / (2 * θ) := by
  apply Real.coe_toNNReal
  positivity

private lemma ouClock_monotone {θ : ℝ} (hθ : 0 < θ) : Monotone (ouClock θ) := by
  intro s t hst
  apply Real.toNNReal_mono
  apply div_le_div_of_nonneg_right _ (by positivity)
  apply sub_le_sub_right
  apply Real.exp_le_exp.mpr
  exact mul_le_mul_of_nonneg_left (NNReal.coe_le_coe.mpr hst) (by positivity)

private lemma ouStationaryClock_monotone {θ : ℝ} (hθ : 0 < θ) :
    Monotone (ouStationaryClock θ) := by
  intro s t hst
  apply Real.toNNReal_mono
  apply div_le_div_of_nonneg_right _ (by positivity)
  apply Real.exp_le_exp.mpr
  exact mul_le_mul_of_nonneg_left (NNReal.coe_le_coe.mpr hst) (by positivity)

private lemma ou_exp_min (θ s t : ℝ) :
    exp (-θ * s) * exp (-θ * t) * exp (2 * θ * min s t) =
      exp (-θ * |t - s|) := by
  rw [← Real.exp_add, ← Real.exp_add]
  congr 1
  rcases le_total s t with hst | hts
  · rw [min_eq_left hst, abs_of_nonneg (sub_nonneg.mpr hst)]
    ring
  · rw [min_eq_right hts, abs_of_nonpos (sub_nonpos.mpr hts)]
    ring

private lemma ou_exp_sum (θ s t : ℝ) :
    exp (-θ * s) * exp (-θ * t) = exp (-θ * (t + s)) := by
  rw [← Real.exp_add]
  congr 1
  ring

/-- **Construction (Doob 1942).** The time change `σ e^{-θt} B((e^{2θt} - 1)/(2θ))` of a
pre-Brownian motion is an Ornstein–Uhlenbeck process started at `0`. -/
theorem IsPreBrownianReal.isOrnsteinUhlenbeckFromZero_ouOfBrownian {B : ℝ≥0 → Ω → ℝ}
    (hB : IsPreBrownianReal B P) {θ : ℝ} (hθ : 0 < θ) (σ : ℝ) :
    IsOrnsteinUhlenbeckFromZero θ σ (ouOfBrownian θ σ B) P := by
  refine ⟨hθ, ?_, ?_, ?_⟩
  · exact (hB.isGaussianProcess.comp_right (ouClock θ)).smul
      (fun (t : ℝ≥0) ↦ σ * exp (-θ * t))
  · intro t
    unfold ouOfBrownian
    rw [integral_const_mul, hB.integral_eval, mul_zero]
  · intro s t
    unfold ouOfBrownian
    rw [covariance_const_mul_left, covariance_const_mul_right, hB.covariance_eval,
      ← (ouClock_monotone hθ).map_min, ouClock_coe hθ, NNReal.coe_min]
    unfold ouCovariance
    calc
      _ = σ ^ 2 / (2 * θ) *
          (exp (-θ * s) * exp (-θ * t) * exp (2 * θ * min (s : ℝ) (t : ℝ)) -
            exp (-θ * s) * exp (-θ * t)) := by ring
      _ = _ := by rw [ou_exp_min, ou_exp_sum]

/-- **Construction (Doob 1942).** The time change `σ e^{-θt} B(e^{2θt}/(2θ))` of a
pre-Brownian motion is a stationary Ornstein–Uhlenbeck process. -/
theorem IsPreBrownianReal.isStationaryOrnsteinUhlenbeck_ouStationaryOfBrownian
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P) {θ : ℝ} (hθ : 0 < θ) (σ : ℝ) :
    IsStationaryOrnsteinUhlenbeck θ σ (ouStationaryOfBrownian θ σ B) P := by
  refine ⟨hθ, ?_, ?_, ?_⟩
  · exact (hB.isGaussianProcess.comp_right (ouStationaryClock θ)).smul
      (fun (t : ℝ≥0) ↦ σ * exp (-θ * t))
  · intro t
    unfold ouStationaryOfBrownian
    rw [integral_const_mul, hB.integral_eval, mul_zero]
  · intro s t
    unfold ouStationaryOfBrownian
    rw [covariance_const_mul_left, covariance_const_mul_right, hB.covariance_eval,
      ← (ouStationaryClock_monotone hθ).map_min, ouStationaryClock_coe hθ, NNReal.coe_min]
    unfold ouStationaryCovariance
    calc
      _ = σ ^ 2 / (2 * θ) *
          (exp (-θ * s) * exp (-θ * t) * exp (2 * θ * min (s : ℝ) (t : ℝ))) := by ring
      _ = _ := by rw [ou_exp_min]

/-- There is a probability measure on paths `ℝ≥0 → ℝ` under which the coordinate process is a
pre-Brownian motion (Kolmogorov extension of the Brownian finite-dimensional laws). -/
theorem exists_isPreBrownianReal_eval :
    ∃ μ : Measure (ℝ≥0 → ℝ), IsPreBrownianReal (fun t f ↦ f t) μ := by
  obtain ⟨μ, hμ⟩ := MathlibExt.Probability.KolmogorovExtensionWanted.kolmogorov_extension
    (α := fun _ : ℝ≥0 ↦ ℝ) BrownianReal.projectiveFamily
    BrownianReal.isProjectiveMeasureFamily_projectiveFamily
  exact ⟨μ, ⟨fun I ↦ ⟨(Finset.measurable_restrict I).aemeasurable, hμ I⟩⟩⟩

/-- An Ornstein–Uhlenbeck process started at `0` exists for every `θ > 0` and `σ`. -/
theorem exists_isOrnsteinUhlenbeckFromZero {θ : ℝ} (hθ : 0 < θ) (σ : ℝ) :
    ∃ μ : Measure (ℝ≥0 → ℝ), ∃ X : ℝ≥0 → (ℝ≥0 → ℝ) → ℝ, IsOrnsteinUhlenbeckFromZero θ σ X μ := by
  obtain ⟨μ, hB⟩ := exists_isPreBrownianReal_eval
  exact ⟨μ, _, hB.isOrnsteinUhlenbeckFromZero_ouOfBrownian hθ σ⟩

/-- A stationary Ornstein–Uhlenbeck process exists for every `θ > 0` and `σ`. -/
theorem exists_isStationaryOrnsteinUhlenbeck {θ : ℝ} (hθ : 0 < θ) (σ : ℝ) :
    ∃ μ : Measure (ℝ≥0 → ℝ), ∃ X : ℝ≥0 → (ℝ≥0 → ℝ) → ℝ,
      IsStationaryOrnsteinUhlenbeck θ σ X μ := by
  obtain ⟨μ, hB⟩ := exists_isPreBrownianReal_eval
  exact ⟨μ, _, hB.isStationaryOrnsteinUhlenbeck_ouStationaryOfBrownian hθ σ⟩

/-! ### Laws -/

/-- The one-time law of the OU process started at `0`:
`X t ~ N(0, (σ² / (2θ)) (1 - e^{-2θt}))`. -/
theorem IsOrnsteinUhlenbeckFromZero.hasLaw_eval {θ σ : ℝ} {X : ℝ≥0 → Ω → ℝ}
    (hX : IsOrnsteinUhlenbeckFromZero θ σ X P) (t : ℝ≥0) :
    HasLaw (X t) (gaussianReal 0 (σ ^ 2 / (2 * θ) * (1 - exp (-2 * θ * t))).toNNReal) P := by
  have hG := hX.isGaussianProcess.hasGaussianLaw_eval t
  refine ⟨hG.aemeasurable, ?_⟩
  rw [hG.map_eq_gaussianReal, hX.integral_eval, ← covariance_self hG.aemeasurable,
    hX.covariance_eval, ouCovariance_self]

/-- The OU process of `IsOrnsteinUhlenbeckFromZero` starts at `0` almost surely. -/
theorem IsOrnsteinUhlenbeckFromZero.eval_zero_ae_eq_zero {θ σ : ℝ} {X : ℝ≥0 → Ω → ℝ}
    (hX : IsOrnsteinUhlenbeckFromZero θ σ X P) : ∀ᵐ ω ∂P, X 0 ω = 0 := by
  have h := hX.hasLaw_eval 0
  have h0 : Real.toNNReal (σ ^ 2 / (2 * θ) * (1 - exp (-2 * θ * ((0 : ℝ≥0) : ℝ)))) = 0 := by
    simp
  rw [h0, gaussianReal_zero_var] at h
  exact h.ae_eq_of_dirac

/-- **Relaxation to stationarity.** For the process started at `0`,
`cov(X (s + h), X (t + h)) → (σ² / (2θ)) e^{-θ|t-s|}` as `h → ∞`. -/
theorem IsOrnsteinUhlenbeckFromZero.tendsto_covariance_add {θ σ : ℝ} {X : ℝ≥0 → Ω → ℝ}
    (hX : IsOrnsteinUhlenbeckFromZero θ σ X P) (s t : ℝ≥0) :
    Tendsto (fun h : ℝ≥0 ↦ cov[X (s + h), X (t + h); P]) atTop
      (𝓝 (ouStationaryCovariance θ σ s t)) := by
  have hc : Tendsto (fun h : ℝ≥0 ↦ (h : ℝ)) atTop atTop :=
    NNReal.tendsto_coe_atTop.2 tendsto_id
  refine ((tendsto_ouCovariance_add hX.rate_pos σ s t).comp hc).congr fun h ↦ ?_
  simp [hX.covariance_eval]

/-- **Stationary law.** Each `X t` of a stationary OU process is `N(0, σ² / (2θ))`. -/
theorem IsStationaryOrnsteinUhlenbeck.hasLaw_eval {θ σ : ℝ} {X : ℝ≥0 → Ω → ℝ}
    (hX : IsStationaryOrnsteinUhlenbeck θ σ X P) (t : ℝ≥0) :
    HasLaw (X t) (gaussianReal 0 (σ ^ 2 / (2 * θ)).toNNReal) P := by
  have hG := hX.isGaussianProcess.hasGaussianLaw_eval t
  refine ⟨hG.aemeasurable, ?_⟩
  rw [hG.map_eq_gaussianReal, hX.integral_eval, ← covariance_self hG.aemeasurable,
    hX.covariance_eval, ouStationaryCovariance_self]

/-- The finite-dimensional laws of a real Gaussian process are determined by its mean and
covariance functions: two Gaussian processes with the same means and covariances (possibly on
different probability spaces) have the same finite-dimensional laws. -/
theorem IsGaussianProcess.map_restrict_eq_of_covariance_eq {T Ω' : Type*}
    {mΩ' : MeasurableSpace Ω'} {Q : Measure Ω'} {X : T → Ω → ℝ} {Y : T → Ω' → ℝ}
    (hX : IsGaussianProcess X P) (hY : IsGaussianProcess Y Q)
    (hmean : ∀ t, P[X t] = Q[Y t]) (hcov : ∀ s t, cov[X s, X t; P] = cov[Y s, Y t; Q])
    (I : Finset T) :
    P.map (fun ω ↦ I.restrict (X · ω)) = Q.map (fun ω ↦ I.restrict (Y · ω)) := by
  have : IsProbabilityMeasure P := hX.isProbabilityMeasure
  have : IsProbabilityMeasure Q := hY.isProbabilityMeasure
  have hXm : AEMeasurable (fun ω ↦ I.restrict (X · ω)) P :=
    .of_eval fun _ ↦ hX.aemeasurable _
  have hYm : AEMeasurable (fun ω ↦ I.restrict (Y · ω)) Q :=
    .of_eval fun _ ↦ hY.aemeasurable _
  apply (MeasurableEquiv.toLp 2 (I → ℝ)).map_measurableEquiv_injective
  rw [MeasurableEquiv.coe_toLp,
    AEMeasurable.map_map_of_aemeasurable (by fun_prop) hXm,
    AEMeasurable.map_map_of_aemeasurable (by fun_prop) hYm]
  have hXg : IsGaussian (P.map (WithLp.toLp 2 ∘ fun ω ↦ I.restrict (X · ω))) :=
    ((hX.hasGaussianLaw I).toLp_pi 2).isGaussian_map
  have hYg : IsGaussian (Q.map (WithLp.toLp 2 ∘ fun ω ↦ I.restrict (Y · ω))) :=
    ((hY.hasGaussianLaw I).toLp_pi 2).isGaussian_map
  apply IsGaussian.ext
  · rw [integral_map, integral_map]
    · simp only [Function.comp_def, id_eq]
      ext i
      rw [eval_integral_piLp, eval_integral_piLp]
      · exact hmean i
      · exact fun j ↦ (hY.hasGaussianLaw_eval j).integrable
      · exact fun j ↦ (hX.hasGaussianLaw_eval j).integrable
    all_goals fun_prop
  · ext x y
    rw [covarianceBilin_apply_pi, covarianceBilin_apply_pi]
    · congrm ∑ i, ∑ j, _ * ?_
      exact hcov i j
    · exact fun i ↦ (hY.hasGaussianLaw_eval i).memLp_two
    · exact fun i ↦ (hX.hasGaussianLaw_eval i).memLp_two

/-- A time shift of a stationary OU process is a stationary OU process. -/
theorem IsStationaryOrnsteinUhlenbeck.shift {θ σ : ℝ} {X : ℝ≥0 → Ω → ℝ}
    (hX : IsStationaryOrnsteinUhlenbeck θ σ X P) (h : ℝ≥0) :
    IsStationaryOrnsteinUhlenbeck θ σ (fun t ↦ X (t + h)) P := by
  refine ⟨hX.rate_pos, hX.isGaussianProcess.comp_right (· + h), fun t ↦ hX.integral_eval _,
    fun s t ↦ ?_⟩
  rw [hX.covariance_eval, ouStationaryCovariance, ouStationaryCovariance, NNReal.coe_add,
    NNReal.coe_add, show (t : ℝ) + h - (s + h) = t - s by ring]

/-- **Strict stationarity.** Every finite-dimensional law of a stationary OU process is
invariant under time shifts. -/
theorem IsStationaryOrnsteinUhlenbeck.map_restrict_shift {θ σ : ℝ} {X : ℝ≥0 → Ω → ℝ}
    (hX : IsStationaryOrnsteinUhlenbeck θ σ X P) (h : ℝ≥0) (I : Finset ℝ≥0) :
    P.map (fun ω ↦ I.restrict (fun t ↦ X (t + h) ω)) = P.map (fun ω ↦ I.restrict (X · ω)) := by
  refine (hX.shift h).isGaussianProcess.map_restrict_eq_of_covariance_eq hX.isGaussianProcess
    (fun t ↦ ?_) (fun s t ↦ ?_) I
  · rw [(hX.shift h).integral_eval, hX.integral_eval]
  · rw [(hX.shift h).covariance_eval, hX.covariance_eval]

/-! ### Mean reversion and the transition law -/

/-- For a centered Gaussian process with `cov(X u, X t) = c cov(X u, X s)` for all `u ≤ s`,
the conditional expectation of `X t` given the natural filtration at `s` is `c X s`. -/
theorem IsGaussianProcess.condExp_natural_eq_of_covariance {X : ℝ≥0 → Ω → ℝ}
    (hX : IsGaussianProcess X P) (hm : ∀ t, StronglyMeasurable (X t))
    (hint : ∀ t, P[X t] = 0) {s t : ℝ≥0} (c : ℝ)
    (hc : ∀ u ≤ s, cov[X u, X t; P] = c * cov[X u, X s; P]) :
    P[X t | Filtration.natural X hm s] =ᵐ[P] fun ω ↦ c * X s ω := by
  classical
  have := hX.isProbabilityMeasure
  have hs := (hX.hasGaussianLaw_eval s).memLp_two
  have ht := (hX.hasGaussianLaw_eval t).memLp_two
  have hcs : MemLp (fun ω ↦ c * X s ω) 2 P := hs.const_mul c
  let R : Ω → ℝ := fun ω ↦ X t ω - c * X s ω
  let Y : Ω → Set.Iic s → ℝ := fun ω u ↦ X u ω
  have hjoint : IsGaussianProcess
      (Sum.elim (fun _ : Unit ↦ R) (fun u : Set.Iic s ↦ X u)) P := by
    apply hX.of_isGaussianProcess
    rintro (u | ⟨u, hu⟩)
    · exact ⟨{s, t},
        { toFun x := x ⟨t, by simp⟩ - c * x ⟨s, by simp⟩
          map_add' x y := by simp; ring
          map_smul' a x := by simp; ring }, by simp [R]⟩
    · exact ⟨{u},
        { toFun x := x ⟨u, by simp⟩
          map_add' x y := by simp
          map_smul' a x := by simp }, by simp⟩
  have hindpath : IndepFun (fun ω (_ : Unit) ↦ R ω) Y P := by
    apply hjoint.indepFun_of_covariance_eq_zero
    · intro u
      exact ((hm t).sub ((hm s).const_mul c)).measurable.aemeasurable
    · intro u
      exact (hm u).measurable.aemeasurable
    · intro v u
      change cov[fun ω ↦ X t ω - c * X s ω, X u; P] = 0
      rw [covariance_fun_sub_left ht hcs (hX.hasGaussianLaw_eval u).memLp_two,
        covariance_const_mul_left, covariance_comm (X := X t),
        covariance_comm (X := X s), hc u u.property]
      ring
  have hind : IndepFun R Y P :=
    hindpath.comp (measurable_pi_apply ()) measurable_id
  have hRm : StronglyMeasurable R := (hm t).sub ((hm s).const_mul c)
  have hle := (Filtration.natural X hm).le s
  have hmean : P[R] = 0 := by
    dsimp [R]
    rw [integral_sub (hX.hasGaussianLaw_eval t).integrable
      ((hX.hasGaussianLaw_eval s).integrable.const_mul c),
      integral_const_mul, hint, hint]
    ring
  have hRcond : P[R | Filtration.natural X hm s] =ᵐ[P] fun _ ↦ (0 : ℝ) := by
    have hspaces : Indep (MeasurableSpace.comap R inferInstance)
        (Filtration.natural X hm s) P := by
      rw [Filtration.natural_eq_comap]
      exact (IndepFun_iff_Indep _ _ _).1 hind
    simpa [hmean] using condExp_indep_eq hRm.measurable.comap_le hle
      (measurable_iff_comap_le.2 le_rfl).stronglyMeasurable hspaces
  have hpred : P[fun ω ↦ c * X s ω | Filtration.natural X hm s] =
      fun ω ↦ c * X s ω :=
    condExp_of_stronglyMeasurable hle
      ((Filtration.stronglyAdapted_natural hm s).const_mul c)
      ((hX.hasGaussianLaw_eval s).integrable.const_mul c)
  have hsub := condExp_sub (hX.hasGaussianLaw_eval t).integrable
    ((hX.hasGaussianLaw_eval s).integrable.const_mul c) (Filtration.natural X hm s)
  filter_upwards [hRcond, hsub] with ω hR hsub
  rw [hpred] at hsub
  change P[R | Filtration.natural X hm s] ω =
    P[X t | Filtration.natural X hm s] ω - c * X s ω at hsub
  linarith

/-- For a centered Gaussian process with `cov(X s, X t) = c Var(X s)`, the conditional law of
`X t` given `X s = x` is `N(c x, Var(X t) - c² Var(X s))` for almost every `x`. -/
theorem IsGaussianProcess.condDistrib_eval_eq_of_covariance {T : Type*}
    {X : T → Ω → ℝ} (hX : IsGaussianProcess X P) (hm : ∀ t, Measurable (X t))
    (hint : ∀ t, P[X t] = 0) {s t : T} (c : ℝ) (hc : cov[X s, X t; P] = c * Var[X s; P]) :
    haveI := hX.isProbabilityMeasure
    ∀ᵐ x ∂(P.map (X s)),
      condDistrib (X t) (X s) P x =
        gaussianReal (c * x) (Var[X t; P] - c ^ 2 * Var[X s; P]).toNNReal := by
  have : IsProbabilityMeasure P := hX.isProbabilityMeasure
  have hs := (hX.hasGaussianLaw_eval s).memLp_two
  have ht := (hX.hasGaussianLaw_eval t).memLp_two
  have hcs : MemLp (fun ω ↦ c * X s ω) 2 P := hs.const_mul c
  have hcov : cov[fun ω ↦ X t ω - c * X s ω, X s; P] = 0 := by
    rw [covariance_fun_sub_left ht hcs hs, covariance_const_mul_left,
      covariance_comm (X := X t), hc, covariance_self (hm s).aemeasurable]
    ring
  let A : ℝ →L[ℝ] ℝ := c • ContinuousLinearMap.id ℝ ℝ
  have hA : ∀ x y : ℝ,
      cov[fun ω ↦ inner ℝ x (X t ω - A (X s ω)),
        fun ω ↦ inner ℝ y (X s ω); P] = 0 := by
    intro x y
    simp [A, covariance_mul_const_left,
      covariance_mul_const_right, hcov]
  obtain ⟨hZ, _, hcd⟩ := MetaMathlibExt.condDistrib_of_hasGaussianLaw
    (hm t) (hm s) hX.hasGaussianLaw_prodMk A hA
  have hmean : P[fun ω ↦ X t ω - c * X s ω] = 0 := by
    rw [integral_sub (ht.integrable one_le_two) (hcs.integrable one_le_two),
      integral_const_mul, hint, hint]
    ring
  have hvar : Var[fun ω ↦ X t ω - c * X s ω; P] =
      Var[X t; P] - c ^ 2 * Var[X s; P] := by
    rw [variance_fun_sub ht hcs, covariance_const_mul_right,
      covariance_comm (X := X t), hc, variance_const_mul]
    ring
  filter_upwards [hcd] with x hx
  rw [hx, MetaMathlibExt.noiseKernel_apply, hZ.map_eq_gaussianReal]
  simpa [A, hmean, hvar] using
    (gaussianReal_map_const_add (μ := 0)
      (v := (Var[X t; P] - c ^ 2 * Var[X s; P]).toNNReal) (c * x))

/-- **Mean reversion.** For the OU process started at `0` and `s ≤ t`,
`E[X t | F s] = e^{-θ(t-s)} X s`, where `F` is the natural filtration of `X`. -/
theorem IsOrnsteinUhlenbeckFromZero.condExp_natural {θ σ : ℝ} {X : ℝ≥0 → Ω → ℝ}
    (hX : IsOrnsteinUhlenbeckFromZero θ σ X P) (hm : ∀ t, StronglyMeasurable (X t)) {s t : ℝ≥0}
    (hst : s ≤ t) :
    P[X t | Filtration.natural X hm s] =ᵐ[P] fun ω ↦ exp (-θ * (t - s)) * X s ω := by
  refine hX.isGaussianProcess.condExp_natural_eq_of_covariance hm hX.integral_eval _
    fun u hu ↦ ?_
  have hu' : (u : ℝ) ≤ s := hu
  have hst' : (s : ℝ) ≤ t := hst
  rw [hX.covariance_eval, hX.covariance_eval, ouCovariance, ouCovariance,
    abs_of_nonneg (by linarith : (0 : ℝ) ≤ t - u), abs_of_nonneg (by linarith : (0 : ℝ) ≤ s - u)]
  have e1 : exp (-θ * (t - u)) = exp (-θ * (t - s)) * exp (-θ * (s - u)) := by
    rw [← exp_add]; ring_nf
  have e2 : exp (-θ * (t + u)) = exp (-θ * (t - s)) * exp (-θ * (s + u)) := by
    rw [← exp_add]; ring_nf
  rw [e1, e2]; ring

/-- **Mean reversion.** For the stationary OU process and `s ≤ t`,
`E[X t | F s] = e^{-θ(t-s)} X s`, where `F` is the natural filtration of `X`. -/
theorem IsStationaryOrnsteinUhlenbeck.condExp_natural {θ σ : ℝ} {X : ℝ≥0 → Ω → ℝ}
    (hX : IsStationaryOrnsteinUhlenbeck θ σ X P) (hm : ∀ t, StronglyMeasurable (X t))
    {s t : ℝ≥0} (hst : s ≤ t) :
    P[X t | Filtration.natural X hm s] =ᵐ[P] fun ω ↦ exp (-θ * (t - s)) * X s ω := by
  refine hX.isGaussianProcess.condExp_natural_eq_of_covariance hm hX.integral_eval _
    fun u hu ↦ ?_
  have hu' : (u : ℝ) ≤ s := hu
  have hst' : (s : ℝ) ≤ t := hst
  rw [hX.covariance_eval, hX.covariance_eval, ouStationaryCovariance, ouStationaryCovariance,
    abs_of_nonneg (by linarith : (0 : ℝ) ≤ t - u), abs_of_nonneg (by linarith : (0 : ℝ) ≤ s - u)]
  have e1 : exp (-θ * (t - u)) = exp (-θ * (t - s)) * exp (-θ * (s - u)) := by
    rw [← exp_add]; ring_nf
  rw [e1]; ring

/-- **Transition law.** For the OU process started at `0` and `s ≤ t`, the conditional law of
`X t` given `X s = x` is `N(e^{-θ(t-s)} x, (σ² / (2θ)) (1 - e^{-2θ(t-s)}))` for almost every
`x`. -/
theorem IsOrnsteinUhlenbeckFromZero.condDistrib_eval {θ σ : ℝ}
    {X : ℝ≥0 → Ω → ℝ} (hX : IsOrnsteinUhlenbeckFromZero θ σ X P)
    (hm : ∀ t, Measurable (X t)) {s t : ℝ≥0} (hst : s ≤ t) :
    haveI := hX.isGaussianProcess.isProbabilityMeasure
    ∀ᵐ x ∂(P.map (X s)), condDistrib (X t) (X s) P x =
      gaussianReal (exp (-θ * (t - s)) * x)
        (σ ^ 2 / (2 * θ) * (1 - exp (-2 * θ * (t - s)))).toNNReal := by
  have : IsProbabilityMeasure P := hX.isGaussianProcess.isProbabilityMeasure
  have hst' : (s : ℝ) ≤ t := hst
  have hvar : ∀ r, Var[X r; P] = σ ^ 2 / (2 * θ) * (1 - exp (-2 * θ * r)) := fun r ↦ by
    rw [← covariance_self (hX.isGaussianProcess.aemeasurable r), hX.covariance_eval,
      ouCovariance_self]
  have hsq : exp (-θ * (t - s)) ^ 2 = exp (-2 * θ * (t - s)) := by
    rw [← exp_nat_mul]; ring_nf
  have hc : cov[X s, X t; P] = exp (-θ * (t - s)) * Var[X s; P] := by
    rw [hvar, hX.covariance_eval, ouCovariance, abs_of_nonneg (by linarith : (0 : ℝ) ≤ t - s)]
    have e1 : exp (-θ * (t + s)) = exp (-θ * (t - s)) * exp (-2 * θ * s) := by
      rw [← exp_add]; ring_nf
    rw [e1]; ring
  filter_upwards [hX.isGaussianProcess.condDistrib_eval_eq_of_covariance hm hX.integral_eval _ hc]
    with x hx
  rw [hx, hvar, hvar, hsq]
  congr 2
  have e2 : exp (-2 * θ * t) = exp (-2 * θ * (t - s)) * exp (-2 * θ * s) := by
    rw [← exp_add]; ring_nf
  rw [e2]; ring

/-- **Transition law.** For the stationary OU process and `s ≤ t`, the conditional law of
`X t` given `X s = x` is `N(e^{-θ(t-s)} x, (σ² / (2θ)) (1 - e^{-2θ(t-s)}))` for almost every
`x`. -/
theorem IsStationaryOrnsteinUhlenbeck.condDistrib_eval {θ σ : ℝ}
    {X : ℝ≥0 → Ω → ℝ} (hX : IsStationaryOrnsteinUhlenbeck θ σ X P)
    (hm : ∀ t, Measurable (X t)) {s t : ℝ≥0} (hst : s ≤ t) :
    haveI := hX.isGaussianProcess.isProbabilityMeasure
    ∀ᵐ x ∂(P.map (X s)), condDistrib (X t) (X s) P x =
      gaussianReal (exp (-θ * (t - s)) * x)
        (σ ^ 2 / (2 * θ) * (1 - exp (-2 * θ * (t - s)))).toNNReal := by
  have : IsProbabilityMeasure P := hX.isGaussianProcess.isProbabilityMeasure
  have hst' : (s : ℝ) ≤ t := hst
  have hvar : ∀ r, Var[X r; P] = σ ^ 2 / (2 * θ) := fun r ↦ by
    rw [← covariance_self (hX.isGaussianProcess.aemeasurable r), hX.covariance_eval,
      ouStationaryCovariance_self]
  have hsq : exp (-θ * (t - s)) ^ 2 = exp (-2 * θ * (t - s)) := by
    rw [← exp_nat_mul]; ring_nf
  have hc : cov[X s, X t; P] = exp (-θ * (t - s)) * Var[X s; P] := by
    rw [hvar, hX.covariance_eval, ouStationaryCovariance,
      abs_of_nonneg (by linarith : (0 : ℝ) ≤ t - s)]
    ring
  filter_upwards [hX.isGaussianProcess.condDistrib_eval_eq_of_covariance hm hX.integral_eval _ hc]
    with x hx
  rw [hx, hvar, hvar, hsq]
  congr 2
  ring

/-! ### Pathwise Langevin equation -/

/-- The explicit solution of the pathwise Langevin equation driven by a path `w`:
`e^{-θt} x₀ + σ (w t - e^{-θt} w 0 - θ ∫_0^t e^{-θ(t-u)} w u du)`. This is
`e^{-θt} x₀ + σ ∫_0^t e^{-θ(t-u)} dw(u)` after integration by parts (the Itô-integral form for a
Brownian path is a wanted statement). -/
noncomputable def ouPathSolution (θ σ x₀ : ℝ) (w : ℝ → ℝ) (t : ℝ) : ℝ :=
  exp (-θ * t) * x₀ +
    σ * (w t - exp (-θ * t) * w 0 - θ * ∫ u in (0 : ℝ)..t, exp (-θ * (t - u)) * w u)

private theorem ouPathSolution_eq (θ σ x₀ : ℝ) (w : ℝ → ℝ) (t : ℝ) :
    ouPathSolution θ σ x₀ w t =
      exp (-θ * t) * (x₀ - σ * w 0) -
        σ * θ * exp (-θ * t) * (∫ u in (0 : ℝ)..t, exp (θ * u) * w u) + σ * w t := by
  have hk : (∫ u in (0 : ℝ)..t, exp (-θ * (t - u)) * w u) =
      exp (-θ * t) * (∫ u in (0 : ℝ)..t, exp (θ * u) * w u) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro u _
    dsimp only
    rw [show -θ * (t - u) = -θ * t + θ * u by ring, Real.exp_add]
    ring
  unfold ouPathSolution
  rw [hk]
  ring

/-- The pathwise solution is continuous when the driving path is. -/
theorem continuous_ouPathSolution (θ σ x₀ : ℝ) {w : ℝ → ℝ} (hw : Continuous w) :
    Continuous (ouPathSolution θ σ x₀ w) := by
  have hf : Continuous (fun u => exp (θ * u) * w u) := by fun_prop
  have hJ : Continuous (fun t => ∫ u in (0 : ℝ)..t, exp (θ * u) * w u) := by
    apply continuous_iff_continuousAt.mpr
    intro t
    exact (hf.integral_hasStrictDerivAt 0 t).hasDerivAt.continuousAt
  change Continuous (fun t => ouPathSolution θ σ x₀ w t)
  simp_rw [ouPathSolution_eq]
  fun_prop

private theorem ouPathSolution_sub_hasDerivAt (θ σ x₀ : ℝ) {w : ℝ → ℝ}
    (hw : Continuous w) (t : ℝ) :
    HasDerivAt (fun s => ouPathSolution θ σ x₀ w s - σ * w s)
      (-θ * ouPathSolution θ σ x₀ w t) t := by
  have heq : (fun s => ouPathSolution θ σ x₀ w s - σ * w s) =
      (fun s => exp (-θ * s) * (x₀ - σ * w 0) -
        σ * θ * exp (-θ * s) * (∫ u in (0 : ℝ)..s, exp (θ * u) * w u)) := by
    funext s
    rw [ouPathSolution_eq]
    ring
  have hE : HasDerivAt (fun s : ℝ => exp (-θ * s)) (exp (-θ * t) * (-θ)) t := by
    simpa using ((hasDerivAt_id t).const_mul (-θ)).exp
  have hf : Continuous (fun u => exp (θ * u) * w u) := by fun_prop
  have hJ := (hf.integral_hasStrictDerivAt 0 t).hasDerivAt
  have he : exp (-θ * t) * exp (θ * t) = 1 := by
    rw [← Real.exp_add, show -θ * t + θ * t = 0 by ring, Real.exp_zero]
  rw [heq]
  convert (hE.mul_const (x₀ - σ * w 0)).sub ((hE.const_mul (σ * θ)).mul hJ) using 1
  rw [ouPathSolution_eq]
  linear_combination σ * θ * w t * he

/-- **Pathwise Langevin equation.** For a continuous path `w` and every real `t`,
`ouPathSolution θ σ x₀ w` satisfies `x t = x₀ - θ ∫_0^t x + σ (w t - w 0)` (any real `θ`,
`σ`, `x₀`). -/
theorem ouPathSolution_integral_eq (θ σ x₀ : ℝ) {w : ℝ → ℝ} (hw : Continuous w) (t : ℝ) :
    ouPathSolution θ σ x₀ w t =
      x₀ - θ * (∫ u in (0 : ℝ)..t, ouPathSolution θ σ x₀ w u) + σ * (w t - w 0) := by
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun s _ => ouPathSolution_sub_hasDerivAt θ σ x₀ hw s)
    (((continuous_ouPathSolution θ σ x₀ hw).const_mul (-θ)).intervalIntegrable 0 t)
  have h0 : ouPathSolution θ σ x₀ w 0 = x₀ := by simp [ouPathSolution]
  rw [intervalIntegral.integral_const_mul, h0] at hFTC
  linarith

/-- **Uniqueness.** A continuous solution of `x t = x₀ - θ ∫_0^t x + σ (w t - w 0)` on
`t ≥ 0` equals `ouPathSolution θ σ x₀ w` there. -/
theorem eq_ouPathSolution_of_integral_eq {θ σ x₀ : ℝ} {w x : ℝ → ℝ} (hw : Continuous w)
    (hx : Continuous x)
    (h : ∀ t, 0 ≤ t → x t = x₀ - θ * (∫ u in (0 : ℝ)..t, x u) + σ * (w t - w 0))
    {t : ℝ} (ht : 0 ≤ t) : x t = ouPathSolution θ σ x₀ w t := by
  let d : ℝ → ℝ := fun s => x s - ouPathSolution θ σ x₀ w s
  let D : ℝ → ℝ := fun s => ∫ u in (0 : ℝ)..s, d u
  have hd : Continuous d := hx.sub (continuous_ouPathSolution θ σ x₀ hw)
  have hdeq : ∀ s, 0 ≤ s → d s = -θ * D s := by
    intro s hs
    have hi := intervalIntegral.integral_sub (μ := volume) (hx.intervalIntegrable 0 s)
      ((continuous_ouPathSolution θ σ x₀ hw).intervalIntegrable 0 s)
    have hsol := ouPathSolution_integral_eq θ σ x₀ hw s
    dsimp [d, D]
    rw [hi]
    linarith [h s hs]
  have hD : ∀ s, HasDerivAt D (d s) s := by
    intro s
    exact (hd.integral_hasStrictDerivAt 0 s).hasDerivAt
  have hF : ∀ s, 0 ≤ s → HasDerivAt (fun u => exp (θ * u) * D u) 0 s := by
    intro s hs
    have hE : HasDerivAt (fun u : ℝ => exp (θ * u)) (exp (θ * s) * θ) s := by
      simpa using ((hasDerivAt_id s).const_mul θ).exp
    convert hE.mul (hD s) using 1
    rw [hdeq s hs]
    ring
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun u => exp (θ * u) * D u) (f' := fun _ => (0 : ℝ))
    (a := 0) (b := t)
    (fun s hs => hF s (by rw [Set.uIcc_of_le ht] at hs; exact hs.1))
    (continuous_const.intervalIntegrable 0 t)
  have hDt : D t = 0 := by
    have hprod : exp (θ * t) * D t = 0 := by
      simpa [D] using hFTC.symm
    exact (mul_eq_zero.mp hprod).resolve_left (Real.exp_ne_zero _)
  have hdt := hdeq t ht
  rw [hDt, mul_zero] at hdt
  exact sub_eq_zero.mp hdt

end ProbabilityTheory

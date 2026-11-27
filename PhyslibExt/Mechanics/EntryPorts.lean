/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import PhyslibExt.Mechanics.AircraftPerformance

import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import PhyslibExt.EarthScience.PlanetaryEnergyBalance

/-!
# Entry ports: ballistic entry profile, heat load, radiator equilibrium, peak deceleration

## i. Overview

A ballistic vehicle enters an exponential atmosphere `ρ(h) = ρ0 * exp (-h / H)` at the finite
entry state `(he, ve)` and descends along a straight path at the constant downward flight-path
angle `γ`, `sin γ > 0`. In the drag-dominated model (gravity neglected) with ballistic
coefficient `β = m / (CD * A)` the altitude and speed obey `h' = -v * sin γ` and
`v' = -ρ(h) * v ^ 2 / (2 * β)`. Eliminating time gives `dv/dh = ρ(h) * v / (2 * β * sin γ)`, and
integrating from the entry altitude gives

`v(h) = ve * exp (K * (exp (-he / H) - exp (-h / H)))`, `K = ρ0 * H / (2 * β * sin γ)`,

with `v(he) = ve`. The exponent is the column mass `∫ ρ` between `he` and `h` divided by
`2 * β * sin γ` (`ballisticVelocity_eq_exp_integral`, for `H ≠ 0`).

Model inputs: the exponential density with `ρ0, H > 0`, `β > 0`, a constant downward angle,
drag-dominated motion without gravity or lift, and finite entry data `(he, ve)`, `ve > 0`. The
equations of motion are assumed only on a nonempty finite time window `[t₀, t₁]`, `t₀ ≤ t₁`,
that starts at entry, which is how the fixed finite altitude band enters. The infinite-entry
normalization (dropping `exp (-he / H)`) does not meet the entry condition
(`omitted_entry_term_ne`). The derivative and equation-of-motion results assume `H ≠ 0`, `β > 0`
and a downward path, `sin γ > 0`: at `H = 0` Lean's convention `x / 0 = 0` makes the density
constant and `K = 0`, so the profile is constant; at `β = 0` the same convention turns the drag
term into `0`; and at `sin γ = 0` the altitude rate vanishes, so `dv/dh` is undefined. The
isothermal corollary asks the trajectory to stay in a declared altitude band, where the isothermal
layer model holds. Apart from the window condition `t₀ ≤ t₁`, that band and the radiator's `ε ≤ 1`
and `0 ≤ Tenv` in section E, which restrict statements to their physical regime, each result assumes
only the hypotheses its proof uses. The identity `ballisticVelocity_eq_exp_integral` holds for
`H ≠ 0`, all other parameters arbitrary; it is the integrated drag equation for `β > 0` and
`sin γ > 0`.

Section E records a supplied stagnation-point heating correlation of the Sutton-Graves form
`q = kSG * sqrt (ρ / rn) * v ^ 3` (convective heat flux per unit area at the stagnation point of
a blunt nose of radius `rn`, free-stream density `ρ`, speed `v`) with its citation, its
coefficient `kSG ≥ 0` and its nonempty validity box `0 ≤ ρ ≤ ρmax`, `rmin ≤ rn`, `0 ≤ v ≤ vmax`,
`rmin > 0`, and evaluates it only inside the box. For a history that stays in the box on the
finite horizon `[0, tf]`, `0 ≤ tf`, with an interval-integrable flux, the heat load per unit area
obeys `∫ t in 0..tf, q t ≤ tf * kSG * sqrt (ρmax / rmin) * vmax ^ 3`; along the profile in a band
`[hmin, he]` below the entry altitude, the band maxima `ρ(hmin)` and `ve` replace `ρmax` and
`vmax`. A gray radiator of emissivity `0 < ε ≤ 1` that absorbs the flux `qabs ≥ 0` and exchanges
radiation with large surroundings at `Tenv ≥ 0` has, for `σ > 0`, exactly one nonnegative
equilibrium temperature, `ε * σ * T ^ 4 = qabs + ε * σ * Tenv ^ 4`, by the fourth-power
equilibrium theorem of
`PhyslibExt.EarthScience.PlanetaryEnergyBalance` with coefficient `ε * σ`. The correlation, its
coefficient and its validity box are supplied calibration evidence, not a proved law. The heat
load is heat per unit area; the heat into a surface needs a declared area to multiply it. No
ablation, thermal-protection, empirical adequacy or system safety claim is made.

Section F finds the peak drag deceleration along the profile. For `H ≠ 0`, `β > 0` and
`sin γ > 0` the deceleration `a(h) = ρ(h) * v(h) ^ 2 / (2 * β)` has altitude derivative
`a'(h) = a(h) * (2 * K * exp (-h / H) - 1) / H`. For `ρ0, H, β, ve > 0` and `sin γ > 0`, which
give `K > 0`, its only stationary point is `hstar = H * log (2 * K)`: `a` increases with altitude
below `hstar`, decreases above it, and `hstar` is its strict global maximum. On the finite band
`[hmin, he]`, `hmin < he`, the peak is selected as `hstar` when `hstar` lies in the band and as
the nearer endpoint otherwise (`hmin` when `hstar < hmin`, the entry altitude `he` when
`hstar > he`); under the same hypotheses the selected altitude is the unique maximizer on the
band, and a stationary point below the band is not reached: every deceleration in the band stays
strictly below its value. Since `H > 0` and `K > 0`, `hstar` lies below the ground `h = 0`
exactly when `2 * K < 1`.

## ii. Key results

- `EntryPorts.ballisticVelocity_entry`: `v(he) = ve`.
- `EntryPorts.ballisticVelocity_of_ode`: every solution of the altitude and drag equations with
  entry state `(he, ve)` satisfies `v(t) = ballisticVelocity (h(t))` on its window.
- `EntryPorts.hasDerivAt_ballisticVelocity_comp`: conversely, the profile along an altitude
  trajectory with `h' = -v * sin γ` solves the drag equation.
- `EntryPorts.ballisticVelocity_strictMono`: the speed falls as the vehicle descends.
- `EntryPorts.ballisticVelocity_of_ode_isothermalDensity`: the same profile for a trajectory in a
  declared band of the isothermal layer, with `H` its scale height.
- `EntryPorts.StagnationHeatingCorrelation`, `Applies`, `heatFlux`, `heatLoad`: the supplied
  correlation, its validity box, and the flux and heat load evaluated only inside the box.
- `EntryPorts.StagnationHeatingCorrelation.heatLoad_le`: the finite-horizon heat-load bound.
- `EntryPorts.StagnationHeatingCorrelation.heatLoad_le_of_band`: the bound along the profile in an
  altitude band below the entry altitude.
- `EntryPorts.StagnationHeatingCorrelation.heatLoad_vacuum`: vacuum gives zero heat load.
- `EntryPorts.radiator_equilibrium_exists`, `EntryPorts.radiator_equilibrium_unique`: the radiator
  equilibrium temperature.
- `EntryPorts.ballisticDeceleration`, `EntryPorts.hasDerivAt_ballisticDeceleration`: the
  deceleration and its altitude derivative.
- `EntryPorts.deriv_ballisticDeceleration_eq_zero_iff`,
  `EntryPorts.ballisticDeceleration_lt_peak`: for `ρ0, H, β, ve > 0` and `sin γ > 0`, `hstar` is
  the only stationary point and the strict global maximum.
- `EntryPorts.bandPeakAltitude`, `EntryPorts.isMaxOn_bandPeakAltitude`,
  `EntryPorts.ballisticDeceleration_lt_bandPeakAltitude`: the selected altitude on the band and,
  under the same hypotheses and `hmin < he`, its maximality.

## iii. Table of contents

- A. Exponential density and the profile
- B. The equations of motion
- C. Descent and the entry condition
- D. The isothermal layer
- E. Stagnation-point heat load and radiator equilibrium
- F. Peak deceleration on the entry band

## iv. References

- H. J. Allen and A. J. Eggers, *A study of the motion and aerodynamic heating of ballistic
  missiles entering the earth's atmosphere at high supersonic speeds*, NACA Report 1381, 1958
  (straight-line ballistic entry, `v = v_E exp (-ρ0 H exp (-h / H) / (2 β sin γ))` normalized at
  infinite altitude; peak deceleration at `h = H log (ρ0 H / (β sin γ))`).
- F. J. Regan and S. M. Anandakrishnan, *Dynamics of Atmospheric Re-Entry*, AIAA Education
  Series, 1993 (ballistic entry from a finite entry altitude).
- K. Sutton and R. A. Graves, *A general stagnation-point convective-heating equation for
  arbitrary gas mixtures*, NASA TR R-376, 1971 (`q = k * sqrt (ρ / rn) * V ^ 3`;
  `k = 1.7415e-4 kg ^ (1 / 2) / m` for air with fluxes in `W / m ^ 2`).
- F. P. Incropera, D. P. DeWitt, T. L. Bergman and A. S. Lavine, *Fundamentals of Heat and Mass
  Transfer*, Wiley, chapters 1 and 12: net radiation of a small gray surface to large isothermal
  surroundings, `q = ε * σ * (Ts ^ 4 - Tsur ^ 4)`.
-/

@[expose] public section

namespace EntryPorts

open AircraftPerformance

/-! ## A. Exponential density and the profile -/

/-- Exponential density `ρ(h) = ρ0 * exp (-h / H)` with reference density `ρ0` at `h = 0` and
scale height `H`, height `h` measured upward. In the physical reading `ρ0 > 0` and `H > 0`. With
the convention `x / 0 = 0`, at `H = 0` the density is the constant `ρ0`. -/
noncomputable def exponentialDensity (ρ0 H h : ℝ) : ℝ :=
  ρ0 * Real.exp (-h / H)

/-- Ballistic entry constant `K = ρ0 * H / (2 * β * sin γ)` for ballistic coefficient `β` and
downward flight-path angle `γ`; it is dimensionless. In the physical reading `ρ0, H, β > 0` and
`sin γ > 0`. With the convention `x / 0 = 0`, `K = 0` when `β * sin γ = 0`. -/
noncomputable def ballisticK (ρ0 H β γ : ℝ) : ℝ :=
  ρ0 * H / (2 * β * Real.sin γ)

/-- Finite-entry ballistic velocity profile `v(h) = ve * exp (K * (exp (-he / H) - exp (-h / H)))`
for entry altitude `he` and entry speed `ve`. In the physical reading `ρ0, H, β, ve > 0` and
`sin γ > 0`. With the convention `x / 0 = 0`, it is the constant `ve` when `H = 0` or
`β * sin γ = 0`. -/
noncomputable def ballisticVelocity (ρ0 H β γ he ve h : ℝ) : ℝ :=
  ve * Real.exp (ballisticK ρ0 H β γ * (Real.exp (-he / H) - Real.exp (-h / H)))

/-- The ballistic entry constant is positive for `ρ0, H, β > 0` and a downward angle. -/
lemma ballisticK_pos {ρ0 H β γ : ℝ} (hρ0 : 0 < ρ0) (hH : 0 < H) (hβ : 0 < β)
    (hγ : 0 < Real.sin γ) : 0 < ballisticK ρ0 H β γ := by
  unfold ballisticK
  exact div_pos (mul_pos hρ0 hH) (mul_pos (mul_pos two_pos hβ) hγ)

/-- The profile meets the finite entry condition `v(he) = ve`. -/
lemma ballisticVelocity_entry (ρ0 H β γ he ve : ℝ) :
    ballisticVelocity ρ0 H β γ he ve he = ve := by
  unfold ballisticVelocity
  rw [sub_self, mul_zero, Real.exp_zero, mul_one]

/-- Column mass between two heights, for `H ≠ 0`: `∫ ρ = ρ0 * H * (exp (-he / H) - exp (-h / H))`
over `[he, h]`, by the fundamental theorem of calculus. For `ρ0 ≥ 0` it is the column mass per unit
area between `he` and `h` when `he ≤ h`, and minus the column mass between `h` and `he` when
`h < he`. -/
lemma integral_exponentialDensity {H : ℝ} (hH : H ≠ 0) (ρ0 he h : ℝ) :
    ∫ s in he..h, exponentialDensity ρ0 H s =
      ρ0 * H * (Real.exp (-he / H) - Real.exp (-h / H)) := by
  have hder : ∀ s : ℝ, HasDerivAt (fun s => -(ρ0 * H) * Real.exp (-s / H))
      (exponentialDensity ρ0 H s) s := by
    intro s
    have h1 : HasDerivAt (fun s : ℝ => -s / H) (-1 / H) s :=
      (hasDerivAt_id' s).neg.div_const H
    have heq : exponentialDensity ρ0 H s = -(ρ0 * H) * (Real.exp (-s / H) * (-1 / H)) := by
      unfold exponentialDensity
      field_simp
    rw [heq]
    exact h1.exp.const_mul (-(ρ0 * H))
  have hcont : Continuous (fun s : ℝ => exponentialDensity ρ0 H s) := by
    unfold exponentialDensity
    exact continuous_const.mul (Real.continuous_exp.comp ((continuous_id.neg).div_const H))
  have hFTC : (∫ s in he..h, exponentialDensity ρ0 H s) =
      (-(ρ0 * H) * Real.exp (-h / H)) - (-(ρ0 * H) * Real.exp (-he / H)) :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hder x)
      (hcont.intervalIntegrable he h)
  rw [hFTC]
  ring

/-- Integrated form of `dv/dh = ρ(h) * v / (2 * β * sin γ)`: the exponent of the profile is the
integral of the density from `he` to `h` (for `ρ0 ≥ 0` the oriented column mass) divided by
`2 * β * sin γ`. The identity of the two formulas
holds for `H ≠ 0`, all other parameters arbitrary (with the convention `x / 0 = 0`, both sides are
`ve` when `β * sin γ = 0`); it is the integrated drag equation only for `β > 0` and `sin γ > 0`,
where `2 * β * sin γ ≠ 0` (`hasDerivAt_ballisticVelocity`). -/
lemma ballisticVelocity_eq_exp_integral {H : ℝ} (hH : H ≠ 0) (ρ0 β γ he ve h : ℝ) :
    ballisticVelocity ρ0 H β γ he ve h =
      ve * Real.exp ((∫ s in he..h, exponentialDensity ρ0 H s) / (2 * β * Real.sin γ)) := by
  rw [integral_exponentialDensity hH]
  unfold ballisticVelocity ballisticK
  congr 1
  congr 1
  ring

/-- For `H ≠ 0`, `β > 0` and a downward path, `sin γ > 0`, the profile solves the altitude form
of the equations of motion, `dv/dh = ρ(h) * v / (2 * β * sin γ)`. -/
lemma hasDerivAt_ballisticVelocity {H : ℝ} (hH : H ≠ 0) (ρ0 β γ he ve h : ℝ) (hβ : 0 < β)
    (hγ : 0 < Real.sin γ) :
    HasDerivAt (ballisticVelocity ρ0 H β γ he ve)
      (exponentialDensity ρ0 H h * ballisticVelocity ρ0 H β γ he ve h /
        (2 * β * Real.sin γ)) h := by
  have h1 : HasDerivAt (fun h : ℝ => -h / H) (-1 / H) h :=
    (hasDerivAt_id' h).neg.div_const H
  have hV : HasDerivAt (fun h : ℝ => ve * Real.exp (ballisticK ρ0 H β γ *
      (Real.exp (-he / H) - Real.exp (-h / H))))
      (ve * (Real.exp (ballisticK ρ0 H β γ * (Real.exp (-he / H) - Real.exp (-h / H))) *
        (ballisticK ρ0 H β γ * (0 - Real.exp (-h / H) * (-1 / H))))) h :=
    (((hasDerivAt_const h (Real.exp (-he / H))).sub h1.exp).const_mul
      (ballisticK ρ0 H β γ)).exp.const_mul ve
  have heq : ve * (Real.exp (ballisticK ρ0 H β γ * (Real.exp (-he / H) - Real.exp (-h / H))) *
      (ballisticK ρ0 H β γ * (0 - Real.exp (-h / H) * (-1 / H)))) =
      exponentialDensity ρ0 H h * ballisticVelocity ρ0 H β γ he ve h /
        (2 * β * Real.sin γ) := by
    unfold exponentialDensity ballisticVelocity ballisticK
    have hD : 2 * β * Real.sin γ ≠ 0 := mul_ne_zero (mul_ne_zero two_ne_zero hβ.ne') hγ.ne'
    field_simp
    ring
  rw [heq] at hV
  exact hV

/-! ## B. The equations of motion -/

set_option linter.unusedVariables false in
/-- Derivation from the equations of motion: for `H ≠ 0`, `β > 0` and a downward path,
`sin γ > 0`, if on the window `[t₀, t₁]`, `t₀ ≤ t₁`, the altitude and speed satisfy
`h' = -v * sin γ` and `v' = -ρ(h) * v ^ 2 / (2 * β)` with entry state `h(t₀) = he`,
`v(t₀) = ve`, then `v(t) = ballisticVelocity (h(t))` throughout the window. The proof does not use
`t₀ ≤ t₁`; the hypothesis excludes the empty window, on which the statement says nothing. -/
lemma ballisticVelocity_of_ode {ρ0 H β γ he ve t₀ t₁ : ℝ} {h v : ℝ → ℝ} (hH : H ≠ 0)
    (hβ : 0 < β) (hγ : 0 < Real.sin γ) (hwin : t₀ ≤ t₁)
    (hh : ∀ t ∈ Set.Icc t₀ t₁, HasDerivAt h (-(v t) * Real.sin γ) t)
    (hv : ∀ t ∈ Set.Icc t₀ t₁,
      HasDerivAt v (-(exponentialDensity ρ0 H (h t)) * v t ^ 2 / (2 * β)) t)
    (h0 : h t₀ = he) (v0 : v t₀ = ve) :
    ∀ t ∈ Set.Icc t₀ t₁, v t = ballisticVelocity ρ0 H β γ he ve (h t) := by
  have hw0 : ∀ t ∈ Set.Icc t₀ t₁, HasDerivAt
      (fun t => v t * Real.exp (-(ballisticK ρ0 H β γ *
        (Real.exp (-he / H) - Real.exp (-h t / H))))) 0 t := by
    intro t ht
    have h1 : HasDerivAt (fun t : ℝ => -h t / H) (-(-(v t) * Real.sin γ) / H) t :=
      (hh t ht).neg.div_const H
    have hE : HasDerivAt (fun t : ℝ => ballisticK ρ0 H β γ *
        (Real.exp (-he / H) - Real.exp (-h t / H)))
        (ballisticK ρ0 H β γ * (0 - Real.exp (-h t / H) * (-(-(v t) * Real.sin γ) / H))) t :=
      ((hasDerivAt_const t (Real.exp (-he / H))).sub h1.exp).const_mul
        (ballisticK ρ0 H β γ)
    have hw : HasDerivAt (fun t => v t * Real.exp (-(ballisticK ρ0 H β γ *
        (Real.exp (-he / H) - Real.exp (-h t / H)))))
        ((-(exponentialDensity ρ0 H (h t)) * v t ^ 2 / (2 * β)) *
          Real.exp (-(ballisticK ρ0 H β γ * (Real.exp (-he / H) - Real.exp (-h t / H)))) +
          v t * (Real.exp (-(ballisticK ρ0 H β γ * (Real.exp (-he / H) - Real.exp (-h t / H)))) *
            (-(ballisticK ρ0 H β γ *
              (0 - Real.exp (-h t / H) * (-(-(v t) * Real.sin γ) / H)))))) t :=
      (hv t ht).mul hE.neg.exp
    have hbal : (-(exponentialDensity ρ0 H (h t)) * v t ^ 2 / (2 * β)) *
          Real.exp (-(ballisticK ρ0 H β γ * (Real.exp (-he / H) - Real.exp (-h t / H)))) +
          v t * (Real.exp (-(ballisticK ρ0 H β γ * (Real.exp (-he / H) - Real.exp (-h t / H)))) *
            (-(ballisticK ρ0 H β γ *
              (0 - Real.exp (-h t / H) * (-(-(v t) * Real.sin γ) / H))))) = 0 := by
      unfold exponentialDensity ballisticK
      have h2β : (2 : ℝ) * β ≠ 0 := mul_ne_zero (by norm_num) hβ.ne'
      have hD : 2 * β * Real.sin γ ≠ 0 := mul_ne_zero h2β hγ.ne'
      field_simp
      ring
    rw [hbal] at hw
    exact hw
  have hconst : ∀ t ∈ Set.Icc t₀ t₁,
      v t * Real.exp (-(ballisticK ρ0 H β γ * (Real.exp (-he / H) - Real.exp (-h t / H)))) =
      ve := by
    intro t ht
    have ht0 : t₀ ≤ t := ht.1
    have hFTC : (∫ y in t₀..t, (0 : ℝ)) =
        (fun t => v t * Real.exp (-(ballisticK ρ0 H β γ *
          (Real.exp (-he / H) - Real.exp (-h t / H))))) t -
        (fun t => v t * Real.exp (-(ballisticK ρ0 H β γ *
          (Real.exp (-he / H) - Real.exp (-h t / H))))) t₀ :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x hx => by
        rw [Set.uIcc_of_le ht0] at hx
        exact hw0 x ⟨hx.1, le_trans hx.2 ht.2⟩) intervalIntegrable_const
    rw [show (∫ y in t₀..t, (0 : ℝ)) = 0 from by simp] at hFTC
    have h1 := sub_eq_zero.mp hFTC.symm
    beta_reduce at h1
    rw [h0, v0, sub_self, mul_zero, neg_zero, Real.exp_zero, mul_one] at h1
    exact h1
  intro t ht
  have h1 := hconst t ht
  have hexp : Real.exp (-(ballisticK ρ0 H β γ * (Real.exp (-he / H) - Real.exp (-h t / H)))) *
      Real.exp (ballisticK ρ0 H β γ * (Real.exp (-he / H) - Real.exp (-h t / H))) = 1 := by
    rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  have h2 : v t =
      ve * Real.exp (ballisticK ρ0 H β γ * (Real.exp (-he / H) - Real.exp (-h t / H))) := by
    calc v t = v t * 1 := (mul_one _).symm
      _ = v t * (Real.exp (-(ballisticK ρ0 H β γ * (Real.exp (-he / H) - Real.exp (-h t / H)))) *
          Real.exp (ballisticK ρ0 H β γ *
            (Real.exp (-he / H) - Real.exp (-h t / H)))) := by rw [hexp]
      _ = (v t * Real.exp (-(ballisticK ρ0 H β γ * (Real.exp (-he / H) - Real.exp (-h t / H))))) *
          Real.exp (ballisticK ρ0 H β γ * (Real.exp (-he / H) - Real.exp (-h t / H))) := by ring
      _ = ve * Real.exp (ballisticK ρ0 H β γ *
          (Real.exp (-he / H) - Real.exp (-h t / H))) := by rw [h1]
  exact h2

/-- Converse: for `H ≠ 0`, `β > 0` and a downward path, `sin γ > 0`, along an altitude trajectory
with `h' = -v * sin γ` for `v = ballisticVelocity ∘ h`, the speed `ballisticVelocity ∘ h`
satisfies the drag equation `v' = -ρ(h) * v ^ 2 / (2 * β)`. -/
lemma hasDerivAt_ballisticVelocity_comp {ρ0 H β γ he ve t : ℝ} {h : ℝ → ℝ} (hH : H ≠ 0)
    (hβ : 0 < β) (hγ : 0 < Real.sin γ)
    (hh : HasDerivAt h (-(ballisticVelocity ρ0 H β γ he ve (h t)) * Real.sin γ) t) :
    HasDerivAt (fun τ => ballisticVelocity ρ0 H β γ he ve (h τ))
      (-(exponentialDensity ρ0 H (h t)) * ballisticVelocity ρ0 H β γ he ve (h t) ^ 2 /
        (2 * β)) t := by
  have hV := hasDerivAt_ballisticVelocity hH ρ0 β γ he ve (h t) hβ hγ
  have hcomp : HasDerivAt (fun τ => ballisticVelocity ρ0 H β γ he ve (h τ))
      (exponentialDensity ρ0 H (h t) * ballisticVelocity ρ0 H β γ he ve (h t) /
        (2 * β * Real.sin γ) * (-(ballisticVelocity ρ0 H β γ he ve (h t)) * Real.sin γ)) t :=
    hV.comp t hh
  have heq : exponentialDensity ρ0 H (h t) * ballisticVelocity ρ0 H β γ he ve (h t) /
        (2 * β * Real.sin γ) * (-(ballisticVelocity ρ0 H β γ he ve (h t)) * Real.sin γ) =
      -(exponentialDensity ρ0 H (h t)) * ballisticVelocity ρ0 H β γ he ve (h t) ^ 2 / (2 * β) := by
    have h2β : (2 : ℝ) * β ≠ 0 := mul_ne_zero (by norm_num) hβ.ne'
    have hD : 2 * β * Real.sin γ ≠ 0 := mul_ne_zero h2β hγ.ne'
    field_simp
  rw [heq] at hcomp
  exact hcomp

/-! ## C. Descent and the entry condition -/

/-- The profile is positive for a positive entry speed. -/
lemma ballisticVelocity_pos {ve : ℝ} (hve : 0 < ve) (ρ0 H β γ he h : ℝ) :
    0 < ballisticVelocity ρ0 H β γ he ve h := by
  unfold ballisticVelocity
  exact mul_pos hve (Real.exp_pos _)

/-- Descent decelerates: for `ρ0, H, β, ve > 0` and a downward path, `sin γ > 0`, the profile is
strictly increasing in altitude, so the speed falls as the vehicle descends below the entry
altitude. -/
lemma ballisticVelocity_strictMono {ρ0 H β γ ve : ℝ} (hρ0 : 0 < ρ0) (hH : 0 < H) (hβ : 0 < β)
    (hγ : 0 < Real.sin γ) (hve : 0 < ve) (he : ℝ) :
    StrictMono (ballisticVelocity ρ0 H β γ he ve) := by
  have hK : 0 < ballisticK ρ0 H β γ := ballisticK_pos hρ0 hH hβ hγ
  intro a b hab
  unfold ballisticVelocity
  have s1 : -b / H < -a / H := div_lt_div_of_pos_right (neg_lt_neg hab) hH
  have s2 : Real.exp (-b / H) < Real.exp (-a / H) := Real.exp_lt_exp.mpr s1
  have s3 : Real.exp (-he / H) - Real.exp (-a / H) < Real.exp (-he / H) - Real.exp (-b / H) :=
    sub_lt_sub_left s2 _
  have s4 : ballisticK ρ0 H β γ * (Real.exp (-he / H) - Real.exp (-a / H)) <
      ballisticK ρ0 H β γ * (Real.exp (-he / H) - Real.exp (-b / H)) :=
    mul_lt_mul_of_pos_left s3 hK
  have s5 : Real.exp (ballisticK ρ0 H β γ * (Real.exp (-he / H) - Real.exp (-a / H))) <
      Real.exp (ballisticK ρ0 H β γ * (Real.exp (-he / H) - Real.exp (-b / H))) :=
    Real.exp_lt_exp.mpr s4
  exact mul_lt_mul_of_pos_left s5 hve

/-- Infinite-entry normalization is not finite entry data: for `ρ0, H, β > 0`, `sin γ > 0` and
`ve ≠ 0`, dropping the `exp (-he / H)` term from the exponent gives a profile whose value at the
entry altitude is not `ve`. -/
lemma omitted_entry_term_ne {ρ0 H β γ ve : ℝ} (hρ0 : 0 < ρ0) (hH : 0 < H) (hβ : 0 < β)
    (hγ : 0 < Real.sin γ) (hve : ve ≠ 0) (he : ℝ) :
    ve * Real.exp (ballisticK ρ0 H β γ * -Real.exp (-he / H)) ≠ ve := by
  have hK : 0 < ballisticK ρ0 H β γ := ballisticK_pos hρ0 hH hβ hγ
  have hexp : ballisticK ρ0 H β γ * -Real.exp (-he / H) < 0 :=
    mul_neg_of_pos_of_neg hK (neg_lt_zero.mpr (Real.exp_pos _))
  intro hcon
  have h1 : Real.exp (ballisticK ρ0 H β γ * -Real.exp (-he / H)) = 1 :=
    mul_left_cancel₀ hve (by rw [mul_one]; exact hcon)
  rw [Real.exp_eq_one_iff] at h1
  exact absurd h1 (ne_of_lt hexp)

/-! ## D. The isothermal layer -/

set_option linter.unusedVariables false in
/-- With the isothermal-layer density `isothermalDensity ρ0 g Rs T` as the atmosphere,
`g, Rs, T > 0`, `β > 0`, a downward path and the window `t₀ ≤ t₁`, the derivation gives the same
profile with `H` the scale height `Rs * T / |g|`. The isothermal layer model holds only on a
declared altitude band `[z₁, z₂]`, so the trajectory is required to stay in it on the window. The
proof does not use the band; the hypothesis restricts the statement to the model's regime. -/
lemma ballisticVelocity_of_ode_isothermalDensity {ρ0 g Rs T β γ he ve t₀ t₁ z₁ z₂ : ℝ}
    {h v : ℝ → ℝ} (hg : 0 < g) (hRs : 0 < Rs) (hT : 0 < T) (hβ : 0 < β) (hγ : 0 < Real.sin γ)
    (hwin : t₀ ≤ t₁) (hband : ∀ t ∈ Set.Icc t₀ t₁, h t ∈ Set.Icc z₁ z₂)
    (hh : ∀ t ∈ Set.Icc t₀ t₁, HasDerivAt h (-(v t) * Real.sin γ) t)
    (hv : ∀ t ∈ Set.Icc t₀ t₁,
      HasDerivAt v (-(isothermalDensity ρ0 g Rs T (h t)) * v t ^ 2 / (2 * β)) t)
    (h0 : h t₀ = he) (v0 : v t₀ = ve) :
    ∀ t ∈ Set.Icc t₀ t₁, v t = ballisticVelocity ρ0 (scaleHeight Rs T g) β γ he ve (h t) := by
  have hH' : scaleHeight Rs T g ≠ 0 :=
    ne_of_gt (scaleHeight_pos hRs hT (ne_of_gt hg))
  have heq : ∀ z : ℝ, isothermalDensity ρ0 g Rs T z =
      exponentialDensity ρ0 (scaleHeight Rs T g) z :=
    fun z => isothermalDensity_eq_exp hg hRs hT ρ0 z
  have hv' : ∀ t ∈ Set.Icc t₀ t₁, HasDerivAt v
      (-(exponentialDensity ρ0 (scaleHeight Rs T g) (h t)) * v t ^ 2 / (2 * β)) t := by
    intro t ht
    simpa [heq (h t)] using hv t ht
  exact ballisticVelocity_of_ode hH' hβ hγ hwin hh hv' h0 v0

/-! ## E. Stagnation-point heat load and radiator equilibrium -/

/-- A supplied stagnation-point heating correlation of the Sutton-Graves form
`q = kSG * sqrt (ρ / rn) * v ^ 3`: the convective heat flux per unit area at the stagnation point
of a blunt nose of radius `rn` moving at speed `v` through free-stream density `ρ`. The record
holds the citation (provenance only, not an applicability condition), the coefficient `kSG ≥ 0`
and the validity box `0 ≤ ρ ≤ ρmax`, `rmin ≤ rn`, `0 ≤ v ≤ vmax` with `rmin > 0`, which is
nonempty. Coefficient and box are calibration evidence supplied with the correlation; nothing
here asserts that the formula is physically adequate inside or outside the box. -/
structure StagnationHeatingCorrelation where
  /-- The published source of the correlation (provenance, not an applicability condition). -/
  citation : String
  /-- The coefficient `kSG`; in SI units `kg ^ (1 / 2) / m` for fluxes in `W / m ^ 2`. -/
  coefficient : ℝ
  /-- The largest free-stream density `ρmax` of the validity box. -/
  maxDensity : ℝ
  /-- The smallest nose radius `rmin` of the validity box. -/
  minNoseRadius : ℝ
  /-- The largest speed `vmax` of the validity box. -/
  maxSpeed : ℝ
  coefficient_nonneg : 0 ≤ coefficient
  minNoseRadius_pos : 0 < minNoseRadius
  maxDensity_nonneg : 0 ≤ maxDensity
  maxSpeed_nonneg : 0 ≤ maxSpeed

namespace StagnationHeatingCorrelation

/-- The correlation applies at free-stream density `ρ`, nose radius `rn` and speed `v`: the point
lies in its validity box `0 ≤ ρ ≤ ρmax`, `rmin ≤ rn`, `0 ≤ v ≤ vmax`. -/
def Applies (C : StagnationHeatingCorrelation) (ρ rn v : ℝ) : Prop :=
  ρ ∈ Set.Icc 0 C.maxDensity ∧ C.minNoseRadius ≤ rn ∧ v ∈ Set.Icc 0 C.maxSpeed

/-- The stagnation-point heat flux `q = kSG * sqrt (ρ / rn) * v ^ 3` per unit area, evaluated only
where the correlation applies. -/
noncomputable def heatFlux (C : StagnationHeatingCorrelation) (ρ rn v : ℝ)
    (_h : C.Applies ρ rn v) : ℝ :=
  C.coefficient * Real.sqrt (ρ / rn) * v ^ 3

/-- The heat load `∫ q dt` over the finite horizon `[0, tf]`, `0 ≤ tf`, of a history
`t ↦ (ρ t, rn t, v t)` that stays in the validity box on the horizon. It is heat per unit area
(`J / m ^ 2` in SI units); the heat into a surface needs a declared area to multiply it. It is
the heat load only for an interval-integrable flux: otherwise Lean's integral is `0` by
convention, and the bounds below assume integrability. -/
noncomputable def heatLoad (C : StagnationHeatingCorrelation) (tf : ℝ) (ρ rn v : ℝ → ℝ)
    (_htf : 0 ≤ tf) (_h : ∀ t ∈ Set.Icc 0 tf, C.Applies (ρ t) (rn t) (v t)) : ℝ :=
  ∫ t in (0 : ℝ)..tf, C.coefficient * Real.sqrt (ρ t / rn t) * v t ^ 3

/-- Pointwise Sutton-Graves bound for arbitrary box limits. -/
private lemma flux_le_of_bounds {k ρ rn v ρm rm vm : ℝ} (hk : 0 ≤ k) (hρ0 : 0 ≤ ρ) (hρ : ρ ≤ ρm)
    (hrm : 0 < rm) (hrn : rm ≤ rn) (hv0 : 0 ≤ v) (hv : v ≤ vm) :
    k * Real.sqrt (ρ / rn) * v ^ 3 ≤ k * Real.sqrt (ρm / rm) * vm ^ 3 := by
  have h1 : ρ / rn ≤ ρm / rm := div_le_div₀ (hρ0.trans hρ) hρ hrm hrn
  have h2 : Real.sqrt (ρ / rn) ≤ Real.sqrt (ρm / rm) := Real.sqrt_le_sqrt h1
  have h3 : v ^ 3 ≤ vm ^ 3 := pow_le_pow_left₀ hv0 hv 3
  exact mul_le_mul (mul_le_mul_of_nonneg_left h2 hk) h3 (pow_nonneg hv0 3)
    (mul_nonneg hk (Real.sqrt_nonneg _))

/-- For `0 ≤ tf`, an interval-integrable integrand at most `M` on `[0, tf]` integrates to at most
`tf * M`. -/
private lemma integral_le_of_forall_le {f : ℝ → ℝ} {tf M : ℝ} (htf : 0 ≤ tf)
    (hint : IntervalIntegrable f MeasureTheory.volume 0 tf) (hf : ∀ t ∈ Set.Icc 0 tf, f t ≤ M) :
    ∫ t in (0 : ℝ)..tf, f t ≤ tf * M := by
  have h := intervalIntegral.integral_mono_on htf hint intervalIntegrable_const hf
  rwa [intervalIntegral.integral_const, smul_eq_mul, sub_zero] at h

/-- The validity box is nonempty: the correlation applies somewhere. -/
lemma exists_applies (C : StagnationHeatingCorrelation) : ∃ ρ rn v : ℝ, C.Applies ρ rn v := by
  exact ⟨0, C.minNoseRadius, 0, ⟨le_rfl, C.maxDensity_nonneg⟩, le_rfl, ⟨le_rfl, C.maxSpeed_nonneg⟩⟩

/-- Where the correlation applies, the heat flux is nonnegative. -/
lemma heatFlux_nonneg (C : StagnationHeatingCorrelation) {ρ rn v : ℝ} (h : C.Applies ρ rn v) :
    0 ≤ C.heatFlux ρ rn v h := by
  unfold heatFlux
  exact mul_nonneg (mul_nonneg C.coefficient_nonneg (Real.sqrt_nonneg _)) (pow_nonneg h.2.2.1 3)

/-- Pointwise bound: where the correlation applies, `q ≤ kSG * sqrt (ρmax / rmin) * vmax ^ 3`. -/
lemma heatFlux_le (C : StagnationHeatingCorrelation) {ρ rn v : ℝ} (h : C.Applies ρ rn v) :
    C.heatFlux ρ rn v h ≤
      C.coefficient * Real.sqrt (C.maxDensity / C.minNoseRadius) * C.maxSpeed ^ 3 := by
  unfold heatFlux
  obtain ⟨⟨hρ0, hρ⟩, hrn, ⟨hv0, hv⟩⟩ := h
  exact flux_le_of_bounds C.coefficient_nonneg hρ0 hρ C.minNoseRadius_pos hrn hv0 hv

/-- The heat load of a history in the validity box with an interval-integrable flux is
nonnegative. -/
lemma heatLoad_nonneg (C : StagnationHeatingCorrelation) {tf : ℝ} {ρ rn v : ℝ → ℝ}
    (htf : 0 ≤ tf) (h : ∀ t ∈ Set.Icc 0 tf, C.Applies (ρ t) (rn t) (v t))
    (hint : IntervalIntegrable (fun t => C.coefficient * Real.sqrt (ρ t / rn t) * v t ^ 3)
      MeasureTheory.volume 0 tf) :
    0 ≤ C.heatLoad tf ρ rn v htf h := by
  unfold heatLoad
  have h0 := intervalIntegral.integral_mono_on htf intervalIntegrable_const hint
    fun t ht => C.heatFlux_nonneg (h t ht)
  simpa using h0

/-- Finite-horizon heat-load bound: for a history that stays in the validity box on `[0, tf]`
and has an interval-integrable flux, the heat load per unit area is at most
`tf * kSG * sqrt (ρmax / rmin) * vmax ^ 3`. -/
lemma heatLoad_le (C : StagnationHeatingCorrelation) {tf : ℝ} {ρ rn v : ℝ → ℝ} (htf : 0 ≤ tf)
    (h : ∀ t ∈ Set.Icc 0 tf, C.Applies (ρ t) (rn t) (v t))
    (hint : IntervalIntegrable (fun t => C.coefficient * Real.sqrt (ρ t / rn t) * v t ^ 3)
      MeasureTheory.volume 0 tf) :
    C.heatLoad tf ρ rn v htf h ≤
      tf * C.coefficient * Real.sqrt (C.maxDensity / C.minNoseRadius) * C.maxSpeed ^ 3 := by
  unfold heatLoad
  have key := integral_le_of_forall_le
    (M := C.coefficient * Real.sqrt (C.maxDensity / C.minNoseRadius) * C.maxSpeed ^ 3) htf hint
    fun t ht => C.heatFlux_le (h t ht)
  calc ∫ t in (0 : ℝ)..tf, C.coefficient * Real.sqrt (ρ t / rn t) * v t ^ 3
      ≤ tf * (C.coefficient * Real.sqrt (C.maxDensity / C.minNoseRadius) * C.maxSpeed ^ 3) := key
    _ = tf * C.coefficient * Real.sqrt (C.maxDensity / C.minNoseRadius) * C.maxSpeed ^ 3 := by
      ring

/-- Vacuum gives zero convective heating: a history in the validity box with zero free-stream
density on `[0, tf]` has zero heat load. -/
lemma heatLoad_vacuum (C : StagnationHeatingCorrelation) {tf : ℝ} {ρ rn v : ℝ → ℝ}
    (htf : 0 ≤ tf) (h : ∀ t ∈ Set.Icc 0 tf, C.Applies (ρ t) (rn t) (v t))
    (hρ : ∀ t ∈ Set.Icc 0 tf, ρ t = 0) : C.heatLoad tf ρ rn v htf h = 0 := by
  unfold heatLoad
  have hzero : Set.EqOn (fun t => C.coefficient * Real.sqrt (ρ t / rn t) * v t ^ 3)
      (fun _ => (0 : ℝ)) (Set.uIcc 0 tf) := by
    intro t ht
    rw [Set.uIcc_of_le htf] at ht
    simp only [hρ t ht, zero_div, Real.sqrt_zero, mul_zero, zero_mul]
  rw [intervalIntegral.integral_congr hzero, intervalIntegral.integral_zero]

/-- Heat load along the finite-entry ballistic profile: for `ρ0, H, β > 0`, a downward path,
`sin γ > 0`, and `ve > 0`, if on `[0, tf]` the altitude `h t` stays in the band `[hmin, he]` below
the entry altitude, the history `(ρ(h t), rn t, v(h t))` stays in the validity box and its flux is
interval integrable, then the density is at most `ρ(hmin)` and the speed at most `ve`, so the heat
load per unit area is at most `tf * kSG * sqrt (ρ(hmin) / rmin) * ve ^ 3`. -/
lemma heatLoad_le_of_band (C : StagnationHeatingCorrelation) {ρ0 H β γ he ve hmin tf : ℝ}
    {h rn : ℝ → ℝ} (hρ0 : 0 < ρ0) (hH : 0 < H) (hβ : 0 < β) (hγ : 0 < Real.sin γ)
    (hve : 0 < ve) (htf : 0 ≤ tf) (hband : ∀ t ∈ Set.Icc 0 tf, h t ∈ Set.Icc hmin he)
    (hbox : ∀ t ∈ Set.Icc 0 tf, C.Applies (exponentialDensity ρ0 H (h t)) (rn t)
      (ballisticVelocity ρ0 H β γ he ve (h t)))
    (hint : IntervalIntegrable (fun t => C.coefficient *
      Real.sqrt (exponentialDensity ρ0 H (h t) / rn t) *
        ballisticVelocity ρ0 H β γ he ve (h t) ^ 3) MeasureTheory.volume 0 tf) :
    C.heatLoad tf (fun t => exponentialDensity ρ0 H (h t)) rn
        (fun t => ballisticVelocity ρ0 H β γ he ve (h t)) htf hbox ≤
      tf * C.coefficient * Real.sqrt (exponentialDensity ρ0 H hmin / C.minNoseRadius) *
        ve ^ 3 := by
  unfold heatLoad
  have hmono := (ballisticVelocity_strictMono hρ0 hH hβ hγ hve he).monotone
  have key := integral_le_of_forall_le
    (M := C.coefficient * Real.sqrt (exponentialDensity ρ0 H hmin / C.minNoseRadius) * ve ^ 3)
    htf hint fun t ht => by
      obtain ⟨⟨hρ0', -⟩, hrn, ⟨hv0, -⟩⟩ := hbox t ht
      have hρle : exponentialDensity ρ0 H (h t) ≤ exponentialDensity ρ0 H hmin := by
        unfold exponentialDensity
        have hdiv : -h t / H ≤ -hmin / H :=
          div_le_div_of_nonneg_right (neg_le_neg (hband t ht).1) hH.le
        exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hdiv) hρ0.le
      have hvle : ballisticVelocity ρ0 H β γ he ve (h t) ≤ ve := by
        have := hmono (hband t ht).2
        rwa [ballisticVelocity_entry] at this
      exact flux_le_of_bounds C.coefficient_nonneg hρ0' hρle C.minNoseRadius_pos hrn hv0 hvle
  calc ∫ t in (0 : ℝ)..tf, C.coefficient * Real.sqrt (exponentialDensity ρ0 H (h t) / rn t) *
        ballisticVelocity ρ0 H β γ he ve (h t) ^ 3
      ≤ tf * (C.coefficient * Real.sqrt (exponentialDensity ρ0 H hmin / C.minNoseRadius) *
        ve ^ 3) := key
    _ = tf * C.coefficient * Real.sqrt (exponentialDensity ρ0 H hmin / C.minNoseRadius) *
        ve ^ 3 := by ring

end StagnationHeatingCorrelation

set_option linter.unusedVariables false in
/-- Radiator equilibrium: a gray radiator of emissivity `ε` that absorbs the flux `qabs` per unit
area and exchanges thermal radiation with large surroundings at absolute temperature `Tenv` emits
`ε * σ * T ^ 4` and absorbs `ε * σ * Tenv ^ 4`, so it is in equilibrium at `T` when
`ε * σ * T ^ 4 = qabs + ε * σ * Tenv ^ 4`. For `0 < ε ≤ 1`, `σ > 0`, `qabs ≥ 0` and `Tenv ≥ 0` a
nonnegative equilibrium exists: the fourth-power equilibrium theorem with coefficient `ε * σ`,
albedo `0` and supplied flux `4 * (qabs + ε * σ * Tenv ^ 4)`. The proof does not use `ε ≤ 1` or
`0 ≤ Tenv`; they restrict the statement to a gray surface and an absolute temperature. -/
lemma radiator_equilibrium_exists {ε σ qabs Tenv : ℝ} (hε : 0 < ε) (hε₁ : ε ≤ 1) (hσ : 0 < σ)
    (hq : 0 ≤ qabs) (hTenv : 0 ≤ Tenv) :
    ∃ T : ℝ, 0 ≤ T ∧ ε * σ * T ^ 4 = qabs + ε * σ * Tenv ^ 4 := by
  have hεσ : 0 < ε * σ := mul_pos hε hσ
  have hS : 0 ≤ 4 * (qabs + ε * σ * Tenv ^ 4) :=
    mul_nonneg (by norm_num) (add_nonneg hq (mul_nonneg hεσ.le (Even.pow_nonneg (by decide) Tenv)))
  obtain ⟨T, hT, hTeq⟩ :=
    EarthScience.planetaryEnergyBalance_equilibrium_exists hεσ hS (le_refl 0) zero_le_one
  refine ⟨T, hT, ?_⟩
  rw [hTeq]
  ring

set_option linter.unusedVariables false in
/-- For `0 < ε ≤ 1`, `σ > 0` and `Tenv ≥ 0` the nonnegative radiator equilibrium is unique: the
uniqueness half of the fourth-power equilibrium theorem with coefficient `ε * σ`. The proof does
not use `ε ≤ 1` or `0 ≤ Tenv`; they restrict the statement to a gray surface and an absolute
temperature. -/
lemma radiator_equilibrium_unique {ε σ qabs Tenv T₁ T₂ : ℝ} (hε : 0 < ε) (hε₁ : ε ≤ 1)
    (hσ : 0 < σ) (hTenv : 0 ≤ Tenv) (hT₁ : 0 ≤ T₁) (hT₂ : 0 ≤ T₂)
    (h₁ : ε * σ * T₁ ^ 4 = qabs + ε * σ * Tenv ^ 4)
    (h₂ : ε * σ * T₂ ^ 4 = qabs + ε * σ * Tenv ^ 4) : T₁ = T₂ := by
  have hεσ : 0 < ε * σ := mul_pos hε hσ
  refine EarthScience.planetaryEnergyBalance_equilibrium_unique
    (S := 4 * (qabs + ε * σ * Tenv ^ 4)) (α := 0) hεσ hT₁ hT₂ ?_ ?_
  · rw [h₁]
    ring
  · rw [h₂]
    ring

/-! ## F. Peak deceleration on the entry band -/

/-- Drag deceleration along the finite-entry profile, `a(h) = ρ(h) * v(h) ^ 2 / (2 * β)`, for the
exponential density and the profile `ballisticVelocity` with entry state `(he, ve)`; for
`ρ0 ≥ 0` and `β > 0` it is the magnitude of `v' = -ρ(h) * v ^ 2 / (2 * β)` at altitude `h`. With
the convention `x / 0 = 0` it is `0` when `β = 0`. -/
noncomputable def ballisticDeceleration (ρ0 H β γ he ve h : ℝ) : ℝ :=
  exponentialDensity ρ0 H h * ballisticVelocity ρ0 H β γ he ve h ^ 2 / (2 * β)

/-- Candidate peak-deceleration altitude `hstar = H * log (2 * K)`, `K = ballisticK ρ0 H β γ`; it
does not depend on the entry state. For `ρ0, H, β, ve > 0` and `sin γ > 0`, which give `K > 0`,
it is the only stationary point and the strict global maximum of the deceleration
(`deriv_ballisticDeceleration_eq_zero_iff`, `ballisticDeceleration_lt_peak`). For `H > 0` and
`0 < 2 * K ≤ 1` it lies at or below `h = 0`. With the conventions `log 0 = 0` and
`log x = log |x|`, `hstar = 0` when `K = 0` and `hstar = H * log |2 * K|` when `K < 0`. -/
noncomputable def peakDecelerationAltitude (ρ0 H β γ : ℝ) : ℝ :=
  H * Real.log (2 * ballisticK ρ0 H β γ)

/-- The peak altitude selected on the band `[hmin, he]`: `hstar` clamped to the band, which for
`hmin < he` is `hstar` when it lies in the band and otherwise the nearer endpoint (`hmin` below the
band, `he` above it); for `hmin ≥ he` it is `hmin`. For `ρ0, H, β, ve > 0`, `sin γ > 0` and
`hmin < he` it maximizes the deceleration on the band (`isMaxOn_bandPeakAltitude`). -/
noncomputable def bandPeakAltitude (ρ0 H β γ hmin he : ℝ) : ℝ :=
  max hmin (min (peakDecelerationAltitude ρ0 H β γ) he)

/-- `2 * K * exp (-h / H) = exp ((hstar - h) / H)` for `K > 0`, `H ≠ 0`. -/
private lemma two_mul_ballisticK_mul_exp {ρ0 H β γ : ℝ} (hH : H ≠ 0)
    (hK : 0 < ballisticK ρ0 H β γ) (h : ℝ) :
    2 * ballisticK ρ0 H β γ * Real.exp (-h / H) =
      Real.exp ((peakDecelerationAltitude ρ0 H β γ - h) / H) := by
  unfold peakDecelerationAltitude
  have h2K : 0 < 2 * ballisticK ρ0 H β γ := mul_pos two_pos hK
  have hsplit : (H * Real.log (2 * ballisticK ρ0 H β γ) - h) / H =
      Real.log (2 * ballisticK ρ0 H β γ) + -h / H := by
    field_simp
    ring
  rw [hsplit, Real.exp_add, Real.exp_log h2K]

/-- The deceleration is positive for `ρ0, β, ve > 0`. -/
lemma ballisticDeceleration_pos {ρ0 β ve : ℝ} (hρ0 : 0 < ρ0) (hβ : 0 < β) (hve : 0 < ve)
    (H γ he h : ℝ) : 0 < ballisticDeceleration ρ0 H β γ he ve h := by
  unfold ballisticDeceleration exponentialDensity
  exact div_pos (mul_pos (mul_pos hρ0 (Real.exp_pos _))
    (pow_pos (ballisticVelocity_pos hve ρ0 H β γ he h) 2)) (mul_pos two_pos hβ)

/-- Derivative in altitude: for `H ≠ 0`, `β > 0` and a downward path, `sin γ > 0`,
`a'(h) = a(h) * (2 * K * exp (-h / H) - 1) / H`. -/
lemma hasDerivAt_ballisticDeceleration {H : ℝ} (hH : H ≠ 0) (ρ0 β γ he ve h : ℝ) (hβ : 0 < β)
    (hγ : 0 < Real.sin γ) :
    HasDerivAt (ballisticDeceleration ρ0 H β γ he ve)
      (ballisticDeceleration ρ0 H β γ he ve h *
        (2 * ballisticK ρ0 H β γ * Real.exp (-h / H) - 1) / H) h := by
  have h1 : HasDerivAt (fun x : ℝ => -x / H) (-1 / H) h := (hasDerivAt_id' h).neg.div_const H
  have hρ : HasDerivAt (fun x => exponentialDensity ρ0 H x)
      (ρ0 * (Real.exp (-h / H) * (-1 / H))) h := h1.exp.const_mul ρ0
  have hv := hasDerivAt_ballisticVelocity hH ρ0 β γ he ve h hβ hγ
  have hprod := (hρ.mul (hv.mul hv)).div_const (2 * β)
  have hfun : ballisticDeceleration ρ0 H β γ he ve = fun x => exponentialDensity ρ0 H x *
      (ballisticVelocity ρ0 H β γ he ve x * ballisticVelocity ρ0 H β γ he ve x) / (2 * β) := by
    funext x
    unfold ballisticDeceleration
    ring
  rw [hfun]
  convert hprod using 1
  simp only [Pi.mul_apply]
  unfold exponentialDensity ballisticK
  have hD : 2 * β * Real.sin γ ≠ 0 := mul_ne_zero (mul_ne_zero two_ne_zero hβ.ne') hγ.ne'
  field_simp
  ring

/-- The candidate maximum: for `ρ0, H, β, ve > 0` and `sin γ > 0` the derivative of the
deceleration vanishes exactly at `hstar = H * log (2 * K)`. -/
lemma deriv_ballisticDeceleration_eq_zero_iff {ρ0 H β γ ve : ℝ} (hρ0 : 0 < ρ0) (hH : 0 < H)
    (hβ : 0 < β) (hγ : 0 < Real.sin γ) (hve : 0 < ve) (he h : ℝ) :
    deriv (ballisticDeceleration ρ0 H β γ he ve) h = 0 ↔
      h = peakDecelerationAltitude ρ0 H β γ := by
  have hK := ballisticK_pos hρ0 hH hβ hγ
  rw [(hasDerivAt_ballisticDeceleration hH.ne' ρ0 β γ he ve h hβ hγ).deriv,
    two_mul_ballisticK_mul_exp hH.ne' hK h]
  have ha := ballisticDeceleration_pos hρ0 hβ hve H γ he h
  constructor
  · intro h0
    have h1 : Real.exp ((peakDecelerationAltitude ρ0 H β γ - h) / H) - 1 = 0 := by
      rcases div_eq_zero_iff.mp h0 with h2 | h2
      · exact (mul_eq_zero.mp h2).resolve_left ha.ne'
      · exact absurd h2 hH.ne'
    have h2 : (peakDecelerationAltitude ρ0 H β γ - h) / H = 0 :=
      (Real.exp_eq_one_iff _).mp (sub_eq_zero.mp h1)
    rcases div_eq_zero_iff.mp h2 with h3 | h3
    · linarith
    · exact absurd h3 hH.ne'
  · intro hh
    rw [hh, sub_self, zero_div, Real.exp_zero, sub_self, mul_zero, zero_div]

/-- For `ρ0, H, β, ve > 0` and `sin γ > 0`, below `hstar` the deceleration is strictly increasing in
altitude: as the vehicle descends below `hstar`, the deceleration falls. -/
lemma ballisticDeceleration_strictMonoOn {ρ0 H β γ ve : ℝ} (hρ0 : 0 < ρ0) (hH : 0 < H)
    (hβ : 0 < β) (hγ : 0 < Real.sin γ) (hve : 0 < ve) (he : ℝ) :
    StrictMonoOn (ballisticDeceleration ρ0 H β γ he ve)
      (Set.Iic (peakDecelerationAltitude ρ0 H β γ)) := by
  have hK := ballisticK_pos hρ0 hH hβ hγ
  apply strictMonoOn_of_deriv_pos (convex_Iic _)
  · exact fun x _ =>
      (hasDerivAt_ballisticDeceleration hH.ne' ρ0 β γ he ve x hβ hγ).continuousAt.continuousWithinAt
  · intro x hx
    rw [interior_Iic] at hx
    rw [(hasDerivAt_ballisticDeceleration hH.ne' ρ0 β γ he ve x hβ hγ).deriv,
      two_mul_ballisticK_mul_exp hH.ne' hK x]
    have ha := ballisticDeceleration_pos hρ0 hβ hve H γ he x
    have hpos : 0 < (peakDecelerationAltitude ρ0 H β γ - x) / H := div_pos (sub_pos.mpr hx) hH
    have h1 : 1 < Real.exp ((peakDecelerationAltitude ρ0 H β γ - x) / H) := by
      rw [← Real.exp_zero]
      exact Real.exp_lt_exp.mpr hpos
    exact div_pos (mul_pos ha (sub_pos.mpr h1)) hH

/-- For `ρ0, H, β, ve > 0` and `sin γ > 0`, above `hstar` the deceleration is strictly decreasing in
altitude: as the vehicle descends toward `hstar`, the deceleration grows. -/
lemma ballisticDeceleration_strictAntiOn {ρ0 H β γ ve : ℝ} (hρ0 : 0 < ρ0) (hH : 0 < H)
    (hβ : 0 < β) (hγ : 0 < Real.sin γ) (hve : 0 < ve) (he : ℝ) :
    StrictAntiOn (ballisticDeceleration ρ0 H β γ he ve)
      (Set.Ici (peakDecelerationAltitude ρ0 H β γ)) := by
  have hK := ballisticK_pos hρ0 hH hβ hγ
  apply strictAntiOn_of_deriv_neg (convex_Ici _)
  · exact fun x _ =>
      (hasDerivAt_ballisticDeceleration hH.ne' ρ0 β γ he ve x hβ hγ).continuousAt.continuousWithinAt
  · intro x hx
    rw [interior_Ici] at hx
    rw [(hasDerivAt_ballisticDeceleration hH.ne' ρ0 β γ he ve x hβ hγ).deriv,
      two_mul_ballisticK_mul_exp hH.ne' hK x]
    have ha := ballisticDeceleration_pos hρ0 hβ hve H γ he x
    have hneg : (peakDecelerationAltitude ρ0 H β γ - x) / H < 0 :=
      div_neg_of_neg_of_pos (sub_neg.mpr hx) hH
    have h1 : Real.exp ((peakDecelerationAltitude ρ0 H β γ - x) / H) < 1 := by
      rw [← Real.exp_zero]
      exact Real.exp_lt_exp.mpr hneg
    exact div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg ha (sub_neg.mpr h1)) hH

/-- For `ρ0, H, β, ve > 0` and `sin γ > 0`, `hstar` is the strict global maximum of the deceleration
over all altitudes. -/
lemma ballisticDeceleration_lt_peak {ρ0 H β γ ve : ℝ} (hρ0 : 0 < ρ0) (hH : 0 < H) (hβ : 0 < β)
    (hγ : 0 < Real.sin γ) (hve : 0 < ve) (he : ℝ) {h : ℝ}
    (hne : h ≠ peakDecelerationAltitude ρ0 H β γ) :
    ballisticDeceleration ρ0 H β γ he ve h <
      ballisticDeceleration ρ0 H β γ he ve (peakDecelerationAltitude ρ0 H β γ) := by
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hmono := ballisticDeceleration_strictMonoOn hρ0 hH hβ hγ hve he
    exact hmono (Set.mem_Iic.mpr (le_of_lt hlt)) (Set.mem_Iic.mpr le_rfl) hlt
  · have hanti := ballisticDeceleration_strictAntiOn hρ0 hH hβ hγ hve he
    exact hanti (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr (le_of_lt hgt)) hgt

/-- Selection inside the band: when `hstar ∈ [hmin, he]` the band peak is `hstar`. -/
lemma bandPeakAltitude_of_mem {ρ0 H β γ hmin he : ℝ}
    (hmem : peakDecelerationAltitude ρ0 H β γ ∈ Set.Icc hmin he) :
    bandPeakAltitude ρ0 H β γ hmin he = peakDecelerationAltitude ρ0 H β γ := by
  unfold bandPeakAltitude
  rw [min_eq_left hmem.2, max_eq_right hmem.1]

/-- Selection below the band: when `hstar < hmin` the band peak is the lower endpoint `hmin`. -/
lemma bandPeakAltitude_of_lt {ρ0 H β γ hmin he : ℝ}
    (hlt : peakDecelerationAltitude ρ0 H β γ < hmin) :
    bandPeakAltitude ρ0 H β γ hmin he = hmin := by
  unfold bandPeakAltitude
  exact max_eq_left ((min_le_left _ _).trans hlt.le)

/-- Selection above a nonempty band: when `hmin < he` and `he < hstar` the band peak is the entry
altitude `he`. -/
lemma bandPeakAltitude_of_gt {ρ0 H β γ hmin he : ℝ} (hband : hmin < he)
    (hgt : he < peakDecelerationAltitude ρ0 H β γ) :
    bandPeakAltitude ρ0 H β γ hmin he = he := by
  unfold bandPeakAltitude
  rw [min_eq_right (le_of_lt hgt), max_eq_right (le_of_lt hband)]

/-- Peak deceleration on the finite entry band: for `ρ0, H, β, ve > 0`, `sin γ > 0` and
`hmin < he`, the selected altitude lies in the band and maximizes the deceleration on it. -/
lemma isMaxOn_bandPeakAltitude {ρ0 H β γ ve hmin he : ℝ} (hρ0 : 0 < ρ0) (hH : 0 < H)
    (hβ : 0 < β) (hγ : 0 < Real.sin γ) (hve : 0 < ve) (hband : hmin < he) :
    bandPeakAltitude ρ0 H β γ hmin he ∈ Set.Icc hmin he ∧
      IsMaxOn (ballisticDeceleration ρ0 H β γ he ve) (Set.Icc hmin he)
        (bandPeakAltitude ρ0 H β γ hmin he) := by
  have hmem : bandPeakAltitude ρ0 H β γ hmin he ∈ Set.Icc hmin he :=
    ⟨le_max_left _ _, max_le hband.le (min_le_right _ _)⟩
  refine ⟨hmem, isMaxOn_iff.2 fun x hx => ?_⟩
  rcases lt_or_ge (peakDecelerationAltitude ρ0 H β γ) hmin with h1 | h1
  · rw [bandPeakAltitude_of_lt h1]
    exact (ballisticDeceleration_strictAntiOn hρ0 hH hβ hγ hve he).antitoneOn
      (Set.mem_Ici.2 h1.le) (Set.mem_Ici.2 (h1.le.trans hx.1)) hx.1
  · rcases le_or_gt (peakDecelerationAltitude ρ0 H β γ) he with h2 | h2
    · rw [bandPeakAltitude_of_mem ⟨h1, h2⟩]
      rcases eq_or_ne x (peakDecelerationAltitude ρ0 H β γ) with hx' | hx'
      · rw [hx']
      · exact (ballisticDeceleration_lt_peak hρ0 hH hβ hγ hve he hx').le
    · rw [bandPeakAltitude_of_gt hband h2]
      exact (ballisticDeceleration_strictMonoOn hρ0 hH hβ hγ hve he).monotoneOn
        (Set.mem_Iic.2 (hx.2.trans h2.le)) (Set.mem_Iic.2 h2.le) hx.2

/-- For `ρ0, H, β, ve > 0` and `sin γ > 0` and a nonempty band, `hmin < he`, the selected altitude
is the only maximizer on the band: every other altitude of the band has a strictly smaller
deceleration. -/
lemma ballisticDeceleration_lt_bandPeakAltitude {ρ0 H β γ ve hmin he : ℝ} (hρ0 : 0 < ρ0)
    (hH : 0 < H) (hβ : 0 < β) (hγ : 0 < Real.sin γ) (hve : 0 < ve) (hband : hmin < he) {h : ℝ}
    (hh : h ∈ Set.Icc hmin he) (hne : h ≠ bandPeakAltitude ρ0 H β γ hmin he) :
    ballisticDeceleration ρ0 H β γ he ve h <
      ballisticDeceleration ρ0 H β γ he ve (bandPeakAltitude ρ0 H β γ hmin he) := by
  rcases lt_or_ge (peakDecelerationAltitude ρ0 H β γ) hmin with h1 | h1
  · rw [bandPeakAltitude_of_lt h1] at hne ⊢
    exact ballisticDeceleration_strictAntiOn hρ0 hH hβ hγ hve he (Set.mem_Ici.2 h1.le)
      (Set.mem_Ici.2 (h1.le.trans hh.1)) (lt_of_le_of_ne hh.1 (Ne.symm hne))
  · rcases le_or_gt (peakDecelerationAltitude ρ0 H β γ) he with h2 | h2
    · rw [bandPeakAltitude_of_mem ⟨h1, h2⟩] at hne ⊢
      exact ballisticDeceleration_lt_peak hρ0 hH hβ hγ hve he hne
    · rw [bandPeakAltitude_of_gt hband h2] at hne ⊢
      exact ballisticDeceleration_strictMonoOn hρ0 hH hβ hγ hve he
        (Set.mem_Iic.2 (hh.2.trans h2.le)) (Set.mem_Iic.2 h2.le) (lt_of_le_of_ne hh.2 hne)

end EntryPorts

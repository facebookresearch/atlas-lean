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

import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Entry ports: finite-entry ballistic velocity profile

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
(`omitted_entry_term_ne`). The derivative and equation-of-motion results assume `β > 0` and a
downward path, `sin γ > 0`: at `β = 0` Lean's convention `x / 0 = 0` turns the drag term into
`0`, and at `sin γ = 0` the altitude rate vanishes, so `dv/dh` is undefined. The isothermal
corollary asks the trajectory to stay in a declared altitude band, where the isothermal layer
model holds. Apart from the window condition `t₀ ≤ t₁` and that band, which restrict statements
to their physical regime, each result assumes only the hypotheses its proof uses. The identity
`ballisticVelocity_eq_exp_integral` holds for `H ≠ 0`, all other parameters arbitrary; it is the
integrated drag equation for `β > 0` and `sin γ > 0`.

## ii. Key results

- `EntryPorts.ballisticVelocity_entry`: `v(he) = ve`.
- `EntryPorts.ballisticVelocity_of_ode`: every solution of the altitude and drag equations with
  entry state `(he, ve)` satisfies `v(t) = ballisticVelocity (h(t))` on its window.
- `EntryPorts.hasDerivAt_ballisticVelocity_comp`: conversely, the profile along an altitude
  trajectory with `h' = -v * sin γ` solves the drag equation.
- `EntryPorts.ballisticVelocity_strictMono`: the speed falls as the vehicle descends.
- `EntryPorts.ballisticVelocity_of_ode_isothermalDensity`: the same profile for a trajectory in a
  declared band of the isothermal layer, with `H` its scale height.

## iii. Table of contents

- A. Exponential density and the profile
- B. The equations of motion
- C. Descent and the entry condition
- D. The isothermal layer

## iv. References

- H. J. Allen and A. J. Eggers, *A study of the motion and aerodynamic heating of ballistic
  missiles entering the earth's atmosphere at high supersonic speeds*, NACA Report 1381, 1958
  (straight-line ballistic entry, `v = v_E exp (-ρ0 H exp (-h / H) / (2 β sin γ))` normalized at
  infinite altitude).
- F. J. Regan and S. M. Anandakrishnan, *Dynamics of Atmospheric Re-Entry*, AIAA Education
  Series, 1993 (ballistic entry from a finite entry altitude).
-/

@[expose] public section

namespace EntryPorts

open AircraftPerformance

/-! ## A. Exponential density and the profile -/

/-- Exponential density `ρ(h) = ρ0 * exp (-h / H)` with reference density `ρ0` at `h = 0` and
scale height `H`, height `h` measured upward. -/
noncomputable def exponentialDensity (ρ0 H h : ℝ) : ℝ :=
  ρ0 * Real.exp (-h / H)

/-- Ballistic entry constant `K = ρ0 * H / (2 * β * sin γ)` for ballistic coefficient `β` and
downward flight-path angle `γ`; it is dimensionless. -/
noncomputable def ballisticK (ρ0 H β γ : ℝ) : ℝ :=
  ρ0 * H / (2 * β * Real.sin γ)

/-- Finite-entry ballistic velocity profile
`v(h) = ve * exp (K * (exp (-he / H) - exp (-h / H)))` for entry altitude `he` and entry speed
`ve`. -/
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
over `[he, h]`, by the fundamental theorem of calculus. -/
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
column mass between `he` and `h` divided by `2 * β * sin γ`. The identity of the two formulas
holds for `H ≠ 0`, all other parameters arbitrary; it is the integrated drag equation only for
`β > 0` and `sin γ > 0`, where `2 * β * sin γ ≠ 0` (`hasDerivAt_ballisticVelocity`). -/
lemma ballisticVelocity_eq_exp_integral {H : ℝ} (hH : H ≠ 0) (ρ0 β γ he ve h : ℝ) :
    ballisticVelocity ρ0 H β γ he ve h =
      ve * Real.exp ((∫ s in he..h, exponentialDensity ρ0 H s) / (2 * β * Real.sin γ)) := by
  rw [integral_exponentialDensity hH]
  unfold ballisticVelocity ballisticK
  congr 1
  congr 1
  ring

/-- For `β > 0` and a downward path, `sin γ > 0`, the profile solves the altitude form of the
equations of motion, `dv/dh = ρ(h) * v / (2 * β * sin γ)`. -/
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
/-- Derivation from the equations of motion: for `β > 0` and a downward path, `sin γ > 0`, if on
the window `[t₀, t₁]`, `t₀ ≤ t₁`, the altitude and speed satisfy `h' = -v * sin γ` and
`v' = -ρ(h) * v ^ 2 / (2 * β)` with entry state `h(t₀) = he`, `v(t₀) = ve`, then
`v(t) = ballisticVelocity (h(t))` throughout the window. The proof does not use `t₀ ≤ t₁`; the
hypothesis excludes the empty window, on which the statement says nothing. -/
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

/-- Converse: for `β > 0` and a downward path, `sin γ > 0`, along an altitude trajectory with
`h' = -v * sin γ` for `v = ballisticVelocity ∘ h`, the speed `ballisticVelocity ∘ h` satisfies the
drag equation `v' = -ρ(h) * v ^ 2 / (2 * β)`. -/
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

/-- Descent decelerates: the profile is strictly increasing in altitude, so the speed falls as
the vehicle descends below the entry altitude. -/
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

/-- Infinite-entry normalization is not finite entry data: dropping the `exp (-he / H)` term from
the exponent gives a profile whose value at the entry altitude is not `ve`. -/
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
/-- With the isothermal-layer density `isothermalDensity ρ0 g Rs T` as the atmosphere, `β > 0`, a
downward path and the window `t₀ ≤ t₁`, the derivation gives the same profile with `H` the scale
height `Rs * T / |g|`. The isothermal layer model holds only on a declared altitude band
`[z₁, z₂]`, so the trajectory is required to stay in it on the window. The proof does not use the
band; the hypothesis restricts the statement to the model's regime. -/
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

end EntryPorts

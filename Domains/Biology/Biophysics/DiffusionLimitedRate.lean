/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Tactic.Ring

/-!
# Smoluchowski's steady radial current

Let `D`, `kT` and the contact radius `R` be positive. With no interaction potential, a steady
radial profile `n` has a derivative within `[R, ∞)` and constant inward current `J` at every
`r ≥ R`. If `n(R) = 0` and `n(r) → n₀` at infinity, then `J = 4π D R n₀`. This is Debye's
zero-potential result in terms of the relative diffusivity, before substituting the
Stokes–Einstein diffusivities. The current identity extends to all real bulk values `n₀`,
including zero and negative values; only positive `n₀` is used to interpret `J/n₀` as a
physical rate constant for a nonnegative density.

## References

* P. Debye, *Reaction Rates in Ionic Solutions*, Transactions of The Electrochemical Society
  82 (1942), 265–272, equation (4′) and Appendix (p. 270).
* M. v. Smoluchowski, *Versuch einer mathematischen Theorie der Koagulationskinetik kolloider
  Lösungen*, Zeitschrift für Physikalische Chemie 92, 129–168 (cited as 1917 by Debye;
  publisher metadata dates the volume to 1918).
-/

namespace WantedExt.Biology.Biophysics.DiffusionLimitedRateWanted

open Filter Topology Set

/-- `n` is a **steady radial profile** with current `J` outside the contact distance `R`, for
diffusion coefficient `D`, thermal energy `kT` and potential derivative `U'`: at every
`r ≥ R`, `n` has a derivative `n'(r)` within `[R, ∞)` and
`4π r² D (n'(r) + n(r) U'(r) / kT) = J`. -/
@[expose] public def IsSteadyProfile (D kT R : ℝ) (U' n : ℝ → ℝ) (J : ℝ) : Prop :=
  ∃ n' : ℝ → ℝ, ∀ r, R ≤ r → HasDerivWithinAt n (n' r) (Ici R) r ∧
    4 * Real.pi * r ^ 2 * D * (n' r + n r * U' r / kT) = J

/-- **Smoluchowski's steady radial current** (Smoluchowski 1917; Debye 1942, equation (4′)): for
`D, kT, R > 0`, no interaction (`U = 0`, `U' = 0`), and any real `n₀`, every steady radial
profile `n` with current `J`, `n(R) = 0` and `n(r) → n₀` satisfies `J = 4π D R n₀` (giving
`J = 0` when `n₀ = 0`, and rate constant `k_D = J / n₀ = 4π D R` for a nonnegative density with
positive bulk density `n₀ > 0`).

Source: Debye (1942), equation (4′); Smoluchowski (1917). -/
public theorem current_eq_smoluchowski (D kT R : ℝ) (hD : 0 < D) (hkT : 0 < kT)
    (hR : 0 < R) (n₀ : ℝ) (n : ℝ → ℝ) (J : ℝ)
    (hn : IsSteadyProfile D kT R (fun _ => 0) n J) (hnR : n R = 0)
    (hlim : Tendsto n atTop (𝓝 n₀)) :
    J = 4 * Real.pi * D * R * n₀ := by
  obtain ⟨n', hn'⟩ := hn
  let A : ℝ := 4 * Real.pi * D
  have hA : A ≠ 0 := ne_of_gt (by dsimp [A]; positivity)
  let C : ℝ := J / A
  let g (r : ℝ) : ℝ := C * (R⁻¹ - r⁻¹)
  have hnDeriv (r : ℝ) (hr : r ∈ Ici R) : HasDerivWithinAt n (C / r ^ 2) (Ici R) r := by
    obtain ⟨hd, hcurrent⟩ := hn' r hr
    have hr0 : r ≠ 0 := (hR.trans_le hr).ne'
    have hzero : n r * 0 / kT = 0 := (div_eq_iff hkT.ne').2 (by simp)
    have hscaled : n' r * (A * r ^ 2) = J := by
      calc
        _ = 4 * Real.pi * r ^ 2 * D * (n' r + n r * 0 / kT) := by
          rw [hzero, add_zero]
          dsimp [A]
          ring
        _ = J := hcurrent
    have hvalue : n' r = C / r ^ 2 := by
      dsimp [C]
      rw [div_div]
      exact (eq_div_iff (mul_ne_zero hA (pow_ne_zero 2 hr0))).2 hscaled
    simpa only [hvalue] using hd
  have hgDeriv (r : ℝ) (hr : r ∈ Ici R) : HasDerivWithinAt g (C / r ^ 2) (Ici R) r := by
    have hr0 : r ≠ 0 := (hR.trans_le hr).ne'
    simpa only [g, neg_neg, div_eq_mul_inv] using
      ((hasDerivWithinAt_inv hr0 (Ici R)).const_sub R⁻¹).const_mul C
  have heq : EqOn n g (Ici R) := by
    refine (convex_Ici R).eqOn_of_fderivWithin_eq
      (fun r hr => (hnDeriv r hr).differentiableWithinAt)
      (fun r hr => (hgDeriv r hr).differentiableWithinAt) (uniqueDiffOn_Ici R) ?_ (le_refl R) ?_
    · intro r hr
      have hu := uniqueDiffOn_Ici R r hr
      rw [(hnDeriv r hr).hasFDerivWithinAt.fderivWithin hu,
        (hgDeriv r hr).hasFDerivWithinAt.fderivWithin hu]
    · simp [g, hnR]
  have hglim : Tendsto g atTop (𝓝 (C * R⁻¹)) := by
    simpa [g] using (tendsto_const_nhds.sub tendsto_inv_atTop_zero).const_mul C
  have hlim' : Tendsto g atTop (𝓝 n₀) :=
    hlim.congr' ((eventually_ge_atTop R).mono fun _ hr => heq hr)
  have hbulk : J / (A * R) = n₀ := by
    simpa only [C, ← div_eq_mul_inv, div_div] using tendsto_nhds_unique hglim hlim'
  calc
    J = n₀ * (A * R) := (div_eq_iff (mul_ne_zero hA hR.ne')).1 hbulk
    _ = 4 * Real.pi * D * R * n₀ := mul_comm _ _

end WantedExt.Biology.Biophysics.DiffusionLimitedRateWanted

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import PhyslibExt.Electromagnetism.ConductingPlaneWave

/-!
# Good-conductor skin depth with an explicit relative error

The good-conductor attenuation and skin depth approximate the exact
forward root of the conducting plane wave with a relative error bounded
by the displacement-to-conduction current ratio.

## i. Overview

A homogeneous isotropic conducting medium has absolute permittivity
`epsilon > 0`, permeability `mu > 0` and conductivity `sigma > 0`, and
is driven at angular frequency `omega > 0`. The exact forward root
`gamma = alpha + i * beta` of
`gamma ^ 2 = -omega ^ 2 * mu * epsilon + i * omega * mu * sigma` has
attenuation constant
`alpha = omega * sqrt (mu * epsilon / 2) *
  sqrt (sqrt (1 + (sigma / (omega * epsilon)) ^ 2) - 1)`,
the `attenuationConstant` of
`PhyslibExt.Electromagnetism.ConductingPlaneWave`, and skin depth
`delta = 1 / alpha`.

Put `rho = omega * epsilon / sigma` (`conductionRatio`, the ratio of
displacement to conduction current) and
`alpha0 = sqrt (omega * mu * sigma / 2)` (`goodConductorAttenuation`,
the attenuation with displacement current dropped), with good-conductor
skin depth `delta0 = 1 / alpha0 = sqrt (2 / (omega * mu * sigma))`.
The exact root normalizes to
`alpha / alpha0 = sqrt (sqrt (1 + rho ^ 2) - rho)`, and from this
real algebra the relative error `1 - alpha / alpha0` lies in
`[0, rho]`. For `rho < 1` the skin depth therefore satisfies
`delta0 <= delta <= delta0 / (1 - rho)`. The lower skin-depth bound
holds for every positive conductivity.

The bound `rho` is weak: the error is never equal to `rho`, and is
about `rho / 2` for small `rho`. At `rho = 1` the exact ratio is
`sqrt (sqrt 2 - 1)`, so the good-conductor expression is an
approximation, not an exact identity, while displacement current is
retained. The positive-conductivity hypothesis is needed: at
`sigma = 0` the attenuation vanishes, there is no finite skin depth,
and with total division the error bound fails.

The bounds are also stated for an arbitrary root of the squared
propagation equation with positive imaginary part, which is shown to
be the forward root.

## ii. Key results

- `skinDepthApproximation_error`: the relative attenuation error lies
  in `[0, rho]`, the skin depth lies in `[delta0, delta0 / (1 - rho)]`
  when `rho < 1`, and `delta0 = sqrt (2 / (omega * mu * sigma))`.
- `attenuationConstant_div_goodConductorAttenuation`: the normalized
  exact attenuation `sqrt (sqrt (1 + rho ^ 2) - rho)`.
- `relativeAttenuationError_lt_conductionRatio`: the error bound is
  never attained.
- `forwardRoot_skinDepthApproximation_error`: the same bounds for any
  root of the squared equation with positive imaginary part.
- `conductionRatio_lt_relativeAttenuationError_zero_sigma`: without
  positive conductivity the error bound fails.

## iii. Table of contents

- A. Good-conductor quantities
- B. Normalized exact root and the relative error bound
- C. Skin-depth bounds
- D. Forward roots of the dispersion equation
- E. Weak-bound and zero-conductivity checks

## iv. References

- D. J. Griffiths, *Introduction to Electrodynamics*, 4th ed.,
  Cambridge University Press, 2017, §9.4.1: electromagnetic waves in
  conductors, the exact attenuation constant and its good-conductor
  limit.
- J. D. Jackson, *Classical Electrodynamics*, 3rd ed., Wiley, 1999,
  §8.1: fields at the surface of and within a good conductor and the
  skin depth `sqrt (2 / (mu * omega * sigma))`.
- `PhyslibExt.Electromagnetism.ConductingPlaneWave`, for the exact
  forward root, the attenuation constant and the skin depth.
-/

@[expose] public section

noncomputable section

namespace PhyslibExt.Electromagnetism.SkinDepthApproximation

open PhyslibExt.Electromagnetism.ConductingPlaneWave

/-! ## A. Good-conductor quantities -/

/-- Displacement-to-conduction current ratio `rho = omega * epsilon / sigma`. -/
noncomputable def conductionRatio (epsilon omega sigma : ℝ) : ℝ :=
  omega * epsilon / sigma

/-- Good-conductor attenuation `alpha0 = sqrt (omega * mu * sigma / 2)`. -/
noncomputable def goodConductorAttenuation (mu omega sigma : ℝ) : ℝ :=
  Real.sqrt (omega * mu * sigma / 2)

/-- Good-conductor skin depth `delta0 = 1 / alpha0`. -/
noncomputable def goodConductorSkinDepth (mu omega sigma : ℝ) : ℝ :=
  1 / goodConductorAttenuation mu omega sigma

/-- Relative attenuation error `1 - alpha / alpha0` of the good-conductor
approximation against the exact attenuation root. -/
noncomputable def relativeAttenuationError (epsilon mu omega sigma : ℝ) : ℝ :=
  1 - attenuationConstant epsilon mu omega sigma /
    goodConductorAttenuation mu omega sigma

/-- The current ratio is positive for positive parameters. -/
lemma conductionRatio_pos (epsilon omega sigma : ℝ)
    (hepsilon : 0 < epsilon) (homega : 0 < omega) (hsigma : 0 < sigma) :
    0 < conductionRatio epsilon omega sigma := by
  unfold conductionRatio
  exact div_pos (mul_pos homega hepsilon) hsigma

/-- The good-conductor attenuation is positive for positive parameters. -/
lemma goodConductorAttenuation_pos (mu omega sigma : ℝ)
    (hmu : 0 < mu) (homega : 0 < omega) (hsigma : 0 < sigma) :
    0 < goodConductorAttenuation mu omega sigma := by
  unfold goodConductorAttenuation
  rw [Real.sqrt_pos]
  positivity

/-- `delta0 = sqrt (2 / (omega * mu * sigma))`. -/
lemma goodConductorSkinDepth_eq_sqrt (mu omega sigma : ℝ)
    (hmu : 0 < mu) (homega : 0 < omega) (hsigma : 0 < sigma) :
    goodConductorSkinDepth mu omega sigma =
      Real.sqrt (2 / (omega * mu * sigma)) := by
  have _ : (0 : ℝ) < omega * mu * sigma := mul_pos (mul_pos homega hmu) hsigma
  unfold goodConductorSkinDepth goodConductorAttenuation
  rw [show (2 : ℝ) / (omega * mu * sigma) = 1 / (omega * mu * sigma / 2) by ring,
    Real.sqrt_div zero_le_one, Real.sqrt_one]

/-! ## B. Normalized exact root and the relative error bound -/

/-- Normalization of the exact attenuation root:
`alpha / alpha0 = sqrt (sqrt (1 + rho ^ 2) - rho)`. -/
lemma attenuationConstant_div_goodConductorAttenuation
    (epsilon mu omega sigma : ℝ)
    (hepsilon : 0 < epsilon) (hmu : 0 < mu) (homega : 0 < omega)
    (hsigma : 0 < sigma) :
    attenuationConstant epsilon mu omega sigma /
        goodConductorAttenuation mu omega sigma =
      Real.sqrt (Real.sqrt (1 + conductionRatio epsilon omega sigma ^ 2) -
        conductionRatio epsilon omega sigma) := by
  have hwe : (0 : ℝ) < omega * epsilon := mul_pos homega hepsilon
  have hρ : (0 : ℝ) < omega * epsilon / sigma := div_pos hwe hsigma
  have h1s : (1 : ℝ) ≤ Real.sqrt (1 + (sigma / (omega * epsilon)) ^ 2) :=
    calc (1 : ℝ) = Real.sqrt 1 := Real.sqrt_one.symm
      _ ≤ Real.sqrt (1 + (sigma / (omega * epsilon)) ^ 2) :=
        Real.sqrt_le_sqrt (le_add_of_nonneg_right (sq_nonneg _))
  have hY : (0 : ℝ) ≤ Real.sqrt (1 + (sigma / (omega * epsilon)) ^ 2) - 1 := by
    linarith
  have hα2 : (attenuationConstant epsilon mu omega sigma) ^ 2 =
      omega ^ 2 * (mu * epsilon / 2) *
        (Real.sqrt (1 + (sigma / (omega * epsilon)) ^ 2) - 1) := by
    unfold attenuationConstant
    rw [mul_pow, mul_pow,
      Real.sq_sqrt (show (0 : ℝ) ≤ mu * epsilon / 2 by positivity),
      Real.sq_sqrt hY]
  have hα02 : (goodConductorAttenuation mu omega sigma) ^ 2 =
      omega * mu * sigma / 2 := by
    unfold goodConductorAttenuation
    exact Real.sq_sqrt (show (0 : ℝ) ≤ omega * mu * sigma / 2 by positivity)
  have hsr : (sigma / (omega * epsilon)) * (omega * epsilon / sigma) = 1 := by
    have h1 : (omega * epsilon) * sigma ≠ 0 := ne_of_gt (mul_pos hwe hsigma)
    rw [div_mul_div_comm, mul_comm sigma (omega * epsilon), div_self h1]
  have h2 : (omega * epsilon / sigma) ^ 2 * (sigma / (omega * epsilon)) ^ 2 = 1 := by
    rw [← mul_pow, mul_comm (omega * epsilon / sigma) (sigma / (omega * epsilon)),
      hsr, one_pow]
  have h3 : (omega * epsilon / sigma) ^ 2 * (1 + (sigma / (omega * epsilon)) ^ 2) =
      1 + (omega * epsilon / sigma) ^ 2 := by
    linear_combination h2
  have hρsqrt : (omega * epsilon / sigma) *
      Real.sqrt (1 + (sigma / (omega * epsilon)) ^ 2) =
      Real.sqrt (1 + (omega * epsilon / sigma) ^ 2) :=
    calc (omega * epsilon / sigma) * Real.sqrt (1 + (sigma / (omega * epsilon)) ^ 2)
        = Real.sqrt ((omega * epsilon / sigma) ^ 2) *
          Real.sqrt (1 + (sigma / (omega * epsilon)) ^ 2) := by
          rw [Real.sqrt_sq (le_of_lt hρ)]
      _ = Real.sqrt ((omega * epsilon / sigma) ^ 2 *
          (1 + (sigma / (omega * epsilon)) ^ 2)) :=
          (Real.sqrt_mul (sq_nonneg _) _).symm
      _ = Real.sqrt (1 + (omega * epsilon / sigma) ^ 2) := by rw [h3]
  have h4 : (omega * epsilon / sigma) *
      (Real.sqrt (1 + (sigma / (omega * epsilon)) ^ 2) - 1) =
      Real.sqrt (1 + (omega * epsilon / sigma) ^ 2) -
        (omega * epsilon / sigma) := by
    rw [mul_sub, hρsqrt, mul_one]
  have hfield : ∀ (Y : ℝ), (omega ^ 2 * (mu * epsilon / 2) * Y) /
      (omega * mu * sigma / 2) = (omega * epsilon / sigma) * Y := by
    intro Y
    have hs : sigma ≠ 0 := ne_of_gt hsigma
    have hB : omega * mu * sigma / 2 ≠ 0 :=
      ne_of_gt (show (0 : ℝ) < omega * mu * sigma / 2 by positivity)
    field_simp
  have hdiv2 : (attenuationConstant epsilon mu omega sigma /
      goodConductorAttenuation mu omega sigma) ^ 2 =
      Real.sqrt (1 + conductionRatio epsilon omega sigma ^ 2) -
        conductionRatio epsilon omega sigma := by
    rw [div_pow, hα2, hα02]
    unfold conductionRatio
    rw [hfield, h4]
  have hnn : (0 : ℝ) ≤ attenuationConstant epsilon mu omega sigma /
      goodConductorAttenuation mu omega sigma :=
    div_nonneg (le_of_lt (attenuationConstant_pos_of_sigma_pos epsilon mu omega sigma
      hepsilon hmu homega hsigma))
      (le_of_lt (goodConductorAttenuation_pos mu omega sigma hmu homega hsigma))
  rw [← hdiv2]
  exact (Real.sqrt_sq hnn).symm

/-- Lower bound: the exact attenuation never exceeds the good-conductor
value, `0 <= 1 - alpha / alpha0`. -/
lemma relativeAttenuationError_nonneg (epsilon mu omega sigma : ℝ)
    (hepsilon : 0 < epsilon) (hmu : 0 < mu) (homega : 0 < omega)
    (hsigma : 0 < sigma) :
    0 ≤ relativeAttenuationError epsilon mu omega sigma := by
  have hnorm := attenuationConstant_div_goodConductorAttenuation epsilon mu omega sigma
    hepsilon hmu homega hsigma
  have hr : (0 : ℝ) ≤ conductionRatio epsilon omega sigma :=
    le_of_lt (conductionRatio_pos epsilon omega sigma hepsilon homega hsigma)
  unfold relativeAttenuationError
  rw [hnorm]
  have h1 : Real.sqrt (1 + conductionRatio epsilon omega sigma ^ 2) ≤
      1 + conductionRatio epsilon omega sigma := by
    rw [Real.sqrt_le_iff]
    constructor
    · linarith
    · nlinarith [hr]
  have hle : Real.sqrt (Real.sqrt (1 + conductionRatio epsilon omega sigma ^ 2) -
      conductionRatio epsilon omega sigma) ≤ 1 := by
    rw [Real.sqrt_le_one]
    linarith
  linarith

/-- Upper bound: `1 - alpha / alpha0 <= rho`. -/
lemma relativeAttenuationError_le_conductionRatio
    (epsilon mu omega sigma : ℝ)
    (hepsilon : 0 < epsilon) (hmu : 0 < mu) (homega : 0 < omega)
    (hsigma : 0 < sigma) :
    relativeAttenuationError epsilon mu omega sigma ≤
      conductionRatio epsilon omega sigma := by
  have hnorm := attenuationConstant_div_goodConductorAttenuation epsilon mu omega sigma
    hepsilon hmu homega hsigma
  have hρ : (0 : ℝ) < conductionRatio epsilon omega sigma :=
    conductionRatio_pos epsilon omega sigma hepsilon homega hsigma
  unfold relativeAttenuationError
  rw [hnorm]
  suffices hmain : (1 : ℝ) - conductionRatio epsilon omega sigma ≤
      Real.sqrt (Real.sqrt (1 + conductionRatio epsilon omega sigma ^ 2) -
        conductionRatio epsilon omega sigma) by
    linarith
  rcases lt_or_ge (conductionRatio epsilon omega sigma) 1 with h1 | h1
  · have hnn1 : (0 : ℝ) ≤ 1 - conductionRatio epsilon omega sigma := by linarith
    have hlt : (conductionRatio epsilon omega sigma) ^ 2 <
        1 + (conductionRatio epsilon omega sigma) ^ 2 := by linarith
    have hle : conductionRatio epsilon omega sigma ≤
        Real.sqrt (1 + conductionRatio epsilon omega sigma ^ 2) :=
      calc conductionRatio epsilon omega sigma
          ≤ |conductionRatio epsilon omega sigma| := le_abs_self _
        _ = Real.sqrt ((conductionRatio epsilon omega sigma) ^ 2) :=
          (Real.sqrt_sq_eq_abs _).symm
        _ ≤ Real.sqrt (1 + (conductionRatio epsilon omega sigma) ^ 2) :=
          le_of_lt (Real.sqrt_lt_sqrt (sq_nonneg _) hlt)
    have hX : (0 : ℝ) ≤ Real.sqrt (1 + conductionRatio epsilon omega sigma ^ 2) -
        conductionRatio epsilon omega sigma := by linarith
    rw [Real.le_sqrt hnn1 hX]
    have hnn2 : (0 : ℝ) ≤ (1 - conductionRatio epsilon omega sigma) ^ 2 +
        conductionRatio epsilon omega sigma :=
      add_nonneg (sq_nonneg _) (le_of_lt hρ)
    have hY : (0 : ℝ) ≤ (1 : ℝ) + conductionRatio epsilon omega sigma ^ 2 := by
      positivity
    have hiff : ((1 - conductionRatio epsilon omega sigma) ^ 2 ≤
        Real.sqrt (1 + conductionRatio epsilon omega sigma ^ 2) -
          conductionRatio epsilon omega sigma) ↔
        ((1 - conductionRatio epsilon omega sigma) ^ 2 +
          conductionRatio epsilon omega sigma ≤
          Real.sqrt (1 + conductionRatio epsilon omega sigma ^ 2)) := by
      constructor <;> intro h <;> linarith
    rw [hiff, Real.le_sqrt hnn2 hY]
    have hr1 : (0 : ℝ) ≤ 1 - conductionRatio epsilon omega sigma := by linarith
    have hr2 : (0 : ℝ) ≤ 2 - conductionRatio epsilon omega sigma := by linarith
    have e1 : (0 : ℝ) ≤ 2 * conductionRatio epsilon omega sigma *
        (1 - conductionRatio epsilon omega sigma) :=
      mul_nonneg (mul_nonneg (by norm_num) (le_of_lt hρ)) hr1
    have e2 : (0 : ℝ) ≤ (conductionRatio epsilon omega sigma) ^ 3 *
        (2 - conductionRatio epsilon omega sigma) :=
      mul_nonneg (pow_nonneg (le_of_lt hρ) 3) hr2
    linear_combination e1 + e2
  · calc (1 : ℝ) - conductionRatio epsilon omega sigma ≤ 0 := by linarith
      _ ≤ Real.sqrt (Real.sqrt (1 + conductionRatio epsilon omega sigma ^ 2) -
          conductionRatio epsilon omega sigma) := Real.sqrt_nonneg _

/-- The upper bound is never attained: `1 - alpha / alpha0 < rho` for
every positive conductivity, so `rho` is a weak bound. -/
lemma relativeAttenuationError_lt_conductionRatio
    (epsilon mu omega sigma : ℝ)
    (hepsilon : 0 < epsilon) (hmu : 0 < mu) (homega : 0 < omega)
    (hsigma : 0 < sigma) :
    relativeAttenuationError epsilon mu omega sigma <
      conductionRatio epsilon omega sigma := by
  have hnorm := attenuationConstant_div_goodConductorAttenuation epsilon mu omega sigma
    hepsilon hmu homega hsigma
  have hρ : (0 : ℝ) < conductionRatio epsilon omega sigma :=
    conductionRatio_pos epsilon omega sigma hepsilon homega hsigma
  unfold relativeAttenuationError
  rw [hnorm]
  suffices hmain : (1 : ℝ) - conductionRatio epsilon omega sigma <
      Real.sqrt (Real.sqrt (1 + conductionRatio epsilon omega sigma ^ 2) -
        conductionRatio epsilon omega sigma) by
    linarith
  have hlt : (conductionRatio epsilon omega sigma) ^ 2 <
      1 + (conductionRatio epsilon omega sigma) ^ 2 := by linarith
  have hsqrtlt : conductionRatio epsilon omega sigma <
      Real.sqrt (1 + conductionRatio epsilon omega sigma ^ 2) :=
    calc conductionRatio epsilon omega sigma
        ≤ |conductionRatio epsilon omega sigma| := le_abs_self _
      _ = Real.sqrt ((conductionRatio epsilon omega sigma) ^ 2) :=
        (Real.sqrt_sq_eq_abs _).symm
      _ < Real.sqrt (1 + (conductionRatio epsilon omega sigma) ^ 2) :=
        Real.sqrt_lt_sqrt (sq_nonneg _) hlt
  rcases lt_or_ge (conductionRatio epsilon omega sigma) 1 with h1 | h1
  · have hnn1 : (0 : ℝ) ≤ 1 - conductionRatio epsilon omega sigma := by linarith
    rw [Real.lt_sqrt hnn1]
    have hnn2 : (0 : ℝ) ≤ (1 - conductionRatio epsilon omega sigma) ^ 2 +
        conductionRatio epsilon omega sigma :=
      add_nonneg (sq_nonneg _) (le_of_lt hρ)
    have hiff : ((1 - conductionRatio epsilon omega sigma) ^ 2 <
        Real.sqrt (1 + conductionRatio epsilon omega sigma ^ 2) -
          conductionRatio epsilon omega sigma) ↔
        ((1 - conductionRatio epsilon omega sigma) ^ 2 +
          conductionRatio epsilon omega sigma <
          Real.sqrt (1 + conductionRatio epsilon omega sigma ^ 2)) := by
      constructor <;> intro h <;> linarith
    rw [hiff, Real.lt_sqrt hnn2]
    have hr1 : (0 : ℝ) < 1 - conductionRatio epsilon omega sigma := by linarith
    have hr2 : (0 : ℝ) ≤ 2 - conductionRatio epsilon omega sigma := by linarith
    have e1 : (0 : ℝ) < 2 * conductionRatio epsilon omega sigma *
        (1 - conductionRatio epsilon omega sigma) :=
      mul_pos (mul_pos (by norm_num) hρ) hr1
    have e2 : (0 : ℝ) ≤ (conductionRatio epsilon omega sigma) ^ 3 *
        (2 - conductionRatio epsilon omega sigma) :=
      mul_nonneg (pow_nonneg (le_of_lt hρ) 3) hr2
    linear_combination e1 + e2
  · have hX : (0 : ℝ) < Real.sqrt (1 + conductionRatio epsilon omega sigma ^ 2) -
        conductionRatio epsilon omega sigma := by linarith
    calc (1 : ℝ) - conductionRatio epsilon omega sigma ≤ 0 := by linarith
      _ < Real.sqrt (Real.sqrt (1 + conductionRatio epsilon omega sigma ^ 2) -
          conductionRatio epsilon omega sigma) := Real.sqrt_pos.mpr hX

/-! ## C. Skin-depth bounds -/

/-- `delta0 <= delta` for every positive conductivity. -/
lemma goodConductorSkinDepth_le_skinDepth (epsilon mu omega sigma : ℝ)
    (hepsilon : 0 < epsilon) (hmu : 0 < mu) (homega : 0 < omega)
    (hsigma : 0 < sigma) :
    goodConductorSkinDepth mu omega sigma ≤ skinDepth epsilon mu omega sigma := by
  have hα0 : (0 : ℝ) < goodConductorAttenuation mu omega sigma :=
    goodConductorAttenuation_pos mu omega sigma hmu homega hsigma
  have hα : (0 : ℝ) < attenuationConstant epsilon mu omega sigma :=
    attenuationConstant_pos_of_sigma_pos epsilon mu omega sigma
      hepsilon hmu homega hsigma
  have herr := relativeAttenuationError_nonneg epsilon mu omega sigma
    hepsilon hmu homega hsigma
  unfold relativeAttenuationError at herr
  have hle : attenuationConstant epsilon mu omega sigma ≤
      goodConductorAttenuation mu omega sigma := by
    have h1 : attenuationConstant epsilon mu omega sigma /
        goodConductorAttenuation mu omega sigma ≤ 1 := by linarith
    exact (div_le_one hα0).mp h1
  unfold goodConductorSkinDepth skinDepth
  exact one_div_le_one_div_of_le hα hle

/-- `delta <= delta0 / (1 - rho)` when `rho < 1`. -/
lemma skinDepth_le_goodConductorSkinDepth_div (epsilon mu omega sigma : ℝ)
    (hepsilon : 0 < epsilon) (hmu : 0 < mu) (homega : 0 < omega)
    (hsigma : 0 < sigma) (hrho : conductionRatio epsilon omega sigma < 1) :
    skinDepth epsilon mu omega sigma ≤
      goodConductorSkinDepth mu omega sigma /
        (1 - conductionRatio epsilon omega sigma) := by
  have hα0 : (0 : ℝ) < goodConductorAttenuation mu omega sigma :=
    goodConductorAttenuation_pos mu omega sigma hmu homega hsigma
  have hα : (0 : ℝ) < attenuationConstant epsilon mu omega sigma :=
    attenuationConstant_pos_of_sigma_pos epsilon mu omega sigma
      hepsilon hmu homega hsigma
  have herr := relativeAttenuationError_le_conductionRatio epsilon mu omega sigma
    hepsilon hmu homega hsigma
  unfold relativeAttenuationError at herr
  have h1ρ : (0 : ℝ) < 1 - conductionRatio epsilon omega sigma := by linarith
  have hle : (1 - conductionRatio epsilon omega sigma) *
      goodConductorAttenuation mu omega sigma ≤
      attenuationConstant epsilon mu omega sigma := by
    have h1 : 1 - conductionRatio epsilon omega sigma ≤
        attenuationConstant epsilon mu omega sigma /
          goodConductorAttenuation mu omega sigma := by linarith
    exact (le_div_iff₀ hα0).mp h1
  unfold skinDepth goodConductorSkinDepth
  rw [div_div]
  exact one_div_le_one_div_of_le (mul_pos hα0 h1ρ) (by linarith [hle])

/-- Headline: the relative attenuation error of the good-conductor
approximation lies in `[0, rho]`; for `0 <= rho < 1` the exact skin
depth lies in `[delta0, delta0 / (1 - rho)]`; and
`delta0 = sqrt (2 / (omega * mu * sigma))`. -/
lemma skinDepthApproximation_error (epsilon mu omega sigma : ℝ)
    (hepsilon : 0 < epsilon) (hmu : 0 < mu) (homega : 0 < omega)
    (hsigma : 0 < sigma) :
    0 ≤ relativeAttenuationError epsilon mu omega sigma ∧
      relativeAttenuationError epsilon mu omega sigma ≤
        conductionRatio epsilon omega sigma ∧
      (0 ≤ conductionRatio epsilon omega sigma →
        conductionRatio epsilon omega sigma < 1 →
          goodConductorSkinDepth mu omega sigma ≤ skinDepth epsilon mu omega sigma ∧
            skinDepth epsilon mu omega sigma ≤
              goodConductorSkinDepth mu omega sigma /
                (1 - conductionRatio epsilon omega sigma)) ∧
      goodConductorSkinDepth mu omega sigma =
        Real.sqrt (2 / (omega * mu * sigma)) := by
  refine ⟨relativeAttenuationError_nonneg epsilon mu omega sigma
      hepsilon hmu homega hsigma,
    relativeAttenuationError_le_conductionRatio epsilon mu omega sigma
      hepsilon hmu homega hsigma,
    ?_, goodConductorSkinDepth_eq_sqrt mu omega sigma hmu homega hsigma⟩
  intro _ h1
  exact ⟨goodConductorSkinDepth_le_skinDepth epsilon mu omega sigma
      hepsilon hmu homega hsigma,
    skinDepth_le_goodConductorSkinDepth_div epsilon mu omega sigma
      hepsilon hmu homega hsigma h1⟩

/-! ## D. Forward roots of the dispersion equation -/

/-- Any root of the squared propagation equation with positive imaginary
part is the forward root, so its real part is the attenuation constant. -/
lemma forwardRoot_re_eq_attenuationConstant (epsilon mu omega sigma : ℝ)
    (hepsilon : 0 < epsilon) (hmu : 0 < mu) (homega : 0 < omega)
    (hsigma : 0 ≤ sigma) (gamma : ℂ)
    (hgamma : satisfiesDispersionEquation epsilon mu omega sigma gamma)
    (him : 0 < gamma.im) :
    gamma.re = attenuationConstant epsilon mu omega sigma := by
  have hprop := dispersion_verification epsilon mu omega sigma
    hepsilon hmu homega hsigma
  obtain ⟨hprop_eq, -, hβ_pos⟩ := hprop
  have hre : (propagationConstant epsilon mu omega sigma).re =
      attenuationConstant epsilon mu omega sigma := by
    simp [propagationConstant]
  have him' : (propagationConstant epsilon mu omega sigma).im =
      phaseConstant epsilon mu omega sigma := by
    simp [propagationConstant]
  have hsq : gamma ^ 2 = (propagationConstant epsilon mu omega sigma) ^ 2 := by
    unfold satisfiesDispersionEquation at hgamma hprop_eq
    rw [hgamma, hprop_eq]
  have hfactor : (gamma + propagationConstant epsilon mu omega sigma) *
      (gamma - propagationConstant epsilon mu omega sigma) = 0 := by
    have h : gamma ^ 2 - (propagationConstant epsilon mu omega sigma) ^ 2 = 0 := by
      rw [hsq, sub_self]
    rwa [sq_sub_sq] at h
  rcases mul_eq_zero.mp hfactor with hsum | hdiff
  · have hneg : gamma = -propagationConstant epsilon mu omega sigma :=
      eq_neg_of_add_eq_zero_left hsum
    exfalso
    have h1 : gamma.im = -(phaseConstant epsilon mu omega sigma) := by
      rw [hneg, Complex.neg_im, him']
    linarith
  · have heq : gamma = propagationConstant epsilon mu omega sigma :=
      sub_eq_zero.mp hdiff
    rw [heq]
    exact hre

/-- The headline bounds stated for an arbitrary forward root `gamma` of
the squared propagation equation, with `alpha = gamma.re` and
`delta = 1 / gamma.re`. -/
lemma forwardRoot_skinDepthApproximation_error (epsilon mu omega sigma : ℝ)
    (hepsilon : 0 < epsilon) (hmu : 0 < mu) (homega : 0 < omega)
    (hsigma : 0 < sigma) (gamma : ℂ)
    (hgamma : satisfiesDispersionEquation epsilon mu omega sigma gamma)
    (him : 0 < gamma.im) :
    0 ≤ 1 - gamma.re / goodConductorAttenuation mu omega sigma ∧
      1 - gamma.re / goodConductorAttenuation mu omega sigma ≤
        conductionRatio epsilon omega sigma ∧
      (0 ≤ conductionRatio epsilon omega sigma →
        conductionRatio epsilon omega sigma < 1 →
          goodConductorSkinDepth mu omega sigma ≤ 1 / gamma.re ∧
            1 / gamma.re ≤
              goodConductorSkinDepth mu omega sigma /
                (1 - conductionRatio epsilon omega sigma)) := by
  have hγ := forwardRoot_re_eq_attenuationConstant epsilon mu omega sigma
    hepsilon hmu homega (le_of_lt hsigma) gamma hgamma him
  rw [hγ]
  refine ⟨relativeAttenuationError_nonneg epsilon mu omega sigma
      hepsilon hmu homega hsigma,
    relativeAttenuationError_le_conductionRatio epsilon mu omega sigma
      hepsilon hmu homega hsigma,
    ?_⟩
  intro _ h1
  exact ⟨goodConductorSkinDepth_le_skinDepth epsilon mu omega sigma
      hepsilon hmu homega hsigma,
    skinDepth_le_goodConductorSkinDepth_div epsilon mu omega sigma
      hepsilon hmu homega hsigma h1⟩

/-! ## E. Weak-bound and zero-conductivity checks -/

/-- At `rho = 1` (that is, `sigma = omega * epsilon`) the exact ratio is
`alpha / alpha0 = sqrt (sqrt 2 - 1)`, about `0.644`; the relative error
`0.356` is well inside the bound `rho = 1`. -/
lemma attenuation_ratio_at_unit_conductionRatio (epsilon mu omega : ℝ)
    (hepsilon : 0 < epsilon) (hmu : 0 < mu) (homega : 0 < omega) :
    attenuationConstant epsilon mu omega (omega * epsilon) /
        goodConductorAttenuation mu omega (omega * epsilon) =
      Real.sqrt (Real.sqrt 2 - 1) := by
  have hnorm := attenuationConstant_div_goodConductorAttenuation epsilon mu omega
    (omega * epsilon) hepsilon hmu homega (mul_pos homega hepsilon)
  have hrho : conductionRatio epsilon omega (omega * epsilon) = 1 := by
    unfold conductionRatio
    exact div_self (ne_of_gt (mul_pos homega hepsilon))
  have h12 : (1 : ℝ) + 1 ^ 2 = 2 := by norm_num
  rw [hnorm, hrho, h12]

/-- At `sigma = 0` there is no finite skin depth: the attenuation is zero,
so `alpha * delta` is not `1`. -/
lemma attenuationConstant_mul_skinDepth_zero_sigma (epsilon mu omega : ℝ)
    (hepsilon : 0 < epsilon) (hmu : 0 < mu) (homega : 0 < omega) :
    attenuationConstant epsilon mu omega 0 * skinDepth epsilon mu omega 0 ≠ 1 := by
  have h0 := attenuationConstant_zero_sigma epsilon mu omega hepsilon hmu homega
  unfold skinDepth
  rw [h0]
  simp

/-- Violated premise: at `sigma = 0` the error bound fails for the
library's total division, since the ratio is `0` and the relative error
is `1`. The positive-conductivity hypothesis is therefore needed. -/
lemma conductionRatio_lt_relativeAttenuationError_zero_sigma
    (epsilon mu omega : ℝ)
    (hepsilon : 0 < epsilon) (hmu : 0 < mu) (homega : 0 < omega) :
    conductionRatio epsilon omega 0 < relativeAttenuationError epsilon mu omega 0 := by
  have h0 := attenuationConstant_zero_sigma epsilon mu omega hepsilon hmu homega
  unfold conductionRatio relativeAttenuationError
  rw [h0]
  simp

end PhyslibExt.Electromagnetism.SkinDepthApproximation

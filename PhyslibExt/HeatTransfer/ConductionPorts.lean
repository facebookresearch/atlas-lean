/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Tactic.Ring

/-!
# Heat conduction ports: quadratic energy identity with boundary work

## i. Overview

For a temperature field satisfying `u_t = D * u_xx + src` on
`[0, L]`, the quadratic energy `E(t) = ∫₀ᴸ u(t, x)^2 / 2 dx` obeys
an identity with three contributions: the diffusion contribution
`-D * ∫₀ᴸ u_x^2 dx` (a dissipation when `0 ≤ D`), boundary work
`D * (u(t, L) * u_x(t, L) - u(t, 0) * u_x(t, 0))`, and the source
power `∫₀ᴸ u * src dx`. The boundary terms are retained explicitly:
they are the outward Robin/Neumann work at the two ends, not
discarded. The zero-Dirichlet specialization recovers the familiar
dissipation-plus-source form.

This quadratic functional is a mathematical energy for the linear
model; it is not claimed to be thermodynamic stored energy.

## ii. Key results

- `ConductionPorts.heatEnergy_hasDerivAt`: the full identity with
  explicit boundary work at one time `t`, under the stated
  pointwise one-time assumptions: `ut` is the actual time
  derivative, the spatial derivatives are given in `HasDerivAt`
  form on `[0, L]`, and the differentiation under the integral is
  the `HasDerivAt` hypothesis `hE` (no joint `ContDiff` hypothesis
  is declared or needed).
- `ConductionPorts.heatEnergy_hasDerivAt_zeroDirichlet`: under
  `u(t, 0) = u(t, L) = 0` the boundary work vanishes.
- `ConductionPorts.diffusion_contribution_nonpos`: the diffusion
  contribution `-D * ∫₀ᴸ u_x^2` is nonpositive when `0 ≤ D`.

## iii. Table of contents

- A. The quadratic energy identity

## iv. References

- The calculation is the standard multiplier-by-`u` energy argument
  for the linear heat equation; the statement is self-contained.

## A. The quadratic energy identity

-/

@[expose] public section

namespace ConductionPorts

/-- Quadratic heat-energy identity with explicit boundary work, at
one time `t`: for a temperature field `u` with actual time
derivative `ut`, spatial derivatives `ux`, `uxx` in `HasDerivAt`
form on `Set.uIcc 0 L` (`0 ≤ L`), satisfying
`ut t x = D * uxx t x + src t x` there, the energy
`E(τ) = ∫₀ᴸ u(τ, x)^2 / 2 dx` has derivative at `t` equal to
`-D * ∫₀ᴸ ux^2 dx + D * (u(t, L) * ux(t, L) - u(t, 0) * ux(t, 0))
+ ∫₀ᴸ u * src dx`. The boundary terms are retained, not discarded.
All hypotheses are scoped to the single time `t` and the interval
`[0, L]`. The hypothesis `hE` is the differentiation under the
integral, as a `HasDerivAt` for the energy itself; `ut` is
required to be the actual time derivative (`hut`). No joint
regularity hypothesis is declared: the assumptions are exactly
the pointwise derivative and continuity data at this `t`. The integration by parts is proved
from the stated derivative and continuity data. The first term is
the diffusion contribution; it is a dissipation only when
`0 ≤ D` (see `diffusion_contribution_nonpos`). -/
theorem heatEnergy_hasDerivAt {D L : ℝ} (hL : 0 ≤ L)
    {u ut ux uxx src : ℝ → ℝ → ℝ} {t : ℝ}
    (hut : ∀ x ∈ Set.uIcc 0 L, HasDerivAt (fun τ : ℝ => u τ x) (ut t x) t)
    (hux : ∀ x ∈ Set.uIcc 0 L, HasDerivAt (fun y : ℝ => u t y) (ux t x) x)
    (huxx : ∀ x ∈ Set.uIcc 0 L, HasDerivAt (fun y : ℝ => ux t y) (uxx t x) x)
    (hPDE : ∀ x ∈ Set.uIcc 0 L, ut t x = D * uxx t x + src t x)
    (hcont_u : ContinuousOn (fun x : ℝ => u t x) (Set.Icc 0 L))
    (hcont_ux : ContinuousOn (fun x : ℝ => ux t x) (Set.Icc 0 L))
    (hcont_uxx : ContinuousOn (fun x : ℝ => uxx t x) (Set.Icc 0 L))
    (hE : HasDerivAt (fun τ : ℝ => ∫ x in (0 : ℝ)..L, u τ x ^ 2 / 2)
      (∫ x in (0 : ℝ)..L, u t x * ut t x) t)
    (hint : IntervalIntegrable (fun x : ℝ => u t x * ut t x)
      MeasureTheory.volume 0 L) :
    HasDerivAt (fun τ : ℝ => ∫ x in (0 : ℝ)..L, u τ x ^ 2 / 2)
      (-D * (∫ x in (0 : ℝ)..L, ux t x ^ 2) +
        D * (u t L * ux t L - u t 0 * ux t 0) +
          ∫ x in (0 : ℝ)..L, u t x * src t x) t := by
  have _ := hut
  have hux_int : IntervalIntegrable (fun x : ℝ => ux t x) MeasureTheory.volume 0 L :=
    hcont_ux.intervalIntegrable_of_Icc hL
  have huxx_int : IntervalIntegrable (fun x : ℝ => uxx t x) MeasureTheory.volume 0 L :=
    hcont_uxx.intervalIntegrable_of_Icc hL
  have hIBP : (∫ x in (0 : ℝ)..L, u t x * uxx t x)
      = u t L * ux t L - u t 0 * ux t 0 - ∫ x in (0 : ℝ)..L, ux t x * ux t x :=
    intervalIntegral.integral_mul_deriv_eq_deriv_mul hux huxx hux_int huxx_int
  have hcont_u_uxx : ContinuousOn (fun x : ℝ => u t x * uxx t x) (Set.Icc 0 L) :=
    hcont_u.mul hcont_uxx
  have hu_uxx_int : IntervalIntegrable (fun x : ℝ => u t x * uxx t x)
      MeasureTheory.volume 0 L :=
    hcont_u_uxx.intervalIntegrable_of_Icc hL
  have hD_int : IntervalIntegrable (fun x : ℝ => D * (u t x * uxx t x))
      MeasureTheory.volume 0 L :=
    hu_uxx_int.const_mul D
  have hsub : Set.uIoc (0 : ℝ) L ⊆ Set.uIcc 0 L := by
    rw [Set.uIoc_of_le hL, Set.uIcc_of_le hL]
    exact Set.Ioc_subset_Icc_self
  have hEqSrc : Set.EqOn (fun x : ℝ => u t x * ut t x - D * (u t x * uxx t x))
      (fun x : ℝ => u t x * src t x) (Set.uIoc 0 L) := by
    apply Set.EqOn.mono hsub
    intro x hx
    show u t x * ut t x - D * (u t x * uxx t x) = u t x * src t x
    rw [hPDE x hx]
    ring
  have hsrc_int : IntervalIntegrable (fun x : ℝ => u t x * src t x)
      MeasureTheory.volume 0 L :=
    IntervalIntegrable.congr hEqSrc (hint.sub hD_int)
  have hEqAdd : Set.EqOn (fun x : ℝ => u t x * ut t x)
      (fun x : ℝ => D * (u t x * uxx t x) + u t x * src t x) (Set.uIcc 0 L) := by
    intro x hx
    show u t x * ut t x = D * (u t x * uxx t x) + u t x * src t x
    rw [hPDE x hx]
    ring
  have hIntEq : (∫ x in (0 : ℝ)..L, u t x * ut t x)
      = D * (∫ x in (0 : ℝ)..L, u t x * uxx t x)
        + ∫ x in (0 : ℝ)..L, u t x * src t x :=
    calc (∫ x in (0 : ℝ)..L, u t x * ut t x)
        = ∫ x in (0 : ℝ)..L, (D * (u t x * uxx t x) + u t x * src t x) :=
          intervalIntegral.integral_congr hEqAdd
      _ = (∫ x in (0 : ℝ)..L, D * (u t x * uxx t x))
          + ∫ x in (0 : ℝ)..L, u t x * src t x :=
          intervalIntegral.integral_add hD_int hsrc_int
      _ = D * (∫ x in (0 : ℝ)..L, u t x * uxx t x)
          + ∫ x in (0 : ℝ)..L, u t x * src t x := by
          rw [intervalIntegral.integral_const_mul]
  have hsq : (∫ x in (0 : ℝ)..L, ux t x * ux t x)
      = ∫ x in (0 : ℝ)..L, ux t x ^ 2 := by
    simp only [pow_two]
  have hval : (∫ x in (0 : ℝ)..L, u t x * ut t x)
      = -D * (∫ x in (0 : ℝ)..L, ux t x ^ 2) +
        D * (u t L * ux t L - u t 0 * ux t 0) +
          ∫ x in (0 : ℝ)..L, u t x * src t x := by
    rw [hIntEq, hIBP, hsq]
    ring
  rw [hval] at hE
  exact hE

/-- Zero-Dirichlet specialization at one time `t`: if additionally
`u t 0 = 0` and `u t L = 0`, the boundary work vanishes and the
energy derivative is the diffusion-plus-source form. -/
theorem heatEnergy_hasDerivAt_zeroDirichlet {D L : ℝ} (hL : 0 ≤ L)
    {u ut ux uxx src : ℝ → ℝ → ℝ} {t : ℝ}
    (hut : ∀ x ∈ Set.uIcc 0 L, HasDerivAt (fun τ : ℝ => u τ x) (ut t x) t)
    (hux : ∀ x ∈ Set.uIcc 0 L, HasDerivAt (fun y : ℝ => u t y) (ux t x) x)
    (huxx : ∀ x ∈ Set.uIcc 0 L, HasDerivAt (fun y : ℝ => ux t y) (uxx t x) x)
    (hPDE : ∀ x ∈ Set.uIcc 0 L, ut t x = D * uxx t x + src t x)
    (hcont_u : ContinuousOn (fun x : ℝ => u t x) (Set.Icc 0 L))
    (hcont_ux : ContinuousOn (fun x : ℝ => ux t x) (Set.Icc 0 L))
    (hcont_uxx : ContinuousOn (fun x : ℝ => uxx t x) (Set.Icc 0 L))
    (hE : HasDerivAt (fun τ : ℝ => ∫ x in (0 : ℝ)..L, u τ x ^ 2 / 2)
      (∫ x in (0 : ℝ)..L, u t x * ut t x) t)
    (hint : IntervalIntegrable (fun x : ℝ => u t x * ut t x)
      MeasureTheory.volume 0 L)
    (hb0 : u t 0 = 0) (hbL : u t L = 0) :
    HasDerivAt (fun τ : ℝ => ∫ x in (0 : ℝ)..L, u τ x ^ 2 / 2)
      (-D * (∫ x in (0 : ℝ)..L, ux t x ^ 2) +
          ∫ x in (0 : ℝ)..L, u t x * src t x) t := by
  have h := heatEnergy_hasDerivAt hL hut hux huxx hPDE hcont_u hcont_ux hcont_uxx hE hint
  have hval : -D * (∫ x in (0 : ℝ)..L, ux t x ^ 2) +
      D * (u t L * ux t L - u t 0 * ux t 0) +
        ∫ x in (0 : ℝ)..L, u t x * src t x
      = -D * (∫ x in (0 : ℝ)..L, ux t x ^ 2) +
        ∫ x in (0 : ℝ)..L, u t x * src t x := by
    rw [hb0, hbL]
    ring
  rw [hval] at h
  exact h

/-- The diffusion contribution is nonpositive when the diffusivity
is nonnegative: `-D * ∫₀ᴸ ux^2 ≤ 0` for `0 ≤ D` and `0 ≤ L`. -/
lemma diffusion_contribution_nonpos {D L : ℝ} (hD : 0 ≤ D) (hL : 0 ≤ L)
    (ux : ℝ → ℝ → ℝ) (t : ℝ)
    (hint : IntervalIntegrable (fun x : ℝ => ux t x ^ 2)
      MeasureTheory.volume 0 L) :
    -D * (∫ x in (0 : ℝ)..L, ux t x ^ 2) ≤ 0 := by
  have hnn : 0 ≤ ∫ x in (0 : ℝ)..L, ux t x ^ 2 :=
    intervalIntegral.integral_nonneg hL (fun x _ => sq_nonneg _)
  exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hD) hnn

end ConductionPorts

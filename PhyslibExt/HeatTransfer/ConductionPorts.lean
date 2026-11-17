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
an identity with three contributions: bulk dissipation
`-D * ∫₀ᴸ u_x^2 dx`, boundary work
`D * (u(t, L) * u_x(t, L) - u(t, 0) * u_x(t, 0))`, and the source
power `∫₀ᴸ u * src dx`. The boundary terms are retained explicitly:
they are the outward Robin/Neumann work at the two ends, not
discarded. The zero-Dirichlet specialization recovers the familiar
dissipation-plus-source form.

This quadratic functional is a mathematical energy for the linear
model; it is not claimed to be thermodynamic stored energy.

## ii. Key results

- `ConductionPorts.heatEnergy_deriv`: the full identity with
  explicit boundary work, for a jointly-`C²` representative (the
  differentiation under the integral is the hypothesis `hswap`;
  the integration by parts is proved from the stated `HasDerivAt`
  and continuity data).
- `ConductionPorts.heatEnergy_deriv_zeroDirichlet`: under
  `u(t, 0) = u(t, L) = 0` the boundary work vanishes.

## iii. Table of contents

- A. The quadratic energy identity

## iv. References

- The calculation is the standard multiplier-by-`u` energy argument
  for the linear heat equation; the statement is self-contained.

## A. The quadratic energy identity

-/

@[expose] public section

namespace ConductionPorts

/-- Quadratic heat-energy identity with explicit boundary work: for
a temperature field `u t x` on `[0, L]` with time derivative `ut`,
spatial derivatives `ux`, `uxx`, satisfying
`ut = D * uxx + src` pointwise, the energy
`E(t) = ∫₀ᴸ u(t, x)^2 / 2 dx` has derivative
`-D * ∫₀ᴸ ux^2 dx + D * (u(t, L) * ux(t, L) - u(t, 0) * ux(t, 0))
+ ∫₀ᴸ u * src dx`. The boundary terms are retained, not discarded.
The hypotheses `hux`, `huxx` give the spatial derivatives in
`HasDerivAt` form and `hcont_u`, `hcont_ux`, `hcont_uxx` the
continuity on `[0, L]` with `0 ≤ L`; `hswap` is the
differentiation-under-the-integral step for the declared
jointly-`C²` representative. The integration by parts is proved
from the stated derivative and continuity data. -/
theorem heatEnergy_deriv {D L : ℝ} {u ut ux uxx src : ℝ → ℝ → ℝ}
    (hL : 0 ≤ L)
    (hux : ∀ t x : ℝ, HasDerivAt (fun y : ℝ => u t y) (ux t x) x)
    (huxx : ∀ t x : ℝ, HasDerivAt (fun y : ℝ => ux t y) (uxx t x) x)
    (hPDE : ∀ t x : ℝ, ut t x = D * uxx t x + src t x)
    (hcont_u : ∀ t : ℝ, ContinuousOn (fun x : ℝ => u t x) (Set.Icc 0 L))
    (hcont_ux : ∀ t : ℝ, ContinuousOn (fun x : ℝ => ux t x) (Set.Icc 0 L))
    (hcont_uxx : ∀ t : ℝ, ContinuousOn (fun x : ℝ => uxx t x) (Set.Icc 0 L))
    (hswap : ∀ t : ℝ,
      deriv (fun τ : ℝ => ∫ x in (0 : ℝ)..L, u τ x ^ 2 / 2) t =
        ∫ x in (0 : ℝ)..L, u t x * ut t x)
    (hint : ∀ t : ℝ, IntervalIntegrable (fun x : ℝ => u t x * ut t x)
      MeasureTheory.volume 0 L)
    (t : ℝ) :
    deriv (fun τ : ℝ => ∫ x in (0 : ℝ)..L, u τ x ^ 2 / 2) t =
      -D * (∫ x in (0 : ℝ)..L, ux t x ^ 2) +
        D * (u t L * ux t L - u t 0 * ux t 0) +
          ∫ x in (0 : ℝ)..L, u t x * src t x := by
  rw [hswap t]
  have hint_ux : IntervalIntegrable (fun x : ℝ => ux t x) MeasureTheory.volume 0 L :=
    (hcont_ux t).intervalIntegrable_of_Icc hL
  have hint_uxx : IntervalIntegrable (fun x : ℝ => uxx t x) MeasureTheory.volume 0 L :=
    (hcont_uxx t).intervalIntegrable_of_Icc hL
  have hint_u_uxx : IntervalIntegrable (fun x : ℝ => u t x * uxx t x)
      MeasureTheory.volume 0 L :=
    ((hcont_u t).mul (hcont_uxx t)).intervalIntegrable_of_Icc hL
  have hint_Duuxx : IntervalIntegrable (fun x : ℝ => D * (u t x * uxx t x))
      MeasureTheory.volume 0 L :=
    hint_u_uxx.const_mul D
  have hsrc_eq : ∀ x : ℝ, u t x * src t x = u t x * ut t x - D * (u t x * uxx t x) := by
    intro x
    rw [hPDE t x]
    ring
  have hEq_src : Set.EqOn (fun x : ℝ => u t x * ut t x - D * (u t x * uxx t x))
      (fun x : ℝ => u t x * src t x) (Set.uIoc 0 L) :=
    fun x _ => (hsrc_eq x).symm
  have hint_u_src : IntervalIntegrable (fun x : ℝ => u t x * src t x)
      MeasureTheory.volume 0 L :=
    IntervalIntegrable.congr hEq_src ((hint t).sub hint_Duuxx)
  have hsplit : ∫ x in (0 : ℝ)..L, u t x * ut t x
      = D * (∫ x in (0 : ℝ)..L, u t x * uxx t x) + ∫ x in (0 : ℝ)..L, u t x * src t x := by
    have heq : Set.EqOn (fun x : ℝ => u t x * ut t x)
        (fun x : ℝ => D * (u t x * uxx t x) + u t x * src t x) (Set.uIcc 0 L) := by
      intro x _
      show u t x * ut t x = D * (u t x * uxx t x) + u t x * src t x
      rw [hPDE t x]
      ring
    calc ∫ x in (0 : ℝ)..L, u t x * ut t x
        = ∫ x in (0 : ℝ)..L, D * (u t x * uxx t x) + u t x * src t x :=
          intervalIntegral.integral_congr heq
      _ = (∫ x in (0 : ℝ)..L, D * (u t x * uxx t x))
          + ∫ x in (0 : ℝ)..L, u t x * src t x :=
          intervalIntegral.integral_add hint_Duuxx hint_u_src
      _ = D * (∫ x in (0 : ℝ)..L, u t x * uxx t x)
          + ∫ x in (0 : ℝ)..L, u t x * src t x := by
          rw [intervalIntegral.integral_const_mul]
  have hibp : ∫ x in (0 : ℝ)..L, u t x * uxx t x
      = u t L * ux t L - u t 0 * ux t 0 - ∫ x in (0 : ℝ)..L, ux t x * ux t x :=
    intervalIntegral.integral_mul_deriv_eq_deriv_mul
      (fun x _ => hux t x) (fun x _ => huxx t x) hint_ux hint_uxx
  have hsq : ∫ x in (0 : ℝ)..L, ux t x ^ 2 = ∫ x in (0 : ℝ)..L, ux t x * ux t x :=
    intervalIntegral.integral_congr (fun x _ => pow_two (ux t x))
  rw [hsplit, hibp, hsq]
  ring

/-- Zero-Dirichlet specialization: if additionally `u t 0 = 0` and
`u t L = 0`, the boundary work vanishes and the identity reduces to
the dissipation-plus-source form. -/
theorem heatEnergy_deriv_zeroDirichlet {D L : ℝ} {u ut ux uxx src : ℝ → ℝ → ℝ}
    (hL : 0 ≤ L)
    (hux : ∀ t x : ℝ, HasDerivAt (fun y : ℝ => u t y) (ux t x) x)
    (huxx : ∀ t x : ℝ, HasDerivAt (fun y : ℝ => ux t y) (uxx t x) x)
    (hPDE : ∀ t x : ℝ, ut t x = D * uxx t x + src t x)
    (hcont_u : ∀ t : ℝ, ContinuousOn (fun x : ℝ => u t x) (Set.Icc 0 L))
    (hcont_ux : ∀ t : ℝ, ContinuousOn (fun x : ℝ => ux t x) (Set.Icc 0 L))
    (hcont_uxx : ∀ t : ℝ, ContinuousOn (fun x : ℝ => uxx t x) (Set.Icc 0 L))
    (hswap : ∀ t : ℝ,
      deriv (fun τ : ℝ => ∫ x in (0 : ℝ)..L, u τ x ^ 2 / 2) t =
        ∫ x in (0 : ℝ)..L, u t x * ut t x)
    (hint : ∀ t : ℝ, IntervalIntegrable (fun x : ℝ => u t x * ut t x)
      MeasureTheory.volume 0 L)
    (hb0 : ∀ t : ℝ, u t 0 = 0) (hbL : ∀ t : ℝ, u t L = 0)
    (t : ℝ) :
    deriv (fun τ : ℝ => ∫ x in (0 : ℝ)..L, u τ x ^ 2 / 2) t =
      -D * (∫ x in (0 : ℝ)..L, ux t x ^ 2) +
          ∫ x in (0 : ℝ)..L, u t x * src t x := by
  have hmain := heatEnergy_deriv hL hux huxx hPDE hcont_u hcont_ux hcont_uxx hswap hint t
  rw [hb0 t, hbL t] at hmain
  exact hmain.trans (by ring)

end ConductionPorts

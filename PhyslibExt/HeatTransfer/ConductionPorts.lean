/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
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
- `ConductionPorts.robinEnergy_hasDerivAt`,
  `ConductionPorts.robinEnergy_deriv_nonpos`: under the outward
  Robin conditions `k * u_x(0) = h0 * θ(0)` and
  `-k * u_x(L) = hL * θ(L)` for `θ = u - Ta`, the boundary work is
  `-(D / k) * (h0 * θ(0)^2 + hL * θ(L)^2)`, so the energy derivative
  is nonpositive for `0 ≤ D`, `0 < k`, `0 ≤ h0`, `0 ≤ hL`.
- `ConductionPorts.robin_uniqueness`: uniqueness for the source-free
  Robin problem by the difference energy.
- `ConductionPorts.robinCosineMode`,
  `ConductionPorts.neumannCosineMode`: nonzero cosine fixtures;
  `ConductionPorts.wrongLeftSign_boundaryInput` and
  `ConductionPorts.negativeH_boundaryInput` show the sign
  conventions are sharp.

## iii. Table of contents

- A. The quadratic energy identity
- B. Outward Robin/Neumann dissipation

## iv. References

- The calculation is the standard multiplier-by-`u` energy argument
  for the linear heat equation; the statement is self-contained.

## A. The quadratic energy identity

## B. Outward Robin/Neumann dissipation

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


/-- Robin energy identity at one time `t`. From the upstream boundary-work identity
for `θ = u - Ta` with no source (`hE`), the outward Robin conditions at `0` and `L`
turn the boundary work into `-(D / k) * (h0 * θ(0)^2 + hL * θ(L)^2)`. -/
theorem robinEnergy_hasDerivAt {D L k h0 hL Ta t : ℝ} (hk : 0 < k)
    {u ux : ℝ → ℝ → ℝ}
    (hBC0 : k * ux t 0 = h0 * (u t 0 - Ta))
    (hBCL : -k * ux t L = hL * (u t L - Ta))
    (hE : HasDerivAt (fun τ : ℝ => ∫ x in (0 : ℝ)..L, (u τ x - Ta) ^ 2 / 2)
      (-D * (∫ x in (0 : ℝ)..L, ux t x ^ 2) +
        D * ((u t L - Ta) * ux t L - (u t 0 - Ta) * ux t 0) +
          ∫ x in (0 : ℝ)..L, (u t x - Ta) * (0 : ℝ)) t) :
    HasDerivAt (fun τ : ℝ => ∫ x in (0 : ℝ)..L, (u τ x - Ta) ^ 2 / 2)
      (-D * (∫ x in (0 : ℝ)..L, ux t x ^ 2) -
        D / k * (h0 * (u t 0 - Ta) ^ 2 + hL * (u t L - Ta) ^ 2)) t := by
  have hk' : k ≠ 0 := hk.ne'
  have hZ : (∫ x in (0 : ℝ)..L, (u t x - Ta) * (0 : ℝ)) = 0 := by simp
  have e0 : ux t 0 = h0 * (u t 0 - Ta) / k := by
    rw [eq_div_iff hk']
    linear_combination hBC0
  have eL : ux t L = -(hL * (u t L - Ta)) / k := by
    rw [eq_div_iff hk']
    linear_combination -hBCL
  have hval : (-D * (∫ x in (0 : ℝ)..L, ux t x ^ 2) -
        D / k * (h0 * (u t 0 - Ta) ^ 2 + hL * (u t L - Ta) ^ 2))
      = (-D * (∫ x in (0 : ℝ)..L, ux t x ^ 2) +
        D * ((u t L - Ta) * ux t L - (u t 0 - Ta) * ux t 0) +
          ∫ x in (0 : ℝ)..L, (u t x - Ta) * (0 : ℝ)) := by
    rw [hZ, e0, eL]
    field_simp
    ring
  rw [hval]
  exact hE

/-- Sign of the Robin energy derivative: for `0 ≤ D`, `0 < k`, `0 ≤ h0`, `0 ≤ hL`
and `0 ≤ L`, the value in `robinEnergy_hasDerivAt` is `≤ 0`. -/
theorem robinEnergy_deriv_nonpos {D L k h0 hL Ta t : ℝ} (hD : 0 ≤ D) (hL0 : 0 ≤ L)
    (hk : 0 < k) (hh0 : 0 ≤ h0) (hhL : 0 ≤ hL) (u ux : ℝ → ℝ → ℝ) :
    -D * (∫ x in (0 : ℝ)..L, ux t x ^ 2) -
        D / k * (h0 * (u t 0 - Ta) ^ 2 + hL * (u t L - Ta) ^ 2) ≤ 0 := by
  have hI : 0 ≤ ∫ x in (0 : ℝ)..L, ux t x ^ 2 :=
    intervalIntegral.integral_nonneg hL0 (fun x _ => sq_nonneg _)
  have hS : 0 ≤ h0 * (u t 0 - Ta) ^ 2 + hL * (u t L - Ta) ^ 2 :=
    add_nonneg (mul_nonneg hh0 (sq_nonneg _)) (mul_nonneg hhL (sq_nonneg _))
  have hDk : 0 ≤ D / k := div_nonneg hD hk.le
  have h1 : -D * (∫ x in (0 : ℝ)..L, ux t x ^ 2) ≤ 0 := by
    have hDI : 0 ≤ D * (∫ x in (0 : ℝ)..L, ux t x ^ 2) := mul_nonneg hD hI
    linarith
  have h2 : 0 ≤ D / k * (h0 * (u t 0 - Ta) ^ 2 + hL * (u t L - Ta) ^ 2) :=
    mul_nonneg hDk hS
  exact sub_nonpos.mpr (le_trans h1 h2)

/-- Uniqueness for the source-free Robin problem on `[0, T] × [0, L]`. Two fields
`u1`, `u2` share `D`, `k`, `h0`, `hL`, `Ta` and satisfy the outward Robin
conditions at every `t ∈ (0, T)`. `hEw` is the upstream heat-energy identity for the difference
`w = u1 - u2` with zero source (its PDE `w_t = D * w_xx` follows from the two
source-free PDEs), at every `t ∈ (0, T)`. The difference energy is continuous on
`[0, T]` (`hEcont`), `w t` is continuous on `[0, L]` for `t ∈ [0, T]` (`hwcont`),
and the initial data agree on `[0, L]`. Then `u1 = u2` on `[0, T] × [0, L]`. -/
theorem robin_uniqueness {D L k h0 hL Ta T : ℝ} (hD : 0 ≤ D) (hL0 : 0 < L)
    (hk : 0 < k) (hh0 : 0 ≤ h0) (hhL : 0 ≤ hL)
    {u1 u2 ux1 ux2 : ℝ → ℝ → ℝ}
    (hBC0₁ : ∀ t ∈ Set.Ioo 0 T, k * ux1 t 0 = h0 * (u1 t 0 - Ta))
    (hBCL₁ : ∀ t ∈ Set.Ioo 0 T, -k * ux1 t L = hL * (u1 t L - Ta))
    (hBC0₂ : ∀ t ∈ Set.Ioo 0 T, k * ux2 t 0 = h0 * (u2 t 0 - Ta))
    (hBCL₂ : ∀ t ∈ Set.Ioo 0 T, -k * ux2 t L = hL * (u2 t L - Ta))
    (hEw : ∀ t ∈ Set.Ioo 0 T,
      HasDerivAt (fun τ : ℝ => ∫ x in (0 : ℝ)..L, (u1 τ x - u2 τ x) ^ 2 / 2)
        (-D * (∫ x in (0 : ℝ)..L, (ux1 t x - ux2 t x) ^ 2) +
          D * ((u1 t L - u2 t L) * (ux1 t L - ux2 t L) -
            (u1 t 0 - u2 t 0) * (ux1 t 0 - ux2 t 0)) +
            ∫ x in (0 : ℝ)..L, (u1 t x - u2 t x) * (0 : ℝ)) t)
    (hEcont : ContinuousOn
      (fun τ : ℝ => ∫ x in (0 : ℝ)..L, (u1 τ x - u2 τ x) ^ 2 / 2) (Set.Icc 0 T))
    (hwcont : ∀ t ∈ Set.Icc 0 T,
      ContinuousOn (fun x : ℝ => u1 t x - u2 t x) (Set.Icc 0 L))
    (hinit : ∀ x ∈ Set.Icc 0 L, u1 0 x = u2 0 x) :
    ∀ t ∈ Set.Icc 0 T, ∀ x ∈ Set.Icc 0 L, u1 t x = u2 t x := by
  by_cases hT : 0 ≤ T
  · have hderiv : ∀ t ∈ Set.Ioo 0 T,
        deriv (fun τ : ℝ => ∫ x in (0 : ℝ)..L, (u1 τ x - u2 τ x) ^ 2 / 2) t ≤ 0 := by
      intro t ht
      have h1 := hBC0₁ t ht
      have h2 := hBCL₁ t ht
      have h3 := hBC0₂ t ht
      have h4 := hBCL₂ t ht
      have hBC0w : k * (ux1 t 0 - ux2 t 0) = h0 * ((u1 t 0 - u2 t 0) - 0) := by
        linear_combination h1 - h3
      have hBCLw : -k * (ux1 t L - ux2 t L) = hL * ((u1 t L - u2 t L) - 0) := by
        linear_combination h2 - h4
      have hE0 : HasDerivAt (fun τ : ℝ => ∫ x in (0 : ℝ)..L, ((u1 τ x - u2 τ x) - 0) ^ 2 / 2)
          (-D * (∫ x in (0 : ℝ)..L, (ux1 t x - ux2 t x) ^ 2) +
            D * (((u1 t L - u2 t L) - 0) * (ux1 t L - ux2 t L) -
              ((u1 t 0 - u2 t 0) - 0) * (ux1 t 0 - ux2 t 0)) +
            ∫ x in (0 : ℝ)..L, ((u1 t x - u2 t x) - 0) * (0 : ℝ)) t := by
        simpa only [sub_zero] using hEw t ht
      have hder := robinEnergy_hasDerivAt (Ta := (0 : ℝ)) hk
        (u := fun τ x => u1 τ x - u2 τ x) (ux := fun τ x => ux1 τ x - ux2 τ x)
        hBC0w hBCLw hE0
      have hderE : HasDerivAt (fun τ : ℝ => ∫ x in (0 : ℝ)..L, (u1 τ x - u2 τ x) ^ 2 / 2)
          (-D * (∫ x in (0 : ℝ)..L, (ux1 t x - ux2 t x) ^ 2) -
            D / k * (h0 * (u1 t 0 - u2 t 0) ^ 2 + hL * (u1 t L - u2 t L) ^ 2)) t := by
        simpa only [sub_zero] using hder
      have hV : (-D * (∫ x in (0 : ℝ)..L, (ux1 t x - ux2 t x) ^ 2) -
          D / k * (h0 * (u1 t 0 - u2 t 0) ^ 2 + hL * (u1 t L - u2 t L) ^ 2)) ≤ 0 := by
        have h := robinEnergy_deriv_nonpos (Ta := (0 : ℝ)) (t := t) hD hL0.le hk hh0 hhL
          (fun τ x => u1 τ x - u2 τ x) (fun τ x => ux1 τ x - ux2 τ x)
        simpa only [sub_zero] using h
      rw [hderE.deriv]
      exact hV
    have hdiff : DifferentiableOn ℝ (fun τ : ℝ => ∫ x in (0 : ℝ)..L, (u1 τ x - u2 τ x) ^ 2 / 2)
        (interior (Set.Icc 0 T)) := by
      rw [interior_Icc]
      intro t ht
      exact ((hEw t ht).differentiableAt).differentiableWithinAt
    have hderiv' : ∀ x ∈ interior (Set.Icc 0 T),
        deriv (fun τ : ℝ => ∫ x in (0 : ℝ)..L, (u1 τ x - u2 τ x) ^ 2 / 2) x ≤ 0 := by
      rw [interior_Icc]
      exact hderiv
    have hanti := antitoneOn_of_deriv_nonpos (convex_Icc 0 T) hEcont hdiff hderiv'
    have hcon : ∀ t ∈ Set.Icc 0 T,
        ContinuousOn (fun x : ℝ => (u1 t x - u2 t x) ^ 2 / 2) (Set.Icc 0 L) := by
      intro t ht
      simpa [pow_two] using ((hwcont t ht).mul (hwcont t ht)).div_const 2
    have hE0 : (fun τ : ℝ => ∫ x in (0 : ℝ)..L, (u1 τ x - u2 τ x) ^ 2 / 2) 0 = 0 := by
      show ∫ x in (0 : ℝ)..L, (u1 0 x - u2 0 x) ^ 2 / 2 = 0
      rw [intervalIntegral.integral_of_le hL0.le]
      apply MeasureTheory.integral_eq_zero_of_ae
      show ∀ᵐ (x : ℝ) ∂(MeasureTheory.volume.restrict (Set.Ioc 0 L)),
        (u1 0 x - u2 0 x) ^ 2 / 2 = 0
      rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioc]
      exact Filter.Eventually.of_forall (fun x hx => by
        have hxIcc : x ∈ Set.Icc 0 L := ⟨le_of_lt hx.1, hx.2⟩
        have h := hinit x hxIcc
        simp [h])
    have hEt0 : ∀ t ∈ Set.Icc 0 T,
        (fun τ : ℝ => ∫ x in (0 : ℝ)..L, (u1 τ x - u2 τ x) ^ 2 / 2) t = 0 := by
      intro t ht
      have h00 : (0 : ℝ) ∈ Set.Icc 0 T := ⟨le_refl 0, hT⟩
      have hle : (fun τ : ℝ => ∫ x in (0 : ℝ)..L, (u1 τ x - u2 τ x) ^ 2 / 2) t
          ≤ (fun τ : ℝ => ∫ x in (0 : ℝ)..L, (u1 τ x - u2 τ x) ^ 2 / 2) 0 :=
        hanti h00 ht ht.1
      have hnn : 0 ≤ (fun τ : ℝ => ∫ x in (0 : ℝ)..L, (u1 τ x - u2 τ x) ^ 2 / 2) t := by
        change 0 ≤ ∫ x in (0 : ℝ)..L, (u1 t x - u2 t x) ^ 2 / 2
        exact intervalIntegral.integral_nonneg hL0.le (fun x _ => by positivity)
      rw [hE0] at hle
      exact le_antisymm hle hnn
    intro t ht x hx
    have hEt := hEt0 t ht
    by_contra hne
    have hne' : u1 t x - u2 t x ≠ 0 := sub_ne_zero.mpr hne
    have hpos : 0 < (u1 t x - u2 t x) ^ 2 / 2 := by positivity
    have hlt : 0 < (fun τ : ℝ => ∫ x in (0 : ℝ)..L, (u1 τ x - u2 τ x) ^ 2 / 2) t :=
      intervalIntegral.integral_pos hL0 (hcon t ht) (fun x _ => by positivity) ⟨x, hx, hpos⟩
    rw [hEt] at hlt
    exact lt_irrefl 0 hlt
  · intro t ht
    have hempty : Set.Icc 0 T = ∅ := Set.Icc_eq_empty hT
    rw [hempty] at ht
    simp at ht

/-! ## Fixtures -/

/-- Robin cosine mode (nonzero fixture). `u t x = Ta + exp (-D * μ^2 * t) *
cos (μ * (x - L / 2))` with `ux` its `x`-derivative solves `u_t = D * u_xx` at
every point, satisfies the outward Robin conditions at both ends with
`h = k * μ * tan (μ * L / 2)`, has `h ≥ 0` when `0 ≤ μ`, `0 ≤ L` and
`μ * L / 2 < π / 2`, and has `θ(t, 0) ≠ 0` there. -/
theorem robinCosineMode {D k μ L Ta : ℝ} (hk : 0 < k) (hμ : 0 ≤ μ) (hL0 : 0 ≤ L)
    (hμL : μ * L / 2 < Real.pi / 2) :
    let u : ℝ → ℝ → ℝ := fun t x => Ta + Real.exp (-D * μ ^ 2 * t) * Real.cos (μ * (x - L / 2))
    let ux : ℝ → ℝ → ℝ := fun t x => -μ * Real.exp (-D * μ ^ 2 * t) * Real.sin (μ * (x - L / 2))
    let ut : ℝ → ℝ → ℝ :=
      fun t x => -D * μ ^ 2 * Real.exp (-D * μ ^ 2 * t) * Real.cos (μ * (x - L / 2))
    let uxx : ℝ → ℝ → ℝ :=
      fun t x => -μ ^ 2 * Real.exp (-D * μ ^ 2 * t) * Real.cos (μ * (x - L / 2))
    let h : ℝ := k * μ * Real.tan (μ * L / 2)
    (∀ t x, HasDerivAt (fun τ => u τ x) (ut t x) t) ∧
    (∀ t x, HasDerivAt (fun y => u t y) (ux t x) x) ∧
    (∀ t x, HasDerivAt (fun y => ux t y) (uxx t x) x) ∧
    (∀ t x, ut t x = D * uxx t x) ∧
    (∀ t, k * ux t 0 = h * (u t 0 - Ta)) ∧
    (∀ t, -k * ux t L = h * (u t L - Ta)) ∧
    0 ≤ h ∧ (∀ t, u t 0 - Ta ≠ 0) := by
  intro u ux ut uxx h
  have hC1pos : 0 < Real.cos (μ * L / 2) := by
    apply Real.cos_pos_of_mem_Ioo
    constructor
    · have hpi : 0 < Real.pi / 2 := by
        have := Real.pi_pos
        linarith
      have hnn : 0 ≤ μ * L / 2 := by positivity
      linarith
    · exact hμL
  have hC1 : Real.cos (μ * L / 2) ≠ 0 := ne_of_gt hC1pos
  have harg0 : μ * (0 - L / 2) = -(μ * L / 2) := by ring
  have hargL : μ * (L - L / 2) = μ * L / 2 := by ring
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro t x
    change HasDerivAt (fun τ : ℝ => Ta + Real.exp (-D * μ ^ 2 * τ) * Real.cos (μ * (x - L / 2)))
      (-D * μ ^ 2 * Real.exp (-D * μ ^ 2 * t) * Real.cos (μ * (x - L / 2))) t
    have hg : HasDerivAt (fun τ : ℝ => -D * μ ^ 2 * τ) (-D * μ ^ 2) t := by
      simpa only [mul_one] using (hasDerivAt_id' t).const_mul (-D * μ ^ 2)
    have hexp : HasDerivAt (fun τ : ℝ => Real.exp (-D * μ ^ 2 * τ))
        (Real.exp (-D * μ ^ 2 * t) * (-D * μ ^ 2)) t :=
      (Real.hasDerivAt_exp _).comp t hg
    have hmul := hexp.mul_const (Real.cos (μ * (x - L / 2)))
    have hfin := hmul.const_add Ta
    have hval : (Real.exp (-D * μ ^ 2 * t) * (-D * μ ^ 2)) * Real.cos (μ * (x - L / 2))
        = -D * μ ^ 2 * Real.exp (-D * μ ^ 2 * t) * Real.cos (μ * (x - L / 2)) := by
      ring
    rwa [hval] at hfin
  · intro t x
    change HasDerivAt (fun y : ℝ => Ta + Real.exp (-D * μ ^ 2 * t) * Real.cos (μ * (y - L / 2)))
      (-μ * Real.exp (-D * μ ^ 2 * t) * Real.sin (μ * (x - L / 2))) x
    have hφ : HasDerivAt (fun y : ℝ => μ * (y - L / 2)) μ x := by
      simpa only [mul_one] using ((hasDerivAt_id' x).sub_const (L / 2)).const_mul μ
    have hcos : HasDerivAt (fun y : ℝ => Real.cos (μ * (y - L / 2)))
        (-Real.sin (μ * (x - L / 2)) * μ) x :=
      (Real.hasDerivAt_cos _).comp x hφ
    have hmul := hcos.const_mul (Real.exp (-D * μ ^ 2 * t))
    have hfin := hmul.const_add Ta
    have hval : Real.exp (-D * μ ^ 2 * t) * (-Real.sin (μ * (x - L / 2)) * μ)
        = -μ * Real.exp (-D * μ ^ 2 * t) * Real.sin (μ * (x - L / 2)) := by
      ring
    rwa [hval] at hfin
  · intro t x
    change HasDerivAt (fun y : ℝ => -μ * Real.exp (-D * μ ^ 2 * t) * Real.sin (μ * (y - L / 2)))
      (-μ ^ 2 * Real.exp (-D * μ ^ 2 * t) * Real.cos (μ * (x - L / 2))) x
    have hφ : HasDerivAt (fun y : ℝ => μ * (y - L / 2)) μ x := by
      simpa only [mul_one] using ((hasDerivAt_id' x).sub_const (L / 2)).const_mul μ
    have hsin : HasDerivAt (fun y : ℝ => Real.sin (μ * (y - L / 2)))
        (Real.cos (μ * (x - L / 2)) * μ) x :=
      (Real.hasDerivAt_sin _).comp x hφ
    have hfin := hsin.const_mul (-μ * Real.exp (-D * μ ^ 2 * t))
    have hval : (-μ * Real.exp (-D * μ ^ 2 * t)) * (Real.cos (μ * (x - L / 2)) * μ)
        = -μ ^ 2 * Real.exp (-D * μ ^ 2 * t) * Real.cos (μ * (x - L / 2)) := by
      ring
    rwa [hval] at hfin
  · intro t x
    change -D * μ ^ 2 * Real.exp (-D * μ ^ 2 * t) * Real.cos (μ * (x - L / 2))
      = D * (-μ ^ 2 * Real.exp (-D * μ ^ 2 * t) * Real.cos (μ * (x - L / 2)))
    ring
  · intro t
    change k * (-μ * Real.exp (-D * μ ^ 2 * t) * Real.sin (μ * (0 - L / 2)))
      = (k * μ * Real.tan (μ * L / 2)) *
        ((Ta + Real.exp (-D * μ ^ 2 * t) * Real.cos (μ * (0 - L / 2))) - Ta)
    rw [harg0, Real.sin_neg, Real.cos_neg, Real.tan_eq_sin_div_cos]
    field_simp
    ring
  · intro t
    change -k * (-μ * Real.exp (-D * μ ^ 2 * t) * Real.sin (μ * (L - L / 2)))
      = (k * μ * Real.tan (μ * L / 2)) *
        ((Ta + Real.exp (-D * μ ^ 2 * t) * Real.cos (μ * (L - L / 2))) - Ta)
    rw [hargL, Real.tan_eq_sin_div_cos]
    field_simp
    ring
  · change 0 ≤ k * μ * Real.tan (μ * L / 2)
    have htan : 0 ≤ Real.tan (μ * L / 2) := by
      rw [Real.tan_eq_sin_div_cos]
      apply div_nonneg
      · apply Real.sin_nonneg_of_mem_Icc
        constructor
        · positivity
        · have hpi : 0 ≤ Real.pi := Real.pi_pos.le
          linarith
      · exact hC1pos.le
    exact mul_nonneg (mul_nonneg hk.le hμ) htan
  · intro t
    change Ta + Real.exp (-D * μ ^ 2 * t) * Real.cos (μ * (0 - L / 2)) - Ta ≠ 0
    rw [harg0, Real.cos_neg]
    have heq : Ta + Real.exp (-D * μ ^ 2 * t) * Real.cos (μ * L / 2) - Ta
        = Real.exp (-D * μ ^ 2 * t) * Real.cos (μ * L / 2) := by
      ring
    rw [heq]
    exact mul_ne_zero (Real.exp_ne_zero _) hC1

/-- Neumann cosine mode (nonzero fixture, `h0 = hL = 0`). With `μ = π / L`,
`u t x = Ta + exp (-D * μ^2 * t) * cos (μ * x)` has zero flux at both ends and
`θ(t, 0) ≠ 0`. -/
theorem neumannCosineMode {D k L Ta : ℝ} (hL0 : 0 < L) :
    let μ : ℝ := Real.pi / L
    let u : ℝ → ℝ → ℝ := fun t x => Ta + Real.exp (-D * μ ^ 2 * t) * Real.cos (μ * x)
    let ux : ℝ → ℝ → ℝ := fun t x => -μ * Real.exp (-D * μ ^ 2 * t) * Real.sin (μ * x)
    (∀ t x, HasDerivAt (fun y => u t y) (ux t x) x) ∧
    (∀ t, k * ux t 0 = 0 * (u t 0 - Ta)) ∧
    (∀ t, -k * ux t L = 0 * (u t L - Ta)) ∧
    (∀ t, u t 0 - Ta ≠ 0) := by
  intro μ u ux
  have hL' : L ≠ 0 := hL0.ne'
  have hμL : μ * L = Real.pi := by
    change Real.pi / L * L = Real.pi
    exact div_mul_cancel₀ _ hL'
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro t x
    change HasDerivAt (fun y : ℝ => Ta + Real.exp (-D * μ ^ 2 * t) * Real.cos (μ * y))
      (-μ * Real.exp (-D * μ ^ 2 * t) * Real.sin (μ * x)) x
    have hφ : HasDerivAt (fun y : ℝ => μ * y) μ x := by
      simpa only [mul_one] using (hasDerivAt_id' x).const_mul μ
    have hcos : HasDerivAt (fun y : ℝ => Real.cos (μ * y)) (-Real.sin (μ * x) * μ) x :=
      (Real.hasDerivAt_cos _).comp x hφ
    have hmul := hcos.const_mul (Real.exp (-D * μ ^ 2 * t))
    have hfin := hmul.const_add Ta
    have hval : Real.exp (-D * μ ^ 2 * t) * (-Real.sin (μ * x) * μ)
        = -μ * Real.exp (-D * μ ^ 2 * t) * Real.sin (μ * x) := by
      ring
    rwa [hval] at hfin
  · intro t
    change k * (-μ * Real.exp (-D * μ ^ 2 * t) * Real.sin (μ * 0))
      = 0 * ((Ta + Real.exp (-D * μ ^ 2 * t) * Real.cos (μ * 0)) - Ta)
    simp [mul_zero, Real.sin_zero]
  · intro t
    change -k * (-μ * Real.exp (-D * μ ^ 2 * t) * Real.sin (μ * L))
      = 0 * ((Ta + Real.exp (-D * μ ^ 2 * t) * Real.cos (μ * L)) - Ta)
    rw [hμL, Real.sin_pi]
    simp
  · intro t
    change Ta + Real.exp (-D * μ ^ 2 * t) * Real.cos (μ * 0) - Ta ≠ 0
    rw [mul_zero, Real.cos_zero]
    have heq : Ta + Real.exp (-D * μ ^ 2 * t) * 1 - Ta = Real.exp (-D * μ ^ 2 * t) := by
      ring
    rw [heq]
    exact Real.exp_ne_zero _

/-- Invalid: the wrong left sign (`-k * ux(0) = h0 * θ(0)`, i.e. normal `+1` at `0`)
admits boundary input: with `k = h0 = D = 1`, `θ(0) = 1`, `ux(0) = -1`,
`θ(L) = ux(L) = 0`, the boundary work `D * (θ(L) ux(L) - θ(0) ux(0))` is `1 > 0`. -/
theorem wrongLeftSign_boundaryInput :
    ∃ k h0 D θ0 ux0 θL uxL : ℝ, 0 < k ∧ 0 < h0 ∧ 0 < D ∧
      -k * ux0 = h0 * θ0 ∧ -k * uxL = 0 * θL ∧
      0 < D * (θL * uxL - θ0 * ux0) := by
  exact ⟨1, 1, 1, 1, -1, 0, 0, by norm_num, by norm_num, by norm_num, by norm_num,
    by norm_num, by norm_num⟩

/-- Invalid: a negative transfer coefficient with the correct signs is not
dissipative: `k = D = 1`, `h0 = -1`, `θ(0) = 1`, `ux(0) = -1`, `θ(L) = ux(L) = 0`
gives positive boundary work. -/
theorem negativeH_boundaryInput :
    ∃ k h0 D θ0 ux0 θL uxL : ℝ, 0 < k ∧ h0 < 0 ∧ 0 < D ∧
      k * ux0 = h0 * θ0 ∧ -k * uxL = 0 * θL ∧
      0 < D * (θL * uxL - θ0 * ux0) := by
  exact ⟨1, -1, 1, 1, -1, 0, 0, by norm_num, by norm_num, by norm_num, by norm_num,
    by norm_num, by norm_num⟩

end ConductionPorts

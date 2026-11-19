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
public import MathlibExt.Biology.Biophysics.MembraneCable
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import PhyslibExt.Engineering.ZoneQuadraticDissipation

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

Section D treats a straight fin (conductivity `k`, cross-section `A`,
perimeter `P`, film coefficient `h`, length `L`) as the steady passive
cable of `MathlibExt.Biology.Biophysics.MembraneCable`: the temperature
excess `θ = T - Ta` is the voltage, the conducted heat rate `q` (in the
`+x` direction) is the axial current, `ri = 1 / (k A)` and
`rm = 1 / (h P)`. The existing sealed-end and transfer solutions then
give the fin results; no new ODE solution is built.

Section E states the lumped thermal-network balances in the form used
here: finitely many nodes with heat capacities `C i`, symmetric
conductances `G i j = G j i` and external inputs `Q i`, obeying
`C i * T i' = ∑ j, G i j * (T j - T i) + Q i` at one time `t`.
Conduction between nodes cancels in the stored heat `∑ i, C i * T i`,
and without inputs the different, quadratic functional
`∑ i, C i * T i ^ 2 / 2` has rate
`-∑ i, ∑ j, G i j * (T i - T j) ^ 2 / 2`. Both identities are the
zone-network results `ZoneHeatInventory.heat_inventory_hasDerivAt` and
`ZoneHeatInventory.quadratic_dissipation_hasDerivAt` with no heating
power and no boundary conductance; they assume only symmetry. Capacity
nonnegativity makes the functional nonnegative and conductance
nonnegativity makes its rate nonpositive. No convergence theorem for
connected networks is claimed.

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
- `ConductionPorts.isFinSteadyState_iff`: Fourier's law and the
  lateral convection balance of a fin are the steady cable equations,
  with length constant `1 / m`, `m = sqrt (h P / (k A))`
  (`ConductionPorts.lengthConstant_fin`), and characteristic resistance
  `1 / sqrt (h P k A)` (`ConductionPorts.charResistance_fin`).
- `ConductionPorts.IsFinSteadyState.temperature_adiabatic`,
  `ConductionPorts.IsFinSteadyState.heatRate_adiabatic`,
  `ConductionPorts.IsFinSteadyState.efficiency_adiabatic`: adiabatic
  tip, `q 0 = sqrt (h P k A) θ 0 tanh (m L)` and efficiency
  `tanh (m L) / (m L)`.
- `ConductionPorts.IsFinSteadyState.heatRate_convectiveTip`: convective
  tip `q L = h A θ L` through the transfer solution;
  `ConductionPorts.IsFinSteadyState.heatRate_pos_of_base_pos`: a hot
  base feeds heat into the fin.
- `ConductionPorts.hasDerivAt_thermalStorage`: the stored heat of a
  thermal network has rate `∑ i, Q i` (symmetric conductances).
- `ConductionPorts.hasDerivAt_quadraticFunctional`: without inputs the
  quadratic functional has rate
  `-∑ i, ∑ j, G i j * (T i - T j) ^ 2 / 2` (symmetric conductances);
  `ConductionPorts.quadraticFunctional_nonneg` (nonnegative capacities)
  and `ConductionPorts.quadraticFunctional_rate_nonpos` (nonnegative
  conductances) give the signs.

## iii. Table of contents

- A. The quadratic energy identity
- B. Outward Robin/Neumann dissipation
- C. Fixtures
- D. Fins as passive cables
- E. Thermal networks: storage and quadratic decay

## iv. References

- The calculation is the standard multiplier-by-`u` energy argument
  for the linear heat equation; the statement is self-contained.
- Fins: F. P. Incropera, D. P. DeWitt, T. L. Bergman, A. S. Lavine,
  *Fundamentals of Heat and Mass Transfer*, 7th ed., Wiley (2011),
  Section 3.6.

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


/-! ## B. Outward Robin/Neumann dissipation -/

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

/-! ## C. Fixtures -/

/-- Robin cosine mode (nonzero fixture). `u t x = Ta + exp (-D * μ^2 * t) *
cos (μ * (x - L / 2))` with `ux` its `x`-derivative solves `u_t = D * u_xx` at
every point, satisfies the outward Robin conditions at both ends with
`h = k * μ * tan (μ * L / 2)`, has `h ≥ 0` when `0 ≤ μ`, `0 ≤ L` and
`μ * L / 2 < π / 2`, and has `θ(t, 0) ≠ 0` there. -/
lemma robinCosineMode {D k μ L Ta : ℝ} (hk : 0 < k) (hμ : 0 ≤ μ) (hL0 : 0 ≤ L)
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

/-- Neumann cosine mode (nonzero boundary fixture, `h0 = hL = 0`). With
`μ = π / L`, `u t x = Ta + exp (-D * μ^2 * t) * cos (μ * x)` has zero flux
at both ends and `θ(t, 0) ≠ 0`. This fixture records only the first
spatial derivative and the zero-flux boundary conditions; the
heat-equation content for cosine modes is in `robinCosineMode`. -/
lemma neumannCosineMode {D k L Ta : ℝ} (hL0 : 0 < L) :
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
lemma wrongLeftSign_boundaryInput :
    ∃ k h0 D θ0 ux0 θL uxL : ℝ, 0 < k ∧ 0 < h0 ∧ 0 < D ∧
      -k * ux0 = h0 * θ0 ∧ -k * uxL = 0 * θL ∧
      0 < D * (θL * uxL - θ0 * ux0) := by
  exact ⟨1, 1, 1, 1, -1, 0, 0, by norm_num, by norm_num, by norm_num, by norm_num,
    by norm_num, by norm_num⟩

/-- Invalid: a negative transfer coefficient with the correct signs is not
dissipative: `k = D = 1`, `h0 = -1`, `θ(0) = 1`, `ux(0) = -1`, `θ(L) = ux(L) = 0`
gives positive boundary work. -/
lemma negativeH_boundaryInput :
    ∃ k h0 D θ0 ux0 θL uxL : ℝ, 0 < k ∧ h0 < 0 ∧ 0 < D ∧
      k * ux0 = h0 * θ0 ∧ -k * uxL = 0 * θL ∧
      0 < D * (θL * uxL - θ0 * ux0) := by
  exact ⟨1, -1, 1, 1, -1, 0, 0, by norm_num, by norm_num, by norm_num, by norm_num,
    by norm_num, by norm_num⟩


/-! ## D. Fins as passive cables -/

section FinCable

open Real Set MathlibExt.Biology.Biophysics.MembraneCable

/-- Steady one-dimensional fin on `[0, L]`: Fourier's law `T' = -q / (k A)` and the lateral
convection balance `q' = -h P (T - Ta)`, as derivatives within `[0, L]`. `q` is the conducted
heat rate in the `+x` direction. -/
structure IsFinSteadyState (k A h P Ta L : ℝ) (T q : ℝ → ℝ) : Prop where
  hasDerivWithinAt_temperature :
    ∀ x ∈ Icc 0 L, HasDerivWithinAt T (-(q x / (k * A))) (Icc 0 L) x
  hasDerivWithinAt_heat :
    ∀ x ∈ Icc 0 L, HasDerivWithinAt q (-(h * P * (T x - Ta))) (Icc 0 L) x

/-- Fin parameter `m = sqrt (h P / (k A))` (inverse length). -/
noncomputable def finParameter (h P k A : ℝ) : ℝ := Real.sqrt (h * P / (k * A))

/-- Division by a reciprocal is multiplication (holds even for `b = 0`). -/
private lemma div_one_div_eq (a b : ℝ) : a / (1 / b) = a * b := by
  rw [one_div, div_inv_eq_mul]

/-- The fin parameter of positive data is positive. -/
private lemma finParameter_pos {k A h P : ℝ} (hk : 0 < k) (hA : 0 < A) (hh : 0 < h)
    (hP : 0 < P) : 0 < finParameter h P k A := by
  unfold finParameter
  exact Real.sqrt_pos.2 (div_pos (mul_pos hh hP) (mul_pos hk hA))

/-- The fin's membrane resistance `1 / (h * P)` is positive. -/
private lemma fin_rm_pos {h P : ℝ} (hh : 0 < h) (hP : 0 < P) : 0 < 1 / (h * P) :=
  one_div_pos.2 (mul_pos hh hP)

/-- The fin's axial resistance `1 / (k * A)` is positive. -/
private lemma fin_ri_pos {k A : ℝ} (hk : 0 < k) (hA : 0 < A) : 0 < 1 / (k * A) :=
  one_div_pos.2 (mul_pos hk hA)

/-- `sqrt (h * P * k * A)` of positive data is positive. -/
private lemma fin_sqrt_pos {k A h P : ℝ} (hk : 0 < k) (hA : 0 < A) (hh : 0 < h)
    (hP : 0 < P) : 0 < Real.sqrt (h * P * k * A) :=
  Real.sqrt_pos.2 (mul_pos (mul_pos (mul_pos hh hP) hk) hA)

/-- `sqrt (h * P * k * A) * m = h * P`. -/
private lemma fin_sqrt_mul_finParameter {k A h P : ℝ} (hk : 0 < k) (hA : 0 < A) (hh : 0 < h)
    (hP : 0 < P) : Real.sqrt (h * P * k * A) * finParameter h P k A = h * P := by
  have hnn : (0:ℝ) ≤ h * P * k * A := (mul_pos (mul_pos (mul_pos hh hP) hk) hA).le
  unfold finParameter
  rw [← Real.sqrt_mul hnn]
  have hid : (h * P * k * A) * (h * P / (k * A)) = (h * P)^2 := by
    field_simp
  rw [hid, Real.sqrt_sq (mul_pos hh hP).le]

/-- `A * (m * k) = sqrt (h * P * k * A)`. -/
private lemma fin_sqrt_eq_mul {k A h P : ℝ} (hk : 0 < k) (hA : 0 < A) (hh : 0 < h)
    (hP : 0 < P) : A * (finParameter h P k A * k) = Real.sqrt (h * P * k * A) := by
  have hmpos := finParameter_pos hk hA hh hP
  have hnn : (0:ℝ) ≤ A * (finParameter h P k A * k) :=
    mul_nonneg hA.le (mul_nonneg hmpos.le hk.le)
  have hnn2 : (0:ℝ) ≤ h * P / (k * A) := (div_pos (mul_pos hh hP) (mul_pos hk hA)).le
  have hsq : (A * (finParameter h P k A * k))^2 = h * P * k * A := by
    unfold finParameter
    rw [mul_pow, mul_pow, Real.sq_sqrt hnn2]
    field_simp
  rw [← Real.sqrt_sq hnn, hsq]

/-- The fin equations are the steady cable equations for `θ = T - Ta` and `q`, with
`rm = 1 / (h P)` and `ri = 1 / (k A)`. -/
lemma isFinSteadyState_iff {k A h P Ta L : ℝ} {T q : ℝ → ℝ} :
    IsFinSteadyState k A h P Ta L T q ↔
      IsSteadyState (1 / (h * P)) (1 / (k * A)) (Icc 0 L) (fun x => T x - Ta) q := by
  have htemp : ∀ x : ℝ, (-(q x / (k * A))) = (-((1:ℝ) / (k * A) * q x)) := fun x => by ring
  have hheat : ∀ x : ℝ, (-(h * P * (T x - Ta))) = (-((T x - Ta) / (1 / (h * P)))) := by
    intro x
    rw [div_one_div_eq]
    ring
  constructor
  · intro hfin
    refine ⟨fun x hx => ?_, fun x hx => ?_⟩
    · have h := hfin.hasDerivWithinAt_temperature x hx
      rw [htemp x] at h
      exact h.sub_const Ta
    · have h := hfin.hasDerivWithinAt_heat x hx
      rw [hheat x] at h
      exact h
  · intro hcable
    refine ⟨fun x hx => ?_, fun x hx => ?_⟩
    · have hV : HasDerivWithinAt (fun x => T x - Ta) (-((1:ℝ) / (k * A) * q x))
        (Icc 0 L) x := hcable.hasDerivWithinAt_voltage x hx
      rw [← htemp x] at hV
      simpa using hV.add_const Ta
    · have hC : HasDerivWithinAt q (-((T x - Ta) / (1 / (h * P)))) (Icc 0 L) x :=
        hcable.hasDerivWithinAt_current x hx
      rw [← hheat x] at hC
      exact hC

/-- The cable length constant of the fin is `1 / m`. -/
lemma lengthConstant_fin {k A h P : ℝ} (hk : 0 < k) (hA : 0 < A) (hh : 0 < h) (hP : 0 < P) :
    lengthConstant (1 / (h * P)) (1 / (k * A)) = 1 / finParameter h P k A := by
  have hdiv : (1:ℝ) / (h * P) / (1 / (k * A)) = (k * A) / (h * P) := by
    field_simp
  have hinv : (k * A) / (h * P) = ((h * P) / (k * A))⁻¹ := (inv_div _ _).symm
  unfold lengthConstant finParameter
  rw [hdiv, hinv, Real.sqrt_inv, one_div]

/-- The cable characteristic resistance of the fin is `1 / sqrt (h P k A)`. -/
lemma charResistance_fin {k A h P : ℝ} (hk : 0 < k) (hA : 0 < A) (hh : 0 < h) (hP : 0 < P) :
    charResistance (1 / (h * P)) (1 / (k * A)) = 1 / Real.sqrt (h * P * k * A) := by
  have hmul : (1:ℝ) / (h * P) * (1 / (k * A)) = (h * P * k * A)⁻¹ := by
    field_simp
  unfold charResistance
  rw [hmul, Real.sqrt_inv, ← one_div]

/-- Division by the fin's cable length constant is multiplication by `m`. -/
private lemma div_lengthConstant_fin {k A h P : ℝ} (hk : 0 < k) (hA : 0 < A) (hh : 0 < h)
    (hP : 0 < P) (y : ℝ) :
    y / lengthConstant (1 / (h * P)) (1 / (k * A)) = finParameter h P k A * y := by
  rw [lengthConstant_fin hk hA hh hP, div_one_div_eq]
  exact mul_comm _ _

/-- Adiabatic tip (`q L = 0`), from the sealed-end solution: the excess is
`θ x = θ 0 * cosh (m (L - x)) / cosh (m L)` on `[0, L]`. -/
lemma IsFinSteadyState.temperature_adiabatic {k A h P Ta L : ℝ} {T q : ℝ → ℝ}
    (hfin : IsFinSteadyState k A h P Ta L T q) (hk : 0 < k) (hA : 0 < A) (hh : 0 < h)
    (hP : 0 < P) (hL : 0 < L) (htip : q L = 0) :
    ∀ x ∈ Icc 0 L, T x - Ta =
      (T 0 - Ta) * Real.cosh (finParameter h P k A * (L - x)) /
        Real.cosh (finParameter h P k A * L) := by
  have hcable : IsSteadyState (1 / (h * P)) (1 / (k * A)) (Icc 0 L) (fun x => T x - Ta) q :=
    isFinSteadyState_iff.mp hfin
  have hsealed := hcable.sealedEnd (fin_rm_pos hh hP) (fin_ri_pos hk hA) hL htip
  intro x hx
  have hx' := hsealed.2 x hx
  simp only [div_lengthConstant_fin hk hA hh hP] at hx'
  exact hx'

/-- Adiabatic-tip heat rate, from the sealed-end input relation:
`q 0 = sqrt (h P k A) * θ 0 * tanh (m L)`. -/
lemma IsFinSteadyState.heatRate_adiabatic {k A h P Ta L : ℝ} {T q : ℝ → ℝ}
    (hfin : IsFinSteadyState k A h P Ta L T q) (hk : 0 < k) (hA : 0 < A) (hh : 0 < h)
    (hP : 0 < P) (hL : 0 < L) (htip : q L = 0) :
    q 0 = Real.sqrt (h * P * k * A) * (T 0 - Ta) * Real.tanh (finParameter h P k A * L) := by
  have hcable : IsSteadyState (1 / (h * P)) (1 / (k * A)) (Icc 0 L) (fun x => T x - Ta) q :=
    isFinSteadyState_iff.mp hfin
  have hrel := (hcable.sealedEnd (fin_rm_pos hh hP) (fin_ri_pos hk hA) hL htip).1
  have harg : L / lengthConstant (1 / (h * P)) (1 / (k * A)) = finParameter h P k A * L :=
    div_lengthConstant_fin hk hA hh hP L
  rw [harg, charResistance_fin hk hA hh hP] at hrel
  have hS0 : Real.sqrt (h * P * k * A) ≠ 0 := (fin_sqrt_pos hk hA hh hP).ne'
  have hc0 : Real.cosh (finParameter h P k A * L) ≠ 0 := (cosh_pos _).ne'
  have h1 : (T 0 - Ta) * Real.sinh (finParameter h P k A * L) =
      (1 / Real.sqrt (h * P * k * A)) * (q 0 * Real.cosh (finParameter h P k A * L)) := by
    rw [← mul_assoc]
    exact hrel
  have hmul : ∀ a : ℝ, Real.sqrt (h * P * k * A) * ((1 / Real.sqrt (h * P * k * A)) * a)
      = a := by
    intro a
    rw [← mul_assoc, mul_one_div_cancel hS0, one_mul]
  have h2 := congrArg (fun v => Real.sqrt (h * P * k * A) * v) h1
  rw [hmul] at h2
  rw [Real.tanh_eq_sinh_div_cosh]
  have hrw : Real.sqrt (h * P * k * A) * (T 0 - Ta) *
        (Real.sinh (finParameter h P k A * L) / Real.cosh (finParameter h P k A * L)) =
      (Real.sqrt (h * P * k * A) * ((T 0 - Ta) * Real.sinh (finParameter h P k A * L))) /
        Real.cosh (finParameter h P k A * L) := by ring
  rw [hrw, eq_div_iff hc0]
  exact h2.symm

/-- Adiabatic-tip efficiency: the heat rate over the rate `h (P L) θ 0` of a fin at the base
temperature is `tanh (m L) / (m L)`, for a nonzero base excess. -/
lemma IsFinSteadyState.efficiency_adiabatic {k A h P Ta L : ℝ} {T q : ℝ → ℝ}
    (hfin : IsFinSteadyState k A h P Ta L T q) (hk : 0 < k) (hA : 0 < A) (hh : 0 < h)
    (hP : 0 < P) (hL : 0 < L) (htip : q L = 0) (hθ : T 0 - Ta ≠ 0) :
    q 0 / (h * (P * L) * (T 0 - Ta)) =
      Real.tanh (finParameter h P k A * L) / (finParameter h P k A * L) := by
  have hq := hfin.heatRate_adiabatic hk hA hh hP hL htip
  have hmpos := finParameter_pos hk hA hh hP
  have hden1 : h * (P * L) * (T 0 - Ta) ≠ 0 :=
    mul_ne_zero (mul_ne_zero hh.ne' (mul_ne_zero hP.ne' hL.ne')) hθ
  have hden2 : finParameter h P k A * L ≠ 0 := mul_ne_zero hmpos.ne' hL.ne'
  have hSm := fin_sqrt_mul_finParameter hk hA hh hP
  rw [hq, div_eq_div_iff hden1 hden2]
  linear_combination (T 0 - Ta) * Real.tanh (finParameter h P k A * L) * L * hSm

/-- Convective tip `q L = h A (T L - Ta)` (outward normal `+x`), through the transfer solution:
`q 0 = sqrt (h P k A) θ 0 (sinh (m L) + (h / (m k)) cosh (m L)) /
(cosh (m L) + (h / (m k)) sinh (m L))`. -/
lemma IsFinSteadyState.heatRate_convectiveTip {k A h P Ta L : ℝ} {T q : ℝ → ℝ}
    (hfin : IsFinSteadyState k A h P Ta L T q) (hk : 0 < k) (hA : 0 < A) (hh : 0 < h)
    (hP : 0 < P) (hL : 0 < L) (htip : q L = h * A * (T L - Ta)) :
    q 0 = Real.sqrt (h * P * k * A) * (T 0 - Ta) *
      ((Real.sinh (finParameter h P k A * L) +
          h / (finParameter h P k A * k) * Real.cosh (finParameter h P k A * L)) /
        (Real.cosh (finParameter h P k A * L) +
          h / (finParameter h P k A * k) * Real.sinh (finParameter h P k A * L))) := by
  have hcable : IsSteadyState (1 / (h * P)) (1 / (k * A)) (Icc 0 L) (fun x => T x - Ta) q :=
    isFinSteadyState_iff.mp hfin
  have hLmem : L ∈ Icc (0:ℝ) L := ⟨hL.le, le_rfl⟩
  have htrans := hcable.eq_cable_Icc (fin_rm_pos hh hP) (fin_ri_pos hk hA) hLmem
  have hmpos := finParameter_pos hk hA hh hP
  have hSpos := fin_sqrt_pos hk hA hh hP
  have hS0 : Real.sqrt (h * P * k * A) ≠ 0 := hSpos.ne'
  have hm0 : finParameter h P k A ≠ 0 := hmpos.ne'
  simp only [cableVoltage, cableCurrent, div_lengthConstant_fin hk hA hh hP,
    charResistance_fin hk hA hh hP] at htrans
  have hdiv1 : ∀ a : ℝ, a / (1 / Real.sqrt (h * P * k * A))
      = a * Real.sqrt (h * P * k * A) := fun a => div_one_div_eq a _
  simp only [hdiv1] at htrans
  have h1 : T L - Ta = (T 0 - Ta) * Real.cosh (finParameter h P k A * L) -
      (1 / Real.sqrt (h * P * k * A)) * q 0 * Real.sinh (finParameter h P k A * L) :=
    htrans.1
  have h2 : q L = q 0 * Real.cosh (finParameter h P k A * L) -
      (T 0 - Ta) * Real.sqrt (h * P * k * A) * Real.sinh (finParameter h P k A * L) :=
    htrans.2
  have hmain : q 0 * Real.cosh (finParameter h P k A * L) -
        (T 0 - Ta) * Real.sqrt (h * P * k * A) * Real.sinh (finParameter h P k A * L) =
      h * A * ((T 0 - Ta) * Real.cosh (finParameter h P k A * L) -
        (1 / Real.sqrt (h * P * k * A)) * q 0 * Real.sinh (finParameter h P k A * L)) := by
    linear_combination -h2 + htip + h * A * h1
  have hAmk := fin_sqrt_eq_mul hk hA hh hP
  have hK : h * A / Real.sqrt (h * P * k * A) = h / (finParameter h P k A * k) := by
    rw [div_eq_div_iff hS0 (mul_ne_zero hm0 hk.ne')]
    linear_combination h * hAmk
  have h4 : (1:ℝ) / Real.sqrt (h * P * k * A) * Real.sqrt (h * P * k * A) = 1 :=
    one_div_mul_cancel hS0
  have hfield : q 0 * (Real.cosh (finParameter h P k A * L) +
        h * A / Real.sqrt (h * P * k * A) * Real.sinh (finParameter h P k A * L)) =
      Real.sqrt (h * P * k * A) * (T 0 - Ta) *
        (Real.sinh (finParameter h P k A * L) +
          h * A / Real.sqrt (h * P * k * A) * Real.cosh (finParameter h P k A * L)) := by
    linear_combination hmain -
      (h * A) * (T 0 - Ta) * Real.cosh (finParameter h P k A * L) * h4
  have hKpos : 0 < h / (finParameter h P k A * k) := div_pos hh (mul_pos hmpos hk)
  have hspos : 0 < Real.sinh (finParameter h P k A * L) :=
    sinh_pos_iff.2 (mul_pos hmpos hL)
  have hden : Real.cosh (finParameter h P k A * L) +
      h / (finParameter h P k A * k) * Real.sinh (finParameter h P k A * L) ≠ 0 :=
    (add_pos (cosh_pos _) (mul_pos hKpos hspos)).ne'
  rw [← hK] at hden ⊢
  have hrw : Real.sqrt (h * P * k * A) * (T 0 - Ta) *
        ((Real.sinh (finParameter h P k A * L) +
            h * A / Real.sqrt (h * P * k * A) * Real.cosh (finParameter h P k A * L)) /
          (Real.cosh (finParameter h P k A * L) +
            h * A / Real.sqrt (h * P * k * A) * Real.sinh (finParameter h P k A * L))) =
      (Real.sqrt (h * P * k * A) * (T 0 - Ta) *
        (Real.sinh (finParameter h P k A * L) +
          h * A / Real.sqrt (h * P * k * A) * Real.cosh (finParameter h P k A * L))) /
        (Real.cosh (finParameter h P k A * L) +
          h * A / Real.sqrt (h * P * k * A) * Real.sinh (finParameter h P k A * L)) := by
    ring
  rw [hrw, eq_div_iff hden]
  exact hfield

/-- Sign check: with an adiabatic tip, a base hotter than the fluid feeds heat into the fin
(`q 0 > 0`, flow in `+x`, out of the wall). -/
lemma IsFinSteadyState.heatRate_pos_of_base_pos {k A h P Ta L : ℝ} {T q : ℝ → ℝ}
    (hfin : IsFinSteadyState k A h P Ta L T q) (hk : 0 < k) (hA : 0 < A) (hh : 0 < h)
    (hP : 0 < P) (hL : 0 < L) (htip : q L = 0) (hθ : 0 < T 0 - Ta) :
    0 < q 0 := by
  have hq := hfin.heatRate_adiabatic hk hA hh hP hL htip
  rw [hq]
  have ht : 0 < Real.tanh (finParameter h P k A * L) := by
    rw [Real.tanh_eq_sinh_div_cosh]
    exact div_pos (sinh_pos_iff.2 (mul_pos (finParameter_pos hk hA hh hP) hL)) (cosh_pos _)
  exact mul_pos (mul_pos (fin_sqrt_pos hk hA hh hP) hθ) ht

end FinCable


/-! ## E. Thermal networks: storage and quadratic decay -/

section ThermalNetwork

variable {ι : Type*} [Fintype ι]

/-- Storage balance at time `t`: if `dT i` is the derivative of `T i` at `t`, the conductances
are symmetric and every node obeys `C i * dT i = ∑ j, G i j * (T j t - T i t) + Q i` at `t`, the
stored heat `∑ i, C i * T i` has derivative `∑ i, Q i` at `t`: conduction between nodes cancels.
This is `ZoneHeatInventory.heat_inventory_hasDerivAt` with inputs `Q` and no heating power. -/
lemma hasDerivAt_thermalStorage {C : ι → ℝ} {G : ι → ι → ℝ} (hG : ∀ i j, G i j = G j i)
    {T : ι → ℝ → ℝ} {dT Q : ι → ℝ} {t : ℝ}
    (hT : ∀ i, HasDerivAt (T i) (dT i) t)
    (hbal : ∀ i, C i * dT i = ∑ j, G i j * (T j t - T i t) + Q i) :
    HasDerivAt (fun τ => ∑ i, C i * T i τ) (∑ i, Q i) t := by
  have h := ZoneHeatInventory.heat_inventory_hasDerivAt C G T (fun i _ => dT i)
    (fun i _ => Q i) (fun _ _ => 0) t hG hT (fun i => by simpa using hbal i)
  simpa using h

/-- Quadratic Lyapunov identity at time `t`: with symmetric conductances and no external inputs,
the functional `∑ i, C i * T i ^ 2 / 2` has derivative
`-∑ i, ∑ j, G i j * (T i t - T j t) ^ 2 / 2` at `t`. This is
`ZoneHeatInventory.quadratic_dissipation_hasDerivAt` with no boundary conductance, zero
reference and no heating power. -/
lemma hasDerivAt_quadraticFunctional {C : ι → ℝ} {G : ι → ι → ℝ} (hG : ∀ i j, G i j = G j i)
    {T : ι → ℝ → ℝ} {dT : ι → ℝ} {t : ℝ}
    (hT : ∀ i, HasDerivAt (T i) (dT i) t)
    (hbal : ∀ i, C i * dT i = ∑ j, G i j * (T j t - T i t)) :
    HasDerivAt (fun τ => ∑ i, C i * T i τ ^ 2 / 2)
      (-∑ i, ∑ j, G i j * (T i t - T j t) ^ 2 / 2) t := by
  have h := ZoneHeatInventory.quadratic_dissipation_hasDerivAt C G (fun _ => 0) 0 T
    (fun i _ => dT i) (fun _ _ => 0) t hG hT (fun i => by simpa using hbal i)
  convert h using 1
  · funext s
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  · simp only [zero_mul, Finset.sum_const_zero, add_zero, mul_zero, sub_zero]
    congr 1
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring

/-- The quadratic functional is nonnegative for nonnegative capacities. -/
lemma quadraticFunctional_nonneg {C : ι → ℝ} (hC : ∀ i, 0 ≤ C i) (T : ι → ℝ) :
    0 ≤ ∑ i, C i * T i ^ 2 / 2 := by
  refine Finset.sum_nonneg fun i _ => ?_
  have := hC i
  positivity

/-- The rate of the quadratic functional is nonpositive for nonnegative conductances. -/
lemma quadraticFunctional_rate_nonpos {G : ι → ι → ℝ} (hGnn : ∀ i j, 0 ≤ G i j) (T : ι → ℝ) :
    -∑ i, ∑ j, G i j * (T i - T j) ^ 2 / 2 ≤ 0 := by
  rw [neg_nonpos]
  refine Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => ?_
  have := hGnn i j
  positivity

end ThermalNetwork

end ConductionPorts

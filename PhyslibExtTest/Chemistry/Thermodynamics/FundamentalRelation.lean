/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import PhyslibExt.Chemistry.Thermodynamics.FundamentalRelation

/-!

# Tests for equilibrium postulates and the fundamental relation

Numeric ideal-gas instance, boundary countermodel and two-subsystem
entropy-maximum example.

-/

@[expose] public section

open Chemistry.Thermodynamics

open scoped Topology

namespace PhyslibExtTest.Chemistry.Thermodynamics

/-!

## A. Ideal-gas numeric instance

With `N = 1`, `kB = 1`, `s0 = 0`, `V = 1` and `U = 3 / 2`, the temperature is
`T = 1`.

-/

/-- At `(U, V, N) = (3/2, 1, 1)` with `kB = 1`, `T = 1`. -/
example : temp (SidealGen 1 0) ((3 / 2, 1, fun _ => 1) : ThermoState 1) = 1 := by
  have hU : (0 : ℝ) < ((3 / 2, 1, fun _ => 1) : ThermoState 1).1 := by
    change (0 : ℝ) < 3 / 2
    norm_num
  have hN : (0 : ℝ) < ((3 / 2, 1, fun _ => 1) : ThermoState 1).2.2 0 := by
    change (0 : ℝ) < 1
    norm_num
  rw [sideal_temp 1 0 _ hU hN (by norm_num)]
  change 2 * (3 / 2) / (3 * 1 * 1) = 1
  norm_num

/-- `p * V = N * kB * T` at the numeric point: both sides equal `1`. -/
example : press (SidealGen 1 0) ((3 / 2, 1, fun _ => 1) : ThermoState 1) * 1 =
    1 * 1 * temp (SidealGen 1 0) ((3 / 2, 1, fun _ => 1) : ThermoState 1) := by
  have hU : (0 : ℝ) < ((3 / 2, 1, fun _ => 1) : ThermoState 1).1 := by
    change (0 : ℝ) < 3 / 2
    norm_num
  have hV : (0 : ℝ) < ((3 / 2, 1, fun _ => 1) : ThermoState 1).2.1 := by
    change (0 : ℝ) < 1
    norm_num
  have hN : (0 : ℝ) < ((3 / 2, 1, fun _ => 1) : ThermoState 1).2.2 0 := by
    change (0 : ℝ) < 1
    norm_num
  exact sideal_pV 1 0 _ hU hV hN (by norm_num)

/-- `U = (3/2) * N * kB * T` at the numeric point. -/
example : (3 / 2 : ℝ) =
    3 / 2 * 1 * 1 * temp (SidealGen 1 0) ((3 / 2, 1, fun _ => 1) : ThermoState 1) := by
  have hU : (0 : ℝ) < ((3 / 2, 1, fun _ => 1) : ThermoState 1).1 := by
    change (0 : ℝ) < 3 / 2
    norm_num
  have hN : (0 : ℝ) < ((3 / 2, 1, fun _ => 1) : ThermoState 1).2.2 0 := by
    change (0 : ℝ) < 1
    norm_num
  exact sideal_U 1 0 _ hU hN (by norm_num)

/-- The entropy value at the numeric point is `(3/2) * log (3/2)`. -/
example : Sideal 1 0 (3 / 2) 1 1 = 3 / 2 * Real.log (3 / 2) := by
  simp only [Sideal, div_one, Real.log_one]
  ring

/-!

## B. Boundary countermodel

-/

/-- At `N = 0` the `∂S/∂U` postulate fails: the slice derivative is `0`. -/
example : dSdU (SidealGen 1 0) ((1, 1, fun _ => 0) : ThermoState 1) = 0 :=
  sideal_dSdU_at_N_zero 1 0 1 1

/-- At `(U, V, N) = (1, 1, 0)` the caloric equation of state fails. -/
example : ¬ (1 : ℝ) =
    3 / 2 * (0 : ℝ) * 1 * temp (SidealGen 1 0) ((1, 1, fun _ => 0) : ThermoState 1) :=
  sideal_EOS_fails_at_N_zero 0

/-!

## C. Two-subsystem entropy maximum

Two ideal-gas subsystems with `V₁ = V₂ = 1`, `N₁ = N₂ = 1`, `kB = 1`, `s0 = 0`
and total energy `Utot = 3`: at `U₁ = 3 / 2` the total-entropy rate vanishes
and both temperatures equal `1`.

-/

/-- The total-entropy rate vanishes at `U₁ = 3 / 2`. -/
example : deriv
    (fun U1 => Sideal 1 0 U1 1 1 + Sideal 1 0 (3 - U1) 1 1) (3 / 2) = 0 := by
  have h := sideal_stot_hasDerivAt 1 0 1 1 1 1 3 (3 / 2) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
  rw [h.deriv]
  norm_num

/-- Both subsystem temperatures equal `1` at `U₁ = 3 / 2`. -/
example : temp (SidealGen 1 0) ((3 / 2, 1, fun _ => 1) : ThermoState 1) =
    temp (SidealGen 1 0) ((3 - 3 / 2, 1, fun _ => 1) : ThermoState 1) := by
  have hU1 : (0 : ℝ) < ((3 / 2, 1, fun _ => 1) : ThermoState 1).1 := by
    change (0 : ℝ) < 3 / 2
    norm_num
  have hN1 : (0 : ℝ) < ((3 / 2, 1, fun _ => 1) : ThermoState 1).2.2 0 := by
    change (0 : ℝ) < 1
    norm_num
  have h1 : temp (SidealGen 1 0) ((3 / 2, 1, fun _ => 1) : ThermoState 1) = 1 := by
    rw [sideal_temp 1 0 _ hU1 hN1 (by norm_num)]
    change 2 * (3 / 2) / (3 * 1 * 1) = 1
    norm_num
  have hU2 : (0 : ℝ) < ((3 - 3 / 2, 1, fun _ => 1) : ThermoState 1).1 := by
    change (0 : ℝ) < 3 - 3 / 2
    norm_num
  have hN2 : (0 : ℝ) < ((3 - 3 / 2, 1, fun _ => 1) : ThermoState 1).2.2 0 := by
    change (0 : ℝ) < 1
    norm_num
  have h2 : temp (SidealGen 1 0) ((3 - 3 / 2, 1, fun _ => 1) : ThermoState 1) = 1 := by
    rw [sideal_temp 1 0 _ hU2 hN2 (by norm_num)]
    change 2 * (3 - 3 / 2) / (3 * 1 * 1) = 1
    norm_num
  rw [h1, h2]

/-- The ideal-gas entropy is concave on its domain (for `kB = 1 ≥ 0`). -/
example : ConcaveOn ℝ sidealDomain
    (fun x : ℝ × ℝ × ℝ => Sideal 1 0 x.1 x.2.1 x.2.2) :=
  sideal_concave 1 0 (by norm_num)

/-- General maximum principle with symbolic subsystem data: at an interior
local maximizer of total entropy the two temperatures agree. -/
example (F : FundamentalRelation 2) (V1 V2 Utot Ustar : ℝ)
    (N1 N2 : Fin 2 → ℝ)
    (hx1 : (Ustar, V1, N1) ∈ thermoDomain 2)
    (hx2 : (Utot - Ustar, V2, N2) ∈ thermoDomain 2)
    (hev1 : ∀ᶠ t in 𝓝 Ustar, (t, V1, N1) ∈ thermoDomain 2)
    (hev2 : ∀ᶠ t in 𝓝 Ustar, (Utot - t, V2, N2) ∈ thermoDomain 2)
    (hmax : IsLocalMax
      (fun U1 => F.S (U1, V1, N1) + F.S (Utot - U1, V2, N2)) Ustar) :
    temp F.S (Ustar, V1, N1) = temp F.S (Utot - Ustar, V2, N2) :=
  entropyMax_temperature_eq F V1 V2 Utot Ustar N1 N2 hx1 hx2 hev1 hev2 hmax

end PhyslibExtTest.Chemistry.Thermodynamics

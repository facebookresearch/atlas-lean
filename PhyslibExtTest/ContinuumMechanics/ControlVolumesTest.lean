/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import PhyslibExt.ContinuumMechanics.ControlVolumes
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.Pi
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.NormNum

/-!
# Control-volume checks

Concrete consumer of `PhyslibExt.ContinuumMechanics.ControlVolumes`:
the field `u t x = t * x` with endpoints `a(t) = 0`, `b(t) = t + 1`.
At `t = 1` the moving integral `∫₀² x dx` plus the endpoint term
`u(1, 2) * 1 = 2` gives energy derivative `4`, matching
`d/dt [t (t+1)^2 / 2]` at `t = 1`. The flux form with `f = 0`,
`src = u_t` gives the same value through the relative fluxes.

On a box `[a, b]` in `ℝ³` with `a < b`, the density `u = 1 + t`, the
flux `q = (-x₁, 0, 0)` and the source `s = 0` satisfy the local law;
the outward flux is minus the box volume, so the stored amount grows
at the rate of the volume, and reversing the outward normal gives a
false balance.

On the unit cube a steady turbine with the flux `(3004 - 1800 x₀, 0, 0)`
and the shaft power density `-1800` satisfies the declared energy law;
its inlet and outlet carry `ṁ θ = 3004` and `1204` with `ṁ = 2`, so the
two-port balance gives `Ẇ_out = 1800` at zero storage rate. Counting
`p / ρ` twice breaks that balance, and a growing storage leaves a
nonzero right-hand side.

In a channel on the unit square with density `1`, velocity `(1 + t, 0)`,
inlet pressure `2`, outlet pressure `1`, impermeable walls and the weight
`(0, -1)`, the two-port momentum balance holds: the port momentum fluxes
cancel, the pressure difference pushes with `(1, 0)` and the walls react
with `(0, 1)`, so the momentum grows at `(1, 0)`. Reversing the inlet's
outward normal while keeping `-p A n` predicts `(-3, 0)` and is refuted.

With the symmetric shear stress `1 + 2 x₀` added and the weight `(0, -3)`,
the same channel carries the viscous port tractions `τ_in = (0, 1)` and
`τ_out = (0, 3)`. The viscous two-port balance applies; its viscous term
`A₀ (τ_out - τ_in) = (0, 2)` and the wall reaction `(0, 1)` balance the
weight, so the predicted rate is the directly computed momentum rate
`(1, 0)`. Counting the inlet's viscous traction with the wrong sign
predicts `(1, 2)` and is refuted.

## i. Overview

These are elaboration and non-vacuity checks, not new results.

## ii. Key results

No new results are introduced here. Sections B, C and D name the
fixture steps that later ones reuse; sections C and D define the
turbine flux and the channel stresses they check.

## iii. Table of contents

- A. Linear field with unit-speed endpoint
- B. Growing storage in a fixed box and the reversed normal
- C. Energy ports of a steady turbine
- D. Momentum ports of pressure-driven channels

## iv. References

None.

## A. Linear field with unit-speed endpoint

-/

/-- Leibniz identity for `u t x = t * x`, `a = 0`, `b(t) = t + 1`
at `t = 1`: the value is `4`. -/
example :
    deriv (fun τ : ℝ => ∫ x in (0 : ℝ)..(τ + 1), τ * x) 1 = 4 := by
  have h := ControlVolumes.movingEndpoint_deriv
    (u := fun t x : ℝ => t * x) (ut := fun _ x : ℝ => x)
    (a := fun _ : ℝ => 0) (b := fun τ : ℝ => τ + 1)
    (a' := fun _ : ℝ => 0) (b' := fun _ : ℝ => 1)
    1
    (hasDerivAt_const 1 (0 : ℝ))
    (by simpa using (hasDerivAt_id 1).add_const (1 : ℝ))
    (by fun_prop)
    (fun t x => by simpa using (hasDerivAt_id t).mul_const x)
    (by fun_prop)
  rw [h]
  rw [integral_id]
  norm_num

/-- Relative-flux form for the same field with `f = 0`: the value
is again `4`. -/
example :
    deriv (fun τ : ℝ => ∫ x in (0 : ℝ)..(τ + 1), τ * x) 1 = 4 := by
  have h := ControlVolumes.movingEndpoint_deriv_flux
    (u := fun t x : ℝ => t * x) (ut := fun _ x : ℝ => x)
    (f := fun _ _ : ℝ => 0) (fx := fun _ _ : ℝ => 0)
    (src := fun _ x : ℝ => x)
    (a := fun _ : ℝ => 0) (b := fun τ : ℝ => τ + 1)
    (a' := fun _ : ℝ => 0) (b' := fun _ : ℝ => 1)
    1
    (hasDerivAt_const 1 (0 : ℝ))
    (by simpa using (hasDerivAt_id 1).add_const (1 : ℝ))
    (by fun_prop)
    (fun t x => by simpa using (hasDerivAt_id t).mul_const x)
    (by fun_prop)
    (fun x _ => hasDerivAt_const x (0 : ℝ))
    continuousOn_const
    (fun _ _ => by ring)
    (by simpa using (continuous_id.intervalIntegrable (0 : ℝ) (2 : ℝ)))
  rw [h]
  rw [integral_id]
  norm_num

/-- Jump transport for the stationary fields `uL t x = x`,
`uR t x = 2x` with interface `s t = t` on `[0, 2]`: at `t = 1`
the derivative of the split integral is the interface jump
`1 * (1 - 2) = -1`. -/
example :
    HasDerivAt
      (fun τ : ℝ => (∫ x in (0 : ℝ)..τ, x) + (∫ x in τ..(2 : ℝ), 2 * x))
      (-1) 1 := by
  have h := ControlVolumes.movingJumpTransport
    (uL := fun _ x : ℝ => x) (uR := fun _ x : ℝ => 2 * x)
    (vL := fun _ _ : ℝ => 0) (vR := fun _ _ : ℝ => 0)
    (s := fun τ : ℝ => τ) (s' := fun _ : ℝ => 1) (a := 0) (b := 2)
    1 (hasDerivAt_id 1)
    (by fun_prop) (fun t x => by simpa using (hasDerivAt_const t (x : ℝ)))
    (by fun_prop) (by fun_prop)
    (fun t x => by simpa using (hasDerivAt_const t (2 * x : ℝ)))
    (by fun_prop)
  rw [show (-1 : ℝ) = (1 : ℝ) - 2 by norm_num]
  simpa using h
/-- Moving lower endpoint: `u t x = t * x`, `a(t) = t`,
`b(t) = t + 1` at `t = 1`. Independently,
`∫ x in t..t+1, t * x = t * (2t + 1) / 2`, whose derivative at
`1` is `5 / 2`; the formula gives `3 / 2 + 2 - 1 = 5 / 2`,
exercising the lower-boundary minus sign. -/
example :
    deriv (fun τ : ℝ => ∫ x in τ..(τ + 1), τ * x) 1 = 5 / 2 := by
  have h := ControlVolumes.movingEndpoint_deriv
    (u := fun t x : ℝ => t * x) (ut := fun _ x : ℝ => x)
    (a := fun τ : ℝ => τ) (b := fun τ : ℝ => τ + 1)
    (a' := fun _ : ℝ => 1) (b' := fun _ : ℝ => 1)
    1
    (hasDerivAt_id 1)
    (by simpa using (hasDerivAt_id 1).add_const (1 : ℝ))
    (by fun_prop)
    (fun t x => by simpa using (hasDerivAt_id t).mul_const x)
    (by fun_prop)
  rw [h, integral_id]
  norm_num

/-- Nonzero flux with a moving lower endpoint: same field with
`f t x = t * x^2 / 2`, so `fx t x = t * x` and
`src t x = x + t * x`. At `t = 1` the formula gives
`3 - (2 - 2) + (1 / 2 - 1) = 5 / 2`, matching the previous
example and exercising the FTC flux reduction. -/
example :
    deriv (fun τ : ℝ => ∫ x in τ..(τ + 1), τ * x) 1 = 5 / 2 := by
  have h := ControlVolumes.movingEndpoint_deriv_flux
    (u := fun t x : ℝ => t * x) (ut := fun _ x : ℝ => x)
    (f := fun t x : ℝ => t * x ^ 2 / 2) (fx := fun t x : ℝ => t * x)
    (src := fun t x : ℝ => x + t * x)
    (a := fun τ : ℝ => τ) (b := fun τ : ℝ => τ + 1)
    (a' := fun _ : ℝ => 1) (b' := fun _ : ℝ => 1)
    1
    (hasDerivAt_id 1)
    (by simpa using (hasDerivAt_id 1).add_const (1 : ℝ))
    (by fun_prop)
    (fun t x => by simpa using (hasDerivAt_id t).mul_const x)
    (by fun_prop)
    (fun x _ => by simpa using ((hasDerivAt_pow 2 x).div_const (2 : ℝ)))
    (by fun_prop)
    (fun _ _ => by ring)
    (by simpa using ((continuous_id.add continuous_id).intervalIntegrable
      (1 : ℝ) (2 : ℝ)))
  rw [h]
  have hint : (∫ x in (1 : ℝ)..(1 + 1), (x + 1 * x)) = 3 := by
    have e : (fun x : ℝ => x + 1 * x) = (fun x : ℝ => 2 * x) :=
      funext fun x => by ring
    rw [e, intervalIntegral.integral_const_mul, integral_id]
    norm_num
  rw [hint]
  norm_num

@[expose] public section

namespace PhyslibExtTest.ContinuumMechanics.ControlVolumes

open Set MeasureTheory _root_.ControlVolumes
open MathlibExt.Probability.FokkerPlanck (divergence)

/-! ## B. Growing storage in a fixed box and the reversed normal -/

/-- The fixture fields satisfy the local law: `∂ₜ(1 + t) + div (-x₁, 0, 0) = 1 - 1 = 0`. -/
lemma fixture_localLaw (t : ℝ) (x : Fin 3 → ℝ) :
    deriv (fun τ : ℝ => 1 + τ) t + divergence (fun y : Fin 3 → ℝ => ![-y 0, 0, 0]) x = 0 := by
  have h1 : deriv (fun τ : ℝ => 1 + τ) t = 1 := by simp
  have e0 : fderiv ℝ (fun y : Fin 3 → ℝ => -y 0) x = -(ContinuousLinearMap.proj 0) :=
    ((hasFDerivAt_apply 0 x).neg).fderiv
  have h2 : divergence (fun y : Fin 3 → ℝ => ![-y 0, 0, 0]) x = -1 := by
    unfold divergence MathlibExt.Probability.FokkerPlanck.pderiv
    simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.tail_cons]
    rw [e0]
    simp
  rw [h1, h2]
  norm_num

/-- The outward flux of `(-x₁, 0, 0)` through a box with `a < b` is minus its volume: the
upper first face contributes `-b₁` and the lower one `+a₁` per unit face area. -/
lemma fixture_boxOutwardFlux {a b : Fin 3 → ℝ} (hab : ∀ i, a i < b i) :
    boxOutwardFlux a b (fun y => ![-y 0, 0, 0]) = -∏ i, (b i - a i) := by
  have hle : a ≤ b := fun i => (hab i).le
  have hface : (a ∘ (0 : Fin 3).succAbove) ≤ (b ∘ (0 : Fin 3).succAbove) := fun j => hle _
  rw [boxOutwardFlux, Fin.sum_univ_succ, Fin.sum_univ_two]
  simp only [Fin.insertNth_apply_same, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.cons_val_one, setIntegral_const, smul_eq_mul, mul_zero, sub_zero, add_zero]
  rw [measureReal_def, Real.volume_Icc_pi_toReal hface]
  simp only [Fin.prod_univ_two, Fin.prod_univ_three, Function.comp_apply, Fin.succAbove_zero,
    Fin.succ_zero_eq_one, Fin.succ_one_eq_two]
  ring

/-- The fixture is an instance of the balance: `u = 1 + t`, `q = (-x₁, 0, 0)`, `s = 0`. -/
lemma fixture_balance {a b : Fin 3 → ℝ} (hab : ∀ i, a i < b i) (t : ℝ) :
    HasDerivAt (fun τ => ∫ _ in Icc a b, (1 + τ : ℝ))
      ((∫ _ in Icc a b, (0 : ℝ)) - boxOutwardFlux a b (fun y => ![-y 0, 0, 0])) t := by
  refine hasDerivAt_boxIntegral (u := fun τ _ => 1 + τ) (s := fun _ _ => 0)
    (q := fun _ y => ![-y 0, 0, 0]) hab isOpen_univ (subset_univ _) ?_ ?_ ?_ ?_
  · unfold Function.uncurry
    fun_prop
  · refine ContDiff.contDiffOn (contDiff_pi.2 fun i => ?_)
    fin_cases i <;> simp <;> fun_prop
  · exact integrableOn_zero
  · intro x _
    exact fixture_localLaw t x

/-- The balance predicts the storage rate `∫ 0 - Φ = ∏ᵢ (b i - a i)`, the positive box
volume. -/
lemma fixture_balance_rhs {a b : Fin 3 → ℝ} (hab : ∀ i, a i < b i) :
    (∫ _ in Icc a b, (0 : ℝ)) - boxOutwardFlux a b (fun y => ![-y 0, 0, 0]) =
        ∏ i, (b i - a i) ∧
      0 < ∏ i, (b i - a i) := by
  refine ⟨?_, Finset.prod_pos fun i _ => sub_pos.2 (hab i)⟩
  rw [fixture_boxOutwardFlux hab]
  simp

/-- **Growing storage**: the stored amount `∫_box (1 + t)` is strictly increasing for `t ≥ 0`. -/
lemma fixture_storage_strictMonoOn {a b : Fin 3 → ℝ} (hab : ∀ i, a i < b i) :
    StrictMonoOn (fun τ : ℝ => ∫ _ in Icc a b, (1 + τ : ℝ)) (Ici 0) := by
  have hle : a ≤ b := fun i => (hab i).le
  have hvol : 0 < volume.real (Icc a b) := by
    rw [measureReal_def, Real.volume_Icc_pi_toReal hle]
    exact Finset.prod_pos fun i _ => sub_pos.2 (hab i)
  intro x _ y _ hxy
  simp only [setIntegral_const, smul_eq_mul]
  nlinarith

/-- **Reversed outward normal changes the balance**: adding the face flux instead of
subtracting it predicts the storage rate `-volume`, which the fixture refutes. -/
lemma fixture_reversedNormal {a b : Fin 3 → ℝ} (hab : ∀ i, a i < b i) (t : ℝ) :
    ¬ HasDerivAt (fun τ => ∫ _ in Icc a b, (1 + τ : ℝ))
      ((∫ _ in Icc a b, (0 : ℝ)) + boxOutwardFlux a b (fun y => ![-y 0, 0, 0])) t := by
  intro h
  have h2 := (fixture_balance hab t).unique h
  have hpos := (fixture_balance_rhs hab).2
  rw [fixture_boxOutwardFlux hab] at h2
  linarith


/-! ## C. Energy ports of a steady turbine -/

/-- The convective-plus-pressure flux of the steady turbine fixture on the unit cube:
`(3004 - 1800 x₀, 0, 0)`. -/
def turbineFlux (y : Fin 3 → ℝ) : Fin 3 → ℝ := ![3004 - 1800 * y 0, 0, 0]

/-- The steady turbine satisfies the declared law with `E = 1`, `J = 0`, `q̇ = 0` and the shaft
power density `ẇ = -1800` delivered to the fluid. -/
lemma fixture_turbine_law (t : ℝ) (x : Fin 3 → ℝ) :
    deriv (fun _ : ℝ => (1 : ℝ)) t + divergence (turbineFlux + fun _ => 0) x = 0 + -1800 := by
  have h1 : deriv (fun _ : ℝ => (1 : ℝ)) t = 0 := deriv_const t 1
  have hz : (turbineFlux + fun _ => (0 : Fin 3 → ℝ)) = turbineFlux := by
    funext y; simp
  have e0 : fderiv ℝ (fun y : Fin 3 → ℝ => 3004 - 1800 * y 0) x (Pi.single 0 1) = -1800 := by
    have h0 : HasFDerivAt (fun y : Fin 3 → ℝ => y 0)
        (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℝ) 0) x :=
      hasFDerivAt_apply 0 x
    have h := (h0.const_mul (1800 : ℝ)).const_sub (3004 : ℝ)
    rw [h.fderiv]
    simp
  have h2 : divergence turbineFlux x = -1800 := by
    unfold divergence MathlibExt.Probability.FokkerPlanck.pderiv
    simp only [Fin.sum_univ_three, turbineFlux, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.tail_cons]
    rw [e0]
    simp
  rw [hz, h1, h2]

/-- The port faces carry the uniform port rates per unit area: inlet `ρ = 1`, `V = 2`, `e = 1000`,
`p = 500`, `z = 0`, `v = (2, 0, 0)`, rate `3004`; outlet `ρ = 1`, `V = 2`, `e = 400`, `p = 200`,
`z = 0`, `v = (2, 0, 0)`, rate `1204`. -/
lemma fixture_turbine_ports (y : Fin 2 → ℝ) :
    turbineFlux ((0 : Fin 3).insertNth 0 y) 0 =
        2 * (1 * (1000 + ![(2 : ℝ), 0, 0] ⬝ᵥ ![2, 0, 0] / 2 + 981 / 100 * 0) + 500) ∧
      turbineFlux ((0 : Fin 3).insertNth 1 y) 0 =
        2 * (1 * (400 + ![(2 : ℝ), 0, 0] ⬝ᵥ ![2, 0, 0] / 2 + 981 / 100 * 0) + 200) := by
  constructor <;> simp [turbineFlux, dotProduct, Fin.sum_univ_three] <;> norm_num

/-- The turbine is an instance of the two-port balance, with zero storage rate. Both ports have the
velocity `(2, 0, 0)`; the mass flows use its component `2` along `e₀`. -/
example (t : ℝ) :
    HasDerivAt (fun _ : ℝ => ∫ _ in Icc (0 : Fin 3 → ℝ) 1, (1 : ℝ))
      (((∫ _ in Icc (0 : Fin 3 → ℝ) 1, (0 : ℝ)) -
            boxOutwardFlux (0 : Fin 3 → ℝ) 1 (fun _ => 0)) -
          ProcessPorts.workOut (∫ _ in Icc (0 : Fin 3 → ℝ) 1, (-1800 : ℝ)) +
        1 * faceArea (0 : Fin 3 → ℝ) 1 0 * ![(2 : ℝ), 0, 0] 0 *
          (specificEnthalpy 1000 500 1 + ![(2 : ℝ), 0, 0] ⬝ᵥ ![2, 0, 0] / 2 + 981 / 100 * 0) -
        1 * faceArea (0 : Fin 3 → ℝ) 1 0 * ![(2 : ℝ), 0, 0] 0 *
          (specificEnthalpy 400 200 1 + ![(2 : ℝ), 0, 0] ⬝ᵥ ![2, 0, 0] / 2 + 981 / 100 * 0)) t := by
  refine hasDerivAt_energy_twoPort (E := fun _ _ => 1) (G := fun _ => turbineFlux)
    (J := fun _ _ => 0) (qdot := fun _ _ => 0) (wdot := fun _ _ => -1800)
    (vi := ![2, 0, 0]) (vo := ![2, 0, 0]) (g := 981 / 100) (zi := 0) (zo := 0)
    (fun i => by simp) isOpen_univ (subset_univ _) ?_ ?_ ?_ ?_ ?_ ?_ one_ne_zero one_ne_zero
    ?_ ?_ ?_
  · unfold Function.uncurry; fun_prop
  · refine ContDiff.contDiffOn (contDiff_pi.2 fun i => ?_)
    fin_cases i <;> simp [turbineFlux] <;> fun_prop
  · exact contDiffOn_const
  · exact integrableOn_zero
  · exact integrableOn_const (by simp [Real.volume_Icc_pi]) (by simp)
  · intro x _
    have h := fixture_turbine_law t x
    simpa using h
  · intro y _
    simpa using (fixture_turbine_ports y).1
  · intro y _
    simpa using (fixture_turbine_ports y).2
  · intro i hi y _
    fin_cases i
    · exact absurd rfl hi
    · simp [turbineFlux]
    · simp [turbineFlux]

/-- **Nonzero energy transfer**: the turbine delivers `Ẇ_out = 1800` from `ṁ θ_in = 3004` and
`ṁ θ_out = 1204` with `ṁ = 2`, `Q̇ = 0` and zero storage rate. -/
example :
    ProcessPorts.workOut (∫ _ in Icc (0 : Fin 3 → ℝ) 1, (-1800 : ℝ)) = 1800 ∧
      faceArea (0 : Fin 3 → ℝ) 1 0 = 1 ∧
      2 * (specificEnthalpy 1000 500 1 + ![(2 : ℝ), 0, 0] ⬝ᵥ ![2, 0, 0] / 2) = 3004 ∧
      2 * (specificEnthalpy 400 200 1 + ![(2 : ℝ), 0, 0] ⬝ᵥ ![2, 0, 0] / 2) = 1204 ∧
      (0 : ℝ) - 1800 + 3004 - 1204 = 0 := by
  have hvol : volume.real (Icc (0 : Fin 3 → ℝ) 1) = 1 := by
    rw [measureReal_def,
      Real.volume_Icc_pi_toReal (show (0 : Fin 3 → ℝ) ≤ 1 from fun i => zero_le_one)]
    simp
  refine ⟨?_, ?_, ?_, ?_, by norm_num⟩
  · rw [setIntegral_const, smul_eq_mul, hvol]; unfold ProcessPorts.workOut; norm_num
  · simp [faceArea]
  · simp [specificEnthalpy, dotProduct, Fin.sum_univ_three]; norm_num
  · simp [specificEnthalpy, dotProduct, Fin.sum_univ_three]; norm_num

/-- **Flow work counted twice** breaks the turbine balance: with `p / ρ` added again at both
ports the right-hand side becomes `600`, not the zero storage rate. -/
example :
    (0 : ℝ) - 1800 + 2 * (specificEnthalpy 1000 500 1 + 500 / 1 + 2) -
        2 * (specificEnthalpy 400 200 1 + 200 / 1 + 2) = 600 := by
  simp [specificEnthalpy]
  norm_num

/-- **A steady balance cannot erase nonzero storage**: with `E = t` and `ẇ = -1799` the same
ports give the storage rate `1`, so the right-hand side `Q̇ - Ẇ_out + inflow - outflow` is `1`,
not `0`. -/
example (t : ℝ) :
    HasDerivAt (fun τ => ∫ _ in Icc (0 : Fin 3 → ℝ) 1, τ)
        (0 - ProcessPorts.workOut (∫ _ in Icc (0 : Fin 3 → ℝ) 1, (-1799 : ℝ)) + 3004 - 1204) t ∧
      (0 - ProcessPorts.workOut (∫ _ in Icc (0 : Fin 3 → ℝ) 1, (-1799 : ℝ)) + 3004 - 1204 : ℝ) ≠
        0 := by
  have hvol : volume.real (Icc (0 : Fin 3 → ℝ) 1) = 1 := by
    rw [measureReal_def,
      Real.volume_Icc_pi_toReal (show (0 : Fin 3 → ℝ) ≤ 1 from fun i => zero_le_one)]
    simp
  have hrhs : (0 - ProcessPorts.workOut (∫ _ in Icc (0 : Fin 3 → ℝ) 1, (-1799 : ℝ)) + 3004 - 1204 :
      ℝ) = 1 := by
    rw [setIntegral_const, smul_eq_mul, hvol]; unfold ProcessPorts.workOut; norm_num
  refine ⟨?_, by rw [hrhs]; norm_num⟩
  rw [hrhs]
  have hf : (fun τ : ℝ => ∫ _ in Icc (0 : Fin 3 → ℝ) 1, τ) = fun τ => τ := by
    funext τ; rw [setIntegral_const, smul_eq_mul, hvol, one_mul]
  rw [hf]
  exact hasDerivAt_id t

/-- The port lemmas at the turbine inlet `x₀ = 0`, whose outward normal is `-e₀`: the fluid
velocity `2 e₀` gives the outward normal velocity `v_n = -2`, so the signed outward rate is
`ṁ θ = -3004` (an inflow of `3004`), and counting `p / ρ` twice adds the signed pressure power
`1 * (-2) * 500`. -/
example :
    portEnergyRate 1 1 (-2) 1000 500 (981 / 100) 0 ![(2 : ℝ), 0, 0] = -3004 ∧
      portEnergyRate 1 1 (-2) 1000 500 (981 / 100) 0 ![(2 : ℝ), 0, 0] =
        1 * 1 * (-2) * (specificEnthalpy 1000 500 1 + ![(2 : ℝ), 0, 0] ⬝ᵥ ![2, 0, 0] / 2 +
          981 / 100 * 0) ∧
      1 * 1 * (-2) * (specificEnthalpy 1000 500 1 + 500 / 1 + ![(2 : ℝ), 0, 0] ⬝ᵥ ![2, 0, 0] / 2 +
          981 / 100 * 0) =
        portEnergyRate 1 1 (-2) 1000 500 (981 / 100) 0 ![(2 : ℝ), 0, 0] + 1 * (-2) * 500 := by
  refine ⟨?_, portEnergyRate_eq_massFlow one_ne_zero 1 (-2) 1000 500 (981 / 100) 0 ![2, 0, 0],
    flowWork_double_count one_ne_zero 1 (-2) 1000 500 (981 / 100) 0 ![2, 0, 0]⟩
  simp [portEnergyRate, dotProduct, Fin.sum_univ_three]
  norm_num


/-! ## D. Momentum ports of pressure-driven channels -/

/-- Directional derivative of an affine function of one coordinate. -/
private lemma fderiv_affine_apply {n : ℕ} (c d : ℝ) (k i : Fin (n + 1)) (x : Fin (n + 1) → ℝ) :
    fderiv ℝ (fun y : Fin (n + 1) → ℝ => c + d * y k) x (Pi.single i 1) =
      d * (Pi.single i (1 : ℝ) : Fin (n + 1) → ℝ) k := by
  have h0 : HasFDerivAt (fun y : Fin (n + 1) → ℝ => y k)
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (n + 1) => ℝ) k) x :=
    hasFDerivAt_apply k x
  have h := (h0.const_mul d).const_add c
  rw [h.fderiv]
  simp

/-- The unit square has unit volume. -/
private lemma volume_real_unitSquare : volume.real (Icc (0 : Fin 2 → ℝ) 1) = 1 := by
  rw [measureReal_def,
    Real.volume_Icc_pi_toReal (show (0 : Fin 2 → ℝ) ≤ 1 from fun i => zero_le_one)]
  simp

/-- Stress field of the channel fixture on the unit square, per unit depth: the normal stress
`σ₀₀ = -(2 - x₀)` along the channel (the pressure `p = 2 - x₀` falling from `2` at the inlet to
`1` at the outlet), the normal stress `σ₁₁ = -(2 - x₁)` across it, and no shear. -/
def channelStress (x : Fin 2 → ℝ) : Fin 2 → Fin 2 → ℝ :=
  ![![-(2 - x 0), 0], ![0, -(2 - x 1)]]

/-- **A pressure-driven flow with a wall reaction** satisfies the pressure-only two-port balance:
on the unit square, density `1`, uniform velocity `(1 + t, 0)`, the stress `channelStress` and the
weight `f = (0, -1)`. The inlet pressure is `2`, the outlet pressure `1`, and the walls `x₁ = 0`,
`x₁ = 1` are impermeable. -/
example (t : ℝ) :
    HasDerivAt (fun τ => fun j => ∫ _ in Icc (0 : Fin 2 → ℝ) 1, (1 : ℝ) * ![1 + τ, 0] j)
      ((1 * faceArea (0 : Fin 2 → ℝ) 1 0 * ![1 + t, 0] 0) • ![1 + t, 0] -
          (1 * faceArea (0 : Fin 2 → ℝ) 1 0 * ![1 + t, 0] 0) • ![1 + t, 0] -
          ((2 * faceArea (0 : Fin 2 → ℝ) 1 0) • -(Pi.single 0 1 : Fin 2 → ℝ) +
            (1 * faceArea (0 : Fin 2 → ℝ) 1 0) • (Pi.single 0 1 : Fin 2 → ℝ)) +
          (fun j => ∫ _ in Icc (0 : Fin 2 → ℝ) 1, ![(0 : ℝ), -1] j) +
        ∑ i : Fin 1, faceTractionResultant (0 : Fin 2 → ℝ) 1 channelStress i.succ) t := by
  refine hasDerivAt_momentum_twoPort (ρ := fun _ _ => 1) (v := fun τ _ => ![1 + τ, 0])
    (σ := fun _ => channelStress) (f := fun _ _ => ![0, -1]) (U := univ)
    (fun i => by simp) isOpen_univ (subset_univ _) ?_ ?_ ?_
    (fun _ => integrableOn_const isCompact_Icc.measure_lt_top.ne) ?_
    (fun _ _ => rfl) (fun _ _ => rfl) ?_ (fun _ _ => rfl) (fun _ _ => rfl) ?_ ?_
  · exact contDiff_const
  · refine contDiff_pi.2 fun i => ?_
    fin_cases i
    · simp only [Function.uncurry, Fin.zero_eta, Matrix.cons_val_zero]
      fun_prop
    · simp only [Function.uncurry, Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_fin_one]
      fun_prop
  · refine ContDiff.contDiffOn (contDiff_pi.2 fun j => contDiff_pi.2 fun i => ?_)
    fin_cases j <;> fin_cases i <;>
      simp only [channelStress, Fin.zero_eta, Fin.mk_one, Fin.isValue, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val_fin_one] <;>
      fun_prop
  · intro j x _
    fin_cases j
    · have hd : deriv (fun τ : ℝ => (1 : ℝ) * ![1 + τ, 0] 0) t = 1 := by simp
      have hF0 : (fun y => momentumFlux (fun _ => 1) (fun _ => ![1 + t, 0]) channelStress 0 y 0) =
          fun y : Fin 2 → ℝ => ((1 + t) * (1 + t) + 2) + (-1) * y 0 := by
        funext y
        simp [momentumFlux, channelStress]
        ring
      have hF1 : (fun y => momentumFlux (fun _ => 1) (fun _ => ![1 + t, 0]) channelStress 0 y 1) =
          fun y : Fin 2 → ℝ => 0 + 0 * y 0 := by
        funext y
        simp [momentumFlux, channelStress]
      simp only [Fin.zero_eta] at hd ⊢
      rw [hd]
      unfold divergence MathlibExt.Probability.FokkerPlanck.pderiv
      rw [Fin.sum_univ_two, hF0, hF1, fderiv_affine_apply, fderiv_affine_apply]
      simp
    · have hd : deriv (fun τ : ℝ => (1 : ℝ) * ![1 + τ, 0] 1) t = 0 := by simp
      have hF0 : (fun y => momentumFlux (fun _ => 1) (fun _ => ![1 + t, 0]) channelStress 1 y 0) =
          fun y : Fin 2 → ℝ => 0 + 0 * y 0 := by
        funext y
        simp [momentumFlux, channelStress]
      have hF1 : (fun y => momentumFlux (fun _ => 1) (fun _ => ![1 + t, 0]) channelStress 1 y 1) =
          fun y : Fin 2 → ℝ => 2 + (-1) * y 1 := by
        funext y
        simp [momentumFlux, channelStress]
        ring
      simp only [Fin.mk_one] at hd ⊢
      rw [hd]
      unfold divergence MathlibExt.Probability.FokkerPlanck.pderiv
      rw [Fin.sum_univ_two, hF0, hF1, fderiv_affine_apply, fderiv_affine_apply]
      simp
  · intro y _
    funext j
    fin_cases j <;> norm_num [channelStress]
  · intro y _
    funext j
    fin_cases j <;> norm_num [channelStress]
  · intro i hi y _
    fin_cases i
    · exact absurd rfl hi
    · simp

/-- The terms of the channel balance: the port momentum fluxes cancel, the pressure difference
pushes with `(1, 0)`, the weight is `(0, -1)`, and the walls react with the nonzero force `(0, 1)`
(the bottom wall at pressure `2` against the top wall at `1`). The momentum `(1 + t, 0)` grows at
the predicted rate `(1, 0)`. -/
lemma fixture_channel_values (t : ℝ) :
    ∑ i : Fin 1, faceTractionResultant (0 : Fin 2 → ℝ) 1 channelStress i.succ = ![0, 1] ∧
      (fun j => ∫ _ in Icc (0 : Fin 2 → ℝ) 1, ![(0 : ℝ), -1] j) = ![0, -1] ∧
      -((2 * faceArea (0 : Fin 2 → ℝ) 1 0) • -(Pi.single 0 1 : Fin 2 → ℝ) +
          (1 * faceArea (0 : Fin 2 → ℝ) 1 0) • (Pi.single 0 1 : Fin 2 → ℝ)) = ![1, 0] ∧
      HasDerivAt (fun τ => fun j => ∫ _ in Icc (0 : Fin 2 → ℝ) 1, (1 : ℝ) * ![1 + τ, 0] j)
        ![1, 0] t := by
  have hA : faceArea (0 : Fin 2 → ℝ) 1 0 = 1 := by simp [faceArea]
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hvol : volume.real (Icc (0 : Fin 1 → ℝ) 1) = 1 := by
      rw [measureReal_def,
        Real.volume_Icc_pi_toReal (show (0 : Fin 1 → ℝ) ≤ 1 from fun k => zero_le_one)]
      simp
    rw [Fin.sum_univ_one]
    funext j
    unfold faceTractionResultant
    fin_cases j
    · simp [channelStress]
    · norm_num [channelStress, hvol]
  · funext j
    rw [setIntegral_const, volume_real_unitSquare, one_smul]
  · rw [hA]
    funext j
    fin_cases j <;> norm_num
  · have hf : (fun τ => fun j => ∫ _ in Icc (0 : Fin 2 → ℝ) 1, (1 : ℝ) * ![1 + τ, 0] j) =
        fun τ => ![1 + τ, 0] := by
      funext τ j
      rw [setIntegral_const, volume_real_unitSquare, one_smul, one_mul]
    rw [hf]
    refine hasDerivAt_pi.2 fun j => ?_
    fin_cases j
    · simpa using (hasDerivAt_id t).const_add (1 : ℝ)
    · simpa using hasDerivAt_const t (0 : ℝ)

/-- **Changing a normal orientation without changing the flux sign fails**: taking the inlet's
outward normal as `+e₀` (the flow direction) while keeping `-p A n` turns the pressure term into
`(-3, 0)`, and the channel's momentum rate `(1, 0)` refutes the resulting balance. -/
example (t : ℝ) :
    ¬ HasDerivAt (fun τ => fun j => ∫ _ in Icc (0 : Fin 2 → ℝ) 1, (1 : ℝ) * ![1 + τ, 0] j)
      ((1 * faceArea (0 : Fin 2 → ℝ) 1 0 * ![1 + t, 0] 0) • ![1 + t, 0] -
          (1 * faceArea (0 : Fin 2 → ℝ) 1 0 * ![1 + t, 0] 0) • ![1 + t, 0] -
          ((2 * faceArea (0 : Fin 2 → ℝ) 1 0) • (Pi.single 0 1 : Fin 2 → ℝ) +
            (1 * faceArea (0 : Fin 2 → ℝ) 1 0) • (Pi.single 0 1 : Fin 2 → ℝ)) +
          (fun j => ∫ _ in Icc (0 : Fin 2 → ℝ) 1, ![(0 : ℝ), -1] j) +
        ∑ i : Fin 1, faceTractionResultant (0 : Fin 2 → ℝ) 1 channelStress i.succ) t := by
  intro h
  obtain ⟨hW, hB, -, hP⟩ := fixture_channel_values t
  have h2 := congrFun (hP.unique h) 0
  have hA : faceArea (0 : Fin 2 → ℝ) 1 0 = 1 := by simp [faceArea]
  rw [hW, hB, hA] at h2
  norm_num [Matrix.vecHead] at h2


/-- Stress field of the viscous channel fixture on the unit square, per unit depth: the normal
stresses of `channelStress` and the symmetric shear stress `σ₀₁ = σ₁₀ = 1 + 2 x₀`, which grows
along the channel. On a surface of unit normal `+e₀` its viscous traction is `(0, 1 + 2 x₀)`:
`τ_in = (0, 1)` on the inlet face `x₀ = 0` and `τ_out = (0, 3)` on the outlet face `x₀ = 1`. -/
def viscousChannelStress (x : Fin 2 → ℝ) : Fin 2 → Fin 2 → ℝ :=
  ![![-(2 - x 0), 1 + 2 * x 0], ![1 + 2 * x 0, -(2 - x 1)]]

/-- **Nonzero viscous port tractions**: the channel with density `1`, velocity `(1 + t, 0)`, the
stress `viscousChannelStress` and the body force `(0, -3)` is an instance of
`hasDerivAt_momentum_twoPort_viscous`, with the inlet pressure `2` and viscous traction
`τ_in = (0, 1)` and the outlet pressure `1` and viscous traction `τ_out = (0, 3)`. -/
lemma fixture_viscousChannel_balance (t : ℝ) :
    HasDerivAt (fun τ => fun j => ∫ _ in Icc (0 : Fin 2 → ℝ) 1, (1 : ℝ) * ![1 + τ, 0] j)
      ((1 * faceArea (0 : Fin 2 → ℝ) 1 0 * ![1 + t, 0] 0) • ![1 + t, 0] -
          (1 * faceArea (0 : Fin 2 → ℝ) 1 0 * ![1 + t, 0] 0) • ![1 + t, 0] -
          ((2 * faceArea (0 : Fin 2 → ℝ) 1 0) • -(Pi.single 0 1 : Fin 2 → ℝ) +
            (1 * faceArea (0 : Fin 2 → ℝ) 1 0) • (Pi.single 0 1 : Fin 2 → ℝ)) +
          (fun j => ∫ _ in Icc (0 : Fin 2 → ℝ) 1, ![(0 : ℝ), -3] j) +
          ∑ i : Fin 1, faceTractionResultant (0 : Fin 2 → ℝ) 1 viscousChannelStress i.succ +
        faceArea (0 : Fin 2 → ℝ) 1 0 • (![(0 : ℝ), 3] - ![0, 1])) t := by
  refine hasDerivAt_momentum_twoPort_viscous (ρ := fun _ _ => 1) (v := fun τ _ => ![1 + τ, 0])
    (σ := fun _ => viscousChannelStress) (f := fun _ _ => ![0, -3]) (U := univ)
    (fun i => by simp) isOpen_univ (subset_univ _) ?_ ?_ ?_
    (fun _ => integrableOn_const isCompact_Icc.measure_lt_top.ne) ?_
    (fun _ _ => rfl) (fun _ _ => rfl) ?_ (fun _ _ => rfl) (fun _ _ => rfl) ?_ ?_
  · exact contDiff_const
  · refine contDiff_pi.2 fun i => ?_
    fin_cases i
    · simp only [Function.uncurry, Fin.zero_eta, Matrix.cons_val_zero]
      fun_prop
    · simp only [Function.uncurry, Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_fin_one]
      fun_prop
  · refine ContDiff.contDiffOn (contDiff_pi.2 fun j => contDiff_pi.2 fun i => ?_)
    fin_cases j <;> fin_cases i <;>
      simp only [viscousChannelStress, Fin.zero_eta, Fin.mk_one, Fin.isValue,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one] <;>
      fun_prop
  · intro j x _
    fin_cases j
    · have hd : deriv (fun τ : ℝ => (1 : ℝ) * ![1 + τ, 0] 0) t = 1 := by simp
      have hF0 : (fun y => momentumFlux (fun _ => 1) (fun _ => ![1 + t, 0]) viscousChannelStress 0
          y 0) = fun y : Fin 2 → ℝ => ((1 + t) * (1 + t) + 2) + (-1) * y 0 := by
        funext y
        simp [momentumFlux, viscousChannelStress]
        ring
      have hF1 : (fun y => momentumFlux (fun _ => 1) (fun _ => ![1 + t, 0]) viscousChannelStress 0
          y 1) = fun y : Fin 2 → ℝ => -1 + (-2) * y 0 := by
        funext y
        simp [momentumFlux, viscousChannelStress]
        ring
      simp only [Fin.zero_eta] at hd ⊢
      rw [hd]
      unfold divergence MathlibExt.Probability.FokkerPlanck.pderiv
      rw [Fin.sum_univ_two, hF0, hF1, fderiv_affine_apply, fderiv_affine_apply]
      simp
    · have hd : deriv (fun τ : ℝ => (1 : ℝ) * ![1 + τ, 0] 1) t = 0 := by simp
      have hF0 : (fun y => momentumFlux (fun _ => 1) (fun _ => ![1 + t, 0]) viscousChannelStress 1
          y 0) = fun y : Fin 2 → ℝ => -1 + (-2) * y 0 := by
        funext y
        simp [momentumFlux, viscousChannelStress]
        ring
      have hF1 : (fun y => momentumFlux (fun _ => 1) (fun _ => ![1 + t, 0]) viscousChannelStress 1
          y 1) = fun y : Fin 2 → ℝ => 2 + (-1) * y 1 := by
        funext y
        simp [momentumFlux, viscousChannelStress]
        ring
      simp only [Fin.mk_one] at hd ⊢
      rw [hd]
      unfold divergence MathlibExt.Probability.FokkerPlanck.pderiv
      rw [Fin.sum_univ_two, hF0, hF1, fderiv_affine_apply, fderiv_affine_apply]
      norm_num
  · intro y _
    funext j
    fin_cases j <;> norm_num [viscousChannelStress]
  · intro y _
    funext j
    fin_cases j <;> norm_num [viscousChannelStress]
  · intro i hi y _
    fin_cases i
    · exact absurd rfl hi
    · simp

/-- The terms of the viscous channel balance: the shear stresses on the two walls cancel, so the
walls react with `(0, 1)` as in the inviscid channel; the body force is `(0, -3)`; and the viscous
port term is `A₀ (τ_out - τ_in) = (0, 3) - (0, 1) = (0, 2)`, the outlet face (outward normal `+e₀`)
carrying `τ_out` and the inlet face (outward normal `-e₀`) carrying `-τ_in`. -/
lemma fixture_viscousChannel_values :
    ∑ i : Fin 1, faceTractionResultant (0 : Fin 2 → ℝ) 1 viscousChannelStress i.succ = ![0, 1] ∧
      (fun j => ∫ _ in Icc (0 : Fin 2 → ℝ) 1, ![(0 : ℝ), -3] j) = ![0, -3] ∧
      faceArea (0 : Fin 2 → ℝ) 1 0 • (![(0 : ℝ), 3] - ![0, 1]) = ![0, 2] := by
  have hA : faceArea (0 : Fin 2 → ℝ) 1 0 = 1 := by simp [faceArea]
  have hvol : volume.real (Icc (0 : Fin 1 → ℝ) 1) = 1 := by
    rw [measureReal_def,
      Real.volume_Icc_pi_toReal (show (0 : Fin 1 → ℝ) ≤ 1 from fun k => zero_le_one)]
    simp
  have hins : ∀ (c : ℝ) (y : Fin 1 → ℝ), (Fin.insertNth (1 : Fin 2) c y : Fin 2 → ℝ) 0 = y 0 :=
    fun _ _ => rfl
  refine ⟨?_, ?_, ?_⟩
  · rw [Fin.sum_univ_one]
    funext j
    unfold faceTractionResultant
    fin_cases j
    · simp [viscousChannelStress, hins]
    · norm_num [viscousChannelStress, hvol]
  · funext j
    rw [setIntegral_const, volume_real_unitSquare, one_smul]
  · rw [hA, one_smul]
    funext j
    fin_cases j <;> norm_num

/-- **The viscous balance predicts the directly computed rate**: the pressure term `(1, 0)`, the
body force `(0, -3)`, the wall reaction `(0, 1)` and the viscous term `(0, 2)` add up to `(1, 0)`,
the derivative of the momentum `(1 + t, 0)` computed without any balance law. -/
example (t : ℝ) :
    ((1 * faceArea (0 : Fin 2 → ℝ) 1 0 * ![1 + t, 0] 0) • ![1 + t, 0] -
        (1 * faceArea (0 : Fin 2 → ℝ) 1 0 * ![1 + t, 0] 0) • ![1 + t, 0] -
        ((2 * faceArea (0 : Fin 2 → ℝ) 1 0) • -(Pi.single 0 1 : Fin 2 → ℝ) +
          (1 * faceArea (0 : Fin 2 → ℝ) 1 0) • (Pi.single 0 1 : Fin 2 → ℝ)) +
        (fun j => ∫ _ in Icc (0 : Fin 2 → ℝ) 1, ![(0 : ℝ), -3] j) +
        ∑ i : Fin 1, faceTractionResultant (0 : Fin 2 → ℝ) 1 viscousChannelStress i.succ +
      faceArea (0 : Fin 2 → ℝ) 1 0 • (![(0 : ℝ), 3] - ![0, 1])) = ![1, 0] ∧
      HasDerivAt (fun τ => fun j => ∫ _ in Icc (0 : Fin 2 → ℝ) 1, (1 : ℝ) * ![1 + τ, 0] j)
        ![1, 0] t := by
  obtain ⟨hW, hB, hV⟩ := fixture_viscousChannel_values
  obtain ⟨-, -, hP, hD⟩ := fixture_channel_values t
  refine ⟨?_, hD⟩
  rw [hW, hB, hV, sub_self, zero_sub, hP]
  funext j
  fin_cases j <;> norm_num

/-- **The inlet sign of the viscous term matters**: with the inlet's viscous traction counted as
`+τ_in`, that is `A₀ (τ_out + τ_in)` in place of `A₀ (τ_out - τ_in)`, the predicted rate is
`(1, 2)`, which the momentum rate `(1, 0)` refutes. -/
example (t : ℝ) :
    ¬ HasDerivAt (fun τ => fun j => ∫ _ in Icc (0 : Fin 2 → ℝ) 1, (1 : ℝ) * ![1 + τ, 0] j)
      ((1 * faceArea (0 : Fin 2 → ℝ) 1 0 * ![1 + t, 0] 0) • ![1 + t, 0] -
          (1 * faceArea (0 : Fin 2 → ℝ) 1 0 * ![1 + t, 0] 0) • ![1 + t, 0] -
          ((2 * faceArea (0 : Fin 2 → ℝ) 1 0) • -(Pi.single 0 1 : Fin 2 → ℝ) +
            (1 * faceArea (0 : Fin 2 → ℝ) 1 0) • (Pi.single 0 1 : Fin 2 → ℝ)) +
          (fun j => ∫ _ in Icc (0 : Fin 2 → ℝ) 1, ![(0 : ℝ), -3] j) +
          ∑ i : Fin 1, faceTractionResultant (0 : Fin 2 → ℝ) 1 viscousChannelStress i.succ +
        faceArea (0 : Fin 2 → ℝ) 1 0 • (![(0 : ℝ), 3] + ![0, 1])) t := by
  intro h
  obtain ⟨hW, hB, -⟩ := fixture_viscousChannel_values
  obtain ⟨-, -, -, hD⟩ := fixture_channel_values t
  have h2 := congrFun (hD.unique h) 1
  have hA : faceArea (0 : Fin 2 → ℝ) 1 0 = 1 := by simp [faceArea]
  rw [hW, hB, hA] at h2
  norm_num [Matrix.vecHead, Matrix.vecTail] at h2

end PhyslibExtTest.ContinuumMechanics.ControlVolumes

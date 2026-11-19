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

## i. Overview

These are elaboration and non-vacuity checks, not new results.

## ii. Key results

No new results are introduced here. Sections B and C name the
fixture steps that later ones reuse; section C defines the turbine
flux it checks.

## iii. Table of contents

- A. Linear field with unit-speed endpoint
- B. Growing storage in a fixed box and the reversed normal
- C. Energy ports of a steady turbine

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

/-- The turbine is an instance of the two-port balance, with zero storage rate. -/
example (t : ℝ) :
    HasDerivAt (fun _ : ℝ => ∫ _ in Icc (0 : Fin 3 → ℝ) 1, (1 : ℝ))
      (((∫ _ in Icc (0 : Fin 3 → ℝ) 1, (0 : ℝ)) -
            boxOutwardFlux (0 : Fin 3 → ℝ) 1 (fun _ => 0)) -
          ProcessPorts.workOut (∫ _ in Icc (0 : Fin 3 → ℝ) 1, (-1800 : ℝ)) +
        1 * faceArea (0 : Fin 3 → ℝ) 1 0 * 2 *
          (specificEnthalpy 1000 500 1 + ![(2 : ℝ), 0, 0] ⬝ᵥ ![2, 0, 0] / 2 + 981 / 100 * 0) -
        1 * faceArea (0 : Fin 3 → ℝ) 1 0 * 2 *
          (specificEnthalpy 400 200 1 + ![(2 : ℝ), 0, 0] ⬝ᵥ ![2, 0, 0] / 2 + 981 / 100 * 0)) t := by
  refine hasDerivAt_energy_twoPort (E := fun _ _ => 1) (G := fun _ => turbineFlux)
    (J := fun _ _ => 0) (qdot := fun _ _ => 0) (wdot := fun _ _ => -1800)
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

/-- The port lemmas at the turbine inlet: the inlet rate is `ṁ θ_in` with `ṁ = 2`, and counting
`p / ρ` twice adds the pressure power `2 * 500`. -/
example :
    portEnergyRate 1 1 2 1000 500 (981 / 100) 0 ![(2 : ℝ), 0, 0] =
        1 * 1 * 2 * (specificEnthalpy 1000 500 1 + ![(2 : ℝ), 0, 0] ⬝ᵥ ![2, 0, 0] / 2 +
          981 / 100 * 0) ∧
      1 * 1 * 2 * (specificEnthalpy 1000 500 1 + 500 / 1 + ![(2 : ℝ), 0, 0] ⬝ᵥ ![2, 0, 0] / 2 +
          981 / 100 * 0) =
        portEnergyRate 1 1 2 1000 500 (981 / 100) 0 ![(2 : ℝ), 0, 0] + 1 * 2 * 500 :=
  ⟨portEnergyRate_eq_massFlow one_ne_zero 1 2 1000 500 (981 / 100) 0 ![2, 0, 0],
    flowWork_double_count one_ne_zero 1 2 1000 500 (981 / 100) 0 ![2, 0, 0]⟩

end PhyslibExtTest.ContinuumMechanics.ControlVolumes

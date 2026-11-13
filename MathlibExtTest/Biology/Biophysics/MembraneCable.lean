/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Biology.Biophysics.MembraneCable

/-! Tests for the Nernst potential and the steady-state passive cable: concrete Nernst values and
signs, a Boltzmann profile witnessing the zero-flux hypotheses, concrete length constants, and
non-vacuity witnesses for the semi-infinite and sealed-end boundary conditions. -/

open Real Set

namespace MathlibExtTest.Biology.Biophysics.MembraneCable

open MathlibExt.Biology.Biophysics.MembraneCable

/-! ### Nernst potential -/

/-- Unit constants and a concentration ratio `e`: `E = 1`. -/
example : nernstPotential 1 1 1 1 1 (exp 1) = 1 := by simp [nernstPotential]

/-- Equal concentrations: no equilibrium voltage. -/
example : nernstPotential 8 310 1 96485 140 140 = 0 := nernstPotential_self _ _ _ _ _

/-- A cation more concentrated outside (`c_in = 12 < c_out = 145`) has a positive Nernst
potential. -/
example : 0 < nernstPotential 8 310 1 96485 12 145 :=
  (nernstPotential_pos_iff (by norm_num) (by norm_num) (by norm_num) (by norm_num)).2
    (by norm_num)

/-- A cation more concentrated inside (`c_in = 140 > c_out = 5`) has a negative Nernst potential;
reversing the valence (an anion) flips the sign back. -/
example : nernstPotential 8 310 1 96485 140 5 < 0 ∧ 0 < nernstPotential 8 310 (-1) 96485 140 5 := by
  have h : 0 < nernstPotential 8 310 1 96485 5 140 :=
    (nernstPotential_pos_iff (by norm_num) (by norm_num) (by norm_num) (by norm_num)).2
      (by norm_num)
  rw [nernstPotential_swap] at h
  refine ⟨by linarith, ?_⟩
  rw [nernstPotential_neg_valence]; linarith

/-- At the Nernst potential the electrochemical potentials agree (non-vacuity of
`electrochemicalPotential_eq_iff`). -/
example (μ₀ : ℝ) :
    electrochemicalPotential 8 310 1 96485 μ₀ 140 (nernstPotential 8 310 1 96485 140 5) =
      electrochemicalPotential 8 310 1 96485 μ₀ 5 0 :=
  (electrochemicalPotential_eq_iff (by norm_num) (by norm_num) (by norm_num)).2 (sub_zero _)

/-- Boltzmann form at unit constants: the concentration ratio is `exp E`. -/
example : (5 : ℝ) / 140 = exp (nernstPotential 1 1 1 1 140 5) := by
  simpa using div_eq_exp_nernstPotential (R := 1) (T := 1) (z := 1) (F := 1)
    (by norm_num) (by norm_num) (by norm_num : (0 : ℝ) < 140) (by norm_num : (0 : ℝ) < 5)

/-- Non-vacuity of the zero-flux derivation: with unit constants, the Boltzmann profile
`c x = e^{-x}`, `φ x = x` on `[0, 1]` carries zero Nernst–Planck flux, so the membrane voltage
`φ 0 - φ 1 = -1` is the Nernst potential of `c 0 = 1`, `c 1 = e⁻¹`. -/
example : (0 : ℝ) - 1 = nernstPotential 1 1 1 1 1 (exp (-1)) := by
  have h := sub_eq_nernstPotential_of_flux_eq_zero (D := 1) (R := 1) (T := 1) (z := 1) (F := 1)
    (L := 1) (c := fun x ↦ exp (-x)) (c' := fun x ↦ -exp (-x)) (φ := id) (φ' := fun _ ↦ 1)
    one_ne_zero (by norm_num) (by norm_num) zero_le_one (fun x _ ↦ exp_pos _)
    (fun x _ ↦ by simpa using ((hasDerivAt_neg x).exp).hasDerivWithinAt)
    (fun x _ ↦ (hasDerivAt_id x).hasDerivWithinAt)
    (fun x _ ↦ by simp [nernstPlanckFlux])
  simpa using h

/-! ### Passive cable -/

private lemma lengthConstant_four_one : lengthConstant 4 1 = 2 := by
  rw [lengthConstant, div_one, show (4 : ℝ) = 2 ^ 2 by norm_num, sqrt_sq zero_le_two]

private lemma charResistance_four_one : charResistance 4 1 = 2 := by
  rw [charResistance, mul_one, show (4 : ℝ) = 2 ^ 2 by norm_num, sqrt_sq zero_le_two]

/-- `rm = 4`, `ri = 1`: `λ = 2` and `r∞ = 2`. -/
example : lengthConstant 4 1 = 2 ∧ charResistance 4 1 = 2 :=
  ⟨lengthConstant_four_one, charResistance_four_one⟩

/-- `rm = 9`, `ri = 4`: `λ² = 9 / 4` and `r∞ = ri λ`. -/
example : lengthConstant 9 4 ^ 2 = 9 / 4 ∧ charResistance 9 4 = 4 * lengthConstant 9 4 :=
  ⟨lengthConstant_sq (by norm_num) (by norm_num), charResistance_eq (by norm_num) (by norm_num)⟩

/-- The transfer-form solution starts from the prescribed voltage and current. -/
example (V₀ I₀ : ℝ) : cableVoltage 4 1 V₀ I₀ 0 = V₀ ∧ cableCurrent 4 1 V₀ I₀ 0 = I₀ := by
  simp [cableVoltage, cableCurrent]

/-- Non-vacuity of the semi-infinite boundary condition: inject `I₀ = 3` into a cable with
`rm = 4`, `ri = 1`; `V x = 6 e^{-x/2}`, `I x = 3 e^{-x/2}` is a bounded steady state on `[0, ∞)`,
and the theorem recovers `V x = r∞ I₀ e^{-x/λ}`. -/
example {x : ℝ} (hx : 0 ≤ x) :
    IsSteadyState 4 1 (Ici 0) (fun x ↦ 6 * exp (-(x / 2))) (fun x ↦ 3 * exp (-(x / 2))) ∧
      (fun x ↦ 6 * exp (-(x / 2))) x =
        charResistance 4 1 * 3 * exp (-(x / lengthConstant 4 1)) := by
  have hV : (fun x ↦ 6 * exp (-(x / 2))) = cableVoltage 4 1 (charResistance 4 1 * 3) 3 := by
    funext y
    rw [cableVoltage_charResistance_mul, charResistance_four_one, lengthConstant_four_one]; ring
  have hI : (fun x ↦ 3 * exp (-(x / 2))) = cableCurrent 4 1 (charResistance 4 1 * 3) 3 := by
    funext y
    rw [cableCurrent_charResistance_mul (by norm_num) (by norm_num), lengthConstant_four_one]
  have hss : IsSteadyState 4 1 (Ici 0) (fun x ↦ 6 * exp (-(x / 2)))
      (fun x ↦ 3 * exp (-(x / 2))) := by
    rw [hV, hI]; exact isSteadyState_cable (by norm_num) (by norm_num) _ _ _
  refine ⟨hss, hss.voltage_eq_of_current_injection (by norm_num) (by norm_num) ⟨6, fun y hy ↦ ?_⟩
    (by simp) hx⟩
  have : exp (-(y / 2)) ≤ 1 := exp_le_one_iff.2 (by linarith)
  rw [abs_of_pos (by positivity)]; linarith

/-- Length-constant derivation at `rm = 4`, `ri = 1`: the decay rate `1/2` gives a steady state,
the decay rate `1` does not. -/
example : (∃ I, IsSteadyState 4 1 univ (fun x ↦ 5 * exp (-(1 / 2 * x))) I) ∧
    ¬ ∃ I, IsSteadyState 4 1 univ (fun x ↦ 5 * exp (-(1 * x))) I := by
  constructor
  · refine (exists_isSteadyState_exp_iff (by norm_num) (by norm_num) (by norm_num)
      (by norm_num)).2 ?_
    rw [lengthConstant_four_one]; norm_num
  · rw [exists_isSteadyState_exp_iff (by norm_num) (by norm_num) (by norm_num) (by norm_num),
      lengthConstant_four_one]
    norm_num

/-- Non-vacuity of the sealed-end boundary condition: with `rm = 4`, `ri = 1`, `L = 1` and
injected current `I₀ = 1`, choosing `V₀ = 2 cosh (1/2) / sinh (1/2)` gives a steady state on
`[0, 1]` with `I 1 = 0`, whose end voltage is `V₀ / cosh (1/2)`. -/
example :
    let V₀ := 2 * cosh (1 / 2) / sinh (1 / 2)
    IsSteadyState 4 1 (Icc 0 1) (cableVoltage 4 1 V₀ 1) (cableCurrent 4 1 V₀ 1) ∧
      cableCurrent 4 1 V₀ 1 1 = 0 ∧
      cableVoltage 4 1 V₀ 1 1 = V₀ / cosh (1 / 2) := by
  intro V₀
  have hss := isSteadyState_cable (rm := 4) (ri := 1) (by norm_num) (by norm_num) (Icc 0 1) V₀ 1
  have hs : sinh (1 / 2 : ℝ) ≠ 0 := (sinh_pos_iff.2 (by norm_num)).ne'
  have hI : cableCurrent 4 1 V₀ 1 1 = 0 := by
    simp only [cableCurrent, lengthConstant_four_one, charResistance_four_one, V₀]
    field_simp
    ring
  refine ⟨hss, hI, ?_⟩
  have := hss.sealedEnd_voltage_end (by norm_num) (by norm_num) one_pos
  simpa [cableVoltage, lengthConstant_four_one] using this hI

end MathlibExtTest.Biology.Biophysics.MembraneCable

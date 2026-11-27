/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import PhyslibExt.Mechanics.PropulsionPorts

/-!
# Rocket velocity-increment checks

Concrete consumers of `PhyslibExt.Mechanics.PropulsionPorts`: the linear mass history
`m t = 2 - t` on `[0, 1]` with `ve = 1` (increment, burn and boundary), a specific-impulse
instance, constant mass, and the zero-mass input that the positivity hypothesis excludes; then a
parcel step of the vehicle of mass `2` at rest with flow `1` and exhaust speed `3`, and the parcel
lemmas applied to it, to the linear burning history `M s = 2 - s` and to the nonlinear burning
history `M s = 2 - s - s ^ 2`, with forward steps for the histories, and a forward step that
leaves no mass; the separate-flow thrust of a rocket and of a turbojet, and a steady duct flow on
the unit square that satisfies the box momentum balance with a nonzero wall thrust; finally staged
burns: a burn from `4` to `3`, a jettison from `3` to `2` and a burn from `2` to `1` at `ve = 1`,
two stages with exhaust speeds `2` and `3` and a discarded dry mass `1`, and a mass increase that
balances momentum but is no jettison.

## i. Overview

These are elaboration and non-vacuity checks, not new results.

## ii. Key results

No new general results are introduced here; section E defines the fixture stress
`shearDuctStress`, and section F the two-stage fixture data `twoStageMass`, `twoStageExhaust` and
`twoStageVelocity`.

## iii. Table of contents

- A. Linear burn and zero mass
- B. Burn, specific impulse and constant mass
- C. Parcel fixture
- D. Parcel lemmas on the fixture state
- E. Separate-flow thrust
- F. Staged burns and dry-mass jettison

## iv. References

None.

## A. Linear burn and zero mass

-/

public section

namespace PhyslibExtTest.Mechanics.PropulsionPorts

open Set PhyslibExt.Mechanics.PropulsionPorts

/-- Derivative data, positivity and the law for the linear burn `m t = 2 - t`,
`v t = log (2 / (2 - t))`, `ve = 1` on `[0, 1]`. -/
lemma linearBurn_data : ∀ t ∈ Icc (0 : ℝ) 1,
    HasDerivAt (fun s : ℝ => 2 - s) (-1) t ∧
    HasDerivAt (fun s : ℝ => Real.log (2 / (2 - s))) (1 / (2 - t)) t ∧
    0 < 2 - t ∧ (2 - t) * (1 / (2 - t)) = -1 * (-1) := by
  intro t ht
  obtain ⟨ht0, ht1⟩ := mem_Icc.mp ht
  have hpos : (0 : ℝ) < 2 - t := by linarith
  have hne : (2 : ℝ) - t ≠ 0 := ne_of_gt hpos
  have hsub : HasDerivAt (fun s : ℝ => 2 - s) (-1) t :=
    (hasDerivAt_id t).const_sub 2
  have hdiv : HasDerivAt (fun s : ℝ => 2 / (2 - s)) ((0 * (2 - t) - 2 * -1) / (2 - t) ^ 2) t :=
    (hasDerivAt_const t (2 : ℝ)).fun_div hsub hne
  have hinner_ne : (2 : ℝ) / (2 - t) ≠ 0 := div_ne_zero (by norm_num) hne
  have hlog := hdiv.log hinner_ne
  have hder_eq : ((0 * (2 - t) - 2 * -1) / (2 - t) ^ 2) / (2 / (2 - t)) = 1 / (2 - t) := by
    field_simp
    ring
  rw [hder_eq] at hlog
  have hlaw : (2 - t) * (1 / (2 - t)) = -1 * (-1) := by
    field_simp
  exact ⟨hsub, hlog, hpos, hlaw⟩

/-- Fixture: `m t = 2 - t` on `[0, 1]` with `ve = 1`. The velocity `v t = log (2 / (2 - t))`
satisfies the law (`m' = -1`, `v' = 1 / (2 - t)`), the mass stays positive, and the increment
`v 1 - v 0` is `1 * log (m 0 / m 1) = log 2 > 0`. -/
example :
    (∀ t ∈ Icc (0 : ℝ) 1,
      HasDerivAt (fun s : ℝ => 2 - s) (-1) t ∧
      HasDerivAt (fun s : ℝ => Real.log (2 / (2 - s))) (1 / (2 - t)) t ∧
      0 < 2 - t ∧ (2 - t) * (1 / (2 - t)) = -1 * (-1)) ∧
    Real.log (2 / (2 - 1)) - Real.log (2 / (2 - 0)) = 1 * Real.log ((2 - 0) / (2 - 1)) ∧
    Real.log (2 / (2 - 1)) - Real.log (2 / (2 - 0)) = Real.log 2 ∧
    0 < Real.log 2 := by
  have hinc := velocity_increment_eq_log (m := fun s : ℝ => 2 - s)
    (v := fun s : ℝ => Real.log (2 / (2 - s))) (m' := fun _ => -1) (v' := fun s => 1 / (2 - s))
    (ve := 1) (tb := 1) zero_le_one (fun t ht => (linearBurn_data t ht).1)
    (fun t ht => (linearBurn_data t ht).2.1) (fun t ht => (linearBurn_data t ht).2.2.1)
    (fun t ht => (linearBurn_data t ht).2.2.2)
  refine ⟨linearBurn_data, hinc, ?_, Real.log_pos (by norm_num)⟩
  norm_num [Real.log_one]

/-- Zero mass is excluded: with `m ≡ 0`, `ve = 1` and `v t = t` on `[0, 1]` the derivative data
and the law `0 * 1 = -1 * 0` hold, yet the increment `1 - 0` differs from
`1 * log (0 / 0) = 0`. Positivity of the mass cannot be dropped. -/
example :
    (∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt (fun _ : ℝ => (0 : ℝ)) 0 t ∧
      HasDerivAt (fun s : ℝ => s) 1 t ∧ (0 : ℝ) * 1 = -1 * 0) ∧
    (1 : ℝ) - 0 ≠ 1 * Real.log (0 / 0) := by
  refine ⟨?_, ?_⟩
  · intro t ht
    refine ⟨hasDerivAt_const t 0, hasDerivAt_id t, by norm_num⟩
  · simp

/-! ## B. Burn, specific impulse and constant mass -/

/-- The linear burn expels mass (`m 1 = 1 < 2 = m 0`), so its increment is positive. -/
example : 0 < Real.log (2 / (2 - 1)) - Real.log (2 / (2 - 0)) := by
  have hb := velocity_increment_burn_and_boundary (m := fun s : ℝ => 2 - s)
    (v := fun s : ℝ => Real.log (2 / (2 - s))) (m' := fun _ => -1) (v' := fun s => 1 / (2 - s))
    (ve := 1) (tb := 1) zero_le_one one_pos (fun t ht => (linearBurn_data t ht).1)
    (fun t ht => (linearBurn_data t ht).2.1) (fun t ht => (linearBurn_data t ht).2.2.1)
    (fun t ht => (linearBurn_data t ht).2.2.2) (fun x _ y _ hxy => by simp only; linarith)
  exact hb.2.2.mpr (by norm_num)

/-- Specific impulse at a burning instant: mass `1000`, velocity rate `6`, mass rate `-2` and
exhaust speed `3000` satisfy the law (`6000 = 6000`); with `g0 = 10` the impulse is `300`. -/
example : specificImpulse (1000 * 6) (-(-2)) 10 = 300 := by
  have h := specificImpulse_eq_of_law (m := fun _ : ℝ => 1000) (v' := fun _ => 6)
    (m' := fun _ => -2) (ve := 3000) (g0 := 10) (t := 0) (by norm_num) (by norm_num)
    (by norm_num)
  rw [h]
  norm_num

/-- With constant mass `5` the law forces zero velocity rate, so any velocity history obeying it
on `[0, 1]` ends where it starts. -/
example (v v' : ℝ → ℝ) (hv : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt v (v' t) t)
    (hlaw : ∀ t ∈ Icc (0 : ℝ) 1, 5 * v' t = -3 * 0) : v 1 = v 0 :=
  velocity_increment_const_mass zero_le_one (by norm_num) hv hlaw


/-! ## C. Parcel fixture -/

open Filter Topology PhyslibExt.Mechanics.PowerPorts

/-- `m = 2`, `v = 0`, `q = 1`, `ve = 3`, `F = 0`: the step `h = 1 / 2` gives `v_h = 1` (momentum
`(3 / 2) · 1 + (1 / 2) · (-3) = 0`), the slope tends to `3 / 2`, and the balance without the
expelled momentum predicts no acceleration at all. -/
example :
    parcelVelocity 2 0 1 3 0 (1 / 2) = 1 ∧
      Tendsto (fun h => (parcelVelocity 2 0 1 3 0 h - 0) / h) (𝓝[≠] 0) (𝓝 (3 / 2)) ∧
      Tendsto (fun h => (naiveParcelVelocity 2 0 1 0 h - 0) / h) (𝓝[≠] 0) (𝓝 0) := by
  refine ⟨?_, ?_, ?_⟩
  · unfold parcelVelocity
    norm_num
  · have h := parcel_slope_tendsto (show (0 : ℝ) < 2 by norm_num) 0 1 3 0
    have heq : ((3 : ℝ) * 1 + 0) / 2 = 3 / 2 := by norm_num
    rwa [heq] at h
  · have h := naive_slope_tendsto (show (0 : ℝ) < 2 by norm_num) 0 1 0
    have heq : ((1 : ℝ) * 0 + 0) / 2 = 0 := by norm_num
    rwa [heq] at h

/-! ## D. Parcel lemmas on the fixture state -/

/-- The fixture step `h = 1 / 2` satisfies the parcel momentum balance. -/
example : (2 - 1 * (1 / 2)) * parcelVelocity 2 0 1 3 0 (1 / 2) + 1 * (1 / 2) * (0 - 3) =
    2 * 0 + 0 * (1 / 2) :=
  (parcel_momentum_iff (by norm_num) 0 3 0 _).mpr rfl

/-- The linear burning history `M s = 2 - s` at `t = 0`: each forward step `0 < h < 2`, which
leaves the positive mass `2 - h`, expels the nonnegative mass `h` at exactly the constant rate `1`,
and the constant-flow step leaves `2 - h` and conserves momentum, so it is the actual parcel step;
with `ve = 3` and `F = 0` its slope tends to `3 / 2`. -/
example : (∀ h : ℝ, 0 < h → h < 2 → 0 ≤ 2 - (2 - h) ∧ (2 - (2 - h)) / h = 1 ∧
      (2 - h) * parcelVelocity 2 0 1 3 0 h + (2 - (2 - h)) * (0 - 3) = 2 * 0 + 0 * h) ∧
    Tendsto (fun h => (parcelVelocity 2 0 1 3 0 h - 0) / h) (𝓝[>] 0) (𝓝 (3 / 2)) := by
  obtain ⟨h₁, h₂⟩ := parcel_continuum_linear (M := fun s : ℝ => 2 - s) (m' := -1) (t := 0)
    (fun h => by ring) (by norm_num) (by norm_num) 0 3 0
  refine ⟨fun h hh hh2 => ?_, by simpa using h₂⟩
  obtain ⟨e₁, e₂, -, e₄⟩ := h₁ h hh (show (0 : ℝ) < 2 - (0 + h) by linarith)
  exact ⟨by simpa using e₁, by simpa using e₂, by simpa using e₄⟩

/-- Positive remaining mass is needed: for the same history the forward step `h = 2` leaves no
mass, and the constant-flow update there, a division by zero, violates the momentum balance; the
step `h = 3` would leave the negative mass `-1`. -/
example : (2 : ℝ) - (0 + 2) = 0 ∧
    (2 - 1 * 2) * parcelVelocity 2 0 1 3 0 2 + 1 * 2 * (0 - 3) ≠ 2 * 0 + 0 * 2 ∧
    (2 : ℝ) - (0 + 3) < 0 := by
  refine ⟨by norm_num, ?_, by norm_num⟩
  norm_num

/-- The nonlinear burning history `M s = 2 - s - s ^ 2` at `t = 0`, with `M' 0 = -1`: a forward
parcel step `h > 0` with the actual flow `q_h = 1 + h` expels the nonnegative mass `h + h ^ 2` and
leaves exactly the mass `M h` for small `h`, and with `ve = 3`, `F = 0` its slope tends to
`3 / 2`. The constant flow `1` would leave `2 - h` instead: at `h = 1 / 2`, `3 / 2` against
`M (1 / 2) = 5 / 4`. -/
example :
    (∀ᶠ h in 𝓝[>] (0 : ℝ), 0 ≤ 2 - (2 - h - h ^ 2) ∧
      2 - (2 - (2 - h - h ^ 2)) / h * h = 2 - h - h ^ 2) ∧
      Tendsto (fun h => (parcelVelocity 2 0 ((2 - (2 - h - h ^ 2)) / h) 3 0 h - 0) / h)
        (𝓝[>] 0) (𝓝 (3 / 2)) ∧
      (2 : ℝ) - 1 * (1 / 2) ≠ 2 - 1 / 2 - (1 / 2) ^ 2 := by
  have hM : HasDerivAt (fun s : ℝ => 2 - s - s ^ 2) (-1) 0 := by
    simpa using ((hasDerivAt_id' (0 : ℝ)).const_sub 2).fun_sub (hasDerivAt_pow 2 (0 : ℝ))
  obtain ⟨-, h₂, h₃⟩ := parcel_continuum hM (by norm_num) (by norm_num) 0 3 0
  refine ⟨?_, by simpa using h₃, by norm_num⟩
  filter_upwards [h₂] with h hh
  exact ⟨by simpa using hh.1, by simpa using hh.2.1⟩

/-- Without expelled mass the parcel step of the fixture vehicle under the force `4` is the
fixed-mass velocity `0 + (1 / 2) / 2 · 4 = 1`. -/
example : parcelVelocity 2 0 0 3 4 (1 / 2) = constForceVelocity 2 0 4 (1 / 2) :=
  parcelVelocity_zero_flow (by norm_num) 0 3 4 (1 / 2)

/-- The fixture flow accelerates the vehicle, and ignoring the expelled momentum misses it. -/
example : 0 < ((3 : ℝ) * 1 + 0) / 2 ∧ ((1 : ℝ) * 0 + 0) / 2 ≠ (3 * 1 + 0) / 2 :=
  ⟨parcel_accel_pos (by norm_num) (by norm_num) (by norm_num) rfl,
    naive_limit_ne (by norm_num) (by norm_num) (by norm_num) 0⟩

/-! ## E. Separate-flow thrust -/

section SeparateFlowThrust

open MeasureTheory ControlVolumes
open MathlibExt.Probability.FokkerPlanck (divergence)

/-- **Rocket fixture.** Propellant flow `100`, exhaust velocity `3000`, exit pressure `120000`
in the ambient `100000` and exit area `1 / 2`: thrust `310000 = 300000 + 10000` (momentum and
pressure terms), effective exhaust velocity `3100` and specific impulse `3100 / g0`. -/
lemma rocket_fixture (vIn pIn g0 : ℝ) :
    separateFlowThrust 0 vIn pIn 0 100 3000 120000 (1 / 2) 100000 = 310000 ∧
      effectiveExhaustVelocity (separateFlowThrust 0 vIn pIn 0 100 3000 120000 (1 / 2) 100000)
        100 = 3100 ∧
      specificImpulse (separateFlowThrust 0 vIn pIn 0 100 3000 120000 (1 / 2) 100000) 100 g0 =
        3100 / g0 := by
  have hT : separateFlowThrust 0 vIn pIn 0 100 3000 120000 (1 / 2) 100000 = 310000 := by
    rw [separateFlowThrust]
    norm_num
  have hc : effectiveExhaustVelocity
      (separateFlowThrust 0 vIn pIn 0 100 3000 120000 (1 / 2) 100000) 100 = 3100 := by
    rw [hT, effectiveExhaustVelocity]
    norm_num
  exact ⟨hT, hc, by rw [specificImpulse_totalFlow_eq, hc]⟩

/-- **Turbojet fixture.** Inlet flow `50` at `250` with `p_in = p_a`, fuel flow `1`, exhaust flow
`51` at `600` with `p_e = p_a`: thrust `18100`; the equal-flow formula gives `17500`, short by
`ṁ_f v_e = 600`; the fuel-flow specific impulse is `51` times the total-flow one. -/
lemma turbojet_fixture (pA AIn AE g0 : ℝ) (hg0 : 0 < g0) :
    separateFlowThrust 50 250 pA AIn 51 600 pA AE pA = 18100 ∧
      separateFlowThrust 50 250 pA AIn 50 600 pA AE pA = 17500 ∧
      specificImpulse (separateFlowThrust 50 250 pA AIn 51 600 pA AE pA) 1 g0 =
        51 * specificImpulse (separateFlowThrust 50 250 pA AIn 51 600 pA AE pA) 51 g0 := by
  have hT : separateFlowThrust 50 250 pA AIn 51 600 pA AE pA = 18100 := by
    rw [separateFlowThrust]
    ring
  refine ⟨hT, by rw [separateFlowThrust]; ring, ?_⟩
  rw [hT, specificImpulse, specificImpulse]
  field_simp

/-- Partial derivatives of `A (y 0) + B (y 0) y 1 + C (y 0) y 1²` on `Fin 2 → ℝ`. -/
private lemma fderiv_quad_apply {A B C : ℝ → ℝ} {A' B' C' : ℝ} (x : Fin 2 → ℝ)
    (hA : HasDerivAt A A' (x 0)) (hB : HasDerivAt B B' (x 0)) (hC : HasDerivAt C C' (x 0))
    (i : Fin 2) :
    fderiv ℝ (fun y : Fin 2 → ℝ => A (y 0) + B (y 0) * y 1 + C (y 0) * y 1 ^ 2) x
        (Pi.single i 1) =
      (A' + B' * x 1 + C' * x 1 ^ 2) * (Pi.single i 1 : Fin 2 → ℝ) 0 +
        (B (x 0) + 2 * C (x 0) * x 1) * (Pi.single i 1 : Fin 2 → ℝ) 1 := by
  have h0 : HasFDerivAt (fun y : Fin 2 → ℝ => y 0)
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 0) x := hasFDerivAt_apply 0 x
  have h1 : HasFDerivAt (fun y : Fin 2 → ℝ => y 1)
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 1) x := hasFDerivAt_apply 1 x
  have h := ((hA.comp_hasFDerivAt x h0).add ((hB.comp_hasFDerivAt x h0).mul h1)).add
    ((hC.comp_hasFDerivAt x h0).mul (h1.pow 2))
  rw [show (fun y : Fin 2 → ℝ => A (y 0) + B (y 0) * y 1 + C (y 0) * y 1 ^ 2) =
    ((A ∘ fun y : Fin 2 → ℝ => y 0) + (B ∘ fun y : Fin 2 → ℝ => y 0) * fun y => y 1) +
      (C ∘ fun y : Fin 2 → ℝ => y 0) * fun y => y 1 ^ 2 from rfl, h.fderiv]
  simp only [Function.comp_apply, add_apply, smul_apply,
    ContinuousLinearMap.proj_apply, smul_eq_mul]
  ring

/-- Stress of a steady shear-driven duct on the unit square: the pressure
`p = x₀² / 2 - x₀³ / 3` along the duct, the symmetric shear `σ₀₁ = σ₁₀ = (x₀ - x₀²) x₁`, which
vanishes on the port faces `x₀ = 0, 1`, and the transverse normal stress
`σ₁₁ = -(1 - 2 x₀) x₁² / 2` that balances the transverse momentum. -/
noncomputable def shearDuctStress (x : Fin 2 → ℝ) : Fin 2 → Fin 2 → ℝ :=
  ![![-(x 0 ^ 2 / 2 - x 0 ^ 3 / 3), (x 0 - x 0 ^ 2) * x 1],
    ![(x 0 - x 0 ^ 2) * x 1, -((1 - 2 * x 0) * x 1 ^ 2 / 2)]]

/-- **A steady duct with nonzero wall thrust.** On the unit square, density `1`, the uniform
velocity `(1, 0)`, the stress `shearDuctStress` and no body force satisfy the hypotheses of
`wallForce_eq_separateFlowThrust`, with shear-free ports at the pressures `0` (inlet) and `1 / 6`
(exhaust) and impermeable side walls: the axial wall force on the fluid is the thrust `1 / 6`. -/
lemma shearDuct_wallForce :
    (∑ i : Fin 1, faceTractionResultant (0 : Fin 2 → ℝ) 1 shearDuctStress i.succ) 0 = 1 / 6 := by
  have hA : faceArea (0 : Fin 2 → ℝ) 1 0 = 1 := by simp [faceArea]
  have h := wallForce_eq_separateFlowThrust (n := 1) (a := 0) (b := 1) (ρ := fun _ _ => 1)
    (v := fun _ _ => ![1, 0])
    (σ := fun _ => shearDuctStress) (f := fun _ _ => 0) (U := univ) (t := 0) (pi := 0)
    (po := 1 / 6) (fun i => by simp) isOpen_univ (subset_univ _) contDiff_const contDiff_const
    ?_ (fun _ => integrableOn_const isCompact_Icc.measure_lt_top.ne) ?_ (fun _ _ => rfl)
    (fun _ _ => rfl) ?_ (fun _ _ => rfl) (fun _ _ => rfl) ?_ ?_ (hasDerivAt_const _ _)
    (by simp) 0
  · rw [h, hA, separateFlowThrust]
    norm_num
  · refine ContDiff.contDiffOn (contDiff_pi.2 fun j => contDiff_pi.2 fun i => ?_)
    fin_cases j <;> fin_cases i <;>
      simp only [shearDuctStress, Fin.zero_eta, Fin.mk_one, Fin.isValue, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val_fin_one] <;>
      fun_prop
  · intro j x _
    have hpA : HasDerivAt (fun s : ℝ => 1 + (s ^ 2 / 2 - s ^ 3 / 3)) (x 0 - x 0 ^ 2) (x 0) :=
      ((((hasDerivAt_pow 2 (x 0)).div_const 2).sub ((hasDerivAt_pow 3 (x 0)).div_const
        3)).const_add 1).congr_deriv (by push_cast; ring)
    have hgB : HasDerivAt (fun s : ℝ => -(s - s ^ 2)) (-(1 - 2 * x 0)) (x 0) :=
      ((hasDerivAt_id' (x 0)).sub (hasDerivAt_pow 2 (x 0))).neg.congr_deriv (by push_cast; ring)
    have hcC : HasDerivAt (fun s : ℝ => (1 - 2 * s) / 2) (-1) (x 0) :=
      (((hasDerivAt_id' (x 0)).const_mul 2).const_sub 1).div_const 2 |>.congr_deriv (by norm_num)
    have hz : ∀ c : ℝ, HasDerivAt (fun _ : ℝ => c) 0 (x 0) := fun c => hasDerivAt_const _ c
    unfold divergence MathlibExt.Probability.FokkerPlanck.pderiv
    rw [Fin.sum_univ_two]
    fin_cases j
    · have hF0 : (fun y => momentumFlux (fun _ => 1) (fun _ => ![1, 0]) shearDuctStress 0 y 0) =
          fun y : Fin 2 → ℝ => (fun s : ℝ => 1 + (s ^ 2 / 2 - s ^ 3 / 3)) (y 0) +
            (fun _ : ℝ => (0 : ℝ)) (y 0) * y 1 + (fun _ : ℝ => (0 : ℝ)) (y 0) * y 1 ^ 2 := by
        funext y
        simp [momentumFlux, shearDuctStress]
        ring
      have hF1 : (fun y => momentumFlux (fun _ => 1) (fun _ => ![1, 0]) shearDuctStress 0 y 1) =
          fun y : Fin 2 → ℝ => (fun _ : ℝ => (0 : ℝ)) (y 0) +
            (fun s : ℝ => -(s - s ^ 2)) (y 0) * y 1 + (fun _ : ℝ => (0 : ℝ)) (y 0) * y 1 ^ 2 := by
        funext y
        simp [momentumFlux, shearDuctStress]
        ring
      simp only [Fin.zero_eta, Fin.isValue]
      rw [hF0, hF1, fderiv_quad_apply x hpA (hz 0) (hz 0), fderiv_quad_apply x (hz 0) hgB (hz 0)]
      simp
    · have hF0 : (fun y => momentumFlux (fun _ => 1) (fun _ => ![1, 0]) shearDuctStress 1 y 0) =
          fun y : Fin 2 → ℝ => (fun _ : ℝ => (0 : ℝ)) (y 0) +
            (fun s : ℝ => -(s - s ^ 2)) (y 0) * y 1 + (fun _ : ℝ => (0 : ℝ)) (y 0) * y 1 ^ 2 := by
        funext y
        simp [momentumFlux, shearDuctStress]
        ring
      have hF1 : (fun y => momentumFlux (fun _ => 1) (fun _ => ![1, 0]) shearDuctStress 1 y 1) =
          fun y : Fin 2 → ℝ => (fun _ : ℝ => (0 : ℝ)) (y 0) + (fun _ : ℝ => (0 : ℝ)) (y 0) * y 1 +
            (fun s : ℝ => (1 - 2 * s) / 2) (y 0) * y 1 ^ 2 := by
        funext y
        simp [momentumFlux, shearDuctStress]
        ring
      simp only [Fin.mk_one, Fin.isValue]
      rw [hF0, hF1, fderiv_quad_apply x (hz 0) hgB (hz 0), fderiv_quad_apply x (hz 0) (hz 0) hcC]
      simp
      ring
  · intro y _
    funext j
    fin_cases j <;> simp [shearDuctStress]
  · intro y _
    funext j
    fin_cases j <;> norm_num [shearDuctStress]
  · intro i hi y _
    fin_cases i
    · exact absurd rfl hi
    · simp

end SeparateFlowThrust

/-! ## F. Staged burns and dry-mass jettison -/

private lemma hasDerivAt_log_div_sub {c t : ℝ} (hc : c ≠ 0) (hct : c - t ≠ 0) :
    HasDerivAt (fun u => Real.log (c / (c - u))) (1 / (c - t)) t := by
  have hsub : HasDerivAt (fun u : ℝ => c - u) (-1) t :=
    HasDerivAt.const_sub c (hasDerivAt_id t)
  have hdiv : HasDerivAt (fun u : ℝ => c / (c - u)) (c / (c - t) ^ 2) t := by
    refine (HasDerivAt.fun_div (hasDerivAt_const t c) hsub hct).congr_deriv ?_
    field_simp
    ring
  have hne : c / (c - t) ≠ 0 := div_ne_zero hc hct
  have hlog := HasDerivAt.log hdiv hne
  refine hlog.congr_deriv ?_
  field_simp

/-- Burn from `4` to `3`, jettison from `3` to `2`, burn from `2` to `1`, all at `ve = 1`: the
staged increment is `log (8 / 3)`, less than `log 4`, the increment of one burn from `4` to `1`
that counts the jettison as propellant. -/
lemma staged_ratio_fixture :
    1 * Real.log (4 / 3) + 1 * Real.log (2 / 1) = Real.log (8 / 3) ∧
      Real.log (8 / 3) < 1 * Real.log (4 / 1) := by
  have hmul : (4 / 3 : ℝ) * (2 / 1) = 8 / 3 := by norm_num
  have hlog := Real.log_mul (show (4 / 3 : ℝ) ≠ 0 by norm_num) (show (2 / 1 : ℝ) ≠ 0 by norm_num)
  rw [hmul] at hlog
  refine ⟨?_, ?_⟩
  · linarith [hlog]
  · have h4 : (4 : ℝ) / 1 = 4 := by norm_num
    rw [h4, one_mul]
    exact Real.log_lt_log (by norm_num) (by norm_num)

/-- Fixture masses on `[0, 1]`: burn `0` from `4` to `3`, burn `1` (and later) from `2` to `1`. -/
noncomputable def twoStageMass : ℕ → ℝ → ℝ
  | 0 => fun t => 4 - t
  | _ + 1 => fun t => 2 - t

/-- Fixture exhaust speeds: `2` for burn `0`, `3` for burn `1` (and later). -/
noncomputable def twoStageExhaust : ℕ → ℝ
  | 0 => 2
  | _ + 1 => 3

/-- Fixture velocities: `2 log (4 / (4 - t))` in burn `0`; after the jettison, which keeps the
velocity `2 log (4 / 3)`, `2 log (4 / 3) + 3 log (2 / (2 - t))` in burn `1` (and later). -/
noncomputable def twoStageVelocity : ℕ → ℝ → ℝ
  | 0 => fun t => 2 * Real.log (4 / (4 - t))
  | _ + 1 => fun t => 2 * Real.log (4 / 3) + 3 * Real.log (2 / (2 - t))

/-- Two stages with different exhaust speeds and a nonzero discarded dry mass: both burns satisfy
the reduced law with mass rate `-1` on `[0, 1]`, the jettison from `3` to `2` conserves momentum
at zero relative velocity, and the velocity gained is `2 log (4 / 3) + 3 log 2`, less than the
`2 log (4 / 2) + 3 log 2` obtained by counting the dropped mass as first-stage propellant. -/
lemma twoStage_fixture :
    (∀ i ≤ 1, ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt (twoStageMass i) (-1) t ∧
        HasDerivAt (twoStageVelocity i) (twoStageExhaust i / twoStageMass i t) t ∧
        0 < twoStageMass i t ∧
        twoStageMass i t * (twoStageExhaust i / twoStageMass i t) = -twoStageExhaust i * -1) ∧
      twoStageMass 1 0 * twoStageVelocity 1 0 +
          (twoStageMass 0 1 - twoStageMass 1 0) * twoStageVelocity 0 1 =
        twoStageMass 0 1 * twoStageVelocity 0 1 ∧
      twoStageMass 1 0 < twoStageMass 0 1 ∧ twoStageExhaust 0 ≠ twoStageExhaust 1 ∧
      twoStageVelocity 1 1 - twoStageVelocity 0 0 = 2 * Real.log (4 / 3) + 3 * Real.log 2 ∧
      2 * Real.log (4 / 3) + 3 * Real.log 2 < 2 * Real.log (4 / 2) + 3 * Real.log 2 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi t ht
    have hi01 : i = 0 ∨ i = 1 := by omega
    obtain ⟨ht0, ht1⟩ := Set.mem_Icc.mp ht
    rcases hi01 with rfl | rfl
    · simp only [twoStageMass, twoStageExhaust, twoStageVelocity]
      have h4t : (0 : ℝ) < 4 - t := by linarith
      have h4t' : (4 : ℝ) - t ≠ 0 := ne_of_gt h4t
      refine ⟨?_, ?_, h4t, ?_⟩
      · exact HasDerivAt.const_sub 4 (hasDerivAt_id t)
      · have hlog := hasDerivAt_log_div_sub (c := 4) (t := t) (by norm_num) h4t'
        have h2 := HasDerivAt.const_mul 2 hlog
        exact h2.congr_deriv (mul_one_div 2 (4 - t))
      · field_simp
    · simp only [twoStageMass, twoStageExhaust, twoStageVelocity]
      have h2t : (0 : ℝ) < 2 - t := by linarith
      have h2t' : (2 : ℝ) - t ≠ 0 := ne_of_gt h2t
      refine ⟨?_, ?_, h2t, ?_⟩
      · exact HasDerivAt.const_sub 2 (hasDerivAt_id t)
      · have hlog := hasDerivAt_log_div_sub (c := 2) (t := t) (by norm_num) h2t'
        have h3 := HasDerivAt.const_mul 3 hlog
        have hadd := HasDerivAt.const_add (2 * Real.log (4 / 3)) h3
        exact hadd.congr_deriv (mul_one_div 3 (2 - t))
      · field_simp
  · have e1 : twoStageMass 1 0 = 2 := by norm_num [twoStageMass]
    have e2 : twoStageMass 0 1 = 3 := by norm_num [twoStageMass]
    have ev1 : twoStageVelocity 1 0 = 2 * Real.log (4 / 3) := by
      have h21 : (2 : ℝ) / (2 - 0) = 1 := by norm_num
      simp only [twoStageVelocity]
      rw [h21, Real.log_one, mul_zero, add_zero]
    have ev0 : twoStageVelocity 0 1 = 2 * Real.log (4 / 3) := by
      have h41 : (4 : ℝ) / (4 - 1) = 4 / 3 := by norm_num
      simp only [twoStageVelocity]
      rw [h41]
    rw [e1, e2, ev1, ev0]
    ring
  · norm_num [twoStageMass]
  · norm_num [twoStageExhaust]
  · have ev11 : twoStageVelocity 1 1 = 2 * Real.log (4 / 3) + 3 * Real.log 2 := by
      have h21 : (2 : ℝ) / (2 - 1) = 2 := by norm_num
      simp only [twoStageVelocity]
      rw [h21]
    have ev00 : twoStageVelocity 0 0 = 0 := by
      have h40 : (4 : ℝ) / (4 - 0) = 1 := by norm_num
      simp only [twoStageVelocity]
      rw [h40, Real.log_one, mul_zero]
    rw [ev11, ev00, sub_zero]
  · have hlt : Real.log (4 / 3 : ℝ) < Real.log (4 / 2) :=
      Real.log_lt_log (by norm_num) (by norm_num)
    linarith [hlt]

-- The staged lemma on the two-stage fixture: the burns satisfy the reduced law with mass rate `-1`
-- and the jettison conserves momentum, so the velocity gained is the sum of the burn increments
-- `2 log (4 / 3) + 3 log (2 / 1)`; the dropped mass `1` enters no logarithm.
example : twoStageVelocity 1 1 - twoStageVelocity 0 0 =
    2 * Real.log (4 / 3) + 3 * Real.log (2 / 1) := by
  obtain ⟨hdata, hjet, hdrop, -⟩ := twoStage_fixture
  have h := staged_velocity_increment 1 (m := twoStageMass) (v := twoStageVelocity)
    (m' := fun _ _ => -1) (v' := fun i t => twoStageExhaust i / twoStageMass i t)
    (ve := twoStageExhaust) (tb := fun _ => 1) (fun _ _ => zero_le_one)
    (fun i hi t ht => (hdata i hi t ht).1) (fun i hi t ht => (hdata i hi t ht).2.1)
    (fun i hi t ht => (hdata i hi t ht).2.2.1) (fun i hi t ht => (hdata i hi t ht).2.2.2)
    (fun i hi => by
      obtain rfl : i = 0 := by omega
      exact hdrop.le)
    (fun i hi => by
      obtain rfl : i = 0 := by omega
      exact hjet)
  rw [h, Finset.sum_range_succ, Finset.sum_range_one]
  norm_num [twoStageExhaust, twoStageMass]

-- The jettison of the two-stage fixture keeps the velocity: from mass `3` at the velocity
-- `2 log (4 / 3)` to mass `2`, the balance holds exactly for the unchanged velocity.
example (w : ℝ) : 2 * w + (3 - 2) * (2 * Real.log (4 / 3)) = 3 * (2 * Real.log (4 / 3)) ↔
    w = 2 * Real.log (4 / 3) :=
  jettison_velocity_eq (by norm_num)

-- Counting the jettison `3 → 2` as propellant of the burn from `4` adds `log (3 / 2) > 0` at
-- `ve = 1`.
example : 1 * Real.log (4 / 2) = 1 * Real.log (4 / 3) + 1 * Real.log (3 / 2) ∧
    1 * Real.log (4 / 3) < 1 * Real.log (4 / 2) :=
  jettison_as_propellant_overstates one_pos (by norm_num) (by norm_num) (by norm_num)

-- A momentum balance alone does not make a transition a jettison: the mass increase from `1` to `2`
-- at zero velocity balances momentum, but it is no drop, so it is not a transition of the staged
-- lemma.
example : (2 : ℝ) * 0 + (1 - 2) * 0 = 1 * 0 ∧ ¬ (2 : ℝ) ≤ 1 := by norm_num

end PhyslibExtTest.Mechanics.PropulsionPorts

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import PhyslibExt.EarthScience.Geotechnical.InfiniteSlope
import Mathlib.Data.Fin.VecNotation
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Infinite-slope safety-ratio checks

Concrete consumers of the safety-ratio admission in
`PhyslibExt.EarthScience.Geotechnical.InfiniteSlope`: the
textbook dry-slope factor `c / τd + tan φ / tan β`, sign
controls off the genuine-slope domain, the effective
normal stress on a non-unit normal, and pore-pressure
monotonicity on a witness slab.

## i. Overview

These are elaboration and sign checks, not new results.

## ii. Key results

No new definitions or results are introduced here.

## iii. Table of contents

- A. Safety ratio and controls
- B. Pore-pressure monotonicity

## iv. References

- `PhyslibExt.EarthScience.Geotechnical.InfiniteSlope`
-/

open EarthScience
open scoped Matrix

namespace PhyslibExtTest.EarthScience.Geotechnical.InfiniteSlope

/-! ## A. Safety ratio and controls -/

/-- Textbook dry-slope form at zero pore pressure: the
Mohr–Coulomb safety ratio is `c / τd + tan φ / tan β`. -/
example {c phi gamma z beta : ℝ} (hgamma : 0 < gamma) (hz : 0 < z)
    (hbeta0 : 0 < beta) (hbeta : beta < Real.pi / 2) :
    infiniteSlopeSafetyRatio
        (infiniteSlopeResistingStress c phi gamma z beta 0) gamma z beta
      = c / infiniteSlopeDrivingStress gamma z beta
        + Real.tan phi / Real.tan beta := by
  have hpos := infiniteSlopeDrivingStress_pos hgamma hz hbeta0 hbeta
  have htan := infiniteSlopeDriving_eq_normal_mul_tan hbeta0 hbeta
    (gamma := gamma) (z := z)
  unfold infiniteSlopeSafetyRatio infiniteSlopeResistingStress
  rw [sub_zero, add_div, htan]
  have hγz : gamma * z ≠ 0 := mul_ne_zero hgamma.ne' hz.ne'
  have hcos : Real.cos beta ≠ 0 :=
    (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hbeta⟩).ne'
  have hsin : Real.sin beta ≠ 0 :=
    (Real.sin_pos_of_pos_of_lt_pi hbeta0 (by linarith [Real.pi_pos])).ne'
  have hN : infiniteSlopeNormalStress gamma z beta ≠ 0 := by
    unfold infiniteSlopeNormalStress
    exact mul_ne_zero hγz (pow_ne_zero 2 hcos)
  rw [Real.tan_eq_sin_div_cos, Real.tan_eq_sin_div_cos]
  field_simp [hN]

/-- Sign control: with negative unit weight the driving
stress at `β = π / 4` is negative, off the admission domain. -/
example : infiniteSlopeDrivingStress (-1) 1 (Real.pi / 4) < 0 := by
  unfold infiniteSlopeDrivingStress
  have hsin : 0 < Real.sin (Real.pi / 4) := by
    rw [Real.sin_pi_div_four]
    positivity
  have hcos : 0 < Real.cos (Real.pi / 4) := by
    rw [Real.cos_pi_div_four]
    positivity
  nlinarith [mul_pos hsin hcos]

/-- Endpoint control: at `β = 0` there is no driving stress. -/
example (gamma z : ℝ) : infiniteSlopeDrivingStress gamma z 0 = 0 := by
  simp [infiniteSlopeDrivingStress]

/-- The bridge on a non-unit normal scales: for `v = (2, 0)`
the identity with `hv : v ⬝ᵥ v = 4` is not the unit-normal
statement; the unit normal `(1, 0)` recovers `σn - u`. -/
example (u : ℝ) :
    (![1, 0] : Fin 2 → ℝ) ⬝ᵥ
        (effectiveStressCompressionPositive
          (!![10, 3; 5, 7] : Matrix (Fin 2) (Fin 2) ℝ) u *ᵥ ![1, 0])
      = 10 - u := by
  have h := effectiveNormalStress_eq
    (!![10, 3; 5, 7] : Matrix (Fin 2) (Fin 2) ℝ) u ![1, 0] (by
      simp [dotProduct, Fin.sum_univ_two])
  rw [h]
  simp [dotProduct, Fin.sum_univ_two, Matrix.mulVec, Matrix.of_apply]

#print axioms EarthScience.infiniteSlopeDrivingStress_pos
#print axioms EarthScience.infiniteSlopeSafetyRatio_admission
#print axioms EarthScience.infiniteSlope_mohrCoulomb_admission
#print axioms EarthScience.effectiveNormalStress_eq

/-! ## B. Pore-pressure monotonicity

Witness slab `gamma = 2`, `z = 3`, `beta = π / 4`, `c = 1`:
then `σn = τd = 3` and the ratio at friction angle `phi` and
pore pressure `u` is `(1 + (3 - u) * tan phi) / 3`. -/

/-- Safety ratio on the witness slab at friction angle
`phi` and pore pressure `u`. -/
private noncomputable def ratioAt (phi u : ℝ) : ℝ :=
  infiniteSlopeSafetyRatio
    (infiniteSlopeResistingStress 1 phi 2 3 (Real.pi / 4) u)
    2 3 (Real.pi / 4)

private lemma witnessNormal :
    infiniteSlopeNormalStress 2 3 (Real.pi / 4) = 3 := by
  unfold infiniteSlopeNormalStress
  rw [Real.cos_pi_div_four]
  have h2 : (√2 / 2 : ℝ) ^ 2 = 1 / 2 := by
    rw [div_pow, Real.sq_sqrt (by norm_num)]
    norm_num
  rw [h2]
  norm_num

private lemma witnessDriving :
    infiniteSlopeDrivingStress 2 3 (Real.pi / 4) = 3 := by
  unfold infiniteSlopeDrivingStress
  rw [Real.sin_pi_div_four, Real.cos_pi_div_four]
  rw [show (2 : ℝ) * 3 * (√2 / 2) * (√2 / 2) = (3 / 2) * (√2 * √2) by ring,
    Real.mul_self_sqrt (by norm_num)]
  norm_num

/-- Witness values `σn = τd = 3`. -/
example : infiniteSlopeDrivingStress 2 3 (Real.pi / 4) = 3
    ∧ infiniteSlopeNormalStress 2 3 (Real.pi / 4) = 3 :=
  ⟨witnessDriving, witnessNormal⟩

private lemma ratioAt_eq (phi u : ℝ) :
    ratioAt phi u = (1 + (3 - u) * Real.tan phi) / 3 := by
  unfold ratioAt infiniteSlopeSafetyRatio
    infiniteSlopeResistingStress
  rw [witnessNormal, witnessDriving]

/-- Strictly positive friction: `F 1 = 1` and `F 2 = 2 / 3`
by computation at `phi = π / 4`. -/
example : ratioAt (Real.pi / 4) 1 = 1
    ∧ ratioAt (Real.pi / 4) 2 = 2 / 3 := by
  constructor <;> rw [ratioAt_eq, Real.tan_pi_div_four] <;> norm_num

/-- Two ordered admissible pore pressures: `F 2 < F 1`
through the strict theorem. -/
example : ratioAt (Real.pi / 4) 2 < ratioAt (Real.pi / 4) 1 := by
  have h := infiniteSlopeSafetyRatio_strictAntiOn_porePressure
    (c := 1) (phi := Real.pi / 4) (gamma := 2) (z := 3)
    (beta := Real.pi / 4) (by norm_num) (by norm_num)
    (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])
    (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])
  have h1 : (1 : ℝ) ∈
      Set.Icc 0 (infiniteSlopeNormalStress 2 3 (Real.pi / 4)) := by
    rw [witnessNormal]
    exact Set.mem_Icc.mpr ⟨by norm_num, by norm_num⟩
  have h2 : (2 : ℝ) ∈
      Set.Icc 0 (infiniteSlopeNormalStress 2 3 (Real.pi / 4)) := by
    rw [witnessNormal]
    exact Set.mem_Icc.mpr ⟨by norm_num, by norm_num⟩
  exact h h1 h2 (by norm_num)

/-- `phi = 0` equality: `F 1 = F 2 = 1 / 3` by computation. -/
example : ratioAt 0 1 = 1 / 3 ∧ ratioAt 0 2 = 1 / 3 := by
  constructor <;> rw [ratioAt_eq] <;> simp [Real.tan_zero]

/-- `phi = 0` equality through the main theorem's third
conjunct. -/
example : ratioAt 0 1 = ratioAt 0 2 := by
  have hm := (infiniteSlopeSafetyRatio_porePressure_monotonicity
    (c := 1) (phi := 0) (gamma := 2) (z := 3) (beta := Real.pi / 4)
    (by norm_num) (by norm_num) (by linarith [Real.pi_pos])
    (by linarith [Real.pi_pos]) le_rfl (by linarith [Real.pi_pos])
    (by norm_num)).2.2 rfl
  have h1 : (1 : ℝ) ∈
      Set.Icc 0 (infiniteSlopeNormalStress 2 3 (Real.pi / 4)) := by
    rw [witnessNormal]
    exact Set.mem_Icc.mpr ⟨by norm_num, by norm_num⟩
  have h2 : (2 : ℝ) ∈
      Set.Icc 0 (infiniteSlopeNormalStress 2 3 (Real.pi / 4)) := by
    rw [witnessNormal]
    exact Set.mem_Icc.mpr ⟨by norm_num, by norm_num⟩
  have e1 := hm h1
  have e2 := hm h2
  exact e1.trans e2.symm

/-- Iff necessity: at `phi = 0` the ratio is not strictly
antitone on the witness slab. -/
example : ¬ StrictAntiOn
    (fun u => infiniteSlopeSafetyRatio
      (infiniteSlopeResistingStress 1 0 2 3 (Real.pi / 4) u)
      2 3 (Real.pi / 4))
    (Set.Icc 0 (infiniteSlopeNormalStress 2 3 (Real.pi / 4))) := by
  intro hst
  have hm := (infiniteSlopeSafetyRatio_porePressure_monotonicity
    (c := 1) (phi := 0) (gamma := 2) (z := 3) (beta := Real.pi / 4)
    (by norm_num) (by norm_num) (by linarith [Real.pi_pos])
    (by linarith [Real.pi_pos]) le_rfl (by linarith [Real.pi_pos])
    (by norm_num)).2.1
  exact absurd (hm.mp hst) (by norm_num)

/-- Negative control: at the totalized `phi = π / 2`
(`tan (π / 2) = 0`) the ratio is constant, not strict. -/
example : ¬ StrictAntiOn
    (fun u => infiniteSlopeSafetyRatio
      (infiniteSlopeResistingStress 1 (Real.pi / 2) 2 3
        (Real.pi / 4) u)
      2 3 (Real.pi / 4))
    (Set.Icc 0 (infiniteSlopeNormalStress 2 3 (Real.pi / 4))) := by
  intro hst
  have h1 : (1 : ℝ) ∈
      Set.Icc 0 (infiniteSlopeNormalStress 2 3 (Real.pi / 4)) := by
    rw [witnessNormal]
    exact Set.mem_Icc.mpr ⟨by norm_num, by norm_num⟩
  have h2 : (2 : ℝ) ∈
      Set.Icc 0 (infiniteSlopeNormalStress 2 3 (Real.pi / 4)) := by
    rw [witnessNormal]
    exact Set.mem_Icc.mpr ⟨by norm_num, by norm_num⟩
  have hlt := hst h1 h2 (by norm_num)
  simp only [infiniteSlopeSafetyRatio, infiniteSlopeResistingStress,
    Real.tan_pi_div_two, witnessNormal, witnessDriving] at hlt
  norm_num at hlt

/-- Negative control: at `phi = -π / 4` the ratio increases
with pore pressure, so it is not antitone. -/
example : ¬ AntitoneOn
    (fun u => infiniteSlopeSafetyRatio
      (infiniteSlopeResistingStress 1 (-(Real.pi / 4)) 2 3
        (Real.pi / 4) u)
      2 3 (Real.pi / 4))
    (Set.Icc 0 (infiniteSlopeNormalStress 2 3 (Real.pi / 4))) := by
  intro hanti
  have h1 : (1 : ℝ) ∈
      Set.Icc 0 (infiniteSlopeNormalStress 2 3 (Real.pi / 4)) := by
    rw [witnessNormal]
    exact Set.mem_Icc.mpr ⟨by norm_num, by norm_num⟩
  have h2 : (2 : ℝ) ∈
      Set.Icc 0 (infiniteSlopeNormalStress 2 3 (Real.pi / 4)) := by
    rw [witnessNormal]
    exact Set.mem_Icc.mpr ⟨by norm_num, by norm_num⟩
  have hle := hanti h1 h2 (by norm_num)
  change ratioAt (-(Real.pi / 4)) 2 ≤ ratioAt (-(Real.pi / 4)) 1 at hle
  have e1 : ratioAt (-(Real.pi / 4)) 1 = -1 / 3 := by
    rw [ratioAt_eq, Real.tan_neg, Real.tan_pi_div_four]
    norm_num
  have e2 : ratioAt (-(Real.pi / 4)) 2 = 0 := by
    rw [ratioAt_eq, Real.tan_neg, Real.tan_pi_div_four]
    norm_num
  rw [e2, e1] at hle
  norm_num at hle

/-- Negative control: at `beta = 0` the driving stress
vanishes and the totalized ratio is identically `0`, not
strict. -/
example : ¬ StrictAntiOn
    (fun u => infiniteSlopeSafetyRatio
      (infiniteSlopeResistingStress 1 (Real.pi / 4) 2 3 0 u)
      2 3 0)
    (Set.Icc 0 (infiniteSlopeNormalStress 2 3 0)) := by
  intro hst
  have hσ0 : infiniteSlopeNormalStress 2 3 0 = 6 := by
    norm_num [infiniteSlopeNormalStress]
  have h1 : (1 : ℝ) ∈ Set.Icc 0 (infiniteSlopeNormalStress 2 3 0) := by
    rw [hσ0]
    exact Set.mem_Icc.mpr ⟨by norm_num, by norm_num⟩
  have h2 : (2 : ℝ) ∈ Set.Icc 0 (infiniteSlopeNormalStress 2 3 0) := by
    rw [hσ0]
    exact Set.mem_Icc.mpr ⟨by norm_num, by norm_num⟩
  have hlt := hst h1 h2 (by norm_num)
  simp [infiniteSlopeSafetyRatio, infiniteSlopeDrivingStress] at hlt

/-- Degenerate domain: at `beta = π / 2` the contact domain
is `{0}`, strict antitonicity holds vacuously even at
`phi = 0`, so the strictness iff needs the genuine-slope
premises. -/
example : StrictAntiOn
    (fun u => infiniteSlopeSafetyRatio
      (infiniteSlopeResistingStress 1 0 2 3 (Real.pi / 2) u)
      2 3 (Real.pi / 2))
    (Set.Icc 0 (infiniteSlopeNormalStress 2 3 (Real.pi / 2))) := by
  intro x hx y hy hxy
  have hσ : infiniteSlopeNormalStress 2 3 (Real.pi / 2) = 0 := by
    simp [infiniteSlopeNormalStress, Real.cos_pi_div_two]
  rw [hσ] at hx hy
  have hx0 : x = 0 := le_antisymm hx.2 hx.1
  have hy0 : y = 0 := le_antisymm hy.2 hy.1
  rw [hx0, hy0] at hxy
  exact absurd hxy (by norm_num)

/-- Out of domain: the totalized formula keeps decreasing
past `u = σn` (`F 4 = 0`, `F 5 = -1 / 3`). These values are
outside the contact domain; no theorem claims anything
there. -/
example : ratioAt (Real.pi / 4) 4 = 0
    ∧ ratioAt (Real.pi / 4) 5 = -1 / 3 := by
  constructor <;> rw [ratioAt_eq, Real.tan_pi_div_four] <;> norm_num

/-- Endpoint: at `u = σn` the frictional part vanishes and
the ratio is `c / τd`. -/
example {c phi gamma z beta : ℝ} :
    infiniteSlopeSafetyRatio
        (infiniteSlopeResistingStress c phi gamma z beta
          (infiniteSlopeNormalStress gamma z beta))
        gamma z beta
      = c / infiniteSlopeDrivingStress gamma z beta := by
  simp [infiniteSlopeSafetyRatio, infiniteSlopeResistingStress]

/-- Dry cohesionless endpoint on the witness slab: the
ratio at `u = 0` with `c = 0` is
`tan phi / tan beta = 1`. -/
example : infiniteSlopeSafetyRatio
      (infiniteSlopeResistingStress 0 (Real.pi / 4) 2 3
        (Real.pi / 4) 0)
      2 3 (Real.pi / 4) = 1 := by
  unfold infiniteSlopeSafetyRatio infiniteSlopeResistingStress
  rw [witnessNormal, witnessDriving, Real.tan_pi_div_four]
  norm_num

/-- Composition with admission: if the slab is admitted
(ratio at least one) at `u₂`, it is admitted at every
admissible `u₁ ≤ u₂`. -/
example {c phi gamma z beta u₁ u₂ : ℝ}
    (hgamma : 0 < gamma) (hz : 0 < z) (hbeta0 : 0 < beta)
    (hbeta : beta < Real.pi / 2)
    (hphi0 : 0 ≤ phi) (hphi : phi < Real.pi / 2)
    (hu₁ : u₁ ∈ Set.Icc 0 (infiniteSlopeNormalStress gamma z beta))
    (hu₂ : u₂ ∈ Set.Icc 0 (infiniteSlopeNormalStress gamma z beta))
    (hle : u₁ ≤ u₂)
    (hadm : 1 ≤ infiniteSlopeSafetyRatio
      (infiniteSlopeResistingStress c phi gamma z beta u₂)
      gamma z beta) :
    1 ≤ infiniteSlopeSafetyRatio
      (infiniteSlopeResistingStress c phi gamma z beta u₁)
      gamma z beta :=
  le_trans hadm
    (infiniteSlopeSafetyRatio_antitoneOn_porePressure hgamma hz
      hbeta0 hbeta hphi0 hphi hu₁ hu₂ hle)

#print axioms EarthScience.infiniteSlopeSafetyRatio_porePressure_sub
#print axioms
  EarthScience.infiniteSlopeSafetyRatio_antitoneOn_porePressure
#print axioms
  EarthScience.infiniteSlopeSafetyRatio_strictAntiOn_porePressure
#print axioms
  EarthScience.infiniteSlopeSafetyRatio_eqOn_porePressure_of_phi_eq_zero
#print axioms
  EarthScience.infiniteSlopeSafetyRatio_porePressure_monotonicity

end PhyslibExtTest.EarthScience.Geotechnical.InfiniteSlope

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import PhyslibExt.EarthScience.Geotechnical.LayeredStressProfile
import PhyslibExt.EarthScience.Geotechnical.EffectiveStress
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Layered stress profile checks

Concrete consumers of
`PhyslibExt.EarthScience.Geotechnical.LayeredStressProfile`
on the two-layer column `t = (2, 3)`, `γ = (18, 20)`,
`q = 10`, `γw = 10` with the water table at depth `2`, plus
domain controls: interior water table, negative thickness,
off-column values, monotonicity slope sign, and the
hydrostatic, unit-weight, and compression-positive entry
bridges.

## i. Overview

These are elaboration and sign checks, not new results.

## ii. Key results

No new definitions or results are introduced here.

## iii. Table of contents

- A. Two-layer numerals
- B. Water-table placements and monotonicity
- C. Bridges and controls

## iv. References

- `PhyslibExt.EarthScience.Geotechnical.LayeredStressProfile`
-/

open EarthScience

namespace PhyslibExtTest.EarthScience.Geotechnical.LayeredStressProfile

noncomputable def tNeg : ℕ → ℝ := fun i => if i = 0 then -1 else 2

noncomputable def t2 : ℕ → ℝ := fun i => if i = 0 then 2 else 3

noncomputable def γ2 : ℕ → ℝ := fun i => if i = 0 then 18 else 20

lemma ht2 : ∀ i, 0 ≤ t2 i := fun i => by
  unfold t2
  split_ifs <;> norm_num

lemma top2_0 : layerTop t2 0 = 0 := by simp [layerTop]

lemma top2_1 : layerTop t2 1 = 2 := by simp [layerTop, t2]

lemma top2_2 : layerTop t2 2 = 5 := by
  norm_num [layerTop, t2, Finset.sum_range_succ]

/-! ## A. Two-layer numerals -/

/-- Total stress `86` at depth `4`. -/
example : layeredTotalStress 2 10 t2 γ2 4 = 86 := by
  rw [layeredTotalStress_on_layer (k := 1) (by norm_num) 10 γ2 ht2
    (by rw [top2_1]; norm_num) (by rw [top2_2]; norm_num), top2_1]
  norm_num [t2, γ2]

/-- Effective stress above the table: `28` at depth `1`. -/
example : layeredEffectiveStress 2 10 10 (layerTop t2 1) t2 γ2 1 = 28 := by
  rw [layeredEffectiveStress_on_layer_above (k := 0) (by norm_num)
    (by norm_num) 10 10 γ2 ht2 (by rw [top2_0]; norm_num)
    (by rw [top2_1]; norm_num), top2_0]
  norm_num [γ2]

/-- Effective stress below the table: `66` at depth `4`. -/
example : layeredEffectiveStress 2 10 10 (layerTop t2 1) t2 γ2 4 = 66 := by
  rw [layeredEffectiveStress_on_layer_below (k := 1) (by norm_num) le_rfl
    10 10 γ2 ht2 (by rw [top2_1]; norm_num) (by rw [top2_2]; norm_num),
    top2_1]
  norm_num [t2, γ2]

/-- Submerged slope increment `20` over `[3, 5]`. -/
example : layeredEffectiveStress 2 10 10 (layerTop t2 1) t2 γ2 5
    - layeredEffectiveStress 2 10 10 (layerTop t2 1) t2 γ2 3 = 20 := by
  rw [layeredEffectiveStress_sub_submerged (k := 1) (by norm_num) le_rfl
    10 10 γ2 ht2 (by rw [top2_1]; norm_num) (by norm_num) (by rw [top2_2])]
  norm_num [γ2]

/-- Layer-1 total-stress increment `60`. -/
example : layeredTotalStress 2 10 t2 γ2 (layerTop t2 2)
    - layeredTotalStress 2 10 t2 γ2 (layerTop t2 1) = 60 := by
  rw [layeredTotalStress_layer_increment (k := 1) (by norm_num) 10 γ2 ht2,
    intervalIntegral.integral_const, smul_eq_mul, top2_1, top2_2]
  norm_num [γ2]

/-! ## B. Water-table placements and monotonicity -/

/-- Water table at the surface (`m = 0`). -/
example {n k : ℕ} (hk : k < n) (q γw : ℝ) {t : ℕ → ℝ} (γ : ℕ → ℝ)
    (ht : ∀ i, 0 ≤ t i) {z : ℝ}
    (h1 : layerTop t k ≤ z) (h2 : z ≤ layerTop t (k + 1)) :
    layeredEffectiveStress n q γw (layerTop t 0) t γ z
      = q + (∑ i ∈ Finset.range k, γ i * t i) + γ k * (z - layerTop t k)
        - γw * z := by
  rw [layeredEffectiveStress_on_layer_below hk (Nat.zero_le k) q γw γ ht h1 h2]
  simp [layerTop]

/-- Dry column (`m = n`): effective equals total stress. -/
example {n k : ℕ} (hk : k < n) (q γw : ℝ) {t : ℕ → ℝ} (γ : ℕ → ℝ)
    (ht : ∀ i, 0 ≤ t i) {z : ℝ}
    (h1 : layerTop t k ≤ z) (h2 : z ≤ layerTop t (k + 1)) :
    layeredEffectiveStress n q γw (layerTop t n) t γ z
      = layeredTotalStress n q t γ z := by
  rw [layeredEffectiveStress_on_layer_above hk hk q γw γ ht h1 h2,
    layeredTotalStress_on_layer hk q γ ht h1 h2]

/-- Water table below the column (`m = 3 > n = 2`): the
effective stress at depth `4` is the total stress `86`. -/
example : layeredEffectiveStress 2 10 10 (layerTop t2 3) t2 γ2 4 = 86 := by
  rw [layeredEffectiveStress_on_layer_above (k := 1) (m := 3) (by norm_num)
    (by norm_num) 10 10 γ2 ht2 (by rw [top2_1]; norm_num)
    (by rw [top2_2]; norm_num), top2_1]
  norm_num [t2, γ2]

/-- Below-water monotonicity when `γ k ≥ γw`. -/
example {n k m : ℕ} (hk : k < n) (hmk : m ≤ k) (q γw : ℝ) {t : ℕ → ℝ}
    (γ : ℕ → ℝ) (ht : ∀ i, 0 ≤ t i) (hge : γw ≤ γ k) {z₁ z₂ : ℝ}
    (h1 : layerTop t k ≤ z₁) (h12 : z₁ ≤ z₂) (h2 : z₂ ≤ layerTop t (k + 1)) :
    layeredEffectiveStress n q γw (layerTop t m) t γ z₁
      ≤ layeredEffectiveStress n q γw (layerTop t m) t γ z₂ := by
  have h := layeredEffectiveStress_sub_submerged hk hmk q γw γ ht h1 h12 h2
  nlinarith [mul_nonneg (sub_nonneg.2 hge) (sub_nonneg.2 h12)]

/-- Strict decrease when `γ k < γw`. -/
example {n k m : ℕ} (hk : k < n) (hmk : m ≤ k) (q γw : ℝ) {t : ℕ → ℝ}
    (γ : ℕ → ℝ) (ht : ∀ i, 0 ≤ t i) (hlt : γ k < γw) {z₁ z₂ : ℝ}
    (h1 : layerTop t k ≤ z₁) (h12 : z₁ < z₂) (h2 : z₂ ≤ layerTop t (k + 1)) :
    layeredEffectiveStress n q γw (layerTop t m) t γ z₂
      < layeredEffectiveStress n q γw (layerTop t m) t γ z₁ := by
  have h := layeredEffectiveStress_sub_submerged hk hmk q γw γ ht h1 h12.le h2
  nlinarith

/-- Interior water table: one layer `[0, 4]`, table at `2`;
`2` is no interface and the profile is not affine on the
layer (values `0, 40, 60` at `0, 2, 4`). -/
example : (∀ m : ℕ, layerTop (fun _ => (4 : ℝ)) m ≠ 2) ∧
    2 * layeredEffectiveStress 1 0 10 2 (fun _ => 4) (fun _ => 20) 2 ≠
      layeredEffectiveStress 1 0 10 2 (fun _ => 4) (fun _ => 20) 0
        + layeredEffectiveStress 1 0 10 2 (fun _ => 4) (fun _ => 20) 4 := by
  have hform : ∀ z : ℝ, 0 ≤ z → z ≤ 4 →
      layeredEffectiveStress 1 0 10 2 (fun _ => 4) (fun _ => 20) z
        = 20 * z - 10 * max (z - 2) 0 := by
    intro z h0 h4
    have h := layeredEffectiveStress_on_layer (n := 1) (k := 0)
      (t := fun _ => (4 : ℝ)) (by norm_num) 0 10 2
      (fun _ => 20) (fun _ => by norm_num)
      (by simpa [layerTop] using h0) (by simpa [layerTop] using h4)
    rw [h]
    simp [layerTop]
  refine ⟨fun m h => ?_, ?_⟩
  · simp [layerTop] at h
    have h' : ((m * 2 : ℕ) : ℝ) = 1 := by push_cast; linarith
    norm_cast at h'
    omega
  · rw [hform 2 (by norm_num) (by norm_num), hform 0 (by norm_num) (by norm_num),
      hform 4 (by norm_num) (by norm_num)]
    norm_num

/-! ## C. Bridges and controls -/

/-- Hydrostatic bridge, as a client of the module lemma. -/
example {ρ g zw z : ℝ} (h : zw ≤ z) :
    staticPorePressure (ρ * g) zw z
        = (fun d => (0 : ℝ) + ρ * g * d) (z - zw)
      ∧ HasDerivAt (fun d => (0 : ℝ) + ρ * g * d) (ρ * g) (z - zw) :=
  staticPorePressure_eq_hydrostatic_of_ge h

/-- Unit-weight slope bridge and its positivity criterion. -/
example {n k m : ℕ} (hk : k < n) (hmk : m ≤ k) (q γw Gs e : ℝ)
    {t : ℕ → ℝ} (γ : ℕ → ℝ) (ht : ∀ i, 0 ≤ t i)
    (hγk : γ k = bulkUnitWeight Gs 1 e γw) (he : 1 + e ≠ 0) {z₁ z₂ : ℝ}
    (h1 : layerTop t k ≤ z₁) (h12 : z₁ ≤ z₂) (h2 : z₂ ≤ layerTop t (k + 1)) :
    layeredEffectiveStress n q γw (layerTop t m) t γ z₂
      - layeredEffectiveStress n q γw (layerTop t m) t γ z₁
        = submergedUnitWeight Gs e γw * (z₂ - z₁) :=
  layeredEffectiveStress_sub_submergedUnitWeight hk hmk q γw Gs e γ ht hγk he
    h1 h12 h2

example {Gs e γw : ℝ} (hγ : 0 < γw) (he : 0 < 1 + e) :
    0 < submergedUnitWeight Gs e γw ↔ 1 < Gs :=
  submerged_pos_iff hγ he

/-- Compression-positive entry bridge: the profile is the
`(0, 0)` entry of the effective stress of a hydrostatic
total stress. -/
example (n : ℕ) (q γw zw : ℝ) (t γ : ℕ → ℝ) (z : ℝ) :
    effectiveStressCompressionPositive
        (layeredTotalStress n q t γ z • (1 : Matrix (Fin 1) (Fin 1) ℝ))
        (staticPorePressure γw zw z) 0 0
      = layeredEffectiveStress n q γw zw t γ z := by
  simp [effectiveStressCompressionPositive, layeredEffectiveStress]

/-- Orientation control: `γw * max (zw - z) 0` is not the
static profile. -/
example : staticPorePressure 10 2 5 ≠ 10 * max (2 - 5) 0 := by
  norm_num [staticPorePressure]

/-- Negative-thickness control: without `0 ≤ t`, the
on-layer formula fails (actual `1`, formula `0`). -/
example : layerTop tNeg 1 ≤ 0 ∧ 0 ≤ layerTop tNeg 2 ∧ ¬ (∀ i, 0 ≤ tNeg i) ∧
    layeredTotalStress 2 0 tNeg (fun _ => 1) 0 = 1 ∧
    (0 : ℝ) + (∑ i ∈ Finset.range 1, (fun _ => (1 : ℝ)) i * tNeg i)
      + (fun _ => (1 : ℝ)) 1 * (0 - layerTop tNeg 1) = 0 := by
  refine ⟨?_, ?_, fun h => by have := h 0; norm_num [tNeg] at this, ?_, ?_⟩ <;>
    norm_num [layerTop, layeredTotalStress, traversedThickness, tNeg,
      Finset.sum_range_succ, max_def, min_def]

/-- Off-column values: constant surcharge above the surface
and full overburden below the base. -/
example : layeredTotalStress 2 10 t2 γ2 (-1) = 10 := by
  norm_num [layeredTotalStress, traversedThickness, layerTop, t2, γ2,
    Finset.sum_range_succ, max_def, min_def]

example : layeredTotalStress 2 10 t2 γ2 9 = 106 := by
  norm_num [layeredTotalStress, traversedThickness, layerTop, t2, γ2,
    Finset.sum_range_succ, max_def, min_def]

/-- Empty column: total stress is the surcharge. -/
example (q : ℝ) (t γ : ℕ → ℝ) (z : ℝ) :
    layeredTotalStress 0 q t γ z = q := by
  simp [layeredTotalStress]

#print axioms EarthScience.layeredTotalStress_on_layer
#print axioms EarthScience.layeredEffectiveStress_on_layer
#print axioms EarthScience.continuous_layeredEffectiveStress
#print axioms EarthScience.layeredEffectiveStress_continuous_and_on_layer
#print axioms EarthScience.layeredEffectiveStress_continuous_and_affine_on_each_layer
#print axioms EarthScience.staticPorePressure_eq_hydrostatic_of_ge
#print axioms EarthScience.layeredEffectiveStress_sub_submergedUnitWeight

end PhyslibExtTest.EarthScience.Geotechnical.LayeredStressProfile

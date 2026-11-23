/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import PhyslibExt.EarthScience.HydrostaticColumn
public import PhyslibExt.EarthScience.Geotechnical.UnitWeights
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Layered vertical effective-stress profile

## i. Overview

Contiguous horizontal layers are prefix sums of thicknesses
`t` with layer unit weights `γ`, a compression-positive
surcharge `q`, and a static water table at depth `zw`. Depth
`z` increases downward from the ground surface. Total stress
is surcharge plus `Σ γ i * traversed thickness`; pore
pressure is the static profile `γw * max (z - zw) 0`, gauge
zero at the table; effective stress is the difference, in
the compression-positive convention. The profile is
continuous everywhere and affine on each layer when the
water table is a layer break; the general on-layer formula
covers a table inside a layer without splitting. The
physical column is `0 ≤ z ≤ layerTop t n` with `t i ≥ 0`;
static water only (no seepage, perched water, or capillary
rise).

## ii. Key results

- `EarthScience.layeredTotalStress_on_layer` and
  `layeredEffectiveStress_on_layer`: the affine on-layer
  forms.
- `EarthScience.continuous_layeredEffectiveStress`: the
  profile is continuous in depth.
- `EarthScience.layeredEffectiveStress_continuous_and_affine_on_each_layer`:
  continuity packaged with per-layer affinity at an
  interface water table.
- `EarthScience.staticPorePressure_eq_hydrostatic_of_ge`
  and `layeredEffectiveStress_sub_submergedUnitWeight`: the
  hydrostatic-column and submerged-unit-weight bridges.

## iii. Table of contents

- A. Layer geometry and stress definitions
- B. On-layer profiles and continuity
- C. Bridges to the hydrostatic column and unit weights

## iv. References

- J. A. Knappett and R. F. Craig, *Craig's Soil Mechanics*,
  9th edition, CRC Press, 2019: total, pore-water, and
  effective stress in layered soil.
- `PhyslibExt.EarthScience.HydrostaticColumn` for the
  depth-coordinate hydrostatic profile.
- `PhyslibExt.EarthScience.Geotechnical.UnitWeights` for
  bulk and submerged unit weights.
-/

@[expose] public section

namespace EarthScience

/-! ## A. Layer geometry and stress definitions -/

/-- Depth of the top of layer `k`: prefix sum of thicknesses. -/
noncomputable def layerTop (t : ℕ → ℝ) (k : ℕ) : ℝ :=
  ∑ i ∈ Finset.range k, t i

/-- Thickness of layer `i` traversed at depth `z`, clamped to
the layer interval. -/
noncomputable def traversedThickness (t : ℕ → ℝ) (i : ℕ) (z : ℝ) : ℝ :=
  max (layerTop t i) (min z (layerTop t (i + 1))) - layerTop t i

/-- Total vertical stress: surcharge plus the layer sum. -/
noncomputable def layeredTotalStress (n : ℕ) (q : ℝ) (t γ : ℕ → ℝ)
    (z : ℝ) : ℝ :=
  q + ∑ i ∈ Finset.range n, γ i * traversedThickness t i z

/-- Static pore pressure below a water table at depth `zw`. -/
noncomputable def staticPorePressure (γw zw z : ℝ) : ℝ :=
  γw * max (z - zw) 0

/-- Effective vertical stress: total minus static pore
pressure. -/
noncomputable def layeredEffectiveStress (n : ℕ) (q γw zw : ℝ)
    (t γ : ℕ → ℝ) (z : ℝ) : ℝ :=
  layeredTotalStress n q t γ z - staticPorePressure γw zw z

private lemma layerTop_succ' (t : ℕ → ℝ) (k : ℕ) :
    layerTop t (k + 1) = layerTop t k + t k := by
  simp [layerTop, Finset.sum_range_succ]

private lemma layerTop_mono' {t : ℕ → ℝ} (ht : ∀ i, 0 ≤ t i) {a b : ℕ}
    (h : a ≤ b) :
    layerTop t a ≤ layerTop t b := by
  unfold layerTop
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro x hx
    simp [Finset.mem_range] at hx ⊢
    omega
  · intro i _ _
    exact ht i

private lemma traversed_of_le {t : ℕ → ℝ} (ht : ∀ i, 0 ≤ t i) (i : ℕ) (z : ℝ)
    (hz : z ≤ layerTop t i) : traversedThickness t i z = 0 := by
  unfold traversedThickness
  have hmono : layerTop t i ≤ layerTop t (i + 1) :=
    layerTop_mono' ht (Nat.le_succ i)
  have hmin : min z (layerTop t (i + 1)) = z := min_eq_left (le_trans hz hmono)
  have hmax : max (layerTop t i) z = layerTop t i := max_eq_left hz
  rw [hmin, hmax, sub_self]

private lemma traversed_of_ge {t : ℕ → ℝ} (ht : ∀ i, 0 ≤ t i) (i : ℕ) (z : ℝ)
    (hz : layerTop t (i + 1) ≤ z) : traversedThickness t i z = t i := by
  unfold traversedThickness
  have hmono : layerTop t i ≤ layerTop t (i + 1) :=
    layerTop_mono' ht (Nat.le_succ i)
  have hmin : min z (layerTop t (i + 1)) = layerTop t (i + 1) :=
    min_eq_right hz
  have hmax : max (layerTop t i) (layerTop t (i + 1)) = layerTop t (i + 1) :=
    max_eq_right hmono
  rw [hmin, hmax]
  have hsucc := layerTop_succ' t i
  linarith

private lemma traversed_of_mem {t : ℕ → ℝ} (_ht : ∀ i, 0 ≤ t i) (i : ℕ) (z : ℝ)
    (h1 : layerTop t i ≤ z) (h2 : z ≤ layerTop t (i + 1)) :
    traversedThickness t i z = z - layerTop t i := by
  unfold traversedThickness
  have hmin : min z (layerTop t (i + 1)) = z := min_eq_left h2
  have hmax : max (layerTop t i) z = z := max_eq_right h1
  rw [hmin, hmax]

/-! ## B. On-layer profiles and continuity -/

/-- On layer `k` the total stress is the affine form:
surcharge plus completed layers plus `γ k` times depth into
the layer. -/
theorem layeredTotalStress_on_layer {n k : ℕ} (hk : k < n) (q : ℝ)
    {t : ℕ → ℝ} (γ : ℕ → ℝ) (ht : ∀ i, 0 ≤ t i) {z : ℝ}
    (h1 : layerTop t k ≤ z) (h2 : z ≤ layerTop t (k + 1)) :
    layeredTotalStress n q t γ z
      = q + (∑ i ∈ Finset.range k, γ i * t i) + γ k * (z - layerTop t k) := by
  unfold layeredTotalStress
  have hkle : k ≤ n := Nat.le_of_lt hk
  have hsplit := Finset.sum_range_add_sum_Ico
    (fun i => γ i * traversedThickness t i z) hkle
  have hhead := Finset.sum_eq_sum_Ico_succ_bot hk
    (fun i => γ i * traversedThickness t i z)
  have hearly : ∀ i ∈ Finset.range k,
      γ i * traversedThickness t i z = γ i * t i := by
    intro i hi
    rw [Finset.mem_range] at hi
    have hle : i + 1 ≤ k := hi
    have hmono : layerTop t (i + 1) ≤ layerTop t k := layerTop_mono' ht hle
    have hz : layerTop t (i + 1) ≤ z := le_trans hmono h1
    rw [traversed_of_ge ht i z hz]
  have hlate : ∀ i ∈ Finset.Ico (k + 1) n,
      γ i * traversedThickness t i z = 0 := by
    intro i hi
    rw [Finset.mem_Ico] at hi
    have hmono : layerTop t (k + 1) ≤ layerTop t i := layerTop_mono' ht hi.1
    have hz : z ≤ layerTop t i := le_trans h2 hmono
    rw [traversed_of_le ht i z hz, mul_zero]
  have hsum_early : (∑ i ∈ Finset.range k, γ i * traversedThickness t i z)
      = ∑ i ∈ Finset.range k, γ i * t i :=
    Finset.sum_congr rfl hearly
  have hsum_late :
      (∑ i ∈ Finset.Ico (k + 1) n, γ i * traversedThickness t i z) = 0 :=
    Finset.sum_eq_zero hlate
  have hmid : γ k * traversedThickness t k z = γ k * (z - layerTop t k) := by
    rw [traversed_of_mem ht k z h1 h2]
  have hcomb : (∑ i ∈ Finset.range n, γ i * traversedThickness t i z)
      = (∑ i ∈ Finset.range k, γ i * t i) + γ k * (z - layerTop t k) := by
    calc (∑ i ∈ Finset.range n, γ i * traversedThickness t i z)
        = (∑ i ∈ Finset.range k, γ i * traversedThickness t i z)
          + (∑ i ∈ Finset.Ico k n, γ i * traversedThickness t i z) :=
          hsplit.symm
      _ = (∑ i ∈ Finset.range k, γ i * traversedThickness t i z)
          + (γ k * traversedThickness t k z
            + (∑ i ∈ Finset.Ico (k + 1) n,
              γ i * traversedThickness t i z)) := by
          rw [hhead]
      _ = (∑ i ∈ Finset.range k, γ i * t i) + γ k * (z - layerTop t k) := by
          rw [hsum_early, hmid, hsum_late, add_zero]
  rw [hcomb]
  ring

/-- Above the water table (at interface `m`), effective
stress on layer `k < m` has no pore-pressure term. -/
theorem layeredEffectiveStress_on_layer_above {n k m : ℕ} (hk : k < n)
    (hkm : k < m) (q γw : ℝ) {t : ℕ → ℝ} (γ : ℕ → ℝ)
    (ht : ∀ i, 0 ≤ t i) {z : ℝ}
    (h1 : layerTop t k ≤ z) (h2 : z ≤ layerTop t (k + 1)) :
    layeredEffectiveStress n q γw (layerTop t m) t γ z
      = q + (∑ i ∈ Finset.range k, γ i * t i) + γ k * (z - layerTop t k) := by
  unfold layeredEffectiveStress staticPorePressure
  have htot := layeredTotalStress_on_layer hk q γ ht h1 h2
  rw [htot]
  have hmono : layerTop t (k + 1) ≤ layerTop t m :=
    layerTop_mono' ht (by omega)
  have hz : z ≤ layerTop t m := le_trans h2 hmono
  have hle : z - layerTop t m ≤ 0 := by linarith
  have hmax : max (z - layerTop t m) 0 = 0 := max_eq_right hle
  rw [hmax, mul_zero, sub_zero]

/-- Below the water table (at interface `m`), effective
stress on layer `k ≥ m` subtracts `γw * (z - layerTop t m)`. -/
theorem layeredEffectiveStress_on_layer_below {n k m : ℕ} (hk : k < n)
    (hmk : m ≤ k) (q γw : ℝ) {t : ℕ → ℝ} (γ : ℕ → ℝ)
    (ht : ∀ i, 0 ≤ t i) {z : ℝ}
    (h1 : layerTop t k ≤ z) (h2 : z ≤ layerTop t (k + 1)) :
    layeredEffectiveStress n q γw (layerTop t m) t γ z
      = q + (∑ i ∈ Finset.range k, γ i * t i) + γ k * (z - layerTop t k)
        - γw * (z - layerTop t m) := by
  unfold layeredEffectiveStress staticPorePressure
  have htot := layeredTotalStress_on_layer hk q γ ht h1 h2
  rw [htot]
  have hmono : layerTop t m ≤ layerTop t k := layerTop_mono' ht hmk
  have hz : layerTop t m ≤ z := le_trans hmono h1
  have hge : 0 ≤ z - layerTop t m := by linarith
  have hmax : max (z - layerTop t m) 0 = z - layerTop t m := max_eq_left hge
  rw [hmax]

/-- The effective-stress profile is continuous in depth. -/
lemma continuous_layeredEffectiveStress (n : ℕ) (q γw zw : ℝ)
    (t γ : ℕ → ℝ) :
    Continuous (layeredEffectiveStress n q γw zw t γ) := by
  unfold layeredEffectiveStress layeredTotalStress staticPorePressure
    traversedThickness
  fun_prop

/-- On a submerged layer the effective-stress slope is
`γ k - γw`. -/
lemma layeredEffectiveStress_sub_submerged {n k m : ℕ} (hk : k < n)
    (hmk : m ≤ k) (q γw : ℝ) {t : ℕ → ℝ} (γ : ℕ → ℝ)
    (ht : ∀ i, 0 ≤ t i) {z₁ z₂ : ℝ}
    (h1 : layerTop t k ≤ z₁) (h12 : z₁ ≤ z₂)
    (h2 : z₂ ≤ layerTop t (k + 1)) :
    layeredEffectiveStress n q γw (layerTop t m) t γ z₂
      - layeredEffectiveStress n q γw (layerTop t m) t γ z₁
        = (γ k - γw) * (z₂ - z₁) := by
  have h1' : layerTop t k ≤ z₂ := le_trans h1 h12
  have h2' : z₁ ≤ layerTop t (k + 1) := le_trans h12 h2
  have ha := layeredEffectiveStress_on_layer_below hk hmk q γw γ ht h1' h2
  have hb := layeredEffectiveStress_on_layer_below hk hmk q γw γ ht h1 h2'
  rw [ha, hb]
  ring

/-- The total-stress increment across one layer is the
integral of the constant `γ k` over that layer (not an
overburden-integral statement for a varying profile). -/
lemma layeredTotalStress_layer_increment {n k : ℕ} (hk : k < n)
    (q : ℝ) {t : ℕ → ℝ} (γ : ℕ → ℝ) (ht : ∀ i, 0 ≤ t i) :
    layeredTotalStress n q t γ (layerTop t (k + 1))
        - layeredTotalStress n q t γ (layerTop t k)
      = ∫ _ in layerTop t k..layerTop t (k + 1), γ k := by
  have hle : layerTop t k ≤ layerTop t (k + 1) :=
    layerTop_mono' ht (Nat.le_succ k)
  have htop := layeredTotalStress_on_layer hk q γ ht hle le_rfl
  have hbot := layeredTotalStress_on_layer hk q γ ht le_rfl hle
  rw [htop, hbot, intervalIntegral.integral_const, smul_eq_mul]
  ring

/-- On layer `k`, for a water table at any depth `zw`, the
effective stress is the affine total stress minus
`γw * max (z - zw) 0` (affine on each side of the table). -/
theorem layeredEffectiveStress_on_layer {n k : ℕ} (hk : k < n)
    (q γw zw : ℝ) {t : ℕ → ℝ} (γ : ℕ → ℝ)
    (ht : ∀ i, 0 ≤ t i) {z : ℝ}
    (h1 : layerTop t k ≤ z) (h2 : z ≤ layerTop t (k + 1)) :
    layeredEffectiveStress n q γw zw t γ z
      = q + (∑ i ∈ Finset.range k, γ i * t i) + γ k * (z - layerTop t k)
        - γw * max (z - zw) 0 := by
  unfold layeredEffectiveStress staticPorePressure
  have htot := layeredTotalStress_on_layer hk q γ ht h1 h2
  rw [htot]

/-- Packaged profile statement: the effective stress is
continuous and has the on-layer affine-minus-hydrostatic
form on every layer, for a water table at any depth. -/
theorem layeredEffectiveStress_continuous_and_on_layer (n : ℕ)
    (q γw zw : ℝ) {t : ℕ → ℝ} (γ : ℕ → ℝ) (ht : ∀ i, 0 ≤ t i) :
    Continuous (layeredEffectiveStress n q γw zw t γ)
      ∧ ∀ k : ℕ, k < n → ∀ z : ℝ, layerTop t k ≤ z →
        z ≤ layerTop t (k + 1) →
        layeredEffectiveStress n q γw zw t γ z
          = q + (∑ i ∈ Finset.range k, γ i * t i)
            + γ k * (z - layerTop t k) - γw * max (z - zw) 0 := by
  constructor
  · exact continuous_layeredEffectiveStress n q γw zw t γ
  · intro k hk z h1 h2
    exact layeredEffectiveStress_on_layer hk q γw zw γ ht h1 h2

/-- With the water table at an interface, the effective
stress is continuous and affine (`a + b * z`) on every
layer. -/
theorem layeredEffectiveStress_continuous_and_affine_on_each_layer
    {n m : ℕ} (q γw : ℝ) {t : ℕ → ℝ} (γ : ℕ → ℝ) (ht : ∀ i, 0 ≤ t i) :
    Continuous (layeredEffectiveStress n q γw (layerTop t m) t γ)
      ∧ ∀ k < n, ∃ a b : ℝ, ∀ z ∈ Set.Icc (layerTop t k) (layerTop t (k + 1)),
        layeredEffectiveStress n q γw (layerTop t m) t γ z = a + b * z := by
  refine ⟨continuous_layeredEffectiveStress n q γw (layerTop t m) t γ,
    fun k hk => ?_⟩
  by_cases hkm : k < m
  · refine ⟨q + (∑ i ∈ Finset.range k, γ i * t i) - γ k * layerTop t k,
      γ k, fun z hz => ?_⟩
    rw [layeredEffectiveStress_on_layer_above hk hkm q γw γ ht hz.1 hz.2]
    ring
  · refine ⟨q + (∑ i ∈ Finset.range k, γ i * t i) - γ k * layerTop t k
      + γw * layerTop t m, γ k - γw, fun z hz => ?_⟩
    rw [layeredEffectiveStress_on_layer_below hk (not_lt.mp hkm) q γw γ ht
      hz.1 hz.2]
    ring

/-! ## C. Bridges to the hydrostatic column and unit weights -/

/-- Below the table, the static pore pressure with
`γw = ρ * g` is the canonical depth-coordinate hydrostatic
profile at gauge zero, with its derivative. -/
lemma staticPorePressure_eq_hydrostatic_of_ge {ρ g zw z : ℝ}
    (h : zw ≤ z) :
    staticPorePressure (ρ * g) zw z
        = (fun d => (0 : ℝ) + ρ * g * d) (z - zw)
      ∧ HasDerivAt (fun d => (0 : ℝ) + ρ * g * d) (ρ * g) (z - zw) := by
  refine ⟨?_, (hydrostatic_pressure_depth 0 ρ g (z - zw)).1⟩
  unfold staticPorePressure
  rw [max_eq_left (by linarith)]
  ring

/-- For a saturated submerged layer with unit weight
`bulkUnitWeight Gs 1 e γw`, the effective-stress slope is
`submergedUnitWeight Gs e γw`. -/
lemma layeredEffectiveStress_sub_submergedUnitWeight {n k m : ℕ}
    (hk : k < n) (hmk : m ≤ k) (q γw Gs e : ℝ) {t : ℕ → ℝ} (γ : ℕ → ℝ)
    (ht : ∀ i, 0 ≤ t i) (hγk : γ k = bulkUnitWeight Gs 1 e γw)
    (he : 1 + e ≠ 0) {z₁ z₂ : ℝ}
    (h1 : layerTop t k ≤ z₁) (h12 : z₁ ≤ z₂)
    (h2 : z₂ ≤ layerTop t (k + 1)) :
    layeredEffectiveStress n q γw (layerTop t m) t γ z₂
      - layeredEffectiveStress n q γw (layerTop t m) t γ z₁
        = submergedUnitWeight Gs e γw * (z₂ - z₁) := by
  rw [layeredEffectiveStress_sub_submerged hk hmk q γw γ ht h1 h12 h2, hγk,
    submerged_eq_sat_sub_water he]

end EarthScience

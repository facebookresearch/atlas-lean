/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Set.Basic
public import Mathlib.Order.Monotone.Basic
public import Mathlib.LinearAlgebra.AffineSpace.AffineMap
public import PhyslibExt.EarthScience.SaturationPressure
import Mathlib.Tactic.Linarith

/-!
# Building-envelope no-supersaturation certificate

## i. Overview

For one homogeneous building-envelope layer, model temperature
and vapor partial pressure as affine between the two faces. If
the larger face vapor pressure is at most the saturation
pressure at the colder face temperature, monotonicity of the
saturation curve makes that value a lower bound over the whole
face-temperature interval, so the affine vapor pressure is
nowhere supersaturated in the layer. The layerwise form applies
the same certificate on a common partition. This is a
conservative admission for the affine steady model only; it
does not predict condensate or assert standards compliance.

## ii. Key results

- `Engineering.BuildingEnvelope.affine_no_supersaturation`:
  one-layer certificate.
- `Engineering.BuildingEnvelope.affine_no_supersaturation_layers`:
  common-partition layerwise form.
- `Engineering.BuildingEnvelope.affine_no_supersaturation_layers_saturationPressure`:
  specialization to the EarthScience saturation-pressure curve.

## iii. Table of contents

- A. Affine no-supersaturation certificate

## iv. References

- Standard steady-state (Glaser) vapor diffusion through a
  multilayer wall assembly.
- `PhyslibExt.EarthScience.SaturationPressure` for the
  Clausius-Clapeyron saturation-pressure model and its strict
  increase on positive temperatures.
-/

@[expose] public section

/-! ## A. Affine no-supersaturation certificate -/
namespace Engineering.BuildingEnvelope

/-- Affine profile between endpoint values `a` and `b`, as
Mathlib's affine line map. The normalized layer coordinate is
`θ`; the profile is the affine interpolation used on one
homogeneous layer, not a field equation. -/
noncomputable abbrev affineProfile (a b θ : ℝ) : ℝ :=
  AffineMap.lineMap a b θ

/-- The affine profile in coordinates:
`affineProfile a b θ = (1 - θ) * a + θ * b`. -/
@[simp] lemma affineProfile_apply (a b θ : ℝ) :
    affineProfile a b θ = (1 - θ) * a + θ * b :=
  AffineMap.lineMap_apply_ring a b θ

/-- Conservative one-layer no-supersaturation certificate.

Let `psat` be a saturation-pressure curve, monotone on positive
absolute temperatures. On one layer, the temperature and vapor
partial pressure are the affine profiles between face values
`(Tl, Tr)` and `(pl, pr)`, with `Tl, Tr > 0`. If the larger face
vapor pressure is at most `psat (min Tl Tr)` (the saturation
lower bound over the whole face-temperature interval supplied by
monotonicity), then at every `θ ∈ [0, 1]` the affine temperature
is positive and the affine vapor pressure does not exceed the
saturation pressure there. This is only a no-supersaturation
admission for the affine model, not a condensate prediction. -/
lemma affine_no_supersaturation {psat : ℝ → ℝ}
    (hmono : MonotoneOn psat (Set.Ioi 0))
    {Tl Tr pl pr θ : ℝ} (hTl : 0 < Tl) (hTr : 0 < Tr)
    (hcert : max pl pr ≤ psat (min Tl Tr))
    (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    0 < affineProfile Tl Tr θ
      ∧ affineProfile pl pr θ ≤ psat (affineProfile Tl Tr θ) := by
  have h1θ : 0 ≤ 1 - θ := by linarith
  have hTl_min : min Tl Tr ≤ Tl := min_le_left _ _
  have hTr_min : min Tl Tr ≤ Tr := min_le_right _ _
  have h1 : (1 - θ) * min Tl Tr ≤ (1 - θ) * Tl :=
    mul_le_mul_of_nonneg_left hTl_min h1θ
  have h2 : θ * min Tl Tr ≤ θ * Tr :=
    mul_le_mul_of_nonneg_left hTr_min hθ0
  have hminT : min Tl Tr ≤ affineProfile Tl Tr θ := by
    rw [affineProfile_apply]
    linarith
  have hpl : pl ≤ max pl pr := le_max_left _ _
  have hpr : pr ≤ max pl pr := le_max_right _ _
  have h3 : (1 - θ) * pl ≤ (1 - θ) * max pl pr :=
    mul_le_mul_of_nonneg_left hpl h1θ
  have h4 : θ * pr ≤ θ * max pl pr :=
    mul_le_mul_of_nonneg_left hpr hθ0
  have hP : affineProfile pl pr θ ≤ max pl pr := by
    rw [affineProfile_apply]
    linarith
  have hmin_pos : 0 < min Tl Tr := lt_min hTl hTr
  have hTpos : 0 < affineProfile Tl Tr θ := lt_of_lt_of_le hmin_pos hminT
  have hmem_min : min Tl Tr ∈ Set.Ioi 0 := Set.mem_Ioi.mpr hmin_pos
  have hmem_T : affineProfile Tl Tr θ ∈ Set.Ioi 0 := Set.mem_Ioi.mpr hTpos
  have hmono_le : psat (min Tl Tr) ≤ psat (affineProfile Tl Tr θ) :=
    hmono hmem_min hmem_T hminT
  exact ⟨hTpos, le_trans hP (le_trans hcert hmono_le)⟩

/-- Layerwise form on one common partition: if every face
temperature up to layer `n` is positive and every layer `i < n`
passes the same conservative endpoint-maximum certificate, then
every affine point of every layer has positive temperature and
is nowhere supersaturated. -/
lemma affine_no_supersaturation_layers {n : ℕ} {psat : ℝ → ℝ}
    (hmono : MonotoneOn psat (Set.Ioi 0))
    {Tface Pface : ℕ → ℝ}
    (hT : ∀ i : ℕ, i ≤ n → 0 < Tface i)
    (hcert : ∀ i : ℕ, i < n
      → max (Pface i) (Pface (i + 1))
        ≤ psat (min (Tface i) (Tface (i + 1))))
    {i : ℕ} {θ : ℝ} (hi : i < n) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    0 < affineProfile (Tface i) (Tface (i + 1)) θ
      ∧ affineProfile (Pface i) (Pface (i + 1)) θ
        ≤ psat (affineProfile (Tface i) (Tface (i + 1)) θ) := by
  have hi_le : i ≤ n := Nat.le_of_lt hi
  have hsucc_le : i + 1 ≤ n := hi
  exact affine_no_supersaturation hmono (hT i hi_le) (hT (i + 1) hsucc_le)
    (hcert i hi) hθ0 hθ1

/-- Layerwise no-supersaturation certificate for the
EarthScience Clausius-Clapeyron saturation-pressure curve
`T ↦ es0 * exp ((L / Rv) * (1 / T0 - 1 / T))`, with positive
parameters `es0`, `L`, `Rv`, and reference temperature `T0`. This is the generic layerwise
certificate instantiated with the saturation curve's strict
monotonicity on positive temperatures. -/
lemma affine_no_supersaturation_layers_saturationPressure
    {n : ℕ} {es0 L Rv T0 : ℝ} (hes0 : 0 < es0) (hL : 0 < L)
    (hRv : 0 < Rv) (_hT0 : 0 < T0) {Tface Pface : ℕ → ℝ}
    (hT : ∀ i : ℕ, i ≤ n → 0 < Tface i)
    (hcert : ∀ i : ℕ, i < n
      → max (Pface i) (Pface (i + 1))
        ≤ es0 * Real.exp ((L / Rv)
            * (1 / T0 - 1 / min (Tface i) (Tface (i + 1)))))
    {i : ℕ} {θ : ℝ} (hi : i < n) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    0 < affineProfile (Tface i) (Tface (i + 1)) θ
      ∧ affineProfile (Pface i) (Pface (i + 1)) θ
        ≤ es0 * Real.exp ((L / Rv)
            * (1 / T0
              - 1 / affineProfile (Tface i) (Tface (i + 1)) θ)) :=
  affine_no_supersaturation_layers
    (EarthScience.saturation_pressure_strictMono hes0 hL hRv).monotoneOn
    hT hcert hi hθ0 hθ1

end Engineering.BuildingEnvelope

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Basic.Real.Basic

public import Mathlib.Order.Filter.Defs
public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Topology.Order.Basic

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Moisture basis: wet and dry basis conversion

## i. Overview

Moisture content on the two standard bases, the single owned conversion
used by the drying models. For water mass `mw ≥ 0` and dry-solid mass
`ms > 0`, the wet basis is `w = mw / (mw + ms)` and the dry basis is
`X = mw / ms`. They are related by `X = w / (1 - w)` and `w = X / (1 + X)`;
`w = 1` (no dry solids) is outside the dry-basis conversion, and the dry
basis diverges as `w → 1`. Numerical values after a consistent choice of
mass units; dimensions are not tracked.

## ii. Key results

- `Drying.dryBasis_of_wetBasis` and `Drying.wetBasis_dryBasis_inv`: the two
  bases of one material determine each other.
- `Drying.wetOfDry_dryOfWet` and `Drying.dryOfWet_wetOfDry`: the basis maps
  are inverse on their domains.
- `Drying.dryOfWet_unbounded`: the dry basis is unbounded as the wet basis
  approaches `1`.
- `Drying.tendsto_dryOfWet_at_one`: that endpoint divergence as a limit
  from below.
- `Drying.wetBasis_eq_one_of_zero_solids`: with no dry solids the wet basis
  is `1`, outside the conversion.

## iii. Table of contents

- A. Wet and dry bases and their conversion

## iv. References

- A. S. Mujumdar (ed.), *Handbook of Industrial Drying*, 4th ed., CRC Press
  (2014), Chapter 1 (moisture content on wet and dry bases).
-/

@[expose] public section

namespace Engineering.Process.Drying

/-- Wet-basis moisture fraction `w = mw / (mw + ms)`. -/
noncomputable def wetBasis (mw ms : ℝ) : ℝ :=
  mw / (mw + ms)

/-- Dry-basis moisture ratio `X = mw / ms`. -/
noncomputable def dryBasis (mw ms : ℝ) : ℝ :=
  mw / ms

/-- Dry basis as a function of wet basis alone: `X = w / (1 - w)`. -/
noncomputable def dryOfWet (w : ℝ) : ℝ :=
  w / (1 - w)

/-- Wet basis as a function of dry basis alone: `w = X / (1 + X)`. -/
noncomputable def wetOfDry (X : ℝ) : ℝ :=
  X / (1 + X)

/-- The wet basis is nonnegative. -/
lemma wetBasis_nonneg {mw ms : ℝ} (hmw : 0 ≤ mw) (hms : 0 < ms) :
    0 ≤ wetBasis mw ms := by
  unfold wetBasis
  exact div_nonneg hmw (by linarith)

/-- With dry solids present, the wet basis is strictly below `1`. -/
lemma wetBasis_lt_one {mw ms : ℝ} (hmw : 0 ≤ mw) (hms : 0 < ms) :
    wetBasis mw ms < 1 := by
  have hpos : 0 < mw + ms := by linarith
  unfold wetBasis
  rw [div_lt_one hpos]
  linarith

/-- The dry basis is nonnegative. -/
lemma dryBasis_nonneg {mw ms : ℝ} (hmw : 0 ≤ mw) (hms : 0 < ms) :
    0 ≤ dryBasis mw ms := by
  unfold dryBasis
  exact div_nonneg hmw (le_of_lt hms)

/-- **Wet to dry.** The dry basis of a material is `w / (1 - w)` of its
wet basis. -/
lemma dryBasis_of_wetBasis {mw ms : ℝ} (hms : 0 < ms) (hmw : 0 ≤ mw) :
    dryBasis mw ms = dryOfWet (wetBasis mw ms) := by
  have hms' : ms ≠ 0 := ne_of_gt hms
  have hsum : mw + ms ≠ 0 := ne_of_gt (by linarith)
  have h1 : (1 : ℝ) - mw / (mw + ms) = ms / (mw + ms) := by
    field_simp
    ring
  unfold dryBasis dryOfWet wetBasis
  rw [h1]
  field_simp

/-- **Dry to wet.** The wet basis of a material is `X / (1 + X)` of its
dry basis. -/
lemma wetBasis_dryBasis_inv {mw ms : ℝ} (hms : 0 < ms) (hmw : 0 ≤ mw) :
    wetBasis mw ms = wetOfDry (dryBasis mw ms) := by
  have hms' : ms ≠ 0 := ne_of_gt hms
  have hsum : mw + ms ≠ 0 := ne_of_gt (by linarith)
  have h1 : (1 : ℝ) + mw / ms = (mw + ms) / ms := by
    field_simp
    ring
  unfold wetBasis wetOfDry dryBasis
  rw [h1]
  field_simp

/-- The two basis maps are inverse on `w < 1`. -/
lemma wetOfDry_dryOfWet {w : ℝ} (h1 : w < 1) :
    wetOfDry (dryOfWet w) = w := by
  have hne : (1 : ℝ) - w ≠ 0 := ne_of_gt (by linarith)
  have h2 : (1 : ℝ) + w / (1 - w) = 1 / (1 - w) := by
    field_simp
    ring
  unfold wetOfDry dryOfWet
  rw [h2]
  field_simp

/-- The two basis maps are inverse on nonnegative dry basis. -/
lemma dryOfWet_wetOfDry {X : ℝ} (hX : 0 ≤ X) :
    dryOfWet (wetOfDry X) = X := by
  have hne : (1 : ℝ) + X ≠ 0 := ne_of_gt (by linarith)
  have h1 : (1 : ℝ) - X / (1 + X) = 1 / (1 + X) := by
    field_simp
    ring
  unfold dryOfWet wetOfDry
  rw [h1]
  field_simp

/-- Divergence at the wet end: the dry basis is unbounded as the wet
basis approaches `1` from below. -/
lemma dryOfWet_unbounded (M : ℝ) :
    ∃ w : ℝ, 0 ≤ w ∧ w < 1 ∧ M < dryOfWet w := by
  set N : ℝ := |M| + 1 with hN
  have hNpos : 0 < N := by rw [hN]; positivity
  refine ⟨N / (N + 1), ?_, ?_, ?_⟩
  · exact div_nonneg (le_of_lt hNpos) (by linarith)
  · rw [div_lt_one (by linarith : (0 : ℝ) < N + 1)]
    linarith
  · have hM : M < N := lt_of_le_of_lt (le_abs_self M) (by linarith)
    have hcomp : dryOfWet (N / (N + 1)) = N := by
      have hne : N + 1 ≠ 0 := ne_of_gt (by linarith)
      have h1 : (1 : ℝ) - N / (N + 1) = 1 / (N + 1) := by
        field_simp
        ring
      unfold dryOfWet
      rw [h1]
      field_simp
    rw [hcomp]
    exact hM

/-- **Endpoint divergence.** The dry basis tends to infinity as the wet
basis approaches `1` from below: inputs sufficiently close to `1` exceed
every bound, not merely some input somewhere in `[0, 1)`. -/
lemma tendsto_dryOfWet_at_one :
    Filter.Tendsto dryOfWet (nhdsWithin 1 (Set.Iio 1)) Filter.atTop := by
  rw [Filter.tendsto_atTop]
  intro M
  by_cases hM : M ≤ 0
  · have h0 : ∀ᶠ w : ℝ in nhdsWithin 1 (Set.Iio 1), (0:ℝ) < w :=
      eventually_nhdsWithin_of_eventually_nhds (eventually_gt_nhds (by linarith : (0:ℝ) < 1))
    have hmem : ∀ᶠ w : ℝ in nhdsWithin 1 (Set.Iio 1), w ∈ Set.Iio (1:ℝ) :=
      self_mem_nhdsWithin
    filter_upwards [h0, hmem] with w hw0 hw1
    rw [Set.mem_Iio] at hw1
    unfold dryOfWet
    have hden : (0:ℝ) < 1 - w := by linarith
    have hnn : (0:ℝ) ≤ w / (1 - w) := div_nonneg (le_of_lt hw0) (le_of_lt hden)
    linarith
  · have hMpos : 0 < M := not_le.mp hM
    set T : ℝ := M / (M + 1) with hT
    have hpos1 : (0:ℝ) < M + 1 := by linarith
    have hTlt1 : T < 1 := by
      rw [hT, div_lt_one hpos1]
      linarith
    have hev : ∀ᶠ w : ℝ in nhdsWithin 1 (Set.Iio 1), T < w :=
      eventually_nhdsWithin_of_eventually_nhds (eventually_gt_nhds hTlt1)
    have hmem : ∀ᶠ w : ℝ in nhdsWithin 1 (Set.Iio 1), w ∈ Set.Iio (1:ℝ) :=
      self_mem_nhdsWithin
    filter_upwards [hev, hmem] with w hwT hw1
    rw [Set.mem_Iio] at hw1
    unfold dryOfWet
    have hden : (0:ℝ) < 1 - w := by linarith
    rw [le_div_iff₀ hden]
    rw [hT, div_lt_iff₀ hpos1] at hwT
    have h2 : w * (M + 1) = M * w + w := by ring
    have h3 : M * (1 - w) = M - M * w := by ring
    rw [h2] at hwT
    rw [h3]
    linarith

/-- Assumption necessity: with no dry solids and positive water mass, the
wet basis equals `1`, so the `ms > 0` hypothesis in `wetBasis_lt_one`
cannot be dropped and `w = 1` stays outside the conversion. -/
lemma wetBasis_eq_one_of_zero_solids {mw : ℝ} (hmw : 0 < mw) :
    wetBasis mw 0 = 1 := by
  unfold wetBasis
  rw [add_zero]
  exact div_self (ne_of_gt hmw)

end Engineering.Process.Drying

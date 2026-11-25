/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import PhyslibExt.EarthScience.Geotechnical.WinklerFooting

/-!
# Full-contact Winkler admission

## i. Overview

The affine Winkler contact pressure `p(x) = ks * (a + b * x)` on
`[-B/2, B/2]` (see `EarthScience.footingResultantForce`) is
nonnegative at every footing point exactly when
`a ≥ |b| * B / 2`: the pressure is affine, so its minimum on the
interval is at an edge, and full contact (no tension cutoff) is
admissible exactly under this condition. Equality permits zero
pressure at one edge.

## ii. Key results

- `EarthScience.footingPressure_nonneg_iff`: the full-contact
  admission criterion.

## iii. Table of contents

- A. Full-contact admission

## iv. References

- J. E. Bowles, *Foundation Analysis and Design*, 5th edition,
  McGraw-Hill, 1996 (Winkler subgrade reaction; the affine contact
  pressure under combined settlement and rotation is nonnegative
  throughout exactly when its edge values are, which is the
  criterion proved here).
-/

@[expose] public section

namespace EarthScience

/-! ## A. Full-contact admission -/

/-- Contact pressure `ks * (a + b * x)` at a footing point `x`. -/
noncomputable def footingPressure (ks a b x : ℝ) : ℝ := ks * (a + b * x)

/-- Full-contact admission: for `ks > 0` and `B > 0`, pressure is nonnegative everywhere on
the footing `[-B / 2, B / 2]` exactly when `a ≥ |b| * B / 2`. -/
lemma footingPressure_nonneg_iff {ks a b B : ℝ} (hks : 0 < ks)
    (hB : 0 < B) :
    (∀ x ∈ Set.Icc (-B / 2) (B / 2), 0 ≤ footingPressure ks a b x)
      ↔ |b| * B / 2 ≤ a := by
  unfold footingPressure
  constructor
  · intro h
    by_cases hb : 0 ≤ b
    · have hxmem : -B / 2 ∈ Set.Icc (-B / 2) (B / 2) :=
        Set.mem_Icc.mpr ⟨le_refl _, by linarith⟩
      have h0 : 0 ≤ a + b * (-B / 2) :=
        (mul_nonneg_iff_of_pos_left hks).mp (h _ hxmem)
      rw [abs_of_nonneg hb]
      have e : b * (-B / 2) = -(b * B / 2) := by ring
      rw [e] at h0
      linarith
    · have hb' : b < 0 := lt_of_not_ge hb
      have hxmem : B / 2 ∈ Set.Icc (-B / 2) (B / 2) :=
        Set.mem_Icc.mpr ⟨by linarith, le_refl _⟩
      have h0 : 0 ≤ a + b * (B / 2) :=
        (mul_nonneg_iff_of_pos_left hks).mp (h _ hxmem)
      rw [abs_of_neg hb']
      have e : b * (B / 2) = -(-b * B / 2) := by ring
      rw [e] at h0
      linarith
  · intro h x hx
    obtain ⟨hlo, hhi⟩ := Set.mem_Icc.mp hx
    have hxabs : |x| ≤ B / 2 := abs_le.mpr ⟨by linarith, hhi⟩
    have h2 : |b * x| ≤ |b| * (B / 2) := by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left hxabs (abs_nonneg b)
    have h3 : -(|b| * (B / 2)) ≤ b * x := (abs_le.mp h2).1
    have e : |b| * (B / 2) = |b| * B / 2 := by ring
    rw [e] at h3
    have hinner : 0 ≤ a + b * x := by linarith
    exact mul_nonneg hks.le hinner

end EarthScience

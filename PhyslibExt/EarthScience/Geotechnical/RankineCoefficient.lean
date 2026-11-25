/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity

/-!
# Rankine active coefficient from the principal-stress limit

## i. Overview

Compression-positive principal stresses `σ1 ≥ σ3 ≥ 0`, cohesion
`c ≥ 0`, friction angle `0 ≤ φ < π / 2`. The Mohr–Coulomb
principal-stress limit equality is an explicit material input;
the result is its rearrangement into
`σ3 = K_a σ1 - 2 c √K_a` with the sine form
`K_a = (1 - sin φ) / (1 + sin φ)`, equal to the textbook
`tan² (π/4 - φ/2)`. No wall geometry or displacement is
included; the admission `0 ≤ σ3` excludes the tensile zone,
and no tension-crack or tension-cutoff model is included. The
admission premises `_horder`, `_hσ3`, and `_hc` are domain
markers the proof does not use: the equivalence is algebraic
for all real `σ1`, `σ3`, and `c` on the `φ` range, and
`_horder` in fact follows from `_hσ3`, `_hc`, the angle
bounds, and either side of the equivalence.

## ii. Key results

- `EarthScience.rankineActiveCoefficient`: the sine-form
  Rankine active coefficient.
- `EarthScience.sqrt_rankineActiveCoefficient` and its primed
  form: `√K_a = cos φ / (1 + sin φ) = (1 - sin φ) / cos φ`.
- `EarthScience.rankine_principal_limit_iff`: the
  principal-stress limit equality is the Rankine active
  formula.

## iii. Table of contents

- A. Coefficient, square roots, and the limit equivalence

## iv. References

- J. A. Knappett and R. F. Craig, *Craig's Soil Mechanics*,
  9th edition, CRC Press, 2019: Rankine active state and the
  Mohr–Coulomb principal-stress relation.
- `PhyslibExt.EarthScience.Geotechnical.RankineWall` for the
  dry cohesionless pressure law that consumes a supplied
  active coefficient.
-/

@[expose] public section

namespace EarthScience

/-! ## A. Coefficient, square roots, and the limit equivalence -/

/-- Rankine active earth-pressure coefficient, sine form. -/
noncomputable def rankineActiveCoefficient (φ : ℝ) : ℝ :=
  (1 - Real.sin φ) / (1 + Real.sin φ)

/-- Range of the active coefficient on the physical
friction-angle domain: `0 < K_a ≤ 1` (the positivity is
what the wall pressure and resultant consumers need). -/
lemma rankineActiveCoefficient_pos_le_one {φ : ℝ} (h0 : 0 ≤ φ)
    (h1 : φ < Real.pi / 2) :
    0 < rankineActiveCoefficient φ ∧ rankineActiveCoefficient φ ≤ 1 := by
  have hcos : 0 < Real.cos φ :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], h1⟩
  have hsin0 : 0 ≤ Real.sin φ :=
    Real.sin_nonneg_of_nonneg_of_le_pi h0 (by linarith [Real.pi_pos])
  have hs1 : Real.sin φ < 1 := by
    nlinarith [Real.sin_sq_add_cos_sq φ, Real.sin_le_one φ,
      Real.neg_one_le_sin φ, mul_pos hcos hcos]
  unfold rankineActiveCoefficient
  exact ⟨div_pos (by linarith) (by linarith),
    (div_le_one (by linarith)).2 (by linarith)⟩

/-- Square-root identity in the `cos φ / (1 + sin φ)` form. -/
lemma sqrt_rankineActiveCoefficient {φ : ℝ} (h0 : 0 ≤ φ)
    (h1 : φ < Real.pi / 2) :
    Real.sqrt (rankineActiveCoefficient φ)
      = Real.cos φ / (1 + Real.sin φ) := by
  have hs : 0 ≤ Real.sin φ :=
    Real.sin_nonneg_of_nonneg_of_le_pi h0 (by linarith [Real.pi_pos, h1])
  have hc : 0 < Real.cos φ :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos, h0], h1⟩
  have h1s : (0 : ℝ) < 1 + Real.sin φ := by linarith
  have h1sne : (1 : ℝ) + Real.sin φ ≠ 0 := ne_of_gt h1s
  have hcos2 : Real.cos φ ^ 2 = (1 - Real.sin φ) * (1 + Real.sin φ) := by
    have h := Real.sin_sq_add_cos_sq φ
    linear_combination h
  have hsq : (Real.cos φ / (1 + Real.sin φ)) ^ 2
      = rankineActiveCoefficient φ := by
    unfold rankineActiveCoefficient
    rw [div_pow, hcos2]
    field_simp
  have hnonneg : 0 ≤ Real.cos φ / (1 + Real.sin φ) :=
    div_nonneg hc.le h1s.le
  rw [← hsq]
  exact Real.sqrt_sq hnonneg

/-- Square-root identity in the `(1 - sin φ) / cos φ` form. -/
lemma sqrt_rankineActiveCoefficient' {φ : ℝ} (h0 : 0 ≤ φ)
    (h1 : φ < Real.pi / 2) :
    Real.sqrt (rankineActiveCoefficient φ)
      = (1 - Real.sin φ) / Real.cos φ := by
  rw [sqrt_rankineActiveCoefficient h0 h1]
  have hs : 0 ≤ Real.sin φ :=
    Real.sin_nonneg_of_nonneg_of_le_pi h0 (by linarith [Real.pi_pos, h1])
  have hc : 0 < Real.cos φ :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos, h0], h1⟩
  have h1s : (0 : ℝ) < 1 + Real.sin φ := by linarith
  have hcos2 : Real.cos φ ^ 2 = (1 - Real.sin φ) * (1 + Real.sin φ) := by
    have h := Real.sin_sq_add_cos_sq φ
    linear_combination h
  rw [div_eq_div_iff h1s.ne' hc.ne']
  linear_combination hcos2

/-- Main result: on the compression-positive physical domain,
the principal-stress limit equality is the Rankine active
formula. The underscore premises mark the admission domain
and are not used by the proof. -/
theorem rankine_principal_limit_iff {σ1 σ3 c φ : ℝ}
    (_horder : σ3 ≤ σ1) (_hσ3 : 0 ≤ σ3) (_hc : 0 ≤ c)
    (h0 : 0 ≤ φ) (h1 : φ < Real.pi / 2) :
    (σ1 - σ3) / 2 = ((σ1 + σ3) / 2) * Real.sin φ + c * Real.cos φ ↔
      σ3 = rankineActiveCoefficient φ * σ1
        - 2 * c * Real.sqrt (rankineActiveCoefficient φ) := by
  have hs : 0 ≤ Real.sin φ :=
    Real.sin_nonneg_of_nonneg_of_le_pi h0 (by linarith [Real.pi_pos, h1])
  have h1s : (0 : ℝ) < 1 + Real.sin φ := by linarith
  have h1sne : (1 : ℝ) + Real.sin φ ≠ 0 := ne_of_gt h1s
  rw [sqrt_rankineActiveCoefficient h0 h1]
  unfold rankineActiveCoefficient
  constructor
  · intro h
    have h2 : σ3 * (1 + Real.sin φ)
        = (1 - Real.sin φ) * σ1 - 2 * c * Real.cos φ := by
      linear_combination -2 * h
    field_simp
    linear_combination h2
  · intro h
    have h2 : σ3 * (1 + Real.sin φ)
        = (1 - Real.sin φ) * σ1 - 2 * c * Real.cos φ := by
      field_simp at h
      linear_combination h
    linear_combination (-1 / 2) * h2

end EarthScience

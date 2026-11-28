/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# The zero mode of the Helfrich sphere

For bending modulus $k_c > 0$, radius $R > 0$, spontaneous curvature $c_0 \in \mathbb{R}$
and pressure difference $p \in \mathbb{R}$, the $l = 0$ coefficient in the spherical
second-variation formula is $q_0(p) = R(p + 2k_c c_0/R^2)$. It is nonnegative exactly
when $p \ge p_c - 12k_c/R^3$, where $p_c = 2k_c(6-c_0 R)/R^3$. The algebra uses only
$R > 0$; the statement retains $k_c > 0$ from the vesicle model.

The lower bound for the zero mode is separate from the upper bound $p \le p_c$ for
simultaneous nonnegativity of all modes $l \ge 2$. The upper bound alone therefore does
not cover arbitrary coefficients $a_{lm}$: linearized volume preservation excludes $a_{00}$.
This module evaluates the printed mode formula; it does not derive the second variation or
prove vesicle stability.

## References

* Z. C. Tu and Z. C. Ou-Yang, *Elastic Theory of Low-Dimensional Continua and Its Applications in
  Bio- and Nano-Structures*, Journal of Computational and Theoretical Nanoscience 5 (2008),
  no. 4, pp. 422–448, §III.B.2, p. 431 (spherical mode formula immediately before Eq. (83),
  which gives the critical pressure).
* Ou-Yang Zhong-can and W. Helfrich, *Instability and Deformation of a Spherical Vesicle by
  Pressure*, Physical Review Letters 59 (1987), no. 21, pp. 2486–2488 (original critical-pressure
  result, cited at Eq. (83) in the review).
-/

@[expose] public section

namespace WantedExt.Biology.Biophysics.HelfrichSphereStabilityWanted

/-- The **mode coefficient** `q_l(p) = (R/2)[l(l+1) - 2]{2k_c [l(l+1) - c₀R]/R³ - p}` of the second
variation on the sphere of radius `R`. -/
noncomputable def modeCoeff (kc c₀ R p : ℝ) (l : ℕ) : ℝ :=
  R / 2 * ((l * (l + 1) : ℝ) - 2) * (2 * kc * ((l * (l + 1) : ℝ) - c₀ * R) / R ^ 3 - p)

/-- The **critical pressure** `p_c = 2k_c(6 - c₀R)/R³`. -/
noncomputable def criticalPressure (kc c₀ R : ℝ) : ℝ :=
  2 * kc * (6 - c₀ * R) / R ^ 3

/-- **The `l = 0` mode** (Tu and Ou-Yang 2008, clarified): for `k_c > 0` and `R > 0`,
`q_0(p) = R(p + 2k_c c₀/R²)`, and `q_0(p) ≥ 0` iff `p ≥ p_c - 12k_c/R³`.

Source: Tu and Ou-Yang (2008), second variation on the sphere. -/
theorem modeCoeff_zero (kc c₀ R p : ℝ) (hkc : 0 < kc) (hR : 0 < R) :
    modeCoeff kc c₀ R p 0 = R * (p + 2 * kc * c₀ / R ^ 2) ∧
      (0 ≤ modeCoeff kc c₀ R p 0 ↔ criticalPressure kc c₀ R - 12 * kc / R ^ 3 ≤ p) := by
  -- Keep the vesicle model's positive bending modulus; the algebra needs only `hR`.
  have _ := hkc
  have hmode : modeCoeff kc c₀ R p 0 = R * (p + 2 * kc * c₀ / R ^ 2) := by
    simp only [modeCoeff, Nat.cast_zero, zero_mul, zero_sub]
    field_simp [hR.ne']
    ring
  have hthreshold : criticalPressure kc c₀ R - 12 * kc / R ^ 3 = -(2 * kc * c₀ / R ^ 2) := by
    unfold criticalPressure
    field_simp [hR.ne']
    ring
  refine ⟨hmode, ?_⟩
  rw [hmode, hthreshold, mul_nonneg_iff_of_pos_left hR, neg_le_iff_add_nonneg]

end WantedExt.Biology.Biophysics.HelfrichSphereStabilityWanted

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Basic.Real.Basic

/-!
# Cohen's kappa

Two raters classify the same items into `k` categories with joint table `pᵢⱼ` (a probability
table: entries nonnegative, summing to `1`), row margins `pᵢ.` and column margins `p.ⱼ`. The
observed agreement is `p_o = ∑ᵢ pᵢᵢ`, the chance agreement is `p_e = ∑ᵢ pᵢ. p.ᵢ`, and Cohen's
kappa is `κ = (p_o - p_e) / (1 - p_e)`.

## Main statements

* `kappa_eq_zero_of_independent`: when the table is the product of its margins (independent
  raters), `p_o = p_e`, so `κ = 0` when `p_e < 1`.

The definitions follow Cohen (1960) as restated in secondary sources, and the statements here are
derived from them.

## References

* J. Cohen, "A coefficient of agreement for nominal scales", Educ. Psychol. Meas. 20 (1960)
  37–46, doi:10.1177/001316446002000104.
-/

@[expose] public section

namespace WantedExt.Biology.StatisticalGenetics.CohenKappaWanted

/-- `P` is a joint probability table: every entry is nonnegative and the entries sum to `1`. -/
def IsTable {k : ℕ} (P : Fin k → Fin k → ℝ) : Prop := (∀ i j, 0 ≤ P i j) ∧ ∑ i, ∑ j, P i j = 1

/-- Row margin `pᵢ. = ∑ⱼ pᵢⱼ`. -/
noncomputable def rowMargin {k : ℕ} (P : Fin k → Fin k → ℝ) (i : Fin k) : ℝ := ∑ j, P i j

/-- Column margin `p.ⱼ = ∑ᵢ pᵢⱼ`. -/
noncomputable def colMargin {k : ℕ} (P : Fin k → Fin k → ℝ) (j : Fin k) : ℝ := ∑ i, P i j

/-- Observed agreement `p_o = ∑ᵢ pᵢᵢ`. -/
noncomputable def observed {k : ℕ} (P : Fin k → Fin k → ℝ) : ℝ := ∑ i, P i i

/-- Chance agreement `p_e = ∑ᵢ pᵢ. p.ᵢ`. -/
noncomputable def chance {k : ℕ} (P : Fin k → Fin k → ℝ) : ℝ :=
  ∑ i, rowMargin P i * colMargin P i

/-- **Cohen's kappa** `κ = (p_o - p_e) / (1 - p_e)`. -/
noncomputable def kappa {k : ℕ} (P : Fin k → Fin k → ℝ) : ℝ :=
  (observed P - chance P) / (1 - chance P)

set_option linter.unusedVariables false in
/-- **Independent raters** (Cohen 1960; derived): let `P` be a joint probability table that is the
product of its margins (`pᵢⱼ = pᵢ. p.ⱼ` for all `i, j`) with chance agreement `p_e < 1`. Then
`κ = 0`.

Source: Cohen (1960). -/
public theorem kappa_eq_zero_of_independent {k : ℕ} (P : Fin k → Fin k → ℝ)
    (hP : IsTable P) (hind : ∀ i j, P i j = rowMargin P i * colMargin P j)
    (he : chance P < 1) :
    kappa P = 0 := by
  have h : observed P = chance P := by
    simp only [observed, chance, hind]
  simp only [kappa, h, sub_self, zero_div]

end WantedExt.Biology.StatisticalGenetics.CohenKappaWanted

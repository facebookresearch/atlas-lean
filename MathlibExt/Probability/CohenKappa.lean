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

For a joint probability table of two raters, Cohen's kappa compares observed agreement with
chance agreement computed from the margins. Perfect agreement is characterized directly from the
formula when chance agreement is less than one.

Reference: J. Cohen, "A coefficient of agreement for nominal scales", Educ. Psychol. Meas. 20
(1960) 37–46, doi:10.1177/001316446002000104. The equivalence is derived from the definition.
-/

@[expose] public section

-- Keep the original namespace so existing clients can use the same declarations.
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

-- Keep the named probability-table hypothesis from the original statement.
set_option linter.unusedVariables false in
/-- **Perfect agreement** (Cohen 1960; derived): let `P` be a joint probability table with chance
agreement `p_e < 1`. Then `κ = 1` if and only if the observed agreement is `p_o = 1`.

Source: Cohen (1960). -/
theorem kappa_eq_one_iff {k : ℕ} (P : Fin k → Fin k → ℝ) (hP : IsTable P)
    (he : chance P < 1) :
    kappa P = 1 ↔ observed P = 1 := by
  have hdenom : 1 - chance P ≠ 0 := (sub_pos.mpr he).ne'
  rw [kappa, div_eq_iff hdenom, one_mul, sub_left_inj]

end WantedExt.Biology.StatisticalGenetics.CohenKappaWanted

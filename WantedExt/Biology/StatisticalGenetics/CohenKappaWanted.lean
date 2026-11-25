/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Cohen's kappa and its maximum for fixed margins

Two raters classify the same items into `k` categories with joint table `pᵢⱼ` (a probability
table: entries nonnegative, summing to `1`), row margins `pᵢ.` and column margins `p.ⱼ`. The
observed agreement is `p_o = ∑ᵢ pᵢᵢ`, the chance agreement is `p_e = ∑ᵢ pᵢ. p.ᵢ`, and Cohen's
kappa is `κ = (p_o - p_e) / (1 - p_e)`. When `p_e < 1`: `κ = 1` if and only if the agreement is
perfect (`p_o = 1`); `κ = 0` when the table is the product of its margins (independent raters);
and, for fixed margins, `κ ≤ κ_max = (∑ᵢ min(pᵢ., p.ᵢ) - p_e) / (1 - p_e)`, since
`pᵢᵢ ≤ min(pᵢ., p.ᵢ)`, with equality for a table with these margins whose diagonal is
`min(pᵢ., p.ᵢ)` (Cohen's `κ_M`, the maximum permitted by the margins).

Recorded here: the three properties, including attainment of `κ_max`. The primary is paywalled
and was not read; the definitions follow Cohen (1960) as restated in secondary sources, and the
three properties are derived.

Sources: J. Cohen, "A coefficient of agreement for nominal scales", Educ. Psychol. Meas. 20
(1960) 37–46, doi:10.1177/001316446002000104.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Basic.Real.Basic

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

/-- The **maximum kappa for the margins of `P`**:
`κ_max = (∑ᵢ min(pᵢ., p.ᵢ) - p_e) / (1 - p_e)`. -/
noncomputable def kappaMax {k : ℕ} (P : Fin k → Fin k → ℝ) : ℝ :=
  (∑ i, min (rowMargin P i) (colMargin P i) - chance P) / (1 - chance P)

/-- **Perfect agreement** (Cohen 1960; derived): let `P` be a joint probability table with chance
agreement `p_e < 1`. Then `κ = 1` if and only if the observed agreement is `p_o = 1`.

Source: Cohen (1960). -/
public theorem_wanted kappa_eq_one_iff {k : ℕ} (P : Fin k → Fin k → ℝ) (hP : IsTable P)
    (he : chance P < 1) :
    kappa P = 1 ↔ observed P = 1

/-- **Independent raters** (Cohen 1960; derived): let `P` be a joint probability table that is the
product of its margins (`pᵢⱼ = pᵢ. p.ⱼ` for all `i, j`) with chance agreement `p_e < 1`. Then
`κ = 0`.

Source: Cohen (1960). -/
public theorem_wanted kappa_eq_zero_of_independent {k : ℕ} (P : Fin k → Fin k → ℝ)
    (hP : IsTable P) (hind : ∀ i j, P i j = rowMargin P i * colMargin P j)
    (he : chance P < 1) :
    kappa P = 0

/-- **The maximum kappa for fixed margins** (Cohen 1960; derived): let `P` be a joint probability
table with chance agreement `p_e < 1`. Then (1) `κ(P) ≤ κ_max(P)`; (2) every joint probability
table `Q` with the same row and column margins as `P` has `κ(Q) ≤ κ_max(P)`; and (3) the bound is
attained: some joint probability table `Q` with the same row and column margins as `P` has
`κ(Q) = κ_max(P)`. So `κ_max(P)` is the maximum of `κ` over the tables with the margins of `P`.

Source: Cohen (1960). -/
public theorem_wanted kappa_le_kappaMax {k : ℕ} (P : Fin k → Fin k → ℝ) (hP : IsTable P)
    (he : chance P < 1) :
    kappa P ≤ kappaMax P ∧
      (∀ Q : Fin k → Fin k → ℝ, IsTable Q → (∀ i, rowMargin Q i = rowMargin P i) →
        (∀ j, colMargin Q j = colMargin P j) → kappa Q ≤ kappaMax P) ∧
      ∃ Q : Fin k → Fin k → ℝ, IsTable Q ∧ (∀ i, rowMargin Q i = rowMargin P i) ∧
        (∀ j, colMargin Q j = colMargin P j) ∧ kappa Q = kappaMax P

end WantedExt.Biology.StatisticalGenetics.CohenKappaWanted

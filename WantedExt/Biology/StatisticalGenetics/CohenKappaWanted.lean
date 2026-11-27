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

Recorded here: perfect agreement. The definitions, the independent-raters property
(`kappa_eq_zero_of_independent`) and the maximum kappa for fixed margins, with its attainment
(`kappa_le_kappaMax`), are in `Domains.Biology.StatisticalGenetics.CohenKappa`, which this module
re-exports. The primary is paywalled and was not read; the definitions follow Cohen (1960) as
restated in secondary sources, and the three properties are derived.

Sources: J. Cohen, "A coefficient of agreement for nominal scales", Educ. Psychol. Meas. 20
(1960) 37–46, doi:10.1177/001316446002000104.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Basic.Real.Basic
public import Domains.Biology.StatisticalGenetics.CohenKappa

@[expose] public section

namespace WantedExt.Biology.StatisticalGenetics.CohenKappaWanted

/-- **Perfect agreement** (Cohen 1960; derived): let `P` be a joint probability table with chance
agreement `p_e < 1`. Then `κ = 1` if and only if the observed agreement is `p_o = 1`.

Source: Cohen (1960). -/
public theorem_wanted kappa_eq_one_iff {k : ℕ} (P : Fin k → Fin k → ℝ) (hP : IsTable P)
    (he : chance P < 1) :
    kappa P = 1 ↔ observed P = 1

end WantedExt.Biology.StatisticalGenetics.CohenKappaWanted

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Collapsibility and the noncollapsibility of the odds ratio

Let `X` (treatment), `Y` (response) and `Z` (covariate) be binary, with observed independence
`X ⊥ Z` (`P(X = x, Z = z) = P(X = x) P(Z = z)`). Under this observed-data independence, the
marginal risk given `X = x` is the common-weight `P(Z)`-mixture of the stratum risks `r(x, z)`,
and the risk ratio standardized to `P(Z)` equals the crude risk ratio (an observed-data identity;
causal non-confounding requires exchangeability assumptions not stated here). A risk difference or
risk ratio that is constant across the strata of `Z` is therefore strictly collapsible: its
marginal value equals the common stratum value. The odds ratio is not collapsible: if the odds
ratio `ψ ≠ 1` is constant across strata and `Z` is associated with the response given treatment,
the marginal odds ratio lies strictly between `1` and `ψ`; it equals `ψ` when `Z` is not
associated with the response.

Sources: S. Greenland, J. M. Robins and J. Pearl, "Confounding and collapsibility in causal
inference", Statist. Sci. 14 (1999) 29–46, pp. 37–39 and Tables 1–2, crediting M. H. Gail
(1986) for the odds-ratio statement.
-/
module

public import Batteries.Util.ProofWanted
public import Domains.Biology.StatisticalGenetics.AssociationTests.RiskEffectCollapsibility
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Basic.Real.Basic

@[expose] public section

namespace WantedExt.Biology.StatisticalGenetics.OddsRatioCollapsibilityWanted

/-- The odds `t / (1 - t)` of a probability `t`. It is meaningful for `t ≠ 1` (a probability in
`[0, 1)`); at `t = 1`, Lean's convention `x / 0 = 0` makes the value `0`. -/
noncomputable def odds (t : ℝ) : ℝ :=
  t / (1 - t)

/-- **Noncollapsibility of the odds ratio** (Greenland, Robins and Pearl 1999, p. 39; Gail 1986).
Let `q ∈ (0, 1)` be `P(Z = 1)`, let every stratum risk `r x z` lie in `(0, 1)`, and let
`m x = q r(x, 1) + (1 - q) r(x, 0)` be the marginal risk (the mixture that holds when `X` is
independent of `Z`). Suppose the stratum odds ratio is constant,
`odds (r 1 z) = ψ · odds (r 0 z)` for both `z`, with `ψ ≠ 1`, and that `Z` is associated with the
response given treatment, `r(0, 1) ≠ r(0, 0)`. Then the marginal odds ratio
`ω = odds (m 1) / odds (m 0)` lies strictly between `1` and `ψ`: `1 < ω < ψ` if `ψ > 1`, and
`ψ < ω < 1` if `ψ < 1`.

Source: Greenland, Robins and Pearl (1999), p. 39 and Table 2, crediting Gail (1986). -/
public theorem_wanted marginalOddsRatio_strictly_between (q : ℝ) (hq0 : 0 < q) (hq1 : q < 1)
    (r : Bool → Bool → ℝ) (hr0 : ∀ x z, 0 < r x z) (hr1 : ∀ x z, r x z < 1) (ψ : ℝ)
    (hψ : ∀ z, odds (r true z) = ψ * odds (r false z)) (hψ1 : ψ ≠ 1)
    (hassoc : r false true ≠ r false false) :
    let ω := odds (q * r true true + (1 - q) * r true false) /
      odds (q * r false true + (1 - q) * r false false)
    (1 < ψ → 1 < ω ∧ ω < ψ) ∧ (ψ < 1 → ψ < ω ∧ ω < 1)

/-- **No association, no change** (Greenland, Robins and Pearl 1999, p. 39). Let `q ∈ [0, 1]` be
`P(Z = 1)`, let every stratum risk `r x z` lie in `(0, 1)`, and let
`m x = q r(x, 1) + (1 - q) r(x, 0)` be the marginal risk. If `Z` is not associated with the
response given treatment, `r(x, 1) = r(x, 0)` for both `x`, and the stratum odds ratio is `ψ` in
each stratum, then the marginal odds ratio `odds (m 1) / odds (m 0)` equals `ψ`.

Source: Greenland, Robins and Pearl (1999), p. 39. -/
public theorem_wanted marginalOddsRatio_eq_of_no_assoc (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (r : Bool → Bool → ℝ) (hr0 : ∀ x z, 0 < r x z) (hr1 : ∀ x z, r x z < 1) (ψ : ℝ)
    (hψ : ∀ z, odds (r true z) = ψ * odds (r false z)) (hno : ∀ x, r x true = r x false) :
    odds (q * r true true + (1 - q) * r true false) /
      odds (q * r false true + (1 - q) * r false false) = ψ

end WantedExt.Biology.StatisticalGenetics.OddsRatioCollapsibilityWanted

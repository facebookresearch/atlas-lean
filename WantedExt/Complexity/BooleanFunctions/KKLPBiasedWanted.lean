/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Complexity.BooleanFunctions.KKL.KKLInequality

/-!
# The KKL inequality for `p`-biased product measures

The Kahn–Kalai–Linial inequality for the Bernoulli(`p`) product measure on `{0, 1}^E`, for every
`p ∈ (0, 1)`, with a constant depending only on `p`:
`c(p) · Var(1_A) · log (1 / maxₑ Infₑ(A)) ≤ ∑ₑ Infₑ(A)`.

The ported library proves the case `p = 1/2` with `c = 2`
(`StatMech.Probability.fsr_pbiased_endpoint`); for `p ≠ 1/2` it carries the inequality
as the hypothesis `StatMech.Probability.KKLHypercontractive p c`.

The ported sharp-threshold modules ask for the constant `c = 2` on an interval `(1/2, q)`
(`StatMech.Probability.kpb_PBiasedHC`). That uniform constant is not a published result and is
not recorded here; the published theorem gives some `c(p) > 0`, which degrades as `p → 0` or
`p → 1`.

## Main statements

* `kkl_pbiased`: for every `p ∈ (0, 1)` there is `c > 0` with `KKLHypercontractive p c`.

## References

* J. Bourgain, J. Kahn, G. Kalai, Y. Katznelson, N. Linial, *The influence of variables in
  product spaces*, Israel J. Math. 77 (1992), 55–64.
* M. Talagrand, *On Russo's approximate zero-one law*, Ann. Probab. 22 (1994), 1576–1587.
* E. Friedgut, G. Kalai, *Every monotone graph property has a sharp threshold*, Proc. Amer.
  Math. Soc. 124 (1996), 2993–3002.
-/

@[expose] public section

namespace MathlibExt.Complexity.BooleanFunctions.KKLPBiasedWanted

open StatMech.Probability

/-- **KKL inequality for `p`-biased measures** (Bourgain–Kahn–Kalai–Katznelson–Linial;
Talagrand). For every `p ∈ (0, 1)` there is `c > 0` such that for every finite nonempty `E` and
every Boolean function `φ` on `{0, 1}^E`,
`c · Var_p(φ) · log (1 / maxₑ Infₑ^p(φ)) ≤ ∑ₑ Infₑ^p(φ)`, where `Infₑ^p(φ)` is the probability
under the Bernoulli(`p`) product measure that `e` is pivotal for `φ`.

Talagrand's inequality `Var_p(φ) ≤ K(p) ∑ₑ Infₑ / log (1 / (p (1 - p) Infₑ))` gives this with
`c = 1 / K(p)`, since each `Infₑ ≤ maxₑ Infₑ`.

Source: M. Talagrand, *On Russo's approximate zero-one law*, Ann. Probab. 22 (1994);
J. Bourgain, J. Kahn, G. Kalai, Y. Katznelson, N. Linial, *The influence of variables in product
spaces*, Israel J. Math. 77 (1992). -/
public theorem_wanted kkl_pbiased :
    ∀ p : ℝ, 0 < p → p < 1 → ∃ c : ℝ, 0 < c ∧ KKLHypercontractive p c

end MathlibExt.Complexity.BooleanFunctions.KKLPBiasedWanted

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import MathlibExt.Analysis.HarmonicAnalysis.DyadicMaximal

/-!
# Vector-valued dyadic maximal inequality (statement)

The scalar weak type (1,1) and `L^p` bounds for the dyadic maximal function are proved in
`MathlibExt.Analysis.HarmonicAnalysis.DyadicMaximal`. This module records the vector-valued
extension of C. Fefferman and E. M. Stein in the normalisation of that module: dyadic intervals
`[m 2^{-k}, (m + 1) 2^{-k})` of `ℝ` with Lebesgue measure, and averages of `‖f‖ₑ`.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace MathlibExt.Analysis.HarmonicAnalysis.VectorValuedMaximalWanted

open MathlibExt.Analysis.HarmonicAnalysis.DyadicMaximal

/-- **Dyadic Fefferman–Stein vector-valued maximal inequality.** For `1 < p, q < ∞` there is a
finite constant `C` such that for every sequence of measurable functions `f_i : ℝ → ℝ`,
`∫ (∑_i (M_d f_i)^q)^{p/q} ≤ C ∫ (∑_i |f_i|^q)^{p/q}`, that is
`‖(M_d f_i)_i‖_{L^p(ℓ^q)} ≤ C^{1/p} ‖(f_i)_i‖_{L^p(ℓ^q)}` (T. Hytönen, *Dyadic analysis and
weights*, lecture notes, University of Helsinki, version of 2 May 2014, Theorem 4.9 with `μ`
the Lebesgue measure on `ℝ`; C. Fefferman and E. M. Stein, *Some maximal inequalities*,
Amer. J. Math. 93 (1971), 107–115, for the Hardy–Littlewood maximal function on `ℝ^n`). -/
public theorem_wanted exists_lintegral_tsum_rpow_dyadicMaximalFunction_le {p q : ℝ}
    (_hp : 1 < p) (_hq : 1 < q) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ f : ℕ → ℝ → ℝ, (∀ i, Measurable (f i)) →
      ∫⁻ x, (∑' i, dyadicMaximalFunction (f i) x ^ q) ^ (p / q) ≤
        C * ∫⁻ x, (∑' i, ‖f i x‖ₑ ^ q) ^ (p / q)

end MathlibExt.Analysis.HarmonicAnalysis.VectorValuedMaximalWanted

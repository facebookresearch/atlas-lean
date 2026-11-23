/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Ultraflat unimodular polynomials exist (Hayman-Lingham, Problem 4.31, (D4) and (D5))

W. K. Hayman and E. F. Lingham, Research Problems in Function Theory, Problem 4.31 (P. Erdős and D.
Newman), for `f(z) = ∑_{k=0}^{n} a_k z^k` with `|a_k| = 1` (D1): is there any `n`-th degree
polynomial of the form (D1) for which `min_{|z|=1} |f(z)| > (1 - ε) n^{1/2}` (D4) for every positive
`ε` if `n > n₀(ε)`? Perhaps there is an `n`-th degree polynomial of the form (D1) for which, for all
`z`, `|z| = 1`, `(1 - ε) n^{1/2} < |f(z)| < (1 + ε) n^{1/2}` (D5).
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.Complex.Norm

@[expose] public section

namespace MathlibExt.Analysis.UltraflatUnimodularPolynomialsAMR22Problem4031Wanted

/-!
Source: W. K. Hayman and E. F. Lingham, Research Problems in Function Theory, Fiftieth Anniversary
Edition (2019), arXiv:1809.07200, Problem 4.31 (P. Erdős and D. Newman). UnsolvedMath record
UM-02304031 (`AMR-022-4031`), dataset ulamai/UnsolvedMath v1.8.0.

Only (D4) and (D5) are stated here. The other parts of Problem 4.31: (D2) for unimodular
coefficients is refuted (WantedExt `UnimodularPolynomialSupNormErdosProblem230Wanted`, the same
problem as Erdős Problem 230); (D2) for coefficients `±1` is the open entry
`OpenConjectures/Analysis/ErdosProblem1150`; whether `n^{3/10+ε}` can be replaced by `n^ε` in (D3)
and whether (D5) holds with `n^{1/2} + O(1)` are the open entry
`OpenConjectures/Analysis/UnimodularPolynomialFlatnessErrorTerms`; (D2) for sparse `±1` polynomials
is not formalized. '`n > n₀(ε)`' is read as: for every `ε > 0` there is `n₀` such that for every `n
> n₀` some polynomial of degree `n` of the form (D1) satisfies the bound; the minimum over the
circle exceeds a bound iff every value does, since the circle is compact.
-/

/-- The value at `z` of the polynomial `f(z) = ∑_{k=0}^{n} a_k z^k` with coefficients `a`. -/
noncomputable def polyEval {n : ℕ} (a : Fin (n + 1) → ℂ) (z : ℂ) : ℂ :=
  ∑ k, a k * z ^ (k : ℕ)

/-- Erdős–Newman's question (D4): for every `ε > 0` and every `n > n₀(ε)` there is a polynomial
`f(z) = ∑_{k=0}^{n} a_k z^k` with `|a_k| = 1` and `min_{|z|=1} |f(z)| > (1 - ε) n^{1/2}`. -/
def unimodularMinLowerBound : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ, ∀ n : ℕ, n₀ < n → ∃ a : Fin (n + 1) → ℂ, (∀ k, ‖a k‖ = 1) ∧
    ∀ z : ℂ, ‖z‖ = 1 → (1 - ε) * Real.sqrt n < ‖polyEval a z‖

/-- Erdős–Newman's question (D5): for every `ε > 0` and every `n > n₀(ε)` there is a polynomial
`f(z) = ∑_{k=0}^{n} a_k z^k` with `|a_k| = 1` and `(1 - ε) n^{1/2} < |f(z)| < (1 + ε) n^{1/2}` for
all `|z| = 1` (an ultraflat polynomial). -/
def unimodularUltraflat : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ, ∀ n : ℕ, n₀ < n → ∃ a : Fin (n + 1) → ℂ, (∀ k, ‖a k‖ = 1) ∧
    ∀ z : ℂ, ‖z‖ = 1 →
      (1 - ε) * Real.sqrt n < ‖polyEval a z‖ ∧ ‖polyEval a z‖ < (1 + ε) * Real.sqrt n

/--
Resolved true: Kahane's ultraflat polynomials satisfy `|f(z)| = (1 + o(1)) n^{1/2}` uniformly on
`|z| = 1`, so for every `ε > 0` and large `n` their minimum on the circle exceeds `(1 - ε) n^{1/2}`.
Source: W. K. Hayman and E. F. Lingham, Research Problems in Function Theory, Fiftieth Anniversary
Edition (2019), arXiv:1809.07200, Problem 4.31 (P. Erdős and D. Newman); resolution: J.-P. Kahane,
Sur les polynômes à coefficients unimodulaires, Bull. London Math. Soc. 12 (1980), 321-342; as
recorded on erdosproblems.com/230 (Problem 4.31 of Hayman's list), erdosproblems.com/230 (the
Erdős–Newman conjecture, 'Problem 4.31 in [Ha74]'): 'Kahane constructed ultraflat polynomials P(z) =
∑ a_k z^k with |a_k| = 1 such that P(z) = (1 + o(1)) √n uniformly for all z with |z| = 1'; Bombieri
and Bourgain (JEMS 2009) improve the error to O(n^{7/18} (log n)^{O(1)}),
https://www.erdosproblems.com/230.
-/
public theorem_wanted unimodularMinLowerBound_holds : unimodularMinLowerBound

/--
Resolved true: Kahane's ultraflat polynomials satisfy `(1 - ε) n^{1/2} < |f(z)| < (1 + ε) n^{1/2}`
on `|z| = 1` for every `ε > 0` once `n` is large. Source: W. K. Hayman and E. F. Lingham, Research
Problems in Function Theory, Fiftieth Anniversary Edition (2019), arXiv:1809.07200, Problem 4.31 (P.
Erdős and D. Newman); resolution: J.-P. Kahane, Sur les polynômes à coefficients unimodulaires,
Bull. London Math. Soc. 12 (1980), 321-342; as recorded on erdosproblems.com/230 (Problem 4.31 of
Hayman's list), erdosproblems.com/230 (the Erdős–Newman conjecture, 'Problem 4.31 in [Ha74]'):
'Kahane constructed ultraflat polynomials P(z) = ∑ a_k z^k with |a_k| = 1 such that P(z) = (1 +
o(1)) √n uniformly for all z with |z| = 1'; Bombieri and Bourgain (JEMS 2009) improve the error to
O(n^{7/18} (log n)^{O(1)}), https://www.erdosproblems.com/230.
-/
public theorem_wanted unimodularUltraflat_holds : unimodularUltraflat

end MathlibExt.Analysis.UltraflatUnimodularPolynomialsAMR22Problem4031Wanted

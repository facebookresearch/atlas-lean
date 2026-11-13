/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Derivatives of polynomials on connected lemniscates (Erdős Problem 115)

Erdős Problem 115: if `p` is a polynomial of degree `n` such that `{z : |p(z)| ≤ 1}` is connected,
is `max |p'(z)|` over that set at most `(1/2 + o(1)) n²`?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.Analysis.CStarAlgebra.Classes

@[expose] public section

namespace MathlibExt.Analysis.ConnectedLemniscateDerivativeErdosProblem115Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #115, https://www.erdosproblems.com/115 (status PROVED
(LEAN)). UnsolvedMath record UM-30006728 (`EP-115`), dataset ulamai/UnsolvedMath v1.8.0.

`p` is monic. The record's wording drops this normalization, but it is part of the problem: Erëmenko
states the conjecture of Erdős proved by Erëmenko and Lempert for monic polynomials (A. Erëmenko, A
Markov-type inequality for arbitrary plane continua, Proc. Amer. Math. Soc. 135 (2007), 1505-1510,
Theorem A), and erdosproblems.com's remark that the maximum is at least `n` with equality only for
`z^n` holds only for monic `p`. Without it the claim is false: for `a z^n` the set is connected and
the maximum is `n |a|^{1/n}`, unbounded in `a`. `(1/2 + o(1)) n²` is read as: for every `ε > 0` and
all large `n`. Compared with the formal-conjectures statement `ErdosProblems/115.lean` (equivalent;
it is also stated for monic `p`; no code imported).
-/

open Filter

/-- Erdős Problem 115: for every `ε > 0` and all large `n`, every monic complex polynomial `p` of
degree `n` whose filled lemniscate `{z : |p z| ≤ 1}` is connected satisfies `|p' z| ≤ (1/2 + ε) n²`
on that set. -/
def connectedLemniscateDerivativeBound : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop, ∀ p : Polynomial ℂ, p.Monic → p.natDegree = n →
    IsConnected {z : ℂ | ‖p.eval z‖ ≤ 1} → ∀ z : ℂ, ‖p.eval z‖ ≤ 1 →
      ‖p.derivative.eval z‖ ≤ (1 / 2 + ε) * (n : ℝ) ^ 2

/--
Resolved true: Erëmenko and Lempert proved that for monic `p` of degree `n` with connected `{|p| ≤
1}`, `|p'| ≤ 2^{1/n - 1} n²` on that set, the value attained by the Chebyshev polynomials; `2^{1/n -
1} n² ≤ (1/2 + ε) n²` once `2^{1/n} ≤ 1 + 2ε`. erdosproblems.com/115 lists the problem as proved.
Source: T. F. Bloom, Erdős Problems, Problem #115, https://www.erdosproblems.com/115 (status PROVED
(LEAN)); resolution: A. Erëmenko and L. Lempert, An extremal problem for polynomials, Proc. Amer.
Math. Soc. 122 (1994), 191-193, main theorem, as restated in A. Erëmenko, Proc. Amer. Math. Soc. 135
(2007), Theorem A: for monic p of degree n with {|p| ≤ 1} connected, sup over that set of |p'| ≤
2^{1/n - 1} n², attained by Chebyshev polynomials (erdosproblems.com/115).
-/
public theorem_wanted connectedLemniscateDerivativeBound_holds : connectedLemniscateDerivativeBound

end MathlibExt.Analysis.ConnectedLemniscateDerivativeErdosProblem115Wanted

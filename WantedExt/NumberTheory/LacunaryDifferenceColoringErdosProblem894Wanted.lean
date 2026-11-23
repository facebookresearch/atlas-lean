/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Chromatic number of lacunary Cayley graphs on the integers (Erdős Problem 894)

Erdős Problem 894: let `A = {n_1 < n_2 < ⋯} ⊂ ℕ` be lacunary (some `ε > 0` has `n_{k+1} ≥ (1 + ε)
n_k` for all `k`). Must there exist a finite coloring of `ℕ` with no monochromatic solutions to `a -
b ∈ A`?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Basic.Real.Basic

@[expose] public section

namespace MathlibExt.NumberTheory.LacunaryDifferenceColoringErdosProblem894Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #894, https://www.erdosproblems.com/894 (status
PROVED). UnsolvedMath record UM-30007072 (`EP-894`), dataset ulamai/UnsolvedMath v1.8.0.

The `n_k` are positive (a zero term would forbid `a = b` and make the question false), and `n_{k+1}
≥ (1 + ε) n_k` makes the sequence strictly increasing. A monochromatic solution is `b` and `b + n_k`
of the same color. Compared with the formal-conjectures statement `ErdosProblems/894.lean`
(formal-conjectures' `IsLacunary` asks for the ratio bound only eventually, the same for increasing
positive sequences; no code imported).
-/

/-- Erdős Problem 894: for every lacunary sequence of positive integers `a_k` (some `ε > 0` has
`a_{k+1} ≥ (1 + ε) a_k` for all `k`) there is a coloring of `ℕ` with finitely many colors and no
two integers of the same color whose difference is some `a_k`. -/
def lacunaryDifferenceColoring : Prop :=
  ∀ a : ℕ → ℕ, (∀ k, 0 < a k) → (∃ ε : ℝ, 0 < ε ∧ ∀ k, (1 + ε) * a k ≤ a (k + 1)) →
    ∃ (r : ℕ) (col : ℕ → Fin r), ∀ b k, col (b + a k) ≠ col b

/--
Resolved true: Katznelson bounded the chromatic number of the Cayley graph of a lacunary sequence,
and Peres and Schlag showed it is at most `C r^{-1} |log r|` when `n_{k+1} / n_k > 1 + r`;
erdosproblems.com/894 lists the problem as proved. Source: T. F. Bloom, Erdős Problems, Problem
#894, https://www.erdosproblems.com/894 (status PROVED); resolution: Y. Katznelson, Chromatic
numbers of Cayley graphs on ℤ and recurrence, Combinatorica (2001), 211-219; Y. Peres and W. Schlag,
Two Erdős problems on lacunary sequences: chromatic number and Diophantine approximation, Bull.
Lond. Math. Soc. (2010), 295-300, arXiv:0706.0223, Peres-Schlag Theorem 1.1: if n_{j+1}/n_j ≥ 1 + ε
with 0 < ε < 1/4, some θ has inf_j ‖θ n_j‖ > c ε |log ε|^{-1}, and coloring n by the arc of length
at most δ containing θn (Katznelson's argument, Section 1) gives chromatic number at most ⌈δ^{-1}⌉ <
C ε^{-1} |log ε| for the graph on ℤ joining x, y when |x - y| is some n_j; erdosproblems.com/894:
the answer is yes, https://arxiv.org/abs/0706.0223.
-/
public theorem_wanted lacunaryDifferenceColoring_holds : lacunaryDifferenceColoring

end MathlibExt.NumberTheory.LacunaryDifferenceColoringErdosProblem894Wanted

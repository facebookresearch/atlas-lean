/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Area of polynomial lemniscates with roots in the unit disc (Erdős Problem 116)

Erdős Problem 116: let `p(z) = ∏_{i ≤ n} (z - zᵢ)` with `|zᵢ| ≤ 1`. Is the area of `{z : |p(z)| <
1}` greater than `n^{-O(1)}` (or perhaps even `(log n)^{-O(1)}`)?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis

@[expose] public section

namespace MathlibExt.Analysis.LemniscateAreaLowerBoundErdosProblem116Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #116, https://www.erdosproblems.com/116 (status PROVED
(LEAN)). UnsolvedMath record UM-30006729 (`EP-116`), dataset ulamai/UnsolvedMath v1.8.0.

Area is Lebesgue measure on `ℂ`. `> n^{-O(1)}` is read as `≥ c n^{-C}` for all `n ≥ 1` with
constants `c > 0` and `C`, and the parenthetical form as `≥ c (log n)^{-C}` for `n ≥ 2`; each is a
target. Compared with the formal-conjectures statement `ErdosProblems/116.lean` (the first target is
equivalent to `erdos_116`; the second follows from `erdos_116.variants.log`, its case `C = 1`; no
code imported).
-/

open MeasureTheory

/-- Erdős Problem 116, main question: there are `c > 0` and `C` such that for every `n ≥ 1` and
all `z₁, …, zₙ` in the closed unit disc, `{w : |∏ (w - zᵢ)| < 1}` has area at least `c n^{-C}`. -/
def lemniscateAreaPolynomialLowerBound : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∃ C : ℕ, ∀ n : ℕ, 0 < n → ∀ z : Fin n → ℂ, (∀ i, ‖z i‖ ≤ 1) →
    ENNReal.ofReal (c / (n : ℝ) ^ C) ≤ volume {w : ℂ | ‖∏ i, (w - z i)‖ < 1}

/-- Erdős Problem 116, stronger form: the area is at least `c (log n)^{-C}` for `n ≥ 2`. -/
def lemniscateAreaLogLowerBound : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∃ C : ℕ, ∀ n : ℕ, 2 ≤ n → ∀ z : Fin n → ℂ, (∀ i, ‖z i‖ ≤ 1) →
    ENNReal.ofReal (c / Real.log n ^ C) ≤ volume {w : ℂ | ‖∏ i, (w - z i)‖ < 1}

/--
Resolved true: the lower bound `≫ n^{-4}` for all `n ≥ 1` follows from a result of Pommerenke
(1961), and plby/lean-proofs has a formal proof of this statement (as formal-conjectures'
`erdos_116`); erdosproblems.com/116 lists the problem as proved. Source: T. F. Bloom, Erdős
Problems, Problem #116, https://www.erdosproblems.com/116 (status PROVED (LEAN)); resolution: C.
Pommerenke, On metric properties of complex polynomials, Michigan Math. J. 8 (1961), 97-115; M.
Krishnapur, E. Lundberg and K. Ramachandran, On the area of polynomial lemniscates, arXiv:2503.18270
(2025), area ≫ n^{-4} for all n ≥ 1 from Pommerenke's result (erdosproblems.com/116; formal proof
plby/lean-proofs src/latest/ErdosProblems/Erdos116.lean); Krishnapur-Lundberg-Ramachandran, Theorem
1: c / log n ≤ the minimal area for all large n, https://arxiv.org/abs/2503.18270.
-/
public theorem_wanted lemniscateAreaPolynomialLowerBound_holds : lemniscateAreaPolynomialLowerBound

/--
Resolved true: Krishnapur, Lundberg and Ramachandran proved (Theorem 1) that for all large `n` the
minimal area over monic polynomials of degree `n` with all zeros in the closed unit disc is at least
`c / log n` (and at most `C / log log n`); the finitely many smaller `n ≥ 2` are covered by
Pommerenke's `≫ n^{-4}` after shrinking `c`, so `C = 1` works. erdosproblems.com/116 records this
bound. Source: T. F. Bloom, Erdős Problems, Problem #116, https://www.erdosproblems.com/116 (status
PROVED (LEAN)); resolution: C. Pommerenke, On metric properties of complex polynomials, Michigan
Math. J. 8 (1961), 97-115; M. Krishnapur, E. Lundberg and K. Ramachandran, On the area of polynomial
lemniscates, arXiv:2503.18270 (2025), area ≫ n^{-4} for all n ≥ 1 from Pommerenke's result
(erdosproblems.com/116; formal proof plby/lean-proofs src/latest/ErdosProblems/Erdos116.lean);
Krishnapur-Lundberg-Ramachandran, Theorem 1: c / log n ≤ the minimal area for all large n,
https://arxiv.org/abs/2503.18270.
-/
public theorem_wanted lemniscateAreaLogLowerBound_holds : lemniscateAreaLogLowerBound

end MathlibExt.Analysis.LemniscateAreaLowerBoundErdosProblem116Wanted

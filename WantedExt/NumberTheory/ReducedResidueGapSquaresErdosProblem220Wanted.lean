/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Squared gaps between reduced residues (Erdős Problem 220)

Erdős Problem 220: let `n ≥ 1` and `a₁ < ⋯ < a_φ(n)` be the integers `1 ≤ m < n` coprime to `n`. Is
`∑_{1 ≤ k < φ(n)} (aₖ₊₁ - aₖ)² ≪ n² / φ(n)`?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Finset.Sort
public import Mathlib.Data.Nat.Totient

@[expose] public section

namespace MathlibExt.NumberTheory.ReducedResidueGapSquaresErdosProblem220Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #220, https://www.erdosproblems.com/220 (status PROVED
(LEAN)). UnsolvedMath record UM-30006773 (`EP-220`), dataset ulamai/UnsolvedMath v1.8.0.

The residues are listed in increasing order and the gaps are those of consecutive entries; the
implied constant is absolute. Compared with the formal-conjectures statement
`ErdosProblems/220.lean` (equivalent, there with `C > 0`; no code imported).
-/

/-- The integers `1 ≤ m < n` coprime to `n`, in increasing order: `a₁ < ⋯ < a_φ(n)`. -/
def sortedTotatives (n : ℕ) : List ℕ :=
  ((Finset.Ico 1 n).filter (fun m => Nat.Coprime m n)).sort (· ≤ ·)

/-- The sum of the squared gaps `∑ₖ (aₖ₊₁ - aₖ)²` of a list `a₁, a₂, …`. -/
def sumSquaredGaps (l : List ℕ) : ℕ :=
  (List.zipWith (fun a b => (b - a) ^ 2) l l.tail).sum

/-- Erdős Problem 220: with `a₁ < ⋯ < a_φ(n)` the integers in `[1, n)` coprime to `n`,
`∑_{1 ≤ k < φ(n)} (aₖ₊₁ - aₖ)² ≪ n² / φ(n)` for all `n ≥ 1`. -/
def reducedResidueSquaredGapsBound : Prop :=
  ∃ C : ℝ, ∀ n : ℕ, 1 ≤ n →
    (sumSquaredGaps (sortedTotatives n) : ℝ) ≤ C * (n : ℝ) ^ 2 / (Nat.totient n : ℝ)

/--
Resolved true: Montgomery and Vaughan proved `∑ (aₖ₊₁ - aₖ)^γ ≪_γ n^γ / φ(n)^{γ - 1}` for every `γ ≥
1`; `γ = 2` is the bound asked for. erdosproblems.com/220 lists the problem as proved. Source: T. F.
Bloom, Erdős Problems, Problem #220, https://www.erdosproblems.com/220 (status PROVED (LEAN));
resolution: H. L. Montgomery and R. C. Vaughan, On the distribution of reduced residues, Ann. of
Math. (2) 123 (1986), 311-333, erdosproblems.com/220: proved by Montgomery and Vaughan, ∑ (a_{k+1} -
a_k)^γ ≪_γ n^γ / φ(n)^{γ-1} for every γ ≥ 1, https://doi.org/10.2307/1971274.
-/
public theorem_wanted reducedResidueSquaredGapsBound_holds : reducedResidueSquaredGapsBound

end MathlibExt.NumberTheory.ReducedResidueGapSquaresErdosProblem220Wanted

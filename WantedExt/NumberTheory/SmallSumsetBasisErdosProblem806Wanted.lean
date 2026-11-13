/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Small bases for sets of size `√n` (Erdős Problem 806)

Erdős Problem 806 (Erdős and Newman): let `A ⊆ {1, …, n}` with `|A| ≤ n^{1/2}`. Must there exist `B
⊂ ℤ` with `|B| = o(n^{1/2})` such that `A ⊆ B + B`?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.Real.Sqrt

@[expose] public section

namespace MathlibExt.NumberTheory.SmallSumsetBasisErdosProblem806Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #806, https://www.erdosproblems.com/806 (status
PROVED). UnsolvedMath record UM-30007043 (`EP-806`), dataset ulamai/UnsolvedMath v1.8.0.

`o(n^{1/2})` is uniform in `A`: for every `ε > 0` and all large `n`, every such `A` has a `B` with
`|B| ≤ ε √n`. `A` is a finite set of integers in `[1, n]`; `B + B` is the pointwise sumset. Compared
with the formal-conjectures statement `ErdosProblems/806.lean` (equivalent; no code imported).
-/

open Pointwise in
/-- Erdős Problem 806 (Erdős and Newman): for every `ε > 0` and all large `n`, every
`A ⊆ {1, …, n}` with `|A| ≤ √n` lies in `B + B` for some `B ⊆ ℤ` with `|B| ≤ ε √n`. -/
def smallBasisCoversSqrtSets : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in Filter.atTop, ∀ A : Finset ℤ, A ⊆ Finset.Icc 1 (n : ℤ) →
    (A.card : ℝ) ≤ Real.sqrt n → ∃ B : Finset ℤ, A ⊆ B + B ∧ (B.card : ℝ) ≤ ε * Real.sqrt n

/--
Resolved true: Alon, Bukh and Sudakov proved that every `A ⊆ {1, …, n}` with `|A| ≤ n^{1/2}` lies in
`B + B` for some `B` with `|B| ≪ (log log n / log n) n^{1/2}`; erdosproblems.com/806 lists the
problem as proved. Source: T. F. Bloom, Erdős Problems, Problem #806,
https://www.erdosproblems.com/806 (status PROVED); resolution: N. Alon, B. Bukh and B. Sudakov,
Discrete Kakeya-type problems and small bases, Israel J. Math. 174 (2009), 285-301, Corollary
1.5(a): every finite solvable group, in particular ℤ/nℤ, satisfies the EN-condition (every A of size
at most √n has a basis B, A ⊂ B + B, with |B| ≤ 50 √n log log n/log n); Section 1 transfers this to
A ⊆ {1, …, n} through ℤ/nℤ (B = B' ∪ (B' - n) ⊂ ℤ), answering the Erdős-Newman question in the
affirmative, https://web.math.princeton.edu/~nalon/PDFS/dkakeya2.pdf.
-/
public theorem_wanted smallBasisCoversSqrtSets_holds : smallBasisCoversSqrtSets

end MathlibExt.NumberTheory.SmallSumsetBasisErdosProblem806Wanted

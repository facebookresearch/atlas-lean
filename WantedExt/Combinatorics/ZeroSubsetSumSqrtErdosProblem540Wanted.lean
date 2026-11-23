/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Zero subset sums in `ℤ / N ℤ` (Erdős Problem 540)

Erdős Problem 540 (Erdős and Heilbronn): if `A ⊆ ℤ / N ℤ` has size `≫ N ^ (1/2)`, is there a
nonempty `S ⊆ A` with `∑_{n ∈ S} n ≡ 0 (mod N)`?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.Real.Sqrt

@[expose] public section

namespace MathlibExt.Combinatorics.ZeroSubsetSumSqrtErdosProblem540Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #540, https://www.erdosproblems.com/540 (status PROVED
(LEAN)). UnsolvedMath record UM-30006923 (`EP-540`), dataset ulamai/UnsolvedMath v1.8.0.

`≫ N ^ (1/2)` is `|A| ≥ C √N` for one absolute `C`. Compared with the formal-conjectures statement
`ErdosProblems/540.lean` (equivalent; no code imported).
-/

/-- **The Erdős–Heilbronn zero subset sum statement (Erdős Problem 540).** This is the statement
that there is a real number $C > 0$ such that for every integer $N \ge 1$, every set
$A \subseteq \mathbb{Z}/N\mathbb{Z}$ with $|A| \ge C\sqrt{N}$ has a nonempty subset $S \subseteq A$
whose elements sum to $0$ in $\mathbb{Z}/N\mathbb{Z}$. -/
def sqrtSizeHasZeroSubsetSum : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 0 < N → ∀ A : Finset (ZMod N), C * Real.sqrt N ≤ A.card →
    ∃ S ⊆ A, S.Nonempty ∧ ∑ x ∈ S, x = 0

/--
**Zero subset sums of large sets in $\mathbb{Z}/N\mathbb{Z}$ (Erdős Problem 540).** There is a real
number $C > 0$ such that for every integer $N \ge 1$, every set $A \subseteq \mathbb{Z}/N\mathbb{Z}$
with $|A| \ge C\sqrt{N}$ has a nonempty subset $S \subseteq A$ whose elements sum to $0$ in
$\mathbb{Z}/N\mathbb{Z}$.

Resolved true: Olson proved it for prime $N$ and Szemerédi for all $N$ (in every finite abelian
group); Hamidoune and Zémor showed $(1 + o(1))\sqrt{2N}$ suffices.

Source: T. F. Bloom, Erdős Problems,
Problem #540, https://www.erdosproblems.com/540 (status PROVED (LEAN)); resolution: E. Szemerédi, On
a conjecture of Erdős and Heilbronn, Acta Arith. (1970), 227-229, erdosproblems.com/540: yes; Olson
for N prime, Szemerédi for all N (indeed for all finite abelian groups),
https://www.erdosproblems.com/540.
-/
public theorem_wanted sqrtSizeHasZeroSubsetSum_holds : sqrtSizeHasZeroSubsetSum

end MathlibExt.Combinatorics.ZeroSubsetSumSqrtErdosProblem540Wanted

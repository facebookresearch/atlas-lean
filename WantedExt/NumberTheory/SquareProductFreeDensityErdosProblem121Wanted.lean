/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Large sets with no square product of k distinct elements (Erdős Problem 121)

Erdős Problem 121: let `F_k(N)` be the size of the largest `A ⊆ {1, …, N}` such that the product of
no `k` distinct elements of `A` is a square. Is `F_5(N) = (1 - o(1)) N`? More generally, is
`F_{2k+1}(N) = (1 - o(1)) N`?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent

@[expose] public section

namespace MathlibExt.NumberTheory.SquareProductFreeDensityErdosProblem121Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #121, https://www.erdosproblems.com/121 (status
DISPROVED (LEAN)). UnsolvedMath record UM-30006731 (`EP-121`), dataset ulamai/UnsolvedMath v1.8.0.

`(1 - o(1)) N` is asymptotic equivalence with `N`. The general question is read for every odd size
`2k + 1 ≥ 5`, as a universal statement over `k ≥ 2` (`F_3(N) = (1 - o(1)) N` is a theorem of Erdős,
Sárközy and Sós); its refutation already follows from the first question at `k = 2`. A third target
records Tao's quantitative answer for every odd size `2k + 1 ≥ 5`, which is stronger than both
refutations. Compared with the formal-conjectures statement `ErdosProblems/121.lean` (the first
target is `erdos_121`, the second is `erdos_121.variants.odd` with `k ≥ 2`, the third is
`erdos_121.variants.tao` at the odd sizes; no code imported).
-/

open Filter Asymptotics

/-- `F_k(N)`: the largest size of `A ⊆ {1, …, N}` such that no product of `k` distinct elements of
`A` is a square. -/
noncomputable def maxSquareProductFree (k N : ℕ) : ℕ :=
  sSup {m : ℕ | ∃ A : Finset ℕ, A ⊆ Finset.Icc 1 N ∧
    (∀ S ⊆ A, S.card = k → ¬ IsSquare (∏ n ∈ S, n)) ∧ A.card = m}

/-- Erdős Problem 121, first question: `F_5(N) = (1 - o(1)) N`. -/
def fiveProductFreeAlmostFull : Prop :=
  (fun N : ℕ => (maxSquareProductFree 5 N : ℝ)) ~[atTop] fun N : ℕ => (N : ℝ)

/-- Erdős Problem 121, general question: `F_{2k+1}(N) = (1 - o(1)) N` for every odd size
`2k + 1 ≥ 5` (`F_3(N) = (1 - o(1)) N` is a theorem of Erdős, Sárközy and Sós). -/
def oddProductFreeAlmostFull : Prop :=
  ∀ k : ℕ, 2 ≤ k →
    (fun N : ℕ => (maxSquareProductFree (2 * k + 1) N : ℝ)) ~[atTop] fun N : ℕ => (N : ℝ)

/-- Tao's answer for every odd size `2k + 1 ≥ 5`: some `c > 0` has `F_{2k+1}(N) ≤ (1 - c) N` for
all large `N`. This is stronger than the negations of both questions above. -/
def oddProductFreeBoundedAwayFromFull : Prop :=
  ∀ k : ℕ, 2 ≤ k → ∃ c : ℝ, 0 < c ∧
    ∀ᶠ N : ℕ in atTop, (maxSquareProductFree (2 * k + 1) N : ℝ) ≤ (1 - c) * N

/--
Resolved false: Tao proved (Theorem 1.2) that for every `k ≥ 4` there is `c_k > 0` with `F_k(N) ≤ (1
- c_k + o(1)) N`, in particular for `k = 5`; erdosproblems.com/121 lists the problem as disproved.
Source: T. F. Bloom, Erdős Problems, Problem #121, https://www.erdosproblems.com/121 (status
DISPROVED (LEAN)); resolution: T. Tao, On product representations of squares, arXiv:2405.11610
(2024), Theorem 1.2: for every k ≥ 4 there is c_k > 0 with F_k(N) ≤ (1 - c_k + o(1)) N
(erdosproblems.com/121); formal proof plby/lean-proofs src/latest/ErdosProblems/Erdos121.lean,
https://arxiv.org/abs/2405.11610.
-/
public theorem_wanted fiveProductFreeAlmostFull_refuted : ¬ fiveProductFreeAlmostFull

/--
Resolved false: already the size `5` (`k = 2`) fails, by Tao's Theorem 1.2 as in the first question;
erdosproblems.com/121 lists the problem as disproved. Source: T. F. Bloom, Erdős Problems, Problem
#121, https://www.erdosproblems.com/121 (status DISPROVED (LEAN)); resolution: T. Tao, On product
representations of squares, arXiv:2405.11610 (2024), Theorem 1.2: for every k ≥ 4 there is c_k > 0
with F_k(N) ≤ (1 - c_k + o(1)) N (erdosproblems.com/121); formal proof plby/lean-proofs
src/latest/ErdosProblems/Erdos121.lean, https://arxiv.org/abs/2405.11610.
-/
public theorem_wanted oddProductFreeAlmostFull_refuted : ¬ oddProductFreeAlmostFull

/--
Resolved true (Tao's answer, stronger than the source's questions): Theorem 1.2 gives `c_k > 0` with
`F_k(N) ≤ (1 - c_k + o(1)) N` for every `k ≥ 4`; at the odd size `2k + 1 ≥ 5` take `c = c_{2k+1} /
2`. Each odd size fails, whereas refuting either question needs only one. Source: T. F. Bloom, Erdős
Problems, Problem #121, https://www.erdosproblems.com/121 (status DISPROVED (LEAN)); resolution: T.
Tao, On product representations of squares, arXiv:2405.11610 (2024), Theorem 1.2: for every k ≥ 4
there is c_k > 0 with F_k(N) ≤ (1 - c_k + o(1)) N (erdosproblems.com/121); formal proof
plby/lean-proofs src/latest/ErdosProblems/Erdos121.lean, https://arxiv.org/abs/2405.11610.
-/
public theorem_wanted oddProductFreeBoundedAwayFromFull_holds : oddProductFreeBoundedAwayFromFull

end MathlibExt.NumberTheory.SquareProductFreeDensityErdosProblem121Wanted

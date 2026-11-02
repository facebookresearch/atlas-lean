/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Union-free families of sets (Erdős Problem 447)

Erdős Problem 447: how large can a family `F` of subsets of `[n]` be with no `A ∪ B = C` for
distinct `A, B, C ∈ F`? Must `|F| = o(2^n)`? Perhaps even `|F| < (1 + o(1)) C(n, ⌊n/2⌋)`?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.Asymptotics.Defs

@[expose] public section

namespace MathlibExt.Combinatorics.UnionFreeFamiliesErdosProblem447Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #447, https://www.erdosproblems.com/447 (status PROVED
(LEAN)). UnsolvedMath record UM-30006877 (`EP-447`), dataset ulamai/UnsolvedMath v1.8.0.

`[n]` is `Fin n` and the maximum is an `sSup` over a bounded set. The two yes/no questions are
separate targets, and the opening "how large" is not stated beyond them; `(1 + o(1)) C(n, ⌊n/2⌋)` is
stated as: for every `ε > 0`, eventually `|F| ≤ (1 + ε) C(n, ⌊n/2⌋)`. Compared with the
formal-conjectures statement `ErdosProblems/447.lean` (equivalent; no code imported).
-/

open Asymptotics

/-- **Union-free family.** A family $F$ of subsets of $\{0, \dots, n-1\}$ is union-free if there
are no pairwise distinct $A, B, C \in F$ with $A \cup B = C$. -/
def IsUnionFree {n : ℕ} (F : Finset (Finset (Fin n))) : Prop :=
  ∀ A ∈ F, ∀ B ∈ F, ∀ C ∈ F, A ≠ B → A ≠ C → B ≠ C → A ∪ B ≠ C

/-- **Maximum size of a union-free family.** For a natural number $n$, the largest size $|F|$ of a
union-free family $F$ of subsets of $\{0, \dots, n-1\}$. -/
noncomputable def maxUnionFreeSize (n : ℕ) : ℕ :=
  sSup {k : ℕ | ∃ F : Finset (Finset (Fin n)), IsUnionFree F ∧ F.card = k}

/-- **Erdős Problem 447, first question.** The assertion that the maximum size of a union-free
family of subsets of $\{0, \dots, n-1\}$ is $o(2^n)$ as $n \to \infty$. -/
def maxUnionFreeSizeLittleO : Prop :=
  (fun n : ℕ => (maxUnionFreeSize n : ℝ)) =o[Filter.atTop] fun n : ℕ => (2 : ℝ) ^ n

/-- **Erdős Problem 447, second question.** The assertion that, for every real $\varepsilon > 0$
and all sufficiently large $n$, the maximum size of a union-free family of subsets of
$\{0, \dots, n-1\}$ is at most $(1 + \varepsilon)\binom{n}{\lfloor n/2 \rfloor}$; that is, it is
at most $(1 + o(1))\binom{n}{\lfloor n/2 \rfloor}$. -/
def maxUnionFreeSizeCentralBinomial : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in Filter.atTop,
    (maxUnionFreeSize n : ℝ) ≤ (1 + ε) * n.choose (n / 2)

/--
**Union-free families have vanishing density (Erdős Problem 447).** The maximum size of a
union-free family of subsets of $\{0, \dots, n-1\}$ is $o(2^n)$ as $n \to \infty$.

This follows from Kleitman's bound $(1 + o(1))\binom{n}{\lfloor n/2 \rfloor}$; Erdős reported an
earlier unpublished proof by Sárközy and Szemerédi.

Source: T. F.
Bloom, Erdős Problems, Problem #447, https://www.erdosproblems.com/447 (status PROVED (LEAN));
resolution: D. Kleitman, Collections of subsets containing no two sets and their union, Proceedings
of the LA Meeting AMS (1971), 153-155, |F| < (1 + o(1)) C(n, ⌊n/2⌋) (erdosproblems.com/447).
-/
public theorem_wanted maxUnionFreeSizeLittleO_holds : maxUnionFreeSizeLittleO

/--
**Kleitman's bound for union-free families (Erdős Problem 447).** For every real
$\varepsilon > 0$ and all sufficiently large $n$, the maximum size of a union-free family of
subsets of $\{0, \dots, n-1\}$ is at most $(1 + \varepsilon)\binom{n}{\lfloor n/2 \rfloor}$; that
is, it is at most $(1 + o(1))\binom{n}{\lfloor n/2 \rfloor}$.

Source: T. F. Bloom, Erdős Problems, Problem #447,
https://www.erdosproblems.com/447 (status PROVED (LEAN)); resolution: D. Kleitman, Collections of
subsets containing no two sets and their union, Proceedings of the LA Meeting AMS (1971), 153-155,
|F| < (1 + o(1)) C(n, ⌊n/2⌋) (erdosproblems.com/447).
-/
public theorem_wanted maxUnionFreeSizeCentralBinomial_holds : maxUnionFreeSizeCentralBinomial

end MathlibExt.Combinatorics.UnionFreeFamiliesErdosProblem447Wanted

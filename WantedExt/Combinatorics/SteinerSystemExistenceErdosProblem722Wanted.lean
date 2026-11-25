/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Existence of Steiner systems (Erdős Problem 722)

Erdős Problem 722: let `k > r` and `n` be sufficiently large in terms of `k` and `r`. Does there
always exist a block `r-(n, k, 1)` design (Steiner system with parameters `(n, k, r)`), provided the
trivial necessary divisibility conditions `C(k - i, r - i) ∣ C(n - i, r - i)` are satisfied for
every `0 ≤ i < r`?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Order.Filter.AtTopBot.Defs

@[expose] public section

namespace MathlibExt.Combinatorics.SteinerSystemExistenceErdosProblem722Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #722, https://www.erdosproblems.com/722 (status
PROVED). UnsolvedMath record UM-30006994 (`EP-722`), dataset ulamai/UnsolvedMath v1.8.0.

A Steiner system is a family of `k`-subsets of `Fin n` such that every `r`-subset lies in exactly
one member. For `r = 0` the conditions are vacuous and one block suffices, so including `r = 0` is
harmless. Compared with the formal-conjectures statement `ErdosProblems/722.lean` (equivalent; no
code imported).
-/

/-- **Existence conjecture for Steiner systems.** The statement that for all natural numbers
$r < k$ there is an $N$ such that for every $n \ge N$ with
$\binom{k-i}{r-i} \mid \binom{n-i}{r-i}$ for all $0 \le i < r$, there is a Steiner system
$S(r, k, n)$: a family $F$ of $k$-element subsets of $\{0, \dots, n-1\}$ such that every
$r$-element subset of $\{0, \dots, n-1\}$ is contained in exactly one member of $F$
(Erdős Problem 722). -/
def steinerSystemsExistForLargeN : Prop :=
  ∀ r k : ℕ, r < k → ∀ᶠ n : ℕ in Filter.atTop,
    (∀ i < r, (k - i).choose (r - i) ∣ (n - i).choose (r - i)) →
      ∃ F : Finset (Finset (Fin n)), (∀ A ∈ F, A.card = k) ∧
        ∀ S : Finset (Fin n), S.card = r → ∃! A, A ∈ F ∧ S ⊆ A

/--
**Keevash's existence theorem for Steiner systems.** For all natural numbers $r < k$ there is
an $N$ such that for every $n \ge N$ with $\binom{k-i}{r-i} \mid \binom{n-i}{r-i}$ for all
$0 \le i < r$, there is a Steiner system $S(r, k, n)$: a family $F$ of $k$-element subsets of
$\{0, \dots, n-1\}$ such that every $r$-element subset of $\{0, \dots, n-1\}$ is contained in
exactly one member of $F$.

Keevash proved the existence conjecture for designs, which gives this statement (earlier cases:
Kirkman for $(r, k) = (2, 3)$, Hanani, Wilson for $r = 2$); erdosproblems.com/722 lists the
problem as proved.

Source: T. F. Bloom, Erdős Problems, Problem #722,
https://www.erdosproblems.com/722 (status PROVED); resolution: P. Keevash, The existence of designs,
arXiv:1401.3665 (2014), abstract: proves the existence conjecture for combinatorial designs
(Steiner's question of 1853): the divisibility conditions suffice for all large n;
erdosproblems.com/722: proved by Keevash for all (r, k), https://arxiv.org/abs/1401.3665.
-/
public theorem_wanted steinerSystemsExistForLargeN_holds : steinerSystemsExistForLargeN

end MathlibExt.Combinatorics.SteinerSystemExistenceErdosProblem722Wanted

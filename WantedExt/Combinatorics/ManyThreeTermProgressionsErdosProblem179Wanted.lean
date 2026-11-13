/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Sets with many three-term progressions (Erdős Problem 179)

Erdős Problem 179: let `F_k(N, ℓ)` be the least number such that every `N`-element set of integers
with at least `F_k(N, ℓ)` `k`-term arithmetic progressions contains an `ℓ`-term progression. Is
`F₃(N, 4) = o(N²)`? Is `lim_{N → ∞} log F₃(N, ℓ) / log N = 2` for every `ℓ > 3`?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

@[expose] public section

namespace MathlibExt.Combinatorics.ManyThreeTermProgressionsErdosProblem179Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #179, https://www.erdosproblems.com/179 (status
PROVED). UnsolvedMath record UM-30006752 (`EP-179`), dataset ulamai/UnsolvedMath v1.8.0.

Sets are finite subsets of `ℕ` (the count is translation invariant). A `k`-term progression is a
pair `(a, d)` with `d ≥ 1` and `a + i d ∈ A` for `i < k`; for `k ≥ 2` such `a, d` are at most `max
A` and `(a, d) ↦ (a, a + d)` is injective, so the count is at most `N²`, `F_k(N, ℓ)` is the infimum
of a nonempty set, and `F₃(N, ℓ) ≥ 1` (sets of powers of `2` have no `3`-term progression). The
open-ended "find good upper bounds" is not formalized.
-/

open Filter Topology Asymptotics

/-- **Containing a $k$-term arithmetic progression.** A finite set $A \subseteq \mathbb{N}$
contains a $k$-term arithmetic progression when there are natural numbers $a$ and $d \ge 1$ with
$a + i d \in A$ for every natural number $i < k$, that is, $a, a + d, \dots, a + (k - 1) d$ all
lie in $A$. For $k = 0$ this holds vacuously. -/
def HasAP (A : Finset ℕ) (k : ℕ) : Prop :=
  ∃ a d : ℕ, 0 < d ∧ ∀ i < k, a + i * d ∈ A

/-- **Number of $k$-term arithmetic progressions in a set.** For a finite set
$A \subseteq \mathbb{N}$ and a natural number $k$, $\mathrm{AP}_k(A)$ is the number of pairs
$(a, d)$ of natural numbers with $a \in A$ and $1 \le d \le \max A$ such that $a + i d \in A$ for
every natural number $i < k$. For $k \ge 2$ the conditions $a \in A$ and $d \le \max A$ follow
from the others, so $\mathrm{AP}_k(A)$ counts the $k$-term progressions
$a, a + d, \dots, a + (k - 1) d$ in $A$ with $d \ge 1$. -/
def apCount (A : Finset ℕ) (k : ℕ) : ℕ :=
  ((A ×ˢ Finset.Icc 1 (A.sup id)).filter (fun p => ∀ i < k, p.1 + i * p.2 ∈ A)).card

/-- **The progression threshold $F_k(N, \ell)$.** For natural numbers $k$, $\ell$ and $N$,
$F_k(N, \ell)$ is the least natural number $m$ such that every $N$-element set
$A \subseteq \mathbb{N}$ with $\mathrm{AP}_k(A) \ge m$ contains an $\ell$-term arithmetic
progression, where $\mathrm{AP}_k(A)$ is the number of pairs $(a, d)$ with $a \in A$,
$1 \le d \le \max A$ and $a + i d \in A$ for all $i < k$ (for $k \ge 2$, the number of $k$-term
progressions in $A$ with $d \ge 1$); if no such $m$ exists, $F_k(N, \ell) = 0$.

For $k \ge 2$ such an $m$ always exists, since an $N$-element set has at most $N^2$ $k$-term
progressions. -/
noncomputable def apThreshold (k ℓ N : ℕ) : ℕ :=
  sInf {m : ℕ | ∀ A : Finset ℕ, A.card = N → m ≤ apCount A k → HasAP A ℓ}

/-- **Erdős Problem 179: is $F_3(N, 4) = o(N^2)$?** The statement that $F_3(N, 4) = o(N^2)$ as
$N \to \infty$ over the natural numbers, that is, $F_3(N, 4) / N^2 \to 0$, where $F_3(N, 4)$ is the
least $m$ such that every $N$-element set $A \subseteq \mathbb{N}$ containing at least $m$
three-term arithmetic progressions $a, a + d, a + 2d$ with $d \ge 1$ contains a $4$-term
arithmetic progression. -/
def threeAPThresholdForFourAPLittleO : Prop :=
  (fun N : ℕ => (apThreshold 3 4 N : ℝ)) =o[atTop] (fun N : ℕ => (N : ℝ) ^ 2)

/-- **Erdős Problem 179: does $\log F_3(N, \ell) / \log N$ tend to $2$?** The statement that for
every natural number $\ell > 3$, $\log F_3(N, \ell) / \log N \to 2$ as $N \to \infty$ over the
natural numbers, where $F_3(N, \ell)$ is the least $m$ such that every $N$-element set
$A \subseteq \mathbb{N}$ containing at least $m$ three-term arithmetic progressions
$a, a + d, a + 2d$ with $d \ge 1$ contains an $\ell$-term arithmetic progression. -/
def threeAPThresholdExponentTwo : Prop :=
  ∀ ℓ : ℕ, 3 < ℓ →
    Tendsto (fun N : ℕ => Real.log (apThreshold 3 ℓ N) / Real.log N) atTop (𝓝 2)

/--
**Erdős Problem 179: $F_3(N, 4) = o(N^2)$.** As $N \to \infty$ over the natural numbers,
$F_3(N, 4) / N^2 \to 0$, that is, $F_3(N, 4) = o(N^2)$, where $F_3(N, 4)$ is the least natural
number $m$ such that every $N$-element set $A \subseteq \mathbb{N}$ containing at least $m$
three-term arithmetic progressions $a, a + d, a + 2d$ with $d \ge 1$ contains a $4$-term
arithmetic progression.

Write $F_k(N, \ell)$ for the same threshold with $k$-term progressions in place of three-term ones
and $\ell$-term progressions in place of $4$-term ones. Fox and Pohoata bound $F_k(N, \ell)$ above
by $(r_\ell(N) / N)^{O(1)} N^2$, where $r_\ell(N)$ is the largest size of a subset of
$\{1, \dots, N\}$ without $\ell$-term progressions; since $r_\ell(N) = o(N)$ by Szemerédi's
theorem, this bound is $o(N^2)$. erdosproblems.com/179 records
$F_k(N, \ell) \le N^2 / (\log \log N)^{C_\ell}$ for a constant $C_\ell$ depending only on $\ell$.

Source: T.
F. Bloom, Erdős Problems, Problem #179, https://www.erdosproblems.com/179 (status PROVED);
resolution: J. Fox and C. Pohoata, Sets without k-term progressions can have many shorter
progressions, Random Structures Algorithms 58 (2021), 383-389, arXiv:1908.09905, main theorem: for
all k > s ≥ 3, log f_{s,k}(n) / log n → 2, where f_{s,k}(n) = F_s(n, k) - 1 is the largest number of
s-term progressions in an n-set with no k-term progression; erdosproblems.com/179: F_k(N, ℓ) ≤ N² /
(log log N)^{C_ℓ}, https://arxiv.org/abs/1908.09905.
-/
public theorem_wanted threeAPThresholdForFourAPLittleO_holds : threeAPThresholdForFourAPLittleO

/--
**Erdős Problem 179: $\log F_3(N, \ell) / \log N$ tends to $2$.** For every natural number
$\ell > 3$, $\log F_3(N, \ell) / \log N \to 2$ as $N \to \infty$ over the natural numbers, where
$F_3(N, \ell)$ is the least natural number $m$ such that every $N$-element set
$A \subseteq \mathbb{N}$ containing at least $m$ three-term arithmetic progressions
$a, a + d, a + 2d$ with $d \ge 1$ contains an $\ell$-term arithmetic progression.

Fox and Pohoata prove that $\log f_{s,k}(n) / \log n \to 2$ for all $k > s \ge 3$, where
$f_{s,k}(n)$ is the largest number of $s$-term progressions in an $n$-element set with no
$k$-term progression; since $F_3(N, \ell) = f_{3,\ell}(N) + 1$, taking $s = 3$ and $k = \ell$
gives the statement.

Source: T. F. Bloom,
Erdős Problems, Problem #179, https://www.erdosproblems.com/179 (status PROVED); resolution: J. Fox
and C. Pohoata, Sets without k-term progressions can have many shorter progressions, Random
Structures Algorithms 58 (2021), 383-389, arXiv:1908.09905, main theorem: for all k > s ≥ 3, log
f_{s,k}(n) / log n → 2, where f_{s,k}(n) = F_s(n, k) - 1 is the largest number of s-term
progressions in an n-set with no k-term progression; erdosproblems.com/179: F_k(N, ℓ) ≤ N² / (log
log N)^{C_ℓ}, https://arxiv.org/abs/1908.09905.
-/
public theorem_wanted threeAPThresholdExponentTwo_holds : threeAPThresholdExponentTwo

end MathlibExt.Combinatorics.ManyThreeTermProgressionsErdosProblem179Wanted

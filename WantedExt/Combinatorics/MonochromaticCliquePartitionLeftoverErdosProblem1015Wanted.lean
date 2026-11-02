/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Vertices left over by monochromatic clique packings (Erdős Problem 1015)

Erdős Problem 1015: let `f(t)` be minimal such that, in any two-colouring of the edges of `K_n`,
the edges can be partitioned into vertex disjoint monochromatic copies of `K_t` (not necessarily
the same colour) with at most `f(t)` vertices remaining. Estimate `f(t)`. In particular, is it
true that `f(t)^{1/t} → 1`? Is it true that `f(t) ≪ t`?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Combinatorics.SimpleGraph.Clique
public import MathlibExt.Combinatorics.SimpleGraph.Ramsey

@[expose] public section

namespace MathlibExt.Combinatorics.MonochromaticCliquePartitionLeftoverErdosProblem1015Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #1015, https://www.erdosproblems.com/1015 (status
SOLVED). UnsolvedMath record UM-30007126 (`EP-1015`), dataset ulamai/UnsolvedMath v1.8.0.

A two-colouring of the edges of `K_n` is a graph `G` on `Fin n` (red edges those of `G`, blue
edges those of `Gᶜ`), and a monochromatic `K_k` is a `k`-clique of `G` or of `Gᶜ`. As the page
notes, the question is meant for `n` sufficiently large depending on `t` (called `k` here), so the
least leftover depends on `n`; Burr, Erdős and Spencer call it `f(n, k)`. The page records their
answer as `R(t, t - 1) + x(t, n)` with `n + 1 ≡ R(t, t - 1) + x (mod t)`; Theorem 6 of the paper
reads `r(k, k - 1) - 1 + rem(n - r(k, k - 1) + 1, k)`, so the page drops the `- 1` (the page's
value is never congruent to `n` modulo `t`, while a leftover always is; for `t = 3` and `n ≡ 1
(mod 3)` it gives `5` against Moon's `f(3) = 4`). This module states Theorem 6 as printed in the
paper, with `r(k, k - 1)` the MathlibExt Ramsey number `SimpleGraph.graphRamsey k (k - 1)`, for
every `k ≥ 2` (for `k = 2` the value is `n mod 2`). The two follow-up questions are not stated:
their negative answers follow from Theorem 6 and the exponential growth of `r(t, t - 1)`, a step
the page does not record. formal-conjectures has no statement of this problem.
-/

open SimpleGraph

/-- **Monochromatic clique packings.** Let $n$ and $k$ be natural numbers, and view a simple
graph $G$ on the vertex set $\{0, 1, \dots, n - 1\}$ as a two-colouring of the edges of the
complete graph $K_n$: the edges of $G$ are red and the edges of its complement $G^c$ are blue.
A finite family $P$ of sets of vertices is a monochromatic $k$-clique packing for $G$ when the
sets in $P$ are pairwise disjoint and each of them is a $k$-clique of $G$ or a $k$-clique of
$G^c$, that is, a set of exactly $k$ vertices spanning a monochromatic copy of $K_k$. -/
def IsMonochromaticCliquePacking {n : ℕ} (G : SimpleGraph (Fin n)) (k : ℕ)
    (P : Finset (Finset (Fin n))) : Prop :=
  (P : Set (Finset (Fin n))).PairwiseDisjoint id ∧ ∀ S ∈ P, G.IsNClique k S ∨ Gᶜ.IsNClique k S

/-- **Burr–Erdős–Spencer leftover value.** For natural numbers $k$ and $n$, let $r = R(k, k - 1)$
be the classical two-colour Ramsey number. The leftover value is
$r - 1 + \big((n + 1 - r) \bmod k\big)$, where subtraction is truncated at $0$ (in particular
$n + 1 - r$ is read as $0$ when $n + 1 \le r$) and $a \bmod 0 = a$.

For $k \ge 2$ and large $n$, Burr, Erdős and Spencer showed that this is the least number of
vertices that vertex-disjoint monochromatic copies of $K_k$ can be guaranteed to leave uncovered
in every two-colouring of the edges of $K_n$. -/
noncomputable def leftoverValue (k n : ℕ) : ℕ :=
  graphRamsey k (k - 1) - 1 + (n + 1 - graphRamsey k (k - 1)) % k

/-- **Erdős Problem 1015 in the Burr–Erdős–Spencer form.** This is the statement that for every
natural number $k \ge 2$ there is $n_0$ such that for every $n \ge n_0$ the following holds. Let
$r = R(k, k - 1)$ be the classical two-colour Ramsey number and let
$L = r - 1 + \big((n + 1 - r) \bmod k\big)$, where $n + 1 - r$ is read as $0$ if it is negative.
View a simple graph $G$ on $n$ vertices as a two-colouring of the edges of $K_n$, with the edges
of $G$ red and those of its complement $G^c$ blue. Then every such colouring admits a
monochromatic $k$-clique packing, that is, a finite family of pairwise disjoint sets of vertices,
each a $k$-clique of $G$ or of $G^c$, leaving at most $L$ vertices uncovered; and some colouring
admits no such packing leaving fewer than $L$ vertices uncovered. In other words, for these $n$
the least number $f(n, k)$ such that every two-colouring of $K_n$ admits such a packing leaving at
most $f(n, k)$ vertices uncovered equals $L$. -/
def monochromaticCliquePartitionLeftover : Prop :=
  ∀ k : ℕ, 2 ≤ k → ∃ n₀ : ℕ, ∀ n ≥ n₀,
    (∀ G : SimpleGraph (Fin n), ∃ P, IsMonochromaticCliquePacking G k P ∧
        n - k * P.card ≤ leftoverValue k n) ∧
    ∃ G : SimpleGraph (Fin n), ∀ P, IsMonochromaticCliquePacking G k P →
        leftoverValue k n ≤ n - k * P.card

/-- **Burr–Erdős–Spencer theorem on monochromatic clique packings.** For every natural number
$k \ge 2$ there is $n_0$ such that for every $n \ge n_0$ the following holds. Let
$r = R(k, k - 1)$ be the classical two-colour Ramsey number and let
$L = r - 1 + \big((n + 1 - r) \bmod k\big)$, where $n + 1 - r$ is read as $0$ if it is negative.
View a simple graph $G$ on $n$ vertices as a two-colouring of the edges of $K_n$, with the edges
of $G$ red and those of its complement $G^c$ blue. Then every such colouring admits a finite
family of pairwise disjoint sets of vertices, each a $k$-clique of $G$ or of $G^c$, that leaves at
most $L$ vertices uncovered; and some colouring admits no such family leaving fewer than $L$
vertices uncovered.

Source: T. F. Bloom,
Erdős Problems, Problem #1015, https://www.erdosproblems.com/1015 (status SOLVED); resolution: S.
A. Burr, P. Erdős and J. H. Spencer, Ramsey theorems for multiple copies of graphs, Trans. Amer.
Math. Soc. 209 (1975), 87-99, §5, Theorem 6: if k is given, then for sufficiently large n, f(n, k)
= r(k, k - 1) - 1 + rem(n - r(k, k - 1) + 1, k), where f(n, k) is the minimal integer such that
any two-coloring of K_n admits vertex-disjoint monochromatic K_k with at most f(n, k) points left
over; erdosproblems.com/1015 lists the problem as solved citing this paper,
https://users.renyi.hu/~p_erdos/1975-35.pdf.
-/
public theorem_wanted monochromaticCliquePartitionLeftover_holds :
    monochromaticCliquePartitionLeftover

end MathlibExt.Combinatorics.MonochromaticCliquePartitionLeftoverErdosProblem1015Wanted

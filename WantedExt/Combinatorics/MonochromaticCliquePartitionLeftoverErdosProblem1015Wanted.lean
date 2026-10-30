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

/-- A two-colouring of the edges of `K_n` is a graph `G` on `Fin n` (red edges: those of `G`,
blue edges: those of `Gᶜ`). `IsMonochromaticCliquePacking G k P` says that `P` is a family of
pairwise disjoint `k`-sets of vertices, each spanning a monochromatic `K_k`, that is, a
`k`-clique of `G` or of `Gᶜ`. -/
def IsMonochromaticCliquePacking {n : ℕ} (G : SimpleGraph (Fin n)) (k : ℕ)
    (P : Finset (Finset (Fin n))) : Prop :=
  (P : Set (Finset (Fin n))).PairwiseDisjoint id ∧ ∀ S ∈ P, G.IsNClique k S ∨ Gᶜ.IsNClique k S

/-- The Burr-Erdős-Spencer value `r(k, k - 1) - 1 + rem(n - r(k, k - 1) + 1, k)` of the least
possible number of uncovered vertices, where `r(k, k - 1)` is the classical two-colour Ramsey
number `graphRamsey k (k - 1)`. -/
noncomputable def leftoverValue (k n : ℕ) : ℕ :=
  graphRamsey k (k - 1) - 1 + (n + 1 - graphRamsey k (k - 1)) % k

/-- Erdős Problem 1015, answered by Burr, Erdős and Spencer (Theorem 6): for every `k ≥ 2` and all
sufficiently large `n`, the least number `f(n, k)` such that every two-colouring of the edges of
`K_n` admits vertex-disjoint monochromatic copies of `K_k` leaving at most `f(n, k)` vertices
uncovered equals `leftoverValue k n`. Both halves are stated: every colouring admits a packing
leaving at most that many vertices, and some colouring admits no packing leaving fewer. -/
def monochromaticCliquePartitionLeftover : Prop :=
  ∀ k : ℕ, 2 ≤ k → ∃ n₀ : ℕ, ∀ n ≥ n₀,
    (∀ G : SimpleGraph (Fin n), ∃ P, IsMonochromaticCliquePacking G k P ∧
        n - k * P.card ≤ leftoverValue k n) ∧
    ∃ G : SimpleGraph (Fin n), ∀ P, IsMonochromaticCliquePacking G k P →
        leftoverValue k n ≤ n - k * P.card

/--
Resolved: Burr, Erdős and Spencer (Theorem 6) determined the least leftover for large `n`: every
two-colouring of `K_n` has vertex-disjoint monochromatic `K_k` missing at most `r(k, k - 1) - 1 +
rem(n - r(k, k - 1) + 1, k)` vertices, and this is attained by one colouring. Source: T. F. Bloom,
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

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# A density-zero set of unavoidable cycle lengths (Erdős Problem 72)

Erdős Problem 72: is there a set `A ⊂ ℕ` of density `0` and a constant `c > 0` such that every graph
on sufficiently many vertices with average degree `≥ c` contains a cycle whose length is in `A`?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Combinatorics.SimpleGraph.Paths
public import MathlibExt.Data.Set.Density

@[expose] public section

namespace MathlibExt.GraphTheory.ZeroDensityCycleLengthsErdosProblem72Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #72, https://www.erdosproblems.com/72 (status PROVED).
UnsolvedMath record UM-30006711 (`EP-72`), dataset ulamai/UnsolvedMath v1.8.0.

Density is natural density (`Set.HasDensity`, MathlibExt). Average degree `≥ c` on `n` vertices is
`c n ≤ 2 |E(G)|`; cycles are `Walk.IsCycle`, whose lengths are at least `3`. Compared with the
formal-conjectures statement `ErdosProblems/72.lean` (equivalent; no code imported).
-/

/-- Erdős Problem 72: there are a set `A ⊆ ℕ` of natural density `0` and a constant `c > 0` such
that every graph on sufficiently many vertices with average degree at least `c` (i.e.
`2 |E(G)| ≥ c |V(G)|`) contains a cycle whose length lies in `A`. -/
def zeroDensityUnavoidableCycleLengths : Prop :=
  ∃ A : Set ℕ, A.HasDensity 0 ∧ ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in Filter.atTop,
    ∀ G : SimpleGraph (Fin n), c * n ≤ 2 * (G.edgeSet.ncard : ℝ) →
      ∃ (v : Fin n) (p : G.Walk v v), p.IsCycle ∧ p.length ∈ A

/--
Resolved true: Verstraëte proved non-constructively that such a set `A` of density `0` exists; Liu
and Montgomery later showed that the powers of `2` work (every graph of large enough average degree
has a cycle whose length is a power of `2`). erdosproblems.com/72 lists the problem as proved.
Source: T. F. Bloom, Erdős Problems, Problem #72, https://www.erdosproblems.com/72 (status PROVED);
resolution: J. Verstraëte, Unavoidable cycle lengths in graphs, J. Graph Theory 49 (2005), 151-167;
H. Liu and R. Montgomery, A solution to Erdős and Hajnal's odd cycle problem, arXiv:2010.15802
(2020), erdosproblems.com/72: solved by Verstraëte (a non-constructive proof that such a set A
exists); Liu and Montgomery (abstract of arXiv:2010.15802) proved that an average degree condition
forces a cycle whose length is a power of 2, https://www.erdosproblems.com/72.
-/
public theorem_wanted zeroDensityUnavoidableCycleLengths_holds : zeroDensityUnavoidableCycleLengths

end MathlibExt.GraphTheory.ZeroDensityCycleLengthsErdosProblem72Wanted

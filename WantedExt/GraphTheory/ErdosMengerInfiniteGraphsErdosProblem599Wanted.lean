/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# The Erdős-Menger conjecture (Erdős Problem 599)

Erdős Problem 599: let `G` be a (possibly infinite) graph and `A, B` disjoint independent sets of
vertices. Must there exist a family `P` of disjoint paths between `A` and `B` and a set `S` which
contains exactly one vertex from each path in `P`, and such that every path between `A` and `B`
contains at least one vertex from `S`?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Order.CompletePartialOrder

@[expose] public section

namespace MathlibExt.GraphTheory.ErdosMengerInfiniteGraphsErdosProblem599Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #599, https://www.erdosproblems.com/599 (status
PROVED). UnsolvedMath record UM-30006946 (`EP-599`), dataset ulamai/UnsolvedMath v1.8.0.

The family is indexed by a type `ι`; path `i` is a `Walk.IsPath` from `a i ∈ A` to `b i ∈ B`,
distinct paths have disjoint vertex sets, `S` lies on the paths and meets each in exactly one
vertex, and every path from a vertex of `A` to a vertex of `B` meets `S`. Paths may pass through
further vertices of `A ∪ B`; every such path contains an `A`-`B` path meeting `A ∪ B` only at its
ends, so Aharoni and Berger's theorem, stated for those paths and for arbitrary `A, B`, implies this
form. MathlibExt's `menger_AB_infinite` covers only finite connectivity. Compared with the
formal-conjectures statement `ErdosProblems/599.lean` (equivalent; no code imported).
-/

/-- Erdős Problem 599 (the Erdős-Menger conjecture): for every graph `G` (possibly infinite) and
disjoint independent vertex sets `A, B` there are a family `p` of pairwise vertex-disjoint paths
from `A` to `B` and a set `S` consisting of exactly one vertex from each path of the family such
that every path from `A` to `B` meets `S`. -/
def erdosMengerConjecture : Prop :=
  ∀ (V : Type) (G : SimpleGraph V) (A B : Set V), Disjoint A B → G.IsIndepSet A →
    G.IsIndepSet B →
    ∃ (ι : Type) (a b : ι → V) (p : ∀ i, G.Walk (a i) (b i)) (S : Set V),
      (∀ i, a i ∈ A ∧ b i ∈ B ∧ (p i).IsPath) ∧
      (∀ i j, i ≠ j → Disjoint {v | v ∈ (p i).support} {v | v ∈ (p j).support}) ∧
      S ⊆ {v | ∃ i, v ∈ (p i).support} ∧ (∀ i, ∃! v, v ∈ S ∧ v ∈ (p i).support) ∧
      ∀ a' ∈ A, ∀ b' ∈ B, ∀ q : G.Walk a' b', q.IsPath → ∃ v ∈ q.support, v ∈ S

/--
Resolved true: Aharoni and Berger proved Menger's theorem for infinite graphs in the form
conjectured by Erdős: for any vertex sets `A, B` of any graph there are a family of disjoint `A`-`B`
paths and an `A`-`B` separator consisting of one vertex from each path; erdosproblems.com/599 lists
the problem as proved. Source: T. F. Bloom, Erdős Problems, Problem #599,
https://www.erdosproblems.com/599 (status PROVED); resolution: R. Aharoni and E. Berger, Menger's
theorem for infinite graphs, Invent. Math. (2009), 1-62, erdosproblems.com/599: proved by Aharoni
and Berger, https://www.erdosproblems.com/599.
-/
public theorem_wanted erdosMengerConjecture_holds : erdosMengerConjecture

end MathlibExt.GraphTheory.ErdosMengerInfiniteGraphsErdosProblem599Wanted

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Number of cliques in graphs with no K_t minor (Open Problem Garden 37081)

Open Problem Garden, Number of Cliques in Minor-Closed Classes (D. R. Wood): is there a constant `c`
such that every `n`-vertex `K_t`-minor-free graph has at most `c ^ t * n` cliques?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Basic.Real.Basic
public import Mathlib.Combinatorics.SimpleGraph.Clique
public import MathlibExt.Combinatorics.Graph.GraphMinor

@[expose] public section

namespace MathlibExt.GraphTheory.CliquesMinorFreeOpenGardenProblem37081Wanted

/-!
Source: Open Problem Garden, Number of Cliques in Minor-Closed Classes (node 37081; D. R. Wood),
http://www.openproblemgarden.org/op/number_of_cliques_in_minor_closed_classes. UnsolvedMath record
UM-00003107 (`OPG-37081`), dataset ulamai/UnsolvedMath v1.8.0.

A clique is a (not necessarily maximal) set of pairwise adjacent vertices, as the source says; the
empty set is not counted (Lee and Oum count it, which only weakens the bound by `1`). Graphs are
finite simple graphs; minors are MathlibExt's `MetaMathlibExt.IsMinor` (deletions and contractions
up to isomorphism) and `K_t` is `MetaMathlibExt.cliqueFinGraph t`, for positive integers `t` as in
Lee and Oum's Theorem 1.1. The constant `c` is a real number, uniform in `t` and `n`.
-/

open MetaMathlibExt

/-- The number of nonempty cliques (sets of pairwise adjacent vertices, not necessarily maximal) of
a graph on a finite vertex type. -/
noncomputable def numCliques {V : Type} (G : SimpleGraph V) : ℕ :=
  Nat.card {s : Finset V // s.Nonempty ∧ G.IsClique (s : Set V)}

/-- Wood's question, with a positive answer: there is a constant `c` such that, for every positive
integer `t`, every graph on `n` vertices with no `K_t` minor has at most `c ^ t * n` cliques. -/
def cliquesMinorFree : Prop :=
  ∃ c : ℝ, ∀ (t : ℕ), 0 < t → ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
    ¬ IsMinor (cliqueFinGraph t) ⟨V, G⟩ → (numCliques G : ℝ) ≤ c ^ t * Fintype.card V

/--
Resolved true: Lee and Oum proved that every `n`-vertex graph with no `K_t`-subdivision, in
particular every graph with no `K_t` minor, has at most `2 ^ (50 t) * n` cliques, answering Wood's
question; Fox and Wei later found the optimal base, `3 ^ (2t/3 + o(t)) * n` for `K_t`-minor-free
graphs. Source: Open Problem Garden, Number of Cliques in Minor-Closed Classes (node 37081; D. R.
Wood), http://www.openproblemgarden.org/op/number_of_cliques_in_minor_closed_classes; resolution: C.
Lee and S. Oum, Number of cliques in graphs with a forbidden subdivision, SIAM J. Discrete Math. 29
(2015), 1999-2005, doi:10.1137/140979988; arXiv:1407.7707, Theorem 1.1: for all positive integers t,
every n-vertex graph with no K_t-subdivision has at most 2^{50t} n cliques; abstract: 'This strongly
answers a question of D. Wood asking if the number of cliques in n-vertex graphs with no K_t-minor
is at most 2^{ct} n'; the source page's 2014 update records the affirmative answer; J. Fox and F.
Wei, J. Combin. Theory Ser. B 126 (2017), 175-197, prove the bound 3^{2t/3+o(t)} n for
K_t-minor-free graphs, https://doi.org/10.1137/140979988.
-/
public theorem_wanted cliquesMinorFree_holds : cliquesMinorFree

end MathlibExt.GraphTheory.CliquesMinorFreeOpenGardenProblem37081Wanted

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Matching cuts in sparse high-girth graphs
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Combinatorics.SimpleGraph.Girth
public import Mathlib.Combinatorics.SimpleGraph.Matching
public import Mathlib.Data.Rat.Init
public import Mathlib.Basic.Real.Basic
public import Batteries.Util.ProofWanted

@[expose] public section

namespace MathlibExt.Combinatorics.MatchingCutGirthWanted

/-! Source record `OPG-37364`, ported from the Open Problem Garden entry
"Matching cut and girth"
(http://www.openproblemgarden.org/op/matching_cut_and_girth).

For every real `d` there is `g` such that every graph of average degree below `d`
and girth at least `g` has a matching-cut.

Average degree uses the canonical `edgeFinset` count; the girth bound uses
`egirth` (which is `⊤` for acyclic graphs); a matching-cut is a matching
subgraph (`Subgraph.IsMatching`) whose edge deletion (`deleteEdges`)
disconnects the graph.

Adequacy gaps: the source poses a question, formalized here as the
affirmative answer; the matching-cut may be empty (then the graph is already
disconnected); graphs are finite with at least two vertices (matching cuts
need two sides; the singleton refutes the unguarded form). -/

/-- **Average degree of a finite graph.** For a simple graph $G$ on a finite vertex set $V$ with
edge set $E$, the average degree of $G$ is the rational number $2|E|/|V|$; it equals $0$ when $V$
is empty. -/
noncomputable def avgDegree {V : Type*} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] : ℚ :=
  (2 * G.edgeFinset.card : ℚ) / Fintype.card V

/-- **Matching cut.** A simple graph $G$ has a matching cut if some matching $M$ of $G$, that is,
a set of pairwise disjoint edges of $G$, is such that deleting the edges of $M$ from $G$ leaves
two vertices $u$ and $v$ that are not joined by any path. The matching may be empty, in which
case this says that $G$ itself has two vertices not joined by any path. -/
def HasMatchingCut {V : Type*} (G : SimpleGraph V) : Prop :=
  ∃ H : G.Subgraph, H.IsMatching ∧
    ∃ u v : V, ¬ (G.deleteEdges H.edgeSet).Reachable u v

/-- **Matching cut and girth question, affirmative form.** For every real number $d$ there is a
natural number $g$ such that every simple graph $G$ on a finite vertex set with at least two
vertices, whose average degree is less than $d$ and whose girth is at least $g$, has a matching
cut. An acyclic graph has infinite girth, so it meets the girth bound for every $g$.

Source: [OPG-37364], Open Problem Garden, "Matching cut and girth". -/
def conjecture : Prop :=
  ∀ d : ℝ, ∃ g : ℕ, ∀ (V : Type*) [Fintype V] [Nontrivial V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj],
    (avgDegree G : ℝ) < d →
    ((g : ℕ∞) ≤ G.egirth) →
    HasMatchingCut G

/-- **Negative answer to the matching cut and girth question.** It is not the case that for
every real number $d$ there is a natural number $g$ such that every simple graph on a finite
vertex set with at least two vertices, average degree less than $d$ and girth at least $g$ has a
matching cut. That is, there is a real number $d$ such that for every natural number $g$ some
simple graph on a finite vertex set with at least two vertices, average degree less than $d$ and
girth at least $g$ has no matching cut.

Feghali, Lucke, Paulusma and Ries (Lemma 5) construct, for every $g$, a connected 14-regular
bipartite graph of girth at least $g$ with no matching cut; these graphs give $d = 15$.

Source: C. Feghali, F. Lucke, D. Paulusma and B. Ries, Matching Cuts in Graphs of High
Girth and H-Free Graphs, ISAAC 2023, arXiv:2212.12317, https://arxiv.org/abs/2212.12317. Moved
from `OpenConjectures/Combinatorics/MatchingCutGirth`.
-/
public theorem_wanted conjecture_refuted : ¬ conjecture

end MathlibExt.Combinatorics.MatchingCutGirthWanted

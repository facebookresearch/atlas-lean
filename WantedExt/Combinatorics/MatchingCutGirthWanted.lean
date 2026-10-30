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

/-- Average degree via the canonical edge count. -/
noncomputable def avgDegree {V : Type*} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] : ℚ :=
  (2 * G.edgeFinset.card : ℚ) / Fintype.card V

/-- `G` has a matching-cut: a matching subgraph whose deletion disconnects. -/
def HasMatchingCut {V : Type*} (G : SimpleGraph V) : Prop :=
  ∃ H : G.Subgraph, H.IsMatching ∧
    ∃ u v : V, ¬ (G.deleteEdges H.edgeSet).Reachable u v

/-- [OPG-37364] For every real `d` there is `g` such that every finite graph with at least two
vertices, average degree below `d` and girth at least `g` has a matching-cut. -/
def conjecture : Prop :=
  ∀ d : ℝ, ∃ g : ℕ, ∀ (V : Type*) [Fintype V] [Nontrivial V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj],
    (avgDegree G : ℝ) < d →
    ((g : ℕ∞) ≤ G.egirth) →
    HasMatchingCut G

/--
Resolved false: The question has a negative answer: Feghali, Lucke, Paulusma and Ries
(arXiv:2212.12317, Lemma 5) construct, for every g, a connected 14-regular bipartite graph of
girth at least g with no matching cut, and note that this answers the Open Problem Garden
question in the negative. With d = 15 these graphs refute the affirmative statement registered
here. Source: C. Feghali, F. Lucke, D. Paulusma and B. Ries, Matching Cuts in Graphs of High
Girth and H-Free Graphs, ISAAC 2023, arXiv:2212.12317, https://arxiv.org/abs/2212.12317. Moved
from `OpenConjectures/Combinatorics/MatchingCutGirth`.
-/
public theorem_wanted conjecture_refuted : ¬ conjecture

end MathlibExt.Combinatorics.MatchingCutGirthWanted

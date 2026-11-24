/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Online linear-time suffix tree construction (Ukkonen)

Ukkonen's Algorithm 2 reads the string `T = t₁…tₙ` left to right and, after
reading `i` symbols, holds the suffix tree of the prefix `t₁…tᵢ`, using
suffix links and implicit (open) edges; the total time is `O(n)`. The `O(n)`
running-time reading needs a RAM cost model and is context here. A suffix
tree here is a compacted edge-labeled tree: every substring of `T` is spelled
by a root path, every root path spells a substring of `T`, and no edge label
is empty.

Overlap: none (`CSLibExt/Algorithms/Lean/DataStructures/SuffixTree.lean` is a
naive quadratic construction and explicitly lists Ukkonen's linear-time
construction as out of scope).

Sources: E. Ukkonen, "On-line construction of suffix trees", Algorithmica
14(3):249-260, 1995, doi:10.1007/BF01206331, Algorithm 2.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.List.Basic

@[expose] public section

namespace WantedExt.Biology.ComputationalBiology.SuffixTreeWanted

variable {α : Type*} [DecidableEq α]

/-- A compacted edge-labeled tree: nodes, root, and `(from, label, to)`
edges. -/
structure SuffixTree (α : Type*) where
  nodes : List ℕ
  root : ℕ
  edges : List (ℕ × List α × ℕ)

/-- A node sequence from `start` spells a label: adjacent edges from the
table concatenate to it. -/
def SpellsPath (T : SuffixTree α) (start : ℕ) (nodes : List ℕ)
    (label : List α) : Prop :=
  ∃ edges : List (ℕ × List α × ℕ),
    edges.length + 1 = nodes.length ∧
    (∀ e ∈ edges, e ∈ T.edges) ∧
    (∀ i : ℕ, ∀ u v : ℕ, i + 1 < nodes.length →
      nodes[i]? = some u → nodes[i + 1]? = some v →
      ∃ l, (u, l, v) ∈ edges) ∧
    label = (edges.map fun e => e.2.1).flatten ∧
    nodes.head? = some start

/-- State reached from the root by spelling a label. -/
def Reached (T : SuffixTree α) (label : List α) (v : ℕ) : Prop :=
  ∃ nodes, SpellsPath T T.root nodes label ∧ nodes.getLast? = some v

/-- Suffix-tree-of: substrings spelled from the root and back, compacted
(no empty edge labels). -/
def IsSuffixTreeOf (T : SuffixTree α) (S : List α) : Prop :=
  (∀ sub : List α, sub.Sublist S →
    ∃ nodes, SpellsPath T T.root nodes sub) ∧
  (∀ nodes : List ℕ, ∀ label : List α,
    SpellsPath T T.root nodes label → label.Sublist S) ∧
  ∀ e ∈ T.edges, e.2.1 ≠ []

/-- Suffix links: the link of a state reached by `a :: l` is reached by `l`. -/
def HasSuffixLinks (T : SuffixTree α) (link : ℕ → Option ℕ) : Prop :=
  ∀ v : ℕ, ∀ a : α, ∀ l : List α, Reached T (a :: l) v →
    ∃ u, link v = some u ∧ Reached T l u

/-- **Ukkonen's on-line construction** (Ukkonen 1995, Algorithm 2):
hypotheses are the string `T`, a step count `i` within bounds (`hi`), and a
build procedure `build` giving the state after each prefix with suffix links
(`hbuild`). Conclusion: after `i` symbols the state is the suffix tree of
the length-`i` prefix.

Source: Ukkonen (1995), Algorithm 2. -/
theorem_wanted ukkonen_online (T : List α) (i : ℕ) (hi : i ≤ T.length)
    (build : ℕ → SuffixTree α)
    (hbuild : ∀ j, j ≤ T.length → ∃ link, HasSuffixLinks (build j) link) :
    IsSuffixTreeOf (build i) (T.take i)

end WantedExt.Biology.ComputationalBiology.SuffixTreeWanted

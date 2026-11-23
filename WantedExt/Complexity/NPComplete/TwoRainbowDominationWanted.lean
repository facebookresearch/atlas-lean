/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# 2-RAINBOW DOMINATION is NP-complete

Source:
B. Brešar and T. Kraner Šumenjak, "On the 2-rainbow domination in graphs", Discrete Applied
Mathematics 155(17) (2007), 2394-2400, doi:10.1016/j.dam.2007.07.018.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Computability.Complexity.Karp.Color
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.TwoRainbowDomination

/-!
# 2-RAINBOW DOMINATION is NP-complete

INSTANCE: a finite simple undirected graph `G = (V, E)` and a non-negative integer `K`.
QUESTION: is there a 2-rainbow dominating function of weight at most `K`, that is, a function
`f : V → 𝒫({1, 2})` such that every vertex `v` with `f(v) = ∅` has neighbors whose labels
together cover `{1, 2}`, and `∑_{v ∈ V} |f(v)| ≤ K`?

Brešar and Kraner Šumenjak (2007) prove that deciding whether a graph has a 2-rainbow
dominating function of a given weight is NP-complete, even for bipartite or chordal graphs.

The two colors are `Fin 2`, vertices are `Fin n`, and the graph is
`Cslib.Complexity.Karp.edgeGraph n E`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: the number of vertices `n`, the edge list, and the bound `K`. -/
abbrev TwoRainbowDominationInstance := ℕ × List (ℕ × ℕ) × ℕ

/-- The graph of the instance as a `SimpleGraph (Fin n)`. -/
def Graph (i : TwoRainbowDominationInstance) : SimpleGraph (Fin i.1) :=
  Cslib.Complexity.Karp.edgeGraph i.1 i.2.1

/-- Well-formedness of an instance: the edge list is a simple undirected edge list on
`Fin n`. -/
def WellFormed (i : TwoRainbowDominationInstance) : Prop :=
  i.2.1.Nodup ∧ ∀ e ∈ i.2.1, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2.1

/-- A 2-rainbow dominating function of weight at most `K` exists: `f` assigns each vertex a
set of colors from `Fin 2`, every vertex with the empty set sees each color on some
neighbor, and the total number of assigned colors is at most `K`. -/
def TwoRainbowDominationFeasible (i : TwoRainbowDominationInstance) : Prop :=
  ∃ f : Fin i.1 → Finset (Fin 2),
    (∀ v, f v = ∅ → ∀ c : Fin 2, ∃ u, (Graph i).Adj v u ∧ c ∈ f u) ∧
    ∑ v, (f v).card ≤ i.2.2

open Classical in
/-- 2-RAINBOW DOMINATION as a decision problem over bitstrings. -/
noncomputable def twoRainbowDominationDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode (α := TwoRainbowDominationInstance) x with
  | some i => decide (WellFormed i ∧ TwoRainbowDominationFeasible i)
  | none => false

/-- **2-RAINBOW DOMINATION is NP-complete.** Source: Brešar and Kraner Šumenjak (2007). -/
public theorem_wanted twoRainbowDomination_npComplete :
    twoRainbowDominationDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L twoRainbowDominationDec

end MetaMathlibExt.Complexity.NPComplete.TwoRainbowDomination

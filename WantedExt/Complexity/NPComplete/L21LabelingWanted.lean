/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# L(2,1)-LABELING is NP-complete

Source:
J. R. Griggs and R. K. Yeh, "Labelling graphs with a condition at distance 2", SIAM Journal on
Discrete Mathematics 5 (1992), 586-595, doi:10.1137/0405048;
J. Fiala, T. Kloks and J. Kratochvíl, "Fixed-parameter complexity of λ-labelings", Discrete
Applied Mathematics 113 (2001), 59-72, doi:10.1016/S0166-218X(00)00387-5.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import CSLibExt.Computability.Complexity.Karp.Color
public import Mathlib.Algebra.Order.Group.Int
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Combinatorics.SimpleGraph.Metric
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.L21Labeling

/-!
# L(2,1)-LABELING is NP-complete

INSTANCE: a finite simple undirected graph `G = (V, E)` with `V` nonempty, and a positive
integer `K`.
QUESTION: is there an `L(2,1)`-labelling of `G` with span at most `K`, that is, a map
`f : V → {0, 1, …, K}` such that `|f(x) - f(y)| ≥ 2` whenever `x` and `y` are adjacent and
`|f(x) - f(y)| ≥ 1` whenever the distance between `x` and `y` is two? Equivalently, is
`λ(G) ≤ K`, where `λ(G)` is the least possible maximum label?

Griggs and Yeh introduce `L(2,1)`-labellings (labels are nonnegative reals; they show it
suffices to consider nonnegative integers) and show that determining `λ(G)` is NP-complete by
relating it to Hamiltonian paths: already the question `λ(G) ≤ |V|` is NP-complete (on graphs
of diameter 2). This module states the problem with `K` part of the instance, which contains
that case (`K = |V|`); membership in NP is immediate (a labelling is a certificate). Fiala,
Kloks and Kratochvíl record the result ("determining `λ(G)` is an NP-complete problem even for
graphs `G` with diameter 2") and prove NP-completeness for every fixed `K ≥ 4`.

Labels are natural numbers `f v ≤ K`; differences are taken in `ℤ`. "Distance two" is Mathlib's
graph distance `SimpleGraph.dist` (the length of a shortest walk; `0` for unreachable pairs), so
`dist x y = 2` holds exactly for distinct non-adjacent vertices with a common neighbour.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: vertex count `n` (vertices `Fin n`), edge list, span bound `K`. -/
abbrev L21LabelingInstance := ℕ × List (ℕ × ℕ) × ℕ

/-- The graph of the instance as a `SimpleGraph (Fin n)`. -/
def Graph (i : L21LabelingInstance) : SimpleGraph (Fin i.1) :=
  Cslib.Complexity.Karp.edgeGraph i.1 i.2.1

/-- Well-formedness of an instance: the graph has at least one vertex (so that the maximum
label `λ(G)` is defined), the edge list describes a simple graph on `Fin n` (no duplicate edges
in either orientation, no self-loops, endpoints in range), and `0 < K`. -/
def WellFormed (i : L21LabelingInstance) : Prop :=
  0 < i.1 ∧
    (i.2.1.Nodup ∧ ∀ e ∈ i.2.1, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2.1) ∧
    0 < i.2.2

/-- Some labelling `f : V → {0, …, K}` has labels at least `2` apart on adjacent vertices and
at least `1` apart on vertices at distance two. -/
def L21LabelingFeasible (i : L21LabelingInstance) : Prop :=
  ∃ f : Fin i.1 → ℕ, (∀ v, f v ≤ i.2.2) ∧
    (∀ x y, (Graph i).Adj x y → 2 ≤ |(f x : ℤ) - f y|) ∧
    ∀ x y, (Graph i).dist x y = 2 → 1 ≤ |(f x : ℤ) - f y|

open Classical in
/-- L(2,1)-LABELING as a decision problem over bitstrings. -/
noncomputable def l21LabelingDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode (α := L21LabelingInstance) x with
  | some i => decide (WellFormed i ∧ L21LabelingFeasible i)
  | none => false

/-- **L(2,1)-LABELING is NP-complete.** Source: Griggs and Yeh (1992); Fiala, Kloks and
Kratochvíl (2001). -/
public theorem_wanted l21Labeling_npComplete :
    l21LabelingDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L l21LabelingDec

end MetaMathlibExt.Complexity.NPComplete.L21Labeling

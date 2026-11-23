/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# BANDWIDTH for caterpillars with hairs of length at most 3 is NP-complete

Source:
B. Monien, "The bandwidth minimization problem for caterpillars with hair length 3 is
NP-complete", SIAM Journal on Algebraic and Discrete Methods 7 (1986), 505-512,
doi:10.1137/0607057;
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT40] BANDWIDTH (the parent
problem).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Computability.Complexity.Karp.Color
public import WantedExt.Complexity.NPComplete.BandwidthWanted
public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import Mathlib.Combinatorics.SimpleGraph.Metric

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.BandwidthCaterpillarsHairLengthThree

/-!
# BANDWIDTH for caterpillars with hairs of length at most 3 is NP-complete

INSTANCE: a caterpillar `G = (V, E)` with hairs of length at most `3`, and a positive integer
`K ≤ |V|`. QUESTION: is there a linear ordering of `V` with bandwidth `K` or less, i.e., a
one-to-one function `f : V → {1, 2, …, |V|}` such that, for all `{u, v} ∈ E`,
`|f(u) - f(v)| ≤ K`?

Monien: "Caterpillars are special trees; they consist of a simple chain (the body) with
various simple chains attached to the vertices of the body (the attached chains are called
hairs)"; the length of a hair is the number of its edges counted from the body vertex, so an
ordinary caterpillar has hairs of length `1`. `IsCaterpillarWithHairLength h G` says that `G`
is a tree with a path `body` (distinct vertices, consecutive ones adjacent) such that every
vertex off the body has degree at most `2` and lies within distance `h` of the body. This is
the same class: in a tree each component of `G - body` is joined to the body by exactly one
edge, so the degree condition makes it a chain attached at an end, and the distance condition
bounds its length by `h`; conversely every hair vertex has degree at most `2` and is within
distance `h` of its body vertex. Several hairs may hang from one body vertex.

This is the restriction of BANDWIDTH ([GT40], `BandwidthWanted`) to these caterpillars, with
`h = 3`. The instance type and the question are the parent's (`Bandwidth.BandwidthInstance`,
`Bandwidth.BandwidthFeasible`); `WellFormed` is the parent's plus the restriction and GJ's
`0 < K ≤ |V|`, as in `BandwidthTreesMaxDegreeThreeWanted`. Trees are Mathlib's
`SimpleGraph.IsTree`, distances `SimpleGraph.dist`, degrees `SimpleGraph.degree`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- The graph of the instance as a `SimpleGraph (Fin n)`. -/
def Graph (i : Bandwidth.BandwidthInstance) : SimpleGraph (Fin i.1) :=
  Cslib.Complexity.Karp.edgeGraph i.1 i.2.1

open Classical in
/-- `G` is a caterpillar with hairs of length at most `h`: a tree with a path `body` (a list of
distinct vertices, consecutive ones adjacent) such that every vertex off the body has degree at
most `2` and is within distance `h` of some body vertex. -/
def IsCaterpillarWithHairLength (h : ℕ) {n : ℕ} (G : SimpleGraph (Fin n)) : Prop :=
  G.IsTree ∧ ∃ body : List (Fin n), body.Nodup ∧ body.IsChain G.Adj ∧
    ∀ v, v ∉ body → G.degree v ≤ 2 ∧ ∃ b ∈ body, G.dist v b ≤ h

/-- Well-formedness of an instance: the parent's (a simple edge list on `Fin n`), the graph is a
caterpillar with hairs of length at most `3`, and `0 < K ≤ n`. -/
def WellFormed (i : Bandwidth.BandwidthInstance) : Prop :=
  Bandwidth.WellFormed i ∧ IsCaterpillarWithHairLength 3 (Graph i) ∧ 0 < i.2.2 ∧ i.2.2 ≤ i.1

open Classical in
/-- BANDWIDTH for caterpillars with hairs of length at most 3 as a decision problem over
bitstrings. -/
noncomputable def bandwidthCaterpillarsHairLengthThreeDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := Bandwidth.BandwidthInstance) x with
  | some i => decide (WellFormed i ∧ Bandwidth.BandwidthFeasible i)
  | none => false

/-- **BANDWIDTH for caterpillars with hairs of length at most 3 is NP-complete.** Source:
Monien (1986); Garey and Johnson (1979), [GT40] (parent problem). -/
public theorem_wanted bandwidthCaterpillarsHairLengthThree_npComplete :
    bandwidthCaterpillarsHairLengthThreeDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L bandwidthCaterpillarsHairLengthThreeDec

end MetaMathlibExt.Complexity.NPComplete.BandwidthCaterpillarsHairLengthThree

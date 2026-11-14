/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# HAMILTONIAN CIRCUIT on circle graphs is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT37] HAMILTONIAN CIRCUIT;
P. Damaschke, "The Hamiltonian circuit problem for circle graphs is NP-complete",
Information Processing Letters 32 (1989), 1-2, doi:10.1016/0020-0190(89)90059-8.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.HamiltonianCycleUndirectedWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.CircleGraphHamiltonianCircuit

open MetaMathlibExt.Complexity.NPComplete.HamiltonianCycleUndirected
  (HamiltonianCycleUndirectedInstance HamiltonianCycleUndirectedFeasible)

/-!
# HAMILTONIAN CIRCUIT on circle graphs is NP-complete

INSTANCE: a circle graph `G`, given by a chord model: a family of chords of a circle, one per
vertex, two vertices being adjacent when their chords intersect.
QUESTION: does `G` have a Hamiltonian circuit?

A chord is given by its two endpoints, natural numbers `a < b` naming points in clockwise order
on the circle; the endpoints of all chords are distinct. Two chords `(a, b)` and `(c, d)` with
distinct endpoints intersect exactly when their endpoints interleave, `a < c < b < d` or
`c < a < d < b`; nested or disjoint chords do not meet. Every circle graph has such a model.

Vertex `u` is the `u`-th chord, and the circle graph is passed to `HamiltonianCycleUndirected`
([GT37]) as the instance with one vertex per chord and the edge list `chordEdges`: the pairs
`u < v` whose chords intersect. That edge list has no repeated edge, no loop and no reversed
copy, so it is a well-formed `HamiltonianCycleUndirected` edge list, and the question is that
module's `HamiltonianCycleUndirectedFeasible` (a Hamiltonian circuit needs at least three
vertices).

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: the chords, one per vertex, each given by its endpoints `(a, b)`. -/
abbrev CircleGraphHamiltonianCircuitInstance := List (ℕ × ℕ)

/-- Two chords with distinct endpoints intersect: their endpoints interleave. -/
def Crosses (p q : ℕ × ℕ) : Prop :=
  (p.1 < q.1 ∧ q.1 < p.2 ∧ p.2 < q.2) ∨ (q.1 < p.1 ∧ p.1 < q.2 ∧ q.2 < p.2)

/-- Crossing is decidable: it is a statement about natural numbers. -/
instance : DecidableRel Crosses := fun p q => by
  unfold Crosses
  infer_instance

/-- Well-formedness of an instance: every chord has endpoints `a < b`, and all endpoints of all
chords are distinct. -/
def WellFormed (i : CircleGraphHamiltonianCircuitInstance) : Prop :=
  (∀ c ∈ i, c.1 < c.2) ∧ (i.flatMap fun c => [c.1, c.2]).Nodup

/-- The edges of the circle graph: the pairs `(u, v)` with `u < v < |V|` whose chords
intersect. -/
def chordEdges (i : CircleGraphHamiltonianCircuitInstance) : List (ℕ × ℕ) :=
  (List.range i.length).flatMap fun u =>
    ((List.range i.length).filter fun v =>
      decide (u < v ∧ Crosses (i.getD u (0, 0)) (i.getD v (0, 0)))).map fun v => (u, v)

/-- The circle graph as a HAMILTONIAN CIRCUIT instance: one vertex per chord and the chord
edges. -/
def toHamiltonianInstance (i : CircleGraphHamiltonianCircuitInstance) :
    HamiltonianCycleUndirectedInstance :=
  (i.length, chordEdges i)

open Classical in
/-- HAMILTONIAN CIRCUIT on circle graphs as a decision problem over bitstrings. -/
noncomputable def circleGraphHamiltonianCircuitDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := CircleGraphHamiltonianCircuitInstance) x with
  | some i => decide (WellFormed i ∧ HamiltonianCycleUndirectedFeasible (toHamiltonianInstance i))
  | none => false

/-- **HAMILTONIAN CIRCUIT on circle graphs is NP-complete.** Source: Garey and Johnson (1979),
[GT37]; Damaschke (1989). -/
public theorem_wanted circleGraphHamiltonianCircuit_npComplete :
    circleGraphHamiltonianCircuitDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L circleGraphHamiltonianCircuitDec

end MetaMathlibExt.Complexity.NPComplete.CircleGraphHamiltonianCircuit

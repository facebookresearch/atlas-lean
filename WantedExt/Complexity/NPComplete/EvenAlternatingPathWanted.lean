/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# EVEN ALTERNATING PATH (2-arc-colored digraphs) is NP-complete

Source:
D. S. Johnson, "The NP-completeness column: an ongoing guide", J. Algorithms 3 (1982), 381-395,
doi:10.1016/0196-6774(82)90032-3, comment to problem [3] EVEN LENGTH PATH (reference:
O. Vornberger, "Komplexität von Wegproblemen in Graphen", Doctoral Thesis, Gesamthochschule
Paderborn (1980)).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.EvenLengthPathWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.EvenAlternatingPath

/-!
# EVEN ALTERNATING PATH (2-arc-colored digraphs) is NP-complete

INSTANCE: a directed graph `G = (V, A)` whose arcs are colored red or blue, and specified
vertices `s, t ∈ V`.
QUESTION: is there a simple path from `s` to `t` in `G` which contains an even number of arcs
and whose arcs alternate in color along the path?

Johnson's column, comment to problem [3] EVEN LENGTH PATH: "Back in the directed case, suppose
the arcs of `G` are 2-colored. If we ask that the path not only contain an even number of arcs,
but also that the arcs alternate in color along the path, we again have an NP-complete
problem", citing Vornberger's 1980 thesis (not available); the comment adds that the variant
is solvable in polynomial time for undirected graphs, or if either color class is a matching.
Membership in NP: the path is a certificate.

The digraph, `s` and `t` form an instance of `EvenLengthPathWanted` (vertices `Fin n`, a list
of distinct arcs without loops, `s, t < n`), whose `EvenLengthPath.Graph` and
`EvenLengthPath.WellFormed` are reused; the coloring is the list of red arcs, a set of listed
arcs, and every other arc is blue. As in `EvenLengthPathWanted`, a path is a vertex list that is
a `List.IsChainFromTo` chain of arcs from `s` to `t`, simple when its vertices are distinct, with
`p.length - 1` arcs; its arcs are the consecutive pairs `p.zip p.tail`, and they alternate in
color when every two consecutive arcs have different colors. For `s = t` the one-vertex path has
zero arcs, so such an instance is a yes-instance.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: an EVEN LENGTH PATH instance (vertex count `n`, arc list, `s`, `t`) and the
list of red arcs; the other arcs are blue. -/
abbrev EvenAlternatingPathInstance :=
  EvenLengthPath.EvenLengthPathInstance × List (ℕ × ℕ)

/-- Well-formedness of an instance: a well-formed EVEN LENGTH PATH instance
(`EvenLengthPath.WellFormed`), and the red arcs are distinct listed arcs. -/
def WellFormed (i : EvenAlternatingPathInstance) : Prop :=
  EvenLengthPath.WellFormed i.1 ∧ i.2.Nodup ∧ ∀ a ∈ i.2, a ∈ i.1.2.1

/-- The arc `u → v` is red: `(u, v)` is in the red list. -/
def IsRed (i : EvenAlternatingPathInstance) (u v : Fin i.1.1) : Prop :=
  ((u : ℕ), (v : ℕ)) ∈ i.2

/-- Some simple directed path from `s` to `t` has an even number of arcs whose colors
alternate: a chain of arcs `p` from the vertex `s` to the vertex `t` with distinct vertices, an
even number `p.length - 1` of arcs, and consecutive arcs (consecutive entries of `p.zip p.tail`)
of different colors. -/
def EvenAlternatingPathFeasible (i : EvenAlternatingPathInstance) : Prop :=
  ∃ s t : Fin i.1.1, (s : ℕ) = i.1.2.2.1 ∧ (t : ℕ) = i.1.2.2.2 ∧
    ∃ p : List (Fin i.1.1), p.IsChainFromTo (EvenLengthPath.Graph i.1).Adj s t ∧ p.Nodup ∧
      Even (p.length - 1) ∧
      (p.zip p.tail).IsChain fun a b => (IsRed i a.1 a.2 ↔ ¬ IsRed i b.1 b.2)

open Classical in
/-- EVEN ALTERNATING PATH as a decision problem over bitstrings. -/
noncomputable def evenAlternatingPathDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := EvenAlternatingPathInstance) x with
  | some i => decide (WellFormed i ∧ EvenAlternatingPathFeasible i)
  | none => false

/-- **EVEN ALTERNATING PATH (2-arc-colored digraphs) is NP-complete.** Source: Johnson (1982),
comment to problem [3] (Vornberger 1980). -/
public theorem_wanted evenAlternatingPath_npComplete :
    evenAlternatingPathDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L evenAlternatingPathDec

end MetaMathlibExt.Complexity.NPComplete.EvenAlternatingPath

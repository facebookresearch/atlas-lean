/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# STACKER-CRANE with unit lengths is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [ND26] STACKER-CRANE, comment;
G. N. Frederickson, M. S. Hecht and C. E. Kim, "Approximation algorithms for some routing
problems", SIAM Journal on Computing 7 (1978), 178-193, doi:10.1137/0207017.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.StackerCraneWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.StackerCraneUnitLengths

/-!
# STACKER-CRANE with unit lengths is NP-complete

INSTANCE: a mixed graph `G = (V, A, E)` (`A` directed edges, `E` undirected edges) in which
every edge has length `1`, and a bound `B ∈ ℤ⁺`. QUESTION: is there a cycle in `G` that includes
each directed edge in `A` at least once, traversing such edges only in the specified direction,
and that has total length no more than `B`?

This is STACKER-CRANE (`WantedExt.Complexity.NPComplete.StackerCraneWanted`, Garey and Johnson
[ND26], reference [Frederickson, Hecht, and Kim, 1978], transformation from HAMILTONIAN
CIRCUIT) restricted as in the [ND26] comment: "Remains NP-complete even if all edge lengths
equal 1." The comment carries no separate citation. With unit lengths the transformation from
HAMILTONIAN CIRCUIT reads: each vertex `v` becomes a directed edge `v⁻ → v⁺`, each edge
`{u, v}` becomes the undirected edges `{u⁺, v⁻}` and `{v⁺, u⁻}`, and `B = 2|V|`; a cycle
through all `|V|` directed edges needs at least one undirected edge after each of them, so
length `2|V|` forces every directed edge once, each followed by a single undirected edge, which
is a Hamiltonian circuit.

The instance type, `StackerCrane.WellFormed` and `StackerCrane.StackerCraneFeasible` (a closed
walk given as a list of moves, lengths counted with repetition) are reused unchanged; the
restriction adds to well-formedness that every directed and undirected edge has length `1`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- Well-formedness of an instance: a well-formed STACKER-CRANE instance in which every
directed and every undirected edge has length `1`. -/
def WellFormed (i : StackerCrane.StackerCraneInstance) : Prop :=
  StackerCrane.WellFormed i ∧ (∀ e ∈ i.2.1, e.2.2 = 1) ∧ ∀ e ∈ i.2.2.1, e.2.2 = 1

open Classical in
/-- STACKER-CRANE with unit lengths as a decision problem over bitstrings. -/
noncomputable def stackerCraneUnitLengthsDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := StackerCrane.StackerCraneInstance) x with
  | some i => decide (WellFormed i ∧ StackerCrane.StackerCraneFeasible i)
  | none => false

/-- **STACKER-CRANE is NP-complete with unit lengths.** Source: Garey and Johnson (1979),
[ND26], comment; Frederickson, Hecht, and Kim (1978). -/
public theorem_wanted stackerCraneUnitLengths_npComplete :
    stackerCraneUnitLengthsDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L stackerCraneUnitLengthsDec

end MetaMathlibExt.Complexity.NPComplete.StackerCraneUnitLengths

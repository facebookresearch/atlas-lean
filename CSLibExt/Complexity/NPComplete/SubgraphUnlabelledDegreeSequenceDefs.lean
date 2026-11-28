/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# SUBGRAPH WITH GIVEN UNLABELLED DEGREE SEQUENCE: definitions

Source:
D. S. Johnson, "The NP-completeness column: an ongoing guide", Journal of Algorithms 6 (1985),
145-159, doi:10.1016/0196-6774(85)90025-2, comment on entry [4] DEGREE CONSTRAINED SUBGRAPH:
"If, however, we are given just the desired degrees, and are not constrained as to which
vertices get which degrees, the problem once more becomes NP-complete", attributed to Camerini
and Maffioli;
P. M. Camerini and F. Maffioli, "Unlabelled partition systems: optimization and complexity",
SIAM Journal on Algebraic and Discrete Methods 5 (1984), 426-441, doi:10.1137/0605041 (cited by
Johnson as Report LCE83-1, Politecnico di Milano, 1983; full text not available here).
-/
module

public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Computability.Complexity.Karp.Color
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Combinatorics.SimpleGraph.Finite

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.SubgraphUnlabelledDegreeSequence

/-- An instance: vertex count `n` (vertices `Fin n`), edge list, and the list of desired
degrees. -/
abbrev SubgraphUnlabelledDegreeSequenceInstance := ℕ × List (ℕ × ℕ) × List ℕ

/-- Well-formedness of an instance: the edge list describes a simple graph on `Fin n` (no
duplicate edges in either orientation, no self-loops, endpoints in range), and there are `n`
desired degrees. -/
def WellFormed (i : SubgraphUnlabelledDegreeSequenceInstance) : Prop :=
  (i.2.1.Nodup ∧ ∀ e ∈ i.2.1, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2.1) ∧
    i.2.2.length = i.1

open Classical in
/-- Some sublist `E'` of the edge list spans a subgraph `(V, E')` whose multiset of vertex
degrees equals the multiset of desired degrees. -/
def SubgraphUnlabelledDegreeSequenceFeasible (i : SubgraphUnlabelledDegreeSequenceInstance) :
    Prop :=
  ∃ es : List (ℕ × ℕ), es.Sublist i.2.1 ∧
    (Finset.univ : Finset (Fin i.1)).val.map
        (fun v => (Cslib.Complexity.Karp.edgeGraph i.1 es).degree v) = (i.2.2 : Multiset ℕ)

open Classical in
/-- SUBGRAPH WITH GIVEN UNLABELLED DEGREE SEQUENCE as a decision problem over bitstrings. -/
noncomputable def subgraphUnlabelledDegreeSequenceDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := SubgraphUnlabelledDegreeSequenceInstance) x with
  | some i => decide (WellFormed i ∧ SubgraphUnlabelledDegreeSequenceFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.SubgraphUnlabelledDegreeSequence

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# CLIQUE on dually chordal graphs: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT19] CLIQUE (the parent problem);
A. Brandstädt, V. D. Chepoi and F. F. Dragan, "The algorithmic use of hypertree structure and
maximum neighbourhood orderings", Discrete Applied Mathematics 82(1-3) (1998), 43-77,
doi:10.1016/s0166-218x(97)00125-x (cited by Wikipedia, "Dually chordal graph", for this
result);
A. Leitert, "3-Colourability of dually chordal graphs in linear time", arXiv:1206.0233 (2012),
Section 3 (adding a universal vertex makes any graph dually chordal, which reduces several
NP-complete problems to dually chordal graphs; the idea is credited to Brandstädt et al.);
ISGCI, *Information System on Graph Classes and their Inclusions*, class `gc_185` (dually
chordal), problem Clique: NP-complete (note `ref_1504`: the universal-vertex reduction,
communicated by V. Santos).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.CliqueClawFreeDefs
public import CSLibExt.Complexity.NPComplete.IndependentSetDuallyChordalDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.CliqueDuallyChordal

open CliqueClawFree (CliqueClawFreeInstance Graph CliqueClawFreeFeasible)
open IndependentSetDuallyChordal (DuallyChordal)

/-- Well-formedness of an instance: the edge list describes a simple graph on `Fin n` (no
duplicate edges in either orientation, no self-loops, endpoints in range) that is dually
chordal, and `0 < K ≤ |V|`. -/
def WellFormed (i : CliqueClawFreeInstance) : Prop :=
  (i.2.1.Nodup ∧ ∀ e ∈ i.2.1, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2.1) ∧
    DuallyChordal (Graph i) ∧ 0 < i.2.2 ∧ i.2.2 ≤ i.1

open Classical in
/-- CLIQUE on dually chordal graphs as a decision problem over bitstrings. -/
noncomputable def cliqueDuallyChordalDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := CliqueClawFreeInstance) x with
  | some i => decide (WellFormed i ∧ CliqueClawFreeFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.CliqueDuallyChordal

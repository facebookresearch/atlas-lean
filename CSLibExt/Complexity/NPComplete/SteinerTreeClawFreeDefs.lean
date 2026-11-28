/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# STEINER TREE IN GRAPHS (unit weights) for claw-free graphs: definitions

Source:
H. L. Bodlaender, N. Brettell, M. Johnson, G. Paesani, D. Paulusma and E. J. van Leeuwen,
"Steiner trees for hereditary graph classes: a treewidth perspective", Theoretical Computer
Science 867 (2021), 30-39, doi:10.1016/j.tcs.2021.03.012 (arXiv:2004.07492), Lemma 8 ("The
unweighted Vertex Steiner Tree problem is NP-complete for line graphs") and the proof of
Theorem 2 ("the class of claw-free graphs, which in turn contains the class of line graphs");
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [ND12] STEINER TREE IN GRAPHS (the
parent problem).
-/
module

public import MathlibExt.Combinatorics.SimpleGraph.ClawFreeIndependencePoly
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.SteinerTreeDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.SteinerTreeClawFree

open SteinerTree (SteinerTreeInstance SteinerTreeFeasible)

/-- Well-formedness of an instance: a well-formed STEINER TREE IN GRAPHS instance in which every
edge has weight `1`, whose graph is claw-free, and `0 < K`. -/
def WellFormed (i : SteinerTreeInstance) : Prop :=
  SteinerTree.WellFormed i ∧ (∀ e ∈ i.2.1, e.2.2 = 1) ∧
    (SteinerTree.Graph i i.2.1).IsClawFree ∧ 0 < i.2.2.2

open Classical in
/-- STEINER TREE IN GRAPHS (unit weights) for claw-free graphs as a decision problem
over bitstrings. -/
noncomputable def steinerTreeClawFreeDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := SteinerTreeInstance) x with
  | some i => decide (WellFormed i ∧ SteinerTreeFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.SteinerTreeClawFree

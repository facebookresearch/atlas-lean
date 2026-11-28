/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# STEINER PROBLEM IN PHYLOGENY (maximum parsimony for binary sequences): definitions

Source:
L. R. Foulds and R. L. Graham, "The Steiner problem in phylogeny is NP-complete", Advances in
Applied Mathematics 3(1) (1982), 43-49, doi:10.1016/S0196-8858(82)80004-3;
N. Misra, G. Blelloch, R. Ravi, and R. Schwartz, "Generalized Buneman pruning for inferring the
most parsimonious multi-state phylogeny", arXiv:0910.1830 (maximum parsimony is NP-hard
[Foulds and Graham] and, for discrete characters, equivalent to finding a minimum Steiner tree
displaying the input taxa).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import MathlibExt.Combinatorics.SimpleGraph.HypercubeExtremal
public import Mathlib.Combinatorics.SimpleGraph.Acyclic

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.SteinerProblemInPhylogeny

/-- An instance: the sequence length `m`, the species' sequences, and the bound `K`. -/
abbrev SteinerProblemInPhylogenyInstance := ℕ × List (List Bool) × ℕ

/-- A listed sequence as a vertex `Fin m → Bool` of the hypercube `Q_m`. -/
def toVertex (m : ℕ) (s : List Bool) : Fin m → Bool :=
  fun k => s.getD k false

/-- Well-formedness of an instance: there is at least one species, and every species is a
sequence of length `m`. -/
def WellFormed (i : SteinerProblemInPhylogenyInstance) : Prop :=
  i.2.1 ≠ [] ∧ ∀ s ∈ i.2.1, s.length = i.1

/-- Some subtree of the hypercube `Q_m` contains every species and has at most `K` edges. -/
def SteinerProblemInPhylogenyFeasible (i : SteinerProblemInPhylogenyInstance) : Prop :=
  ∃ T : (SimpleGraph.hypercubeGraph i.1).Subgraph, T.coe.IsTree ∧
    (∀ s ∈ i.2.1, toVertex i.1 s ∈ T.verts) ∧ T.edgeSet.ncard ≤ i.2.2

open Classical in
/-- STEINER PROBLEM IN PHYLOGENY as a decision problem over bitstrings. -/
noncomputable def steinerProblemInPhylogenyDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := SteinerProblemInPhylogenyInstance) x with
  | some i => decide (WellFormed i ∧ SteinerProblemInPhylogenyFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.SteinerProblemInPhylogeny

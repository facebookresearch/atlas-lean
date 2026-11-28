/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# PAIRED DOMINATION: definitions

Source:
T. W. Haynes and P. J. Slater, "Paired-domination in graphs", Networks 32(3) (1998), 199-206,
doi:10.1002/(SICI)1097-0037(199810)32:3<199::AID-NET4>3.0.CO;2-F.
-/
module

public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Computability.Complexity.Karp.Color
public import MathlibExt.Combinatorics.SimpleGraph.Domination
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Combinatorics.SimpleGraph.Matching

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.PairedDomination

/-- An instance: vertex count `n` (vertices `0, …, n - 1`), edge list, and the bound `K`. -/
abbrev PairedDominationInstance := ℕ × List (ℕ × ℕ) × ℕ

/-- The graph of the instance as a `SimpleGraph (Fin n)`. -/
def Graph (i : PairedDominationInstance) : SimpleGraph (Fin i.1) :=
  Cslib.Complexity.Karp.edgeGraph i.1 i.2.1

/-- Well-formedness of an instance: the edge list describes a simple graph (no duplicate edges in
either orientation, no self-loops, endpoints in range), no vertex is isolated, and `K` is positive
and even. -/
def WellFormed (i : PairedDominationInstance) : Prop :=
  (i.2.1.Nodup ∧ ∀ e ∈ i.2.1, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2.1) ∧
    (∀ v : Fin i.1, ∃ w, (Graph i).Adj v w) ∧ 0 < i.2.2 ∧ Even i.2.2

/-- Some dominating set `V'` with `|V'| ≤ K` is the vertex set of a matching of `G`, i.e. `G[V']`
has a perfect matching. -/
def PairedDominationFeasible (i : PairedDominationInstance) : Prop :=
  ∃ S : Finset (Fin i.1), S.card ≤ i.2.2 ∧ (Graph i).IsDominating ↑S ∧
    ∃ M : (Graph i).Subgraph, M.verts = ↑S ∧ M.IsMatching

open Classical in
/-- PAIRED DOMINATION as a decision problem over bitstrings. -/
noncomputable def pairedDominationDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := PairedDominationInstance) x with
  | some i => decide (WellFormed i ∧ PairedDominationFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.PairedDomination

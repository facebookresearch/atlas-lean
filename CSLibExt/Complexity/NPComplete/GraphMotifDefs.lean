/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# GRAPH MOTIF: definitions

Source:
M. R. Fellows, G. Fertin, D. Hermelin and S. Vialette, "Upper and lower bounds for finding
connected motifs in vertex-colored graphs", Journal of Computer and System Sciences 77(4)
(2011), 799-811, doi:10.1016/j.jcss.2010.07.003;
V. Lacroix, C. G. Fernandes and M.-F. Sagot, "Motif search in graphs: application to metabolic
networks", IEEE/ACM Transactions on Computational Biology and Bioinformatics 3(4) (2006),
360-368, doi:10.1109/TCBB.2006.55.
-/
module

public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Computability.Complexity.Karp.Color
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Data.Multiset.MapFold
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.GraphMotif

/-- An instance: vertex count `n` (vertices `0, …, n - 1`), edge list, the colors of the
vertices in order, and the motif `M` as a list. -/
abbrev GraphMotifInstance := ℕ × List (ℕ × ℕ) × List ℕ × List ℕ

/-- The graph of the instance as a `SimpleGraph (Fin n)`. -/
def Graph (i : GraphMotifInstance) : SimpleGraph (Fin i.1) :=
  Cslib.Complexity.Karp.edgeGraph i.1 i.2.1

/-- The color of vertex `v`. -/
def color (i : GraphMotifInstance) (v : Fin i.1) : ℕ :=
  i.2.2.1.getD v 0

/-- Well-formedness of an instance: the edge list describes a simple graph (no duplicate edges
in either orientation, no self-loops, endpoints in range), and there is one color per
vertex. -/
def WellFormed (i : GraphMotifInstance) : Prop :=
  (i.2.1.Nodup ∧ ∀ e ∈ i.2.1, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2.1) ∧
    i.2.2.1.length = i.1

/-- Some vertex set `S` induces a connected subgraph and has color multiset `M`. -/
def GraphMotifFeasible (i : GraphMotifInstance) : Prop :=
  ∃ S : Finset (Fin i.1), ((Graph i).induce (S : Set (Fin i.1))).Connected ∧
    S.val.map (color i) = (i.2.2.2 : Multiset ℕ)

open Classical in
/-- GRAPH MOTIF as a decision problem over bitstrings. -/
noncomputable def graphMotifDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := GraphMotifInstance) x with
  | some i => decide (WellFormed i ∧ GraphMotifFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.GraphMotif

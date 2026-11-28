/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# EVEN ALTERNATING PATH (2-arc-colored digraphs): definitions

Source:
D. S. Johnson, "The NP-completeness column: an ongoing guide", J. Algorithms 3 (1982), 381-395,
doi:10.1016/0196-6774(82)90032-3, comment to problem [3] EVEN LENGTH PATH (reference:
O. Vornberger, "Komplexität von Wegproblemen in Graphen", Doctoral Thesis, Gesamthochschule
Paderborn (1980)).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.EvenLengthPathDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.EvenAlternatingPath

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

end MetaMathlibExt.Complexity.NPComplete.EvenAlternatingPath

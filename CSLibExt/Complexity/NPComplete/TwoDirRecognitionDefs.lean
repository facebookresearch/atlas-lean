/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# RECOGNITION OF 2-DIR GRAPHS: definitions

Source:
J. Kratochvíl and J. Matoušek, "NP-hardness results for intersection graphs", Commentationes
Mathematicae Universitatis Carolinae 30 (1989), 761-773, http://dml.cz/dmlcz/106799 (Theorem 1:
"RECOG(k-DIR) and RECOG(PURE-k-DIR), for every k ≥ 2, are NP-complete"; Proposition 5, whose
proof for 2-DIR is deferred to the next reference);
J. Kratochvíl, "A special planar satisfiability problem and a consequence of its
NP-completeness", Discrete Applied Mathematics 52 (1994), 233-252,
doi:10.1016/0166-218X(94)90143-0;
ISGCI, *Information System on Graph Classes and their Inclusions*, class "2-DIR" (gc_864),
problem Recognition: NP-complete.
-/
module

public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Computability.Complexity.Karp.Color
public import CSLibExt.Complexity.NPComplete.SegmentIntersectionCliqueDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.TwoDirRecognition

open SegmentIntersectionClique (Seg toPoint segPoints)

/-- An instance: vertex count `n` (vertices `Fin n`) and edge list. -/
abbrev TwoDirRecognitionInstance := ℕ × List (ℕ × ℕ)

/-- The graph of the instance as a `SimpleGraph (Fin n)`. -/
def Graph (i : TwoDirRecognitionInstance) : SimpleGraph (Fin i.1) :=
  Cslib.Complexity.Karp.edgeGraph i.1 i.2

/-- A segment with distinct endpoints that is horizontal (equal y-coordinates) or vertical (equal
x-coordinates). -/
def IsAxisSegment (σ : Seg) : Prop :=
  toPoint σ.1 ≠ toPoint σ.2 ∧ ((toPoint σ.1).2 = (toPoint σ.2).2 ∨ (toPoint σ.1).1 = (toPoint σ.2).1)

/-- `G` is a 2-DIR graph: some assignment of horizontal or vertical segments to the vertices makes
two distinct vertices adjacent exactly when their segments intersect. -/
def IsTwoDir {n : ℕ} (G : SimpleGraph (Fin n)) : Prop :=
  ∃ rep : Fin n → Seg, (∀ v, IsAxisSegment (rep v)) ∧
    ∀ u v, u ≠ v → (G.Adj u v ↔ (segPoints (rep u) ∩ segPoints (rep v)).Nonempty)

/-- Well-formedness of an instance: the edge list describes a simple graph on `Fin n` (no
duplicate edges in either orientation, no self-loops, endpoints in range). -/
def WellFormed (i : TwoDirRecognitionInstance) : Prop :=
  i.2.Nodup ∧ ∀ e ∈ i.2, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2

/-- The graph is a 2-DIR graph. -/
def TwoDirRecognitionFeasible (i : TwoDirRecognitionInstance) : Prop :=
  IsTwoDir (Graph i)

open Classical in
/-- RECOGNITION OF 2-DIR GRAPHS as a decision problem over bitstrings. -/
noncomputable def twoDirRecognitionDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := TwoDirRecognitionInstance) x with
  | some i => decide (WellFormed i ∧ TwoDirRecognitionFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.TwoDirRecognition

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# POLARITY OF (2K₂, C₅)-FREE GRAPHS: definitions

Source:
V. B. Le and R. Nevries, "Complexity and algorithms for recognizing polar and monopolar
graphs", Theoretical Computer Science 528 (2014), 1-11, doi:10.1016/j.tcs.2014.01.032
(recognizing polar graphs is NP-complete on `{2K₂, C₅}`-free co-planar graphs).
-/
module

public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Computability.Complexity.Karp.Color
public import Mathlib.Combinatorics.SimpleGraph.Copy
public import Mathlib.Combinatorics.SimpleGraph.CycleGraph
public import Mathlib.Combinatorics.SimpleGraph.Hasse
public import Mathlib.Combinatorics.SimpleGraph.Sum
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.PolarityTriangleFreeDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.PolarityTwoKTwoCFiveFree

open MetaMathlibExt.Complexity.NPComplete.PolarityTriangleFree (IsPolar)

/-- An instance: vertex count `n` (vertices `Fin n`) and edge list. -/
abbrev PolarityTwoKTwoCFiveFreeInstance := ℕ × List (ℕ × ℕ)

/-- The graph of the instance as a `SimpleGraph (Fin n)`. -/
def Graph (i : PolarityTwoKTwoCFiveFreeInstance) : SimpleGraph (Fin i.1) :=
  Cslib.Complexity.Karp.edgeGraph i.1 i.2

/-- Well-formedness of an instance: the edge list describes a simple graph on `Fin n` (no
duplicate edges in either orientation, no self-loops, endpoints in range) with no induced `2K₂`
and no induced `C₅`. -/
def WellFormed (i : PolarityTwoKTwoCFiveFreeInstance) : Prop :=
  (i.2.Nodup ∧ ∀ e ∈ i.2, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2) ∧
    ¬ (SimpleGraph.pathGraph 2 ⊕g SimpleGraph.pathGraph 2).IsIndContained (Graph i) ∧
    ¬ (SimpleGraph.cycleGraph 5).IsIndContained (Graph i)

/-- The graph is polar. -/
def PolarityTwoKTwoCFiveFreeFeasible (i : PolarityTwoKTwoCFiveFreeInstance) : Prop :=
  IsPolar (Graph i)

open Classical in
/-- POLARITY OF (2K₂, C₅)-FREE GRAPHS as a decision problem over bitstrings. -/
noncomputable def polarityTwoKTwoCFiveFreeDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := PolarityTwoKTwoCFiveFreeInstance) x with
  | some i => decide (WellFormed i ∧ PolarityTwoKTwoCFiveFreeFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.PolarityTwoKTwoCFiveFree

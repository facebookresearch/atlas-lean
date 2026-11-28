/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# BOXICITY AT MOST 2: definitions

Source:
J. Kratochvíl, "A special planar satisfiability problem and a consequence of its
NP-completeness", Discrete Applied Mathematics 52 (1994), 233-252,
doi:10.1016/0166-218X(94)90143-0 (abstract: NP-completeness "of recognizing several classes of
intersection graphs of geometric objects in the plane, including grid intersection graphs and
graphs of boxicity two").
-/
module

public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Computability.Complexity.Karp.Color
public import Mathlib.Basic.Real.Basic
public import Mathlib.Order.Interval.Set.Basic

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.BoxicityTwo

/-- An instance: vertex count `n` (vertices `Fin n`) and edge list. -/
abbrev BoxicityTwoInstance := ℕ × List (ℕ × ℕ)

/-- The graph of the instance as a `SimpleGraph (Fin n)`. -/
def Graph (i : BoxicityTwoInstance) : SimpleGraph (Fin i.1) :=
  Cslib.Complexity.Karp.edgeGraph i.1 i.2

/-- Well-formedness of an instance: the edge list describes a simple graph on `Fin n` (no
duplicate edges in either orientation, no self-loops, endpoints in range). -/
def WellFormed (i : BoxicityTwoInstance) : Prop :=
  i.2.Nodup ∧ ∀ e ∈ i.2, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2

/-- The graph is an intersection graph of closed axis-parallel rectangles: vertex `v` gets the
nonempty rectangle `Set.Icc (lo v) (hi v)` of `ℝ × ℝ`, and two distinct vertices are adjacent
exactly when their rectangles intersect. -/
def BoxicityTwoFeasible (i : BoxicityTwoInstance) : Prop :=
  ∃ lo hi : Fin i.1 → ℝ × ℝ, (∀ v, lo v ≤ hi v) ∧
    ∀ u v, u ≠ v → ((Graph i).Adj u v ↔ (Set.Icc (lo u) (hi u) ∩ Set.Icc (lo v) (hi v)).Nonempty)

open Classical in
/-- BOXICITY AT MOST 2 as a decision problem over bitstrings. -/
noncomputable def boxicityTwoDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := BoxicityTwoInstance) x with
  | some i => decide (WellFormed i ∧ BoxicityTwoFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.BoxicityTwo

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# BOXICITY AT MOST 2 is NP-complete

Source:
J. Kratochvíl, "A special planar satisfiability problem and a consequence of its
NP-completeness", Discrete Applied Mathematics 52 (1994), 233-252,
doi:10.1016/0166-218X(94)90143-0 (abstract: NP-completeness "of recognizing several classes of
intersection graphs of geometric objects in the plane, including grid intersection graphs and
graphs of boxicity two").
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Computability.Complexity.Karp.Color
public import Mathlib.Basic.Real.Basic
public import Mathlib.Order.Interval.Set.Basic

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.BoxicityTwo

/-!
# BOXICITY AT MOST 2 is NP-complete

INSTANCE: a graph `G = (V, E)`. QUESTION: is the boxicity of `G` at most `2`, i.e., is `G` the
intersection graph of a family of axis-parallel rectangles in the plane, one per vertex, two
distinct vertices being adjacent exactly when their rectangles intersect?

A closed axis-parallel rectangle `[x₁, x₂] × [y₁, y₂]` is the order interval
`Set.Icc (x₁, y₁) (x₂, y₂)` of `ℝ × ℝ` with its componentwise order; it is nonempty when
`(x₁, y₁) ≤ (x₂, y₂)`. This mirrors the interval representation of `IsIntervalGraph` in
`IntervalGraphCompletionWanted` (closed intervals `Set.Icc` of `ℝ`, adjacency iff the
intervals meet), one dimension up. Graphs of boxicity `0` (complete graphs) and `1` (interval
graphs) are included, as "at most 2" requires.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

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

/-- **BOXICITY AT MOST 2 is NP-complete.** Source: Kratochvíl (1994). -/
public theorem_wanted boxicityTwo_npComplete :
    boxicityTwoDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L boxicityTwoDec

end MetaMathlibExt.Complexity.NPComplete.BoxicityTwo

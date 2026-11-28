/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# BOUNDED DIAMETER AUGMENTATION: definitions

Source:
P. Crescenzi and V. Kann (eds.), *A compendium of NP optimization problems*, web edition
(2000), problem MINIMUM BOUNDED DIAMETER AUGMENTATION;
C.-L. Li, S. T. McCormick and D. Simchi-Levi, "On the minimum-cardinality-bounded-diameter and
the bounded-cardinality-minimum-diameter edge addition problems", Operations Research Letters
11 (1992), 303-308, doi:10.1016/0167-6377(92)90007-P.
-/
module

public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Computability.Complexity.Karp.Color
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Combinatorics.SimpleGraph.Diam
public import Mathlib.Data.Set.Card

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.BoundedDiameterAugmentation

/-- An instance: the vertex count `n` in unary (a list of length `n`; vertices `0, …, n - 1`),
the edge list, the diameter bound `D`, and the bound `K` on the number of added edges. -/
abbrev BoundedDiameterAugmentationInstance := List Bool × List (ℕ × ℕ) × ℕ × ℕ

/-- The graph of the instance as a `SimpleGraph (Fin n)`, `n` the length of the unary list. -/
def Graph (i : BoundedDiameterAugmentationInstance) : SimpleGraph (Fin i.1.length) :=
  Cslib.Complexity.Karp.edgeGraph i.1.length i.2.1

/-- Well-formedness of an instance: `n` is written in unary as `[true, …, true]`, the edge list
describes a simple graph (no duplicate edges in either orientation, no self-loops, endpoints in
range), `0 < D < |V|`, and `K` is positive. -/
def WellFormed (i : BoundedDiameterAugmentationInstance) : Prop :=
  (∀ b ∈ i.1, b = true) ∧
    (i.2.1.Nodup ∧ ∀ e ∈ i.2.1, e.1 < i.1.length ∧ e.2 < i.1.length ∧ e.1 ≠ e.2 ∧
      (e.2, e.1) ∉ i.2.1) ∧
    0 < i.2.2.1 ∧ i.2.2.1 < i.1.length ∧ 0 < i.2.2.2

/-- Some set `H` of at most `K` vertex pairs makes the diameter of `G ⊔ H` at most `D`. -/
def BoundedDiameterAugmentationFeasible (i : BoundedDiameterAugmentationInstance) : Prop :=
  ∃ H : SimpleGraph (Fin i.1.length), H.edgeSet.ncard ≤ i.2.2.2 ∧
    (Graph i ⊔ H).ediam ≤ (i.2.2.1 : ℕ∞)

open Classical in
/-- BOUNDED DIAMETER AUGMENTATION as a decision problem over bitstrings. -/
noncomputable def boundedDiameterAugmentationDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := BoundedDiameterAugmentationInstance) x with
  | some i => decide (WellFormed i ∧ BoundedDiameterAugmentationFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.BoundedDiameterAugmentation

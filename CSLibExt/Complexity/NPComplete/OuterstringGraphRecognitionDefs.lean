/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# OUTERSTRING GRAPH RECOGNITION: definitions

Source:
A. Rok and B. Walczak, "Outerstring graphs are χ-bounded", SIAM Journal on Discrete Mathematics
33 (2019), 2181-2199, doi:10.1137/17M1157374 (arXiv:1312.1559; Section 1: the definition of
outerstring graphs used below, NP-hardness of their recognition after J. Kratochvíl, "String
graphs. I. The number of critical nonstring graphs is infinite", Journal of Combinatorial Theory,
Series B 52 (1991), 53-66, doi:10.1016/0095-8956(91)90090-7, and membership in NP by reduction to
string graph recognition, which is in NP by M. Schaefer, E. Sedgwick and D. Štefankovič,
"Recognizing string graphs in NP", Journal of Computer and System Sciences 67 (2003), 365-380,
doi:10.1016/S0022-0000(03)00045-X);
ISGCI (https://www.graphclasses.org/classes/gc_951.html), class outer-string, problem
"Recognition": NP-complete, citing Rok and Walczak.
-/
module

public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Computability.Complexity.Karp.Color
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Basic.Real.Basic
public import Mathlib.Topology.ContinuousMap.Defs
public import Mathlib.Topology.UnitInterval

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.OuterstringGraphRecognition

/-- An instance: vertex count `n` (vertices `Fin n`) and edge list. -/
abbrev OuterstringGraphRecognitionInstance := ℕ × List (ℕ × ℕ)

/-- The graph of the instance as a `SimpleGraph (Fin n)`. -/
def Graph (i : OuterstringGraphRecognitionInstance) : SimpleGraph (Fin i.1) :=
  Cslib.Complexity.Karp.edgeGraph i.1 i.2

/-- Well-formedness of an instance: the edge list describes a simple graph on `Fin n` (no
duplicate edges in either orientation, no self-loops, endpoints in range). -/
def WellFormed (i : OuterstringGraphRecognitionInstance) : Prop :=
  i.2.Nodup ∧ ∀ e ∈ i.2, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2

/-- `γ` is a grounded curve: an injective continuous map from `[0, 1]` to the plane whose point
`γ 0` lies on the line `y = 0` and whose other points lie strictly above it. -/
def IsGroundedCurve (γ : C(unitInterval, ℝ × ℝ)) : Prop :=
  Function.Injective γ ∧ (γ 0).2 = 0 ∧ ∀ t, t ≠ 0 → 0 < (γ t).2

/-- `G` is an outerstring graph: there are grounded curves `γ v`, one per vertex and pairwise
distinct as sets, such that two distinct vertices are adjacent exactly when their curves
intersect. -/
def IsOuterstring {n : ℕ} (G : SimpleGraph (Fin n)) : Prop :=
  ∃ γ : Fin n → C(unitInterval, ℝ × ℝ), (∀ v, IsGroundedCurve (γ v)) ∧
    Function.Injective (fun v => Set.range (γ v)) ∧
    ∀ u v, u ≠ v → (G.Adj u v ↔ (Set.range (γ u) ∩ Set.range (γ v)).Nonempty)

/-- The graph of the instance is an outerstring graph. -/
def OuterstringGraphRecognitionFeasible (i : OuterstringGraphRecognitionInstance) : Prop :=
  IsOuterstring (Graph i)

open Classical in
/-- OUTERSTRING GRAPH RECOGNITION as a decision problem over bitstrings. -/
noncomputable def outerstringGraphRecognitionDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := OuterstringGraphRecognitionInstance) x with
  | some i => decide (WellFormed i ∧ OuterstringGraphRecognitionFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.OuterstringGraphRecognition

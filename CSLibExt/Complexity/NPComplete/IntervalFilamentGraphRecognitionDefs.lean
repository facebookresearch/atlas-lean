/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# RECOGNITION OF INTERVAL FILAMENT GRAPHS: definitions

Source:
M. Pergel, "Recognition of polygon-circle graphs and graphs of interval filaments is
NP-complete", Graph-Theoretic Concepts in Computer Science (WG 2007), LNCS 4769 (2007), 238-247,
doi:10.1007/978-3-540-74839-7_23;
F. Gavril, "Maximum weight independent sets and cliques in intersection graphs of filaments",
Information Processing Letters 73 (2000), 181-188, doi:10.1016/S0020-0190(00)00025-9 (the class).
-/
module

public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Computability.Complexity.Karp.Color
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Basic.Real.Basic
public import Mathlib.Order.Interval.Set.Defs
public import Mathlib.Topology.ContinuousOn
public import Mathlib.Topology.MetricSpace.Pseudo.Defs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.IntervalFilamentGraphRecognition

/-- An instance: vertex count `n` (vertices `0, …, n - 1`) and edge list. -/
abbrev IntervalFilamentGraphRecognitionInstance := ℕ × List (ℕ × ℕ)

/-- The graph of the instance as a `SimpleGraph (Fin n)`. -/
def Graph (i : IntervalFilamentGraphRecognitionInstance) : SimpleGraph (Fin i.1) :=
  Cslib.Complexity.Karp.edgeGraph i.1 i.2

/-- Well-formedness of an instance: the edge list describes a simple graph on `0, …, n - 1` (no
duplicate edges in either orientation, no self-loops, endpoints in range). -/
def WellFormed (i : IntervalFilamentGraphRecognitionInstance) : Prop :=
  i.2.Nodup ∧ ∀ e ∈ i.2, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2

/-- `(a, b, f)` is an interval filament representation of `G`: for every vertex `v`, `f v` is
continuous and non-negative on the closed interval `[a v, b v]` with `a v < b v`, and zero at both
endpoints; and two distinct vertices are adjacent if and only if their filaments (the graphs of
`f u` and `f v` over their intervals) have a common point. -/
def IsIntervalFilamentRepresentation {V : Type*} (G : SimpleGraph V) (a b : V → ℝ)
    (f : V → ℝ → ℝ) : Prop :=
  (∀ v, a v < b v ∧ ContinuousOn (f v) (Set.Icc (a v) (b v)) ∧
      (∀ x ∈ Set.Icc (a v) (b v), 0 ≤ f v x) ∧ f v (a v) = 0 ∧ f v (b v) = 0) ∧
    ∀ u v, u ≠ v →
      (G.Adj u v ↔ ∃ x ∈ Set.Icc (a u) (b u) ∩ Set.Icc (a v) (b v), f u x = f v x)

/-- The graph of the instance is an interval filament graph. -/
def IntervalFilamentGraphRecognitionFeasible (i : IntervalFilamentGraphRecognitionInstance) :
    Prop :=
  ∃ (a b : Fin i.1 → ℝ) (f : Fin i.1 → ℝ → ℝ), IsIntervalFilamentRepresentation (Graph i) a b f

open Classical in
/-- RECOGNITION OF INTERVAL FILAMENT GRAPHS as a decision problem over bitstrings. -/
noncomputable def intervalFilamentGraphRecognitionDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := IntervalFilamentGraphRecognitionInstance) x with
  | some i => decide (WellFormed i ∧ IntervalFilamentGraphRecognitionFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.IntervalFilamentGraphRecognition

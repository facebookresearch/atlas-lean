/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# WEAK BISPLIT GRAPH RECOGNITION: definitions

Source:
A. Brandstädt, P. L. Hammer, V. B. Le and V. V. Lozin, "Bisplit graphs", Discrete Mathematics
299 (2005), 11-32, doi:10.1016/j.disc.2004.08.046 (Section 4: the definitions of `k`-bisplit and
weak bisplit graphs; Theorem 15: "Recognizing weak bisplit graphs is NP-complete, even for
3-colorable comparability graphs"; earlier version: Rutcor Research Report RRR 28-2002).
-/
module

public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Computability.Complexity.Karp.Color
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Data.Finset.Basic

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.WeakBisplitRecognition

/-- An instance: vertex count `n` (vertices `0, …, n - 1`) and edge list. -/
abbrev WeakBisplitRecognitionInstance := ℕ × List (ℕ × ℕ)

/-- The graph of the instance as a `SimpleGraph (Fin n)`. -/
def Graph (i : WeakBisplitRecognitionInstance) : SimpleGraph (Fin i.1) :=
  Cslib.Complexity.Karp.edgeGraph i.1 i.2

/-- Well-formedness of an instance: the edge list describes a simple graph on `0, …, n - 1` (no
duplicate edges in either orientation, no self-loops, endpoints in range). -/
def WellFormed (i : WeakBisplitRecognitionInstance) : Prop :=
  i.2.Nodup ∧ ∀ e ∈ i.2, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2

/-- `G` is weak bisplit: some stable set `X` has every connected component of `G[V \ X]` a
bi-clique, with sides given by `s`: two vertices outside `X` that are joined by a path outside
`X` are adjacent exactly when they lie on different sides. -/
def IsWeakBisplit {n : ℕ} (G : SimpleGraph (Fin n)) : Prop :=
  ∃ X : Finset (Fin n), G.IsIndepSet (X : Set (Fin n)) ∧ ∃ s : Fin n → Bool,
    ∀ u v : ↥(X : Set (Fin n))ᶜ, (G.induce (X : Set (Fin n))ᶜ).Reachable u v →
      (G.Adj u v ↔ s u ≠ s v)

/-- The graph of the instance is weak bisplit. -/
def WeakBisplitRecognitionFeasible (i : WeakBisplitRecognitionInstance) : Prop :=
  IsWeakBisplit (Graph i)

open Classical in
/-- WEAK BISPLIT GRAPH RECOGNITION as a decision problem over bitstrings. -/
noncomputable def weakBisplitRecognitionDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := WeakBisplitRecognitionInstance) x with
  | some i => decide (WellFormed i ∧ WeakBisplitRecognitionFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.WeakBisplitRecognition

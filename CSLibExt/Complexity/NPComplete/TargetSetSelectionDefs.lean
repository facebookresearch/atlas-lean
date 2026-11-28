/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# TARGET SET SELECTION: definitions

Source:
P. A. Dreyer Jr. and F. S. Roberts, "Irreversible k-threshold processes: graph-theoretical
threshold models of the spread of disease and of opinion", Discrete Applied Mathematics 157(7)
(2009), 1615-1627, doi:10.1016/j.dam.2008.09.012;
N. Chen, "On the approximability of influence in social networks", SIAM Journal on Discrete
Mathematics 23(3) (2009), 1400-1415, doi:10.1137/08073617X;
J. Kynčl, B. Lidický and T. Vyskočil, "Irreversible 2-conversion set in graphs of bounded
degree", Discrete Mathematics & Theoretical Computer Science 19(3) (2017),
doi:10.23638/DMTCS-19-3-5.
-/
module

public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Computability.Complexity.Karp.Color
public import Mathlib.Data.Set.Card

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.TargetSetSelection

/-- An instance: vertex count `n` (vertices `Fin n`), edge list, thresholds `t(0), …, t(n - 1)`,
bound `K`. -/
abbrev TargetSetSelectionInstance := ℕ × List (ℕ × ℕ) × List ℕ × ℕ

/-- The graph of the instance as a `SimpleGraph (Fin n)`. -/
def Graph (i : TargetSetSelectionInstance) : SimpleGraph (Fin i.1) :=
  Cslib.Complexity.Karp.edgeGraph i.1 i.2.1

/-- The threshold `t(v)` of vertex `v`. -/
def threshold (i : TargetSetSelectionInstance) (v : Fin i.1) : ℕ :=
  i.2.2.1.getD v 0

/-- The active vertices after `k` rounds, starting from `S`: a vertex becomes active once at
least `t(v)` of its neighbors are active, and stays active. -/
def activated (i : TargetSetSelectionInstance) (S : Set (Fin i.1)) : ℕ → Set (Fin i.1)
  | 0 => S
  | k + 1 => activated i S k ∪
      {v | threshold i v ≤ ((Graph i).neighborSet v ∩ activated i S k).ncard}

/-- Well-formedness of an instance: the edge list describes a simple graph on `Fin n` (no
duplicate edges in either orientation, no self-loops, endpoints in range), there is one positive
threshold per vertex, and `0 < K ≤ n`. -/
def WellFormed (i : TargetSetSelectionInstance) : Prop :=
  (i.2.1.Nodup ∧ ∀ e ∈ i.2.1, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2.1) ∧
    i.2.2.1.length = i.1 ∧ (∀ t ∈ i.2.2.1, 0 < t) ∧ 0 < i.2.2.2 ∧ i.2.2.2 ≤ i.1

/-- Some target set of at most `K` vertices activates every vertex within `n` rounds. -/
def TargetSetSelectionFeasible (i : TargetSetSelectionInstance) : Prop :=
  ∃ S : Finset (Fin i.1), S.card ≤ i.2.2.2 ∧ activated i S i.1 = Set.univ

open Classical in
/-- TARGET SET SELECTION as a decision problem over bitstrings. -/
noncomputable def targetSetSelectionDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := TargetSetSelectionInstance) x with
  | some i => decide (WellFormed i ∧ TargetSetSelectionFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.TargetSetSelection

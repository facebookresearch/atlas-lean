/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# IDENTIFYING CODE: definitions

Source:
I. Charon, O. Hudry and A. Lobstein, "Minimizing the size of an identifying or locating-dominating
code in a graph is NP-hard", Theoretical Computer Science 290 (2003), 2109-2120,
doi:10.1016/S0304-3975(02)00536-4, Theorem 2.1 (with `r = 1`).
-/
module

public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Computability.Complexity.Karp.Color
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Combinatorics.SimpleGraph.Metric

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.IdentifyingCode

/-- An instance: vertex count `n`, edge list, bound `K`. -/
abbrev IdentifyingCodeInstance := ℕ × List (ℕ × ℕ) × ℕ

/-- The graph of the instance as a `SimpleGraph (Fin n)`. -/
def Graph (i : IdentifyingCodeInstance) : SimpleGraph (Fin i.1) :=
  Cslib.Complexity.Karp.edgeGraph i.1 i.2.1

/-- Well-formedness of an instance: the edge list describes a simple graph on `Fin n` (no
duplicate edges in either orientation, no self-loops, endpoints in range), the graph is
connected, and `K ≤ |V|`. -/
def WellFormed (i : IdentifyingCodeInstance) : Prop :=
  (i.2.1.Nodup ∧ ∀ e ∈ i.2.1, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2.1) ∧
    (Graph i).Connected ∧ i.2.2 ≤ i.1

/-- Some set `C` of at most `K` vertices is an identifying code: every ball `B₁(v)` contains a
codeword, and for distinct `u` and `v` some codeword lies in exactly one of `B₁(u)` and
`B₁(v)`. -/
def IdentifyingCodeFeasible (i : IdentifyingCodeInstance) : Prop :=
  ∃ C : Finset (Fin i.1), C.card ≤ i.2.2 ∧
    (∀ v, ∃ c ∈ C, (Graph i).dist c v ≤ 1) ∧
    ∀ u v, u ≠ v → ∃ c ∈ C, ¬ ((Graph i).dist c u ≤ 1 ↔ (Graph i).dist c v ≤ 1)

open Classical in
/-- IDENTIFYING CODE as a decision problem over bitstrings. -/
noncomputable def identifyingCodeDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := IdentifyingCodeInstance) x with
  | some i => decide (WellFormed i ∧ IdentifyingCodeFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.IdentifyingCode

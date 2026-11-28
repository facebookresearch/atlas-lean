/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# CAPACITY REPRESENTATIVES: definitions

Source:
P. Crescenzi and V. Kann (eds.), *A compendium of NP optimization problems*, MAXIMUM CAPACITY
REPRESENTATIVES;
M. Bellare, "Interactive proofs and approximation: reductions from two provers in one round",
Proceedings of the 2nd Israel Symposium on Theory and Computing Systems (ISTCS 1993), 266-274,
doi:10.1109/ISTCS.1993.253462.
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.CapacityRepresentatives

/-- An instance: the sets `S₁, ..., S_m`, the capacity matrix (rows and columns indexed by the
elements `0, ..., N - 1`), and the bound `K`. -/
abbrev CapacityRepresentativesInstance := List (List ℕ) × List (List ℕ) × ℕ

/-- Well-formedness of an instance: the capacity matrix is `N × N` with `N` its number of rows,
the sets consist of elements below `N` and are duplicate-free and pairwise disjoint, and `K` is
positive. -/
def WellFormed (i : CapacityRepresentativesInstance) : Prop :=
  (∀ row ∈ i.2.1, row.length = i.2.1.length) ∧ (∀ s ∈ i.1, ∀ x ∈ s, x < i.2.1.length) ∧
    i.1.flatten.Nodup ∧ 0 < i.2.2

/-- The capacity `c(x, y)`: the entry in row `x` and column `y` of the matrix. -/
def capacity (i : CapacityRepresentativesInstance) (x y : ℕ) : ℕ :=
  (i.2.1.getD x []).getD y 0

/-- Some choice of one representative `t[k] ∈ S_{k+1}` for every set has capacity
`∑_{k ≠ l} c(t[k], t[l])` at least `K`. -/
def CapacityRepresentativesFeasible (i : CapacityRepresentativesInstance) : Prop :=
  ∃ t : List ℕ, List.Forall₂ (fun x s => x ∈ s) t i.1 ∧
    i.2.2 ≤ ∑ k ∈ Finset.range i.1.length, ∑ l ∈ (Finset.range i.1.length).filter (· ≠ k),
      capacity i (t.getD k 0) (t.getD l 0)

open Classical in
/-- CAPACITY REPRESENTATIVES as a decision problem over bitstrings. -/
noncomputable def capacityRepresentativesDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := CapacityRepresentativesInstance) x with
  | some i => decide (WellFormed i ∧ CapacityRepresentativesFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.CapacityRepresentatives

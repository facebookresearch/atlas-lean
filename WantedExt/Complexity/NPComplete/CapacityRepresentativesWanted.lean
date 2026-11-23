/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# CAPACITY REPRESENTATIVES is NP-complete

Source:
P. Crescenzi and V. Kann (eds.), *A compendium of NP optimization problems*, MAXIMUM CAPACITY
REPRESENTATIVES;
M. Bellare, "Interactive proofs and approximation: reductions from two provers in one round",
Proceedings of the 2nd Israel Symposium on Theory and Computing Systems (ISTCS 1993), 266-274,
doi:10.1109/ISTCS.1993.253462.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.CapacityRepresentatives

/-!
# CAPACITY REPRESENTATIVES is NP-complete

INSTANCE: disjoint sets `S₁, ..., S_m` and, for any `i ≠ j`, `x ∈ Sᵢ` and `y ∈ S_j`, a
nonnegative capacity `c(x, y)`; a positive integer `K`. QUESTION: is there a system of
representatives `T`, i.e. a set `T` with `|T ∩ Sᵢ| = 1` for every `i`, whose capacity
`∑_{x, y ∈ T} c(x, y)` is at least `K`?

This is the decision version of Crescenzi and Kann's MAXIMUM CAPACITY REPRESENTATIVES,
whose entry records that it "does not admit a PTAS" (Bellare), so the decision version is
NP-hard. It contains MAX CUT directly: for a graph with edge weights `w`, take
`S_v = {v⁰, v¹}` for every vertex `v` and `c(uᵃ, vᵇ) = w(uv)` when `uv` is an edge and `a ≠ b`
(else `0`); a system of representatives is a 2-coloring, and its capacity is twice the weight of
the cut. Membership in NP: `T` is a certificate.

The elements are `0, ..., N - 1` and the capacities are an `N × N` matrix of natural numbers
(nonnegative) given as a list of rows, entry `c(x, y)` in row `x` and column `y`; entries for
two elements of the same set are never used. The sets `S₁, ..., S_m` are lists of elements,
duplicate-free and pairwise disjoint (the concatenation has no duplicates). Since the sets are
disjoint, a system of representatives is a choice of one element `tᵢ ∈ Sᵢ` for every `i` (a list
`t` with `t[i] ∈ Sᵢ`), and `∑_{x, y ∈ T} c(x, y)` is the sum of `c(tᵢ, t_j)` over the ordered
pairs `i ≠ j` (`c(x, y)` is given only for elements of different sets).

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

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

/-- **CAPACITY REPRESENTATIVES is NP-complete.** Source: Crescenzi and Kann, MAXIMUM CAPACITY
REPRESENTATIVES; Bellare (1993). -/
public theorem_wanted capacityRepresentatives_npComplete :
    capacityRepresentativesDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L capacityRepresentativesDec

end MetaMathlibExt.Complexity.NPComplete.CapacityRepresentatives

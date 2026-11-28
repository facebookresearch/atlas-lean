/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# OPTIMAL LEFT-DEEP JOIN TREE WITH CROSS PRODUCTS: definitions

Source:
S. Cluet and G. Moerkotte, "On the complexity of generating optimal left-deep processing trees
with cross products", in *Database Theory - ICDT '95*, Lecture Notes in Computer Science 893,
Springer (1995), 54-67, doi:10.1007/3-540-58907-4_6 (NP-hardness for the cost function `C_out`,
by a reduction from 3-DIMENSIONAL MATCHING, already for star queries);
G. Moerkotte, *Building Query Compilers*, Section 3.1 (cardinalities, selectivities and `C_out`)
and Section 3.1.6 (the complexity table, "general/tree/star, left-deep, cross products: yes,
ASI: NP-hard", credited to Cluet and Moerkotte).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Order.Field.Rat
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Logic.Equiv.Defs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.OptimalLeftDeepJoinTreeCrossProducts

/-- An instance: the cardinalities `|Rᵢ|`, the selectivities as entries `(i, j, p, q)` meaning
`f_{i,j} = p / q`, and the bound `K`. -/
abbrev OptimalLeftDeepJoinTreeCrossProductsInstance :=
  List ℕ × List (ℕ × ℕ × ℕ × ℕ) × ℕ

/-- The relations of the instance, `Fin n` for `n` listed cardinalities. -/
abbrev Relation (i : OptimalLeftDeepJoinTreeCrossProductsInstance) : Type := Fin i.1.length

/-- The cardinality `|Rₐ|` of relation `a`. -/
def cardinality (i : OptimalLeftDeepJoinTreeCrossProductsInstance) (a : Relation i) : ℕ :=
  i.1.get a

/-- Well-formedness of an instance: there is at least one relation, every cardinality is
positive, every selectivity entry `(i, j, p, q)` has `i < j < n` and `0 < p ≤ q`, and no pair
`(i, j)` is listed twice. -/
def WellFormed (i : OptimalLeftDeepJoinTreeCrossProductsInstance) : Prop :=
  i.1 ≠ [] ∧ (∀ c ∈ i.1, 0 < c) ∧
    (∀ e ∈ i.2.1, e.1 < e.2.1 ∧ e.2.1 < i.1.length ∧ 0 < e.2.2.1 ∧ e.2.2.1 ≤ e.2.2.2) ∧
    (i.2.1.map fun e => (e.1, e.2.1)).Nodup

/-- The selectivity `f_{a,b}`: `p / q` for the entry `(min a b, max a b, p, q)`, and `1` when no
entry lists the pair (no join predicate, a cross product; in particular `f_{a,a} = 1`). -/
def selectivity (i : OptimalLeftDeepJoinTreeCrossProductsInstance) (a b : Relation i) : ℚ :=
  match i.2.1.find? (fun e => decide (e.1 = min (a : ℕ) b ∧ e.2.1 = max (a : ℕ) b)) with
  | some e => (e.2.2.1 : ℚ) / e.2.2.2
  | none => 1

/-- The output cardinality `|s₁, …, s_{k+1}|` of joining the relations at positions `0, …, k`
of the order `π`: `∏_{a ≤ k} |R_{π a}| · ∏_{a < b ≤ k} f_{π a, π b}`. -/
def prefixCardinality (i : OptimalLeftDeepJoinTreeCrossProductsInstance)
    (π : Equiv.Perm (Relation i)) (k : Relation i) : ℚ :=
  (∏ a ∈ Finset.univ.filter (· ≤ k), (cardinality i (π a) : ℚ)) *
    ∏ ab ∈ Finset.univ.filter (fun ab : Relation i × Relation i => ab.1 < ab.2 ∧ ab.2 ≤ k),
      selectivity i (π ab.1) (π ab.2)

/-- The cost `C_out` of the left-deep tree joining the relations in the order `π`: the sum of
the output cardinalities of its joins, `∑_{k ≥ 1} |s₁, …, s_{k+1}|`. -/
def cOut (i : OptimalLeftDeepJoinTreeCrossProductsInstance) (π : Equiv.Perm (Relation i)) :
    ℚ :=
  ∑ k ∈ Finset.univ.filter (fun k : Relation i => 0 < (k : ℕ)), prefixCardinality i π k

/-- Some left-deep tree (an order `π` of the relations, cross products allowed) has
`C_out ≤ K`. -/
def OptimalLeftDeepJoinTreeCrossProductsFeasible
    (i : OptimalLeftDeepJoinTreeCrossProductsInstance) : Prop :=
  ∃ π : Equiv.Perm (Relation i), cOut i π ≤ i.2.2

open Classical in
/-- OPTIMAL LEFT-DEEP JOIN TREE WITH CROSS PRODUCTS as a decision problem over bitstrings. -/
noncomputable def optimalLeftDeepJoinTreeCrossProductsDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := OptimalLeftDeepJoinTreeCrossProductsInstance) x with
  | some i => decide (WellFormed i ∧ OptimalLeftDeepJoinTreeCrossProductsFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.OptimalLeftDeepJoinTreeCrossProducts

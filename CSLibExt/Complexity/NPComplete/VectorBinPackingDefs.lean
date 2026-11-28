/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# VECTOR BIN PACKING: definitions

Source:
G. J. Woeginger, "There is no asymptotic PTAS for two-dimensional vector packing", Information
Processing Letters 64 (1997), 293-297, doi:10.1016/S0020-0190(97)00179-8 (problem statement:
"the input consists of a list L of vectors in [0, 1]^d. The goal is to partition the vectors in
L into the minimum number of subsets, such that in every subset the sum of all vectors is at
most one in every coordinate"; "The vector packing problem is easily seen to be NP-complete,
since it contains classical bin packing as a special case");
M. R. Garey, R. L. Graham, D. S. Johnson and A. C.-C. Yao, "Resource constrained scheduling as
generalized bin packing", Journal of Combinatorial Theory, Series A 21 (1976), 257-298,
doi:10.1016/0097-3165(76)90001-7 (the model);
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of
NP-Completeness*, W. H. Freeman (1979), problem [SR1] BIN PACKING (the case `d = 1`).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Order.Field.Rat

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.VectorBinPacking

/-- An instance: the dimension `d`, the items (each a list of `d` coordinates, coordinate
`(p, q)` denoting `p / q`), and the number `K` of bins. -/
abbrev VectorBinPackingInstance := ℕ × List (List (ℕ × ℕ)) × ℕ

/-- The items of the instance, `Fin n` for `n` listed vectors. -/
abbrev Item (i : VectorBinPackingInstance) : Type := Fin i.2.1.length

/-- Coordinate `c` of item `j`, the rational `p / q` for the listed pair `(p, q)`. -/
def coord (i : VectorBinPackingInstance) (j : Item i) (c : Fin i.1) : ℚ :=
  (((i.2.1.get j).getD c (0, 1)).1 : ℚ) / (((i.2.1.get j).getD c (0, 1)).2 : ℚ)

/-- Well-formedness of an instance: `d ≥ 2`, every item lists `d` coordinates, each a pair
`(p, q)` with `0 < q` and `p ≤ q` (a rational in `[0, 1]`), and `K` is positive. -/
def WellFormed (i : VectorBinPackingInstance) : Prop :=
  2 ≤ i.1 ∧ (∀ v ∈ i.2.1, v.length = i.1 ∧ ∀ x ∈ v, 0 < x.2 ∧ x.1 ≤ x.2) ∧ 0 < i.2.2

/-- Some assignment of the items to `K` bins keeps the sum of the vectors in every bin at most
`1` in every coordinate. -/
def VectorBinPackingFeasible (i : VectorBinPackingInstance) : Prop :=
  ∃ σ : Item i → Fin i.2.2, ∀ b : Fin i.2.2, ∀ c : Fin i.1,
    ∑ j ∈ Finset.univ.filter (fun j => σ j = b), coord i j c ≤ 1

open Classical in
/-- VECTOR BIN PACKING as a decision problem over bitstrings. -/
noncomputable def vectorBinPackingDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := VectorBinPackingInstance) x with
  | some i => decide (WellFormed i ∧ VectorBinPackingFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.VectorBinPacking

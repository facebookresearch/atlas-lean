/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# INTEGER M-DIMENSIONAL KNAPSACK: definitions

Source:
P. Crescenzi and V. Kann (eds.), *A compendium of NP optimization problems*, problem
MAXIMUM INTEGER M-DIMENSIONAL KNAPSACK (decision version; "generalization of [MP10]");
A. K. Chandra, D. S. Hirschberg and C. K. Wong, "Approximate algorithms for some generalized
knapsack problems", Theoret. Comput. Sci. 3 (1976), 293-304,
doi:10.1016/0304-3975(76)90048-7 (the multi-dimensional knapsack problem);
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [MP10] INTEGER KNAPSACK (p. 247;
reference of the entry: G. S. Lueker, "Two NP-complete problems in nonnegative integer
programming", Report 178, Computer Science Laboratory, Princeton University (1975)).
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.IntegerMDimensionalKnapsack

/-- An instance: the columns `j = 1, …, n` (each the column `(a_{1,j}, …, a_{m,j})` of `A`
paired with `c_j`), the vector `b = (b_1, …, b_m)`, and the bound `K`. -/
abbrev IntegerMDimensionalKnapsackInstance := List (List ℕ × ℕ) × List ℕ × ℕ

/-- Well-formedness of an instance for the fixed `m`: every column of `A` has `m` entries,
`b` has `m` entries, and `K` is positive. -/
def WellFormed (m : ℕ) (i : IntegerMDimensionalKnapsackInstance) : Prop :=
  (∀ col ∈ i.1, col.1.length = m) ∧ i.2.1.length = m ∧ 0 < i.2.2

/-- There is `x ∈ ℕⁿ` with `∑_j a_{r,j} x_j ≤ b_r` for every row `r` and `∑_j c_j x_j ≥ K`. -/
def IntegerMDimensionalKnapsackFeasible (i : IntegerMDimensionalKnapsackInstance) : Prop :=
  ∃ x : Fin i.1.length → ℕ,
    (∀ r : Fin i.2.1.length, ∑ j, (i.1.get j).1.getD r 0 * x j ≤ i.2.1.get r) ∧
      i.2.2 ≤ ∑ j, (i.1.get j).2 * x j

open Classical in
/-- INTEGER M-DIMENSIONAL KNAPSACK, for the fixed `m`, as a decision problem over
bitstrings. -/
noncomputable def integerMDimensionalKnapsackDec (m : ℕ) :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := IntegerMDimensionalKnapsackInstance) x with
  | some i => decide (WellFormed m i ∧ IntegerMDimensionalKnapsackFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.IntegerMDimensionalKnapsack

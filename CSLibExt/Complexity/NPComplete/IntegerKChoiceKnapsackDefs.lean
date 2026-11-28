/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# INTEGER K-CHOICE KNAPSACK: definitions

Source:
P. Crescenzi and V. Kann (eds.), *A compendium of NP optimization problems*, problem
MAXIMUM INTEGER K-CHOICE KNAPSACK (decision version; "similar to [MP11]");
A. K. Chandra, D. S. Hirschberg and C. K. Wong, "Approximate algorithms for some generalized
knapsack problems", Theoret. Comput. Sci. 3 (1976), 293-304,
doi:10.1016/0304-3975(76)90048-7 (the integer multiple-choice knapsack problem);
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

namespace MetaMathlibExt.Complexity.NPComplete.IntegerKChoiceKnapsack

/-- An instance: the number `k` of columns, the rows `i = 1, …, n` (row `i` lists the pairs
`(a_{i,j}, c_{i,j})` for `j = 1, …, k`), the capacity `b`, and the bound `K`. -/
abbrev IntegerKChoiceKnapsackInstance := ℕ × List (List (ℕ × ℕ)) × ℕ × ℕ

/-- Well-formedness of an instance: every row has exactly `k` entries (so `A` and `C` are
`n × k` matrices), and `K` is positive. -/
def WellFormed (i : IntegerKChoiceKnapsackInstance) : Prop :=
  (∀ r ∈ i.2.1, r.length = i.1) ∧ 0 < i.2.2.2

/-- The pair `(a_{r,j}, c_{r,j})` of row `r` and column `j`. -/
def entry (i : IntegerKChoiceKnapsackInstance) (r : Fin i.2.1.length) (j : Fin i.1) :
    ℕ × ℕ :=
  (i.2.1.get r).getD j (0, 0)

/-- There are a choice `f(r)` of one column in each row and multiplicities `x_r` with
`∑ a_{r,f(r)} x_r ≤ b` and `∑ c_{r,f(r)} x_r ≥ K`. -/
def IntegerKChoiceKnapsackFeasible (i : IntegerKChoiceKnapsackInstance) : Prop :=
  ∃ (f : Fin i.2.1.length → Fin i.1) (x : Fin i.2.1.length → ℕ),
    ∑ r, (entry i r (f r)).1 * x r ≤ i.2.2.1 ∧
      i.2.2.2 ≤ ∑ r, (entry i r (f r)).2 * x r

open Classical in
/-- INTEGER K-CHOICE KNAPSACK as a decision problem over bitstrings. -/
noncomputable def integerKChoiceKnapsackDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := IntegerKChoiceKnapsackInstance) x with
  | some i => decide (WellFormed i ∧ IntegerKChoiceKnapsackFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.IntegerKChoiceKnapsack

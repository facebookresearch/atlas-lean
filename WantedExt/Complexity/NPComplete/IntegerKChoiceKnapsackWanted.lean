/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# INTEGER K-CHOICE KNAPSACK is NP-complete

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

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.IntegerKChoiceKnapsack

/-!
# INTEGER K-CHOICE KNAPSACK is NP-complete

INSTANCE: non-negative integer `n × k` matrices `A = (a_{i,j})` and `C = (c_{i,j})`, a
non-negative integer `b`, and a positive integer `K`.
QUESTION: is there a non-negative integer vector `x ∈ ℕⁿ` and a function
`f : [1..n] → [1..k]` such that `∑_{i=1}^{n} a_{i,f(i)} x_i ≤ b` and
`∑_{i=1}^{n} c_{i,f(i)} x_i ≥ K`?

Row `i` of the instance lists the `k` pairs `(a_{i,j}, c_{i,j})`, `j = 1, …, k`; rows and
columns are indexed from `0` in Lean. Crescenzi and Kann state the optimization problem
(maximize `∑ c_{i,f(i)} x_i`); the bound `K` is positive, as in the knapsack entries [MP10]
and [MP11] of Garey and Johnson. For `k = 1` the problem is [MP10] INTEGER KNAPSACK (items
`(a_{i,1}, c_{i,1})`, multiplicities `x_i`), which gives NP-hardness. Numbers use the binary
encoding (the problem admits a fully polynomial approximation scheme, Chandra, Hirschberg and
Wong (1976)).

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

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

/-- **INTEGER K-CHOICE KNAPSACK is NP-complete.** Source: Crescenzi and Kann, MAXIMUM INTEGER
K-CHOICE KNAPSACK; Chandra, Hirschberg and Wong (1976); Garey and Johnson (1979), [MP10] (the case
`k = 1`); Lueker (1975). -/
public theorem_wanted integerKChoiceKnapsack_npComplete :
    integerKChoiceKnapsackDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L integerKChoiceKnapsackDec

end MetaMathlibExt.Complexity.NPComplete.IntegerKChoiceKnapsack

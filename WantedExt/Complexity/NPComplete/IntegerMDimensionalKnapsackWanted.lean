/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# INTEGER M-DIMENSIONAL KNAPSACK is NP-complete

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

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.IntegerMDimensionalKnapsack

/-!
# INTEGER M-DIMENSIONAL KNAPSACK is NP-complete

Fix a positive integer `m` (a constant, not part of the instance).

INSTANCE: a non-negative integer `m × n` matrix `A = (a_{r,j})`, a non-negative integer
`m`-vector `b`, a non-negative integer `n`-vector `c`, and a positive integer `K`.
QUESTION: is there a non-negative integer `n`-vector `x` such that `A x ≤ b` (that is,
`∑_{j=1}^{n} a_{r,j} x_j ≤ b_r` for every row `r`) and `∑_{j=1}^{n} c_j x_j ≥ K`?

Column `j` of the instance is the pair of the column `(a_{1,j}, …, a_{m,j})` of `A` and the
entry `c_j`; rows and columns are indexed from `0` in Lean. Crescenzi and Kann state the
optimization problem (maximize `c · x`); the bound `K` is positive, as in [MP10] of Garey and
Johnson. For `m = 1` the problem is [MP10] INTEGER KNAPSACK, and for every `m ≥ 1` that case
embeds by adding `m - 1` zero rows with `b_r = 0`, which gives NP-hardness for each fixed `m`.
Numbers use the binary encoding (for fixed `m` the problem is solvable in pseudo-polynomial
time by dynamic programming over the vectors `b`; it admits a polynomial approximation scheme,
Chandra, Hirschberg and Wong (1976)).

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

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

/-- **INTEGER M-DIMENSIONAL KNAPSACK is NP-complete for every fixed `m ≥ 1`.** Source:
Crescenzi and Kann, MAXIMUM INTEGER M-DIMENSIONAL KNAPSACK; Chandra, Hirschberg and Wong (1976);
Garey and Johnson (1979), [MP10] (the case `m = 1`); Lueker (1975). -/
public theorem_wanted integerMDimensionalKnapsack_npComplete (m : ℕ) (_hm : 0 < m) :
    integerMDimensionalKnapsackDec m ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L (integerMDimensionalKnapsackDec m)

end MetaMathlibExt.Complexity.NPComplete.IntegerMDimensionalKnapsack

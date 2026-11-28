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
public import CSLibExt.Complexity.NPComplete.IntegerKChoiceKnapsackDefs

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

/-- **INTEGER K-CHOICE KNAPSACK is NP-complete.** Source: Crescenzi and Kann, MAXIMUM INTEGER
K-CHOICE KNAPSACK; Chandra, Hirschberg and Wong (1976); Garey and Johnson (1979), [MP10] (the case
`k = 1`); Lueker (1975). -/
public theorem_wanted integerKChoiceKnapsack_npComplete :
    integerKChoiceKnapsackDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L integerKChoiceKnapsackDec

end MetaMathlibExt.Complexity.NPComplete.IntegerKChoiceKnapsack

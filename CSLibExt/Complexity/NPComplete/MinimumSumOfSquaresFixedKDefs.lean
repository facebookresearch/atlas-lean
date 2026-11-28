/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MINIMUM SUM OF SQUARES with a fixed number K ≥ 2 of sets: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [SP19] MINIMUM SUM OF SQUARES,
p. 225 ("Reference: Transformation from PARTITION or 3-PARTITION. Comment: [...] NP-complete in
the ordinary sense and solvable in pseudo-polynomial time for any fixed K.").
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.MinimumSumOfSquaresDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MinimumSumOfSquaresFixedK

open MetaMathlibExt.Complexity.NPComplete.MinimumSumOfSquares (MinimumSumOfSquaresFeasible)

/-- An instance for a fixed `K`: the sizes `s(a)` of the elements of `A` (element `a` is the
`a`-th entry) and the bound `J`. -/
abbrev MinimumSumOfSquaresFixedKInstance := List ℕ × ℕ

/-- The [SP19] instance with `K` sets. -/
def withK (K : ℕ) (i : MinimumSumOfSquaresFixedKInstance) :
    MinimumSumOfSquares.MinimumSumOfSquaresInstance :=
  (i.1, K, i.2)

/-- Well-formedness of an instance for `K`: the [SP19] instance with `K` sets is well formed
(every size positive, `0 < K ≤ |A|`, `J` positive). -/
def WellFormed (K : ℕ) (i : MinimumSumOfSquaresFixedKInstance) : Prop :=
  MinimumSumOfSquares.WellFormed (withK K i)

/-- Some partition of `A` into `K` disjoint sets has sum of squares at most `J` (the [SP19]
question). -/
def MinimumSumOfSquaresFixedKFeasible (K : ℕ) (i : MinimumSumOfSquaresFixedKInstance) : Prop :=
  MinimumSumOfSquaresFeasible (withK K i)

open Classical in
/-- MINIMUM SUM OF SQUARES with `K` sets as a decision problem over bitstrings. -/
noncomputable def minimumSumOfSquaresFixedKDec (K : ℕ) :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := MinimumSumOfSquaresFixedKInstance) x with
  | some i => decide (WellFormed K i ∧ MinimumSumOfSquaresFixedKFeasible K i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.MinimumSumOfSquaresFixedK

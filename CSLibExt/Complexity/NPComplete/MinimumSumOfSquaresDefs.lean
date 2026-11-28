/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MINIMUM SUM OF SQUARES: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [SP19] MINIMUM SUM OF SQUARES,
p. 225 ("Reference: Transformation from PARTITION or 3-PARTITION. Comment: NP-complete in the
strong sense.").
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MinimumSumOfSquares

/-- An instance: the sizes `s(a)` of the elements of `A` (element `a` is the `a`-th entry), the
number `K` of parts and the bound `J`. -/
abbrev MinimumSumOfSquaresInstance := List ℕ × ℕ × ℕ

/-- Well-formedness of an instance: every size is positive, `0 < K ≤ |A|`, and `J` is
positive. -/
def WellFormed (i : MinimumSumOfSquaresInstance) : Prop :=
  (∀ a ∈ i.1, 0 < a) ∧ 0 < i.2.1 ∧ i.2.1 ≤ i.1.length ∧ 0 < i.2.2

/-- The sum of squares `∑_{k} (∑_{a ∈ A_k} s(a))²` of the partition of `A` into the parts
`A_k = f⁻¹(k)`. -/
def sumOfSquares (s : List ℕ) {K : ℕ} (f : Fin s.length → Fin K) : ℕ :=
  ∑ k : Fin K, (∑ a ∈ Finset.univ.filter (fun a => f a = k), s.get a) ^ 2

/-- Some partition of `A` into `K` disjoint sets has sum of squares at most `J`. -/
def MinimumSumOfSquaresFeasible (i : MinimumSumOfSquaresInstance) : Prop :=
  ∃ f : Fin i.1.length → Fin i.2.1, sumOfSquares i.1 f ≤ i.2.2

open Classical in
/-- MINIMUM SUM OF SQUARES as a decision problem over bitstrings. -/
noncomputable def minimumSumOfSquaresDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := MinimumSumOfSquaresInstance) x with
  | some i => decide (WellFormed i ∧ MinimumSumOfSquaresFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.MinimumSumOfSquares

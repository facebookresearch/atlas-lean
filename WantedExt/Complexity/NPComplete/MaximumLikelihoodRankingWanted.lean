/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MAXIMUM LIKELIHOOD RANKING is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of
NP-Completeness*, W. H. Freeman (1979), problem [MS11] MAXIMUM LIKELIHOOD RANKING, p. 281,
crediting L. Rafsky (1977, private communication) (transformation from FEEDBACK ARC SET;
NP-complete in the strong sense).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Order.Group.Int
public import Mathlib.Data.Fintype.Prod
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.Logic.Equiv.Defs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MaximumLikelihoodRanking

/-!
# MAXIMUM LIKELIHOOD RANKING is NP-complete

INSTANCE: an `n × n` matrix `A = (aᵢⱼ)` with integer entries satisfying `aᵢⱼ + aⱼᵢ = 0` for all
`i, j ∈ {1, 2, …, n}`, and a positive integer `B`.
QUESTION: is there a matrix `B' = (bᵢⱼ)` obtained from `A` by simultaneous row and column
permutations such that `∑_{1 ≤ i < j ≤ n} min {bᵢⱼ, 0} ≥ -B`?

A simultaneous row and column permutation by `π` is Mathlib's `Matrix.submatrix A π π`, with
entries `bᵢⱼ = a_{π(i) π(j)}`. Indices are `0`-based (`Fin n`).

Encoding: each entry is a pair of naturals `(positive part, negative part)` standing for their
difference, as in `ZeroOneILP`, and `A` is a list of `n` rows of length `n`. The instance is
decoded from a bitstring with the repository's canonical `MetaMathlibExt.BitstringEncoding`.
Undecodable bitstrings, and bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: `n`, the matrix `A` (rows of `(positive part, negative part)` pairs), and the
bound `B`. -/
abbrev MaximumLikelihoodRankingInstance := ℕ × List (List (ℕ × ℕ)) × ℕ

/-- The entry `aᵣ꜀` of `A`. -/
def entry (i : MaximumLikelihoodRankingInstance) (r c : Fin i.1) : ℤ :=
  (((i.2.1.getD r []).getD c (0, 0)).1 : ℤ) - (((i.2.1.getD r []).getD c (0, 0)).2 : ℤ)

/-- The matrix `A` as a Mathlib `Matrix`. -/
def matrix (i : MaximumLikelihoodRankingInstance) : Matrix (Fin i.1) (Fin i.1) ℤ :=
  Matrix.of (entry i)

/-- Well-formedness of an instance: `A` has `n` rows of length `n`, `aᵢⱼ + aⱼᵢ = 0` for all
`i, j`, and `B` is positive. -/
def WellFormed (i : MaximumLikelihoodRankingInstance) : Prop :=
  i.2.1.length = i.1 ∧ (∀ row ∈ i.2.1, row.length = i.1) ∧
    (∀ r c : Fin i.1, entry i r c + entry i c r = 0) ∧ 0 < i.2.2

/-- Some simultaneous row and column permutation `B' = A.submatrix π π` of `A` has
`∑_{i < j} min {bᵢⱼ, 0} ≥ -B`. -/
def MaximumLikelihoodRankingFeasible (i : MaximumLikelihoodRankingInstance) : Prop :=
  ∃ π : Equiv.Perm (Fin i.1),
    -(i.2.2 : ℤ) ≤ ∑ p ∈ Finset.univ.filter (fun p : Fin i.1 × Fin i.1 => p.1 < p.2),
      min ((matrix i).submatrix π π p.1 p.2) 0

open Classical in
/-- MAXIMUM LIKELIHOOD RANKING as a decision problem over bitstrings. -/
noncomputable def maximumLikelihoodRankingDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := MaximumLikelihoodRankingInstance) x with
  | some i => decide (WellFormed i ∧ MaximumLikelihoodRankingFeasible i)
  | none => false

/-- **MAXIMUM LIKELIHOOD RANKING is NP-complete.** Source: Garey and Johnson (1979), [MS11];
Rafsky (1977). -/
public theorem_wanted maximumLikelihoodRanking_npComplete :
    maximumLikelihoodRankingDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L maximumLikelihoodRankingDec

end MetaMathlibExt.Complexity.NPComplete.MaximumLikelihoodRanking

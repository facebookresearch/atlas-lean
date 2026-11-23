/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MINIMUM WEIGHT SOLUTION TO LINEAR EQUATIONS is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [MP5] MINIMUM WEIGHT
SOLUTION TO LINEAR EQUATIONS (a result of Garey and Johnson, first published
there);
E. Amaldi and V. Kann, "On the approximability of minimizing nonzero variables
or unsatisfied relations in linear systems", Theoretical Computer Science 209
(1998), 237-260, doi:10.1016/S0304-3975(97)00115-1 (records the NP-hardness of
this problem, Min RVLS with equations, citing Garey and Johnson 1979).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Order.Ring.Rat
public import Mathlib.Data.Finset.Card

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MinimumWeightSolutionToLinearEquations

/-!
# MINIMUM WEIGHT SOLUTION TO LINEAR EQUATIONS is NP-complete

INSTANCE: a finite set `X` of pairs `(x, b)`, where `x` is an `m`-tuple of integers and `b` is
an integer, and a positive integer `K ≤ m`. QUESTION: is there an `m`-tuple `y` with rational
entries such that `y` has at most `K` non-zero entries and such that `x · y = b` for all
`(x, b) ∈ X`?

Each integer is encoded as a pair of naturals `(positive part, negative part)` representing their
difference (`intOf`), as in `WantedExt.Complexity.NPComplete.ZeroOneILPWanted`; numbers use the
canonical binary encoding. `X` is a list of pairs; a repeated pair repeats an equation, which
does not change the question.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: the length `m` of the tuples, the list `X` of pairs `(x, b)` (`x` a list of `m`
encoded integers, `b` an encoded integer), and the bound `K`. -/
abbrev MinimumWeightSolutionToLinearEquationsInstance :=
  ℕ × List (List (ℕ × ℕ) × (ℕ × ℕ)) × ℕ

/-- The integer `p.1 - p.2` encoded by a pair of naturals. -/
def intOf (p : ℕ × ℕ) : ℤ := (p.1 : ℤ) - (p.2 : ℤ)

/-- Well-formedness of an instance: every `x` is an `m`-tuple, and `0 < K ≤ m`. -/
def WellFormed (i : MinimumWeightSolutionToLinearEquationsInstance) : Prop :=
  (∀ e ∈ i.2.1, e.1.length = i.1) ∧ 0 < i.2.2 ∧ i.2.2 ≤ i.1

/-- A rational `m`-tuple `y` with at most `K` non-zero entries such that `x · y = b` for every
pair `(x, b)` of `X`. -/
def MinimumWeightSolutionToLinearEquationsFeasible
    (i : MinimumWeightSolutionToLinearEquationsInstance) : Prop :=
  ∃ y : Fin i.1 → ℚ, (Finset.univ.filter fun j => y j ≠ 0).card ≤ i.2.2 ∧
    ∀ e ∈ i.2.1, ∑ j : Fin i.1, (intOf (e.1.getD j (0, 0)) : ℚ) * y j = intOf e.2

open Classical in
/-- MINIMUM WEIGHT SOLUTION TO LINEAR EQUATIONS as a decision problem over bitstrings. -/
noncomputable def minimumWeightSolutionToLinearEquationsDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := MinimumWeightSolutionToLinearEquationsInstance) x with
  | some i => decide (WellFormed i ∧ MinimumWeightSolutionToLinearEquationsFeasible i)
  | none => false

/-- **MINIMUM WEIGHT SOLUTION TO LINEAR EQUATIONS is NP-complete.** Source: Garey and Johnson
(1979), [MP5]; Amaldi and Kann (1998). -/
public theorem_wanted minimumWeightSolutionToLinearEquations_npComplete :
    minimumWeightSolutionToLinearEquationsDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L minimumWeightSolutionToLinearEquationsDec

end MetaMathlibExt.Complexity.NPComplete.MinimumWeightSolutionToLinearEquations

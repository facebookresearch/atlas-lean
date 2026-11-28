/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# INTEGER EXPRESSION MEMBERSHIP: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [AN18] INTEGER
EXPRESSION MEMBERSHIP;
L. J. Stockmeyer and A. R. Meyer, "Word problems requiring exponential time
(preliminary report)", Proceedings of the 5th Annual ACM Symposium on Theory of
Computing (STOC 1973), 1-9, doi:10.1145/800125.804029;
P. McKenzie and K. W. Wagner, "The complexity of membership problems for circuits
over sets of natural numbers", Computational Complexity 16 (2007), 211-244,
doi:10.1007/s00037-007-0229-6, Theorem 2.3(i) (`MF(∪, +)` is NP-complete).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Algebra.Group.Pointwise.Set.Basic

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.IntegerExpressionMembership

open scoped Pointwise

/-- Integer expressions over `∪` and `+`: a number, a union, or a sum. -/
inductive IntExpr where
  /-- The number `n`, representing `{n}`. -/
  | num (n : ℕ)
  /-- The union `f ∪ g`. -/
  | union (f g : IntExpr)
  /-- The sum `f + g`. -/
  | plus (f g : IntExpr)

/-- The set of natural numbers an integer expression represents. -/
def IntExpr.denote : IntExpr → Set ℕ
  | .num n => {n}
  | .union f g => f.denote ∪ g.denote
  | .plus f g => f.denote + g.denote

/-- The prefix token list of an integer expression: `(0, n)` for the number `n`, `(1, 0)` for
`∪` and `(2, 0)` for `+`, each operator followed by the tokens of its two operands. -/
def IntExpr.tokens : IntExpr → List (ℕ × ℕ)
  | .num n => [(0, n)]
  | .union f g => (1, 0) :: (f.tokens ++ g.tokens)
  | .plus f g => (2, 0) :: (f.tokens ++ g.tokens)

/-- An instance: the prefix token list of the expression `e`, and the target `K`. -/
abbrev IntegerExpressionMembershipInstance := List (ℕ × ℕ) × ℕ

/-- Well-formedness of an instance: the token list is the prefix token list of an integer
expression, every number token `(0, n)` carries a positive integer `n`, and `0 < K`. -/
def WellFormed (i : IntegerExpressionMembershipInstance) : Prop :=
  (∃ e : IntExpr, e.tokens = i.1) ∧ (∀ t ∈ i.1, t.1 = 0 → 0 < t.2) ∧ 0 < i.2

/-- `K` lies in the set represented by the expression whose prefix token list is given. -/
def IntegerExpressionMembershipFeasible (i : IntegerExpressionMembershipInstance) : Prop :=
  ∃ e : IntExpr, e.tokens = i.1 ∧ i.2 ∈ e.denote

open Classical in
/-- INTEGER EXPRESSION MEMBERSHIP as a decision problem over bitstrings. -/
noncomputable def integerExpressionMembershipDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := IntegerExpressionMembershipInstance) x with
  | some i => decide (WellFormed i ∧ IntegerExpressionMembershipFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.IntegerExpressionMembership

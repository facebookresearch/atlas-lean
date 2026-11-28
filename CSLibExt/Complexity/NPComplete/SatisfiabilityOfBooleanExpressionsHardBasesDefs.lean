/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# SATISFIABILITY OF BOOLEAN EXPRESSIONS over a fixed set of connectives that expresses `x ∧ ¬y`: definitions
is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [LO7] SATISFIABILITY OF BOOLEAN
EXPRESSIONS, comment (pp. 260-261): "Remains NP-complete if `B` is restricted to `{∧, ∨, →, ¬}`,
or any other truth-functionally complete set of connectives. Also NP-complete for any
truth-functionally incomplete set of connectives containing `{↛}`, `{↚}`, `{≢, ∨}`, or `{≢, ∧}`
as a subset [Lewis, 1978]. Problem is solvable in polynomial time for any truth-functionally
incomplete set of connectives *not* containing one of these four sets as a subset.";
H. R. Lewis, "Satisfiability problems for propositional calculi", Mathematical Systems Theory 13
(1979), 45-53, doi:10.1007/BF01744287.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.SatisfiabilityOfBooleanExpressionsDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.SatisfiabilityOfBooleanExpressionsHardBases

open SatisfiabilityOfBooleanExpressions (BoolExpr parse SatisfiabilityOfBooleanExpressionsInstance
  SatisfiabilityOfBooleanExpressionsFeasible)

/-- `B` expresses `x ∧ ¬y`: some well-formed expression over the variables `u₀, u₁` and the
connectives of `B` is true under a truth assignment exactly when `u₀` is true and `u₁` is
false. -/
def ExpressesAndNot (B : List ℕ) : Prop :=
  ∃ toks : List (ℕ × ℕ), SatisfiabilityOfBooleanExpressions.WellFormed (2, B, toks) ∧
    ∃ E : BoolExpr, parse toks = some E ∧ ∀ σ : ℕ → Bool, E.eval σ = (σ 0 && !σ 1)

/-- Well-formedness of an instance for the fixed set `B`: a well-formed SATISFIABILITY OF
BOOLEAN EXPRESSIONS instance whose connectives are drawn from `B`. -/
def WellFormed (B : List ℕ) (i : SatisfiabilityOfBooleanExpressionsInstance) : Prop :=
  SatisfiabilityOfBooleanExpressions.WellFormed i ∧ ∀ c ∈ i.2.1, c ∈ B

open Classical in
/-- SATISFIABILITY OF BOOLEAN EXPRESSIONS over the fixed set `B` of connectives as a decision
problem over bitstrings. -/
noncomputable def satisfiabilityOfBooleanExpressionsHardBasesDec (B : List ℕ) :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := SatisfiabilityOfBooleanExpressionsInstance) x with
  | some i => decide (WellFormed B i ∧ SatisfiabilityOfBooleanExpressionsFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.SatisfiabilityOfBooleanExpressionsHardBases

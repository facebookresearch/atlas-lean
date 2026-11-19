/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# SATISFIABILITY OF BOOLEAN EXPRESSIONS over a fixed set of connectives that expresses `x ∧ ¬y`
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

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.SatisfiabilityOfBooleanExpressionsWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.SatisfiabilityOfBooleanExpressionsHardBases

open SatisfiabilityOfBooleanExpressions (BoolExpr parse SatisfiabilityOfBooleanExpressionsInstance
  SatisfiabilityOfBooleanExpressionsFeasible)

/-!
# SATISFIABILITY OF BOOLEAN EXPRESSIONS over a fixed set of connectives that expresses `x ∧ ¬y`
is NP-complete

For a fixed set `B` of binary Boolean connectives that can express `x ∧ ¬y`:
INSTANCE: a variable set `U` and a well-formed Boolean expression `E` over `U` and `B`.
QUESTION: is there a truth assignment for `U` that satisfies `E`?

This is [LO7] SATISFIABILITY OF BOOLEAN EXPRESSIONS
(`WantedExt.Complexity.NPComplete.SatisfiabilityOfBooleanExpressionsWanted`) with `B` fixed, in
the hard case of the [LO7] comment. The parent's connective codes (`c < 16`, value at `(p, q)`
bit `2p + q` of `c`), expressions, postfix reader `parse`, `WellFormed` and
`SatisfiabilityOfBooleanExpressionsFeasible` are reused unchanged; for a fixed `B` the instance's
own connective list must be drawn from `B`.

`ExpressesAndNot B` says that some well-formed expression over the variables `u₀, u₁` and the
connectives of `B` computes `u₀ ∧ ¬u₁`. This is Lewis's criterion: satisfiability of
`B`-expressions is NP-complete when `x ∧ ¬y` is expressible from `B`, and polynomial otherwise.
For sets of binary connectives it is GJ's condition: a truth-functionally complete set expresses
every function; `{↛}` is `x ∧ ¬y` itself (code `4`), `{↚}` gives it with the arguments swapped,
`{≢, ∨}` as `(u₀ ∨ u₁) ≢ u₁` and `{≢, ∧}` as `u₀ ∧ (u₀ ≢ u₁)`. Conversely, by Post's
classification an incomplete set lies in one of the five maximal clones, and `x ∧ ¬y` lies only
in the 0-preserving one; the 0-preserving binary connectives are `0, ∧, ↛, ↚, ≢, ∨` and the two
projections, and among them `x ∧ ¬y` is expressible exactly from sets containing `↛`, `↚`, or
`≢` together with `∨` or `∧`: once `↛` and `↚` are excluded, a set without `≢` has only
monotone connectives and a set without `∨` and `∧` only affine ones, and `x ∧ ¬y` is neither.
One `theorem_wanted` covers every such `B`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

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

/-- **SATISFIABILITY OF BOOLEAN EXPRESSIONS over any fixed set of binary connectives that
expresses `x ∧ ¬y` is NP-complete.** Source: Garey and Johnson (1979), [LO7], comment; Lewis
(1979). -/
public theorem_wanted satisfiabilityOfBooleanExpressionsHardBases_npComplete (B : List ℕ)
    (_hB : ExpressesAndNot B) :
    satisfiabilityOfBooleanExpressionsHardBasesDec B ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L (satisfiabilityOfBooleanExpressionsHardBasesDec B)

end MetaMathlibExt.Complexity.NPComplete.SatisfiabilityOfBooleanExpressionsHardBases

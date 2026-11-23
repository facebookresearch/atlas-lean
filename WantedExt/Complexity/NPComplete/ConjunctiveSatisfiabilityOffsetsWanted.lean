/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# CONJUNCTIVE SATISFIABILITY WITH OFFSETS is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of
NP-Completeness*, W. H. Freeman (1979), problem [LO16] CONJUNCTIVE SATISFIABILITY WITH FUNCTIONS
AND INEQUALITIES, comment (the variant with terms `u` and `u + c`, attributed to [Chan, 1977]);
T.-H. Chan, "An algorithm for checking PL/CV arithmetic inferences", Technical Report 77-326,
Department of Computer Science, Cornell University (1977), Section 4, Theorems 2 and 4,
hdl:1813/7447.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ConjunctiveSatisfiabilityOffsets

/-!
# CONJUNCTIVE SATISFIABILITY WITH OFFSETS is NP-complete

The variant of CONJUNCTIVE SATISFIABILITY WITH FUNCTIONS AND INEQUALITIES ([LO16],
`ConjunctiveSatisfiabilityFunctionsInequalitiesWanted`) "in which `W` and `V` are either of the
form `u` or `u + c` for some `u ∈ U` and `c ∈ ℤ`", with all four relations allowed.

INSTANCE: a set `U` of variables and a collection `C` of "clauses" of the form `W * V`, where `*`
is one of `≤`, `>`, `=`, `≠`, and each of `W` and `V` is of the form `u` or `u + c` for some
`u ∈ U` and `c ∈ ℤ`.
QUESTION: is there an assignment of integer values to the variables `u ∈ U` such that all the
clauses in `C` are satisfied under the usual interpretations of `≤`, `>`, `=` and `≠`?

The variables are `0, …, n - 1`. A term `(u, (p, q))` is `u + (p - q)`, so the term `u` is
`(u, (0, 0))` and `u + c` is `(u, (p, q))` with `p - q = c`. A clause `(W, r, V)` is `W ≤ V`,
`W > V`, `W = V` or `W ≠ V` for `r = 0, 1, 2, 3`. Garey and Johnson note that the problem is
solvable in polynomial time when only `≤` and `>`, or only `=` and `≠`, are allowed [Chan, 1977].
Chan's Theorems 2 and 4 show that satisfiability of such relations (which he writes as a weighted
digraph of relations `x ≥ y + c` with the `≠`-relations kept as constraints) is NP-complete.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- A term `(u, (p, q))`: the variable `u` plus the integer offset `p - q`. -/
abbrev OffsetTerm := ℕ × ℕ × ℕ

/-- A clause `(W, r, V)`: the terms `W` and `V` related by `≤`, `>`, `=`, `≠` for
`r = 0, 1, 2, 3`. -/
abbrev OffsetClause := OffsetTerm × ℕ × OffsetTerm

/-- An instance: the number `n` of variables and the clauses. -/
abbrev ConjunctiveSatisfiabilityOffsetsInstance := ℕ × List OffsetClause

/-- The value of a term `u + c` under the integer assignment `σ`. -/
def termValue (σ : ℕ → ℤ) (t : OffsetTerm) : ℤ :=
  σ t.1 + ((t.2.1 : ℤ) - t.2.2)

/-- The clause `W * V` holds under the integer assignment `σ`. -/
def ClauseHolds (σ : ℕ → ℤ) (c : OffsetClause) : Prop :=
  match c.2.1 with
  | 0 => termValue σ c.1 ≤ termValue σ c.2.2
  | 1 => termValue σ c.2.2 < termValue σ c.1
  | 2 => termValue σ c.1 = termValue σ c.2.2
  | _ => termValue σ c.1 ≠ termValue σ c.2.2

/-- Well-formedness of an instance: every clause relates two terms on variables `< n` by one of
the relations `0` to `3`. -/
def WellFormed (i : ConjunctiveSatisfiabilityOffsetsInstance) : Prop :=
  ∀ c ∈ i.2, c.1.1 < i.1 ∧ c.2.1 ≤ 3 ∧ c.2.2.1 < i.1

/-- Some assignment of integer values to the variables satisfies every clause. -/
def ConjunctiveSatisfiabilityOffsetsFeasible (i : ConjunctiveSatisfiabilityOffsetsInstance) :
    Prop :=
  ∃ σ : ℕ → ℤ, ∀ c ∈ i.2, ClauseHolds σ c

open Classical in
/-- CONJUNCTIVE SATISFIABILITY WITH OFFSETS as a decision problem over bitstrings. -/
noncomputable def conjunctiveSatisfiabilityOffsetsDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := ConjunctiveSatisfiabilityOffsetsInstance) x with
  | some i => decide (WellFormed i ∧ ConjunctiveSatisfiabilityOffsetsFeasible i)
  | none => false

/-- **CONJUNCTIVE SATISFIABILITY WITH OFFSETS is NP-complete.** Source: Garey and Johnson (1979),
[LO16]; Chan (1977), Theorems 2 and 4. -/
public theorem_wanted conjunctiveSatisfiabilityOffsets_npComplete :
    conjunctiveSatisfiabilityOffsetsDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L conjunctiveSatisfiabilityOffsetsDec

end MetaMathlibExt.Complexity.NPComplete.ConjunctiveSatisfiabilityOffsets

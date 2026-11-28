/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# ALLEN INTERVAL ALGEBRA SATISFIABILITY is NP-complete

Source:
M. Vilain and H. Kautz, "Constraint propagation algorithms for temporal reasoning",
Proceedings of the Fifth National Conference on Artificial Intelligence (AAAI-86), 1986,
377-382, Theorem 2 ("Determining the satisfiability of a set of assertions in the interval
algebra is NP-hard", by a reduction from 3SAT); revised version: M. Vilain, H. Kautz and
P. van Beek, "Constraint propagation algorithms for temporal reasoning: a revised report", in
*Readings in Qualitative Reasoning about Physical Systems*, Morgan Kaufmann (1990), 373-381,
doi:10.1016/B978-1-4832-1447-4.50034-1. The interval algebra is that of J. F. Allen,
"Maintaining knowledge about temporal intervals", Communications of the ACM 26(11) (1983),
832-843, doi:10.1145/182.358434.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Basic.Real.Basic

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.AllenIntervalAlgebraSatisfiability

/-!
# ALLEN INTERVAL ALGEBRA SATISFIABILITY is NP-complete

INSTANCE: interval variables `I₀, …, I_{n-1}` and a finite set of assertions `Iᵢ (R) Iⱼ`, where
each `R` is a set of Allen's thirteen simple relations, read as their disjunction.
QUESTION: is there an assignment of a real interval `[sᵢ, eᵢ]` with `sᵢ < eᵢ` to every variable
such that, for every assertion `Iᵢ (R) Iⱼ`, the intervals `Iᵢ` and `Iⱼ` stand in one of the
simple relations of `R`?

The thirteen simple relations (`simpleRel`, codes `0, …, 12`) compare the endpoints of `Iᵢ` and
`Iⱼ`, as in Allen (1983): before, after, meets, met-by, overlaps, overlapped-by, starts,
started-by, during, contains, finishes, finished-by, and equals. For intervals of positive
length exactly one of them holds. An assertion is a triple `(i, j, R)` with `R` a list of codes;
the empty list is the empty disjunction, which no assignment satisfies. Several assertions may
concern the same pair; they all have to hold. The problem is in NP: a variable that occurs in no
assertion can take any interval of positive length, and for the at most `2m` variables occurring
in the `m` assertions only the relative order of their endpoints matters, so a certificate
assigns them endpoints in `{0, …, 4m - 1}`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: the number `n` of interval variables and the assertions `(i, j, R)`, where `R`
lists the codes of the simple relations allowed between `Iᵢ` and `Iⱼ`. -/
abbrev AllenIntervalAlgebraSatisfiabilityInstance := ℕ × List (ℕ × ℕ × List ℕ)

/-- Allen's simple relation with code `r` between the intervals `[a.1, a.2]` and `[b.1, b.2]`:
`0` before, `1` after, `2` meets, `3` met-by, `4` overlaps, `5` overlapped-by, `6` starts,
`7` started-by, `8` during, `9` contains, `10` finishes, `11` finished-by, `12` equals. Other
codes name no relation. -/
def simpleRel (r : ℕ) (a b : ℝ × ℝ) : Prop :=
  match r with
  | 0 => a.2 < b.1
  | 1 => b.2 < a.1
  | 2 => a.2 = b.1
  | 3 => b.2 = a.1
  | 4 => a.1 < b.1 ∧ b.1 < a.2 ∧ a.2 < b.2
  | 5 => b.1 < a.1 ∧ a.1 < b.2 ∧ b.2 < a.2
  | 6 => a.1 = b.1 ∧ a.2 < b.2
  | 7 => a.1 = b.1 ∧ b.2 < a.2
  | 8 => b.1 < a.1 ∧ a.2 < b.2
  | 9 => a.1 < b.1 ∧ b.2 < a.2
  | 10 => a.2 = b.2 ∧ b.1 < a.1
  | 11 => a.2 = b.2 ∧ a.1 < b.1
  | 12 => a.1 = b.1 ∧ a.2 = b.2
  | _ => False

/-- Well-formedness of an instance: every assertion names two of the `n` variables, and every
relation code is one of the thirteen simple relations. -/
def WellFormed (i : AllenIntervalAlgebraSatisfiabilityInstance) : Prop :=
  ∀ c ∈ i.2, c.1 < i.1 ∧ c.2.1 < i.1 ∧ ∀ r ∈ c.2.2, r < 13

/-- Some assignment of real intervals `I k = [(I k).1, (I k).2]` of positive length satisfies
every assertion: for `(i, j, R)`, some simple relation of `R` holds between `I i` and `I j`.
Assignments are functions on `ℕ`; under `WellFormed` only their values on `0, …, n - 1`
matter. -/
def AllenIntervalAlgebraSatisfiabilityFeasible
    (i : AllenIntervalAlgebraSatisfiabilityInstance) : Prop :=
  ∃ I : ℕ → ℝ × ℝ, (∀ k < i.1, (I k).1 < (I k).2) ∧
    ∀ c ∈ i.2, ∃ r ∈ c.2.2, simpleRel r (I c.1) (I c.2.1)

open Classical in
/-- ALLEN INTERVAL ALGEBRA SATISFIABILITY as a decision problem over bitstrings. -/
noncomputable def allenIntervalAlgebraSatisfiabilityDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := AllenIntervalAlgebraSatisfiabilityInstance) x with
  | some i => decide (WellFormed i ∧ AllenIntervalAlgebraSatisfiabilityFeasible i)
  | none => false

/-- **ALLEN INTERVAL ALGEBRA SATISFIABILITY is NP-complete.** NP-hardness: Vilain and Kautz
(1986), Theorem 2; membership in NP: the endpoint-order certificate of the module docstring. -/
public theorem_wanted allenIntervalAlgebraSatisfiability_npComplete :
    allenIntervalAlgebraSatisfiabilityDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L allenIntervalAlgebraSatisfiabilityDec

end MetaMathlibExt.Complexity.NPComplete.AllenIntervalAlgebraSatisfiability

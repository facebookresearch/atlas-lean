/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MINIMUM DISJUNCTIVE NORMAL FORM is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [LO9] MINIMUM
DISJUNCTIVE NORMAL FORM;
J. F. Gimpel, "A method of producing a Boolean function having an arbitrarily
prescribed prime implicant table", IEEE Transactions on Electronic Computers
EC-14 (1965), 485-488, doi:10.1109/PGEC.1965.264175;
E. Allender, L. Hellerstein, P. McCabe, T. Pitassi, and M. Saks, "Minimizing
disjunctive normal form formulas and AC⁰ circuits given a truth table", SIAM
Journal on Computing 38 (2008), 63-84, doi:10.1137/060664537.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Logics.Propositional.CNF.Semantics

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MinimumDisjunctiveNormalForm

/-!
# MINIMUM DISJUNCTIVE NORMAL FORM is NP-complete

INSTANCE: a set `U = {u₁, …, uₙ}` of variables, a set `A ⊆ {T, F}ⁿ` of truth assignments, and
a positive integer `K`. QUESTION: is there a disjunctive normal form expression `E` over `U`,
having no more than `K` disjuncts, which is true for precisely those truth assignments in `A`,
and no others?

Variables are `u₀, …, u_{n-1}`; a truth assignment is a list of `n` Booleans, and `A` is given
explicitly as a list of such lists (Allender et al. call this the `A` version, `Min-DNF(A)`). A
disjunct is a list of literals `(x, b)`, true when every literal holds; a literal holds under an
assignment `a` when `a.getD x false = b`, which is CSLibExt's
`Cslib.Logic.PL.CNFLiteral.Satisfies`. A DNF expression is a list of disjuncts, true when some
disjunct is true.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: the number `n` of variables, the list of truth assignments `A`, and the bound
`K`. -/
abbrev MinimumDisjunctiveNormalFormInstance := ℕ × List (List Bool) × ℕ

/-- A DNF expression is true under the assignment `σ` when some disjunct has all of its
literals satisfied. -/
def DNFTrue (σ : ℕ → Bool) (E : List (List (ℕ × Bool))) : Prop :=
  ∃ t ∈ E, ∀ l ∈ t, Cslib.Logic.PL.CNFLiteral.Satisfies σ l

/-- Well-formedness of an instance: every listed truth assignment has length `n`, and `K` is
positive. -/
def WellFormed (i : MinimumDisjunctiveNormalFormInstance) : Prop :=
  (∀ a ∈ i.2.1, a.length = i.1) ∧ 0 < i.2.2

/-- Some DNF expression over `u₀, …, u_{n-1}` with at most `K` disjuncts is true on exactly the
assignments in `A`. -/
def MinimumDisjunctiveNormalFormFeasible (i : MinimumDisjunctiveNormalFormInstance) : Prop :=
  ∃ E : List (List (ℕ × Bool)), E.length ≤ i.2.2 ∧ (∀ t ∈ E, ∀ l ∈ t, l.1 < i.1) ∧
    ∀ a : List Bool, a.length = i.1 → (DNFTrue (fun x => a.getD x false) E ↔ a ∈ i.2.1)

open Classical in
/-- MINIMUM DISJUNCTIVE NORMAL FORM as a decision problem over bitstrings. -/
noncomputable def minimumDisjunctiveNormalFormDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := MinimumDisjunctiveNormalFormInstance) x with
  | some i => decide (WellFormed i ∧ MinimumDisjunctiveNormalFormFeasible i)
  | none => false

/-- **MINIMUM DISJUNCTIVE NORMAL FORM is NP-complete.** Source: Garey and Johnson (1979),
[LO9]; Gimpel (1965); Allender, Hellerstein, McCabe, Pitassi, and Saks (2008). -/
public theorem_wanted minimumDisjunctiveNormalForm_npComplete :
    minimumDisjunctiveNormalFormDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L minimumDisjunctiveNormalFormDec

end MetaMathlibExt.Complexity.NPComplete.MinimumDisjunctiveNormalForm

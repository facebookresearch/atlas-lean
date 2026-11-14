/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# UNIFICATION WITH COMMUTATIVE OPERATORS is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [AN16] UNIFICATION
WITH COMMUTATIVE OPERATORS (credited there to R. Sethi, private communication,
1977);
F. Baader and W. Snyder, "Unification theory", in *Handbook of Automated
Reasoning*, vol. I, Elsevier (2001), 445-533,
doi:10.1016/B978-044450813-3/50010-2, Section 3.4 (commutativity `C_f`:
unification with constants is NP-complete; the hardness result is the one in
Garey and Johnson, attributed to Sethi).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Foundations.Unification.Basic

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.UnificationWithCommutativeOperators

open Cslib.Unification

/-!
# UNIFICATION WITH COMMUTATIVE OPERATORS is NP-complete

INSTANCE: a set `V` of variables, a set `C` of constants, and ordered pairs `(eᵢ, fᵢ)`,
`1 ≤ i ≤ n`, of expressions, where an expression is either a variable from `V`, a constant
from `C`, or `(e + f)` where `e` and `f` are expressions. QUESTION: is there an assignment to
each `v ∈ V` of a variable-free expression `I(v)` such that, if `I(e)` denotes the expression
obtained by replacing each occurrence of each variable `v` in `e` by `I(v)`, then
`I(eᵢ) ≡ I(fᵢ)` for `1 ≤ i ≤ n`, where `e ≡ f` if and only
if `e = f`, or `e = (a + b)`, `f = (c + d)` and either `a ≡ c` and `b ≡ d`, or `a ≡ d` and
`b ≡ c`?

Expressions are the binary terms `Cslib.Unification.Term (Fin |C|)` (`var`, `const`, and
`node l r` for `(l + r)`), with variables `0, ..., |V| - 1` and constants `Fin |C|`; `I(e)` is
`Term.subst`, and "variable-free" is `Term.vars = ∅`. The equivalence `≡` is `CommEquiv`, the
least relation closed under the three clauses of the source's recursive definition (which is
well founded on the size of the expressions, so it has exactly one solution).

Each expression is given by its prefix (Polish) token list `tokens`, which determines the term
uniquely: `(0, v)` is the variable `v`, `(1, c)` the constant `c`, and `(2, 0)` is `+`, followed by
the tokens of its two operands.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- Equality modulo commutativity of `+` (`Term.node`): `e ≡ f` if `e = f`, or
`e = (a + b)`, `f = (c + d)` and either `a ≡ c` and `b ≡ d`, or `a ≡ d` and `b ≡ c`. -/
inductive CommEquiv {C : Type} : Term C → Term C → Prop where
  /-- `e ≡ e`. -/
  | refl (e : Term C) : CommEquiv e e
  /-- `(a + b) ≡ (c + d)` when `a ≡ c` and `b ≡ d`. -/
  | node {a b c d : Term C} : CommEquiv a c → CommEquiv b d →
      CommEquiv (.node a b) (.node c d)
  /-- `(a + b) ≡ (c + d)` when `a ≡ d` and `b ≡ c`. -/
  | swap {a b c d : Term C} : CommEquiv a d → CommEquiv b c →
      CommEquiv (.node a b) (.node c d)

/-- The prefix token list of an expression: `(0, v)` for the variable `v`, `(1, c)` for the
constant `c`, and `(2, 0)` for `+` followed by the tokens of its two operands. -/
def tokens {k : ℕ} : Term (Fin k) → List (ℕ × ℕ)
  | .var v => [(0, v)]
  | .const c => [(1, c.val)]
  | .node l r => (2, 0) :: (tokens l ++ tokens r)

/-- An instance: the number of variables `|V|` (variables `0, ..., |V| - 1`), the number of
constants `|C|` (constants `Fin |C|`), and the pairs `(eᵢ, fᵢ)` as prefix token lists. -/
abbrev UnificationWithCommutativeOperatorsInstance :=
  ℕ × ℕ × List (List (ℕ × ℕ) × List (ℕ × ℕ))

/-- The pairs of expressions whose token lists are those of the instance. -/
def Pairs (i : UnificationWithCommutativeOperatorsInstance)
    (es : List (Term (Fin i.2.1) × Term (Fin i.2.1))) : Prop :=
  es.map (fun p => (tokens p.1, tokens p.2)) = i.2.2

/-- Well-formedness of an instance: the token lists are those of expressions over the
constants `Fin |C|`, and every variable token `(0, v)` names a variable `v < |V|`. -/
def WellFormed (i : UnificationWithCommutativeOperatorsInstance) : Prop :=
  (∃ es, Pairs i es) ∧ ∀ p ∈ i.2.2, ∀ t ∈ p.1 ++ p.2, t.1 = 0 → t.2 < i.1

/-- Some assignment `I` of a variable-free expression to each variable `v < |V|` makes
`I(eᵢ) ≡ I(fᵢ)` for every pair. -/
def UnificationWithCommutativeOperatorsFeasible
    (i : UnificationWithCommutativeOperatorsInstance) : Prop :=
  ∃ es, Pairs i es ∧ ∃ I : Subst (Fin i.2.1), (∀ v < i.1, (I v).vars = ∅) ∧
    ∀ p ∈ es, CommEquiv (p.1.subst I) (p.2.subst I)

open Classical in
/-- UNIFICATION WITH COMMUTATIVE OPERATORS as a decision problem over bitstrings. -/
noncomputable def unificationWithCommutativeOperatorsDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := UnificationWithCommutativeOperatorsInstance) x with
  | some i => decide (WellFormed i ∧ UnificationWithCommutativeOperatorsFeasible i)
  | none => false

/-- **UNIFICATION WITH COMMUTATIVE OPERATORS is NP-complete.** Source: Garey and Johnson (1979),
[AN16] (Sethi, private communication); Baader and Snyder (2001), Section 3.4. -/
public theorem_wanted unificationWithCommutativeOperators_npComplete :
    unificationWithCommutativeOperatorsDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L unificationWithCommutativeOperatorsDec

end MetaMathlibExt.Complexity.NPComplete.UnificationWithCommutativeOperators

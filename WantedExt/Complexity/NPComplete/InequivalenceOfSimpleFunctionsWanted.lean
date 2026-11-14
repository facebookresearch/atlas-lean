/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# INEQUIVALENCE OF SIMPLE FUNCTIONS is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [PO15] INEQUIVALENCE OF
SIMPLE FUNCTIONS, p. 276 (reference [Tsichritzis, 1970]; transformation from INEQUIVALENCE
OF LOOP PROGRAMS WITHOUT NESTING);
D. Tsichritzis, "The equivalence problem of simple programs", Journal of the ACM 17 (1970),
729-738, doi:10.1145/321607.321621 (the simple functions are the functions of the loop
programs without nesting, `L₁`);
R. L. Constable, H. B. Hunt III and S. Sahni, "On the computational complexity of program
scheme equivalence", SIAM Journal on Computing 9 (1980), 396-416, doi:10.1137/0209031 (the
equivalence problem for `L₁` programs is NP-complete).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.InequivalenceOfSimpleFunctions

/-!
# INEQUIVALENCE OF SIMPLE FUNCTIONS is NP-complete

INSTANCE: a finite set `X` of variables, and two expressions `f` and `g` over `X`, each a
composition of functions from the collection `s(x) = x + 1`, `p(x) = max {x - 1, 0}`,
`plus(x, y) = x + y`, `div(x, t) = ⌊x / t⌋`, `mod(x, t) = x - t · ⌊x / t⌋`,
`w(x, y) = if y = 0 then x else 0`, and `selectᵢⁿ(x₁, x₂, …, xₙ) = xᵢ`, where the leaves
`x, y, xᵢ` are variables of `X` and `i, n, t` are positive integers with `i ≤ n`.
QUESTION: is there an assignment of non-negative integer values to the variables in `X` for
which the values of `f` and `g` differ?

The variables are `x₀, …, x_{|X|-1}`. Expressions are the trees `SimpleExpr` (no sharing of
subexpressions), evaluated by `SimpleExpr.eval`; `p` is truncated subtraction on `ℕ`, and
`div` and `mod` are `ℕ`'s `/` and `%`. A bare variable is also an expression; this adds no
functions, since `x = select₁¹(x)`. The instance gives each expression as its prefix (Polish)
token list `SimpleExpr.tokens`: `(0, k, 0)` is the variable `xₖ`, `(1, 0, 0)` is `s`,
`(2, 0, 0)` is `p`, `(3, 0, 0)` is `plus`, `(4, t, 0)` is `div(·, t)`, `(5, t, 0)` is
`mod(·, t)`, `(6, 0, 0)` is `w`, and `(7, i, n)` is `selectᵢⁿ`, each operator followed by the
tokens of its operands in order. Every token fixes its operator's arity, so a token list
determines its tree.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- Expressions over the simple functions, with variables `xₖ` at the leaves. -/
inductive SimpleExpr where
  /-- The variable `xₖ`. -/
  | var (k : ℕ)
  /-- `s(e) = e + 1`. -/
  | succ (e : SimpleExpr)
  /-- `p(e) = max {e - 1, 0}`. -/
  | pred (e : SimpleExpr)
  /-- `plus(e, e') = e + e'`. -/
  | plus (e e' : SimpleExpr)
  /-- `div(e, t) = ⌊e / t⌋`. -/
  | div (e : SimpleExpr) (t : ℕ)
  /-- `mod(e, t) = e - t · ⌊e / t⌋`. -/
  | mod (e : SimpleExpr) (t : ℕ)
  /-- `w(e, e') = if e' = 0 then e else 0`. -/
  | w (e e' : SimpleExpr)
  /-- `selectᵢⁿ(e₁, …, eₙ) = eᵢ`, with `n` the length of the argument list. -/
  | select (i : ℕ) (es : List SimpleExpr)

/-- The value of an expression under the assignment `a` of non-negative integers to the
variables (`a k` is the value of `xₖ`). -/
def SimpleExpr.eval (a : ℕ → ℕ) : SimpleExpr → ℕ
  | .var k => a k
  | .succ e => e.eval a + 1
  | .pred e => e.eval a - 1
  | .plus e e' => e.eval a + e'.eval a
  | .div e t => e.eval a / t
  | .mod e t => e.eval a % t
  | .w e e' => if e'.eval a = 0 then e.eval a else 0
  | .select i es => (es.map fun e => e.eval a).getD (i - 1) 0

/-- The prefix token list of an expression (see the module docstring). -/
def SimpleExpr.tokens : SimpleExpr → List (ℕ × ℕ × ℕ)
  | .var k => [(0, k, 0)]
  | .succ e => (1, 0, 0) :: e.tokens
  | .pred e => (2, 0, 0) :: e.tokens
  | .plus e e' => (3, 0, 0) :: (e.tokens ++ e'.tokens)
  | .div e t => (4, t, 0) :: e.tokens
  | .mod e t => (5, t, 0) :: e.tokens
  | .w e e' => (6, 0, 0) :: (e.tokens ++ e'.tokens)
  | .select i es => (7, i, es.length) :: (es.map fun e => e.tokens).flatten

/-- An instance: the number `|X|` of variables, and the prefix token lists of `f` and `g`. -/
abbrev InequivalenceOfSimpleFunctionsInstance :=
  ℕ × List (ℕ × ℕ × ℕ) × List (ℕ × ℕ × ℕ)

/-- A token list is the prefix token list of an expression over the variables
`x₀, …, x_{nX-1}` whose `div` and `mod` divisors `t` are positive and whose selectors
`selectᵢᵐ` have `1 ≤ i ≤ m`. -/
def IsExpr (nX : ℕ) (ts : List (ℕ × ℕ × ℕ)) : Prop :=
  (∃ e : SimpleExpr, e.tokens = ts) ∧
    ∀ t ∈ ts, (t.1 = 0 → t.2.1 < nX) ∧ (t.1 = 4 ∨ t.1 = 5 → 0 < t.2.1) ∧
      (t.1 = 7 → 1 ≤ t.2.1 ∧ t.2.1 ≤ t.2.2)

/-- Well-formedness of an instance: both token lists are expressions over `X` (`IsExpr`). -/
def WellFormed (i : InequivalenceOfSimpleFunctionsInstance) : Prop :=
  IsExpr i.1 i.2.1 ∧ IsExpr i.1 i.2.2

/-- Some assignment of non-negative integers to the variables gives `f` and `g` different
values. -/
def InequivalenceOfSimpleFunctionsFeasible (i : InequivalenceOfSimpleFunctionsInstance) :
    Prop :=
  ∃ f g : SimpleExpr, f.tokens = i.2.1 ∧ g.tokens = i.2.2 ∧
    ∃ a : ℕ → ℕ, f.eval a ≠ g.eval a

open Classical in
/-- INEQUIVALENCE OF SIMPLE FUNCTIONS as a decision problem over bitstrings. -/
noncomputable def inequivalenceOfSimpleFunctionsDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := InequivalenceOfSimpleFunctionsInstance) x with
  | some i => decide (WellFormed i ∧ InequivalenceOfSimpleFunctionsFeasible i)
  | none => false

/-- **INEQUIVALENCE OF SIMPLE FUNCTIONS is NP-complete.** Source: Garey and Johnson (1979),
[PO15]; Tsichritzis (1970); Constable, Hunt and Sahni (1980). -/
public theorem_wanted inequivalenceOfSimpleFunctions_npComplete :
    inequivalenceOfSimpleFunctionsDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L inequivalenceOfSimpleFunctionsDec

end MetaMathlibExt.Complexity.NPComplete.InequivalenceOfSimpleFunctions

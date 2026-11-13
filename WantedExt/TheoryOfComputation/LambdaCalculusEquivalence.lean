/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Computability.RE

@[expose] public section

set_option autoImplicit false

namespace Cslib.LambdaCalculusEquivalenceWanted

/-!
# Untyped lambda calculus

Untyped lambda terms with de Bruijn indices, one-step beta reduction, and
Church numerals/booleans. A predicate is lambda-decidable when some term
reduces, on Church numeral input, to the Church boolean of its truth value.
-/

/-- Untyped lambda terms, with de Bruijn indices.
Source: Barendregt, *The Lambda Calculus: Its Syntax and Semantics*,
North-Holland, 1984, §2.1. -/
inductive ULTerm where
  | var : ℕ → ULTerm
  | app : ULTerm → ULTerm → ULTerm
  | lam : ULTerm → ULTerm

/-- Lift free variables at or above `c` by one.
Source: Barendregt, *The Lambda Calculus: Its Syntax and Semantics*,
North-Holland, 1984, §2.1. -/
def ULShift (c : ℕ) : ULTerm → ULTerm
  | .var k => if k < c then .var k else .var (k + 1)
  | .app t u => .app (ULShift c t) (ULShift c u)
  | .lam t => .lam (ULShift (c + 1) t)

/-- Lower free variables strictly above `c` by one (the inverse of
`ULShift` on variables above the cutoff; variables at or below `c` are
unchanged).
Source: Pierce, *Types and Programming Languages*, MIT Press, 2002,
§6.1 (`shift` with `d = -1`). -/
def ULShiftDown (c : ℕ) : ULTerm → ULTerm
  | .var k => if k ≤ c then .var k else .var (k - 1)
  | .app t u => .app (ULShiftDown c t) (ULShiftDown c u)
  | .lam t => .lam (ULShiftDown (c + 1) t)

/-- Auxiliary substitution of `s` for variable `c`: replace `var c` by `s`
(shifted when going under a binder); variables other than `c` are left
unchanged. This is *not* by itself capture-avoiding at the top level: it
does not decrement variables above `c` for the removed binder. Use
`ULSubstTop` for beta reduction.
Source: Pierce, *Types and Programming Languages*, MIT Press, 2002,
§6.1 (`subst`). -/
def ULSubst (c : ℕ) (s : ULTerm) : ULTerm → ULTerm
  | .var k => if k = c then s else .var k
  | .app t u => .app (ULSubst c s t) (ULSubst c s u)
  | .lam t => .lam (ULSubst (c + 1) (ULShift 0 s) t)

/-- Top-level (capture-avoiding) substitution, as used by beta: shift the
argument up by one, substitute, then shift the result down by one for the
removed binder. E.g. reducing the inner redex of the closed term
`lam. ((lam. var 1) (var 0))` gives `lam. var 0` (not `lam. var 1`):
without the final shift-down the result would be open.
Source: Pierce, *Types and Programming Languages*, MIT Press, 2002,
§6.1 (`termSubstTop`). -/
def ULSubstTop (s t : ULTerm) : ULTerm :=
  ULShiftDown 0 (ULSubst 0 (ULShift 0 s) t)

/-- One-step beta reduction (with congruence).
Source: Barendregt, *The Lambda Calculus: Its Syntax and Semantics*,
North-Holland, 1984, §3.1. -/
inductive ULStep : ULTerm → ULTerm → Prop
  | beta {t u : ULTerm} : ULStep (.app (.lam t) u) (ULSubstTop u t)
  | appL {t t' u : ULTerm} (h : ULStep t t') : ULStep (.app t u) (.app t' u)
  | appR {t u u' : ULTerm} (h : ULStep u u') : ULStep (.app t u) (.app t u')
  | lam {t t' : ULTerm} (h : ULStep t t') : ULStep (.lam t) (.lam t')

/-- The reviewer's counterexample, computed: substituting `var 0` for the
bound variable in `var 1` and removing the binder yields `var 0`. -/
example : ULSubstTop (.var 0) (.var 1) = .var 0 := rfl

/-- The Church numeral body: `f` applied `n` times to `x`, inside two
binders (`var 1` is `f`, `var 0` is `x`).
Source: Barendregt, *The Lambda Calculus: Its Syntax and Semantics*,
North-Holland, 1984, §2.2. -/
def churchApp : ℕ → ULTerm
  | 0 => .var 0
  | n + 1 => .app (.var 1) (churchApp n)

/-- The Church numeral of `n`.
Source: Barendregt, *The Lambda Calculus: Its Syntax and Semantics*,
North-Holland, 1984, §2.2. -/
def church (n : ℕ) : ULTerm :=
  .lam (.lam (churchApp n))

/-- The Church boolean of `b`.
Source: Barendregt, *The Lambda Calculus: Its Syntax and Semantics*,
North-Holland, 1984, §2.2. -/
def churchBool : Bool → ULTerm
  | true => .lam (.lam (.var 1))
  | false => .lam (.lam (.var 0))

/-- A predicate is **lambda-decidable** when some untyped lambda term
reduces, on Church numeral input, to the Church boolean of its truth value.
Source: Barendregt, *The Lambda Calculus: Its Syntax and Semantics*,
North-Holland, 1984, §2.2; Soare, *Recursively Enumerable Sets and
Degrees*, Ch. I, Theorem 2.3. -/
def LambdaDecidable (P : ℕ → Prop) : Prop :=
  ∃ t : ULTerm, ∀ n : ℕ,
    (P n → ∃ u, Relation.ReflTransGen ULStep (.app t (church n)) u ∧
      u = churchBool true) ∧
    (¬ P n → ∃ u, Relation.ReflTransGen ULStep (.app t (church n)) u ∧
      u = churchBool false)

/-- **Lambda calculus computes exactly the computable predicates**: a
predicate is lambda-decidable iff it is computable. Source: Church,
"The calculi of lambda-conversion", *Annals of Mathematics Studies* 6
(1941); Kleene, "Lambda-definability and recursiveness", *Duke Mathematical
Journal* 2 (1936), 340–353; Soare, *Recursively Enumerable Sets and Degrees*,
Ch. I, Theorem 2.3. -/
theorem_wanted lambda_decidable_iff_computablePred :
  ∀ {P : ℕ → Prop}, LambdaDecidable P ↔ ComputablePred P

end Cslib.LambdaCalculusEquivalenceWanted

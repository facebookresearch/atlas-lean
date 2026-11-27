/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import CSLibExt.Languages.LambdaCalculus.HindleyMilner.Substitution

/-!
# Call-by-value semantics with constants for let-polymorphic expressions

The pure fragment of the calculus of Pottier and Rémy (*The Essence of ML Type Inference*,
§10.1, Figures 10-1 and 10-2) over the expressions of
`CSLibExt/Languages/LambdaCalculus/HindleyMilner/Typing.lean`, which are kept unchanged.

Constants are names bound by an initial context $\Gamma_0$ whose visible schemes are closed
(their Definition 10.5.2): a `Constants` record gives the context, an arity for each constant,
and the partition into constructors and destructors. The context is a list, so a signature has
finitely many constants, whereas the source allows the set of constants to be finite or
infinite (their §10.1). Constants and program variables are distinct syntactic classes in
the source; here a well-formedness predicate `Constants.WF` restores this: a program never binds
the name of a constant. Without constants, every closed typed expression would be a value or a
redex, and progress would say nothing.

Values are abstractions, variables that are not constants, and constants applied to values below
their arity (constructors up to their arity, destructors strictly below it). Evaluation is
call-by-value, left to right: β-reduction and `let` substitute a value, a δ-relation reduces
saturated destructor applications, and the evaluation contexts are `[]`, `E e`, `v E` and
`let x = E in e`.

The δ-relation is a parameter. `Constants.Agrees` collects the hypotheses on it, all explicit:
the shape of δ-redexes, well-formedness of δ-reducts, and the two requirements of Pottier and
Rémy's Definition 10.5.5 (δ-reduction preserves types; a well-typed constant application to values
is a value or reduces). The reduction need not happen at the root: a destructor applied to more
values than its arity reduces inside the application, by reducing its saturated head. The
well-formedness of reducts, preservation and progress are asked only of well-formed expressions:
the source keeps program variables and constants apart (§10.1), so an expression that binds a
constant name is no program, and δ owes it nothing. δ relates expressions only, with no store, so
every constant has a pure semantics in the sense of their Definition 10.5.6 and no value
restriction is used.

## Main definitions

- `Expr.apps`, `Constants`, `Constants.names`, `Constants.IsValue`, `Constants.Step`,
  `Constants.WF`, `Constants.Agrees`, `Constants.Typed`.

## References

- F. Pottier, D. Rémy, *The Essence of ML Type Inference*, chapter 10 of B. C. Pierce (ed.),
  *Advanced Topics in Types and Programming Languages*, MIT Press 2005: §10.1 (Figures 10-1 and
  10-2) and §10.5 (Definitions 10.5.2, 10.5.5 and 10.5.6).
- A. K. Wright, M. Felleisen, *A syntactic approach to type soundness*, Information and
  Computation 115(1), 1994, 38-94.
-/

@[expose] public section

set_option autoImplicit false

universe u

namespace Cslib.HindleyMilner

open Cslib.Unification Cslib.Unification.Term

/-- **Application to a list of arguments.** The expression $h\, a_1 \cdots a_k$ obtained by
applying $h$ to the arguments $a_1, \dots, a_k$ in order, left-associated; with no arguments it
is $h$. -/
def Expr.apps (h : Expr) (args : List Expr) : Expr := args.foldl Expr.app h

/-- **Constants.** A signature of finitely many constants over base types $B$: a typing context
$\Gamma_0$, a list binding each constant name to a type scheme, an arity for each name, and the
predicate telling the constructors apart from the destructors. The context is closed: the
visible scheme of each name, the scheme of its first binding in $\Gamma_0$, has no free type
variable. A binding shadowed by an earlier binding of the same name is not visible and may have
free type variables. Pottier and Rémy allow the set of constants to be finite or infinite
(§10.1); here it is the finite set of names bound by $\Gamma_0$. -/
structure Constants (B : Type u) where
  /-- The initial context $\Gamma_0$, binding each constant to its type scheme. -/
  ctx : Ctx B
  /-- The arity of each constant. -/
  arity : String → ℕ
  /-- The constructors; every other constant is a destructor. -/
  IsCtor : String → Prop
  /-- The visible scheme of each name of the initial context has no free type variable. -/
  closed : ctx.ftv = ∅

variable {B : Type u}

namespace Constants

variable (K : Constants B)

/-- **Constant names.** The names bound by the initial context of a signature. -/
def names : Finset String := (K.ctx.map Prod.fst).toFinset

/-- **Values.** The values of the calculus with constants $K$: a variable that is not a
constant, an abstraction, and a constant $c$ applied to values $v_1, \dots, v_k$ when $c$ is a
constructor with $k$ at most its arity or a destructor with $k$ less than its arity. -/
inductive IsValue : Expr → Prop
  | var {z : String} : z ∉ K.names → IsValue (.var z)
  | lam {z : String} {e : Expr} : IsValue (.lam z e)
  | const {c : String} {args : List Expr} : c ∈ K.names → (∀ a ∈ args, IsValue a) →
      (K.IsCtor c ∧ args.length ≤ K.arity c ∨ ¬ K.IsCtor c ∧ args.length < K.arity c) →
      IsValue ((Expr.var c).apps args)

/-- **Call-by-value reduction.** The one-step reduction of the calculus with constants $K$ and a
δ-relation $\delta$: β-reduction $(\lambda z.\, e)\, v \to e[z := v]$ and
$\mathsf{let}\ z = v\ \mathsf{in}\ e \to e[z := v]$ for a value $v$, every pair related by
$\delta$, and reduction in the evaluation contexts $[\,]\, e$, $v\, [\,]$ for a value $v$, and
$\mathsf{let}\ z = [\,]\ \mathsf{in}\ e$. -/
inductive Step (δ : Expr → Expr → Prop) : Expr → Expr → Prop
  | beta {z : String} {e v : Expr} : K.IsValue v → Step δ (.app (.lam z e) v) (e[z := v])
  | letV {z : String} {v e : Expr} : K.IsValue v → Step δ (.let_ z v e) (e[z := v])
  | delta {e e' : Expr} : δ e e' → Step δ e e'
  | appL {e₁ e₁' e₂ : Expr} : Step δ e₁ e₁' → Step δ (.app e₁ e₂) (.app e₁' e₂)
  | appR {v e₂ e₂' : Expr} : K.IsValue v → Step δ e₂ e₂' → Step δ (.app v e₂) (.app v e₂')
  | letL {z : String} {e₁ e₁' e₂ : Expr} :
      Step δ e₁ e₁' → Step δ (.let_ z e₁ e₂) (.let_ z e₁' e₂)

/-- **Well-formed programs.** An expression is well formed for the signature $K$ when none of
its binder names is a constant name: a program never binds a constant. -/
def WF (e : Expr) : Prop := Disjoint e.bv K.names

/-- **Agreement of δ with the signature.** The hypotheses on a δ-relation, for the signature
$K$:

- every δ-redex is a destructor applied to exactly as many values as its arity;
- the δ-reduct of a well-formed δ-redex is well formed;
- δ-reduction of a well-formed δ-redex preserves types in the initial context (Pottier and
  Rémy, Definition 10.5.5 (i));
- a well-formed constant application to values that is well typed in the initial context is a
  value or reduces (Definition 10.5.5 (ii)). The reduction need not be a δ-step at the root: a
  destructor applied to more values than its arity reduces in the evaluation context of the
  application, by reducing its saturated head.

The last three conditions concern only well-formed expressions, which bind no constant: the
source keeps program variables and constants apart (§10.1), so an expression that binds a
constant name is no program and places no obligation on δ. -/
structure Agrees (δ : Expr → Expr → Prop) : Prop where
  /-- δ-redexes are saturated destructor applications to values. -/
  redex : ∀ {e e' : Expr}, δ e e' → ∃ c args, e = (Expr.var c).apps args ∧ c ∈ K.names ∧
    ¬ K.IsCtor c ∧ args.length = K.arity c ∧ ∀ a ∈ args, K.IsValue a
  /-- The δ-reduct of a well-formed δ-redex is well formed. -/
  wf : ∀ {e e' : Expr}, δ e e' → K.WF e → K.WF e'
  /-- δ-reduction of a well-formed δ-redex preserves types in the initial context. -/
  preserve : ∀ {e e' : Expr} {τ : Ty B}, δ e e' → HasType K.ctx e τ → K.WF e →
    HasType K.ctx e' τ
  /-- A well-formed, well-typed constant application to values is a value or reduces. -/
  progress : ∀ {c : String} {args : List Expr} {τ : Ty B}, c ∈ K.names →
    (∀ a ∈ args, K.IsValue a) → HasType K.ctx ((Expr.var c).apps args) τ →
    K.WF ((Expr.var c).apps args) →
    K.IsValue ((Expr.var c).apps args) ∨ ∃ e', K.Step δ ((Expr.var c).apps args) e'

/-- **Typed programs.** An expression is a typed program of type $\tau$ for the signature $K$
when it has type $\tau$ in the initial context and is well formed. -/
def Typed (e : Expr) (τ : Ty B) : Prop := HasType K.ctx e τ ∧ K.WF e

end Constants

end Cslib.HindleyMilner

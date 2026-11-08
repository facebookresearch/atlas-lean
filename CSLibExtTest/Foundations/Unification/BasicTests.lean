/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Foundations.Unification.Basic
public meta import CSLibExt.Foundations.Unification.Basic

@[expose] public section

/-!
# Tests for first-order unification

Computed unifiers on small problems (a binding, a decomposition, a chain of variables,
the curried encoding of `f(x, g(y)) = f(g(z), x)`), the three ways to fail (occurs check,
constant clash, constant against node), and the theorems applied to concrete equations.
-/

set_option autoImplicit false

namespace CSLibExtTest.Foundations.Unification

open Cslib.Unification Cslib.Unification.Term Cslib.Unification.Subst

/-- Function and constant symbols for the examples. -/
inductive Sym where
  | a
  | b
  | f
  | g
  deriving DecidableEq, Repr

/-- Read a substitution on the first `n` variables. -/
def readOff (n : Nat) (s : Option (Subst Sym)) : Option (List (Term Sym)) :=
  s.map fun s ↦ (List.range n).map s

-- `x₀ = a`
#guard readOff 1 (unify [(var 0, const Sym.a)]) == some [const Sym.a]
-- `node x₀ b = node a x₁`
#guard readOff 2 (unify [(node (var 0) (const Sym.b), node (const Sym.a) (var 1))]) ==
  some [const Sym.a, const Sym.b]
-- a chain `x₀ = x₁, x₁ = x₂, x₂ = a`: every variable ends at `a`
#guard readOff 3 (unify [(var 0, var 1), (var 1, var 2), (var 2, const Sym.a)]) ==
  some [const Sym.a, const Sym.a, const Sym.a]
-- `f(x₀, g(x₁)) = f(g(x₂), x₀)`, curried: `x₀ ↦ g(x₂)`, `x₁ ↦ x₂`
#guard readOff 3 (unify [(node (node (const Sym.f) (var 0)) (node (const Sym.g) (var 1)),
    node (node (const Sym.f) (node (const Sym.g) (var 2))) (var 0))]) ==
  some [node (const Sym.g) (var 2), var 2, var 2]
-- trivial equations leave variables alone
#guard readOff 2 (unify [(var 0, var 0), (const Sym.a, const Sym.a)]) == some [var 0, var 1]
-- failures: occurs check, clash of constants, constant against node
#guard (unify [(var 0, node (var 0) (const Sym.a))]).isNone
#guard (unify [(node (var 0) (const Sym.a), var 0)]).isNone
#guard (unify [(const Sym.a, const Sym.b)]).isNone
#guard (unify [(const Sym.a, node (var 0) (var 1))]).isNone
-- the occurs check can fire after an elimination: `x₀ = node x₁ a, x₁ = x₀`
#guard (unify [(var 0, node (var 1) (const Sym.a)), (var 1, var 0)]).isNone

/-- Completeness turns the failed occurs check into the absence of any unifier. -/
example : ∀ s : Subst Sym, ¬ Unifies s [(var 0, node (var 0) (const Sym.a))] :=
  unify_eq_none_iff.mp (by simp [unify, vars])

/-- The computed unifier of `x₀ = a` is most general. -/
example : IsMGU (single 0 (const Sym.a) ≫ var) [(var 0, const Sym.a)] :=
  isMGU_unify (by simp [unify, vars, substEqs])

end CSLibExtTest.Foundations.Unification

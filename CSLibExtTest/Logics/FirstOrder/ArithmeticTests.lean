/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Logics.FirstOrder.Arithmetic

@[expose] public section

/-!
# Tests for Peano arithmetic and Robinson's Q

Substitution of `S x` for the outermost bound variable, and the standard model
`ℕ` for the Q axioms and for one parameterized induction axiom (commutativity of
addition, with one free parameter).
-/

set_option autoImplicit false

open FirstOrder FirstOrder.Language Cslib.Logic.FOL

namespace CSLibExtTest.Logics.FirstOrder.Arithmetic

/-- Substituting `S x` for the outermost bound variable `x` gives `S x`. -/
example : substBoundTerm Arithmetic.succBvar (Arithmetic.bvar (0 : Fin 1)) =
    Arithmetic.tSucc (Arithmetic.bvar (0 : Fin 1)) := by
  show substBoundTerm Arithmetic.succBvar (Term.var (Sum.inr (0 : Fin 1))) =
    Arithmetic.tSucc (Term.var (Sum.inr (0 : Fin 1)))
  rw [substBoundTerm_var_zero]
  simp [Arithmetic.succBvar, Arithmetic.tSucc]

/-- Substituting `S x` for `x` in `S x` gives `S (S x)`. -/
example : substBoundTerm Arithmetic.succBvar
    (Arithmetic.tSucc (Arithmetic.bvar (0 : Fin 1))) =
      Arithmetic.tSucc (Arithmetic.tSucc (Arithmetic.bvar (0 : Fin 1))) := by
  show substBoundTerm Arithmetic.succBvar
      (Term.func ArithmeticFunctions.succ ![Term.var (Sum.inr (0 : Fin 1))]) =
    Arithmetic.tSucc (Arithmetic.tSucc (Term.var (Sum.inr (0 : Fin 1))))
  simp only [substBoundTerm, Term.subst, Arithmetic.tSucc]
  congr 1
  funext i
  have hi : i = 0 := Fin.fin_one_eq_zero i
  subst hi
  simp [Term.subst]
  rfl

/-- The Q axioms hold in `ℕ`. -/
example : ∀ ψ ∈ Arithmetic.QTheory, (ℕ ⊨ ψ) := Arithmetic.nat_models_Q

/-- The parameterized induction axiom for commutativity of addition holds in `ℕ`:
for the body `φ(x, y) := x + y = y + x` with one free parameter `y`, the induction
axiom `∀y [φ(0, y) → (∀x (φ(x, y) → φ(S x, y))) → ∀x φ(x, y)]` holds. -/
example : (ℕ ⊨ Arithmetic.inductionAxiom (k := 1)
    (BoundedFormula.equal
      (Term.func ArithmeticFunctions.add
        ![Term.var (Sum.inr (0 : Fin 1)), Term.var (Sum.inl (0 : Fin 1))])
      (Term.func ArithmeticFunctions.add
        ![Term.var (Sum.inl (0 : Fin 1)), Term.var (Sum.inr (0 : Fin 1))]))) :=
  Arithmetic.nat_models_PA _ (Or.inr (Set.mem_iUnion_of_mem 1 ⟨_, rfl⟩))

end CSLibExtTest.Logics.FirstOrder.Arithmetic

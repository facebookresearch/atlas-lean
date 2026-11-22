/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Logics.Modal.FiniteModelProperty

@[expose] public section

/-! # Tests for the finite model property and decidability of T, S4 and S5 -/

namespace Cslib.Modal.FiniteModelPropertyTests

open Formula

inductive Atom where
  | p
  | q
  deriving DecidableEq

/-- The decision procedures, run by the kernel: `⊥` is not a T-theorem and an atom is not an S4-
or S5-theorem. -/
example : ¬Derivable (Axioms.T : Set (Formula Atom)) .bot := by decide +kernel

example : ¬Derivable (Axioms.S4 : Set (Formula Atom)) (atom .p) := by decide +kernel

example : ¬Derivable (Axioms.S5 : Set (Formula Atom)) (atom .p) := by decide +kernel

/-- T-, S4- and S5-provability are decidable. -/
example (phi : Formula Atom) : Decidable (Derivable Axioms.S4 phi) := inferInstance

/-- The reflexive transitive, non-symmetric model `false ≤ true`, with every atom true at
`false` only. -/
def upward : KripkeModel Bool Atom where
  nonempty_world := ⟨false⟩
  rel w w' := w = false ∨ w' = true
  valuation w _ := w = false

/-- The finite model property of S4: axiom `5` is not an S4-theorem (it fails in `upward`), so it
fails in a finite reflexive transitive model with at most `2 ^ |sub 5|` worlds. -/
example : ∃ (W : Type) (_ : Fintype W) (M : KripkeModel W Atom),
    Fintype.card W ≤ 2 ^ (axiomFive (atom Atom.p)).sub.card ∧ ((∀ w, M.rel w w) ∧
      ∀ {a b c}, M.rel a b → M.rel b c → M.rel a c) ∧ ¬M.Valid (axiomFive (atom .p)) := by
  refine exists_finite_countermodel_S4 fun h ↦ ?_
  have := h.valid_S4 (M := upward) (by intro w; cases w <;> simp [upward])
    (by intro a b c; cases a <;> cases b <;> cases c <;> simp [upward]) false
  simp [axiomFive, upward, KripkeModel.satisfies_dia] at this

/-- The frame condition matters: the `T` axiom fails in some finite model on subsets of its
subformulas, but in no reflexive one. -/
example : ¬FinValid (axiomT (atom Atom.p)) := by decide +kernel

example : FinValidWith FinRefl (axiomT (atom Atom.p)) :=
  derivable_T_iff_finValidWith.mp (derivable_T_iff.mpr fun _ M hrefl ↦ M.valid_axiomT hrefl _)

/-- A reflexive, non-transitive model on `ℕ`: `n` sees `n` and `n + 1`; `p` holds at `0` and `1`. -/
def step : KripkeModel ℕ Atom where
  nonempty_world := ⟨0⟩
  rel n m := m = n ∨ m = n + 1
  valuation n _ := n ≤ 1

/-- The finite model property of T: axiom `4` is not a T-theorem (it fails at `0` in `step`), so
it fails in a finite reflexive model. -/
example : ∃ (W : Type) (_ : Fintype W) (M : KripkeModel W Atom),
    Fintype.card W ≤ 2 ^ (axiomFour (atom Atom.p)).sub.card ∧ (∀ w, M.rel w w) ∧
      ¬M.Valid (axiomFour (atom .p)) := by
  refine exists_finite_countermodel_T fun h ↦ ?_
  have := h.valid_T (M := step) (fun n ↦ Or.inl rfl) 0
  simp only [axiomFour, KripkeModel.satisfies_imp, KripkeModel.satisfies_box] at this
  have h2 := this (fun m hm ↦ by rcases hm with rfl | rfl <;> simp [step]) 1 (Or.inr rfl) 2
    (Or.inr rfl)
  simp [step] at h2

/-- The finite model property of S5: `p` is not an S5-theorem, so it fails in a finite model whose
relation is an equivalence. -/
example : ∃ (W : Type) (_ : Fintype W) (M : KripkeModel W Atom),
    Fintype.card W ≤ 2 ^ (atom Atom.p).sub.card ∧ Equivalence M.rel ∧ ¬M.Valid (atom .p) :=
  exists_finite_countermodel_S5 (by decide +kernel)

end Cslib.Modal.FiniteModelPropertyTests

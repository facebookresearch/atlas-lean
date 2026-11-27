/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import CSLibExt.Languages.StaticAnalysis.WorkList
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Fintype.Pi
import Mathlib.Order.Fin.Basic
import Mathlib.Order.FixedPoints
import Mathlib.Tactic.FinCases

/-! # Tests for the simple work-list algorithm -/

open Function Relation Cslib.Semantics.Rewriting Cslib.StaticAnalysis.WorkList

/-- A two-node system over `Bool`: `x₀ = true` and `x₁ = x₀`. -/
private def copyF : (Fin 2 → Bool) →o (Fin 2 → Bool) where
  toFun x := ![true, x 0]
  monotone' x y h i := by
    fin_cases i
    · exact le_rfl
    · exact h 0

private theorem copyF_apply (x : Fin 2 → Bool) : copyF x = ![true, x 0] := rfl

/-- Only `x₁` reads `x₀`, and nothing reads `x₁`. -/
private def copyDep : Fin 2 → Finset (Fin 2) := ![{1}, ∅]

/-- The dependency hypothesis holds for `copyDep`. -/
example : ∀ i j, j ∉ copyDep i → ∀ x a, copyF (update x i a) j = copyF x j := by
  decide

/-- Non-vacuity: removing node `1`, then `0`, then `1` again is a run from `(⊥, univ)` that
stops at `x = (true, true)` with an empty work-list. -/
example : NormalForm (Step copyF copyDep) (⊥, Finset.univ) (![true, true], ∅) := by
  have h1 : Step copyF copyDep (⊥, Finset.univ) (⊥, {0}) := by
    convert Step.keep (f := copyF) (dep := copyDep) (x := ⊥) (W := Finset.univ) (i := 1)
      (Finset.mem_univ 1) (by decide) using 2
    decide
  have h2 : Step copyF copyDep (⊥, {0}) (![true, false], {1}) := by
    convert Step.update (f := copyF) (dep := copyDep) (x := ⊥) (W := {0}) (i := 0)
      (by simp) (by decide) using 2 <;> decide
  have h3 : Step copyF copyDep (![true, false], {1}) (![true, true], ∅) := by
    convert Step.update (f := copyF) (dep := copyDep) (x := ![true, false]) (W := {1}) (i := 1)
      (by simp) (by decide) using 2 <;> decide
  refine ⟨((ReflTransGen.single h1).tail h2).tail h3, ?_⟩
  · rintro ⟨t, ht⟩
    cases ht with
    | keep hi => simp at hi
    | update hi => simp at hi

/-- The main theorem applied to the system `x₀ = true`, `x₁ = x₀`: every run that stops returns
the least fixed point, here `(true, true)`. -/
example (s : (Fin 2 → Bool) × Finset (Fin 2))
    (hs : NormalForm (Step copyF copyDep) (⊥, Finset.univ) s) :
    s = (![true, true], ∅) := by
  obtain ⟨hW, hfix, -⟩ := (sn_and_isLeast_fixedPoints copyF copyDep (by decide)).2 s hs
  have h0 := congrFun hfix 0
  have h1 := congrFun hfix 1
  simp only [copyF_apply, Matrix.cons_val_zero, Matrix.cons_val_one] at h0 h1
  refine Prod.ext (funext fun i => ?_) hW
  fin_cases i
  · exact h0.symm
  · simpa [← h0] using h1.symm

/-- On a complete lattice, every run that stops returns Mathlib's least fixed point
`OrderHom.lfp f`. -/
example {ι L : Type*} [Fintype ι] [DecidableEq ι] [CompleteLattice L] [WellFoundedGT L]
    (f : (ι → L) →o (ι → L)) (dep : ι → Finset ι)
    (hdep : ∀ i j, j ∉ dep i → ∀ x a, f (update x i a) j = f x j)
    (s : (ι → L) × Finset ι) (hs : NormalForm (Step f dep) (⊥, Finset.univ) s) :
    s.1 = f.lfp :=
  ((sn_and_isLeast_fixedPoints f dep hdep).2 s hs).2.unique f.isLeast_lfp

/-- The step map `0 ↦ 1 ↦ 2 ↦ 2` on the chain `Fin 3`. -/
private def climb : Fin 3 → Fin 3 := ![1, 2, 2]

/-- One node whose constraint reads its own variable: `x₀ = climb x₀`, with least solution
`2`. -/
private def climbF : (Fin 1 → Fin 3) →o (Fin 1 → Fin 3) where
  toFun x _ := climb (x 0)
  monotone' x y h _ := by
    have := h 0
    revert this
    generalize x 0 = a
    generalize y 0 = b
    decide +revert

private theorem climbF_apply (x : Fin 1 → Fin 3) : climbF x = fun _ => climb (x 0) := rfl

/-- Counterexample: the dependency hypothesis must include a node whose constraint reads its own
variable. With `dep 0 = ∅`, the run `(0, {0}) → (1, ∅)` stops at `x₀ = 1`, which is not a fixed
point of `climbF`. -/
example :
    NormalForm (Step climbF fun _ => ∅) (⊥, Finset.univ) (fun _ => 1, ∅) ∧
      (fun _ => 1) ∉ fixedPoints climbF := by
  refine ⟨⟨.single ?_, ?_⟩, ?_⟩
  · convert Step.update (f := climbF) (dep := fun _ => ∅) (x := ⊥) (W := Finset.univ) (i := 0)
      (Finset.mem_univ 0) (by decide) using 2 <;> decide
  · rintro ⟨t, ht⟩
    cases ht with
    | keep hi => simp at hi
    | update hi => simp at hi
  · intro h
    have := congrFun h 0
    revert this
    decide

/-- With `dep 0 = {0}` the dependency hypothesis holds, and every run that stops returns the least
solution `x₀ = 2`. -/
example (s : (Fin 1 → Fin 3) × Finset (Fin 1))
    (hs : NormalForm (Step climbF fun _ => {0}) (⊥, Finset.univ) s) :
    s.1 = fun _ => 2 := by
  obtain ⟨-, hfix, -⟩ :=
    (sn_and_isLeast_fixedPoints climbF (fun _ => {0}) (by decide)).2 s hs
  have h : climb (s.1 0) = s.1 0 := congrFun hfix 0
  have key : ∀ a : Fin 3, climb a = a → a = 2 := by decide
  funext i
  rw [Subsingleton.elim i 0]
  exact key _ h

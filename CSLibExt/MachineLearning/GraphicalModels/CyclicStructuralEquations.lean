/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Fintype.Pi

/-!
# Cyclic structural equations

A system of structural equations on variables `ι` with values in `α` gives each variable a
right-hand side that may read every variable, including itself and later ones: no acyclicity
is imposed. A solution is an assignment satisfying all equations. A recursive (acyclic) system
has exactly one solution for each value of the exogenous noise (Pearl 2009, §7.1); without
acyclicity a system can have no solution or several.

## Main definitions

* `StructuralSystem ι α`: a possibly cyclic system of structural equations, the exogenous noise
  held fixed and absorbed into the right-hand sides.
* `StructuralSystem.IsSolution F x`: `x i = F i x` for every variable `i`.
* `StructuralSystem.negCycle`, `StructuralSystem.copyCycle`: the Boolean systems
  `x = ¬y, y = x` and `x = y, y = x`.

## Main results

* `StructuralSystem.negCycle_not_isSolution`: `x = ¬y, y = x` has no solution.
* `StructuralSystem.copyCycle_isSolution_iff`, `StructuralSystem.copyCycle_not_unique`: the
  solutions of `x = y, y = x` are exactly `x = y = false` and `x = y = true`.

## Relation to recursive structural causal models

A recursive model `M : FiniteSCM α n U`
(`CSLibExt/MachineLearning/GraphicalModels/StructuralCausalModels.lean`) at the noise value `u`
is the special case of a `StructuralSystem (Fin n) α` in which the right-hand side of node `k`,
`fun x => M.f k (M.paVal k x) (u k)`, reads only the earlier nodes `M.pa k`; unfolding the two
definitions, `M.IsSolution u x` is `IsSolution (fun k x => M.f k (M.paVal k x) (u k)) x`. For
such systems `FiniteSCM.existsUnique_isSolution` gives exactly one solution. The two systems
below lie outside that case: each variable reads the other, so the dependency graph has the
cycle `0 → 1 → 0`, and existence or uniqueness fails.

## References

* J. Pearl, *Causality: Models, Reasoning, and Inference*, 2nd ed., Cambridge University Press
  (2009), §7.1.
-/

@[expose] public section

namespace Cslib.MachineLearning.GraphicalModels

/-- A possibly cyclic system of structural equations on the variables `ι` with values in `α`
(the exogenous noise is held fixed and absorbed into the right-hand sides): the right-hand side
of variable `i` is a function of the values of all variables. -/
abbrev StructuralSystem (ι α : Type*) := ι → (ι → α) → α

namespace StructuralSystem

/-- `x` is a solution of the system `F`: `x i = F i x` for every variable `i`. -/
def IsSolution {ι α : Type*} (F : StructuralSystem ι α) (x : ι → α) : Prop :=
  ∀ i, x i = F i x

/-- The cyclic Boolean system `x = ¬y`, `y = x` (variables `0 = x`, `1 = y`). -/
def negCycle : StructuralSystem (Fin 2) Bool :=
  ![fun v => !v 1, fun v => v 0]

/-- The cyclic Boolean system `x = y`, `y = x` (variables `0 = x`, `1 = y`). -/
def copyCycle : StructuralSystem (Fin 2) Bool :=
  ![fun v => v 1, fun v => v 0]

/-- **A cyclic system with no solution**: `x = ¬y`, `y = x` has no solution on `Bool`. -/
theorem negCycle_not_isSolution (x : Fin 2 → Bool) : ¬ negCycle.IsSolution x := by
  intro h
  have h0 := h 0
  have h1 := h 1
  simp only [negCycle, Matrix.cons_val_zero, Matrix.cons_val_one] at h0 h1
  cases hx0 : x 0 <;> cases hx1 : x 1 <;> simp_all

/-- **A cyclic system with two solutions**: the solutions of `x = y`, `y = x` on `Bool` are
exactly `x = y = false` and `x = y = true`. -/
theorem copyCycle_isSolution_iff (x : Fin 2 → Bool) :
    copyCycle.IsSolution x ↔ x = ![false, false] ∨ x = ![true, true] := by
  constructor
  · intro h
    have h0 := h 0
    have h1 := h 1
    simp only [copyCycle, Matrix.cons_val_zero, Matrix.cons_val_one] at h0 h1
    cases hx0 : x 0 <;> cases hx1 : x 1
    · left
      have hpt : ∀ i, x i = ![false, false] i := by
        rw [Fin.forall_fin_two]
        simp_all [Matrix.cons_val_zero, Matrix.cons_val_one]
      exact funext hpt
    · simp_all
    · simp_all
    · right
      have hpt : ∀ i, x i = ![true, true] i := by
        rw [Fin.forall_fin_two]
        simp_all [Matrix.cons_val_zero, Matrix.cons_val_one]
      exact funext hpt
  · intro h
    cases h with
    | inl heq =>
      subst heq
      simp only [IsSolution, Fin.forall_fin_two, copyCycle, Matrix.cons_val_zero,
        Matrix.cons_val_one]
      trivial
    | inr heq =>
      subst heq
      simp only [IsSolution, Fin.forall_fin_two, copyCycle, Matrix.cons_val_zero,
        Matrix.cons_val_one]
      trivial

/-- The two solutions of `x = y`, `y = x` are distinct, so the solution is not unique. -/
theorem copyCycle_not_unique :
    copyCycle.IsSolution ![false, false] ∧ copyCycle.IsSolution ![true, true] ∧
      (![false, false] : Fin 2 → Bool) ≠ ![true, true] := by
  refine ⟨?_, ?_, ?_⟩
  · simp only [IsSolution, Fin.forall_fin_two, copyCycle, Matrix.cons_val_zero,
      Matrix.cons_val_one]
    trivial
  · simp only [IsSolution, Fin.forall_fin_two, copyCycle, Matrix.cons_val_zero,
      Matrix.cons_val_one]
    trivial
  · intro hcon
    have h0 := congrArg (fun v : Fin 2 → Bool => v 0) hcon
    simp only [Matrix.cons_val_zero] at h0
    simp at h0

end StructuralSystem

end Cslib.MachineLearning.GraphicalModels

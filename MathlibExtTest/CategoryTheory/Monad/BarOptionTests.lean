/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.Monad.BarSimplicial
public import Mathlib.CategoryTheory.Monad.Types

/-!
# The two-sided bar construction of the option monad

For the option monad on types, with the monad as its own right and left module, the two-sided bar
construction has `Option^(n + 2) X` in degree `n`. Between degrees `1` and `0` the face `δ 0` joins
the two outer layers and `δ 1` the two inner ones, so they differ on `some none`, and the
degeneracy `σ 0` inserts `some` between the two layers; both faces undo the degeneracy.
-/

@[expose] public section

set_option autoImplicit false

open CategoryTheory Opposite Simplicial

namespace CategoryTheory.Monad.BarOptionTests

/-- The option monad on types. -/
noncomputable abbrev optionMonad : Monad (Type) := ofTypeMonad Option

/-- The two-sided bar construction of the option monad over itself. -/
noncomputable abbrev bar : SimplicialObject (Type ⥤ Type) :=
  twoSidedBar optionMonad (RightModule.regular optionMonad) (LeftModule.regular optionMonad)

example (X : Type) : (bar.obj (op ⦋0⦌)).obj X = Option (Option X) := rfl

example (X : Type) : (bar.obj (op ⦋1⦌)).obj X = Option (Option (Option X)) := rfl

/-- `δ 0` joins the two outer layers. -/
theorem δ_zero_apply (X : Type) (x : Option (Option (Option X))) :
    (bar.map (SimplexCategory.δ (0 : Fin 2)).op).app X x = x.join := by
  simp only [twoSidedBar_map_δ_op]
  rfl

/-- `δ 1` joins the two inner layers. -/
theorem δ_one_apply (X : Type) (x : Option (Option (Option X))) :
    (bar.map (SimplexCategory.δ (1 : Fin 2)).op).app X x = x.map Option.join := by
  simp only [twoSidedBar_map_δ_op]
  rfl

/-- `σ 0` inserts `some` between the two layers. -/
theorem σ_zero_apply (X : Type) (x : Option (Option X)) :
    (bar.map (SimplexCategory.σ (0 : Fin 1)).op).app X x = x.map some := by
  simp only [twoSidedBar_map_σ_op]
  rfl

/-- The two faces from degree `1` to degree `0` are different maps. -/
example :
    (bar.map (SimplexCategory.δ (0 : Fin 2)).op).app Bool ≠
      (bar.map (SimplexCategory.δ (1 : Fin 2)).op).app Bool := by
  intro h
  have hx := congrArg (fun f => f (some none : Option (Option (Option Bool)))) h
  simp only [δ_zero_apply, δ_one_apply] at hx
  simp at hx

example (x : Option (Option Bool)) :
    (bar.map (SimplexCategory.δ (0 : Fin 2)).op).app Bool
      ((bar.map (SimplexCategory.σ (0 : Fin 1)).op).app Bool x) = x :=
  (congrArg (fun y => (bar.map (SimplexCategory.δ (0 : Fin 2)).op).app Bool y)
    (σ_zero_apply Bool x)).trans ((δ_zero_apply Bool _).trans (by cases x <;> rfl))

example (x : Option (Option Bool)) :
    (bar.map (SimplexCategory.δ (1 : Fin 2)).op).app Bool
      ((bar.map (SimplexCategory.σ (0 : Fin 1)).op).app Bool x) = x :=
  (congrArg (fun y => (bar.map (SimplexCategory.δ (1 : Fin 2)).op).app Bool y)
    (σ_zero_apply Bool x)).trans ((δ_one_apply Bool _).trans (by
      cases x with
      | none => rfl
      | some y => cases y <;> rfl))

end CategoryTheory.Monad.BarOptionTests

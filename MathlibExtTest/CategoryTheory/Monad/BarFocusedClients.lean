/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.CategoryTheory.Monad.BarFunctorial
import MathlibExt.CategoryTheory.Monad.BarResolution
import Mathlib.CategoryTheory.Monad.Types

/-!
# Focused clients of the monadic bar construction

Concrete checks for the option monad `T X = Option X` on types, whose multiplication is `joinM`
and whose unit is `some`.

* The two-sided bar `B(T, T, T)` of the regular modules: its objects in degrees 0, 1 and 2 are
  the iterated option types, and its faces and degeneracies are those of `twoSidedBar`. In
  degree 1 the two faces differ: on `some none` the right action gives `none` and the left action
  gives `some none`.
* Simplicial identities on this instance: `d₀ ∘ s₀` and `d₁ ∘ s₀` are the identity, while
  `s₀ ∘ d₀` is not.
* Functoriality: the degree-one object is a functor, here applied to `not`, and the faces are
  natural for it; an algebra morphism that is not the identity induces a map of bar
  resolutions.
* Augmentation and resolution: for the pointed set `Bool` with base `false`, the augmentation is
  `Option.getD false`, the extra degeneracy is `some`, and `s ∘ ε` is not the identity.
* Boundary case: for the identity monad both faces in degree 1 are identities.
-/

set_option autoImplicit false

open CategoryTheory CategoryTheory.Monad Opposite
open scoped Simplicial

namespace MathlibExtTest.CategoryTheory.Monad.BarFocusedClients

/-- The option monad on types. -/
abbrev T : Monad Type :=
  ofTypeMonad Option

/-- `T` as a right module over itself. -/
abbrev R : RightModule T Type :=
  RightModule.regular T

/-- `T` as a left module over itself. -/
abbrev L : LeftModule Type T :=
  LeftModule.regular T

/-- The two-sided bar `B(T, T, T)`. -/
noncomputable abbrev bar : SimplicialObject (Type ⥤ Type) :=
  twoSidedBar T R L

/-! ### Low-degree objects -/

example : bar.obj (op ⦋1⦌) = barObj T R L 1 :=
  twoSidedBar_obj_op_mk T R L 1

example : (barObj T R L 0).obj Bool = Option (Option Bool) :=
  rfl

example : (barObj T R L 1).obj Bool = Option (Option (Option Bool)) :=
  rfl

example : (barObj T R L 2).obj Bool = Option (Option (Option (Option Bool))) :=
  rfl

/-! ### Faces and degeneracies in low degrees -/

/-- The face `d₀` of the two-sided bar is the right action. -/
example : bar.map (SimplexCategory.δ (0 : Fin 2)).op = barFace (T := T) (R := R) (L := L) 0 0 :=
  twoSidedBar_map_δ_op T R L 0

/-- The degeneracy `s₀` of the two-sided bar. -/
example : bar.map (SimplexCategory.σ (0 : Fin 1)).op =
    barDegeneracy (T := T) (R := R) (L := L) 0 0 :=
  twoSidedBar_map_σ_op T R L 0

/-- The faces `d₀, d₁` and the degeneracy `s₀` between degrees 0 and 1. -/
noncomputable abbrev d₀ : barObj T R L 1 ⟶ barObj T R L 0 :=
  barFace 0 0

noncomputable abbrev d₁ : barObj T R L 1 ⟶ barObj T R L 0 :=
  barFace 0 1

noncomputable abbrev s₀ : barObj T R L 0 ⟶ barObj T R L 1 :=
  barDegeneracy 0 0

/-- The element `some none` in degree 1. -/
abbrev x₁ : Option (Option (Option Bool)) :=
  some none

/-- `d₀` is the right action, the outer multiplication. -/
theorem d₀_x₁ : d₀.app Bool x₁ = none :=
  rfl

/-- `d₁` is the left action, the inner multiplication. -/
theorem d₁_x₁ : d₁.app Bool x₁ = some none :=
  rfl

/-- So the two faces differ. -/
theorem d₀_ne_d₁ : d₀ ≠ d₁ := fun h => by
  have h' : (none : Option (Option Bool)) = some none :=
    d₀_x₁.symm.trans ((congrArg (fun f => f.app Bool x₁) h).trans d₁_x₁)
  exact Option.some_ne_none _ h'.symm

/-- `s₀` inserts the unit inside the right-module factor. -/
theorem s₀_none : s₀.app Bool (none : Option (Option Bool)) = none :=
  rfl

theorem s₀_some_none : s₀.app Bool (some none : Option (Option Bool)) = some (some none) :=
  rfl

/-! ### Simplicial identities -/

/-- `d₀ ∘ s₀` is the identity. -/
example : s₀ ≫ d₀ = 𝟙 _ :=
  barDegeneracy_self 0 0

/-- `d₁ ∘ s₀` is the identity. -/
example : s₀ ≫ d₁ = 𝟙 _ :=
  barDegeneracy_succ 0 0

/-- But `s₀ ∘ d₀` sends `some none` to `none`, so it is not the identity. -/
theorem d₀_s₀_x₁ : (d₀ ≫ s₀).app Bool x₁ = none :=
  rfl

theorem d₀_s₀_ne_id : d₀ ≫ s₀ ≠ 𝟙 _ := fun h => by
  have h' : (none : Option (Option (Option Bool))) = some none :=
    d₀_s₀_x₁.symm.trans (congrArg (fun f => f.app Bool x₁) h)
  exact Option.some_ne_none _ h'.symm

/-- The face relation `d₀ d₁ = d₀ d₀` from degree 2. -/
example : barFace (T := T) (R := R) (L := L) 1 1 ≫ barFace 0 0 =
    barFace (T := T) (R := R) (L := L) 1 0 ≫ barFace 0 0 :=
  barFace_face 0 0 0 le_rfl

/-! ### Functoriality -/

/-- The degree-one object is a functor; on `not` it acts on the innermost entry. -/
theorem obj₁_map_not :
    (barObj T R L 1).map (↾not) (some (some (some true)) : Option (Option (Option Bool))) =
      some (some (some false)) :=
  rfl

/-- The faces are natural for `not`. -/
example :
    (barObj T R L 1).map (↾not) ≫ d₀.app Bool = d₀.app Bool ≫ (barObj T R L 0).map (↾not) :=
  d₀.naturality (↾not)

/-- The pointed set `Bool` with base `b`, an algebra for the option monad. -/
def pointed (b : Bool) : T.Algebra where
  A := Bool
  a := ↾fun o => o.getD b
  unit := by ext x; rfl
  assoc := by
    ext o
    rcases o with _ | _ | x <;> rfl

/-- `not` is a morphism from base `false` to base `true`, and not the identity. -/
def notHom : pointed false ⟶ pointed true where
  f := ↾not
  h := by
    ext o
    rcases o with _ | x <;> rfl

/-- It induces a map of bar resolutions, which in degree zero applies `not` inside. -/
theorem resolutionHom_not :
    (resolutionHom notHom).left.app (op ⦋0⦌) (some true : Option Bool) = some false :=
  rfl

/-! ### Augmentation and resolution -/

/-- The augmentation of the resolution is the algebra structure map, `Option.getD false`. -/
theorem augmentation_none :
    (resolutionAugmented (pointed false)).hom.app (op ⦋0⦌) (none : Option Bool) = false := by
  rw [resolutionAugmented_hom_zero]
  rfl

/-- The extra degeneracy is the unit `some`. -/
theorem extra_s' : (resolutionExtra (pointed false)).s' true = some true := by
  rw [resolutionExtra_s']
  rfl

/-- `ε ∘ s` is the identity ... -/
example : (resolutionExtra (pointed false)).s' ≫
    (resolutionAugmented (pointed false)).hom.app (op ⦋0⦌) = 𝟙 _ :=
  (resolutionExtra (pointed false)).s'_comp_ε

/-- ... but `s ∘ ε` is not: it sends `none` to `some false`. -/
theorem s'_ε_none :
    (resolutionExtra (pointed false)).s'
      ((resolutionAugmented (pointed false)).hom.app (op ⦋0⦌) (none : Option Bool)) =
        some false := by
  rw [augmentation_none, resolutionExtra_s']
  rfl

/-! ### Boundary case: the identity monad -/

/-- The regular modules of the identity monad. -/
abbrev Rid : RightModule (Monad.id Type) Type :=
  RightModule.regular _

abbrev Lid : LeftModule Type (Monad.id Type) :=
  LeftModule.regular _

/-- For the identity monad, both faces in degree one are the identity. -/
example : barFace (T := Monad.id Type) (R := Rid) (L := Lid) 0 0 = 𝟙 _ ∧
    barFace (T := Monad.id Type) (R := Rid) (L := Lid) 0 1 = 𝟙 _ :=
  ⟨rfl, rfl⟩

end MathlibExtTest.CategoryTheory.Monad.BarFocusedClients

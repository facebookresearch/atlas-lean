/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import Mathlib.CategoryTheory.Monoidal.Category

@[expose] public section
set_option autoImplicit false
universe uV vV uH

open CategoryTheory MonoidalCategory

namespace CategoryTheory.EnrichedPointFunctionTransport

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  {X Y : V} {H : Sort uH}

/-- Rebase the entire original point function along its proved Hom-object equality. -/
theorem point_function (h : X = Y)
    (p : H → (𝟙_ V ⟶ X)) (q : H → (𝟙_ V ⟶ Y)) (hp : HEq p q) :
    (fun f => p f ≫ eqToHom h) = q := by
  cases h
  cases hp
  funext f
  rw [eqToHom_refl, Category.comp_id]

/-- Evaluate the same whole point transport while all Hom objects are still abstract. -/
@[reassoc]
theorem point_function_apply (h : X = Y)
    (p : H → (𝟙_ V ⟶ X)) (q : H → (𝟙_ V ⟶ Y)) (hp : HEq p q) (f : H) :
    p f ≫ eqToHom h = q f := by
  exact congrFun (point_function h p q hp) f

/-- The entire point function is retained by the isomorphism of its original endpoints. -/
theorem point_function_eqToIso (h : X = Y)
    (p : H → (𝟙_ V ⟶ X)) (q : H → (𝟙_ V ⟶ Y)) (hp : HEq p q) :
    (fun f => p f ≫ (eqToIso h).hom) = q := by
  exact point_function h p q hp

/-- Scalar use of the full isomorphism transport avoids a native function-congruence term. -/
@[reassoc]
theorem point_function_eqToIso_apply (h : X = Y)
    (p : H → (𝟙_ V ⟶ X)) (q : H → (𝟙_ V ⟶ Y)) (hp : HEq p q) (f : H) :
    p f ≫ (eqToIso h).hom = q f := by
  exact point_function_apply h p q hp f

end CategoryTheory.EnrichedPointFunctionTransport

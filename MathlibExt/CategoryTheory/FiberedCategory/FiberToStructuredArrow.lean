/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import Mathlib.CategoryTheory.FiberedCategory.Fiber
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Basic

/-!
# The strict-fiber inclusion in the original left comma

Every functor has this inclusion, without a discrete-base or prefibered
assumption. It retains the given total object and vertical morphism; the
stored fiber equality supplies the original structural arrow. Discrete
fiber equivalences and Cartesian adjunctions reuse this one construction.
Object and Hom universes of the base and total categories are independent.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits

universe uS vS uX vX

namespace CategoryTheory.Functor

variable {S : Type uS} {X : Type uX} [Category.{vS} S] [Category.{vX} X]
  {p : X ⥤ S}

/-- The actual fiber inclusion uses its stored equality in the left-comma direction. -/
def fiberToStructuredArrow (s : S) : p.Fiber s ⥤ StructuredArrow s p where
  obj a := StructuredArrow.mk (eqToHom a.property.symm)
  map {a b} f := StructuredArrow.homMk f.val (by
    let e := Functor.Fiber.fiberInclusionCompIsoConst (p := p) (S := s)
    have h := e.inv.naturality f
    change (𝟙 s) ≫ eqToHom b.property.symm =
      eqToHom a.property.symm ≫ p.map f.val at h
    exact h.symm.trans (Category.id_comp _))
  map_id a := by
    apply StructuredArrow.hom_ext
    rfl
  map_comp f g := by
    apply StructuredArrow.hom_ext
    rfl

/-- The total object is retained by the actual left-comma inclusion. -/
theorem fiberToStructuredArrow_obj_right (s : S) (a : p.Fiber s) :
    ((fiberToStructuredArrow (p := p) s).obj a).right = a.val := rfl

/-- The defining base arrow is exactly the inverse stored fiber equality. -/
theorem fiberToStructuredArrow_obj_hom (s : S) (a : p.Fiber s) :
    ((fiberToStructuredArrow (p := p) s).obj a).hom = eqToHom a.property.symm := rfl

/-- The actual vertical arrow is retained on the right coordinate. -/
theorem fiberToStructuredArrow_map_right (s : S) {a b : p.Fiber s} (f : a ⟶ b) :
    ((fiberToStructuredArrow (p := p) s).map f).right = f.val := rfl


private theorem originalFiberCommaProjectionComputed (s : S) :
    fiberToStructuredArrow (p := p) s ⋙ StructuredArrow.proj s p =
      (Fiber.fiberInclusion : p.Fiber s ⥤ X) := by
  refine Functor.hext (fun _ => rfl) ?_
  intro a b f
  exact heq_of_eq rfl

/-- The whole original left-comma inclusion retains the strict-fiber total projection. -/
public theorem fiberToStructuredArrow_projection (s : S) :
    fiberToStructuredArrow (p := p) s ⋙ StructuredArrow.proj s p =
      (Fiber.fiberInclusion : p.Fiber s ⥤ X) :=
  originalFiberCommaProjectionComputed s

end CategoryTheory.Functor

end

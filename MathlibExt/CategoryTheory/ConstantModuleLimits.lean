/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf
public import Mathlib.Algebra.Category.ModuleCat.Limits

/-!
# Native limits of module presheaves with constant coefficients

A module presheaf over the constant ring has its original restriction
maps as a genuine ModuleCat diagram. Its inverse limit and projections
are the native categorical module limit. This adapter does not supply a
derived inverse-limit identification.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.CategoryTheory.ConstantModuleLimits

open _root_.CategoryTheory Opposite

universe u v w

variable {C : Type u} [Category.{v} C] (R : Type w) [Ring R]
  (M : PresheafOfModules.{w} ((Functor.const Cᵒᵖ).obj (RingCat.of R)))

/-- The actual linear restriction maps of the constant-coefficient module presheaf. -/
def diagram : Cᵒᵖ ⥤ ModuleCat.{w} R where
  obj X := M.obj X
  map f := ModuleCat.ofHom {
    toFun := M.map f
    map_add' := (M.map f).hom.map_add
    map_smul' r x := M.map_smul f r x }
  map_id X := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change M.map (𝟙 X) x = x
    rw [M.map_id]
    rfl
  map_comp f g := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact M.map_comp_apply f g x

variable {M} {N : PresheafOfModules.{w} ((Functor.const Cᵒᵖ).obj (RingCat.of R))}

/-- A map of the original module presheaves induces the same actual linear diagram map. -/
def diagramMap (f : M ⟶ N) : diagram R M ⟶ diagram R N where
  app X := f.app X
  naturality {X Y} a := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact congrArg (fun h => h x) (f.naturality a)

end MathlibExt.CategoryTheory.ConstantModuleLimits

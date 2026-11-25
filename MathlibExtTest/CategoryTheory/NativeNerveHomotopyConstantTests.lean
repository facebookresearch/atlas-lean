/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.CategoryTheory.NerveHomotopy

/-!
# Native equality-transport cylinder values

The actual source has object and Hom level `max u v`, and the target has
object level `u` with the same full Hom level. Equality transport at the
chosen source object is tested on arbitrary interval simplices, including
crossings, with the literal constant target chain as the expected value.
-/

public section

open CategoryTheory Opposite
open scoped Simplicial MonoidalCategory CategoryTheory.Prod

universe u v

namespace MathlibExtTest.NativeNerveHomotopyConstant

variable {A : Type (max u v)} [Category.{max u v} A]
  {B : Type u} [Category.{max u v} B] {F G : A ⥤ B}

/-- Every interval simplex retains the same actual constant target chain. -/
theorem native_equality_transport_constant_target_chain
    (α : F ⟶ G) (c : A) (h : F.obj c = G.obj c)
    (hα : α.app c = eqToHom h) {Δ : SimplexCategoryᵒᵖ}
    (t : (Δ[1] : SSet.{max u v}).obj Δ) :
    (NatTrans.nerveHomotopyMapCommonHom.{u, max u v, 0} α).app Δ
        ⟨(Functor.const (Fin (Δ.unop.len + 1))).obj c, t⟩ =
      (Functor.const (Fin (Δ.unop.len + 1))).obj (F.obj c) := by
  have hNative := NatTrans.nerveHomotopyMapCommonHom_const_apply_of_app_eqToHom.{
    u, max u v, 0} α c h hα t
  refine hNative.trans ?_
  change ((Functor.const (Fin (Δ.unop.len + 1))).obj c) ⋙ F =
    (Functor.const (Fin (Δ.unop.len + 1))).obj (F.obj c)
  apply CategoryTheory.Functor.hext
  · intro i
    rfl
  · intro i j f
    apply heq_of_eq
    change F.map (𝟙 c) = 𝟙 (F.obj c)
    exact F.map_id c

#print axioms native_equality_transport_constant_target_chain

end MathlibExtTest.NativeNerveHomotopyConstant

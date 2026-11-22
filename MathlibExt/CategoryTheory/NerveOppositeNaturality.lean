/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.NerveOpposite
public import MathlibExt.CategoryTheory.NerveCommonHom
public import Mathlib.CategoryTheory.Category.Cat.Op

/-!
# Naturality of the nerve–opposite isomorphism

For `H : C ⥤ D`, the simplicial isomorphism
`nerveOppositeSimplicialIso : nerve Cᵒᵖ ≅ opFunctor.obj (nerve C)`
is natural: pushing forward along `H` and then reversing agrees with
reversing and then pushing forward along `H.op`. Degreewise this is
`unop`/`op` commutation with `Functor.mapComposableArrows`.

Universe boundary: this API uses common object and morphism universes where
required by the pinned `nerveMap`/simplicial-set interface; this is an interface
limitation, not a mathematical restriction.

Nonclaims: no Grothendieck opposite theorem, no realization, cofinality,
homotopy, weak-equivalence, contraction, model-category, or KQ consequence.
-/

@[expose] public section

open CategoryTheory Opposite Simplicial

universe u v uSource vSource uTarget vTarget uObj vObj wHom

namespace CategoryTheory

variable {C D : Type u} [Category.{v} C] [Category.{v} D]

/-- Degreewise commutation of `unop` with postcomposition. -/
private theorem nerveOpposite_unop_mapComposableArrows
    {C : Type uSource} [Category.{vSource} C]
    {D : Type uTarget} [Category.{vTarget} D] (H : C ⥤ D) (n : ℕ)
    (S : ComposableArrows Cᵒᵖ n) :
    (H.mapComposableArrows n).obj S.unop =
      ((H.op.mapComposableArrows n).obj S).unop := by
  have h_obj : ∀ i : Fin (n + 1),
      ((H.mapComposableArrows n).obj S.unop).obj i =
        (((H.op.mapComposableArrows n).obj S).unop).obj i := fun i => by
    simp [ComposableArrows.unop_obj]
  refine ComposableArrows.ext h_obj (fun i hi => ?_)
  refine (conj_eqToHom_iff_heq _ _ (h_obj _) (h_obj _)).mpr ?_
  have hL : (H.mapComposableArrows n).obj S.unop = (S.unop ⋙ H) := rfl
  have hR : (H.op.mapComposableArrows n).obj S = (S ⋙ H.op) := rfl
  rw [hL, hR]
  simp only [ComposableArrows.map', ComposableArrows.unop_map, Functor.comp_map,
    Functor.op_map, Quiver.Hom.unop_op]
  refine heq_of_eq (congrArg (fun f => H.map (Quiver.Hom.unop f)) ?_)
  exact congrArg S.map (Subsingleton.elim _ _)

/-- Naturality of the nerve–opposite simplicial isomorphism. -/
theorem nerveOppositeSimplicialIso_naturality (H : C ⥤ D) :
    (nerveOppositeSimplicialIso C).hom ≫
        SimplicialObject.opFunctor.map (nerveMap H) =
      nerveMap H.op ≫ (nerveOppositeSimplicialIso D).hom := by
  ext Δ S
  obtain ⟨⟨n⟩⟩ := Δ
  simp only [NatTrans.comp_app, SimplicialObject.opFunctor_map_app,
    CategoryTheory.nerveMap_app]
  exact nerveOpposite_unop_mapComposableArrows H n S

/-- The nerve–opposite isomorphism is natural in the category. -/
noncomputable def nerveOppositeNatIso :
    Cat.opFunctor.{v, u} ⋙ nerveFunctor.{v, u} ≅
      nerveFunctor.{v, u} ⋙ SimplicialObject.opFunctor :=
  NatIso.ofComponents (fun C => nerveOppositeSimplicialIso C)
    (fun f => (nerveOppositeSimplicialIso_naturality f.toFunctor).symm)

/-- Component of `nerveOppositeNatIso` at `Cat.of C`. -/
@[simp]
theorem nerveOppositeNatIso_app (C : Type u) [Category.{v} C] :
    nerveOppositeNatIso.app (Cat.of C) = nerveOppositeSimplicialIso C :=
  rfl


section CommonNative

variable {A : Type (max uObj vObj)} [Category.{max vObj wHom} A]
  {B : Type uObj} [Category.{max vObj wHom} B]

/-- Reversing whole native common-Hom chains commutes with their original functor map. -/
theorem nerveOppositeSimplicialIso_nerveMapCommonHom_naturality (F : A ⥤ B) :
    (nerveOppositeSimplicialIso A).hom ≫
        SimplicialObject.opFunctor.map (nerveMapCommonHom.{uObj, vObj, wHom} F) =
      nerveMapCommonHom.{uObj, vObj, wHom} F.op ≫
        (nerveOppositeSimplicialIso B).hom := by
  ext Δ X
  obtain ⟨⟨n⟩⟩ := Δ
  change (F.mapComposableArrows n).obj X.unop =
    ((F.op.mapComposableArrows n).obj X).unop
  exact nerveOpposite_unop_mapComposableArrows F n X

end CommonNative

end CategoryTheory

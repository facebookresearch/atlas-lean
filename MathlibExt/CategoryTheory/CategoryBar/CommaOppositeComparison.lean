/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.CategoryBar.CommaRightComparison
public import MathlibExt.CategoryTheory.NerveOpposite
public import MathlibExt.CategoryTheory.CategoryBar.CommaLeftComparison

/-!
# Right-comma bar versus reversed left-comma replacement

For `F : C ⥤ D` and `d : D`, the right-comma bar at `commaCoeffR F d` identifies with the
opposite of simplicial replacement at `commaCoeffL F.op (op d)`. The bridge is the nerve
transport along the `rightOp` form of `costructuredArrowOpEquivalence F d`, flanked by the accepted
right-comma bar/nerve, nerve-opposite, and left-comma replacement/nerve comparisons. The
`F.op`/`op d` target is load-bearing: the same-direction schematic target is disproved by a
`Fin 2` degree-zero count.

Nonclaims: no Grothendieck naturality, no contraction, no homotopy, no realization, no KQ.
-/

@[expose] public section

open CategoryTheory Opposite Simplicial

universe u₁ v₁ u₂ v₂

namespace CategoryTheory

namespace CategoryBar

/-- Degreewise equivalence whiskering the opposite costructured/structured functors.

Round trips hold by comma `obj_ext`/`hom_ext` and `simp` through the `rightOp` and
`toStructuredArrow`/`toCostructuredArrow'` computation lemmas. -/
noncomputable def costructuredOppositeNerveEquiv
    {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    (F : C ⥤ D) (d : D) (n : ℕ) :
    ComposableArrows (CostructuredArrow F d) n ≃
      ComposableArrows ((StructuredArrow (op d) F.op)ᵒᵖ) n where
  toFun G := G ⋙ (CostructuredArrow.toStructuredArrow F d).rightOp
  invFun G := G ⋙ StructuredArrow.toCostructuredArrow' F d
  left_inv G := by
    have h_obj : ∀ i : Fin (n + 1),
        ((G ⋙ (CostructuredArrow.toStructuredArrow F d).rightOp) ⋙
          StructuredArrow.toCostructuredArrow' F d).obj i =
        G.obj i := by
      intro i
      refine CostructuredArrow.obj_ext _ _ rfl ?_
      unfold CostructuredArrow.toStructuredArrow
        StructuredArrow.toCostructuredArrow' Functor.rightOp
      simp
    refine ComposableArrows.ext h_obj (fun i hi => ?_)
    apply CostructuredArrow.hom_ext _ _
    unfold CostructuredArrow.toStructuredArrow
      StructuredArrow.toCostructuredArrow' Functor.rightOp
    simp only [Functor.comp_map, Functor.comp_obj, CostructuredArrow.comp_left,
      CostructuredArrow.homMk_left, StructuredArrow.homMk_right, Quiver.Hom.unop_op,
      eqToHom_refl, Category.comp_id]
    change (G.map _).left = 𝟙 _ ≫ (G.map _).left
    exact (Category.id_comp _).symm
  right_inv G := by
    have h_unop : ∀ i : Fin (n + 1),
        ((((G ⋙ StructuredArrow.toCostructuredArrow' F d) ⋙
          (CostructuredArrow.toStructuredArrow F d).rightOp).obj i).unop =
        (G.obj i).unop) := by
      intro i
      refine StructuredArrow.obj_ext _ _ rfl ?_
      unfold CostructuredArrow.toStructuredArrow
        StructuredArrow.toCostructuredArrow' Functor.rightOp
      simp
    have h_obj : ∀ i : Fin (n + 1),
        ((G ⋙ StructuredArrow.toCostructuredArrow' F d) ⋙
          (CostructuredArrow.toStructuredArrow F d).rightOp).obj i =
        G.obj i := fun i => by
      have h := h_unop i
      simpa using congrArg Opposite.op h
    refine ComposableArrows.ext h_obj (fun i hi => ?_)
    apply Quiver.Hom.unop_inj
    apply StructuredArrow.hom_ext _ _
    unfold CostructuredArrow.toStructuredArrow
      StructuredArrow.toCostructuredArrow' Functor.rightOp
    simp only [Functor.comp_map, Functor.comp_obj, unop_comp, StructuredArrow.comp_right,
      CostructuredArrow.homMk_left, StructuredArrow.homMk_right, Quiver.Hom.op_unop,
      Quiver.Hom.unop_op, eqToHom_refl, Category.comp_id]
    change StructuredArrow.Hom.right (G.map _).unop
      = StructuredArrow.Hom.right (G.map _).unop ≫ 𝟙 _
    exact (Category.comp_id _).symm

/-- Nerve transport along the opposite costructured/structured equivalence. -/
noncomputable def costructuredStructuredOppositeNerveIso
    {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    (F : C ⥤ D) (d : D) :
    nerve (CostructuredArrow F d) ≅
      nerve ((StructuredArrow (op d) F.op)ᵒᵖ) :=
  NatIso.ofComponents (fun Δ => (costructuredOppositeNerveEquiv F d (Δ.unop.len)).toIso) (by
    intro Δ₁ Δ₂ f
    ext X
    rfl)

/-- Right-comma bar as the opposite of left-comma simplicial replacement.

The `F.op`/`op d` target is load-bearing: the same-direction schematic target is disproved by a
`Fin 2` degree-zero count. -/
noncomputable def barRightCommaOppositeLeftIso
    {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    (F : C ⥤ D) (d : D) :
    categoryBar (C := C) (R := commaCoeffR F d) (L := unitCoeffL C)
      ≅ SimplicialObject.opFunctor.obj
          (simplicialReplacement (C := Cᵒᵖ) (commaCoeffL F.op (op d))) :=
  (barRightCommaSimplicialIso F d).trans
    ((costructuredStructuredOppositeNerveIso F d).trans
      ((nerveOppositeSimplicialIso _).trans
        (SimplicialObject.opFunctor.mapIso
          (commaReplacementNerveIso F.op (op d)).symm)))

end CategoryBar

end CategoryTheory

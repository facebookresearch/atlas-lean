/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  MathlibExt.AlgebraicTopology.SimplicialSet.LeftCommaBousfieldKanSource
public import MathlibExt.AlgebraicTopology.SimplicialSet.LeftCommaBousfieldKan
public import
  MathlibExt.AlgebraicTopology.SimplicialSet.RightCommaBousfieldKanSource
public import MathlibExt.AlgebraicTopology.SimplicialSet.RightCommaBousfieldKan
public import MathlibExt.CategoryTheory.NerveOpposite
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Basic
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Functor
import MathlibExt.CategoryTheory.ComposableArrows.Opposite

/-!
# Left-comma diagram versus the right-comma diagram for `F.op`

For `F : C ⥤ D`, the contravariant left-comma nerve diagram identifies, after
simplex reversal, with the right-comma nerve diagram for `F.op`. The bridge
promotes the static opposite comparison — the pattern of
`CategoryBar.barRightCommaOppositeLeftIso`, through the
structured/costructured opposite equivalence and the nerve-opposite
comparison — from fixed-`(F, d)` data to a natural isomorphism of
`Dᵒᵖ`-diagrams. The source projection and point maps commute with the
transport.

Nonclaims: no contraction, no homotopy, no realization, no weak-equivalence,
no homotopy-fiber, and no Quillen-Theorem-A claim.
-/

@[expose] public section

noncomputable section

open CategoryTheory Opposite Simplicial

namespace SSet

universe u v uD

section GenericOpposite

variable {C : Type u} {D : Type uD} [Category.{v} C] [Category.{v} D]

/-- Degreewise equivalence whiskering the structured/costructured opposite
functors.

This mirrors `CategoryBar.costructuredOppositeNerveEquiv` with the two sides
exchanged: round trips hold by comma `obj_ext`/`hom_ext` and `simp` through
the `rightOp` and `toCostructuredArrow`/`toStructuredArrow'` computation
lemmas. -/
noncomputable def structuredOppositeNerveEquiv
    {C : Type u} [Category.{v} C]
    {D : Type uD} [Category.{v} D]
    (F : C ⥤ D) (d : D) (n : ℕ) :
    ComposableArrows (StructuredArrow d F)ᵒᵖ n ≃
      ComposableArrows (CostructuredArrow F.op (op d)) n where
  toFun G := G ⋙ StructuredArrow.toCostructuredArrow F d
  invFun G := G ⋙ (CostructuredArrow.toStructuredArrow' F d).rightOp
  left_inv G := by
    have h_unop : ∀ i : Fin (n + 1),
        ((((G ⋙ StructuredArrow.toCostructuredArrow F d) ⋙
          (CostructuredArrow.toStructuredArrow' F d).rightOp).obj i).unop =
        (G.obj i).unop) := by
      intro i
      refine StructuredArrow.obj_ext _ _ rfl ?_
      unfold StructuredArrow.toCostructuredArrow
        CostructuredArrow.toStructuredArrow' Functor.rightOp
      simp
    have h_obj : ∀ i : Fin (n + 1),
        ((G ⋙ StructuredArrow.toCostructuredArrow F d) ⋙
          (CostructuredArrow.toStructuredArrow' F d).rightOp).obj i =
        G.obj i := fun i => by
      have h := h_unop i
      simpa using congrArg Opposite.op h
    refine ComposableArrows.ext h_obj (fun i hi => ?_)
    apply Quiver.Hom.unop_inj
    apply StructuredArrow.hom_ext _ _
    unfold StructuredArrow.toCostructuredArrow
      CostructuredArrow.toStructuredArrow' Functor.rightOp
    simp only [Functor.comp_map, Functor.comp_obj, unop_comp,
      StructuredArrow.comp_right, CostructuredArrow.homMk_left,
      StructuredArrow.homMk_right, Quiver.Hom.unop_op,
      eqToHom_refl, Category.comp_id]
    change StructuredArrow.Hom.right (G.map _).unop
      = StructuredArrow.Hom.right (G.map _).unop ≫ 𝟙 _
    exact (Category.comp_id _).symm
  right_inv G := by
    have h_obj : ∀ i : Fin (n + 1),
        ((G ⋙ (CostructuredArrow.toStructuredArrow' F d).rightOp) ⋙
          StructuredArrow.toCostructuredArrow F d).obj i =
        G.obj i := by
      intro i
      refine CostructuredArrow.obj_ext _ _ rfl ?_
      unfold StructuredArrow.toCostructuredArrow
        CostructuredArrow.toStructuredArrow' Functor.rightOp
      simp
    refine ComposableArrows.ext h_obj (fun i hi => ?_)
    apply CostructuredArrow.hom_ext _ _
    unfold StructuredArrow.toCostructuredArrow
      CostructuredArrow.toStructuredArrow' Functor.rightOp
    simp only [Functor.comp_map, Functor.comp_obj, CostructuredArrow.comp_left,
      CostructuredArrow.homMk_left, StructuredArrow.homMk_right,
      Quiver.Hom.unop_op, eqToHom_refl, Category.comp_id]
    change (G.map _).left = 𝟙 _ ≫ (G.map _).left
    exact (Category.id_comp _).symm

/-- Nerve transport along the structured/costructured opposite
equivalence. -/
noncomputable def structuredCostructuredOppositeNerveIso
    {C : Type u} [Category.{v} C]
    {D : Type uD} [Category.{v} D]
    (F : C ⥤ D) (d : D) :
    nerve (StructuredArrow d F)ᵒᵖ ≅
      nerve (CostructuredArrow F.op (op d)) :=
  NatIso.ofComponents
    (fun Δ => (structuredOppositeNerveEquiv.{u, v, uD} F d (Δ.unop.len)).toIso) (by
    intro Δ₁ Δ₂ f
    ext X
    rfl)

/-- Reversed left-comma nerves identify with right-comma nerves for `F.op`.

This is the per-object comparison: nerve reversal followed by transport
along `structuredArrowOpEquivalence`. -/
noncomputable def leftCommaOppositeNerveIso (F : C ⥤ D) (d : Dᵒᵖ) :
    SimplicialObject.opFunctor.obj (nerve (StructuredArrow d.unop F)) ≅
      nerve (CostructuredArrow F.op d) :=
  (nerveOppositeSimplicialIso _).symm.trans
    (structuredCostructuredOppositeNerveIso.{u, v, uD} F d.unop)

/-- Forward component of `leftCommaOppositeNerveIso`: reversal followed by
whiskering with the opposite-equivalence functor. -/
@[simp]
theorem leftCommaOppositeNerveIso_hom_app_mk (F : C ⥤ D) (d : Dᵒᵖ) (n : ℕ)
    (X : ComposableArrows (StructuredArrow d.unop F) n) :
    ((leftCommaOppositeNerveIso.{u, v, uD} F d).hom.app (op ⦋n⦌)) X =
      X.op ⋙ StructuredArrow.toCostructuredArrow F d.unop := by
  rfl

/-- The opposite-equivalence functor is natural in the comma point: pushing
forward along `g.op` after transporting agrees with transporting after
pushing forward along `g`. -/
private theorem toCostructuredArrow_map_square (F : C ⥤ D) {e e' : D}
    (g : e' ⟶ e) :
    StructuredArrow.toCostructuredArrow F e ⋙ CostructuredArrow.map g.op =
      (StructuredArrow.map g).op ⋙
        StructuredArrow.toCostructuredArrow F e' := by
  have h_obj : ∀ X : (StructuredArrow e F)ᵒᵖ,
      (StructuredArrow.toCostructuredArrow F e ⋙
        CostructuredArrow.map g.op).obj X =
        ((StructuredArrow.map g).op ⋙
          StructuredArrow.toCostructuredArrow F e').obj X := by
    intro X
    refine CostructuredArrow.obj_ext _ _ rfl ?_
    unfold StructuredArrow.toCostructuredArrow CostructuredArrow.map
      StructuredArrow.map Functor.op Comma.mapLeft Comma.mapRight
    simp only [Functor.const_obj_obj, Functor.const_map_app,
      CostructuredArrow.right_eq_id, Functor.comp_obj, CostructuredArrow.mk_left,
      CostructuredArrow.mk_right, CostructuredArrow.mk_hom_eq_self,
      StructuredArrow.left_eq_id, eqToHom_refl, unop_id,
      CategoryTheory.Functor.map_id, op_id, Category.id_comp]
    change (g ≫ (unop X).hom).op = (unop X).hom.op ≫ g.op
    exact op_comp
  refine CategoryTheory.Functor.ext h_obj (fun X Y φ => ?_)
  apply CostructuredArrow.hom_ext _ _
  have hEq : ∀ {x y : CostructuredArrow F.op (op e')} (h : x = y),
      (eqToHom h).left = eqToHom (congrArg CostructuredArrow.left h) := by
    intro x y h
    cases h
    rfl
  rw [CostructuredArrow.comp_left, CostructuredArrow.comp_left, hEq, hEq]
  have eX : congrArg CostructuredArrow.left (h_obj X) = rfl :=
    Subsingleton.elim _ _
  have eY : congrArg CostructuredArrow.left (h_obj Y).symm = rfl :=
    Subsingleton.elim _ _
  rw [eX, eY]
  unfold StructuredArrow.toCostructuredArrow CostructuredArrow.map
    StructuredArrow.map Functor.op Comma.mapLeft Comma.mapRight
  simp only [Functor.comp_map, Functor.comp_obj,
    CostructuredArrow.homMk_left, Quiver.Hom.unop_op, eqToHom_refl,
    Category.id_comp, Category.comp_id]

/-- The opposite-equivalence functor commutes with the comma projections. -/
private theorem toCostructuredArrow_proj_square (F : C ⥤ D) (d : Dᵒᵖ) :
    StructuredArrow.toCostructuredArrow F d.unop ⋙
        CostructuredArrow.proj F.op d =
      (StructuredArrow.proj d.unop F).op := by
  rfl

/-- The reversed left-comma diagram is the right-comma diagram for `F.op`.

This assembles the per-object opposite/reversal comparisons into a natural
isomorphism of `Dᵒᵖ`-diagrams. -/
noncomputable def leftCommaOppositeDiagramIso (F : C ⥤ D) :
    leftCommaNerveDiagram.{u, v, uD} F ⋙
      SimplicialObject.opFunctor ≅
      rightCommaNerveDiagram.{u, v, uD} F.op :=
  NatIso.ofComponents (fun d => leftCommaOppositeNerveIso.{u, v, uD} F d) (by
    intro d d' f
    ext Δ X
    obtain ⟨⟨n⟩⟩ := Δ
    set X' : ComposableArrows (StructuredArrow d.unop F) n := X with hXdef
    change ComposableArrows.op (X' ⋙ StructuredArrow.map f.unop) ⋙
        StructuredArrow.toCostructuredArrow F d'.unop =
      ((ComposableArrows.op X' ⋙
        StructuredArrow.toCostructuredArrow F d.unop) ⋙
        CostructuredArrow.map f)
    rw [ComposableArrows.op_mapFunctor]
    change X'.op ⋙ ((StructuredArrow.map f.unop).op ⋙
          StructuredArrow.toCostructuredArrow F d'.unop) =
        X'.op ⋙ (StructuredArrow.toCostructuredArrow F d.unop ⋙
          CostructuredArrow.map f)
    have hsq := toCostructuredArrow_map_square.{u, v, uD} F f.unop
    rw [Quiver.Hom.op_unop] at hsq
    exact congrArg (X'.op ⋙ ·) hsq.symm)

/-- Component of `leftCommaOppositeDiagramIso`. -/
@[simp]
theorem leftCommaOppositeDiagramIso_app (F : C ⥤ D) (d : Dᵒᵖ) :
    (leftCommaOppositeDiagramIso.{u, v, uD} F).app d =
      leftCommaOppositeNerveIso.{u, v, uD} F d :=
  rfl

end GenericOpposite

section NativeProjectionCompat

universe w

variable {C : Type (max u w)} {D : Type u}
  [Category.{max v w} C] [Category.{max v w} D]

/-- The source projections commute with the opposite transport. -/
theorem leftCommaProjectionOppositeCompatNative (F : C ⥤ D) (d : Dᵒᵖ) :
    ((leftCommaOppositeDiagramIso.{max u w, max v w, u} F).app d).hom ≫
        (rightCommaProjection.{u, v, w} F.op).app d =
      SimplicialObject.opFunctor.map ((leftCommaProjection.{max u w, max v w, u} F).app d) ≫
        (nerveOppositeSimplicialIso C).inv := by
  rw [leftCommaOppositeDiagramIso_app]
  ext Δ X
  obtain ⟨⟨n⟩⟩ := Δ
  set X' : ComposableArrows (StructuredArrow d.unop F) n := X with hXdef
  change ((ComposableArrows.op X' ⋙
      StructuredArrow.toCostructuredArrow F d.unop) ⋙
      CostructuredArrow.proj _ _) =
    ComposableArrows.op (X' ⋙ StructuredArrow.proj _ _)
  have hOp : ComposableArrows.op (X' ⋙ StructuredArrow.proj (d.unop) F) =
      ComposableArrows.op X' ⋙ (StructuredArrow.proj (d.unop) F).op :=
    ComposableArrows.op_mapFunctor _ _ _
  rw [hOp]
  change X'.op ⋙ (StructuredArrow.toCostructuredArrow F d.unop ⋙
        CostructuredArrow.proj _ _) =
      X'.op ⋙ (StructuredArrow.proj _ _).op
  exact congrArg (X'.op ⋙ ·) (toCostructuredArrow_proj_square.{max u w, max v w, u} F d)

end NativeProjectionCompat

section LegacyProjectionCompat

variable {C D : Type u} [Category.{v} C] [Category.{v} D]

/-- The original common-object projection square retains its former `.{u, v}` API. -/
theorem leftCommaProjection_opposite_compat (F : C ⥤ D) (d : Dᵒᵖ) :
    ((leftCommaOppositeDiagramIso F).app d).hom ≫
        (rightCommaProjection.{u, v, 0} F.op).app d =
      SimplicialObject.opFunctor.map ((leftCommaProjection F).app d) ≫
        (nerveOppositeSimplicialIso C).inv :=
  leftCommaProjectionOppositeCompatNative.{u, v, 0} F d

end LegacyProjectionCompat

section PointCompat

variable {C D : Type u} [Category.{0} C] [Category.{0} D]

/-- The point maps commute with the opposite transport, by terminality of
`Δ[0]`. -/
theorem leftCommaToPoint_opposite_compat (F : C ⥤ D) (d : Dᵒᵖ) :
    ((leftCommaOppositeDiagramIso.{u, 0, u} F).app d).hom ≫
        (rightCommaToPoint.{u, 0, 0} F.op).app d =
      SimplicialObject.opFunctor.map ((leftCommaToPoint F).app d) ≫
        stdSimplex.isTerminalObj₀.from _ :=
  stdSimplex.isTerminalObj₀.hom_ext _ _

end PointCompat

end SSet

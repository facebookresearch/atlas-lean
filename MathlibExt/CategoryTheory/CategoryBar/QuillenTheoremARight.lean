/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialSet.ToTopReversal
public import MathlibExt.CategoryTheory.NerveOppositeRealization
public import MathlibExt.CategoryTheory.CategoryBar.CommaOppositeComparison
public import MathlibExt.CategoryTheory.CategoryBar.QuillenTheoremA
public import MathlibExt.CategoryTheory.NerveCrossUniverse
public import MathlibExt.AlgebraicTopology.SimplicialSet.NerveEquivalenceWeakEquivalence
public import Mathlib.CategoryTheory.Category.ULift
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal

/-!
# Right-comma Quillen A for native nerve realization

These results relate the realized nerve map of a functor to its right-comma
categories. The right-comma criterion follows from the left-comma theorem,
the comma/opposite comparison, and canonical simplicial realization reversal.

The cross-universe criterion compares the original categories and native
nerve maps through the object-lift comparison, preserving independent object
and morphism universe levels.
-/

universe u v

@[expose] public section

noncomputable section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty Opposite
open scoped Simplicial

namespace SSet.OppositeRealization

/-- The actual op-equivalence preserves the chosen terminal simplicial set. -/
def opTerminalIso : SimplicialObject.opFunctor.obj (⊤_ SSet.{u}) ≅ (⊤_ SSet.{u}) := by
  letI : (SimplicialObject.opFunctor (C := Type u)).IsRightAdjoint :=
    (SimplicialObject.opEquivalence (C := Type u)).toAdjunction.isRightAdjoint
  exact PreservesTerminal.iso SimplicialObject.opFunctor

/-- The exact terminal maps also preserve and reflect the realization-weak property. -/
theorem realizationWeakEquivalences_op_terminal_iff (X : SSet.{u}) :
    SSet.realizationWeakEquivalences (terminal.from (SimplicialObject.opFunctor.obj X)) ↔
      SSet.realizationWeakEquivalences (terminal.from X) := by
  let q : X ⟶ (⊤_ SSet.{u}) := terminal.from X
  let e : SimplicialObject.opFunctor.obj (⊤_ SSet.{u}) ≅ (⊤_ SSet.{u}) := opTerminalIso
  have hq : SimplicialObject.opFunctor.map q ≫ e.hom =
      terminal.from (SimplicialObject.opFunctor.obj X) := terminal.hom_ext _ _
  rw [← hq]
  exact (cancel_right_of_respectsIso SSet.realizationWeakEquivalences
    (SimplicialObject.opFunctor.map q) e.hom).trans
    (realizationWeakEquivalences_op_map_iff q)

private theorem conull_mem_iff_of_iso {X Y : SSet.{u}} (e : X ≅ Y) :
    SSet.realizationWeakEquivalences (terminal.from X) ↔
      SSet.realizationWeakEquivalences (terminal.from Y) := by
  have hq : e.hom ≫ terminal.from Y = terminal.from X := terminal.hom_ext _ _
  rw [← hq]
  exact cancel_left_of_respectsIso SSet.realizationWeakEquivalences e.hom (terminal.from Y)

/-- General-Hom right-comma Quillen A, derived from the existing structured-arrow theorem. -/
theorem nerveMap_mem_of_costructuredArrow
    {C D : Type u} [Category.{v} C] [Category.{v} D] (F : C ⥤ D)
    (h : ∀ d : D, SSet.realizationWeakEquivalences
      (terminal.from (nerve (CostructuredArrow F d) : SSet.{max u v}))) :
    SSet.realizationWeakEquivalences (nerveMap F) := by
  apply (nerveMap_op_mem_iff F).mp
  apply CategoryTheory.nerveMap_mem_realizationWeakEquivalences_of_structuredArrow F.op
  intro d
  let d' : D := d.unop
  let K := StructuredArrow (op d') F.op
  let e : nerve (CostructuredArrow F d') ≅
      SimplicialObject.opFunctor.obj (nerve K) :=
    CategoryTheory.CategoryBar.costructuredStructuredOppositeNerveIso F d' ≪≫
      nerveOppositeSimplicialIso K
  have hk : SSet.realizationWeakEquivalences
      (terminal.from (SimplicialObject.opFunctor.obj (nerve K))) :=
    (conull_mem_iff_of_iso e).mp (h d')
  exact (realizationWeakEquivalences_op_terminal_iff (nerve K)).mp hk

end SSet.OppositeRealization

end

noncomputable section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty Opposite
open scoped Simplicial

attribute [local instance] CategoryTheory.uliftCategory

namespace SSet.OppositeRealization

/-- This comparison is proved degree by degree using the actual object-only lift. -/
private def objectLiftNerveIso (B : Type u) [Category.{v} B] :
    nerve (ULift.{v} B) ≅ nerve B where
  hom := nerveMapCross (ULift.downFunctor : ULift.{v} B ⥤ B)
  inv :=
    { app := fun _ => ↾fun sigma =>
        ((ULift.upFunctor : B ⥤ ULift.{v} B).mapComposableArrows _).obj sigma
      naturality := by
        intro n m f
        ext sigma
        apply ComposableArrows.ext (fun _ => rfl)
        intro i hi
        simp only [ComposableArrows.map',
          eqToHom_refl, Category.id_comp, Category.comp_id] }
  hom_inv_id := by
    ext n sigma
    change ((ULift.upFunctor : B ⥤ ULift.{v} B).mapComposableArrows n.unop.len).obj
        (((ULift.downFunctor : ULift.{v} B ⥤ B).mapComposableArrows n.unop.len).obj
          sigma) = sigma
    apply ComposableArrows.ext (fun _ => rfl)
    intro i hi
    simp only [ComposableArrows.map', Functor.mapComposableArrows_obj_map,
      eqToHom_refl, Category.id_comp, Category.comp_id]
  inv_hom_id := by
    ext n sigma
    change ((ULift.downFunctor : ULift.{v} B ⥤ B).mapComposableArrows n.unop.len).obj
        (((ULift.upFunctor : B ⥤ ULift.{v} B).mapComposableArrows n.unop.len).obj
          sigma) = sigma
    apply ComposableArrows.ext (fun _ => rfl)
    intro i hi
    simp only [ComposableArrows.map', Functor.mapComposableArrows_obj_map,
      eqToHom_refl, Category.id_comp, Category.comp_id]

/-- The cross map retains the exact functor action in every degree. -/
private theorem crossMap_app
    {A : Type (max u v)} [Category.{v} A] {B : Type u} [Category.{v} B]
    (F : A ⥤ B) (n : SimplexCategoryᵒᵖ) (sigma : (nerve A).obj n) :
    (nerveMapCross F).app n sigma = (F.mapComposableArrows n.unop.len).obj sigma := rfl

/-- Only the target objects are lifted; the original comma and nerve maps are retained. -/
theorem crossMap_mem_of_costructuredArrow
    {A : Type (max u v)} [Category.{v} A] {B : Type u} [Category.{v} B]
    (F : A ⥤ B)
    (h : ∀ b : B, SSet.realizationWeakEquivalences
      (terminal.from (nerve (CostructuredArrow F b) : SSet.{max u v}))) :
    SSet.realizationWeakEquivalences (nerveMapCross F) := by
  let U : B ⥤ ULift.{v} B := ULift.upFunctor
  let V : ULift.{v} B ⥤ B := ULift.downFunctor
  let FUp : A ⥤ ULift.{v} B := F ⋙ U
  have hUFull : U.Full :=
    inferInstanceAs ((ULift.equivalence (C := B) : B ≌ ULift.{v} B).functor.Full)
  have hUFaithful : U.Faithful :=
    inferInstanceAs ((ULift.equivalence (C := B) : B ≌ ULift.{v} B).functor.Faithful)
  have hUp : SSet.realizationWeakEquivalences (nerveMap FUp) := by
    apply nerveMap_mem_of_costructuredArrow FUp
    intro bUp
    rcases bUp with ⟨b⟩
    let P := CostructuredArrow.post F U b
    have hP : P.IsEquivalence :=
      @CostructuredArrow.isEquivalence_post _ _ _ _ _ _ b F U hUFull hUFaithful
    have hPW : SSet.realizationWeakEquivalences (nerveMap P) :=
      @CategoryTheory.nerveMap_mem_realizationWeakEquivalences_of_isEquivalence
        _ _ _ _ P hP
    let q := terminal.from (nerve (CostructuredArrow FUp (U.obj b)))
    have hq : nerveMap P ≫ q = terminal.from (nerve (CostructuredArrow F b)) :=
      terminal.hom_ext _ _
    have hc : SSet.realizationWeakEquivalences (nerveMap P ≫ q) := hq.symm ▸ h b
    exact SSet.realizationWeakEquivalences.of_precomp (nerveMap P) q hPW hc
  let e : nerve (ULift.{v} B) ≅ nerve B := objectLiftNerveIso B
  have hDown : SSet.realizationWeakEquivalences e.hom :=
    MorphismProperty.of_isIso SSet.realizationWeakEquivalences e.hom
  have hsquare : nerveMap FUp ≫ e.hom = nerveMapCross F := by
    change nerveMap FUp ≫ nerveMapCross V = nerveMapCross F
    refine (nerveMap_nerveMapCross_comp FUp V).trans ?_
    ext n sigma
    apply ComposableArrows.ext (fun _ => rfl)
    intro i hi
    simp only [ComposableArrows.map',
      eqToHom_refl, Category.id_comp, Category.comp_id]
  exact hsquare ▸ SSet.realizationWeakEquivalences.comp_mem
    (nerveMap FUp) e.hom hUp hDown

end SSet.OppositeRealization

end

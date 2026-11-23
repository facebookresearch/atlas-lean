/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialSet.BisimplicialRows
public import MathlibExt.CategoryTheory.NerveIsomorphismArrow
public import
  MathlibExt.KTheory.Exact.Quillen.QuillenStageGridStageProjection

import MathlibExt.KTheory.Exact.Quillen.QuillenStageGridQProjectionEquivalence
import Mathlib.CategoryTheory.Limits.Shapes.ConcreteCategory

/-!
# Fixed columns of the Quillen Stage-grid projection

At fixed inner nerve degree, the outer simplicial set of Stage-grid lift
chains is the pullback of the source map from the nerve of isomorphism arrows
in `QuillenQ C`.  The endpoint map extracts the Quillen simplex of the final
Stage in the chain.  The other pullback coordinate records the retained
Quillen simplex and the final agreement isomorphism.

The inverse keeps the supplied Stage chain, retains the final Quillen chain at
every inner vertex, and transports the final agreement backwards along the
Stage chain.  This file constructs only the pullback isomorphism and its
projection triangle.  It makes no rowwise or diagonal weak-equivalence,
outer-edgewise, pointed, loop-space, or Q/S comparison claim.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial
open CategoryTheory.ExactCategory
open CategoryTheory.Waldhausen.SConstruction
open SimplexCategory
open scoped Simplicial

universe v u

namespace AlgebraicKTheory

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]

/-- The canonical Waldhausen structure of the exact category in the original Stage-grid row comparisons. -/
local instance quillenStageGridStageProjectionRowsWaldhausenCategory :
    WaldhausenCategory C :=
  ExactCategory.waldhausenCategory C

/-- A weak Stage morphism induces a natural isomorphism between its extracted
Quillen simplices. -/
noncomputable def edgewiseStageQuillenSimplexIsoOfHom
    {a : SimplexCategory}
    {A B : StageWeakCategory C (edgewiseQ.obj a).len}
    (f : A ⟶ B) :
    (edgewiseStageQuillenSimplexFunctor C a).obj A ≅
      (edgewiseStageQuillenSimplexFunctor C a).obj B := by
  letI : IsIso ((edgewiseStageQuillenSimplexFunctor C a).map f) := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro k
    change IsIso
      ((QuillenQ.underlyingIso (edgewiseStageVertexIso f k)).hom)
    infer_instance
  exact asIso ((edgewiseStageQuillenSimplexFunctor C a).map f)

@[simp]
theorem edgewiseStageQuillenSimplexIsoOfHom_hom
    {a : SimplexCategory}
    {A B : StageWeakCategory C (edgewiseQ.obj a).len}
    (f : A ⟶ B) :
    (edgewiseStageQuillenSimplexIsoOfHom (C := C) f).hom =
      edgewiseStageQuillenSimplexMap f :=
  rfl

/-- At fixed inner degree `m`, extract the Quillen simplex of the final Stage
in an `m`-chain. -/
noncomputable def edgewiseStageWeakRowLast (m : ℕ) :
    SSet.simplicialRow (edgewiseStageWeakNerve C) (op ⦋m⦌) ⟶ NQ C where
  app a := ↾fun Z ↦
    (edgewiseStageQuillenSimplexFunctor C a.unop).obj
      (Z.obj (Fin.last m))
  naturality {a b} f := by
    ext Z
    exact Functor.congr_obj
      (edgewiseStageQuillenSimplexFunctor_reindex
        (C := C) f.unop)
      (Z.obj (Fin.last m))

@[simp]
theorem edgewiseStageWeakRowLast_app_apply (m : ℕ)
    (a : SimplexCategoryᵒᵖ) (Z : ComposableArrows
      (StageWeakCategory C (edgewiseQ.obj a.unop).len) m) :
    (ConcreteCategory.hom
      (X := (CategoryTheory.nerve
        (StageWeakCategory C (edgewiseQ.obj a.unop).len)).obj (op ⦋m⦌))
      (Y := (NQ C).obj a)
      ((edgewiseStageWeakRowLast (C := C) m).app a)) Z =
      (edgewiseStageQuillenSimplexFunctor C a.unop).obj
        (Z.obj (Fin.last m)) :=
  rfl

/-- Normalize a Stage chain by retaining one final Quillen simplex.  The
agreement at `i` is the extracted map from `i` to the final Stage followed by
the supplied final agreement. -/
private noncomputable def quillenStageGridLiftChainOfLastIso
    {a : SimplexCategory} {m : ℕ}
    (A : ComposableArrows
      (StageWeakCategory C (edgewiseQ.obj a).len) m)
    (q : QuillenQSimplex C a)
    (e : (edgewiseStageQuillenSimplexFunctor C a).obj
        (A.obj (Fin.last m)) ≅ q) :
    ComposableArrows (QuillenStageGridLift C a) m := by
  let E := edgewiseStageQuillenSimplexFunctor C a
  let agreement : ∀ i : Fin (m + 1),
      E.obj (A.obj i) ≅ q := fun i ↦
    (edgewiseStageQuillenSimplexIsoOfHom (C := C)
      (A.map (homOfLE (Fin.le_last i)))).trans e
  let obj : Fin (m + 1) → QuillenStageGridLift C a := fun i ↦
    ⟨{ left := A.obj i
       right := Discrete.mk q
       hom := (agreement i).hom }, by
      change IsIso ((agreement i).hom)
      infer_instance⟩
  exact
    { obj := obj
      map := fun {i j} f ↦ ObjectProperty.homMk
        { left := A.map f
          right := 𝟙 (Discrete.mk q)
          w := by
            change E.map (A.map f) ≫
                  (E.map (A.map (homOfLE (Fin.le_last j))) ≫ e.hom) =
                (E.map (A.map (homOfLE (Fin.le_last i))) ≫ e.hom) ≫
                  𝟙 q
            have hLast : f ≫ homOfLE (Fin.le_last j) =
                homOfLE (Fin.le_last i) :=
              Subsingleton.elim _ _
            rw [Category.comp_id, ← Category.assoc, ← E.map_comp,
              ← A.map_comp, hLast]
          }
      map_id := fun i ↦
        (quillenStageGridLift_hom_subsingleton (obj i) (obj i)).allEq _ _
      map_comp := fun f g ↦
        (quillenStageGridLift_hom_subsingleton _ _).allEq _ _ }

@[simp]
private theorem quillenStageGridLiftChainOfLastIso_obj_grid
    {a : SimplexCategory} {m : ℕ}
    (A : ComposableArrows
      (StageWeakCategory C (edgewiseQ.obj a).len) m)
    (q : QuillenQSimplex C a)
    (e : (edgewiseStageQuillenSimplexFunctor C a).obj
        (A.obj (Fin.last m)) ≅ q)
    (i : Fin (m + 1)) :
    ((quillenStageGridLiftChainOfLastIso (C := C) A q e).obj i).grid =
      A.obj i :=
  rfl

@[simp]
private theorem quillenStageGridLiftChainOfLastIso_obj_q
    {a : SimplexCategory} {m : ℕ}
    (A : ComposableArrows
      (StageWeakCategory C (edgewiseQ.obj a).len) m)
    (q : QuillenQSimplex C a)
    (e : (edgewiseStageQuillenSimplexFunctor C a).obj
        (A.obj (Fin.last m)) ≅ q)
    (i : Fin (m + 1)) :
    ((quillenStageGridLiftChainOfLastIso (C := C) A q e).obj i).q = q :=
  rfl

@[simp]
private theorem quillenStageGridLiftChainOfLastIso_last_agreementIso
    {a : SimplexCategory} {m : ℕ}
    (A : ComposableArrows
      (StageWeakCategory C (edgewiseQ.obj a).len) m)
    (q : QuillenQSimplex C a)
    (e : (edgewiseStageQuillenSimplexFunctor C a).obj
        (A.obj (Fin.last m)) ≅ q) :
    ((quillenStageGridLiftChainOfLastIso
      (C := C) A q e).obj (Fin.last m)).agreementIso = e := by
  apply Iso.ext
  change (edgewiseStageQuillenSimplexIsoOfHom (C := C)
      (A.map (homOfLE (Fin.le_last (Fin.last m))))).hom ≫ e.hom = e.hom
  rw [edgewiseStageQuillenSimplexIsoOfHom_hom,
    ← edgewiseStageQuillenSimplexFunctor_map]
  have hLast : homOfLE (Fin.le_last (Fin.last m)) = 𝟙 (Fin.last m) :=
    Subsingleton.elim _ _
  rw [hLast, A.map_id,
    (edgewiseStageQuillenSimplexFunctor C a).map_id,
    Category.id_comp]

@[simp]
private theorem quillenStageGridLiftChainOfLastIso_map_left
    {a : SimplexCategory} {m : ℕ}
    (A : ComposableArrows
      (StageWeakCategory C (edgewiseQ.obj a).len) m)
    (q : QuillenQSimplex C a)
    (e : (edgewiseStageQuillenSimplexFunctor C a).obj
        (A.obj (Fin.last m)) ≅ q)
    {i j : Fin (m + 1)} (f : i ⟶ j) :
    ((quillenStageGridLiftChainOfLastIso (C := C) A q e).map f).hom.left =
      A.map f :=
  rfl

@[simp]
private theorem quillenStageGridLiftChainOfLastIso_gridProjection
    {a : SimplexCategory} {m : ℕ}
    (A : ComposableArrows
      (StageWeakCategory C (edgewiseQ.obj a).len) m)
    (q : QuillenQSimplex C a)
    (e : (edgewiseStageQuillenSimplexFunctor C a).obj
        (A.obj (Fin.last m)) ≅ q) :
    ((quillenStageGridProjection C a).mapComposableArrows m).obj
        (quillenStageGridLiftChainOfLastIso (C := C) A q e) = A := by
  apply Functor.hext
  · intro i
    rfl
  · intro i j f
    apply heq_of_eq
    rfl

private theorem sigmaIso_transport_source
    {D : Type u} [Category.{v} D] {X X' Y : D}
    (h : X = X') (e : X ≅ Y) :
    (⟨X, Y, e⟩ : Σ A B : D, A ≅ B) =
      ⟨X', Y, (eqToIso h).symm.trans e⟩ := by
  subst X'
  simp

private theorem sigmaIso_cancel_source_transport
    {D : Type u} [Category.{v} D]
    (s : Σ X Y : D, X ≅ Y) {A : D} (h : A = s.1) :
    (⟨s.1, s.2.1,
      (eqToIso h).symm.trans ((eqToIso h).trans s.2.2)⟩ :
        Σ X Y : D, X ≅ Y) = s := by
  rcases s with ⟨X, Y, e⟩
  change (⟨X, Y,
    (eqToIso h).symm.trans ((eqToIso h).trans e)⟩ :
      Σ X Y : D, X ≅ Y) = (⟨X, Y, e⟩ : Σ X Y : D, X ≅ Y)
  congr 2
  apply Iso.ext
  simp

private theorem quillenStageGridLiftChainOfLastIso_sigma_congr
    {a : SimplexCategory} {m : ℕ}
    (A : ComposableArrows
      (StageWeakCategory C (edgewiseQ.obj a).len) m)
    (s t : Σ X Y : QuillenQSimplex C a, X ≅ Y)
    (hst : s = t)
    (hs : (edgewiseStageQuillenSimplexFunctor C a).obj
        (A.obj (Fin.last m)) = s.1)
    (ht : (edgewiseStageQuillenSimplexFunctor C a).obj
        (A.obj (Fin.last m)) = t.1) :
    quillenStageGridLiftChainOfLastIso (C := C) A s.2.1
        ((eqToIso hs).trans s.2.2) =
      quillenStageGridLiftChainOfLastIso (C := C) A t.2.1
        ((eqToIso ht).trans t.2.2) := by
  subst t
  have hProof : hs = ht := Subsingleton.elim _ _
  cases hProof
  rfl

private theorem isomorphismArrowNerveObjEquiv_whiskerLeft
    {a b : SimplexCategory} (f : b ⟶ a)
    (X Y : ComposableArrows (QuillenQ C) a.len) (e : X ≅ Y) :
    CategoryTheory.isomorphismArrowNerveObjEquiv
        (D := QuillenQ C) (op b)
        (((CategoryTheory.isomorphismArrowNerveObjEquiv
          (D := QuillenQ C) (op a)).symm ⟨X, Y, e⟩).whiskerLeft
            (SimplexCategory.toCat.map f).toFunctor) =
      ⟨(edgewiseQuillenSimplexReindex (C := C) f).obj X,
        (edgewiseQuillenSimplexReindex (C := C) f).obj Y,
        (edgewiseQuillenSimplexReindex (C := C) f).mapIso e⟩ := by
  change CategoryTheory.isomorphismArrowNerveObjEquiv
      (D := QuillenQ C) (op b)
      ((CategoryTheory.isomorphismArrowComposableOfIso
        (QuillenQ C) X Y e).whiskerLeft
          (SimplexCategory.toCat.map f).toFunctor) = _
  have hWhisker :
      (CategoryTheory.isomorphismArrowComposableOfIso
          (QuillenQ C) X Y e).whiskerLeft
          (SimplexCategory.toCat.map f).toFunctor =
        CategoryTheory.isomorphismArrowComposableOfIso (QuillenQ C)
          ((edgewiseQuillenSimplexReindex (C := C) f).obj X)
          ((edgewiseQuillenSimplexReindex (C := C) f).obj Y)
          ((edgewiseQuillenSimplexReindex (C := C) f).mapIso e) := by
    rfl
  rw [hWhisker]
  change (CategoryTheory.isomorphismArrowNerveObjEquiv
      (D := QuillenQ C) (op b))
      ((CategoryTheory.isomorphismArrowNerveObjEquiv
        (D := QuillenQ C) (op b)).symm
        ⟨(edgewiseQuillenSimplexReindex (C := C) f).obj X,
          (edgewiseQuillenSimplexReindex (C := C) f).obj Y,
          (edgewiseQuillenSimplexReindex (C := C) f).mapIso e⟩) = _
  exact Equiv.apply_symm_apply _ _

/-- The final lift in an inner chain determines an outer chain of isomorphism
arrows: extracted final Stage simplex, retained simplex, and agreement. -/
private noncomputable def quillenStageGridRowLastAgreement (m : ℕ) :
    SSet.simplicialRow (quillenStageGridNerve C) (op ⦋m⦌) ⟶
      CategoryTheory.nerve
        (CategoryTheory.IsomorphismArrow (QuillenQ C)) where
  app a := ↾fun Z ↦
    (CategoryTheory.isomorphismArrowNerveObjEquiv
      (D := QuillenQ C) a).symm
      ⟨(edgewiseStageQuillenSimplexFunctor C a.unop).obj
          (Z.obj (Fin.last m)).grid,
        (Z.obj (Fin.last m)).q,
        (Z.obj (Fin.last m)).agreementIso⟩
  naturality {a b} f := by
    ext Z
    let X := Z.obj (Fin.last m)
    change (CategoryTheory.isomorphismArrowNerveObjEquiv
        (D := QuillenQ C) b).symm
          ⟨(edgewiseStageQuillenSimplexFunctor C b.unop).obj
              ((reindexQuillenStageGridLift (C := C) f.unop).obj X).grid,
            ((reindexQuillenStageGridLift (C := C) f.unop).obj X).q,
            ((reindexQuillenStageGridLift
              (C := C) f.unop).obj X).agreementIso⟩ =
      ((CategoryTheory.isomorphismArrowNerveObjEquiv
        (D := QuillenQ C) a).symm
          ⟨(edgewiseStageQuillenSimplexFunctor C a.unop).obj X.grid,
            X.q, X.agreementIso⟩).whiskerLeft
          (SimplexCategory.toCat.map f.unop).toFunctor
    apply (CategoryTheory.isomorphismArrowNerveObjEquiv
      (D := QuillenQ C) b).injective
    rw [Equiv.apply_symm_apply]
    let X' := (reindexQuillenStageGridLift (C := C) f.unop).obj X
    let eNew :
        (edgewiseStageQuillenSimplexFunctor C b.unop).obj
            ((edgewiseStageWeakReindex (C := C) f.unop).obj X.grid) ≅
          (edgewiseQuillenSimplexReindex (C := C) f.unop).obj X.q := by
      change (edgewiseStageQuillenSimplexFunctor C b.unop).obj X'.grid ≅
        X'.q
      exact X'.agreementIso
    change (⟨(edgewiseStageQuillenSimplexFunctor C b.unop).obj
          ((edgewiseStageWeakReindex (C := C) f.unop).obj X.grid),
        (edgewiseQuillenSimplexReindex (C := C) f.unop).obj X.q,
        eNew⟩ :
        Σ P Q : ComposableArrows (QuillenQ C) b.unop.len, P ≅ Q) = _
    let hSource :
        (edgewiseStageQuillenSimplexFunctor C b.unop).obj
            ((edgewiseStageWeakReindex (C := C) f.unop).obj X.grid) =
          (edgewiseQuillenSimplexReindex (C := C) f.unop).obj
            ((edgewiseStageQuillenSimplexFunctor C a.unop).obj X.grid) := by
      exact Functor.congr_obj
        (edgewiseStageQuillenSimplexFunctor_reindex
          (C := C) f.unop) X.grid
    rw [isomorphismArrowNerveObjEquiv_whiskerLeft (C := C)]
    calc
      _ = ⟨(edgewiseQuillenSimplexReindex (C := C) f.unop).obj
              ((edgewiseStageQuillenSimplexFunctor C a.unop).obj X.grid),
            (edgewiseQuillenSimplexReindex (C := C) f.unop).obj X.q,
            (eqToIso hSource).symm.trans eNew⟩ :=
        sigmaIso_transport_source hSource eNew
      _ = _ := by
        congr 2
        apply Iso.ext
        ext k
        let hF := edgewiseStageQuillenSimplexFunctor_reindex
          (C := C) f.unop
        let hD := quillenQSimplexDiscreteInclusion_reindex
          (C := C) f.unop
        have hSource_eq : hSource = Functor.congr_obj hF X.grid :=
          Subsingleton.elim _ _
        rw [hSource_eq]
        change (eqToIso (Functor.congr_obj hF X.grid)).inv.app k ≫
            (((eqToHom hF).app X.grid ≫
              (edgewiseQuillenSimplexReindex (C := C) f.unop).map
                X.obj.hom ≫
              (eqToHom hD).app X.obj.right).app k) =
          ((edgewiseQuillenSimplexReindex (C := C) f.unop).map
            X.obj.hom).app k
        simp only [NatTrans.comp_app, eqToHom_app]
        have hHom :
            ((eqToHom hF).app X.grid).app k =
              (eqToIso (Functor.congr_obj hF X.grid)).hom.app k := by
          change ((eqToHom hF).app X.grid).app k =
            (eqToHom (Functor.congr_obj hF X.grid)).app k
          exact congrArg (fun η ↦ η.app k) (eqToHom_app hF X.grid)
        have hPre :
            (eqToIso (Functor.congr_obj hF X.grid)).inv.app k ≫
                ((eqToHom hF).app X.grid).app k = 𝟙 _ := by
          rw [hHom]
          exact (eqToIso
            (Functor.congr_obj hF X.grid)).inv_hom_id_app k
        simp only [← Category.assoc]
        simp only [eqToHom_app] at hPre ⊢
        rw [hPre, Category.id_comp]
        let p :
            (((edgewiseQuillenSimplexReindex (C := C) f.unop).obj X.q).obj k) =
              (((edgewiseQuillenSimplexReindex (C := C) f.unop).obj X.q).obj k) := by
          exact congrArg (fun q ↦ q.obj k)
            (Functor.congr_obj hD X.obj.right)
        change ((edgewiseQuillenSimplexReindex (C := C) f.unop).map
            X.obj.hom).app k ≫ eqToHom p =
          ((edgewiseQuillenSimplexReindex (C := C) f.unop).map
            X.obj.hom).app k
        have hPost : eqToHom p = 𝟙 _ := by
          simp
        exact (congrArg (fun g ↦
            ((edgewiseQuillenSimplexReindex (C := C) f.unop).map
              X.obj.hom).app k ≫ g) hPost).trans
          (Category.comp_id _)

private theorem quillenStageGridRowLastAgreement_condition (m : ℕ) :
    (SSet.simplicialTransposeFunctor.map
        (quillenStageGridStageProjectionNerve (C := C))).app (op ⦋m⦌) ≫
        edgewiseStageWeakRowLast (C := C) m =
      quillenStageGridRowLastAgreement (C := C) m ≫
        CategoryTheory.isomorphismArrowNerveSource (QuillenQ C) := by
  ext a Z
  let X := Z.obj (Fin.last m)
  change (edgewiseStageQuillenSimplexFunctor C a.unop).obj X.grid =
    ((CategoryTheory.isomorphismArrowSource
      (QuillenQ C)).mapComposableArrows a.unop.len).obj
      ((CategoryTheory.isomorphismArrowNerveObjEquiv
        (D := QuillenQ C) a).symm
          ⟨(edgewiseStageQuillenSimplexFunctor C a.unop).obj X.grid,
            X.q, X.agreementIso⟩)
  rw [← CategoryTheory.isomorphismArrowNerveObjEquiv_source]
  rw [Equiv.apply_symm_apply]

/-- Canonical map from a fixed inner Stage-grid column to the pullback of the
isomorphism-arrow source projection. -/
private noncomputable def quillenStageGridStageProjectionRowToPullback
    (m : ℕ) :
    SSet.simplicialRow (quillenStageGridNerve C) (op ⦋m⦌) ⟶
      pullback (edgewiseStageWeakRowLast (C := C) m)
        (CategoryTheory.isomorphismArrowNerveSource (QuillenQ C)) :=
  pullback.lift
    ((SSet.simplicialTransposeFunctor.map
      (quillenStageGridStageProjectionNerve (C := C))).app (op ⦋m⦌))
    (quillenStageGridRowLastAgreement (C := C) m)
    (quillenStageGridRowLastAgreement_condition (C := C) m)

@[reassoc (attr := simp)]
private theorem quillenStageGridStageProjectionRowToPullback_fst
    (m : ℕ) :
    quillenStageGridStageProjectionRowToPullback (C := C) m ≫
        pullback.fst (edgewiseStageWeakRowLast (C := C) m)
          (CategoryTheory.isomorphismArrowNerveSource (QuillenQ C)) =
      (SSet.simplicialTransposeFunctor.map
        (quillenStageGridStageProjectionNerve (C := C))).app (op ⦋m⦌) :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
private theorem quillenStageGridStageProjectionRowToPullback_snd
    (m : ℕ) :
    quillenStageGridStageProjectionRowToPullback (C := C) m ≫
        pullback.snd (edgewiseStageWeakRowLast (C := C) m)
          (CategoryTheory.isomorphismArrowNerveSource (QuillenQ C)) =
      quillenStageGridRowLastAgreement (C := C) m :=
  pullback.lift_snd _ _ _

private noncomputable def quillenStageGridStageProjectionRowPullbackDataEquiv
    (m : ℕ) (a : SimplexCategoryᵒᵖ) :
    (pullback (edgewiseStageWeakRowLast (C := C) m)
      (CategoryTheory.isomorphismArrowNerveSource
        (QuillenQ C))).obj a ≃
      {p :
          (CategoryTheory.nerve
              (StageWeakCategory C (edgewiseQ.obj a.unop).len)).obj (op ⦋m⦌) ×
            (CategoryTheory.nerve
              (CategoryTheory.IsomorphismArrow (QuillenQ C))).obj a //
        (edgewiseStageWeakRowLast (C := C) m).app a p.1 =
          (CategoryTheory.isomorphismArrowNerveSource
            (QuillenQ C)).app a p.2} :=
  ((pullbackObjIso
      (edgewiseStageWeakRowLast (C := C) m)
      (CategoryTheory.isomorphismArrowNerveSource (QuillenQ C)) a).trans
    (Types.pullbackIsoPullback
      ((edgewiseStageWeakRowLast (C := C) m).app a)
      ((CategoryTheory.isomorphismArrowNerveSource
        (QuillenQ C)).app a))).toEquiv

@[simp]
private theorem quillenStageGridStageProjectionRowPullbackDataEquiv_fst
    (m : ℕ) (a : SimplexCategoryᵒᵖ)
    (z : (pullback (edgewiseStageWeakRowLast (C := C) m)
      (CategoryTheory.isomorphismArrowNerveSource
        (QuillenQ C))).obj a) :
    ((quillenStageGridStageProjectionRowPullbackDataEquiv
      (C := C) m a z).1).1 =
      (pullback.fst (edgewiseStageWeakRowLast (C := C) m)
        (CategoryTheory.isomorphismArrowNerveSource
          (QuillenQ C))).app a z := by
  unfold quillenStageGridStageProjectionRowPullbackDataEquiv
  change
    (((Types.pullbackIsoPullback
      ((edgewiseStageWeakRowLast (C := C) m).app a)
      ((CategoryTheory.isomorphismArrowNerveSource
        (QuillenQ C)).app a)).hom
      ((pullbackObjIso
        (edgewiseStageWeakRowLast (C := C) m)
        (CategoryTheory.isomorphismArrowNerveSource
          (QuillenQ C)) a).hom z)).1).1 = _
  rw [Types.pullbackIsoPullback_hom_fst]
  exact ConcreteCategory.congr_hom
    (pullbackObjIso_hom_comp_fst
      (edgewiseStageWeakRowLast (C := C) m)
      (CategoryTheory.isomorphismArrowNerveSource (QuillenQ C)) a) z

@[simp]
private theorem quillenStageGridStageProjectionRowPullbackDataEquiv_snd
    (m : ℕ) (a : SimplexCategoryᵒᵖ)
    (z : (pullback (edgewiseStageWeakRowLast (C := C) m)
      (CategoryTheory.isomorphismArrowNerveSource
        (QuillenQ C))).obj a) :
    ((quillenStageGridStageProjectionRowPullbackDataEquiv
      (C := C) m a z).1).2 =
      (pullback.snd (edgewiseStageWeakRowLast (C := C) m)
        (CategoryTheory.isomorphismArrowNerveSource
          (QuillenQ C))).app a z := by
  unfold quillenStageGridStageProjectionRowPullbackDataEquiv
  change
    (((Types.pullbackIsoPullback
      ((edgewiseStageWeakRowLast (C := C) m).app a)
      ((CategoryTheory.isomorphismArrowNerveSource
        (QuillenQ C)).app a)).hom
      ((pullbackObjIso
        (edgewiseStageWeakRowLast (C := C) m)
        (CategoryTheory.isomorphismArrowNerveSource
          (QuillenQ C)) a).hom z)).1).2 = _
  rw [Types.pullbackIsoPullback_hom_snd]
  exact ConcreteCategory.congr_hom
    (pullbackObjIso_hom_comp_snd
      (edgewiseStageWeakRowLast (C := C) m)
      (CategoryTheory.isomorphismArrowNerveSource (QuillenQ C)) a) z

private noncomputable def quillenStageGridStageProjectionRowOfPullbackData
    (m : ℕ) (a : SimplexCategoryᵒᵖ)
    (d : {p :
          (SSet.simplicialRow (edgewiseStageWeakNerve C)
              (op ⦋m⦌)).obj a ×
            (CategoryTheory.nerve
              (CategoryTheory.IsomorphismArrow (QuillenQ C))).obj a //
        (edgewiseStageWeakRowLast (C := C) m).app a p.1 =
          (CategoryTheory.isomorphismArrowNerveSource
            (QuillenQ C)).app a p.2}) :
    (SSet.simplicialRow (quillenStageGridNerve C) (op ⦋m⦌)).obj a := by
  let A := d.1.1
  let W := d.1.2
  let s := CategoryTheory.isomorphismArrowNerveObjEquiv
    (D := QuillenQ C) a W
  let h :
      (edgewiseStageQuillenSimplexFunctor C a.unop).obj
          (A.obj (Fin.last m)) = s.1 := by
    have hd :
        (edgewiseStageQuillenSimplexFunctor C a.unop).obj
            (A.obj (Fin.last m)) =
          (CategoryTheory.isomorphismArrowNerveSource
            (QuillenQ C)).app a W := d.2
    exact hd.trans
      (CategoryTheory.isomorphismArrowNerveObjEquiv_source
        (D := QuillenQ C) a W).symm
  exact quillenStageGridLiftChainOfLastIso (C := C) A s.2.1
    ((eqToIso h).trans s.2.2)

/-- Decode pullback data by retaining its target Q-chain and transporting its
isomorphism across the pullback equality at the final Stage. -/
private noncomputable def quillenStageGridStageProjectionRowPullbackInverse
    (m : ℕ) (a : SimplexCategoryᵒᵖ)
    (z : (pullback (edgewiseStageWeakRowLast (C := C) m)
      (CategoryTheory.isomorphismArrowNerveSource
        (QuillenQ C))).obj a) :
    (SSet.simplicialRow (quillenStageGridNerve C) (op ⦋m⦌)).obj a :=
  quillenStageGridStageProjectionRowOfPullbackData (C := C) m a
    (quillenStageGridStageProjectionRowPullbackDataEquiv
      (C := C) m a z)

private theorem quillenStageGridLiftChainOfLastIso_projection
    {a : SimplexCategory} {m : ℕ}
    (Z : ComposableArrows (QuillenStageGridLift C a) m) :
    quillenStageGridLiftChainOfLastIso (C := C)
        (((quillenStageGridProjection C a).mapComposableArrows m).obj Z)
        (Z.obj (Fin.last m)).q
        (Z.obj (Fin.last m)).agreementIso = Z := by
  let A := ((quillenStageGridProjection C a).mapComposableArrows m).obj Z
  let q := (Z.obj (Fin.last m)).q
  let e := (Z.obj (Fin.last m)).agreementIso
  let L := quillenStageGridLiftChainOfLastIso (C := C) A q e
  let hObj : ∀ i : Fin (m + 1), L.obj i = Z.obj i := fun i ↦ by
    let g := Z.map (homOfLE (Fin.le_last i))
    apply ObjectProperty.FullSubcategory.ext
    change ({
      left := (Z.obj i).grid
      right := Discrete.mk q
      hom := ((edgewiseStageQuillenSimplexFunctor C a).map g.hom.left ≫
        e.hom) } : QuillenStageGridAgreement C a) =
      { left := (Z.obj i).obj.left
        right := (Z.obj i).obj.right
        hom := (Z.obj i).obj.hom }
    rw [Comma.mk.injEq]
    let hq : (Z.obj i).q = (Z.obj (Fin.last m)).q :=
      Discrete.eq_of_hom g.hom.right
    have hRight : Discrete.mk q = (Z.obj i).obj.right := by
      change Discrete.mk (Z.obj (Fin.last m)).q =
        Discrete.mk (Z.obj i).q
      exact congrArg Discrete.mk hq.symm
    refine ⟨rfl, hRight, ?_⟩
    have hMap :
        (quillenQSimplexDiscreteInclusion C a).map g.hom.right =
          eqToHom hq := by
      rcases g.hom.right with ⟨hg⟩
      rfl
    rw [show e.hom = (Z.obj (Fin.last m)).obj.hom from
      QuillenStageGridLift.agreementIso_hom (Z.obj (Fin.last m))]
    rw [g.hom.w, hMap]
    exact (comp_eqToHom_heq_iff (Z.obj i).obj.hom
      (Z.obj i).obj.hom hq).2 (HEq.rfl)
  refine CategoryTheory.Functor.ext hObj (h_map := ?_)
  intro i j f
  exact (quillenStageGridLift_hom_subsingleton _ _).allEq _ _

private theorem quillenStageGridStageProjectionRowPullbackInverse_forward
    (m : ℕ) (a : SimplexCategoryᵒᵖ)
    (Z : (SSet.simplicialRow (quillenStageGridNerve C)
      (op ⦋m⦌)).obj a) :
    quillenStageGridStageProjectionRowPullbackInverse (C := C) m a
        ((quillenStageGridStageProjectionRowToPullback
          (C := C) m).app a Z) = Z := by
  let z := (quillenStageGridStageProjectionRowToPullback
    (C := C) m).app a Z
  let d := quillenStageGridStageProjectionRowPullbackDataEquiv
    (C := C) m a z
  have hA : d.1.1 =
      ((quillenStageGridProjection C a.unop).mapComposableArrows m).obj Z := by
    rw [quillenStageGridStageProjectionRowPullbackDataEquiv_fst]
    have hfst := NatTrans.congr_app
      (pullback.lift_fst
        ((SSet.simplicialTransposeFunctor.map
          (quillenStageGridStageProjectionNerve (C := C))).app (op ⦋m⦌))
        (quillenStageGridRowLastAgreement (C := C) m)
        (quillenStageGridRowLastAgreement_condition (C := C) m)) a
    exact ConcreteCategory.congr_hom
      hfst Z
  have hW : d.1.2 =
      (CategoryTheory.isomorphismArrowNerveObjEquiv
        (D := QuillenQ C) a).symm
        ⟨(edgewiseStageQuillenSimplexFunctor C a.unop).obj
            (Z.obj (Fin.last m)).grid,
          (Z.obj (Fin.last m)).q,
          (Z.obj (Fin.last m)).agreementIso⟩ := by
    rw [quillenStageGridStageProjectionRowPullbackDataEquiv_snd]
    have hsnd := NatTrans.congr_app
      (pullback.lift_snd
        ((SSet.simplicialTransposeFunctor.map
          (quillenStageGridStageProjectionNerve (C := C))).app (op ⦋m⦌))
        (quillenStageGridRowLastAgreement (C := C) m)
        (quillenStageGridRowLastAgreement_condition (C := C) m)) a
    exact ConcreteCategory.congr_hom
      hsnd Z
  let A0 := ((quillenStageGridProjection C a.unop).mapComposableArrows m).obj Z
  let W0 := (CategoryTheory.isomorphismArrowNerveObjEquiv
    (D := QuillenQ C) a).symm
    ⟨(edgewiseStageQuillenSimplexFunctor C a.unop).obj
        (Z.obj (Fin.last m)).grid,
      (Z.obj (Fin.last m)).q,
      (Z.obj (Fin.last m)).agreementIso⟩
  let d0 :
      {p :
          (SSet.simplicialRow (edgewiseStageWeakNerve C)
              (op ⦋m⦌)).obj a ×
            (CategoryTheory.nerve
              (CategoryTheory.IsomorphismArrow (QuillenQ C))).obj a //
        (edgewiseStageWeakRowLast (C := C) m).app a p.1 =
          (CategoryTheory.isomorphismArrowNerveSource
            (QuillenQ C)).app a p.2} :=
    ⟨⟨A0, W0⟩, by
      have hc := ConcreteCategory.congr_hom
        (NatTrans.congr_app
          (quillenStageGridRowLastAgreement_condition
            (C := C) m) a) Z
      exact hc⟩
  have hd : d0 = d := by
    apply Subtype.ext
    exact Prod.ext hA.symm hW.symm
  have hDecode := congrArg
    (quillenStageGridStageProjectionRowOfPullbackData (C := C) m a) hd
  unfold quillenStageGridStageProjectionRowPullbackInverse
  change quillenStageGridStageProjectionRowOfPullbackData
      (C := C) m a d = Z
  rw [← hDecode]
  let t0 : Σ X Y : QuillenQSimplex C a.unop, X ≅ Y :=
    ⟨(edgewiseStageQuillenSimplexFunctor C a.unop).obj
        (Z.obj (Fin.last m)).grid,
      (Z.obj (Fin.last m)).q,
      (Z.obj (Fin.last m)).agreementIso⟩
  let s0 := CategoryTheory.isomorphismArrowNerveObjEquiv
    (D := QuillenQ C) a W0
  let h0 :
      (edgewiseStageQuillenSimplexFunctor C a.unop).obj
          (A0.obj (Fin.last m)) = s0.1 := by
    have hc := d0.2
    change (edgewiseStageQuillenSimplexFunctor C a.unop).obj
        (A0.obj (Fin.last m)) =
      ((CategoryTheory.isomorphismArrowSource
        (QuillenQ C)).mapComposableArrows a.unop.len).obj W0 at hc
    exact hc.trans
      (CategoryTheory.isomorphismArrowNerveObjEquiv_source
        (D := QuillenQ C) a W0).symm
  let ht :
      (edgewiseStageQuillenSimplexFunctor C a.unop).obj
          (A0.obj (Fin.last m)) = t0.1 := rfl
  change quillenStageGridLiftChainOfLastIso (C := C) A0 s0.2.1
      ((eqToIso h0).trans s0.2.2) = Z
  have hFirst := quillenStageGridLiftChainOfLastIso_sigma_congr
    A0 s0 t0
      (Equiv.apply_symm_apply
        (CategoryTheory.isomorphismArrowNerveObjEquiv
          (D := QuillenQ C) a) t0) h0 ht
  rw [hFirst]
  dsimp only [t0, A0]
  have he : (eqToIso ht).trans (Z.obj (Fin.last m)).agreementIso =
      (Z.obj (Fin.last m)).agreementIso := by
    apply Iso.ext
    have htrfl : ht = rfl := Subsingleton.elim _ _
    have hId : (eqToIso ht).hom = 𝟙 _ := by
      cases htrfl
      rfl
    rw [Iso.trans_hom, hId]
    change 𝟙 ((edgewiseStageQuillenSimplexFunctor C a.unop).obj
        (Z.obj (Fin.last m)).grid) ≫
      (Z.obj (Fin.last m)).agreementIso.hom =
        (Z.obj (Fin.last m)).agreementIso.hom
    rw [Category.id_comp]
  rw [he]
  exact quillenStageGridLiftChainOfLastIso_projection Z

private theorem quillenStageGridStageProjectionRowPullback_forward_inverse
    (m : ℕ) (a : SimplexCategoryᵒᵖ)
    (z : (pullback (edgewiseStageWeakRowLast (C := C) m)
      (CategoryTheory.isomorphismArrowNerveSource
        (QuillenQ C))).obj a) :
    (quillenStageGridStageProjectionRowToPullback (C := C) m).app a
        (quillenStageGridStageProjectionRowPullbackInverse
          (C := C) m a z) = z := by
  let d := quillenStageGridStageProjectionRowPullbackDataEquiv
    (C := C) m a z
  let A := d.1.1
  let W := d.1.2
  let s := CategoryTheory.isomorphismArrowNerveObjEquiv
    (D := QuillenQ C) a W
  let h :
      (edgewiseStageQuillenSimplexFunctor C a.unop).obj
          (A.obj (Fin.last m)) = s.1 := by
    have hd :
        (edgewiseStageQuillenSimplexFunctor C a.unop).obj
            (A.obj (Fin.last m)) =
          (CategoryTheory.isomorphismArrowNerveSource
            (QuillenQ C)).app a W := d.2
    exact hd.trans
      (CategoryTheory.isomorphismArrowNerveObjEquiv_source
        (D := QuillenQ C) a W).symm
  let e := (eqToIso h).trans s.2.2
  let L : (SSet.simplicialRow (quillenStageGridNerve C)
      (op ⦋m⦌)).obj a :=
    quillenStageGridLiftChainOfLastIso (C := C) A s.2.1 e
  have hInv :
      quillenStageGridStageProjectionRowPullbackInverse (C := C) m a z = L :=
    rfl
  rw [hInv]
  have hAgreement :
      (quillenStageGridRowLastAgreement (C := C) m).app a L = W := by
    apply (CategoryTheory.isomorphismArrowNerveObjEquiv
      (D := QuillenQ C) a).injective
    change (CategoryTheory.isomorphismArrowNerveObjEquiv
        (D := QuillenQ C) a)
          ((CategoryTheory.isomorphismArrowNerveObjEquiv
            (D := QuillenQ C) a).symm
            ⟨(edgewiseStageQuillenSimplexFunctor C a.unop).obj
                (L.obj (Fin.last m)).grid,
              (L.obj (Fin.last m)).q,
              (L.obj (Fin.last m)).agreementIso⟩) =
      (CategoryTheory.isomorphismArrowNerveObjEquiv
        (D := QuillenQ C) a) W
    rw [Equiv.apply_symm_apply]
    change (⟨(edgewiseStageQuillenSimplexFunctor C a.unop).obj
          (A.obj (Fin.last m)), s.2.1,
        (L.obj (Fin.last m)).agreementIso⟩ :
          Σ X Y : QuillenQSimplex C a.unop, X ≅ Y) = s
    have hLast : (L.obj (Fin.last m)).agreementIso = e := by
      change ((quillenStageGridLiftChainOfLastIso
        (C := C) A s.2.1 e).obj (Fin.last m)).agreementIso = e
      exact quillenStageGridLiftChainOfLastIso_last_agreementIso A s.2.1 e
    rw [hLast]
    calc
      _ = ⟨s.1, s.2.1, (eqToIso h).symm.trans e⟩ :=
        sigmaIso_transport_source h e
      _ = s := by
        change ⟨s.1, s.2.1,
          (eqToIso h).symm.trans ((eqToIso h).trans s.2.2)⟩ = s
        exact sigmaIso_cancel_source_transport s h
  apply (quillenStageGridStageProjectionRowPullbackDataEquiv
    (C := C) m a).injective
  apply Subtype.ext
  apply Prod.ext
  · rw [quillenStageGridStageProjectionRowPullbackDataEquiv_fst]
    have hfst := NatTrans.congr_app
      (quillenStageGridStageProjectionRowToPullback_fst
        (C := C) m) a
    change (pullback.fst (edgewiseStageWeakRowLast (C := C) m)
        (CategoryTheory.isomorphismArrowNerveSource
          (QuillenQ C))).app a
          ((quillenStageGridStageProjectionRowToPullback
            (C := C) m).app a L) = A
    let projected : ComposableArrows
        (StageWeakCategory C (edgewiseQ.obj a.unop).len) m :=
      ((quillenStageGridProjection C a.unop).mapComposableArrows m).obj L
    have hFirst : (pullback.fst (edgewiseStageWeakRowLast (C := C) m)
        (CategoryTheory.isomorphismArrowNerveSource (QuillenQ C))).app a
          ((quillenStageGridStageProjectionRowToPullback
            (C := C) m).app a L) = projected :=
      ConcreteCategory.congr_hom hfst L
    have hSecond : projected = A :=
      quillenStageGridLiftChainOfLastIso_gridProjection A s.2.1 e
    exact hFirst.trans hSecond
  · rw [quillenStageGridStageProjectionRowPullbackDataEquiv_snd]
    have hsnd := NatTrans.congr_app
      (quillenStageGridStageProjectionRowToPullback_snd
        (C := C) m) a
    change (pullback.snd (edgewiseStageWeakRowLast (C := C) m)
        (CategoryTheory.isomorphismArrowNerveSource
          (QuillenQ C))).app a
          ((quillenStageGridStageProjectionRowToPullback
            (C := C) m).app a L) = W
    calc
      _ = (quillenStageGridRowLastAgreement (C := C) m).app a L :=
        ConcreteCategory.congr_hom hsnd L
      _ = W := hAgreement

/-- The original Stage-grid row equivalence with its actual pullback, retaining both original inverses. -/
@[no_expose]
noncomputable def quillenStageGridStageProjectionRowPullbackObjEquiv
    (m : ℕ) (a : SimplexCategoryᵒᵖ) :
    (SSet.simplicialRow (quillenStageGridNerve C) (op ⦋m⦌)).obj a ≃
      (pullback (edgewiseStageWeakRowLast (C := C) m)
        (CategoryTheory.isomorphismArrowNerveSource
          (QuillenQ C))).obj a where
  toFun := (quillenStageGridStageProjectionRowToPullback
    (C := C) m).app a
  invFun := quillenStageGridStageProjectionRowPullbackInverse
    (C := C) m a
  left_inv := quillenStageGridStageProjectionRowPullbackInverse_forward
    (C := C) m a
  right_inv := quillenStageGridStageProjectionRowPullback_forward_inverse
    (C := C) m a

/-- The fixed-inner-degree Stage-grid column is the base change of the source
map from the nerve of isomorphism arrows in `QuillenQ C`. -/
noncomputable def quillenStageGridStageProjectionRowPullbackIso
    (m : ℕ) :
    SSet.simplicialRow (quillenStageGridNerve C) (op ⦋m⦌) ≅
      pullback (edgewiseStageWeakRowLast (C := C) m)
        (CategoryTheory.isomorphismArrowNerveSource (QuillenQ C)) :=
  NatIso.ofComponents
    (fun a ↦ (quillenStageGridStageProjectionRowPullbackObjEquiv
      (C := C) m a).toIso)
    (by
      intro a b f
      exact (quillenStageGridStageProjectionRowToPullback
        (C := C) m).naturality f)

/-- The pullback isomorphism followed by the first projection is literally the
fixed-column Stage projection. -/
@[reassoc]
theorem quillenStageGridStageProjectionRowPullbackIso_hom_fst
    (m : ℕ) :
    (quillenStageGridStageProjectionRowPullbackIso (C := C) m).hom ≫
        pullback.fst
          (edgewiseStageWeakRowLast (C := C) m)
          (CategoryTheory.isomorphismArrowNerveSource (QuillenQ C)) =
      (SSet.simplicialTransposeFunctor.map
        (quillenStageGridStageProjectionNerve (C := C))).app (op ⦋m⦌) := by
  change quillenStageGridStageProjectionRowToPullback (C := C) m ≫
      pullback.fst
        (edgewiseStageWeakRowLast (C := C) m)
        (CategoryTheory.isomorphismArrowNerveSource (QuillenQ C)) = _
  exact quillenStageGridStageProjectionRowToPullback_fst (C := C) m

/-- The inverse pullback isomorphism recovers the supplied Stage chain under
the fixed-column Stage projection. -/
@[reassoc]
theorem quillenStageGridStageProjectionRowPullbackIso_inv_stageProjection
    (m : ℕ) :
    (quillenStageGridStageProjectionRowPullbackIso (C := C) m).inv ≫
        (SSet.simplicialTransposeFunctor.map
          (quillenStageGridStageProjectionNerve (C := C))).app (op ⦋m⦌) =
      pullback.fst
        (edgewiseStageWeakRowLast (C := C) m)
        (CategoryTheory.isomorphismArrowNerveSource (QuillenQ C)) := by
  rw [← quillenStageGridStageProjectionRowPullbackIso_hom_fst]
  simp

end AlgebraicKTheory

end

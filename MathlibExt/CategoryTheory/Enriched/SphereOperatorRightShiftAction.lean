/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module
public import MathlibExt.CategoryTheory.Enriched.SphereOperatorRightTensor
public import MathlibExt.CategoryTheory.Enriched.SphereOperatorActionRecovery
public import MathlibExt.CategoryTheory.Enriched.SphereOperatorCoefficientAlgebra
public import MathlibExt.CategoryTheory.Enriched.CotensorCoefficientAction

/-!
# Actions of right shifts on enriched sphere operators

The full coend shift and its coefficient actions are constructed over arbitrary
symmetric enriched monoidal index data. The original generator, block braid,
transpose, and scalar-cotensor maps retain their complete source equations.
Orthogonal right shifts specialize these constructions.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
noncomputable section

open CategoryTheory MonoidalCategory BraidedCategory Limits
open CategoryTheory.Enriched CategoryTheory.Enriched.SphereOperator
open CategoryTheory.EnrichedFunctorCat
open scoped MonoidalClosed

namespace CategoryTheory.Enriched.SphereOperator.RightShift
universe uV vV uI vI

open CategoryTheory.Enriched CategoryTheory.Enriched.SphereOperator

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [SymmetricCategory V] [MonoidalClosed V]
  {I : Type uI} [Category.{vI} I] [MonoidalCategory I]
  [EnrichedOrdinaryCategory V I] [SymmetricCategory I]
  (d : EnrichedMonoidalCategoryData V I) (S : EnrichedFunctor V I V)
  (L : EnrichedFunctor.LaxMonoidalData d
    (MonoidalClosed.enrichedMonoidalCategoryDataSelf V) S)
  [∀ n k : I, HasCoproduct (weightedCoend.relations (weight d n k) S)]
  [∀ n k : I, HasCoproduct (weightedCoend.objects (weight d n k) S)]
  [∀ n k : I, HasCoequalizer (weightedCoend.leftMap (weight d n k) S)
    (weightedCoend.rightMap (weight d n k) S)]

/-- The existing full coend endofunctor selects the original right tensor. -/
abbrev shift (r : I) :
    EnrichedFunctorCat V (OperatorIndex d S L) ⥤ EnrichedFunctorCat V (OperatorIndex d S L) :=
  EnrichedFunctorCat.restriction (GenericRightTensor.indexShift d S L r)

/-- The original coefficient-first action retains the entire sphere object. -/
def action (F : EnrichedFunctorCat V (OperatorIndex d S L))
    (n k a : I) (f : a ⊗ n ⟶ k) :
    S.obj a ⊗ F.toEnrichedFunctor.obj ⟨n⟩ ⟶ F.toEnrichedFunctor.obj ⟨k⟩ :=
  (β_ (S.obj a) (F.toEnrichedFunctor.obj ⟨n⟩)).hom ≫
    MonoidalClosed.uncurry (coefficientHom d S n k a f ≫ F.toEnrichedFunctor.map ⟨n⟩ ⟨k⟩)

omit [SymmetricCategory I] in
/-- The original coefficient braid converts the complete right action. -/
theorem action_eq_braid (F : EnrichedFunctorCat V (OperatorIndex d S L))
    (n k a : I) (f : a ⊗ n ⟶ k) :
    action d S L F n k a f =
      (β_ (S.obj a) (F.toEnrichedFunctor.obj ⟨n⟩)).hom ≫
        coefficientAction d S L F n k a f := by
  unfold action coefficientAction
  rw [MonoidalClosed.uncurry_natural_left]

omit [SymmetricCategory I] in
/-- The whole original coend generator moves through the genuine shift. -/
theorem coefficientHom_shift (r n k a : I) (f : a ⊗ n ⟶ k) :
    coefficientHom d S n k a f ≫ GenericRightTensor.hom d S r n k =
      coefficientHom d S (n ⊗ r) (k ⊗ r) a (GenericRightTensor.label r n k a f) := by
  let u := (λ_ (S.obj a)).inv
  let p := eHomEquiv V f ⊗ₘ 𝟙 (S.obj a)
  let j := weightedCoend.ι (weight d n k) S a
  let t := GenericRightTensor.hom d S r n k
  let p' := eHomEquiv V (GenericRightTensor.label r n k a f) ⊗ₘ 𝟙 (S.obj a)
  let j' := weightedCoend.ι (weight d (n ⊗ r) (k ⊗ r)) S a
  have h : p ≫ j ≫ t = p' ≫ j' :=
    GenericRightTensor.hom_point_generator d S r n k a f
  change ((u ≫ p) ≫ j) ≫ t = (u ≫ p') ≫ j'
  exact (Category.assoc (u ≫ p) j t).trans
    ((Category.assoc u p (j ≫ t)).trans
      ((congrArg (fun q => u ≫ q) h).trans (Category.assoc u p' j').symm))

omit [SymmetricCategory I] in
/-- Every original index arrow and complete coefficient action survives restriction. -/
theorem shift_action (F : EnrichedFunctorCat V (OperatorIndex d S L))
    (r n k a : I) (f : a ⊗ n ⟶ k) :
    action d S L ((shift d S L r).obj F) n k a f =
      action d S L F (n ⊗ r) (k ⊗ r) a (GenericRightTensor.label r n k a f) := by
  let q := coefficientHom d S n k a f
  let t := GenericRightTensor.hom d S r n k
  let q' := coefficientHom d S (n ⊗ r) (k ⊗ r) a (GenericRightTensor.label r n k a f)
  let p := F.toEnrichedFunctor.map
    (⟨n ⊗ r⟩ : OperatorIndex d S L) (⟨k ⊗ r⟩ : OperatorIndex d S L)
  have hq : q ≫ t = q' := coefficientHom_shift d S r n k a f
  have hp : q ≫ (t ≫ p) = q' ≫ p :=
    (Category.assoc q t p).symm.trans (congrArg (fun z => z ≫ p) hq)
  change (β_ (S.obj a) (F.toEnrichedFunctor.obj ⟨n ⊗ r⟩)).hom ≫
      MonoidalClosed.uncurry (q ≫ (t ≫ p)) =
    (β_ (S.obj a) (F.toEnrichedFunctor.obj ⟨n ⊗ r⟩)).hom ≫
      MonoidalClosed.uncurry (q' ≫ p)
  exact congrArg (fun z => (β_ (S.obj a) (F.toEnrichedFunctor.obj ⟨n ⊗ r⟩)).hom ≫
    MonoidalClosed.uncurry z) hp

omit [SymmetricCategory I] in
/-- Postcomposition uses the actual full original restricted index functor. -/
theorem action_postcompose (F : EnrichedFunctorCat V (OperatorIndex d S L))
    (n k l a : I) (f : a ⊗ n ⟶ k) (g : k ⟶ l) :
    action d S L F n k a f ≫
        ((indexRestriction d S L).obj F).toEnrichedFunctor.toOrdinaryFunctor.map g =
      action d S L F n l a (f ≫ g) := by
  let b := (β_ (S.obj a) (F.toEnrichedFunctor.obj ⟨n⟩)).hom
  let p := coefficientAction d S L F n k a f
  let q := ((indexRestriction d S L).obj F).toEnrichedFunctor.toOrdinaryFunctor.map g
  have hLeft := congrArg (fun z => z ≫ q) (action_eq_braid d S L F n k a f)
  have hMiddle := congrArg (fun z => b ≫ z)
    (coefficientAction_postcompose d S L F n k l a f g)
  exact hLeft.trans ((Category.assoc b p q).trans
    (hMiddle.trans (action_eq_braid d S L F n l a (f ≫ g)).symm))

omit d S L in
/-- Both original index blocks are exchanged with their actual associators. -/
def blockSwap (r n a : I) : ((n ⊗ r) ⊗ a) ≅ ((n ⊗ a) ⊗ r) :=
  (α_ n r a) ≪≫ whiskerLeftIso n (β_ r a) ≪≫ (α_ n a r).symm

omit d S L in
/-- The inverse keeps the original reverse block braid. -/
theorem blockSwap_inv (r n a : I) :
    (blockSwap r n a).inv = (α_ n a r).hom ≫
      (n ◁ (β_ a r).hom) ≫ (α_ n r a).inv := by
  change ((α_ n a r).hom ≫ (n ◁ (β_ r a).inv)) ≫ (α_ n r a).inv = _
  rw [← SymmetricCategory.braiding_swap_eq_inv_braiding r a, Category.assoc]

omit d S L in
/-- Every original stabilization label is its original braid followed by the block swap. -/
theorem blockSwap_label (r n a : I) :
    GenericRightTensor.label r n (n ⊗ a) a (β_ a n).hom =
      (β_ a (n ⊗ r)).hom ≫ (blockSwap r n a).hom := by
  change (α_ a n r).inv ≫ ((β_ a n).hom ▷ r) =
    (β_ a (n ⊗ r)).hom ≫ (α_ n r a).hom ≫
      (n ◁ (β_ r a).hom) ≫ (α_ n a r).inv
  rw [braiding_tensor_right_hom]
  simp only [Category.assoc, Iso.inv_hom_id_assoc, ← whiskerLeft_comp_assoc,
    SymmetricCategory.symmetry, whiskerLeft_id, Category.id_comp, Iso.hom_inv_id, Category.comp_id]

/-- The original full transpose of the coefficient-first action. -/
def adjoint (F : EnrichedFunctorCat V (OperatorIndex d S L))
    (n k a : I) (f : a ⊗ n ⟶ k) :
    F.toEnrichedFunctor.obj ⟨n⟩ ⟶ (ihom (S.obj a)).obj (F.toEnrichedFunctor.obj ⟨k⟩) :=
  MonoidalClosed.curry (action d S L F n k a f)

omit [SymmetricCategory I] in
/-- The complete transpose keeps the actual target-index arrow. -/
theorem adjoint_postcompose (F : EnrichedFunctorCat V (OperatorIndex d S L))
    (n k l a : I) (f : a ⊗ n ⟶ k) (g : k ⟶ l) :
    adjoint d S L F n k a f ≫ (ihom (S.obj a)).map
        (((indexRestriction d S L).obj F).toEnrichedFunctor.toOrdinaryFunctor.map g) =
      adjoint d S L F n l a (f ≫ g) := by
  exact (MonoidalClosed.curry_natural_right _ _).symm.trans
    (congrArg MonoidalClosed.curry (action_postcompose d S L F n k l a f g))

/-- All source, shift and coefficient labels keep the whole original stabilization transpose. -/
theorem shift_adjoint (F : EnrichedFunctorCat V (OperatorIndex d S L)) (r n a : I) :
    adjoint d S L ((shift d S L r).obj F) n (n ⊗ a) a (β_ a n).hom =
      adjoint d S L F (n ⊗ r) ((n ⊗ r) ⊗ a) a (β_ a (n ⊗ r)).hom ≫
        (ihom (S.obj a)).map
          (((indexRestriction d S L).obj F).toEnrichedFunctor.toOrdinaryFunctor.map
            (blockSwap r n a).hom) := by
  have hShift := shift_action d S L F r n (n ⊗ a) a (β_ a n).hom
  have hLabel := congrArg (action d S L F (n ⊗ r) ((n ⊗ a) ⊗ r) a)
    (blockSwap_label r n a)
  have hCurry := congrArg MonoidalClosed.curry (hShift.trans hLabel)
  have hTarget := adjoint_postcompose d S L F (n ⊗ r) ((n ⊗ r) ⊗ a)
    ((n ⊗ a) ⊗ r) a (β_ a (n ⊗ r)).hom (blockSwap r n a).hom
  exact hCurry.trans hTarget.symm


omit [SymmetricCategory I] in
/-- The actual scalar cotensor action retains the entire coefficient shuffle and evaluation. -/
theorem cotensor_action (F : EnrichedFunctorCat V (OperatorIndex d S L)) (M : V)
    (n k a : I) (f : a ⊗ n ⟶ k) :
    action d S L (cotensorObject M F) n k a f = MonoidalClosed.curry
      (MonoidalCategory.CoefficientShuffle.map M (S.obj a)
        ((ihom M).obj (F.toEnrichedFunctor.obj ⟨n⟩)) ≫
      (S.obj a ◁ (ihom.ev M).app (F.toEnrichedFunctor.obj ⟨n⟩)) ≫ action d S L F n k a f) := by
  unfold action
  rw [MonoidalClosed.uncurry_natural_left, MonoidalClosed.uncurry_natural_left]
  exact EnrichedFunctor.CotensorCoefficientAction.action M F.toEnrichedFunctor
    (⟨n⟩ : OperatorIndex d S L) ⟨k⟩ (S.obj a) (coefficientHom d S n k a f)

end CategoryTheory.Enriched.SphereOperator.RightShift

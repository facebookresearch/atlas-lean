/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Orthogonal.FunctionSpectrum.ShiftOmega
import MathlibExt.AlgebraicTopology.Spectra.Orthogonal.SphereOneComparison
import MathlibExt.CategoryTheory.Enriched.SphereOperatorSourceNaturality
import MathlibExt.CategoryTheory.Enriched.ScalarCorners
import MathlibExt.CategoryTheory.Monoidal.Closed.CoefficientShuffleNaturality

/-!
# The original orthogonal stabilization map to the loop of a right shift

Every continuous coefficient label commutes with the complete right-degree
structure map. The proof retains the original late-first sphere product,
the actual three-block exchange, and the full native enriched action.
Uncurrying and the scalar coefficient shuffle give the genuine enriched
map from an operator diagram to the sphere cotensor of its right shift.
The actual first representation-sphere isomorphism then gives the map to
the native one-sphere loop. All source and added degrees, including zero,
remain unrestricted.

These are the original structure maps of MMSS Construction 2.1, Theorem 2.2
and Example 4.4 (December 30, 1999 preprint, pages 9 and 12–13), with the
Omega transposes of Definition 8.4 and the full-family extension. The
identification of the right shift with the actual module function object
from a free sphere is a separate source comparison; it is not supplied as
a premise to the action-exchange or delooping proofs here.
-/

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
noncomputable section

open CategoryTheory MonoidalCategory BraidedCategory Limits HomotopicalAlgebra
open CategoryTheory.Enriched CategoryTheory.Enriched.SphereOperator
open CategoryTheory.EnrichedFunctorCat CategoryTheory.Spectra
open HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK
open scoped MonoidalClosed CGWH.modelCategory

namespace PointedCGWH.Spectra.Orthogonal.FunctionSpectrum.Delooping.Internal

universe uV vV uI vI

private theorem arrowBraidShuffle {V : Type uV} [Category.{vV} V]
    [MonoidalCategory V] [SymmetricCategory V] (X A B : V) :
    (α_ X A B).inv ≫ ((β_ A X).inv ▷ B) ≫ (β_ B (A ⊗ X)).inv =
      (X ◁ (β_ A B).hom) ≫ (β_ (B ⊗ A) X).inv ≫ (α_ B A X).hom := by
  rw [← SymmetricCategory.braiding_swap_eq_inv_braiding A X,
    ← SymmetricCategory.braiding_swap_eq_inv_braiding B (A ⊗ X),
    ← SymmetricCategory.braiding_swap_eq_inv_braiding (B ⊗ A) X]
  simpa only [braiding_tensor_left_hom, braiding_tensor_right_hom, Category.assoc,
    Iso.inv_hom_id, Category.comp_id] using (yang_baxter X A B)

private theorem curriedCompositionTransport {V : Type uV} [Category.{vV} V]
    [MonoidalCategory V] [BraidedCategory V] [MonoidalClosed V]
    {A B C X Y Z H₀ H₁ H₂ : V}
    (p : A ⟶ H₀) (q : B ⟶ H₁) (r : C ⟶ H₂)
    (u : H₀ ⟶ (ihom X).obj Y) (v : H₁ ⟶ (ihom Y).obj Z)
    (w : H₂ ⟶ (ihom X).obj Z) (c : H₀ ⊗ H₁ ⟶ H₂) (μ : B ⊗ A ⟶ C)
    (hMap : c ≫ w = (u ⊗ₘ v) ≫ eComp V X Y Z)
    (hSource : (p ⊗ₘ q) ≫ c = (β_ A B).hom ≫ μ ≫ r) :
    ((p ≫ u) ⊗ₘ (q ≫ v)) ≫ eComp V X Y Z = (β_ A B).hom ≫ μ ≫ r ≫ w := by
  rw [← tensorHom_comp_tensorHom p q u v, Category.assoc,
    ← hMap, ← Category.assoc, hSource]
  simp only [Category.assoc]

private theorem scalarActionExchange {V : Type uV} [Category.{vV} V]
    [MonoidalCategory V] [BraidedCategory V]
    (R A X Y Z U W T : V)
    (μ : R ⊗ A ⟶ U) (ν : A ⊗ R ⟶ W) (s : W ⟶ U)
    (p : U ⊗ X ⟶ T) (q : W ⊗ X ⟶ T)
    (f : A ⊗ X ⟶ Y) (rN : R ⊗ X ⟶ Z) (rK : R ⊗ Y ⟶ T) (g : A ⊗ Z ⟶ T)
    (hL : (μ ▷ X) ≫ p = (α_ R A X).hom ≫ (R ◁ f) ≫ rK)
    (hR : (ν ▷ X) ≫ q = (α_ A R X).hom ≫ (A ◁ rN) ≫ g)
    (hs : (β_ R A).hom ≫ ν ≫ s = μ) (hq : q = (s ▷ X) ≫ p) :
    (R ◁ f) ≫ rK =
      NativeOmegaPreparation.CoefficientShuffle.map R A X ≫ (A ◁ rN) ≫ g := by
  have hc := congrArg (fun z : R ⊗ A ⟶ U => (z ▷ X) ≫ p) hs
  simp only [comp_whiskerRight, Category.assoc] at hc
  apply (cancel_epi (α_ R A X).hom).1
  simp only [NativeOmegaPreparation.CoefficientShuffle.map, Category.assoc,
    Iso.hom_inv_id_assoc]
  rw [← hL, ← hR, hq]
  exact hc.symm

private theorem coefficientCurrySquare {V : Type uV} [Category.{vV} V]
    [MonoidalCategory V] [BraidedCategory V] [MonoidalClosed V]
    (M A X X' Y Y' : V) (f : A ⊗ X ⟶ Y) (g : A ⊗ X' ⟶ Y')
    (p : X ⟶ (ihom M).obj X') (q : Y ⟶ (ihom M).obj Y')
    (h : (M ◁ f) ≫ MonoidalClosed.uncurry q =
      NativeOmegaPreparation.CoefficientShuffle.map M A X ≫
        (A ◁ MonoidalClosed.uncurry p) ≫ g) :
    f ≫ q = (A ◁ p) ≫ MonoidalClosed.curry
      (NativeOmegaPreparation.CoefficientShuffle.map M A ((ihom M).obj X') ≫
        (A ◁ (ihom.ev M).app X') ≫ g) := by
  apply MonoidalClosed.uncurry_injective
  rw [MonoidalClosed.uncurry_natural_left, MonoidalClosed.uncurry_natural_left,
    MonoidalClosed.uncurry_curry]
  rw [reassoc_of% NativeOmegaPreparation.CoefficientShuffle.naturality_third M A p]
  simp only [← whiskerLeft_comp_assoc]
  rw [← MonoidalClosed.uncurry_eq]
  exact h

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

open RightShift.Internal

omit [SymmetricCategory I] in
/-- Every complete coefficient action composes with the actual late-first sphere product. -/
theorem action_comp (F : EnrichedFunctorCat V (OperatorIndex d S L))
    (n k l a b : I) (f : a ⊗ n ⟶ k) (g : b ⊗ k ⟶ l) :
    (L.mu b a ▷ F.toEnrichedFunctor.obj ⟨n⟩) ≫
        action d S L F n l (b ⊗ a) ((α_ b a n).hom ≫ (b ◁ f) ≫ g) =
      (α_ (S.obj b) (S.obj a) (F.toEnrichedFunctor.obj ⟨n⟩)).hom ≫
        (S.obj b ◁ action d S L F n k a f) ≫ action d S L F k l b g := by
  let A := S.obj a
  let B := S.obj b
  let C := S.obj (b ⊗ a)
  let X := F.toEnrichedFunctor.obj (⟨n⟩ : OperatorIndex d S L)
  let Y := F.toEnrichedFunctor.obj (⟨k⟩ : OperatorIndex d S L)
  let Z := F.toEnrichedFunctor.obj (⟨l⟩ : OperatorIndex d S L)
  let h := (α_ b a n).hom ≫ (b ◁ f) ≫ g
  let p := coefficientHom d S n k a f ≫ F.toEnrichedFunctor.map ⟨n⟩ ⟨k⟩
  let q := coefficientHom d S k l b g ≫ F.toEnrichedFunctor.map ⟨k⟩ ⟨l⟩
  let r := coefficientHom d S n l (b ⊗ a) h ≫ F.toEnrichedFunctor.map ⟨n⟩ ⟨l⟩
  let u := action d S L F n k a f
  let v := action d S L F k l b g
  let w := action d S L F n l (b ⊗ a) h
  have hu : MonoidalClosed.uncurry p = (β_ A X).inv ≫ u := by
    dsimp only [u, action]
    rw [Iso.inv_hom_id_assoc]
  have hv : MonoidalClosed.uncurry q = (β_ B Y).inv ≫ v := by
    dsimp only [v, action]
    rw [Iso.inv_hom_id_assoc]
  have hw : MonoidalClosed.uncurry r = (β_ C X).inv ≫ w := by
    dsimp only [w, action]
    rw [Iso.inv_hom_id_assoc]
  have hMap : composition d S L n k l ≫ F.toEnrichedFunctor.map ⟨n⟩ ⟨l⟩ =
      (F.toEnrichedFunctor.map ⟨n⟩ ⟨k⟩ ⊗ₘ F.toEnrichedFunctor.map ⟨k⟩ ⟨l⟩) ≫
        eComp V X Y Z := by
    have ht := F.toEnrichedFunctor.map_comp (⟨n⟩ : OperatorIndex d S L) ⟨k⟩ ⟨l⟩
    rw [operatorIndex_comp] at ht
    exact ht
  have hSource := (coefficientHom_comp d S L n k l a b f g).trans
    (Category.assoc (β_ (S.obj a) (S.obj b)).hom (L.mu b a)
      (coefficientHom d S n l (b ⊗ a) h))
  have hFunctor := congrArg MonoidalClosed.uncurry
    (curriedCompositionTransport (coefficientHom d S n k a f)
      (coefficientHom d S k l b g) (coefficientHom d S n l (b ⊗ a) h)
      (F.toEnrichedFunctor.map ⟨n⟩ ⟨k⟩) (F.toEnrichedFunctor.map ⟨k⟩ ⟨l⟩)
      (F.toEnrichedFunctor.map ⟨n⟩ ⟨l⟩) (composition d S L n k l) (L.mu b a)
      hMap hSource)
  have hLeft : MonoidalClosed.uncurry ((p ⊗ₘ q) ≫ eComp V X Y Z) =
      (α_ X A B).inv ≫ ((β_ A X).inv ▷ B) ≫ (β_ B (A ⊗ X)).inv ≫
        (B ◁ u) ≫ v := by
    rw [MonoidalClosed.uncurry_eComp, hu, hv]
    simp only [comp_whiskerRight, Category.assoc]
    rw [braiding_inv_naturality_left_assoc]
  have hRight : MonoidalClosed.uncurry ((β_ A B).hom ≫ L.mu b a ≫ r) =
      (X ◁ (β_ A B).hom) ≫ (β_ (B ⊗ A) X).inv ≫ (L.mu b a ▷ X) ≫ w := by
    rw [MonoidalClosed.uncurry_natural_left, MonoidalClosed.uncurry_natural_left, hw]
    rw [braiding_inv_naturality_right_assoc]
  have hShuffle : (α_ X A B).inv ≫ ((β_ A X).inv ▷ B) ≫
      (β_ B (A ⊗ X)).inv ≫ (B ◁ u) ≫ v =
    (X ◁ (β_ A B).hom) ≫ (β_ (B ⊗ A) X).inv ≫ (α_ B A X).hom ≫ (B ◁ u) ≫ v := by
    simpa only [Category.assoc] using
      congrArg (fun t => t ≫ (B ◁ u) ≫ v) (arrowBraidShuffle X A B)
  have hWhole : (X ◁ (β_ A B).hom) ≫ (β_ (B ⊗ A) X).inv ≫
      (α_ B A X).hom ≫ (B ◁ u) ≫ v =
    (X ◁ (β_ A B).hom) ≫ (β_ (B ⊗ A) X).inv ≫ (L.mu b a ▷ X) ≫ w := by
    exact hShuffle.symm.trans (hLeft.symm.trans (hFunctor.trans hRight))
  exact ((cancel_epi (β_ (B ⊗ A) X).inv).1
    ((cancel_epi (X ◁ (β_ A B).hom)).1 hWhole)).symm

omit [SymmetricCategory I] in
/-- Every entire coefficient-index action retains its original sphere map. -/
theorem action_coefficient (F : EnrichedFunctorCat V (OperatorIndex d S L))
    (n k a b : I) (s : a ⟶ b) (g : b ⊗ n ⟶ k) :
    action d S L F n k a ((s ▷ n) ≫ g) =
      (S.toOrdinaryFunctor.map s ▷ F.toEnrichedFunctor.obj ⟨n⟩) ≫
        action d S L F n k b g := by
  let X := F.toEnrichedFunctor.obj (⟨n⟩ : OperatorIndex d S L)
  let t : S.obj a ⟶ S.obj b := S.toOrdinaryFunctor.map s
  have hc := coefficientAction_relation d S L F n k a b s g
  have hb := braiding_naturality_left t X
  calc
    _ = (β_ (S.obj a) X).hom ≫ coefficientAction d S L F n k a ((s ▷ n) ≫ g) :=
      action_eq_braid d S L F n k a ((s ▷ n) ≫ g)
    _ = (β_ (S.obj a) X).hom ≫ (X ◁ t) ≫ coefficientAction d S L F n k b g :=
      congrArg (fun q => (β_ (S.obj a) X).hom ≫ q) hc
    _ = (t ▷ X) ≫ (β_ (S.obj b) X).hom ≫ coefficientAction d S L F n k b g := by
      simpa only [Category.assoc] using congrArg
        (fun q => q ≫ coefficientAction d S L F n k b g) hb.symm
    _ = _ := congrArg (fun q => (t ▷ X) ≫ q) (action_eq_braid d S L F n k b g).symm

omit d S L in
/-- The two full source action labels differ by the actual coefficient block swap. -/
theorem exchangeLabel (r a n k : I) (f : a ⊗ n ⟶ k) :
    (α_ a r n).hom ≫ (a ◁ (β_ r n).hom) ≫ GenericRightTensor.label r n k a f =
      ((β_ a r).hom ▷ n) ≫ (α_ r a n).hom ≫ (r ◁ f) ≫ (β_ r k).hom := by
  simp only [GenericRightTensor.label]
  rw [braiding_naturality_right r f, braiding_tensor_right_hom]
  simp only [Category.assoc, Iso.hom_inv_id_assoc, ← comp_whiskerRight_assoc,
    SymmetricCategory.symmetry, id_whiskerRight, Category.id_comp]

omit [∀ n k : I, HasCoproduct (weightedCoend.relations (weight d n k) S)]
  [∀ n k : I, HasCoproduct (weightedCoend.objects (weight d n k) S)]
  [∀ n k : I, HasCoequalizer (weightedCoend.leftMap (weight d n k) S)
  (weightedCoend.rightMap (weight d n k) S)] in
/-- The actual tensorator uses the original reverse coefficient block map. -/
theorem coefficientMu_comm (B : EnrichedFunctor.LaxBraidedData L) (r a : I) :
    (β_ (S.obj r) (S.obj a)).hom ≫ L.mu a r ≫
      S.toOrdinaryFunctor.map (β_ a r).hom = L.mu r a := by
  let f : S.obj (r ⊗ a) ⟶ S.obj (a ⊗ r) := S.toOrdinaryFunctor.map (β_ r a).hom
  let g : S.obj (a ⊗ r) ⟶ S.obj (r ⊗ a) := S.toOrdinaryFunctor.map (β_ a r).hom
  have hb : L.mu r a ≫ f = (β_ (S.obj r) (S.obj a)).hom ≫ L.mu a r := B.braided r a
  have hi : f ≫ g = 𝟙 (S.obj (r ⊗ a)) :=
    ((S.toOrdinaryFunctor.map_comp (β_ r a).hom (β_ a r).hom).symm).trans
      ((congrArg S.toOrdinaryFunctor.map (SymmetricCategory.symmetry r a)).trans
        (S.toOrdinaryFunctor.map_id (r ⊗ a)))
  exact (Category.assoc (β_ (S.obj r) (S.obj a)).hom (L.mu a r) g).symm.trans
    ((congrArg (fun q => q ≫ g) hb.symm).trans
      ((Category.assoc (L.mu r a) f g).trans
        ((congrArg (fun q => L.mu r a ≫ q) hi).trans (Category.comp_id _))))

/-- Every full original labelled action commutes with the right-degree structure action. -/
theorem action_exchange (B : EnrichedFunctor.LaxBraidedData L)
    (F : EnrichedFunctorCat V (OperatorIndex d S L)) (r a n k : I) (f : a ⊗ n ⟶ k) :
    (S.obj r ◁ action d S L F n k a f) ≫ action d S L F k (k ⊗ r) r (β_ r k).hom =
      NativeOmegaPreparation.CoefficientShuffle.map (S.obj r) (S.obj a)
          (F.toEnrichedFunctor.obj ⟨n⟩) ≫
        (S.obj a ◁ action d S L F n (n ⊗ r) r (β_ r n).hom) ≫
        action d S L F (n ⊗ r) (k ⊗ r) a (GenericRightTensor.label r n k a f) := by
  let X := F.toEnrichedFunctor.obj (⟨n⟩ : OperatorIndex d S L)
  let l := (α_ r a n).hom ≫ (r ◁ f) ≫ (β_ r k).hom
  let h := (α_ a r n).hom ≫ (a ◁ (β_ r n).hom) ≫ GenericRightTensor.label r n k a f
  let p := action d S L F n (k ⊗ r) (r ⊗ a) l
  let q := action d S L F n (k ⊗ r) (a ⊗ r) h
  have hL := action_comp d S L F n k (k ⊗ r) a r f (β_ r k).hom
  have hR := action_comp d S L F n (n ⊗ r) (k ⊗ r) r a
    (β_ r n).hom (GenericRightTensor.label r n k a f)
  have hLabel : ((β_ a r).hom ▷ n) ≫ l = h := (exchangeLabel r a n k f).symm
  have hq : q = (S.toOrdinaryFunctor.map (β_ a r).hom ▷ X) ≫ p := by
    have hc := action_coefficient d S L F n (k ⊗ r) (a ⊗ r) (r ⊗ a) (β_ a r).hom l
    exact (congrArg (action d S L F n (k ⊗ r) (a ⊗ r)) hLabel).symm.trans hc
  exact scalarActionExchange (S.obj r) (S.obj a) X
    (F.toEnrichedFunctor.obj ⟨k⟩) (F.toEnrichedFunctor.obj ⟨n ⊗ r⟩)
    (S.obj (r ⊗ a)) (S.obj (a ⊗ r)) (F.toEnrichedFunctor.obj ⟨k ⊗ r⟩)
    (L.mu r a) (L.mu a r) (S.toOrdinaryFunctor.map (β_ a r).hom) p q
    (action d S L F n k a f) (action d S L F n (n ⊗ r) r (β_ r n).hom)
    (action d S L F k (k ⊗ r) r (β_ r k).hom)
    (action d S L F (n ⊗ r) (k ⊗ r) a (GenericRightTensor.label r n k a f))
    hL hR (coefficientMu_comm d S L B r a) hq

/-- Every original coefficient label is natural for the full right-degree transpose. -/
theorem adjoint_label_square (B : EnrichedFunctor.LaxBraidedData L)
    (F : EnrichedFunctorCat V (OperatorIndex d S L)) (r a n k : I) (f : a ⊗ n ⟶ k) :
    action d S L F n k a f ≫ adjoint d S L F k (k ⊗ r) r (β_ r k).hom =
      (S.obj a ◁ adjoint d S L F n (n ⊗ r) r (β_ r n).hom) ≫
        action d S L (cotensorObject (S.obj r) ((shift d S L r).obj F)) n k a f := by
  rw [cotensor_action, shift_action]
  exact coefficientCurrySquare (S.obj r) (S.obj a)
    (F.toEnrichedFunctor.obj ⟨n⟩) (F.toEnrichedFunctor.obj ⟨n ⊗ r⟩)
    (F.toEnrichedFunctor.obj ⟨k⟩) (F.toEnrichedFunctor.obj ⟨k ⊗ r⟩)
    (action d S L F n k a f)
    (action d S L F (n ⊗ r) (k ⊗ r) a (GenericRightTensor.label r n k a f))
    (adjoint d S L F n (n ⊗ r) r (β_ r n).hom)
    (adjoint d S L F k (k ⊗ r) r (β_ r k).hom) (by
      rw [adjoint, adjoint, MonoidalClosed.uncurry_curry, MonoidalClosed.uncurry_curry]
      exact action_exchange d S L B F r a n k f)

omit [SymmetricCategory I] in
/-- Every genuine native transformation preserves the entire coefficient-first source action. -/
theorem action_natural {F G : EnrichedFunctorCat V (OperatorIndex d S L)} (q : F ⟶ G)
    (n k a : I) (f : a ⊗ n ⟶ k) :
    action d S L F n k a f ≫ component q ⟨k⟩ =
      (S.obj a ◁ component q ⟨n⟩) ≫ action d S L G n k a f := by
  let X := F.toEnrichedFunctor.obj (⟨n⟩ : OperatorIndex d S L)
  let Y := G.toEnrichedFunctor.obj (⟨n⟩ : OperatorIndex d S L)
  let b := (β_ (S.obj a) X).hom
  have hc := coefficientAction_natural d S L q n k a f
  have hb := braiding_naturality_right (S.obj a) (component q (⟨n⟩ : OperatorIndex d S L))
  calc
    _ = b ≫ coefficientAction d S L F n k a f ≫ component q ⟨k⟩ := by
      rw [action_eq_braid, Category.assoc]
    _ = b ≫ (component q ⟨n⟩ ▷ S.obj a) ≫ coefficientAction d S L G n k a f :=
      congrArg (fun t => b ≫ t) hc
    _ = (S.obj a ◁ component q ⟨n⟩) ≫ (β_ (S.obj a) Y).hom ≫
        coefficientAction d S L G n k a f := by
      simpa only [Category.assoc] using
        congrArg (fun t => t ≫ coefficientAction d S L G n k a f) hb.symm
    _ = _ := congrArg (fun t => (S.obj a ◁ component q ⟨n⟩) ≫ t)
      (action_eq_braid d S L G n k a f).symm

end PointedCGWH.Spectra.Orthogonal.FunctionSpectrum.Delooping.Internal

universe u v



namespace PointedCGWH.Spectra.Orthogonal.FunctionSpectrum.Delooping

/-- The actual continuous orthogonal index category. -/
local instance : Category.{v} OrthogonalIndex := OrthogonalIndex.category.{u, v}
/-- The original block-sum monoidal structure on the orthogonal index. -/
local instance : MonoidalCategory OrthogonalIndex := OrthogonalIndex.monoidalCategory.{u, v}
/-- The genuine continuous enriched structure on the orthogonal index. -/
local instance : EnrichedOrdinaryCategory PointedCGWH.{u, v} OrthogonalIndex :=
  OrthogonalIndex.enrichedOrdinaryCategory.{u, v}
/-- The original continuous block-exchange symmetry. -/
local instance : SymmetricCategory OrthogonalIndex := OrthogonalIndex.symmetricCategory.{u, v}

private abbrev d := OrthogonalIndex.enrichedMonoidalData.{u, v}
private abbrev S := orthogonalSphereFunctor.{u, v}
private abbrev L := orthogonalSphereMonoidalData.{u, v}

open RightShift ShiftOmega

/-- Every complete native source label commutes with the original right-degree action. -/
theorem action_exchange (F : Carrier.{u, v}) (r a n k : OrthogonalIndex)
    (f : RightShift.Arrow.{u, v} (a + n) k) :
    (S.{u, v}.obj r ◁ RightShift.action F n k a f) ≫
        RightShift.action F k (k + r) r (β_ r k).hom =
      NativeOmegaPreparation.CoefficientShuffle.map (S.{u, v}.obj r) (S.{u, v}.obj a)
          (F.toEnrichedFunctor.obj (OrthogonalOperatorIndex.ofIndex.{u, v} n)) ≫
        (S.{u, v}.obj a ◁ RightShift.action F n (n + r) r (β_ r n).hom) ≫
        RightShift.action F (n + r) (k + r) a (RightShift.label r n k a f) :=
  Internal.action_exchange d.{u, v} S.{u, v} L.{u, v}
    orthogonalSphereBraidedData.{u, v} F r a n k f

/-- The entire native right-shift cotensor functor keeps every original enriched action. -/
def shiftedLoop (r : OrthogonalIndex) : Carrier.{u, v} ⥤ Carrier.{u, v} :=
  RightShift.shift r ⋙ cotensor (PointedCGWH.orthogonalSphere.{u, v} r)

/-- All continuous native labels are natural for the original structure transpose. -/
theorem omegaMap_label_square (F : Carrier.{u, v}) (r a n k : OrthogonalIndex)
    (f : RightShift.Arrow.{u, v} (a + n) k) :
    RightShift.action F n k a f ≫ omegaMap F k r =
      (S.{u, v}.obj a ◁ omegaMap F n r) ≫
        RightShift.action ((shiftedLoop r).obj F) n k a f := by
  change RightShift.action F n k a f ≫ omegaMap F k r =
    (S.{u, v}.obj a ◁ omegaMap F n r) ≫
      RightShift.action (cotensorObject (S.{u, v}.obj r) ((RightShift.shift r).obj F)) n k a f
  rw [RightShift.cotensor_action, RightShift.shift_action]
  exact Internal.coefficientCurrySquare (S.{u, v}.obj r) (S.{u, v}.obj a)
    (F.toEnrichedFunctor.obj (OrthogonalOperatorIndex.ofIndex.{u, v} n))
    (F.toEnrichedFunctor.obj (OrthogonalOperatorIndex.ofIndex.{u, v} (n + r)))
    (F.toEnrichedFunctor.obj (OrthogonalOperatorIndex.ofIndex.{u, v} k))
    (F.toEnrichedFunctor.obj (OrthogonalOperatorIndex.ofIndex.{u, v} (k + r)))
    (RightShift.action F n k a f)
    (RightShift.action F (n + r) (k + r) a (RightShift.label r n k a f))
    (omegaMap F n r) (omegaMap F k r) (by
      rw [omegaMap_uncurry, omegaMap_uncurry]
      exact action_exchange F r a n k f)

/-- The original full native transpose at every operator index is the comparison component. -/
def comparisonComponent (r : OrthogonalIndex) (F : Carrier.{u, v})
    (n : OrthogonalOperatorIndex.{u, v}) :
    F.toEnrichedFunctor.obj n ⟶ ((shiftedLoop r).obj F).toEnrichedFunctor.obj n := by
  rcases n with ⟨n⟩
  exact omegaMap F n r

/-- The entire component at an original dimension is the original full-family native adjoint. -/
theorem comparisonComponent_at (r : OrthogonalIndex) (F : Carrier.{u, v}) (n : OrthogonalIndex) :
    comparisonComponent r F (OrthogonalOperatorIndex.ofIndex.{u, v} n) = omegaMap F n r := rfl

/-- Full continuous action squares construct the genuine native enriched comparison. -/
def comparison (r : OrthogonalIndex) (F : Carrier.{u, v}) : F ⟶ (shiftedLoop r).obj F :=
  RightShift.transformation F _ (comparisonComponent r F) (by
    intro a n k f
    exact omegaMap_label_square F r a n k f)

/-- Every comparison component retains the actual original sphere inclusion and transpose. -/
theorem comparison_component (r : OrthogonalIndex) (F : Carrier.{u, v}) (n : OrthogonalIndex) :
    component (comparison r F) (OrthogonalOperatorIndex.ofIndex.{u, v} n) = omegaMap F n r :=
  (RightShift.transformation_component _ _ _ _ _).trans (comparisonComponent_at r F n)

/-- Every whole native transformation keeps its original component under shift and cotensor. -/
theorem shiftedLoop_map_component (r n : OrthogonalIndex) {F G : Carrier.{u, v}} (q : F ⟶ G) :
    component ((shiftedLoop r).map q) (OrthogonalOperatorIndex.ofIndex.{u, v} n) =
      (ihom (PointedCGWH.orthogonalSphere.{u, v} r)).map
        (component q (OrthogonalOperatorIndex.ofIndex.{u, v} (n + r))) :=
  (cotensorMap_component _ _ _).trans
    (congrArg (fun t => (ihom (PointedCGWH.orthogonalSphere.{u, v} r)).map t)
      (RightShift.shift_map_component r n q))

/-- The genuine comparison is natural in every complete native transformation. -/
theorem comparison_naturality (r : OrthogonalIndex) {F G : Carrier.{u, v}} (q : F ⟶ G) :
    q ≫ comparison r G = comparison r F ≫ (shiftedLoop r).map q := by
  apply hom_ext
  intro n
  rcases n with ⟨n⟩
  change component (q ≫ comparison r G) (OrthogonalOperatorIndex.ofIndex.{u, v} n) =
    component (comparison r F ≫ (shiftedLoop r).map q)
      (OrthogonalOperatorIndex.ofIndex.{u, v} n)
  rw [component_comp, component_comp, comparison_component, comparison_component,
    shiftedLoop_map_component]
  exact CurrentFree.adjoint_naturality _ _ _ _ q

/-- All unchanged original structure transposes form a full natural transformation. -/
def comparisonNat (r : OrthogonalIndex) : 𝟭 Carrier.{u, v} ⟶ shiftedLoop r where
  app := comparison r
  naturality _ _ q := comparison_naturality r q

/-- Each original level comparison is weak for the complete source Omega condition. -/
theorem comparison_level_weak (r : OrthogonalIndex) (F : Carrier.{u, v})
    (hF : Actual.OrthogonalIsOmega F) (n : OrthogonalIndex) :
    weakEquivalences PointedCGWH.{u, v}
      (component (comparison r F) (OrthogonalOperatorIndex.ofIndex.{u, v} n)) := by
  rw [comparison_component]
  exact hF (n, r)

attribute [local instance] HomotopicalAlgebra.EnrichedProjective.Native.modelCategory

/-- The whole comparison is weak in the actual canonical native level model. -/
theorem comparison_weak (r : OrthogonalIndex) (F : Carrier.{u, v})
    (hF : Actual.OrthogonalIsOmega F) : weakEquivalences Carrier.{u, v} (comparison r F) := by
  rw [HomotopicalAlgebra.EnrichedProjective.Native.weakEquivalences_eq]
  apply (HomotopicalAlgebra.EvaluationTransfer.evaluationProperty_iff
    (fun n : OrthogonalOperatorIndex.{u, v} => evaluation (V := PointedCGWH.{u, v}) n)
    (weakEquivalences PointedCGWH.{u, v}) _).2
  intro n
  rcases n with ⟨n⟩
  exact comparison_level_weak r F hF n

/-- The actual first right-shift delooping retains all original operator Hom actions. -/
abbrev firstDelooping : Carrier.{u, v} ⥤ Carrier.{u, v} := RightShift.shift 1

/-- Scalar contravariance carries the actual representation-one-sphere isomorphism. -/
def firstLoopIso : cotensor (I := OrthogonalOperatorIndex.{u, v})
    (PointedCGWH.orthogonalSphere.{u, v} 1) ≅ cotensor PointedCGWH.sphereOne.{u, v} :=
  (ScalarLeibniz.cotensorBifunctor (V := PointedCGWH.{u, v})
    (A := OrthogonalOperatorIndex.{u, v})).mapIso
      CategoryTheory.Spectra.orthogonalOneSphereIsoSphereOne.{u, v}.symm.op

/-- Every scalar comparison component uses the original inverse sphere-one coefficient. -/
theorem firstLoopIso_component (F : Carrier.{u, v}) (n : OrthogonalOperatorIndex.{u, v}) :
    component (firstLoopIso.hom.app F) n =
      (MonoidalClosed.pre CategoryTheory.Spectra.orthogonalOneSphereIsoSphereOne.{u, v}.inv).app
        (F.toEnrichedFunctor.obj n) :=
  cotensorScalarMap_component _ F n

/-- The native one-sphere loop of the full first right shift. -/
abbrev firstDeloopingLoop : Carrier.{u, v} ⥤ Carrier.{u, v} :=
  firstDelooping ⋙ cotensor PointedCGWH.sphereOne.{u, v}

/-- The original structure map goes from a spectrum to the native loop of its first right shift. -/
def delta : 𝟭 Carrier.{u, v} ⟶ firstDeloopingLoop.{u, v} :=
  comparisonNat 1 ≫ (Functor.isoWhiskerLeft firstDelooping firstLoopIso).hom

/-- Each delta component is its original nu transpose and sphere-one precomposition. -/
theorem delta_component (F : Carrier.{u, v}) (n : OrthogonalIndex) :
    component (delta.app F) (OrthogonalOperatorIndex.ofIndex.{u, v} n) =
      omegaMap F n 1 ≫
        (MonoidalClosed.pre CategoryTheory.Spectra.orthogonalOneSphereIsoSphereOne.{u, v}.inv).app
          (F.toEnrichedFunctor.obj (OrthogonalOperatorIndex.ofIndex.{u, v} (n + 1))) := by
  change component (comparison 1 F ≫ firstLoopIso.hom.app (firstDelooping.obj F))
    (OrthogonalOperatorIndex.ofIndex.{u, v} n) = _
  exact (component_comp _ _ _).trans
    (congrArg₂ (fun p q => p ≫ q) (comparison_component 1 F n)
      (firstLoopIso_component (firstDelooping.obj F) (OrthogonalOperatorIndex.ofIndex.{u, v} n)))

/-- The entire first right shift is Omega for every original full-family Omega spectrum. -/
theorem firstDelooping_isOmega (F : Carrier.{u, v}) (hF : Actual.OrthogonalIsOmega F) :
    Actual.OrthogonalIsOmega (firstDelooping.obj F) := ShiftOmega.shift_isOmega 1 F hF

/-- The unchanged original comparison is natural in every full native transformation. -/
theorem delta_naturality {F G : Carrier.{u, v}} (q : F ⟶ G) :
    q ≫ delta.app G = delta.app F ≫ firstDeloopingLoop.map q := delta.naturality q

/-- The original one-sphere comparison is level weak on every full-family Omega spectrum. -/
theorem delta_weak (F : Carrier.{u, v}) (hF : Actual.OrthogonalIsOmega F) :
    weakEquivalences Carrier.{u, v} (delta.app F) := by
  let j := (Functor.isoWhiskerLeft firstDelooping firstLoopIso).hom.app F
  have hj : weakEquivalences Carrier.{u, v} j :=
    (weakEquivalences Carrier.{u, v}).of_isIso j
  exact (weakEquivalences Carrier.{u, v}).comp_mem (comparison 1 F) j
    (comparison_weak 1 F hF) hj

end PointedCGWH.Spectra.Orthogonal.FunctionSpectrum.Delooping

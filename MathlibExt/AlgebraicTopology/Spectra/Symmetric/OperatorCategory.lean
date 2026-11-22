/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.Spectra.Symmetric.OperatorAssociativity
public import Mathlib.CategoryTheory.Enriched.Basic

/-!
# The actual generic sphere enriched operator category

All composition laws are proved on the complete tensor products of the
original coefficient coends. No generalized-element detector is assumed.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe uV vV

open CategoryTheory Limits MonoidalCategory
open CategoryTheory.MonoidalCategory
open scoped ExternalProduct

namespace CategoryTheory.Spectra.Symmetric.OperatorCoend

local notation "I" => Operad.SmallFinBijGroupoid

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V] [SymmetricCategory V]
  [HasColimitsOfSize.{0, 0} V]
  [∀ X : V, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]

/-- Complete pairs of the original coefficient generators determine maps from both Hom coends. -/
theorem tensor_hom_ext (T : V) (n k l : I) {Z : V}
    (f g : Hom T n k ⊗ Hom T k l ⟶ Z)
    (h : ∀ (a b : I) (p : a ⊗ n ⟶ k) (q : b ⊗ k ⟶ l),
      (generator T a n k p ⊗ₘ generator T b k l q) ≫ f =
        (generator T a n k p ⊗ₘ generator T b k l q) ≫ g) : f = g := by
  apply ((colimit.isColimit (diagram T n k)).tensor₂
    (colimit.isColimit (diagram T k l))).hom_ext
  intro q
  have hi : ((colimit.cocone (diagram T n k)).tensor₂
      (colimit.cocone (diagram T k l))).ι.app q =
      generator T q.1.left n k q.1.hom ⊗ₘ generator T q.2.left k l q.2.hom := by
    simpa only [Cocone.tensor₂, Functor.mapCocone₂, curriedTensor] using!
      (tensorHom_def (generator T q.1.left n k q.1.hom)
        (generator T q.2.left k l q.2.hom)).symm
  exact (congrArg (fun t => t ≫ f) hi).trans
    ((h q.1.left q.2.left q.1.hom q.2.hom).trans (congrArg (fun t => t ≫ g) hi).symm)

/-- Complete triples of the original coefficient generators determine maps from all three coends. -/
theorem triple_hom_ext (T : V) (n k l m : I) {Z : V}
    (f g : (Hom T n k ⊗ Hom T k l) ⊗ Hom T l m ⟶ Z)
    (h : ∀ (a b c : I) (p : a ⊗ n ⟶ k) (q : b ⊗ k ⟶ l) (r : c ⊗ l ⟶ m),
      ((generator T a n k p ⊗ₘ generator T b k l q) ⊗ₘ generator T c l m r) ≫ f =
        ((generator T a n k p ⊗ₘ generator T b k l q) ⊗ₘ generator T c l m r) ≫ g) : f = g := by
  apply (((colimit.isColimit (diagram T n k)).tensor₂
    (colimit.isColimit (diagram T k l))).tensor₂ (colimit.isColimit (diagram T l m))).hom_ext
  intro q
  have hi : (((colimit.cocone (diagram T n k)).tensor₂
      (colimit.cocone (diagram T k l))).tensor₂ (colimit.cocone (diagram T l m))).ι.app q =
      ((generator T q.1.1.left n k q.1.1.hom ⊗ₘ generator T q.1.2.left k l q.1.2.hom) ⊗ₘ
        generator T q.2.left l m q.2.hom) := by
    have hi12 : ((colimit.cocone (diagram T n k)).tensor₂
        (colimit.cocone (diagram T k l))).ι.app q.1 =
        generator T q.1.1.left n k q.1.1.hom ⊗ₘ generator T q.1.2.left k l q.1.2.hom := by
      simpa only [Cocone.tensor₂, Functor.mapCocone₂, curriedTensor] using!
        (tensorHom_def (generator T q.1.1.left n k q.1.1.hom)
          (generator T q.1.2.left k l q.1.2.hom)).symm
    have hi3 : (((colimit.cocone (diagram T n k)).tensor₂
        (colimit.cocone (diagram T k l))).tensor₂ (colimit.cocone (diagram T l m))).ι.app q =
        ((colimit.cocone (diagram T n k)).tensor₂
          (colimit.cocone (diagram T k l))).ι.app q.1 ⊗ₘ generator T q.2.left l m q.2.hom := by
      simpa only [Cocone.tensor₂, Functor.mapCocone₂, curriedTensor] using!
        (tensorHom_def (((colimit.cocone (diagram T n k)).tensor₂
          (colimit.cocone (diagram T k l))).ι.app q.1) (generator T q.2.left l m q.2.hom)).symm
    exact hi3.trans (congrArg (fun t => t ⊗ₘ generator T q.2.left l m q.2.hom) hi12)
  exact (congrArg (fun t => t ≫ f) hi).trans
    ((h q.1.1.left q.1.2.left q.2.left q.1.1.hom q.1.2.hom q.2.hom).trans
      (congrArg (fun t => t ≫ g) hi).symm)

/-- The full generating composition formula, retaining both original label objects. -/
theorem generator_comp_label (T : V) (n k l : I) (q : Labels n k) (r : Labels k l) :
    (generator T q.left n k q.hom ⊗ₘ generator T r.left k l r.hom) ≫ composition T n k l =
      reverseMultiplication T q.left r.left ≫ compositionInjection T n k l q r := by
  have h : (generator T q.left n k q.hom ⊗ₘ generator T r.left k l r.hom) ≫ composition T n k l =
      (β_ ((Operad.SmallFinBijGroupoid.tensorPowerFunctor T).obj q.left)
        ((Operad.SmallFinBijGroupoid.tensorPowerFunctor T).obj r.left)).hom ≫
        coefficientMultiplication T r.left q.left ≫ compositionInjection T n k l q r :=
    generator_composition T q.left r.left n k l q.hom r.hom
  exact h.trans (Category.assoc _ _ _).symm

/-- Every complete triple of labelled coefficient objects has the genuine associativity equation. -/
theorem generator_assoc (T : V) (n k l m : I) (q : Labels n k) (r : Labels k l) (s : Labels l m) :
    ((generator T q.left n k q.hom ⊗ₘ generator T r.left k l r.hom) ⊗ₘ
        generator T s.left l m s.hom) ≫
      composition T n k l ▷ Hom T l m ≫ composition T n l m =
    ((generator T q.left n k q.hom ⊗ₘ generator T r.left k l r.hom) ⊗ₘ
        generator T s.left l m s.hom) ≫
      (α_ (Hom T n k) (Hom T k l) (Hom T l m)).hom ≫
      Hom T n k ◁ composition T k l m ≫ composition T n k m := by
  let P := Operad.SmallFinBijGroupoid.tensorPowerFunctor T
  let u : P.obj q.left ⟶ Hom T n k := generator T q.left n k q.hom
  let v : P.obj r.left ⟶ Hom T k l := generator T r.left k l r.hom
  let w : P.obj s.left ⟶ Hom T l m := generator T s.left l m s.hom
  let qr : Labels n l := CostructuredArrow.mk (Y := r.left ⊗ q.left) (compositionLabel n k l q r)
  let rs : Labels k m := CostructuredArrow.mk (Y := s.left ⊗ r.left) (compositionLabel k l m r s)
  let uv : P.obj (r.left ⊗ q.left) ⟶ Hom T n l := compositionInjection T n k l q r
  let vw : P.obj (s.left ⊗ r.left) ⟶ Hom T k m := compositionInjection T k l m r s
  let left : P.obj (s.left ⊗ (r.left ⊗ q.left)) ⟶ Hom T n m :=
    compositionInjection T n l m qr s
  let right : P.obj ((s.left ⊗ r.left) ⊗ q.left) ⟶ Hom T n m :=
    compositionInjection T n k m q rs
  have hLabel : P.map (α_ s.left r.left q.left).hom ≫ left = right := by
    exact (generator_relation T (α_ s.left r.left q.left).hom (compositionLabel n l m qr s)).trans
      (congrArg (generator T ((s.left ⊗ r.left) ⊗ q.left) n m) (compositionLabel_assoc n k l m q r s))
  have hFirst : (u ⊗ₘ v) ≫ composition T n k l = reverseMultiplication T q.left r.left ≫ uv :=
    generator_comp_label T n k l q r
  have hLast : (v ⊗ₘ w) ≫ composition T k l m = reverseMultiplication T r.left s.left ≫ vw :=
    generator_comp_label T k l m r s
  have hLeft : (uv ⊗ₘ w) ≫ composition T n l m =
      reverseMultiplication T (r.left ⊗ q.left) s.left ≫ left :=
    generator_comp_label T n l m qr s
  have hRight : (u ⊗ₘ vw) ≫ composition T n k m =
      reverseMultiplication T q.left (s.left ⊗ r.left) ≫ right :=
    generator_comp_label T n k m q rs
  have hc := reverseMultiplication_assoc T q.left r.left s.left
  have hL : ((u ⊗ₘ v) ⊗ₘ w) ≫ composition T n k l ▷ Hom T l m ≫ composition T n l m =
      reverseMultiplication T q.left r.left ▷ P.obj s.left ≫
        reverseMultiplication T (r.left ⊗ q.left) s.left ≫ left := by
    rw [← Category.assoc, tensorHom_comp_whiskerRight, hFirst,
      ← whiskerRight_comp_tensorHom, Category.assoc, hLeft]
  have hR : ((u ⊗ₘ v) ⊗ₘ w) ≫
      (α_ (Hom T n k) (Hom T k l) (Hom T l m)).hom ≫
      Hom T n k ◁ composition T k l m ≫ composition T n k m =
      (α_ (P.obj q.left) (P.obj r.left) (P.obj s.left)).hom ≫
        P.obj q.left ◁ reverseMultiplication T r.left s.left ≫
        reverseMultiplication T q.left (s.left ⊗ r.left) ≫ right := by
    slice_lhs 1 2 => rw [associator_naturality]
    simp only [Category.assoc]
    slice_lhs 2 3 => rw [tensorHom_comp_whiskerLeft, hLast, ← whiskerLeft_comp_tensorHom]
    simp only [Category.assoc]
    slice_lhs 3 4 => exact hRight
  have hMiddle : reverseMultiplication T q.left r.left ▷ P.obj s.left ≫
      reverseMultiplication T (r.left ⊗ q.left) s.left ≫ left =
      (α_ (P.obj q.left) (P.obj r.left) (P.obj s.left)).hom ≫
        P.obj q.left ◁ reverseMultiplication T r.left s.left ≫
        reverseMultiplication T q.left (s.left ⊗ r.left) ≫ right := by
    have h : reverseMultiplication T q.left r.left ▷ P.obj s.left ≫
        reverseMultiplication T (r.left ⊗ q.left) s.left ≫ left =
        (α_ (P.obj q.left) (P.obj r.left) (P.obj s.left)).hom ≫
          P.obj q.left ◁ reverseMultiplication T r.left s.left ≫
          reverseMultiplication T q.left (s.left ⊗ r.left) ≫
          P.map (α_ s.left r.left q.left).hom ≫ left := by
      simpa only [Category.assoc] using congrArg (fun t => t ≫ left) hc
    have hj : (α_ (P.obj q.left) (P.obj r.left) (P.obj s.left)).hom ≫
        P.obj q.left ◁ reverseMultiplication T r.left s.left ≫
        reverseMultiplication T q.left (s.left ⊗ r.left) ≫
        P.map (α_ s.left r.left q.left).hom ≫ left =
        (α_ (P.obj q.left) (P.obj r.left) (P.obj s.left)).hom ≫
          P.obj q.left ◁ reverseMultiplication T r.left s.left ≫
          reverseMultiplication T q.left (s.left ⊗ r.left) ≫ right := by
      simpa only [Category.assoc] using congrArg
        (fun t => ((α_ (P.obj q.left) (P.obj r.left) (P.obj s.left)).hom ≫
          P.obj q.left ◁ reverseMultiplication T r.left s.left ≫
          reverseMultiplication T q.left (s.left ⊗ r.left)) ≫ t) hLabel
    exact h.trans hj
  exact hL.trans (hMiddle.trans hR.symm)

/-- The original coend composition associates on the entire three-Hom tensor object. -/
theorem composition_assoc (T : V) (n k l m : I) :
    composition T n k l ▷ Hom T l m ≫ composition T n l m =
      (α_ (Hom T n k) (Hom T k l) (Hom T l m)).hom ≫
        Hom T n k ◁ composition T k l m ≫ composition T n k m := by
  apply triple_hom_ext T n k l m
  intro a b c p q r
  exact generator_assoc T n k l m (CostructuredArrow.mk (Y := a) p)
    (CostructuredArrow.mk (Y := b) q) (CostructuredArrow.mk (Y := c) r)

/-- The actual value-enriched generic sphere operator category on all original finite indices. -/
@[instance_reducible]
def enrichedCategory (T : V) : EnrichedCategory V I where
  Hom := Hom T
  id := identity T
  comp := composition T
  id_comp n k := by
    rw [identity_comp, Iso.inv_hom_id]
  comp_id n k := by
    rw [comp_identity, Iso.inv_hom_id]
  assoc n k l m := by
    rw [composition_assoc, Iso.inv_hom_id_assoc]

end CategoryTheory.Spectra.Symmetric.OperatorCoend

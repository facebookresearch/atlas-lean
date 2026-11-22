/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.Spectra.Symmetric.OperatorCoend

/-!
# Whole coend composition for the generic sphere operator

The two original finite labels compose with the late coefficient block first.
The value braiding and original tensor-power block comparison give a cocone.
Tensor preservation of both colimits descends this complete cocone.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe uV vV

open CategoryTheory Limits MonoidalCategory
open CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalCategory.TensorPower
open scoped ExternalProduct

namespace CategoryTheory.Spectra.Symmetric.OperatorCoend

local notation "I" => Operad.SmallFinBijGroupoid

/-- The original two-label finite-index composite, with the late coefficient first. -/
def compositionLabel (n k l : I) (q : Labels n k) (r : Labels k l) :
    (r.left ⊗ q.left) ⊗ n ⟶ l :=
  (α_ r.left q.left n).hom ≫ (r.left ◁ q.hom) ≫ r.hom

/-- Both entire original coefficient-index arrows retain the original finite-label relation. -/
theorem compositionLabel_natural (n k l : I) {q q' : Labels n k} {r r' : Labels k l}
    (u : q ⟶ q') (v : r ⟶ r') :
    ((v.left ⊗ₘ u.left) ▷ n) ≫ compositionLabel n k l q' r' = compositionLabel n k l q r := by
  have ha : ((v.left ⊗ₘ u.left) ▷ n) ≫ (α_ r'.left q'.left n).hom =
      (α_ r.left q.left n).hom ≫ (v.left ⊗ₘ (u.left ▷ n)) := by
    simpa only [tensorHom_id] using associator_naturality v.left u.left (𝟙 n)
  have hu : (u.left ▷ n) ≫ q'.hom = q.hom := u.w
  have hv : (v.left ▷ k) ≫ r'.hom = r.hom := v.w
  change ((v.left ⊗ₘ u.left) ▷ n) ≫
    (α_ r'.left q'.left n).hom ≫ (r'.left ◁ q'.hom) ≫ r'.hom =
    (α_ r.left q.left n).hom ≫ (r.left ◁ q.hom) ≫ r.hom
  calc
    _ = (α_ r.left q.left n).hom ≫ (v.left ⊗ₘ (u.left ▷ n)) ≫
        (r'.left ◁ q'.hom) ≫ r'.hom := by
      simpa only [Category.assoc] using
        congrArg (fun t => t ≫ (r'.left ◁ q'.hom) ≫ r'.hom) ha
    _ = (α_ r.left q.left n).hom ≫ (r.left ◁ (u.left ▷ n)) ≫
        (v.left ▷ (q'.left ⊗ n)) ≫ (r'.left ◁ q'.hom) ≫ r'.hom := by
      rw [tensorHom_def']
      simp only [Category.assoc]
    _ = (α_ r.left q.left n).hom ≫ (r.left ◁ (u.left ▷ n)) ≫
        (r.left ◁ q'.hom) ≫ (v.left ▷ k) ≫ r'.hom := by
      slice_lhs 3 4 => rw [← whisker_exchange]
      simp only [Category.assoc]
    _ = _ := by
      slice_lhs 2 3 => rw [← whiskerLeft_comp, hu]
      slice_lhs 3 4 => rw [hv]

/-- The complete ordinary index functor composing both original operator labels. -/
def compositionLabels (n k l : I) : Labels n k × Labels k l ⥤ Labels n l where
  obj q := CostructuredArrow.mk (Y := q.2.left ⊗ q.1.left) (compositionLabel n k l q.1 q.2)
  map f := CostructuredArrow.homMk (f.2.left ⊗ₘ f.1.left) (compositionLabel_natural n k l f.1 f.2)
  map_id q := by
    apply CostructuredArrow.hom_ext
    exact id_tensorHom_id _ _
  map_comp f g := by
    apply CostructuredArrow.hom_ext
    exact (tensorHom_comp_tensorHom _ _ _ _).symm

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V] [SymmetricCategory V]
  [HasColimitsOfSize.{0, 0} V]

/-- The actual block multiplication, typed on the original coefficient-functor objects. -/
def coefficientMultiplication (T : V) (a b : I) :
    (Operad.SmallFinBijGroupoid.tensorPowerFunctor T).obj a ⊗
      (Operad.SmallFinBijGroupoid.tensorPowerFunctor T).obj b ⟶
      (Operad.SmallFinBijGroupoid.tensorPowerFunctor T).obj (a ⊗ b) :=
  (tensorPowObj_add T a.of.len b.of.len).inv

omit [HasColimitsOfSize.{0, 0} V] in
/-- Both original finite coefficient maps retain their full block naturality square. -/
theorem coefficientMultiplication_natural (T : V) {a a' b b' : I} (f : a ⟶ a') (g : b ⟶ b') :
    ((Operad.SmallFinBijGroupoid.tensorPowerFunctor T).map f ⊗ₘ
      (Operad.SmallFinBijGroupoid.tensorPowerFunctor T).map g) ≫
      coefficientMultiplication T a' b' = coefficientMultiplication T a b ≫
      (Operad.SmallFinBijGroupoid.tensorPowerFunctor T).map (f ⊗ₘ g) :=
  genericSphereSequence_block_natural T f g

/-- The original composed finite label enters the actual Hom coend at its entire coefficient. -/
def compositionInjection (T : V) (n k l : I) (q : Labels n k) (r : Labels k l) :
    (Operad.SmallFinBijGroupoid.tensorPowerFunctor T).obj (r.left ⊗ q.left) ⟶ Hom T n l :=
  generator T (r.left ⊗ q.left) n l (compositionLabel n k l q r)

/-- Every pair of original index arrows retains the complete composed-label coend relation. -/
theorem compositionInjection_natural (T : V) (n k l : I)
    {q q' : Labels n k} {r r' : Labels k l} (u : q ⟶ q') (v : r ⟶ r') :
    (Operad.SmallFinBijGroupoid.tensorPowerFunctor T).map (v.left ⊗ₘ u.left) ≫
      compositionInjection T n k l q' r' = compositionInjection T n k l q r :=
  (generator_relation T (v.left ⊗ₘ u.left) (compositionLabel n k l q' r')).trans
    (congrArg (generator T (r.left ⊗ q.left) n l) (compositionLabel_natural n k l u v))

/-- Every complete pair of labels has its original coefficient and block-composition map. -/
def compositionGenerator (T : V) (n k l : I) (q : Labels n k) (r : Labels k l) :
    (Operad.SmallFinBijGroupoid.tensorPowerFunctor T).obj q.left ⊗
      (Operad.SmallFinBijGroupoid.tensorPowerFunctor T).obj r.left ⟶ Hom T n l :=
  (β_ ((Operad.SmallFinBijGroupoid.tensorPowerFunctor T).obj q.left)
      ((Operad.SmallFinBijGroupoid.tensorPowerFunctor T).obj r.left)).hom ≫
    coefficientMultiplication T r.left q.left ≫ compositionInjection T n k l q r

/-- Composition retains every whole original coefficient-index relation in both variables. -/
theorem compositionGenerator_natural (T : V) (n k l : I)
    {q q' : Labels n k} {r r' : Labels k l} (u : q ⟶ q') (v : r ⟶ r') :
    ((Operad.SmallFinBijGroupoid.tensorPowerFunctor T).map u.left ⊗ₘ
      (Operad.SmallFinBijGroupoid.tensorPowerFunctor T).map v.left) ≫
      compositionGenerator T n k l q' r' = compositionGenerator T n k l q r := by
  let P := Operad.SmallFinBijGroupoid.tensorPowerFunctor T
  have hb := BraidedCategory.braiding_naturality (P.map u.left) (P.map v.left)
  have hm := coefficientMultiplication_natural T v.left u.left
  have hw := compositionInjection_natural T n k l u v
  have h : (P.map u.left ⊗ₘ P.map v.left) ≫
      (β_ (P.obj q'.left) (P.obj r'.left)).hom ≫
      coefficientMultiplication T r'.left q'.left ≫ compositionInjection T n k l q' r' =
      (β_ (P.obj q.left) (P.obj r.left)).hom ≫ coefficientMultiplication T r.left q.left ≫
      compositionInjection T n k l q r := by
    slice_lhs 1 2 => rw [hb]
    simp only [Category.assoc]
    slice_lhs 2 3 => rw [hm]
    simp only [Category.assoc]
    slice_lhs 3 4 => exact hw
  exact h

/-- The original complete two-coefficient composition cocone. -/
def compositionCocone (T : V) (n k l : I) : Cocone (diagram T n k ⊠ diagram T k l) where
  pt := Hom T n l
  ι :=
    { app q := compositionGenerator T n k l q.1 q.2
      naturality := by
        rintro ⟨q, r⟩ ⟨q', r'⟩ ⟨u, v⟩
        simp only [Functor.const_obj_map]
        have hf : (diagram T n k ⊠ diagram T k l).map (u, v) =
            (Operad.SmallFinBijGroupoid.tensorPowerFunctor T).map u.left ⊗ₘ
              (Operad.SmallFinBijGroupoid.tensorPowerFunctor T).map v.left := by
          simp only [externalProductBifunctor_obj_map, diagram, genericSphereSequence, Functor.comp_map]
          exact (tensorHom_def _ _).symm
        exact (congrArg (fun t => t ≫ compositionGenerator T n k l q' r') hf).trans
          ((compositionGenerator_natural T n k l u v).trans (Category.comp_id _).symm) }

variable [∀ X : V, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
  [∀ X : V, PreservesColimitsOfSize.{0, 0} (tensorRight X)]

/-- The full composition descends from both original coefficient coends. -/
def composition (T : V) (n k l : I) : Hom T n k ⊗ Hom T k l ⟶ Hom T n l :=
  ((colimit.isColimit (diagram T n k)).tensor₂ (colimit.isColimit (diagram T k l))).desc
    (compositionCocone T n k l)

omit [∀ X : V, PreservesColimitsOfSize.{0, 0} (tensorRight X)] in
/-- Every complete pair of original coefficient generators retains the original composition formula. -/
theorem generator_composition (T : V) (a b n k l : I)
    (f : a ⊗ n ⟶ k) (g : b ⊗ k ⟶ l) :
    (generator T a n k f ⊗ₘ generator T b k l g) ≫ composition T n k l =
      (β_ ((Operad.SmallFinBijGroupoid.tensorPowerFunctor T).obj a)
        ((Operad.SmallFinBijGroupoid.tensorPowerFunctor T).obj b)).hom ≫
      (tensorPowObj_add T b.of.len a.of.len).inv ≫
      generator T (b ⊗ a) n l ((α_ b a n).hom ≫ (b ◁ f) ≫ g) := by
  have h := ((colimit.isColimit (diagram T n k)).tensor₂
    (colimit.isColimit (diagram T k l))).fac (compositionCocone T n k l)
      (CostructuredArrow.mk (Y := a) f, CostructuredArrow.mk (Y := b) g)
  have hi : ((colimit.cocone (diagram T n k)).tensor₂ (colimit.cocone (diagram T k l))).ι.app
      (CostructuredArrow.mk (Y := a) f, CostructuredArrow.mk (Y := b) g) =
      generator T a n k f ⊗ₘ generator T b k l g := by
    simpa only [Cocone.tensor₂, Functor.mapCocone₂, curriedTensor] using!
      (tensorHom_def (generator T a n k f) (generator T b k l g)).symm
  have hr : (compositionCocone T n k l).ι.app
      (CostructuredArrow.mk (Y := a) f, CostructuredArrow.mk (Y := b) g) =
      (β_ ((Operad.SmallFinBijGroupoid.tensorPowerFunctor T).obj a)
        ((Operad.SmallFinBijGroupoid.tensorPowerFunctor T).obj b)).hom ≫
        (tensorPowObj_add T b.of.len a.of.len).inv ≫
        generator T (b ⊗ a) n l ((α_ b a n).hom ≫ (b ◁ f) ≫ g) := rfl
  exact (congrArg (fun t => t ≫ composition T n k l) hi).symm.trans (h.trans hr)

end CategoryTheory.Spectra.Symmetric.OperatorCoend

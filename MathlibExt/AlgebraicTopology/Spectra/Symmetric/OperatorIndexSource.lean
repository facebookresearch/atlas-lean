/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.Spectra.Symmetric.OperatorIndexMaps

/-!
# Whole source-index maps of the generic sphere operator coend

Original finite-index arrows precompose every full operator label. The source
maps are contravariant, commute with the original target maps, and retain all
coend generator relations.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe uV vV

open CategoryTheory Limits MonoidalCategory
open CategoryTheory.MonoidalCategory

namespace CategoryTheory.Spectra.Symmetric.OperatorCoend

local notation "I" => Operad.SmallFinBijGroupoid

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V] [SymmetricCategory V]
  [HasColimitsOfSize.{0, 0} V]

/-- The entire source-index cocone precomposes all original finite labels. -/
def sourceCocone (T : V) {n k : I} (f : n ⟶ k) (l : I) : Cocone (diagram T k l) where
  pt := Hom T n l
  ι :=
    { app q := generator T q.left n l ((q.left ◁ f) ≫ q.hom)
      naturality := by
        intro q q' r
        simp only [Functor.const_obj_map]
        have h := generator_relation T r.left ((q'.left ◁ f) ≫ q'.hom)
        have hl : (r.left ▷ n) ≫ ((q'.left ◁ f) ≫ q'.hom) = (q.left ◁ f) ≫ q.hom := by
          calc
            _ = ((r.left ▷ n) ≫ (q'.left ◁ f)) ≫ q'.hom := (Category.assoc _ _ _).symm
            _ = ((q.left ◁ f) ≫ (r.left ▷ k)) ≫ q'.hom :=
              congrArg (fun t => t ≫ q'.hom) (whisker_exchange r.left f).symm
            _ = (q.left ◁ f) ≫ q.hom :=
              (Category.assoc _ _ _).trans (congrArg (fun t => (q.left ◁ f) ≫ t) r.w)
        exact h.trans ((congrArg (generator T q.left n l) hl).trans (Category.comp_id _).symm) }

/-- The actual source-index map on the whole original Hom coend. -/
def sourceMap (T : V) {n k : I} (f : n ⟶ k) (l : I) : Hom T k l ⟶ Hom T n l :=
  colimit.desc (diagram T k l) (sourceCocone T f l)

/-- Each full original generator retains its actual source-precomposition formula. -/
theorem generator_sourceMap (T : V) (a n k l : I) (f : n ⟶ k) (r : a ⊗ k ⟶ l) :
    generator T a k l r ≫ sourceMap T f l = generator T a n l ((a ◁ f) ≫ r) := by
  unfold sourceMap
  exact colimit.ι_desc (sourceCocone T f l) (CostructuredArrow.mk (Y := a) r)

/-- Original source identities act as identities on the complete Hom coend. -/
theorem sourceMap_id (T : V) (n l : I) : sourceMap T (𝟙 n) l = 𝟙 (Hom T n l) := by
  apply hom_ext T n l
  intro a r
  have hl : ((a ◁ 𝟙 n) ≫ r) = r := by rw [whiskerLeft_id, Category.id_comp]
  exact (generator_sourceMap T a n n l (𝟙 n) r).trans
    ((congrArg (generator T a n l) hl).trans (Category.comp_id _).symm)

/-- Original source composites act contravariantly on the complete Hom coend. -/
theorem sourceMap_comp (T : V) {n k l : I} (f : n ⟶ k) (g : k ⟶ l) (m : I) :
    sourceMap T (f ≫ g) m = sourceMap T g m ≫ sourceMap T f m := by
  apply hom_ext T l m
  intro a r
  have hl : (a ◁ (f ≫ g)) ≫ r = (a ◁ f) ≫ ((a ◁ g) ≫ r) := by
    rw [whiskerLeft_comp, Category.assoc]
  exact (generator_sourceMap T a n l m (f ≫ g) r).trans
    ((congrArg (generator T a n m) hl).trans
      ((generator_sourceMap T a n k m f ((a ◁ g) ≫ r)).symm.trans
        ((congrArg (fun t => t ≫ sourceMap T f m)
          (generator_sourceMap T a k l m g r).symm).trans (Category.assoc _ _ _))))

/-- All original source and target maps commute on the whole Hom coend. -/
theorem sourceMap_targetMap (T : V) {n k l m : I} (f : n ⟶ k) (g : l ⟶ m) :
    sourceMap T f l ≫ targetMap T n g = targetMap T k g ≫ sourceMap T f m := by
  apply hom_ext T k l
  intro a r
  have hL : generator T a k l r ≫ sourceMap T f l ≫ targetMap T n g =
      generator T a n m (((a ◁ f) ≫ r) ≫ g) := by
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (fun t => t ≫ targetMap T n g) (generator_sourceMap T a n k l f r)).trans
        (generator_targetMap T a n l m ((a ◁ f) ≫ r) g))
  have hR : generator T a k l r ≫ targetMap T k g ≫ sourceMap T f m =
      generator T a n m ((a ◁ f) ≫ (r ≫ g)) := by
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (fun t => t ≫ sourceMap T f m) (generator_targetMap T a k l m r g)).trans
        (generator_sourceMap T a n k m f (r ≫ g)))
  exact hL.trans ((congrArg (generator T a n m) (Category.assoc _ _ _)).trans hR.symm)

variable [∀ X : V, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]

/-- Composition with each original source arrow is the whole source-index map. -/
theorem arrow_composition_sourceMap (T : V) {n k : I} (f : n ⟶ k) (l : I) :
    (arrow T f ▷ Hom T k l) ≫ composition T n k l = (λ_ (Hom T k l)).hom ≫ sourceMap T f l := by
  apply (isColimitOfPreserves (tensorLeft (𝟙_ V)) (colimit.isColimit (diagram T k l))).hom_ext
  intro q
  let P := Operad.SmallFinBijGroupoid.tensorPowerFunctor T
  let j : P.obj q.left ⟶ Hom T k l := generator T q.left k l q.hom
  let e : (𝟙_ V) ⟶ Hom T n k := arrow T f
  have hPrefix : ((𝟙_ V) ◁ j) ≫ (e ▷ Hom T k l) = e ⊗ₘ j := (tensorHom_def' e j).symm
  have hComp : (e ⊗ₘ j) ≫ composition T n k l =
      (λ_ (P.obj q.left)).hom ≫ generator T q.left n l ((q.left ◁ f) ≫ q.hom) :=
    arrow_generator T q.left n k l f q.hom
  have hNat : ((𝟙_ V) ◁ j) ≫ (λ_ (Hom T k l)).hom = (λ_ (P.obj q.left)).hom ≫ j :=
    leftUnitor_naturality j
  have hFac : j ≫ sourceMap T f l = generator T q.left n l ((q.left ◁ f) ≫ q.hom) :=
    generator_sourceMap T q.left n k l f q.hom
  have hRight : ((𝟙_ V) ◁ j) ≫ (λ_ (Hom T k l)).hom ≫ sourceMap T f l =
      (λ_ (P.obj q.left)).hom ≫ generator T q.left n l ((q.left ◁ f) ≫ q.hom) := by
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (fun t => t ≫ sourceMap T f l) hNat).trans
        ((Category.assoc _ _ _).trans (congrArg (fun t => (λ_ (P.obj q.left)).hom ≫ t) hFac)))
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun t => t ≫ composition T n k l) hPrefix).trans (hComp.trans hRight.symm))

/-- Composition with each original target arrow is the whole target-index map. -/
theorem composition_arrow_targetMap (T : V) (n : I) {k l : I} (f : k ⟶ l) :
    (Hom T n k ◁ arrow T f) ≫ composition T n k l = (ρ_ (Hom T n k)).hom ≫ targetMap T n f := by
  apply (isColimitOfPreserves (tensorRight (𝟙_ V)) (colimit.isColimit (diagram T n k))).hom_ext
  intro q
  let P := Operad.SmallFinBijGroupoid.tensorPowerFunctor T
  let j : P.obj q.left ⟶ Hom T n k := generator T q.left n k q.hom
  let e : (𝟙_ V) ⟶ Hom T k l := arrow T f
  have hPrefix : (j ▷ (𝟙_ V)) ≫ (Hom T n k ◁ e) = j ⊗ₘ e := (tensorHom_def j e).symm
  have hComp : (j ⊗ₘ e) ≫ composition T n k l =
      (ρ_ (P.obj q.left)).hom ≫ generator T q.left n l (q.hom ≫ f) :=
    generator_arrow T q.left n k l q.hom f
  have hNat : (j ▷ (𝟙_ V)) ≫ (ρ_ (Hom T n k)).hom = (ρ_ (P.obj q.left)).hom ≫ j :=
    rightUnitor_naturality j
  have hFac : j ≫ targetMap T n f = generator T q.left n l (q.hom ≫ f) :=
    generator_targetMap T q.left n k l q.hom f
  have hRight : (j ▷ (𝟙_ V)) ≫ (ρ_ (Hom T n k)).hom ≫ targetMap T n f =
      (ρ_ (P.obj q.left)).hom ≫ generator T q.left n l (q.hom ≫ f) := by
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (fun t => t ≫ targetMap T n f) hNat).trans
        ((Category.assoc _ _ _).trans (congrArg (fun t => (ρ_ (P.obj q.left)).hom ≫ t) hFac)))
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun t => t ≫ composition T n k l) hPrefix).trans (hComp.trans hRight.symm))

end CategoryTheory.Spectra.Symmetric.OperatorCoend

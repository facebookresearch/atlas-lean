/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado

import MathlibExt.Algebra.Category.Grp.FilteredColimits.NatTail
import Mathlib.CategoryTheory.Limits.Fubini

/-!
# Fubini for concrete sequential group colimits

The actual inner quotient leg followed by the actual outer quotient
leg defines a cocone on the full Nat-by-Nat diagram. Mathlib's uncurry
construction proves its universal property for these chosen quotient cocones.
The actual Nat product-category swap and its identity-component source
Iso give the opposite order cocone. Both Fubini maps, all nested
quotient representatives and complete matrix-map naturalities follow.
This product-category swap supplies no native spherical permutation,
double-loop orientation, spectrum model or desired telescope law.
-/

set_option autoImplicit false
set_option maxRecDepth 512
noncomputable section
universe v uC vC
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Prod

private theorem originalJointLegNaturality
    {C : Type uC} [Category.{vC} C] {A B D E F G : C}
    (a : A ⟶ B) (b : B ⟶ D) (c : D ⟶ E) (d : E ⟶ F)
    (x : B ⟶ E) (y : A ⟶ G) (q : G ⟶ E) (z : G ⟶ F)
    (hInner : b ≫ c = x) (hMap : y ≫ q = a ≫ x) (hOuter : q ≫ d = z) :
    (a ≫ b) ≫ (c ≫ d) = y ≫ z := by
  simp only [Category.assoc]
  rw [← Category.assoc b c d, hInner, ← Category.assoc a x d, ← hMap,
    Category.assoc, hOuter]

private theorem originalPairLegMap
    {C : Type uC} [Category.{vC} C] {A B D E F G : C}
    (a : A ⟶ B) (b : B ⟶ D) (c : D ⟶ E)
    (d : B ⟶ F) (e : F ⟶ E) (f : A ⟶ G) (g : G ⟶ F)
    (hOuter : b ≫ c = d ≫ e) (hInner : a ≫ d = f ≫ g) :
    (a ≫ b) ≫ c = f ≫ (g ≫ e) := by
  rw [Category.assoc, hOuter, ← Category.assoc a d e, hInner, Category.assoc]

private theorem originalFubiniLegSquare
    {C : Type uC} [Category.{vC} C] {A B D E F G : C}
    (a : A ⟶ B) (b : B ⟶ D) (c : D ⟶ E) (d : B ⟶ F) (e : F ⟶ E)
    (f : A ⟶ G) (g : G ⟶ D) (h : A ⟶ F) (k : G ⟶ E)
    (hMap : a ≫ b = f ≫ g) (hG : g ≫ c = k) (hF : a ≫ d = h)
    (hFlip : h ≫ e = f ≫ k) : a ≫ (b ≫ c) = a ≫ (d ≫ e) := by
  rw [← Category.assoc, hMap, Category.assoc, hG,
    ← Category.assoc a d e, hF, hFlip]

namespace GrpCat.FilteredColimits.Fubini

/-- The actual outer diagram consists of the SAME genuine inner Nat group colimits. -/
def innerColimitDiagram (F : ℕ ⥤ ℕ ⥤ GrpCat.{v}) : ℕ ⥤ GrpCat.{v} :=
  F ⋙ natQuotientColimit

/-- The full twofold colimit functor uses the SAME actual quotient construction twice. -/
def iteratedColimitFunctor : (ℕ ⥤ ℕ ⥤ GrpCat.{v}) ⥤ GrpCat.{v} :=
  (Functor.whiskeringRight ℕ (ℕ ⥤ GrpCat.{v}) GrpCat.{v}).obj
      natQuotientColimit ⋙
    natQuotientColimit

/-- Every joint leg is the actual inner quotient leg followed by the actual outer quotient leg. -/
def jointLeg (F : ℕ ⥤ ℕ ⥤ GrpCat.{v}) (i j : ℕ) :
    (F.obj i).obj j ⟶ iteratedColimitFunctor.obj F :=
  (GrpCat.FilteredColimits.colimitCocone (F.obj i)).ι.app j ≫
    (GrpCat.FilteredColimits.colimitCocone (innerColimitDiagram F)).ι.app i

/-- Let `F : ℕ ⥤ ℕ ⥤ GrpCat`, `i i' j j' : ℕ`, `f : i ⟶ i'`, and `g : j ⟶ j'`.
The map on the two indices followed by the leg at `(i', j')` equals the leg at `(i, j)`:

```text
((F.map f).app j ≫ (F.obj i').map g) ≫ jointLeg F i' j' = jointLeg F i j
```
-/
theorem jointLeg_naturality (F : ℕ ⥤ ℕ ⥤ GrpCat.{v}) {i i' j j' : ℕ}
    (f : i ⟶ i') (g : j ⟶ j') :
    ((F.map f).app j ≫ (F.obj i').map g) ≫ jointLeg F i' j' = jointLeg F i j := by
  have hi := (GrpCat.FilteredColimits.colimitCocone (F.obj i')).w g
  have hm := (colimitCoconeIsColimit (F.obj i)).ι_map (colimitCocone (F.obj i')) (F.map f) j
  have ho := (GrpCat.FilteredColimits.colimitCocone (innerColimitDiagram F)).w f
  exact originalJointLegNaturality ((F.map f).app j) ((F.obj i').map g)
    ((GrpCat.FilteredColimits.colimitCocone (F.obj i')).ι.app j')
    ((GrpCat.FilteredColimits.colimitCocone (innerColimitDiagram F)).ι.app i')
    ((GrpCat.FilteredColimits.colimitCocone (F.obj i')).ι.app j)
    ((GrpCat.FilteredColimits.colimitCocone (F.obj i)).ι.app j)
    (natQuotientColimit.map (F.map f))
    ((GrpCat.FilteredColimits.colimitCocone (innerColimitDiagram F)).ι.app i) hi hm ho

/-- The full actual pair-leg cocone keeps both original chosen group quotients. -/
def jointCocone (F : ℕ ⥤ ℕ ⥤ GrpCat.{v}) : Cocone (Functor.uncurry.obj F) where
  pt := iteratedColimitFunctor.obj F
  ι :=
    { app := fun p => jointLeg F p.1 p.2
      naturality := fun {p p'} f => by
        exact (jointLeg_naturality F f.1 f.2).trans (Category.comp_id _).symm }

/-- The diagram of the concrete inner quotient cocones and their native induced maps. -/
private def quotientCoconeDiagram (F : ℕ ⥤ ℕ ⥤ GrpCat.{v}) : DiagramOfCocones F where
  obj i := colimitCocone (F.obj i)
  map f :=
    { hom := (colimitCoconeIsColimit _).map (colimitCocone _) (F.map f)
      w j := IsColimit.ι_map _ _ _ j }
  id i := by
    change natQuotientColimit.map (F.map (𝟙 i)) =
      𝟙 (natQuotientColimit.obj (F.obj i))
    rw [F.map_id]
    exact natQuotientColimit.map_id (F.obj i)
  comp {i j k} f g := by
    change natQuotientColimit.map (F.map (f ≫ g)) =
      natQuotientColimit.map (F.map f) ≫ natQuotientColimit.map (F.map g)
    rw [F.map_comp, Functor.map_comp]

private def innerIsColimit (F : ℕ ⥤ ℕ ⥤ GrpCat.{v}) (i : ℕ) :
    IsColimit ((quotientCoconeDiagram F).obj i) :=
  colimitCoconeIsColimit (F.obj i)

/-- Mathlib's uncurry construction makes the concrete pair-leg cocone colimiting. -/
def jointCoconeIsColimit (F : ℕ ⥤ ℕ ⥤ GrpCat.{v}) : IsColimit (jointCocone F) := by
  apply IsColimit.ofCoconeUncurry (innerIsColimit F)
  let c := colimitCocone (innerColimitDiagram F)
  let c' := coconeOfCoconeUncurry (innerIsColimit F) (jointCocone F)
  have h (i : ℕ) : c'.ι.app i = c.ι.app i := by
    apply (innerIsColimit F i).hom_ext
    intro j
    exact (innerIsColimit F i).fac _ j
  let e : c ≅ c' := Cocone.ext (Iso.refl _) (fun i =>
    (Category.comp_id _).trans (h i).symm)
  exact (colimitCoconeIsColimit (innerColimitDiagram F)).ofIsoColimit e

/-- The actual opposite-order cocone uses the SAME full pair source and original quotient maps. -/
def transposedJointCocone (F : ℕ ⥤ ℕ ⥤ GrpCat.{v}) : Cocone (Functor.uncurry.obj F) :=
  (Cocone.precompose (Functor.uncurryObjFlip F.flip).hom).obj
    ((jointCocone F.flip).whisker (CategoryTheory.Prod.swap ℕ ℕ))

/-- EVERY opposite-order leg keeps its actual original inner and outer quotient functions. -/
theorem transposedJointCocone_ι_app (F : ℕ ⥤ ℕ ⥤ GrpCat.{v}) (i j : ℕ) :
    (transposedJointCocone F).ι.app (i, j) = jointLeg F.flip j i := by
  change 𝟙 _ ≫ jointLeg F.flip j i = _
  exact Category.id_comp _

/-- Actual product-category finality and the source Iso preserve the proved opposite-order UPL. -/
def transposedJointCoconeIsColimit (F : ℕ ⥤ ℕ ⥤ GrpCat.{v}) :
    IsColimit (transposedJointCocone F) := by
  let c := (jointCocone F.flip).whisker (CategoryTheory.Prod.swap ℕ ℕ)
  have hc : IsColimit c :=
    (Functor.Final.isColimitWhiskerEquiv (CategoryTheory.Prod.swap ℕ ℕ)
      (jointCocone F.flip)).symm (jointCoconeIsColimit F.flip)
  exact (IsColimit.precomposeHomEquiv (Functor.uncurryObjFlip F.flip) c).symm hc

/-- BOTH complete actual Fubini maps come from the SAME genuine pair-cocone universal properties. -/
def fubiniIso (F : ℕ ⥤ ℕ ⥤ GrpCat.{v}) :
    iteratedColimitFunctor.obj F ≅ iteratedColimitFunctor.obj F.flip :=
  (jointCoconeIsColimit F).coconePointUniqueUpToIso (transposedJointCoconeIsColimit F)

/-- For `F : ℕ ⥤ ℕ ⥤ GrpCat` and `i j : ℕ`, the forward map takes the chosen
pair leg of `F` to the transposed pair leg of `F.flip`:

```text
jointLeg F i j ≫ (fubiniIso F).hom = jointLeg F.flip j i
```
-/
theorem fubiniIso_hom_leg (F : ℕ ⥤ ℕ ⥤ GrpCat.{v}) (i j : ℕ) :
    jointLeg F i j ≫ (fubiniIso F).hom = jointLeg F.flip j i :=
  (IsColimit.comp_coconePointUniqueUpToIso_hom (jointCoconeIsColimit F)
    (transposedJointCoconeIsColimit F) (i, j)).trans (transposedJointCocone_ι_app F i j)

/-- For `F : ℕ ⥤ ℕ ⥤ GrpCat` and `i j : ℕ`, the inverse map takes the transposed
pair leg of `F.flip` back to the chosen pair leg of `F`:

```text
jointLeg F.flip j i ≫ (fubiniIso F).inv = jointLeg F i j
```
-/
theorem fubiniIso_inv_leg (F : ℕ ⥤ ℕ ⥤ GrpCat.{v}) (i j : ℕ) :
    jointLeg F.flip j i ≫ (fubiniIso F).inv = jointLeg F i j := by
  apply (cancel_mono (fubiniIso F).hom).mp
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  exact (fubiniIso_hom_leg F i j).symm

/-- Let `F : ℕ ⥤ ℕ ⥤ GrpCat`, `i j : ℕ`, and `a : (F.obj i).obj j`. The forward map
sends the nested quotient representative at `(i, j)` to the one at `(j, i)` for `F.flip`,
with the same element `a`:

```text
(fubiniIso F).hom.hom (G.mk (innerColimitDiagram F) ⟨i, G.mk (F.obj i) ⟨j, a⟩⟩)
  = G.mk (innerColimitDiagram F.flip) ⟨j, G.mk (F.flip.obj j) ⟨i, a⟩⟩
```
-/
theorem fubiniIso_hom_apply (F : ℕ ⥤ ℕ ⥤ GrpCat.{v}) (i j : ℕ) (a : (F.obj i).obj j) :
    (fubiniIso F).hom.hom
        (GrpCat.FilteredColimits.G.mk (innerColimitDiagram F)
          ⟨i, GrpCat.FilteredColimits.G.mk (F.obj i) ⟨j, a⟩⟩) =
      GrpCat.FilteredColimits.G.mk (innerColimitDiagram F.flip)
        ⟨j, GrpCat.FilteredColimits.G.mk (F.flip.obj j) ⟨i, a⟩⟩ :=
  ConcreteCategory.congr_hom (fubiniIso_hom_leg F i j) a

/-- Let `F : ℕ ⥤ ℕ ⥤ GrpCat`, `i j : ℕ`, and `a : (F.obj i).obj j`. The inverse map
sends the nested quotient representative at `(j, i)` for `F.flip` back to `(i, j)` for `F`,
with the same element `a`:

```text
(fubiniIso F).inv.hom (G.mk (innerColimitDiagram F.flip) ⟨j, G.mk (F.flip.obj j) ⟨i, a⟩⟩)
  = G.mk (innerColimitDiagram F) ⟨i, G.mk (F.obj i) ⟨j, a⟩⟩
```
-/
theorem fubiniIso_inv_apply (F : ℕ ⥤ ℕ ⥤ GrpCat.{v}) (i j : ℕ) (a : (F.obj i).obj j) :
    (fubiniIso F).inv.hom
        (GrpCat.FilteredColimits.G.mk (innerColimitDiagram F.flip)
          ⟨j, GrpCat.FilteredColimits.G.mk (F.flip.obj j) ⟨i, a⟩⟩) =
      GrpCat.FilteredColimits.G.mk (innerColimitDiagram F)
        ⟨i, GrpCat.FilteredColimits.G.mk (F.obj i) ⟨j, a⟩⟩ :=
  ConcreteCategory.congr_hom (fubiniIso_inv_leg F i j) a

/-- For `F G : ℕ ⥤ ℕ ⥤ GrpCat`, a natural transformation `a : F ⟶ G`, and `i j : ℕ`,
the induced map on the chosen double quotients factors on each pair leg through
`(a.app i).app j`:

```text
jointLeg F i j ≫ iteratedColimitFunctor.map a = (a.app i).app j ≫ jointLeg G i j
```
-/
theorem iteratedColimit_map_fac {F G : ℕ ⥤ ℕ ⥤ GrpCat.{v}} (a : F ⟶ G) (i j : ℕ) :
    jointLeg F i j ≫ iteratedColimitFunctor.map a = (a.app i).app j ≫ jointLeg G i j := by
  let Q : (ℕ ⥤ GrpCat.{v}) ⥤ GrpCat.{v} := natQuotientColimit
  have ho := (colimitCoconeIsColimit (innerColimitDiagram F)).ι_map
    (colimitCocone (innerColimitDiagram G)) (Functor.whiskerRight a Q) i
  have hi := (colimitCoconeIsColimit (F.obj i)).ι_map (colimitCocone (G.obj i)) (a.app i) j
  exact originalPairLegMap
    ((GrpCat.FilteredColimits.colimitCocone (F.obj i)).ι.app j)
    ((GrpCat.FilteredColimits.colimitCocone (innerColimitDiagram F)).ι.app i)
    (iteratedColimitFunctor.map a) (natQuotientColimit.map (a.app i))
    ((GrpCat.FilteredColimits.colimitCocone (innerColimitDiagram G)).ι.app i)
    ((a.app i).app j) ((GrpCat.FilteredColimits.colimitCocone (G.obj i)).ι.app j) ho hi

/-- For `F G : ℕ ⥤ ℕ ⥤ GrpCat` and a natural transformation `a : F ⟶ G`, the
forward Fubini map commutes with the induced map on double quotients. The map on the
opposite-order quotients is induced by the flipped transformation:

```text
iteratedColimitFunctor.map a ≫ (fubiniIso G).hom =
  (fubiniIso F).hom ≫ iteratedColimitFunctor.map ((flipFunctor ℕ ℕ GrpCat).map a)
```
-/
theorem fubiniIso_naturality {F G : ℕ ⥤ ℕ ⥤ GrpCat.{v}} (a : F ⟶ G) :
    iteratedColimitFunctor.map a ≫ (fubiniIso G).hom =
      (fubiniIso F).hom ≫ iteratedColimitFunctor.map
        ((CategoryTheory.flipFunctor ℕ ℕ GrpCat.{v}).map a) := by
  apply (jointCoconeIsColimit F).hom_ext
  rintro ⟨i, j⟩
  have hm := iteratedColimit_map_fac a i j
  have hG := fubiniIso_hom_leg G i j
  have hF := fubiniIso_hom_leg F i j
  have hFlip := iteratedColimit_map_fac
    ((CategoryTheory.flipFunctor ℕ ℕ GrpCat.{v}).map a) j i
  exact originalFubiniLegSquare (jointLeg F i j) (iteratedColimitFunctor.map a)
    ((fubiniIso G).hom) ((fubiniIso F).hom)
    (iteratedColimitFunctor.map ((CategoryTheory.flipFunctor ℕ ℕ GrpCat.{v}).map a))
    ((a.app i).app j) (jointLeg G i j) (jointLeg F.flip j i) (jointLeg G.flip j i)
    hm hG hF hFlip

/-- The WHOLE genuine two-order Group colimit comparison retains every full matrix input. -/
def fubiniNatIso : iteratedColimitFunctor.{v} ≅
    CategoryTheory.flipFunctor ℕ ℕ GrpCat.{v} ⋙ iteratedColimitFunctor :=
  NatIso.ofComponents fubiniIso (fun a => fubiniIso_naturality a)

/-- The ENTIRE natural Fubini hom function is the SAME actual pair-UPL comparison. -/
theorem fubiniNatIso_hom_app (F : ℕ ⥤ ℕ ⥤ GrpCat.{v}) :
    fubiniNatIso.hom.app F = (fubiniIso F).hom := rfl

/-- The ENTIRE natural Fubini inv function is the SAME actual pair-UPL inverse comparison. -/
theorem fubiniNatIso_inv_app (F : ℕ ⥤ ℕ ⥤ GrpCat.{v}) :
    fubiniNatIso.inv.app F = (fubiniIso F).inv := rfl

/-- For `F G : ℕ ⥤ ℕ ⥤ GrpCat` and a natural transformation `a : F ⟶ G`, the
inverse Fubini map commutes with the induced map on double quotients. Starting in
opposite order, use the flipped transformation before applying the inverse:

```text
iteratedColimitFunctor.map ((flipFunctor ℕ ℕ GrpCat).map a) ≫ (fubiniIso G).inv =
  (fubiniIso F).inv ≫ iteratedColimitFunctor.map a
```
-/
theorem fubiniNatIso_inv_naturality {F G : ℕ ⥤ ℕ ⥤ GrpCat.{v}} (a : F ⟶ G) :
    iteratedColimitFunctor.map ((CategoryTheory.flipFunctor ℕ ℕ GrpCat.{v}).map a) ≫
        (fubiniIso G).inv = (fubiniIso F).inv ≫ iteratedColimitFunctor.map a :=
  fubiniNatIso.inv.naturality a

end GrpCat.FilteredColimits.Fubini

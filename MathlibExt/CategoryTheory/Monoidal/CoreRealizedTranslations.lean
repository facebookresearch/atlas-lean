/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.CategoryTheory.Preadditive.Basic
public import MathlibExt.CategoryTheory.Monoidal.ActionLocalization
public import MathlibExt.CategoryTheory.Limits.Shapes.CoreBiproductMonoidal
public import MathlibExt.CategoryTheory.Monoidal.SInverseS
public import MathlibExt.CategoryTheory.Monoidal.SInverseSTranslationAction
public import MathlibExt.CategoryTheory.NerveCrossUniverse
public import
  MathlibExt.AlgebraicTopology.TopologicalSpace.SimplicialRealization.PointSet.SSetRealizeHomotopy
public import Mathlib.Topology.Homotopy.Equiv

/-!
# Actual generic right-positive and right-negative realized homotopy equivalences

The constructed model comparison, right translations and positive braiding
are carried once below. Negative braiding is derived from the actual raw
coordinate swap. The two published legacy diagonal transformations are
transported through the model unit and counit to the exact generic P/N
composites. Ordinary nerve maps at shared object-u and Hom-max(u,v)
retain the independent original universes u and v.

Only the realized continuous homotopies are reversed. The resulting unbased
HomotopyEquiv has realized P forward and realized N backward exactly. The
positive object A ⊞ X and negative denominator den ⊞ X retain their full
+[X] and −[X] offsets. No CW, Kan, split-exactness or based-preservation
premise is used; no kernel/middle equivalence or full Q-plus theorem follows
from this source alone.
-/

@[expose] public section

universe u v

open CategoryTheory.MonoidalActionCategory

noncomputable section

set_option autoImplicit false

open CategoryTheory Limits ZeroObject
open CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Limits.CoreBiprodMonoidal MonoidalCategory
open scoped CategoryTheory.MonoidalCategory.MonoidalLeftAction

namespace CategoryTheory.CoreLocalizationComparison

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C]

attribute [local instance] MonoidalActionCategory.diagonalAction

/-- Forget the two actual Core wrappers, retaining positive-first coordinates. -/
def toPairObj (a : SInverse (Core C) (Core C)) : SInverseS.Pair C :=
  ⟨a.of.1.of, a.of.2.of⟩

/-- Wrap the two actual additive coordinates in the original core. -/
def fromPairObj (a : SInverseS.Pair C) : SInverse (Core C) (Core C) :=
  ⟨((⟨a.fst⟩ : Core C), (⟨a.snd⟩ : Core C))⟩

/-- The raw forward map keeps the original two isomorphisms and stabilizer object. -/
def toPairRaw {a b : SInverse (Core C) (Core C)}
    (r : MonoidalActionCategory.RawHom a b) : SInverseS.RawHom (toPairObj a) (toPairObj b) where
  stabilizer := r.stabilizer.of
  hom₁ := r.hom.1.iso
  hom₂ := r.hom.2.iso

/-- The raw inverse wraps the same stabilizer and both original isomorphisms. -/
def fromPairRaw {a b : SInverseS.Pair C} (r : SInverseS.RawHom a b) :
    MonoidalActionCategory.RawHom (fromPairObj a) (fromPairObj b) where
  stabilizer := ⟨r.stabilizer⟩
  hom := (⟨r.hom₁⟩, ⟨r.hom₂⟩)

/-- The generic object roundtrip is the original pair, not a replacement object. -/
theorem from_to_Obj (a : SInverse (Core C) (Core C)) : fromPairObj (toPairObj a) = a := rfl

/-- The additive object roundtrip is the original pair. -/
theorem to_from_Obj (a : SInverseS.Pair C) : toPairObj (fromPairObj a) = a := rfl

/-- The generic raw roundtrip retains all original data. -/
theorem from_to_Raw {a b : SInverse (Core C) (Core C)}
    (r : MonoidalActionCategory.RawHom a b) : fromPairRaw (toPairRaw r) = r := rfl

/-- The additive raw roundtrip retains all original data. -/
theorem to_from_Raw {a b : SInverseS.Pair C} (r : SInverseS.RawHom a b) :
    toPairRaw (fromPairRaw r) = r := rfl

private theorem right_whisker_hom {T U : Core C} (e : T ⟶ U) (A : Core C) :
    (e ▷ A).iso.hom = biprod.map e.iso.hom (𝟙 A.of) := by
  rewrite [← tensorHom_id, coreBiprodTensorHom_iso_hom]
  rfl

private theorem left_whisker_hom (T : Core C) {A B : Core C} (e : A ⟶ B) :
    (T ◁ e).iso.hom = biprod.map (𝟙 T.of) e.iso.hom :=
  (coreBiprodTensorLeft_map_iso_hom T e).trans
    (coreLeftBiprodFunctor_map_iso_hom T.of e)

/-- The forward relation map uses the actual underlying stabilizer isomorphism. -/
theorem toPairRaw_rel {a b : SInverse (Core C) (Core C)}
    {r s : MonoidalActionCategory.RawHom a b} (h : r.Rel s) :
    (toPairRaw r).Rel (toPairRaw s) := by
  obtain ⟨e, he⟩ := h
  refine ⟨e.hom.iso, ?_, ?_⟩
  · apply Iso.ext
    have hA := congrArg
      (fun q : (r.stabilizer ⊙ₗ a.of) ⟶ b.of => q.1.iso.hom) he
    change (e.hom ▷ a.of.1).iso.hom ≫ s.hom.1.iso.hom = r.hom.1.iso.hom at hA
    change biprod.map e.hom.iso.hom (𝟙 a.of.1.of) ≫ s.hom.1.iso.hom =
      r.hom.1.iso.hom
    exact (congrArg
      (fun k : r.stabilizer.of ⊞ a.of.1.of ⟶ s.stabilizer.of ⊞ a.of.1.of =>
        k ≫ s.hom.1.iso.hom) (right_whisker_hom e.hom a.of.1).symm).trans hA
  · apply Iso.ext
    have hB := congrArg
      (fun q : (r.stabilizer ⊙ₗ a.of) ⟶ b.of => q.2.iso.hom) he
    change (e.hom ▷ a.of.2).iso.hom ≫ s.hom.2.iso.hom = r.hom.2.iso.hom at hB
    change biprod.map e.hom.iso.hom (𝟙 a.of.2.of) ≫ s.hom.2.iso.hom =
      r.hom.2.iso.hom
    exact (congrArg
      (fun k : r.stabilizer.of ⊞ a.of.2.of ⟶ s.stabilizer.of ⊞ a.of.2.of =>
        k ≫ s.hom.2.iso.hom) (right_whisker_hom e.hom a.of.2).symm).trans hB

/-- The inverse relation map wraps the actual stabilizer isomorphism via Core.isoMk. -/
theorem fromPairRaw_rel {a b : SInverseS.Pair C} {r s : SInverseS.RawHom a b}
    (h : r.Rel s) : (fromPairRaw r).Rel (fromPairRaw s) := by
  obtain ⟨e, h1, h2⟩ := h
  let E : (⟨r.stabilizer⟩ : Core C) ≅ (⟨s.stabilizer⟩ : Core C) := Core.isoMk e
  refine ⟨E, ?_⟩
  apply Prod.ext
  · apply Core.hom_ext
    have hA : biprod.map e.hom (𝟙 a.fst) ≫ s.hom₁.hom = r.hom₁.hom :=
      congrArg Iso.hom h1
    change (E.hom ▷ (⟨a.fst⟩ : Core C)).iso.hom ≫ s.hom₁.hom = r.hom₁.hom
    exact (congrArg
      (fun k : r.stabilizer ⊞ a.fst ⟶ s.stabilizer ⊞ a.fst => k ≫ s.hom₁.hom)
      (right_whisker_hom E.hom ⟨a.fst⟩)).trans hA
  · apply Core.hom_ext
    have hB : biprod.map e.hom (𝟙 a.snd) ≫ s.hom₂.hom = r.hom₂.hom :=
      congrArg Iso.hom h2
    change (E.hom ▷ (⟨a.snd⟩ : Core C)).iso.hom ≫ s.hom₂.hom = r.hom₂.hom
    exact (congrArg
      (fun k : r.stabilizer ⊞ a.snd ⟶ s.stabilizer ⊞ a.snd => k ≫ s.hom₂.hom)
      (right_whisker_hom E.hom ⟨a.snd⟩)).trans hB

/-- The forward map takes the actual two Core unitors to the actual additive unitors. -/
theorem toPairRaw_id (a : SInverse (Core C) (Core C)) :
    toPairRaw (MonoidalActionCategory.RawHom.id a) = SInverseS.RawHom.id (toPairObj a) := by
  have h1 : (toPairRaw (MonoidalActionCategory.RawHom.id a)).hom₁ =
      (SInverseS.RawHom.id (toPairObj a)).hom₁ := coreBiprodLeftUnitor_iso a.of.1
  have h2 : (toPairRaw (MonoidalActionCategory.RawHom.id a)).hom₂ =
      (SInverseS.RawHom.id (toPairObj a)).hom₂ := coreBiprodLeftUnitor_iso a.of.2
  exact congrArg₂
    (fun (f : (0 : C) ⊞ a.of.1.of ≅ a.of.1.of)
      (g : (0 : C) ⊞ a.of.2.of ≅ a.of.2.of) =>
      (⟨0, f, g⟩ : SInverseS.RawHom (toPairObj a) (toPairObj a))) h1 h2

/-- The forward map preserves actual composition with the same later-before-earlier order. -/
theorem toPairRaw_comp {a b c : SInverse (Core C) (Core C)}
    (r : MonoidalActionCategory.RawHom a b) (s : MonoidalActionCategory.RawHom b c) :
    toPairRaw (r.comp s) = (toPairRaw r).comp (toPairRaw s) := by
  let T : C := s.stabilizer.of ⊞ r.stabilizer.of
  have h1 : (toPairRaw (r.comp s)).hom₁ = ((toPairRaw r).comp (toPairRaw s)).hom₁ := by
    apply Iso.ext
    let A : C := T ⊞ a.of.1.of
    let B : C := s.stabilizer.of ⊞ (r.stabilizer.of ⊞ a.of.1.of)
    let D : C := s.stabilizer.of ⊞ b.of.1.of
    have ha : ((α_ s.stabilizer r.stabilizer a.of.1).hom).iso.hom =
        (biprod.associator s.stabilizer.of r.stabilizer.of a.of.1.of).hom :=
      congrArg Iso.hom (coreBiprodAssociator_iso _ _ _)
    have hw : (s.stabilizer ◁ r.hom.1).iso.hom =
        biprod.map (𝟙 s.stabilizer.of) r.hom.1.iso.hom :=
      left_whisker_hom s.stabilizer r.hom.1
    change ((α_ s.stabilizer r.stabilizer a.of.1).hom).iso.hom ≫
        (s.stabilizer ◁ r.hom.1).iso.hom ≫ s.hom.1.iso.hom =
      (biprod.associator s.stabilizer.of r.stabilizer.of a.of.1.of).hom ≫
        biprod.map (𝟙 s.stabilizer.of) r.hom.1.iso.hom ≫ s.hom.1.iso.hom
    exact congrArg₂ (fun (f : A ⟶ B) (g : B ⟶ D) => f ≫ g ≫ s.hom.1.iso.hom) ha hw
  have h2 : (toPairRaw (r.comp s)).hom₂ = ((toPairRaw r).comp (toPairRaw s)).hom₂ := by
    apply Iso.ext
    let A : C := T ⊞ a.of.2.of
    let B : C := s.stabilizer.of ⊞ (r.stabilizer.of ⊞ a.of.2.of)
    let D : C := s.stabilizer.of ⊞ b.of.2.of
    have ha : ((α_ s.stabilizer r.stabilizer a.of.2).hom).iso.hom =
        (biprod.associator s.stabilizer.of r.stabilizer.of a.of.2.of).hom :=
      congrArg Iso.hom (coreBiprodAssociator_iso _ _ _)
    have hw : (s.stabilizer ◁ r.hom.2).iso.hom =
        biprod.map (𝟙 s.stabilizer.of) r.hom.2.iso.hom :=
      left_whisker_hom s.stabilizer r.hom.2
    change ((α_ s.stabilizer r.stabilizer a.of.2).hom).iso.hom ≫
        (s.stabilizer ◁ r.hom.2).iso.hom ≫ s.hom.2.iso.hom =
      (biprod.associator s.stabilizer.of r.stabilizer.of a.of.2.of).hom ≫
        biprod.map (𝟙 s.stabilizer.of) r.hom.2.iso.hom ≫ s.hom.2.iso.hom
    exact congrArg₂ (fun (f : A ⟶ B) (g : B ⟶ D) => f ≫ g ≫ s.hom.2.iso.hom) ha hw
  exact congrArg₂
    (fun (f : T ⊞ a.of.1.of ≅ c.of.1.of) (g : T ⊞ a.of.2.of ≅ c.of.2.of) =>
      (⟨T, f, g⟩ : SInverseS.RawHom (toPairObj a) (toPairObj c))) h1 h2

private theorem toPairRaw_injective {a b : SInverse (Core C) (Core C)}
    (r s : MonoidalActionCategory.RawHom a b) (h : toPairRaw r = toPairRaw s) : r = s :=
  (from_to_Raw r).symm.trans ((congrArg fromPairRaw h).trans (from_to_Raw s))

/-- The inverse map preserves the actual generic unit representative. -/
theorem fromPairRaw_id (a : SInverseS.Pair C) :
    fromPairRaw (SInverseS.RawHom.id a) =
      MonoidalActionCategory.RawHom.id (fromPairObj a) := by
  apply toPairRaw_injective
  exact (to_from_Raw (SInverseS.RawHom.id a)).trans (toPairRaw_id (fromPairObj a)).symm

/-- The inverse map preserves composition and both original isomorphism fields. -/
theorem fromPairRaw_comp {a b c : SInverseS.Pair C}
    (r : SInverseS.RawHom a b) (s : SInverseS.RawHom b c) :
    fromPairRaw (r.comp s) = (fromPairRaw r).comp (fromPairRaw s) := by
  apply toPairRaw_injective
  have h : toPairRaw ((fromPairRaw r).comp (fromPairRaw s)) = r.comp s :=
    (toPairRaw_comp (fromPairRaw r) (fromPairRaw s)).trans
      (congrArg₂ SInverseS.RawHom.comp (to_from_Raw r) (to_from_Raw s))
  exact (to_from_Raw (r.comp s)).trans h.symm

/-- The actual positive-first quotient map to the additive pair category. -/
def toPairHomMap {a b : SInverse (Core C) (Core C)} (f : a ⟶ b) :
    toPairObj a ⟶ toPairObj b :=
  Quotient.map toPairRaw (by
    intro r s h
    exact toPairRaw_rel h) f

/-- The actual positive-first quotient map to the generic core localization. -/
def fromPairHomMap {a b : SInverseS.Pair C} (f : a ⟶ b) :
    fromPairObj a ⟶ fromPairObj b :=
  Quotient.map fromPairRaw (by
    intro r s h
    exact fromPairRaw_rel h) f

/-- The forward quotient map retains the actual raw representative. -/
theorem toPairHomMap_mk {a b : SInverse (Core C) (Core C)}
    (r : MonoidalActionCategory.RawHom a b) :
    toPairHomMap (MonoidalActionCategory.Hom.mk r) = SInverseS.Hom.mk (toPairRaw r) := rfl

/-- The inverse quotient map retains the actual raw representative. -/
theorem fromPairHomMap_mk {a b : SInverseS.Pair C} (r : SInverseS.RawHom a b) :
    fromPairHomMap (SInverseS.Hom.mk r) = MonoidalActionCategory.Hom.mk (fromPairRaw r) := rfl

/-- The actual model comparison functor, retaining both given coordinates. -/
def toPairFunctor : SInverse (Core C) (Core C) ⥤ SInverseS.Pair C where
  obj := toPairObj
  map {a b} f := toPairHomMap f
  map_id a := by
    change SInverseS.Hom.mk (toPairRaw (MonoidalActionCategory.RawHom.id a)) =
      SInverseS.Hom.mk (SInverseS.RawHom.id (toPairObj a))
    exact congrArg SInverseS.Hom.mk (toPairRaw_id a)
  map_comp {a b c} f g := by
    refine Quotient.inductionOn₂ f g ?_
    intro r s
    change SInverseS.Hom.mk (toPairRaw (r.comp s)) =
      SInverseS.Hom.mk ((toPairRaw r).comp (toPairRaw s))
    exact congrArg SInverseS.Hom.mk (toPairRaw_comp r s)

/-- The actual inverse model comparison functor. -/
def fromPairFunctor : SInverseS.Pair C ⥤ SInverse (Core C) (Core C) where
  obj := fromPairObj
  map {a b} f := fromPairHomMap f
  map_id a := by
    change MonoidalActionCategory.Hom.mk (fromPairRaw (SInverseS.RawHom.id a)) =
      MonoidalActionCategory.Hom.mk (MonoidalActionCategory.RawHom.id (fromPairObj a))
    exact congrArg MonoidalActionCategory.Hom.mk (fromPairRaw_id a)
  map_comp {a b c} f g := by
    refine Quotient.inductionOn₂ f g ?_
    intro r s
    change MonoidalActionCategory.Hom.mk (fromPairRaw (r.comp s)) =
      MonoidalActionCategory.Hom.mk ((fromPairRaw r).comp (fromPairRaw s))
    exact congrArg MonoidalActionCategory.Hom.mk (fromPairRaw_comp r s)

/-- The generic morphism roundtrip is the original morphism class. -/
theorem from_to_map {a b : SInverse (Core C) (Core C)} (f : a ⟶ b) :
    (fromPairFunctor (C := C)).map ((toPairFunctor (C := C)).map f) = f := by
  obtain ⟨r, rfl⟩ := MonoidalActionCategory.Hom.exists_rep f
  change MonoidalActionCategory.Hom.mk (fromPairRaw (toPairRaw r)) =
    MonoidalActionCategory.Hom.mk r
  exact congrArg MonoidalActionCategory.Hom.mk (from_to_Raw r)

/-- The additive morphism roundtrip is the original morphism class. -/
theorem to_from_map {a b : SInverseS.Pair C} (f : a ⟶ b) :
    (toPairFunctor (C := C)).map ((fromPairFunctor (C := C)).map f) = f := by
  refine Quotient.inductionOn f ?_
  intro r
  change SInverseS.Hom.mk (toPairRaw (fromPairRaw r)) = SInverseS.Hom.mk r
  exact congrArg SInverseS.Hom.mk (to_from_Raw r)

/-- The unit consists of the actual identities of the original core pairs. -/
def modelUnit : 𝟭 (SInverse (Core C) (Core C)) ≅
    toPairFunctor (C := C) ⋙ fromPairFunctor :=
  NatIso.ofComponents (fun a => Iso.refl a) (by
    intro a b f
    change f ≫ 𝟙 b = 𝟙 a ≫
      (fromPairFunctor (C := C)).map ((toPairFunctor (C := C)).map f)
    have h : (fromPairFunctor (C := C)).map ((toPairFunctor (C := C)).map f) = f :=
      from_to_map f
    exact (Category.comp_id f).trans
      (((congrArg (fun k : a ⟶ b => 𝟙 a ≫ k) h).trans (Category.id_comp f)).symm))

/-- The counit consists of the actual identities of the original additive pairs. -/
def modelCounit : fromPairFunctor (C := C) ⋙ toPairFunctor ≅ 𝟭 (SInverseS.Pair C) :=
  NatIso.ofComponents (fun a => Iso.refl a) (by
    intro a b f
    change (toPairFunctor (C := C)).map ((fromPairFunctor (C := C)).map f) ≫ 𝟙 b =
      𝟙 a ≫ f
    have h : (toPairFunctor (C := C)).map ((fromPairFunctor (C := C)).map f) = f :=
      to_from_map f
    exact (congrArg (fun k : a ⟶ b => k ≫ 𝟙 b) h).trans
      ((Category.comp_id f).trans (Category.id_comp f).symm))

/-- The unit component is the original pair identity. -/
theorem modelUnit_hom_app (a : SInverse (Core C) (Core C)) :
    (modelUnit (C := C)).hom.app a = 𝟙 a := rfl

/-- The counit component is the original pair identity. -/
theorem modelCounit_hom_app (a : SInverseS.Pair C) :
    (modelCounit (C := C)).hom.app a = 𝟙 a := rfl

/-- The actual functor/unit/counit triangle is proved using the original identities. -/
theorem model_triangle (a : SInverse (Core C) (Core C)) :
    (toPairFunctor (C := C)).map ((modelUnit (C := C)).hom.app a) ≫
        (modelCounit (C := C)).hom.app ((toPairFunctor (C := C)).obj a) =
      𝟙 ((toPairFunctor (C := C)).obj a) := by
  let F := toPairFunctor (C := C)
  let b := F.obj a
  change F.map (𝟙 a) ≫ 𝟙 b = 𝟙 b
  exact (congrArg (fun f : b ⟶ b => f ≫ 𝟙 b) (F.map_id a)).trans
    (Category.id_comp (𝟙 b))

/-- The constructed equivalence of the actual two positive-first models. -/
def coreAdditivePairEquivalence : SInverse (Core C) (Core C) ≌ SInverseS.Pair C where
  functor := toPairFunctor
  inverse := fromPairFunctor
  unitIso := modelUnit
  counitIso := modelCounit
  functor_unitIso_comp a := model_triangle a

/-- The equivalence forwards the actual pair without swapping coordinates. -/
theorem coreAdditivePairEquivalence_functor_obj (a : SInverse (Core C) (Core C)) :
    (coreAdditivePairEquivalence (C := C)).functor.obj a = toPairObj a := rfl

/-- Its inverse wraps the same actual pair without swapping coordinates. -/
theorem coreAdditivePairEquivalence_inverse_obj (a : SInverseS.Pair C) :
    (coreAdditivePairEquivalence (C := C)).inverse.obj a = fromPairObj a := rfl

/-- The forward raw denominator is the original denominator isomorphism. -/
theorem toPairRaw_denominator {a b : SInverse (Core C) (Core C)}
    (r : MonoidalActionCategory.RawHom a b) : (toPairRaw r).hom₂ = r.hom.2.iso := rfl

/-- The inverse raw denominator is the original denominator isomorphism. -/
theorem fromPairRaw_denominator {a b : SInverseS.Pair C} (r : SInverseS.RawHom a b) :
    (fromPairRaw r).hom.2.iso = r.hom₂ := rfl

/-- The forward raw stabilizer is the original object of the underlying category. -/
theorem toPairRaw_stabilizer {a b : SInverse (Core C) (Core C)}
    (r : MonoidalActionCategory.RawHom a b) : (toPairRaw r).stabilizer = r.stabilizer.of := rfl

/-- The inverse raw stabilizer is the same object, wrapped in the original core. -/
theorem fromPairRaw_stabilizer {a b : SInverseS.Pair C} (r : SInverseS.RawHom a b) :
    (fromPairRaw r).stabilizer.of = r.stabilizer := rfl

end CategoryTheory.CoreLocalizationComparison

end

noncomputable section

set_option autoImplicit false

open CategoryTheory Limits ZeroObject
open CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Limits.CoreBiprodMonoidal MonoidalCategory
open scoped CategoryTheory.MonoidalCategory.MonoidalLeftAction

namespace CategoryTheory.GenericCoreResidualTranslation

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C]

attribute [local instance] MonoidalActionCategory.diagonalAction

/-- The actual pair functor appending x on the right of the positive coordinate. -/
def positivePairFunctor (x : Core C) : Core C × Core C ⥤ Core C × Core C :=
  (MonoidalCategory.tensorRight x).prod (𝟭 (Core C))

/-- The actual lineator is the inverse associator and the denominator identity. -/
def positiveLineator (x T : Core C) (a : Core C × Core C) :
    T ⊙ₗ (positivePairFunctor x).obj a ⟶ (positivePairFunctor x).obj (T ⊙ₗ a) :=
  ((α_ T a.1 x).inv, 𝟙 (T ⊗ a.2))

/-- Naturality in the actual stabilizer morphism. -/
theorem positiveLineator_naturality_left (x : Core C) {T U : Core C}
    (e : T ⟶ U) (a : Core C × Core C) :
    e ⊵ₗ (positivePairFunctor x).obj a ≫ positiveLineator x U a =
      positiveLineator x T a ≫ (positivePairFunctor x).map (e ⊵ₗ a) := by
  apply Prod.ext
  · exact associator_inv_naturality_left e a.1 x
  · change (e ▷ a.2) ≫ 𝟙 _ = 𝟙 _ ≫ (e ▷ a.2)
    exact (Category.comp_id _).trans (Category.id_comp _).symm

/-- Naturality in the actual pair morphism, including its denominator. -/
theorem positiveLineator_naturality_right (x T : Core C) {a b : Core C × Core C}
    (f : a ⟶ b) :
    T ⊴ₗ (positivePairFunctor x).map f ≫ positiveLineator x T b =
      positiveLineator x T a ≫ (positivePairFunctor x).map (T ⊴ₗ f) := by
  apply Prod.ext
  · exact associator_inv_naturality_middle T f.1 x
  · change (T ◁ f.2) ≫ 𝟙 _ = 𝟙 _ ≫ (T ◁ f.2)
    exact (Category.comp_id _).trans (Category.id_comp _).symm

/-- The lineator pentagon is the actual monoidal pentagon, not an assumed result. -/
theorem positiveLineator_associativity (x T U : Core C) (a : Core C × Core C) :
    positiveLineator x (T ⊗ U) a ≫ (positivePairFunctor x).map (αₗ T U a).hom =
      (αₗ T U ((positivePairFunctor x).obj a)).hom ≫
        T ⊴ₗ positiveLineator x U a ≫ positiveLineator x T (U ⊙ₗ a) := by
  apply Prod.ext
  · change (α_ (T ⊗ U) a.1 x).inv ≫ (α_ T U a.1).hom ▷ x =
      (α_ T U (a.1 ⊗ x)).hom ≫ T ◁ (α_ U a.1 x).inv ≫ (α_ T (U ⊗ a.1) x).inv
    exact (pentagon_hom_inv_inv_inv_hom (W := T) (X := U) (Y := a.1) (Z := x)).symm
  · change 𝟙 _ ≫ (α_ T U a.2).hom =
      (α_ T U a.2).hom ≫ T ◁ (𝟙 _) ≫ 𝟙 _
    simp only [whiskerLeft_id, Category.id_comp, Category.comp_id]

/-- The lineator unit follows from the actual left unitor whiskering law. -/
theorem positiveLineator_unitality (x : Core C) (a : Core C × Core C) :
    positiveLineator x (𝟙_ (Core C)) a ≫ (positivePairFunctor x).map (λₗ a).hom =
      (λₗ ((positivePairFunctor x).obj a)).hom := by
  apply Prod.ext
  · change (α_ (𝟙_ (Core C)) a.1 x).inv ≫ (λ_ a.1).hom ▷ x =
      (λ_ (a.1 ⊗ x)).hom
    exact (congrArg (fun f => (α_ (𝟙_ (Core C)) a.1 x).inv ≫ f)
      (leftUnitor_whiskerRight a.1 x)).trans (by
        simp only [Iso.inv_hom_id_assoc])
  · exact Category.id_comp _

/-- The actual positive right-translation object, with the same denominator. -/
def positiveObj (x : Core C) (a : SInverse (Core C) (Core C)) :
    SInverse (Core C) (Core C) := ⟨(a.of.1 ⊗ x, a.of.2)⟩

/-- Translate the numerator by the actual inverse associator; retain the stabilizer. -/
def positiveRaw (x : Core C) {a b : SInverse (Core C) (Core C)}
    (r : MonoidalActionCategory.RawHom a b) :
    MonoidalActionCategory.RawHom (positiveObj x a) (positiveObj x b) where
  stabilizer := r.stabilizer
  hom := positiveLineator x r.stabilizer a.of ≫ (positivePairFunctor x).map r.hom

/-- The exact positive numerator formula. -/
theorem positiveRaw_numerator (x : Core C) {a b : SInverse (Core C) (Core C)}
    (r : MonoidalActionCategory.RawHom a b) :
    (positiveRaw x r).hom.1 = (α_ r.stabilizer a.of.1 x).inv ≫ r.hom.1 ▷ x := rfl

/-- The denominator map is the original map, by the actual identity composition law. -/
theorem positiveRaw_denominator (x : Core C) {a b : SInverse (Core C) (Core C)}
    (r : MonoidalActionCategory.RawHom a b) : (positiveRaw x r).hom.2 = r.hom.2 :=
  Category.id_comp r.hom.2

/-- The original stabilizer is retained. -/
theorem positiveRaw_stabilizer (x : Core C) {a b : SInverse (Core C) (Core C)}
    (r : MonoidalActionCategory.RawHom a b) : (positiveRaw x r).stabilizer = r.stabilizer := rfl

/-- The actual stabilizer relation is preserved, with the same isomorphism witness. -/
theorem positiveRaw_rel (x : Core C) {a b : SInverse (Core C) (Core C)}
    {r s : MonoidalActionCategory.RawHom a b} (h : r.Rel s) :
    (positiveRaw x r).Rel (positiveRaw x s) := by
  obtain ⟨e, he⟩ := h
  refine ⟨e, ?_⟩
  let F := positivePairFunctor x
  let muR := positiveLineator x r.stabilizer a.of
  let muS := positiveLineator x s.stabilizer a.of
  change e.hom ⊵ₗ F.obj a.of ≫ (muS ≫ F.map s.hom) = muR ≫ F.map r.hom
  calc
    _ = (e.hom ⊵ₗ F.obj a.of ≫ muS) ≫ F.map s.hom := (Category.assoc _ _ _).symm
    _ = (muR ≫ F.map (e.hom ⊵ₗ a.of)) ≫ F.map s.hom :=
      congrArg (fun f => f ≫ F.map s.hom) (positiveLineator_naturality_left x e.hom a.of)
    _ = muR ≫ (F.map (e.hom ⊵ₗ a.of) ≫ F.map s.hom) := Category.assoc _ _ _
    _ = muR ≫ F.map (e.hom ⊵ₗ a.of ≫ s.hom) :=
      congrArg (fun f => muR ≫ f) (F.map_comp _ _).symm
    _ = muR ≫ F.map r.hom := congrArg (fun f => muR ≫ F.map f) he

/-- The actual unit representative is preserved by the proved lineator unitality. -/
theorem positiveRaw_id (x : Core C) (a : SInverse (Core C) (Core C)) :
    positiveRaw x (MonoidalActionCategory.RawHom.id a) =
      MonoidalActionCategory.RawHom.id (positiveObj x a) := by
  let z := positiveObj x a
  have h : ((positiveRaw x (MonoidalActionCategory.RawHom.id a)).hom :
      (𝟙_ (Core C)) ⊙ₗ z.of ⟶ z.of) = (MonoidalActionCategory.RawHom.id z).hom :=
    positiveLineator_unitality x a.of
  exact congrArg
    (fun f : (𝟙_ (Core C)) ⊙ₗ z.of ⟶ z.of =>
      (⟨𝟙_ (Core C), f⟩ : MonoidalActionCategory.RawHom z z)) h

/-- The actual later-before-earlier composition law is preserved by the proved pentagon. -/
theorem positiveRaw_comp (x : Core C) {a b c : SInverse (Core C) (Core C)}
    (r : MonoidalActionCategory.RawHom a b) (s : MonoidalActionCategory.RawHom b c) :
    positiveRaw x (r.comp s) = (positiveRaw x r).comp (positiveRaw x s) := by
  let F := positivePairFunctor x
  let A := positiveLineator x (s.stabilizer ⊗ r.stabilizer) a.of
  let R := positiveLineator x r.stabilizer a.of
  let S := positiveLineator x s.stabilizer b.of
  let U := positiveLineator x s.stabilizer (r.stabilizer ⊙ₗ a.of)
  let alpha := (αₗ s.stabilizer r.stabilizer a.of).hom
  let alphaF := (αₗ s.stabilizer r.stabilizer (F.obj a.of)).hom
  have h : ((positiveRaw x (r.comp s)).hom :
      (s.stabilizer ⊗ r.stabilizer) ⊙ₗ F.obj a.of ⟶ F.obj c.of) =
      ((positiveRaw x r).comp (positiveRaw x s)).hom := by
    change A ≫ F.map (alpha ≫ s.stabilizer ⊴ₗ r.hom ≫ s.hom) =
      alphaF ≫ s.stabilizer ⊴ₗ (R ≫ F.map r.hom) ≫ (S ≫ F.map s.hom)
    calc
      _ = (A ≫ F.map alpha) ≫ F.map (s.stabilizer ⊴ₗ r.hom ≫ s.hom) := by
        exact (congrArg (fun f => A ≫ f) (F.map_comp _ _)).trans
          (Category.assoc _ _ _).symm
      _ = (alphaF ≫ s.stabilizer ⊴ₗ R ≫ U) ≫
          F.map (s.stabilizer ⊴ₗ r.hom ≫ s.hom) :=
        congrArg (fun f => f ≫ F.map (s.stabilizer ⊴ₗ r.hom ≫ s.hom))
          (positiveLineator_associativity x s.stabilizer r.stabilizer a.of)
      _ = alphaF ≫ s.stabilizer ⊴ₗ R ≫
          (U ≫ F.map (s.stabilizer ⊴ₗ r.hom)) ≫ F.map s.hom := by
        simp only [Functor.map_comp, Category.assoc]
      _ = alphaF ≫ s.stabilizer ⊴ₗ R ≫
          (s.stabilizer ⊴ₗ F.map r.hom ≫ S) ≫ F.map s.hom := by
        rw [positiveLineator_naturality_right]
      _ = alphaF ≫ s.stabilizer ⊴ₗ (R ≫ F.map r.hom) ≫ (S ≫ F.map s.hom) := by
        simp only [MonoidalLeftAction.actionHomRight_comp, Category.assoc]
  exact congrArg
    (fun f : (s.stabilizer ⊗ r.stabilizer) ⊙ₗ F.obj a.of ⟶ F.obj c.of =>
      (⟨s.stabilizer ⊗ r.stabilizer, f⟩ :
        MonoidalActionCategory.RawHom (positiveObj x a) (positiveObj x c))) h

/-- The actual positive quotient map. -/
def positiveHomMap (x : Core C) {a b : SInverse (Core C) (Core C)} (f : a ⟶ b) :
    positiveObj x a ⟶ positiveObj x b :=
  Quotient.map (positiveRaw x) (by
    intro r s h
    exact positiveRaw_rel x h) f

/-- The actual positive right-translation functor. -/
def positiveFunctor (x : Core C) : SInverse (Core C) (Core C) ⥤ SInverse (Core C) (Core C) where
  obj := positiveObj x
  map {a b} f := positiveHomMap x f
  map_id a := by
    change MonoidalActionCategory.Hom.mk (positiveRaw x (MonoidalActionCategory.RawHom.id a)) =
      MonoidalActionCategory.Hom.mk (MonoidalActionCategory.RawHom.id (positiveObj x a))
    exact congrArg MonoidalActionCategory.Hom.mk (positiveRaw_id x a)
  map_comp {a b c} f g := by
    refine Quotient.inductionOn₂ f g ?_
    intro r s
    change MonoidalActionCategory.Hom.mk (positiveRaw x (r.comp s)) =
      MonoidalActionCategory.Hom.mk ((positiveRaw x r).comp (positiveRaw x s))
    exact congrArg MonoidalActionCategory.Hom.mk (positiveRaw_comp x r s)

/-- Coordinate swap in the ACTUAL generic localization, retaining the stabilizer. -/
def swapObj (a : SInverse (Core C) (Core C)) : SInverse (Core C) (Core C) :=
  ⟨(a.of.2, a.of.1)⟩

/-- Coordinate swap acts on the original pair of morphisms, not on a replacement model. -/
def swapRaw {a b : SInverse (Core C) (Core C)} (r : MonoidalActionCategory.RawHom a b) :
    MonoidalActionCategory.RawHom (swapObj a) (swapObj b) where
  stabilizer := r.stabilizer
  hom := (r.hom.2, r.hom.1)

/-- The same stabilizer isomorphism witnesses the swapped relation. -/
theorem swapRaw_rel {a b : SInverse (Core C) (Core C)}
    {r s : MonoidalActionCategory.RawHom a b} (h : r.Rel s) : (swapRaw r).Rel (swapRaw s) := by
  obtain ⟨e, he⟩ := h
  refine ⟨e, ?_⟩
  apply Prod.ext
  · exact congrArg (fun f : (r.stabilizer ⊙ₗ a.of) ⟶ b.of => f.2) he
  · exact congrArg (fun f : (r.stabilizer ⊙ₗ a.of) ⟶ b.of => f.1) he

/-- Swapping preserves the actual two action unitors. -/
theorem swapRaw_id (a : SInverse (Core C) (Core C)) :
    swapRaw (MonoidalActionCategory.RawHom.id a) =
      MonoidalActionCategory.RawHom.id (swapObj a) := rfl

/-- Swapping preserves the actual later-before-earlier tensor composite. -/
theorem swapRaw_comp {a b c : SInverse (Core C) (Core C)}
    (r : MonoidalActionCategory.RawHom a b) (s : MonoidalActionCategory.RawHom b c) :
    swapRaw (r.comp s) = (swapRaw r).comp (swapRaw s) := rfl

/-- The actual swapped quotient map. -/
def swapHomMap {a b : SInverse (Core C) (Core C)} (f : a ⟶ b) :
    swapObj a ⟶ swapObj b :=
  Quotient.map swapRaw (by
    intro r s h
    exact swapRaw_rel h) f

/-- The actual coordinate-swap functor. -/
def swapFunctor : SInverse (Core C) (Core C) ⥤ SInverse (Core C) (Core C) where
  obj := swapObj
  map {a b} f := swapHomMap f
  map_id a := by
    change MonoidalActionCategory.Hom.mk (swapRaw (MonoidalActionCategory.RawHom.id a)) =
      MonoidalActionCategory.Hom.mk (MonoidalActionCategory.RawHom.id (swapObj a))
    exact congrArg MonoidalActionCategory.Hom.mk (swapRaw_id a)
  map_comp {a b c} f g := by
    refine Quotient.inductionOn₂ f g ?_
    intro r s
    change MonoidalActionCategory.Hom.mk (swapRaw (r.comp s)) =
      MonoidalActionCategory.Hom.mk ((swapRaw r).comp (swapRaw s))
    exact congrArg MonoidalActionCategory.Hom.mk (swapRaw_comp r s)

/-- Negative translation appends x to the original denominator coordinate. -/
def negativeObj (x : Core C) (a : SInverse (Core C) (Core C)) :
    SInverse (Core C) (Core C) := swapObj (positiveObj x (swapObj a))

/-- The negative raw map is the positive construction on the denominator, with swaps proved. -/
def negativeRaw (x : Core C) {a b : SInverse (Core C) (Core C)}
    (r : MonoidalActionCategory.RawHom a b) :
    MonoidalActionCategory.RawHom (negativeObj x a) (negativeObj x b) :=
  swapRaw (positiveRaw x (swapRaw r))

/-- Negative translation has the literal same positive coordinate. -/
theorem negativeObj_positive (x : Core C) (a : SInverse (Core C) (Core C)) :
    (negativeObj x a).of.1 = a.of.1 := rfl

/-- Its denominator object is the original denominator tensored with x. -/
theorem negativeObj_denominator (x : Core C) (a : SInverse (Core C) (Core C)) :
    (negativeObj x a).of.2 = a.of.2 ⊗ x := rfl

/-- The actual negative denominator formula uses the same inverse associator. -/
theorem negativeRaw_denominator (x : Core C) {a b : SInverse (Core C) (Core C)}
    (r : MonoidalActionCategory.RawHom a b) :
    (negativeRaw x r).hom.2 = (α_ r.stabilizer a.of.2 x).inv ≫ r.hom.2 ▷ x := rfl

/-- Negative translation leaves the original positive morphism unchanged. -/
theorem negativeRaw_numerator (x : Core C) {a b : SInverse (Core C) (Core C)}
    (r : MonoidalActionCategory.RawHom a b) : (negativeRaw x r).hom.1 = r.hom.1 :=
  Category.id_comp r.hom.1

/-- Negative translation keeps the original stabilizer. -/
theorem negativeRaw_stabilizer (x : Core C) {a b : SInverse (Core C) (Core C)}
    (r : MonoidalActionCategory.RawHom a b) : (negativeRaw x r).stabilizer = r.stabilizer := rfl

/-- Both swapped relations and the positive relation are genuine proved laws. -/
theorem negativeRaw_rel (x : Core C) {a b : SInverse (Core C) (Core C)}
    {r s : MonoidalActionCategory.RawHom a b} (h : r.Rel s) :
    (negativeRaw x r).Rel (negativeRaw x s) :=
  swapRaw_rel (positiveRaw_rel x (swapRaw_rel h))

/-- The negative unit class follows from the explicit swapped and positive unit laws. -/
theorem negativeRaw_id (x : Core C) (a : SInverse (Core C) (Core C)) :
    negativeRaw x (MonoidalActionCategory.RawHom.id a) =
      MonoidalActionCategory.RawHom.id (negativeObj x a) := by
  exact (congrArg (fun r => swapRaw (positiveRaw x r)) (swapRaw_id a)).trans
    ((congrArg swapRaw (positiveRaw_id x (swapObj a))).trans
      (swapRaw_id (positiveObj x (swapObj a))))

/-- The negative composite follows from the actual coordinatewise swap/positive laws. -/
theorem negativeRaw_comp (x : Core C) {a b c : SInverse (Core C) (Core C)}
    (r : MonoidalActionCategory.RawHom a b) (s : MonoidalActionCategory.RawHom b c) :
    negativeRaw x (r.comp s) = (negativeRaw x r).comp (negativeRaw x s) := by
  exact (congrArg (fun r => swapRaw (positiveRaw x r)) (swapRaw_comp r s)).trans
    ((congrArg swapRaw (positiveRaw_comp x (swapRaw r) (swapRaw s))).trans
      (swapRaw_comp (positiveRaw x (swapRaw r)) (positiveRaw x (swapRaw s))))

/-- The actual negative functor is built from the proven actual coordinate swap. -/
def negativeFunctor (x : Core C) : SInverse (Core C) (Core C) ⥤ SInverse (Core C) (Core C) :=
  swapFunctor (C := C) ⋙ positiveFunctor x ⋙ swapFunctor

/-- The positive functor has the exact A-tensored-on-the-right object. -/
theorem positiveFunctor_obj (x : Core C) (a : SInverse (Core C) (Core C)) :
    ((positiveFunctor x).obj a).of = (a.of.1 ⊗ x, a.of.2) := rfl

/-- The negative functor has the exact denominator-tensored-on-the-right object. -/
theorem negativeFunctor_obj (x : Core C) (a : SInverse (Core C) (Core C)) :
    ((negativeFunctor x).obj a).of = (a.of.1, a.of.2 ⊗ x) := rfl

/-- The positive functor preserves the actual translated raw representative. -/
theorem positiveFunctor_map_mk (x : Core C) {a b : SInverse (Core C) (Core C)}
    (r : MonoidalActionCategory.RawHom a b) :
    (positiveFunctor x).map (MonoidalActionCategory.Hom.mk r) =
      MonoidalActionCategory.Hom.mk (positiveRaw x r) := rfl

/-- The negative functor preserves the actual translated raw representative. -/
theorem negativeFunctor_map_mk (x : Core C) {a b : SInverse (Core C) (Core C)}
    (r : MonoidalActionCategory.RawHom a b) :
    (negativeFunctor x).map (MonoidalActionCategory.Hom.mk r) =
      MonoidalActionCategory.Hom.mk (negativeRaw x r) := rfl

/-- The original biproduct braiding in the actual Core monoidal category. -/
def coreBraid (a b : Core C) : a ⊗ b ≅ b ⊗ a := Core.isoMk (biprod.braiding a.of b.of)

/-- The concrete same-denominator object Iso from right addition to left addition. -/
def rightToLeftComponent (x : Core C) (a : SInverse (Core C) (Core C)) :
    positiveObj x a ≅ (⟨(x ⊗ a.of.1, a.of.2)⟩ : SInverse (Core C) (Core C)) :=
  (MonoidalActionCategory.inclusion (Core C) (Core C × Core C)).mapIso
    ((coreBraid a.of.1 x).prod (Iso.refl a.of.2))

/-- This comparison is the actual biproduct braiding, with the same denominator. -/
theorem coreBraid_hom_iso_hom (a b : Core C) :
    ((coreBraid a b).hom).iso.hom = (biprod.braiding a.of b.of).hom := rfl

end CategoryTheory.GenericCoreResidualTranslation

end

/-! ## The actual same-denominator braiding comparison -/

noncomputable section

set_option autoImplicit false

open CategoryTheory Limits ZeroObject
open CategoryTheory.MonoidalCategory
open CategoryTheory.CoreLocalizationComparison
open CategoryTheory.GenericCoreResidualTranslation
open scoped CategoryTheory.Limits.CoreBiprodMonoidal MonoidalCategory
open scoped CategoryTheory.MonoidalCategory.MonoidalLeftAction

namespace CategoryTheory.GenericCoreBraidingComparison

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C]

attribute [local instance] MonoidalActionCategory.diagonalAction

/-- The actual legacy first-coordinate functor transported through the given model maps. -/
def legacyPositiveFunctor (x : Core C) :
    SInverse (Core C) (Core C) ⥤ SInverse (Core C) (Core C) :=
  toPairFunctor ⋙ SInverseS.translateFirstFunctor x.of ⋙ fromPairFunctor

/-- Its object retains the original denominator and adds x on the left. -/
def legacyPositiveObj (x : Core C) (a : SInverse (Core C) (Core C)) :
    SInverse (Core C) (Core C) := (legacyPositiveFunctor x).obj a

/-- Its raw map is the actual legacy raw map, wrapped by the proved model comparison. -/
def legacyPositiveRaw (x : Core C) {a b : SInverse (Core C) (Core C)}
    (r : MonoidalActionCategory.RawHom a b) :
    MonoidalActionCategory.RawHom (legacyPositiveObj x a) (legacyPositiveObj x b) :=
  fromPairRaw ((toPairRaw r).translateFirst x.of)

/-- The positive coordinate is literally the legacy left addition. -/
theorem legacyPositiveObj_positive (x : Core C) (a : SInverse (Core C) (Core C)) :
    (legacyPositiveObj x a).of.1 = x ⊗ a.of.1 := rfl

/-- The same original denominator object is retained. -/
theorem legacyPositiveObj_denominator (x : Core C) (a : SInverse (Core C) (Core C)) :
    (legacyPositiveObj x a).of.2 = a.of.2 := rfl

/-- The transported legacy raw stabilizer is the original stabilizer. -/
theorem legacyPositiveRaw_stabilizer (x : Core C) {a b : SInverse (Core C) (Core C)}
    (r : MonoidalActionCategory.RawHom a b) :
    (legacyPositiveRaw x r).stabilizer = r.stabilizer := rfl

/-- The numerator uses the actual published stabilizer-swap isomorphism. -/
theorem legacyPositiveRaw_numerator (x : Core C) {a b : SInverse (Core C) (Core C)}
    (r : MonoidalActionCategory.RawHom a b) :
    (legacyPositiveRaw x r).hom.1.iso =
      SInverseS.swapStabilizerIso x.of r.stabilizer.of a.of.1.of ≪≫
        biprod.mapIso (Iso.refl x.of) r.hom.1.iso := rfl

/-- The original denominator morphism is retained, rather than replaced by a unit. -/
theorem legacyPositiveRaw_denominator (x : Core C) {a b : SInverse (Core C) (Core C)}
    (r : MonoidalActionCategory.RawHom a b) :
    (legacyPositiveRaw x r).hom.2 = r.hom.2 := rfl

/-- The composed functor has this actual raw representative. -/
theorem legacyPositiveFunctor_map_mk (x : Core C) {a b : SInverse (Core C) (Core C)}
    (r : MonoidalActionCategory.RawHom a b) :
    (legacyPositiveFunctor x).map (MonoidalActionCategory.Hom.mk r) =
      MonoidalActionCategory.Hom.mk (legacyPositiveRaw x r) := rfl

/-- The pair isomorphism is braiding in the positive coordinate and identity in the denominator. -/
def braidingPairIso (x : Core C) (a : SInverse (Core C) (Core C)) :
    (positiveObj x a).of ≅ (legacyPositiveObj x a).of :=
  (coreBraid a.of.1 x).prod (Iso.refl a.of.2)

/-- The forward pair map uses the actual biproduct braiding. -/
theorem braidingPairIso_hom (x : Core C) (a : SInverse (Core C) (Core C)) :
    (braidingPairIso x a).hom = ((coreBraid a.of.1 x).hom, 𝟙 a.of.2) := rfl

/-- The inverse pair map retains the same denominator and reverses the actual braiding. -/
theorem braidingPairIso_inv (x : Core C) (a : SInverse (Core C) (Core C)) :
    (braidingPairIso x a).inv = ((coreBraid a.of.1 x).inv, 𝟙 a.of.2) := rfl

omit [HasZeroObject C] in
/-- The three original summands have the same permutation on both sides. -/
theorem braid_associator_permutation (T A X : C) :
    (biprod.associator T A X).inv ≫ (biprod.braiding (T ⊞ A) X).hom =
      biprod.map (𝟙 T) (biprod.braiding A X).hom ≫
        (SInverseS.swapStabilizerIso X T A).hom := by
  apply biprod.hom_ext'
  · apply biprod.hom_ext
    · simp [biprod.associator, biprod.braiding,
        SInverseS.swapStabilizerIso, Category.assoc]
    · apply biprod.hom_ext <;>
        simp [biprod.associator, biprod.braiding,
          SInverseS.swapStabilizerIso, Category.assoc]
  · apply biprod.hom_ext'
    · apply biprod.hom_ext
      · simp [biprod.associator, biprod.braiding,
          SInverseS.swapStabilizerIso, Category.assoc]
      · apply biprod.hom_ext <;>
          simp [biprod.associator, biprod.braiding,
            SInverseS.swapStabilizerIso, Category.assoc]
    · apply biprod.hom_ext
      · simp [biprod.associator, biprod.braiding,
          SInverseS.swapStabilizerIso, Category.assoc]
      · apply biprod.hom_ext <;>
          simp [biprod.associator, biprod.braiding,
            SInverseS.swapStabilizerIso, Category.assoc]

omit [HasZeroObject C] in
private theorem numerator_braiding (T A X B : C) (f : T ⊞ A ⟶ B) :
    (biprod.associator T A X).inv ≫ biprod.map f (𝟙 X) ≫
        (biprod.braiding B X).hom =
      biprod.map (𝟙 T) (biprod.braiding A X).hom ≫
        (SInverseS.swapStabilizerIso X T A).hom ≫ biprod.map (𝟙 X) f := by
  let alpha : T ⊞ (A ⊞ X) ⟶ (T ⊞ A) ⊞ X := (biprod.associator T A X).inv
  let braid : (T ⊞ A) ⊞ X ⟶ X ⊞ (T ⊞ A) := (biprod.braiding (T ⊞ A) X).hom
  let m : X ⊞ (T ⊞ A) ⟶ X ⊞ B := biprod.map (𝟙 X) f
  have hn : biprod.map f (𝟙 X) ≫ (biprod.braiding B X).hom = braid ≫ m :=
    biprod.braid_natural f (𝟙 X)
  have hp : alpha ≫ braid = biprod.map (𝟙 T) (biprod.braiding A X).hom ≫
      (SInverseS.swapStabilizerIso X T A).hom := braid_associator_permutation T A X
  exact (congrArg (fun k => alpha ≫ k) hn).trans
    (((Category.assoc alpha braid m).symm).trans
      ((congrArg (fun k => k ≫ m) hp).trans (Category.assoc _ _ _)))

private theorem core_right_whisker_hom {T U : Core C} (f : T ⟶ U) (A : Core C) :
    (f ▷ A).iso.hom = biprod.map f.iso.hom (𝟙 A.of) := by
  rewrite [← tensorHom_id, coreBiprodTensorHom_iso_hom]
  rfl

private theorem core_left_whisker_hom (T : Core C) {A B : Core C} (f : A ⟶ B) :
    (T ◁ f).iso.hom = biprod.map (𝟙 T.of) f.iso.hom :=
  (coreBiprodTensorLeft_map_iso_hom T f).trans
    (coreLeftBiprodFunctor_map_iso_hom T.of f)

/-- Naturality before the quotient uses the same stabilizer and original denominator map. -/
theorem stabilized_braiding_naturality (x : Core C) {a b : SInverse (Core C) (Core C)}
    (r : MonoidalActionCategory.RawHom a b) :
    (positiveRaw x r).hom ≫ (braidingPairIso x b).hom =
      r.stabilizer ⊴ₗ (braidingPairIso x a).hom ≫ (legacyPositiveRaw x r).hom := by
  apply Prod.ext
  · let T : Core C := r.stabilizer
    let A : Core C := a.of.1
    let B : Core C := b.of.1
    let f : T ⊗ A ⟶ B := r.hom.1
    let lp : T ⊗ (x ⊗ A) ⟶ x ⊗ B := (legacyPositiveRaw x r).hom.1
    have hbFirst : (braidingPairIso x b).hom.1 = (coreBraid B x).hom := rfl
    have hLeftProjection : ((positiveRaw x r).hom ≫ (braidingPairIso x b).hom).1 =
        (positiveRaw x r).hom.1 ≫ (braidingPairIso x b).hom.1 := rfl
    have hLeft : ((positiveRaw x r).hom ≫ (braidingPairIso x b).hom).1 =
        ((α_ T A x).inv ≫ f ▷ x) ≫ (coreBraid B x).hom :=
      hLeftProjection.trans
        (congrArg₂
          (fun (p : T ⊗ (A ⊗ x) ⟶ B ⊗ x) (q : B ⊗ x ⟶ x ⊗ B) => p ≫ q)
          (positiveRaw_numerator x r) hbFirst)
    have hActionFirst : (T ⊴ₗ (braidingPairIso x a).hom).1 =
        T ◁ (coreBraid A x).hom := rfl
    have hRightProjection :
        (T ⊴ₗ (braidingPairIso x a).hom ≫ (legacyPositiveRaw x r).hom).1 =
          (T ⊴ₗ (braidingPairIso x a).hom).1 ≫ lp := rfl
    have hRight :
        (T ⊴ₗ (braidingPairIso x a).hom ≫ (legacyPositiveRaw x r).hom).1 =
          (T ◁ (coreBraid A x).hom) ≫ lp :=
      hRightProjection.trans
        (congrArg (fun p : T ⊗ (A ⊗ x) ⟶ T ⊗ (x ⊗ A) => p ≫ lp) hActionFirst)
    have hCore : ((α_ T A x).inv ≫ f ▷ x) ≫ (coreBraid B x).hom =
        (T ◁ (coreBraid A x).hom) ≫ lp := by
      apply Core.hom_ext
      simp only [coreCategory_comp_iso, Iso.trans_hom]
      have ha : ((α_ T A x).inv).iso.hom =
          (biprod.associator T.of A.of x.of).inv := by
        rfl
      have hr : (f ▷ x).iso.hom = biprod.map f.iso.hom (𝟙 x.of) :=
        core_right_whisker_hom f x
      have hb : (coreBraid B x).hom.iso.hom = (biprod.braiding B.of x.of).hom :=
        coreBraid_hom_iso_hom B x
      have hl : (T ◁ (coreBraid A x).hom).iso.hom =
          biprod.map (𝟙 T.of) (biprod.braiding A.of x.of).hom :=
        (core_left_whisker_hom T (coreBraid A x).hom).trans
          (congrArg (fun q : A.of ⊞ x.of ⟶ x.of ⊞ A.of => biprod.map (𝟙 T.of) q)
            (coreBraid_hom_iso_hom A x))
      have hLegacy : lp.iso.hom =
          (SInverseS.swapStabilizerIso x.of T.of A.of).hom ≫
            biprod.map (𝟙 x.of) f.iso.hom := by
        have hIso := congrArg Iso.hom (legacyPositiveRaw_numerator x r)
        exact hIso.trans (by rfl)
      rewrite [ha, hr, hb, hl, hLegacy]
      have hNum :=
        numerator_braiding.{u, v} (C := C) T.of A.of x.of B.of f.iso.hom
      simpa only [coreBiprodTensorObj_of, Category.assoc] using hNum
    exact hLeft.trans (hCore.trans hRight.symm)
  · change (𝟙 _ ≫ r.hom.2) ≫ 𝟙 _ = (r.stabilizer ◁ 𝟙 a.of.2) ≫ r.hom.2
    simp only [whiskerLeft_id, Category.id_comp, Category.comp_id]

private theorem raw_comp_pairMap_rel {a b c : SInverse (Core C) (Core C)}
    (r : MonoidalActionCategory.RawHom a b) (f : b.of ⟶ c.of) :
    (r.comp (MonoidalActionCategory.RawHom.ofMap (S := Core C) f)).Rel
      (⟨r.stabilizer, r.hom ≫ f⟩ : MonoidalActionCategory.RawHom a c) := by
  refine ⟨λ_ r.stabilizer, ?_⟩
  dsimp only [MonoidalActionCategory.RawHom.comp, MonoidalActionCategory.RawHom.ofMap]
  rw [MonoidalLeftAction.leftUnitor_actionHom]
  simp only [Category.assoc]
  rw [MonoidalLeftAction.actionUnitIso_hom_naturality_assoc]

private theorem raw_pairMap_comp_rel {a b c : SInverse (Core C) (Core C)}
    (f : a.of ⟶ b.of) (r : MonoidalActionCategory.RawHom b c) :
    ((MonoidalActionCategory.RawHom.ofMap (S := Core C) f).comp r).Rel
      (⟨r.stabilizer, r.stabilizer ⊴ₗ f ≫ r.hom⟩ :
        MonoidalActionCategory.RawHom a c) := by
  refine ⟨ρ_ r.stabilizer, ?_⟩
  dsimp only [MonoidalActionCategory.RawHom.comp, MonoidalActionCategory.RawHom.ofMap]
  rw [MonoidalLeftAction.rightUnitor_actionHom]
  simp only [MonoidalLeftAction.actionHomRight_comp, Category.assoc]

/-- The same-denominator braiding is natural for every actual localized morphism. -/
theorem rightToLeftComponent_naturality (x : Core C)
    {a b : SInverse (Core C) (Core C)} (f : a ⟶ b) :
    (positiveFunctor x).map f ≫ (rightToLeftComponent x b).hom =
      (rightToLeftComponent x a).hom ≫ (legacyPositiveFunctor x).map f := by
  obtain ⟨r, rfl⟩ := MonoidalActionCategory.Hom.exists_rep f
  let p := positiveObj x a
  let q := legacyPositiveObj x b
  let rr : MonoidalActionCategory.RawHom p (positiveObj x b) := positiveRaw x r
  let ll : MonoidalActionCategory.RawHom (legacyPositiveObj x a) q := legacyPositiveRaw x r
  let ba : p.of ⟶ (legacyPositiveObj x a).of := (braidingPairIso x a).hom
  let bb : (positiveObj x b).of ⟶ q.of := (braidingPairIso x b).hom
  let rn : MonoidalActionCategory.RawHom p q := ⟨r.stabilizer, rr.hom ≫ bb⟩
  let ln : MonoidalActionCategory.RawHom p q := ⟨r.stabilizer, r.stabilizer ⊴ₗ ba ≫ ll.hom⟩
  have hn : rn = ln := congrArg
    (fun k : r.stabilizer ⊙ₗ p.of ⟶ q.of =>
      (⟨r.stabilizer, k⟩ : MonoidalActionCategory.RawHom p q))
    (stabilized_braiding_naturality x r)
  change MonoidalActionCategory.Hom.mk
      (rr.comp (MonoidalActionCategory.RawHom.ofMap (S := Core C) bb)) =
    MonoidalActionCategory.Hom.mk
      ((MonoidalActionCategory.RawHom.ofMap (S := Core C) ba).comp ll)
  exact (_root_.Quotient.sound (raw_comp_pairMap_rel
    (a := p) (b := positiveObj x b) (c := q) rr bb)).trans
    ((congrArg MonoidalActionCategory.Hom.mk hn).trans
      (_root_.Quotient.sound (raw_pairMap_comp_rel
        (a := p) (b := legacyPositiveObj x a) (c := q) ba ll)).symm)

/-- The constructed comparison to the actual legacy first-coordinate translation. -/
def rightToLegacyPositiveIso (x : Core C) :
    positiveFunctor x ≅ legacyPositiveFunctor x :=
  NatIso.ofComponents (fun a => rightToLeftComponent x a) (by
    intro a b f
    exact rightToLeftComponent_naturality x f)

/-- The forward component is the actual ordinary pair-inclusion braiding. -/
theorem rightToLegacyPositiveIso_hom_app (x : Core C) (a : SInverse (Core C) (Core C)) :
    (rightToLegacyPositiveIso x).hom.app a =
      (MonoidalActionCategory.inclusion (Core C) (Core C × Core C)).map
        (X := (positiveObj x a).of) (Y := (legacyPositiveObj x a).of)
        (braidingPairIso x a).hom := rfl

/-- The inverse component uses the reverse braiding at the identical denominator. -/
theorem rightToLegacyPositiveIso_inv_app (x : Core C) (a : SInverse (Core C) (Core C)) :
    (rightToLegacyPositiveIso x).inv.app a =
      (MonoidalActionCategory.inclusion (Core C) (Core C × Core C)).map
        (X := (legacyPositiveObj x a).of) (Y := (positiveObj x a).of)
        (braidingPairIso x a).inv := rfl

/-- The actual forward and inverse components compose to the original right-positive identity. -/
theorem rightToLegacyPositiveIso_hom_inv (x : Core C) (a : SInverse (Core C) (Core C)) :
    (rightToLegacyPositiveIso x).hom.app a ≫ (rightToLegacyPositiveIso x).inv.app a =
      𝟙 ((positiveFunctor x).obj a) := (rightToLegacyPositiveIso x).hom_inv_id_app a

/-- The reverse composite is the original left-positive identity. -/
theorem rightToLegacyPositiveIso_inv_hom (x : Core C) (a : SInverse (Core C) (Core C)) :
    (rightToLegacyPositiveIso x).inv.app a ≫ (rightToLegacyPositiveIso x).hom.app a =
      𝟙 ((legacyPositiveFunctor x).obj a) := (rightToLegacyPositiveIso x).inv_hom_id_app a

/-- Naturality of the actual inverse comparison is retained in the original localized category. -/
theorem rightToLegacyPositiveIso_inv_naturality (x : Core C)
    {a b : SInverse (Core C) (Core C)} (f : a ⟶ b) :
    (legacyPositiveFunctor x).map f ≫ (rightToLegacyPositiveIso x).inv.app b =
      (rightToLegacyPositiveIso x).inv.app a ≫ (positiveFunctor x).map f :=
  (rightToLegacyPositiveIso x).inv.naturality f

private theorem toPair_legacy_map (x : Core C) {a b : SInverse (Core C) (Core C)}
    (f : a ⟶ b) :
    (toPairFunctor (C := C)).map ((legacyPositiveFunctor x).map f) =
      (SInverseS.translateFirstFunctor x.of).map ((toPairFunctor (C := C)).map f) :=
  to_from_map ((SInverseS.translateFirstFunctor x.of).map ((toPairFunctor (C := C)).map f))

/-- The actual model bridge intertwines right addition with legacy first addition by braiding. -/
def rightPositiveToLegacyPairIso (x : Core C) :
    positiveFunctor x ⋙ toPairFunctor ≅
      toPairFunctor (C := C) ⋙ SInverseS.translateFirstFunctor x.of :=
  NatIso.ofComponents
    (fun a => (toPairFunctor (C := C)).mapIso (rightToLeftComponent x a)) (by
      intro a b f
      let F := toPairFunctor (C := C)
      let ra := (rightToLeftComponent x a).hom
      let rb := (rightToLeftComponent x b).hom
      let pf := (positiveFunctor x).map f
      let lf := (legacyPositiveFunctor x).map f
      change F.map pf ≫ F.map rb =
        F.map ra ≫ (SInverseS.translateFirstFunctor x.of).map (F.map f)
      exact (F.map_comp pf rb).symm.trans
        ((congrArg F.map (rightToLeftComponent_naturality x f)).trans
          ((F.map_comp ra lf).trans
            (congrArg (fun k => F.map ra ≫ k) (toPair_legacy_map x f)))))

/-- The Pair-valued forward component is the bridge image of the same-denominator braiding. -/
theorem rightPositiveToLegacyPairIso_hom_app (x : Core C)
    (a : SInverse (Core C) (Core C)) :
    (rightPositiveToLegacyPairIso x).hom.app a =
      (toPairFunctor (C := C)).map ((rightToLeftComponent x a).hom) := rfl

/-- The Pair-valued inverse is the bridge image of the original inverse component. -/
theorem rightPositiveToLegacyPairIso_inv_app (x : Core C)
    (a : SInverse (Core C) (Core C)) :
    (rightPositiveToLegacyPairIso x).inv.app a =
      (toPairFunctor (C := C)).map ((rightToLeftComponent x a).inv) := rfl

end CategoryTheory.GenericCoreBraidingComparison

end

/-! ## The exact generic P/N maps and their realized unbased homotopy equivalence -/

noncomputable section

set_option autoImplicit false

open CategoryTheory Limits ZeroObject
open CategoryTheory.MonoidalCategory
open CategoryTheory.CoreLocalizationComparison
open CategoryTheory.GenericCoreResidualTranslation
open CategoryTheory.GenericCoreBraidingComparison
open scoped CategoryTheory.Limits.CoreBiprodMonoidal MonoidalCategory
open scoped CategoryTheory.MonoidalCategory.MonoidalLeftAction

namespace CategoryTheory.GenericCoreTranslation

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C]

attribute [local instance] MonoidalActionCategory.diagonalAction

/-- Transport an actual Pair functor through the constructed model maps. -/
def transportedFunctor (H : SInverseS.Pair C ⥤ SInverseS.Pair C) :
    SInverse (Core C) (Core C) ⥤ SInverse (Core C) (Core C) :=
  toPairFunctor ⋙ H ⋙ fromPairFunctor

/-- The actual legacy negative translation transported to the original generic model. -/
def legacyNegativeFunctor (x : Core C) :
    SInverse (Core C) (Core C) ⥤ SInverse (Core C) (Core C) :=
  transportedFunctor (SInverseS.translateSecondFunctor x.of)

/-- The negative target preserves its positive object and prepends x to the denominator. -/
def legacyNegativeObj (x : Core C) (a : SInverse (Core C) (Core C)) :
    SInverse (Core C) (Core C) := (legacyNegativeFunctor x).obj a

/-- The negative raw map is the published legacy second-coordinate raw translation. -/
def legacyNegativeRaw (x : Core C) {a b : SInverse (Core C) (Core C)}
    (r : MonoidalActionCategory.RawHom a b) :
    MonoidalActionCategory.RawHom (legacyNegativeObj x a) (legacyNegativeObj x b) :=
  fromPairRaw ((toPairRaw r).translateSecond x.of)

/-- The transported negative functor has this exact original raw representative. -/
theorem legacyNegativeFunctor_map_mk (x : Core C) {a b : SInverse (Core C) (Core C)}
    (r : MonoidalActionCategory.RawHom a b) :
    (legacyNegativeFunctor x).map (MonoidalActionCategory.Hom.mk r) =
      MonoidalActionCategory.Hom.mk (legacyNegativeRaw x r) := rfl

/-- The negative comparison keeps the positive coordinate and braids the denominator. -/
def negativePairIso (x : Core C) (a : SInverse (Core C) (Core C)) :
    (negativeObj x a).of ≅ (legacyNegativeObj x a).of :=
  (Iso.refl a.of.1).prod (coreBraid a.of.2 x)

/-- Ordinary pair inclusion supplies the component at the original denominator. -/
def negativeComponent (x : Core C) (a : SInverse (Core C) (Core C)) :
    negativeObj x a ≅ legacyNegativeObj x a :=
  (MonoidalActionCategory.inclusion (Core C) (Core C × Core C)).mapIso
    (negativePairIso x a)

/-- Swapping the proved positive square gives the exact negative square with the same stabilizer. -/
theorem negativeStabilizedNaturality (x : Core C) {a b : SInverse (Core C) (Core C)}
    (r : MonoidalActionCategory.RawHom a b) :
    (negativeRaw x r).hom ≫ (negativePairIso x b).hom =
      r.stabilizer ⊴ₗ (negativePairIso x a).hom ≫ (legacyNegativeRaw x r).hom := by
  have h := stabilized_braiding_naturality x (swapRaw r)
  exact congrArg
    (fun k : r.stabilizer ⊙ₗ (positiveObj x (swapObj a)).of ⟶
        (legacyPositiveObj x (swapObj b)).of => (k.2, k.1)) h

/-- The actual negative component is natural for every original quotient arrow. -/
theorem negativeComponentNaturality (x : Core C)
    {a b : SInverse (Core C) (Core C)} (f : a ⟶ b) :
    (negativeFunctor x).map f ≫ (negativeComponent x b).hom =
      (negativeComponent x a).hom ≫ (legacyNegativeFunctor x).map f := by
  obtain ⟨r, rfl⟩ := MonoidalActionCategory.Hom.exists_rep f
  let p := negativeObj x a
  let q := legacyNegativeObj x b
  let rr : MonoidalActionCategory.RawHom p (negativeObj x b) := negativeRaw x r
  let ll : MonoidalActionCategory.RawHom (legacyNegativeObj x a) q := legacyNegativeRaw x r
  let ba : p.of ⟶ (legacyNegativeObj x a).of := (negativePairIso x a).hom
  let bb : (negativeObj x b).of ⟶ q.of := (negativePairIso x b).hom
  let rn : MonoidalActionCategory.RawHom p q := ⟨r.stabilizer, rr.hom ≫ bb⟩
  let ln : MonoidalActionCategory.RawHom p q := ⟨r.stabilizer, r.stabilizer ⊴ₗ ba ≫ ll.hom⟩
  have hn : rn = ln := congrArg
    (fun k : r.stabilizer ⊙ₗ p.of ⟶ q.of =>
      (⟨r.stabilizer, k⟩ : MonoidalActionCategory.RawHom p q))
    (negativeStabilizedNaturality x r)
  change MonoidalActionCategory.Hom.mk
      (rr.comp (MonoidalActionCategory.RawHom.ofMap (S := Core C) bb)) =
    MonoidalActionCategory.Hom.mk
      ((MonoidalActionCategory.RawHom.ofMap (S := Core C) ba).comp ll)
  exact (_root_.Quotient.sound (GenericCoreBraidingComparison.raw_comp_pairMap_rel
    (a := p) (b := negativeObj x b) (c := q) rr bb)).trans
    ((congrArg MonoidalActionCategory.Hom.mk hn).trans
      (_root_.Quotient.sound (GenericCoreBraidingComparison.raw_pairMap_comp_rel
        (a := p) (b := legacyNegativeObj x a) (c := q) ba ll)).symm)

/-- The constructed negative comparison uses the actual original denominator braiding. -/
def rightToLegacyNegativeIso (x : Core C) :
    negativeFunctor x ≅ legacyNegativeFunctor x :=
  NatIso.ofComponents (fun a => negativeComponent x a) (by
    intro a b f
    exact negativeComponentNaturality x f)

/-- Its forward component is the original pair-inclusion denominator braiding. -/
theorem rightToLegacyNegativeIso_hom_app (x : Core C) (a : SInverse (Core C) (Core C)) :
    (rightToLegacyNegativeIso x).hom.app a =
      (MonoidalActionCategory.inclusion (Core C) (Core C × Core C)).map
        (X := (negativeObj x a).of) (Y := (legacyNegativeObj x a).of)
        (negativePairIso x a).hom := rfl

/-- Its inverse retains the same positive object and reverses that actual denominator braiding. -/
theorem rightToLegacyNegativeIso_inv_app (x : Core C) (a : SInverse (Core C) (Core C)) :
    (rightToLegacyNegativeIso x).inv.app a =
      (MonoidalActionCategory.inclusion (Core C) (Core C × Core C)).map
        (X := (legacyNegativeObj x a).of) (Y := (negativeObj x a).of)
        (negativePairIso x a).inv := rfl

/-- The actual model counit compares the two transported compositions. -/
def transportCompositeIso (L R : SInverseS.Pair C ⥤ SInverseS.Pair C) :
    transportedFunctor L ⋙ transportedFunctor R ≅ transportedFunctor (L ⋙ R) :=
  NatIso.ofComponents (fun a => Iso.refl ((transportedFunctor (L ⋙ R)).obj a)) (by
    intro a b f
    let F := toPairFunctor (C := C)
    let G := fromPairFunctor (C := C)
    let q := L.map (F.map f)
    have hq : F.map (G.map q) = q := to_from_map q
    have hm : (transportedFunctor L ⋙ transportedFunctor R).map f =
        (transportedFunctor (L ⋙ R)).map f :=
      congrArg (fun k : L.obj (F.obj a) ⟶ L.obj (F.obj b) => G.map (R.map k)) hq
    let d := (transportedFunctor (L ⋙ R)).obj b
    let u := (transportedFunctor (L ⋙ R)).map f
    change (transportedFunctor L ⋙ transportedFunctor R).map f ≫ 𝟙 d =
      𝟙 ((transportedFunctor (L ⋙ R)).obj a) ≫ u
    exact (congrArg (fun k => k ≫ 𝟙 d) hm).trans
      ((Category.comp_id u).trans (Category.id_comp u).symm))

private theorem transported_delta_naturality
    {H : SInverseS.Pair C ⥤ SInverseS.Pair C} (delta : 𝟭 (SInverseS.Pair C) ⟶ H)
    {a b : SInverse (Core C) (Core C)} (f : a ⟶ b) :
    f ≫ (fromPairFunctor (C := C)).map (delta.app ((toPairFunctor (C := C)).obj b)) =
      (fromPairFunctor (C := C)).map (delta.app ((toPairFunctor (C := C)).obj a)) ≫
        (transportedFunctor H).map f := by
  let F := toPairFunctor (C := C)
  let G := fromPairFunctor (C := C)
  let q := F.map f
  let da := delta.app (F.obj a)
  let db := delta.app (F.obj b)
  have hq : G.map q = f := from_to_map f
  have hd : q ≫ db = da ≫ H.map q := delta.naturality q
  change f ≫ G.map db = G.map da ≫ G.map (H.map q)
  exact (congrArg (fun k : a ⟶ b => k ≫ G.map db) hq.symm).trans
    ((G.map_comp q db).symm.trans ((congrArg G.map hd).trans (G.map_comp da (H.map q))))

/-- Transport the published first-then-second diagonal transformation through the actual model. -/
def transportedDiagonalPN (x : Core C) :
    𝟭 (SInverse (Core C) (Core C)) ⟶ transportedFunctor
      (SInverseS.translateFirstFunctor x.of ⋙ SInverseS.translateSecondFunctor x.of) where
  app a := (fromPairFunctor (C := C)).map
    ((SInverseS.diagonalAddFirstSecondNatTrans x.of).app ((toPairFunctor (C := C)).obj a))
  naturality {a b} f := by
    exact transported_delta_naturality (SInverseS.diagonalAddFirstSecondNatTrans x.of) f

/-- Transport the published second-then-first transformation with its original diagonal arrow. -/
def transportedDiagonalNP (x : Core C) :
    𝟭 (SInverse (Core C) (Core C)) ⟶ transportedFunctor
      (SInverseS.translateSecondFunctor x.of ⋙ SInverseS.translateFirstFunctor x.of) where
  app a := (fromPairFunctor (C := C)).map
    ((SInverseS.diagonalAddSecondFirstNatTrans x.of).app ((toPairFunctor (C := C)).obj a))
  naturality {a b} f := by
    exact transported_delta_naturality (SInverseS.diagonalAddSecondFirstNatTrans x.of) f

/-- Both actual generic functors are compared before removing the intervening model roundtrip. -/
def positiveNegativeComparison (x : Core C) :
    positiveFunctor x ⋙ negativeFunctor x ≅ transportedFunctor
      (SInverseS.translateFirstFunctor x.of ⋙ SInverseS.translateSecondFunctor x.of) :=
  CategoryTheory.Functor.isoWhiskerRight (rightToLegacyPositiveIso x) (negativeFunctor x) ≪≫
    CategoryTheory.Functor.isoWhiskerLeft (legacyPositiveFunctor x) (rightToLegacyNegativeIso x) ≪≫
      transportCompositeIso (SInverseS.translateFirstFunctor x.of)
        (SInverseS.translateSecondFunctor x.of)

/-- The opposite-order comparison retains the same actual two translations. -/
def negativePositiveComparison (x : Core C) :
    negativeFunctor x ⋙ positiveFunctor x ≅ transportedFunctor
      (SInverseS.translateSecondFunctor x.of ⋙ SInverseS.translateFirstFunctor x.of) :=
  CategoryTheory.Functor.isoWhiskerRight (rightToLegacyNegativeIso x) (positiveFunctor x) ≪≫
    CategoryTheory.Functor.isoWhiskerLeft (legacyNegativeFunctor x) (rightToLegacyPositiveIso x) ≪≫
      transportCompositeIso (SInverseS.translateSecondFunctor x.of)
        (SInverseS.translateFirstFunctor x.of)

/-- The actual diagonal arrow supplies Id to P followed by N; no generic homotopy is assumed. -/
def positiveNegativeUnit (x : Core C) :
    𝟭 (SInverse (Core C) (Core C)) ⟶ positiveFunctor x ⋙ negativeFunctor x :=
  transportedDiagonalPN x ≫ (positiveNegativeComparison x).inv

/-- The actual diagonal arrow also supplies Id to N followed by P. -/
def negativePositiveUnit (x : Core C) :
    𝟭 (SInverse (Core C) (Core C)) ⟶ negativeFunctor x ⋙ positiveFunctor x :=
  transportedDiagonalNP x ≫ (negativePositiveComparison x).inv

/-- The original generic nerve in the common max(u,v) universe. -/
def genericNerve : SSet.{max u v} := nerve (SInverse (Core C) (Core C))

/-- The direct nerve map of the actual right-positive functor. -/
def positiveNerveMap (x : Core C) : genericNerve (C := C) ⟶ genericNerve (C := C) :=
  CategoryTheory.nerveMap (positiveFunctor x)

/-- The direct nerve map of the actual right-negative functor, in the identical universe. -/
def negativeNerveMap (x : Core C) : genericNerve (C := C) ⟶ genericNerve (C := C) :=
  CategoryTheory.nerveMap (negativeFunctor x)

/-- The positive map is the ordinary nerve map of the exact same functor. -/
theorem positiveNerveMap_ordinary (x : Core C) :
    positiveNerveMap x = nerveMap (positiveFunctor x) := rfl

/-- The negative map likewise is the ordinary map of the exact same functor. -/
theorem negativeNerveMap_ordinary (x : Core C) :
    negativeNerveMap x = nerveMap (negativeFunctor x) := rfl

/-- The actual positive-then-negative diagonal transformation yields a directed nerve homotopy. -/
def positiveNegativeNerveHomotopy (x : Core C) :
    SSet.Homotopy (𝟙 (genericNerve (C := C))) (positiveNerveMap x ≫ negativeNerveMap x) := by
  have hc : positiveNerveMap x ≫ negativeNerveMap x =
      CategoryTheory.nerveMap (positiveFunctor x ⋙ negativeFunctor x) :=
    CategoryTheory.nerveMap_comp (positiveFunctor x) (negativeFunctor x)
  have hi : CategoryTheory.nerveMap (𝟭 (SInverse (Core C) (Core C))) =
      𝟙 (genericNerve (C := C)) := CategoryTheory.nerveMap_id
  rw [hc, ← hi]
  exact CategoryTheory.NatTrans.nerveHomotopy (positiveNegativeUnit x)

/-- The opposite actual composite has its own directed nerve homotopy. -/
def negativePositiveNerveHomotopy (x : Core C) :
    SSet.Homotopy (𝟙 (genericNerve (C := C))) (negativeNerveMap x ≫ positiveNerveMap x) := by
  have hc : negativeNerveMap x ≫ positiveNerveMap x =
      CategoryTheory.nerveMap (negativeFunctor x ⋙ positiveFunctor x) :=
    CategoryTheory.nerveMap_comp (negativeFunctor x) (positiveFunctor x)
  have hi : CategoryTheory.nerveMap (𝟭 (SInverse (Core C) (Core C))) =
      𝟙 (genericNerve (C := C)) := CategoryTheory.nerveMap_id
  rw [hc, ← hi]
  exact CategoryTheory.NatTrans.nerveHomotopy (negativePositiveUnit x)

/-- The realization is the original generic nerve's native TopCat realization. -/
def genericSpace : TopCat.{max u v} := SSet.toTop.obj (genericNerve (C := C))

/-- The forward map is realization of the exact generic P. -/
def positiveRealizedMap (x : Core C) :
    ContinuousMap (genericSpace (C := C)) (genericSpace (C := C)) :=
  (SSet.toTop.map (positiveNerveMap x)).hom

/-- The backward map is realization of the exact generic N. -/
def negativeRealizedMap (x : Core C) :
    ContinuousMap (genericSpace (C := C)) (genericSpace (C := C)) :=
  (SSet.toTop.map (negativeNerveMap x)).hom

/-- Realization makes the actual Id-to-PN homotopy reversible without a Kan or CW assumption. -/
def positiveNegativeHomotopy (x : Core C) :
    ContinuousMap.Homotopy (ContinuousMap.id (genericSpace (C := C)))
      ((negativeRealizedMap x).comp (positiveRealizedMap x)) := by
  let N : SSet.{max u v} := genericNerve (C := C)
  let f : N ⟶ N := positiveNerveMap x
  let g : N ⟶ N := negativeNerveMap x
  let ht := SSet.realizeHomotopy N N (𝟙 N) (f ≫ g) (positiveNegativeNerveHomotopy x)
  have hId : (SSet.toTop.map (𝟙 N)).hom = ContinuousMap.id (genericSpace (C := C)) := by
    rewrite [SSet.toTop.map_id]
    rfl
  have hComp : (SSet.toTop.map (f ≫ g)).hom =
      (negativeRealizedMap x).comp (positiveRealizedMap x) := by
    rewrite [SSet.toTop.map_comp]
    rfl
  exact ht.cast hId hComp

/-- The opposite composite uses the separately constructed actual Id-to-NP homotopy. -/
def negativePositiveHomotopy (x : Core C) :
    ContinuousMap.Homotopy (ContinuousMap.id (genericSpace (C := C)))
      ((positiveRealizedMap x).comp (negativeRealizedMap x)) := by
  let N : SSet.{max u v} := genericNerve (C := C)
  let f : N ⟶ N := negativeNerveMap x
  let g : N ⟶ N := positiveNerveMap x
  let ht := SSet.realizeHomotopy N N (𝟙 N) (f ≫ g) (negativePositiveNerveHomotopy x)
  have hId : (SSet.toTop.map (𝟙 N)).hom = ContinuousMap.id (genericSpace (C := C)) := by
    rewrite [SSet.toTop.map_id]
    rfl
  have hComp : (SSet.toTop.map (f ≫ g)).hom =
      (positiveRealizedMap x).comp (negativeRealizedMap x) := by
    rewrite [SSet.toTop.map_comp]
    rfl
  exact ht.cast hId hComp

/-- An unbased homotopy equivalence realizes the actual generic P and N as its two maps. -/
def positiveRealizedEquiv (x : Core C) :
    ContinuousMap.HomotopyEquiv (genericSpace (C := C)) (genericSpace (C := C)) where
  toFun := positiveRealizedMap x
  invFun := negativeRealizedMap x
  left_inv := by exact ⟨(positiveNegativeHomotopy x).symm⟩
  right_inv := by exact ⟨(negativePositiveHomotopy x).symm⟩

/-- The same realized negative map is a homotopy equivalence with P as its actual inverse. -/
def negativeRealizedEquiv (x : Core C) :
    ContinuousMap.HomotopyEquiv (genericSpace (C := C)) (genericSpace (C := C)) :=
  (positiveRealizedEquiv x).symm

/-- The positive equivalence has the exact forward map, rather than only a conjugate. -/
theorem positiveRealizedEquiv_toFun (x : Core C) :
    (positiveRealizedEquiv x).toFun = (SSet.toTop.map (positiveNerveMap x)).hom := rfl

/-- Its inverse is the exact realized generic negative functor. -/
theorem positiveRealizedEquiv_invFun (x : Core C) :
    (positiveRealizedEquiv x).invFun = (SSet.toTop.map (negativeNerveMap x)).hom := rfl

/-- The negative equivalence uses the same actual negative map forward. -/
theorem negativeRealizedEquiv_toFun (x : Core C) :
    (negativeRealizedEquiv x).toFun = (SSet.toTop.map (negativeNerveMap x)).hom := rfl

/-- Its inverse is the same actual positive map. -/
theorem negativeRealizedEquiv_invFun (x : Core C) :
    (negativeRealizedEquiv x).invFun = (SSet.toTop.map (positiveNerveMap x)).hom := rfl

end CategoryTheory.GenericCoreTranslation

end

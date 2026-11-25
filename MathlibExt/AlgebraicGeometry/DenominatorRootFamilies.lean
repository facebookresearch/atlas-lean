/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.MonoidSheafCharts
public import Mathlib.CategoryTheory.Core

/-!
# Actual denominator-root extension categories

A root is a symmetric-monoidal extension on the actual denominator sheaf,
with a monoidal/cartesian isomorphism on the original sheaf. Its arrows
preserve that comparison. The fibre groupoid is the core of this actual
category, not a named abstract root carrier.

Reference: Borne--Vistoli arXiv:1001.0466v2, Definitions4.9--4.16.
The stack/descent and parabolic comparison are separate Wanted results.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.DenominatorRootFamilies
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite
open _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.LineBundleTaskContracts
open MathlibExt.AlgebraicGeometry.DeligneFaltingsSheaves
universe u

/-- Isomorphisms of actual DF structures over a fixed monoid sheaf. -/
structure StructureHom {X : Scheme.{u}} {A : MonoidSheaf X} (D E : Structure A) where
  comparison : ∀ (U : X.Etale) (a : A.obj.obj (op U)),
    (D.chart U).module a ≅ (E.chart U).module a
  section_eq : ∀ U a,
    (D.chart U).sectionMap a ≫ (comparison U a).hom = (E.chart U).sectionMap a
  unit : ∀ U, (comparison U 1).hom ≫ (E.chart U).unit.hom = (D.chart U).unit.hom
  multiplication : ∀ U a b,
    tensorMap (comparison U a).hom (comparison U b).hom ≫
      ((E.chart U).multiplication a b).hom =
    ((D.chart U).multiplication a b).hom ≫ (comparison U (a*b)).hom
  reindexing : ∀ {U V : X.Etale} (f : V ⟶ U) (a : A.obj.obj (op U)),
    (Scheme.Modules.pullback f.left).map (comparison U a).hom ≫ (E.reindex f a).hom =
      (D.reindex f a).hom ≫ (comparison V (A.obj.map f.op a)).hom

@[ext] theorem StructureHom.ext {X : Scheme.{u}} {A : MonoidSheaf X}
    {D E : Structure A} {f g : StructureHom D E}
    (h : ∀ U a, f.comparison U a = g.comparison U a) : f = g := by
  cases f
  cases g
  congr
  exact funext fun U => funext fun a => h U a

instance structureCategory {X : Scheme.{u}} (A : MonoidSheaf X) : Category (Structure A) where
  Hom D E := StructureHom D E
  id D := ⟨fun _ _ => Iso.refl _, by intros; simp, by intros; simp,
    by intros; simp, by intros; simp⟩
  comp f g :=
    { comparison := fun U a => f.comparison U a ≪≫ g.comparison U a
      section_eq := by
        intro U a
        simp only [Iso.trans_hom, ← Category.assoc]
        rw [f.section_eq, g.section_eq]
      unit := by intro U; rw [Iso.trans_hom, Category.assoc, g.unit, f.unit]
      multiplication := by
        intro U a b
        simp only [Iso.trans_hom, tensorMap_comp, Category.assoc]
        rw [g.multiplication, ← Category.assoc, f.multiplication]
        exact Category.assoc _ _ _
      reindexing := by
        intro U V h a
        simp only [Iso.trans_hom, Functor.map_comp, Category.assoc]
        rw [g.reindexing, ← Category.assoc, f.reindexing]
        exact Category.assoc _ _ _ }
  id_comp f := by apply StructureHom.ext; intro U a; ext; simp
  comp_id f := by apply StructureHom.ext; intro U a; ext; simp
  assoc f g h := by apply StructureHom.ext; intro U a; ext; simp

lemma sheafMapNaturality {X : Scheme.{u}} {A B : MonoidSheaf X} (j : A ⟶ B)
    {U V : X.Etale} (f : V ⟶ U) (a : A.obj.obj (op U)) :
    B.obj.map f.op (j.hom.app (op U) a) = j.hom.app (op V) (A.obj.map f.op a) :=
  (ConcreteCategory.congr_hom (j.hom.naturality f.op) a).symm

/-- A genuine monoidal/cartesian comparison along a denominator map. -/
structure ComparisonAlong {X : Scheme.{u}} {A B : MonoidSheaf X} (j : A ⟶ B)
    (D : Structure A) (E : Structure B) where
  comparison : ∀ (U : X.Etale) (a : A.obj.obj (op U)),
    (D.chart U).module a ≅ (E.chart U).module (j.hom.app (op U) a)
  section_eq : ∀ U a,
    (D.chart U).sectionMap a ≫ (comparison U a).hom =
      (E.chart U).sectionMap (j.hom.app (op U) a)
  unit : ∀ U, (comparison U 1).hom ≫
    eqToHom (congrArg ((E.chart U).module) (map_one (j.hom.app (op U)).hom)) ≫
      (E.chart U).unit.hom = (D.chart U).unit.hom
  multiplication : ∀ U a b,
    tensorMap (comparison U a).hom (comparison U b).hom ≫
      ((E.chart U).multiplication (j.hom.app (op U) a) (j.hom.app (op U) b)).hom ≫
      eqToHom (congrArg ((E.chart U).module) (map_mul (j.hom.app (op U)).hom a b).symm) =
    ((D.chart U).multiplication a b).hom ≫ (comparison U (a*b)).hom
  reindexing : ∀ {U V : X.Etale} (f : V ⟶ U) (a : A.obj.obj (op U)),
    (Scheme.Modules.pullback f.left).map (comparison U a).hom ≫
      (E.reindex f (j.hom.app (op U) a)).hom ≫
      eqToHom (congrArg ((E.chart V).module) (sheafMapNaturality j f a)) =
    (D.reindex f a).hom ≫ (comparison V (A.obj.map f.op a)).hom

/-- Actual extension objects on the fixed scheme. -/
structure Extension {X : Scheme.{u}} {A B : MonoidSheaf X} (j : A ⟶ B) (D : Structure A) where
  extended : Structure B
  restriction : ComparisonAlong j D extended

namespace Extension
variable {X : Scheme.{u}} {A B : MonoidSheaf X} {j : A ⟶ B} {D : Structure A}

/-- The root comparison must be preserved by every actual arrow. -/
structure Hom (E F : Extension j D) where
  hom : E.extended ⟶ F.extended
  restriction : ∀ U a,
    (E.restriction.comparison U a).hom ≫ (hom.comparison U (j.hom.app (op U) a)).hom =
      (F.restriction.comparison U a).hom

@[ext] theorem Hom.ext {E F : Extension j D} {f g : Hom E F}
    (h : f.hom = g.hom) : f = g := by cases f; cases g; cases h; rfl

instance : Category (Extension j D) where
  Hom E F := Hom E F
  id E := ⟨𝟙 E.extended, by
    intro U a
    change (E.restriction.comparison U a).hom ≫ 𝟙 _ = _
    exact Category.comp_id _⟩
  comp f g := ⟨f.hom ≫ g.hom, by
    intro U a
    change _ ≫ (f.hom.comparison U _).hom ≫ (g.hom.comparison U _).hom = _
    rw [← Category.assoc, f.restriction, g.restriction]⟩
  id_comp f := by apply Hom.ext; exact Category.id_comp _
  comp_id f := by apply Hom.ext; exact Category.comp_id _
  assoc f g h := by apply Hom.ext; exact Category.assoc _ _ _

end Extension

/-- The true root-extension fibre groupoid uses native isomorphisms. -/
abbrev RootFibre {X : Scheme.{u}} {A B : MonoidSheaf X} (j : A ⟶ B) (D : Structure A) :=
  Core (Extension j D)

end MathlibExt.AlgebraicGeometry.DenominatorRootFamilies

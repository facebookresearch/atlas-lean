/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Algebra.TrivSqZeroExt.Basic
public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
public import Mathlib.CategoryTheory.Comma.Over.Basic

/-!
# Actual p-nilpotent square-zero tangent tests

Objects are actual p-nilpotent algebras C over the base R and actual
C-modules M. Their square-zero tests are Spec(C plus M), and morphisms
use the prescribed algebra map and semilinear module map. This tests
formal p-divisible groups over any p-complete base, including bases where
p itself is not zero. No chosen tangent vector-space carrier is supplied.

Scholze--Weinstein, arXiv:1211.6357v2, Sections1-2; Messing, *The crystals
associated to Barsotti-Tate groups* (1972), ChapterII.
-/

@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.PDivisibleTangentTests

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped RightActions

variable (p : ℕ) (R : Type) [CommRing R]

structure Test where
  algebra : CommAlgCat.{0} R
  module : ModuleCat.{0} algebra
  nilpotent : IsNilpotent (p : algebra)

@[ext] structure TestHom (C D : Test p R) where
  base : C.algebra →ₐ[R] D.algebra
  linear : C.module →ₛₗ[base.toRingHom] D.module

theorem TestHom.ext_of_apply {C D : Test p R} (f g : TestHom p R C D)
    (hb : f.base = g.base) (hl : ∀ x, f.linear x = g.linear x) : f = g := by
  cases f with
  | mk bf lf =>
    cases g with
    | mk bg lg =>
      cases hb
      have h : lf = lg := LinearMap.ext hl
      cases h
      rfl

instance : Category (Test p R) where
  Hom := TestHom p R
  id C := ⟨AlgHom.id R C.algebra, LinearMap.id⟩
  comp f g := ⟨g.base.comp f.base, g.linear.comp f.linear⟩
  id_comp f := by
    apply TestHom.ext_of_apply
    · ext x; rfl
    · intro x; rfl
  comp_id f := by
    apply TestHom.ext_of_apply
    · ext x; rfl
    · intro x; rfl
  assoc f g h := by
    apply TestHom.ext_of_apply
    · ext x; rfl
    · intro x; rfl

instance Test.baseModule (C : Test p R) : Module R C.module :=
  Module.compHom C.module (algebraMap R C.algebra)

instance Test.baseTower (C : Test p R) : IsScalarTower R C.algebra C.module where
  smul_assoc r c m := by
    rw [Algebra.smul_def]
    change (algebraMap R C.algebra r * c) • m =
      algebraMap R C.algebra r • (c • m)
    exact mul_smul _ _ _

def Test.oppositeToRing (C : Test p R) : C.algebraᵐᵒᵖ →+* C.algebra where
  toFun := MulOpposite.unop
  map_zero' := rfl
  map_one' := rfl
  map_add' _ _ := rfl
  map_mul' _x _y := mul_comm _ _

instance Test.rightModule (C : Test p R) : Module C.algebraᵐᵒᵖ C.module :=
  Module.compHom C.module (C.oppositeToRing p R)

instance Test.centralScalar (C : Test p R) : IsCentralScalar C.algebra C.module where
  op_smul_eq_smul _r _m := rfl

/-- The actual square-zero algebra of this test object. -/
abbrev Extension (C : Test p R) := TrivSqZeroExt C.algebra C.module

/-- The prescribed base and tangent coefficients define the ring map. -/
def extensionMap {C D : Test p R} (f : C ⟶ D) :
    Extension p R C →ₐ[R] Extension p R D where
  toFun x := (f.base x.fst, f.linear x.snd)
  map_zero' := TrivSqZeroExt.ext (map_zero f.base) (map_zero f.linear)
  map_one' := TrivSqZeroExt.ext (map_one f.base) (map_zero f.linear)
  map_add' x y := TrivSqZeroExt.ext (map_add f.base _ _) (map_add f.linear _ _)
  map_mul' x y := by
    apply TrivSqZeroExt.ext
    · exact map_mul f.base _ _
    · change f.linear (x.fst • y.snd + y.fst • x.snd) =
        f.base x.fst • f.linear y.snd + f.base y.fst • f.linear x.snd
      rw [map_add, f.linear.map_smulₛₗ, f.linear.map_smulₛₗ]
      rfl
  commutes' a := TrivSqZeroExt.ext (f.base.commutes a) (map_zero f.linear)

/-- The actual base-algebra scheme in the test. -/
def baseScheme (C : Test p R) : Over (Spec (.of R)) :=
  Over.mk (Spec.algebraMap R C.algebra)

/-- The actual nilpotent infinitesimal extension scheme. -/
def extensionScheme (C : Test p R) : Over (Spec (.of R)) :=
  Over.mk (Spec.algebraMap R (Extension p R C))

/-- Its actual zero section, induced by augmentation. -/
def zeroSection (C : Test p R) : baseScheme p R C ⟶ extensionScheme p R C :=
  Over.homMk (Spec.map (CommRingCat.ofHom
    (TrivSqZeroExt.fstHom R C.algebra C.module).toRingHom)) (by
      change Spec.map _ ≫ Spec.map _ = Spec.map _
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
      have h : (TrivSqZeroExt.fstHom R C.algebra C.module).toRingHom.comp
          (algebraMap R (Extension p R C)) = algebraMap R C.algebra :=
        RingHom.ext fun a ↦ (TrivSqZeroExt.fstHom R C.algebra C.module).commutes a
      rw [h])

/-- Actual affine Spec in the slice, for arbitrary algebra tests. -/
def specOverFunctor : (CommAlgCat.{0} R)ᵒᵖ ⥤ Over (Spec (.of R)) where
  obj C := Over.mk (Spec.algebraMap R C.unop)
  map f := Over.homMk (Spec.map (CommRingCat.ofHom f.unop.hom.toRingHom)) (by
    change Spec.map _ ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    have h : f.unop.hom.toRingHom.comp (algebraMap R _) = algebraMap R _ :=
      RingHom.ext fun a ↦ f.unop.hom.commutes a
    rw [h])
  map_id _ := by
    apply Over.OverMorphism.ext
    exact Spec.map_id _
  map_comp {C D E} f g := by
    apply Over.OverMorphism.ext
    change Spec.map (CommRingCat.ofHom
      (f.unop.hom.comp g.unop.hom).toRingHom) =
        Spec.map (CommRingCat.ofHom f.unop.hom.toRingHom) ≫
          Spec.map (CommRingCat.ofHom g.unop.hom.toRingHom)
    exact Spec.map_comp (CommRingCat.ofHom g.unop.hom.toRingHom)
      (CommRingCat.ofHom f.unop.hom.toRingHom)

/-- The base algebra functor keeps the given actual algebra maps. -/
def baseAlgebraFunctor : Test p R ⥤ CommAlgCat.{0} R where
  obj C := C.algebra
  map f := CommAlgCat.ofHom f.base
  map_id _ := by ext x; rfl
  map_comp _ _ := by ext x; rfl

/-- The square-zero algebra functor keeps the actual semilinear maps. -/
def extensionAlgebraFunctor : Test p R ⥤ CommAlgCat.{0} R where
  obj C := CommAlgCat.of R (Extension p R C)
  map f := CommAlgCat.ofHom (extensionMap p R f)
  map_id _ := by ext x <;> rfl
  map_comp _ _ := by ext x <;> rfl

/-- The actual contravariant base and square-zero test functors. -/
def baseTests : (Test p R)ᵒᵖ ⥤ Over (Spec (.of R)) :=
  (baseAlgebraFunctor p R).op ⋙ specOverFunctor R

def extensionTests : (Test p R)ᵒᵖ ⥤ Over (Spec (.of R)) :=
  (extensionAlgebraFunctor p R).op ⋙ specOverFunctor R

/-- The actual algebra augmentation, with its coefficient square. -/
def algebraAugmentations : extensionAlgebraFunctor p R ⟶ baseAlgebraFunctor p R where
  app C := CommAlgCat.ofHom (TrivSqZeroExt.fstHom R C.algebra C.module)
  naturality {C D} f := by ext x; rfl

/-- Spec sends that exact augmentation to the natural zero-section map. -/
def augmentations : baseTests p R ⟶ extensionTests p R :=
  Functor.whiskerRight (NatTrans.op (algebraAugmentations p R)) (specOverFunctor R)

end MathlibExt.AlgebraicGeometry.PDivisibleTangentTests

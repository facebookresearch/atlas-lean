/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.LineBundleTaskContracts
public import MathlibExt.AlgebraicGeometry.NativeTensorComparisons
public import MathlibExt.AlgebraicGeometry.LogStructures
public import Mathlib.GroupTheory.MonoidLocalization.GrothendieckGroup

/-!
# Actual divisor groupoids and Deligne--Faltings chart data

Objects are native invertible module sheaves with sections; arrows are
section-preserving native module isomorphisms. The tensor maps are the
fixed presheaf tensor followed by sheafification. Chart multiplication,
units and symmetry use these actual maps. Associativity is tested from
the actual sheafification of the presheaf triple tensor, so no unrelated
monoidal operation is supplied.

The weight category has actual groupification elements and monoid arrows.
References: Borne--Vistoli, arXiv:1001.0466v2, Definitions2.1,3.1,5.1.
Native sheafification/tensor and groupification primitives are completed
Mathlib/Atlas code; no root/parabolic equivalence is assumed.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.DeligneFaltingsCategories

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory
open _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.CoherentCurveLinearSeries
open MathlibExt.AlgebraicGeometry.AlgebraicLineBundleFamilies
open MathlibExt.AlgebraicGeometry.LineBundleTaskContracts

universe u

/-- A genuine line bundle with an actual section. -/
structure DivisorObject (X : Scheme.{u}) where
  module : X.Modules
  line : IsLineBundle module
  sectionMap : Section module

namespace DivisorObject

variable {X : Scheme.{u}}

/-- Section-preserving invertible module maps. -/
structure Hom (L M : DivisorObject X) where
  iso : L.module ≅ M.module
  section_eq : L.sectionMap ≫ iso.hom = M.sectionMap

@[ext] theorem Hom.ext {L M : DivisorObject X} {f g : Hom L M}
    (h : f.iso = g.iso) : f = g := by
  cases f
  cases g
  cases h
  rfl

instance : Groupoid (DivisorObject X) where
  Hom L M := Hom L M
  id L := ⟨Iso.refl _, by simp⟩
  comp f g := ⟨f.iso ≪≫ g.iso, by rw [Iso.trans_hom, ← Category.assoc, f.section_eq,
    g.section_eq]⟩
  inv f := ⟨f.iso.symm, by rw [← f.section_eq]; simp⟩
  id_comp f := by apply Hom.ext; ext; simp
  comp_id f := by apply Hom.ext; ext; simp
  assoc f g h := by apply Hom.ext; ext; simp
  inv_comp f := by apply Hom.ext; ext; simp
  comp_inv f := by apply Hom.ext; ext; simp

/-- The faithful native module forgetful functor. -/
def forget : DivisorObject X ⥤ X.Modules where
  obj L := L.module
  map f := f.iso.hom
  map_id _L := rfl
  map_comp _f _g := rfl

instance : (forget (X := X)).Faithful where
  map_injective h := by apply Hom.ext; exact Iso.ext h

/-- The structure sheaf is locally a rank-one free sheaf. -/
theorem structureLine (X : Scheme.{u}) : IsLineBundle (structureModule X) := by
  intro x
  refine ⟨⊤, by trivial, ?_⟩
  let f := (⊤ : X.Opens).ι
  have : (TopologicalSpace.Opens.map f.base).Final := by infer_instance
  have : (SheafOfModules.pushforward f.toRingCatSheafHom).IsRightAdjoint :=
    inferInstanceAs (Scheme.Modules.pushforward f).IsRightAdjoint
  have := SheafOfModules.instIsIsoPullbackObjUnitToUnitOfFinal f.toRingCatSheafHom
  exact ⟨asIso (SheafOfModules.pullbackObjUnitToUnit f.toRingCatSheafHom)⟩

/-- The actual unit line with unit section. -/
def unitObject (X : Scheme.{u}) : DivisorObject X :=
  ⟨structureModule X, structureLine X, 𝟙 (structureModule X)⟩

end DivisorObject

/-! The sheaf tensor's adjunction, unit, symmetry and triple-tensor comparisons live in
`NativeTensorComparisons`; their names stay available here. -/
export NativeTensorComparisons (moduleAdjunction tensorLeftUnit tensorRightUnit tensorSwap
  tripleTensor tripleLeft tripleRight)

/-- A symmetric-monoidal line/section chart, with fixed native coherence maps. -/
structure DeligneFaltingsChart (X : Scheme.{u}) (P : CommMonCat.{u}) where
  module : P → X.Modules
  line : ∀ p, IsLineBundle (module p)
  sectionMap : ∀ p, Section (module p)
  unit : module 1 ≅ structureModule X
  multiplication : ∀ p q, moduleTensor X (module p) (module q) ≅ module (p * q)
  unit_section : sectionMap 1 ≫ unit.hom = 𝟙 (structureModule X)
  multiplication_section : ∀ p q,
    tensorSection (sectionMap p) (sectionMap q) ≫ (multiplication p q).hom = sectionMap (p * q)
  left_unit : ∀ p,
    (multiplication 1 p).hom ≫ eqToHom (congrArg module (one_mul p)) =
      tensorMap unit.hom (𝟙 (module p)) ≫ (tensorLeftUnit X (module p)).hom
  right_unit : ∀ p,
    (multiplication p 1).hom ≫ eqToHom (congrArg module (mul_one p)) =
      tensorMap (𝟙 (module p)) unit.hom ≫ (tensorRightUnit X (module p)).hom
  symmetry : ∀ p q,
    (multiplication p q).hom =
      (tensorSwap X (module p) (module q)).hom ≫ (multiplication q p).hom ≫
        eqToHom (congrArg module (mul_comm q p))
  associativity : ∀ p q r,
    tripleLeft X (module p) (module q) (module r) ≫
      tensorMap (multiplication p q).hom (𝟙 (module r)) ≫ (multiplication (p*q) r).hom =
    tripleRight X (module p) (module q) (module r) ≫
      tensorMap (𝟙 (module p)) (multiplication q r).hom ≫ (multiplication p (q*r)).hom ≫
        eqToHom (congrArg module (mul_assoc p q r).symm)
  trivial_kernel : ∀ p, (∃ f : module p ≅ structureModule X,
    sectionMap p ≫ f.hom = 𝟙 (structureModule X)) → p = 1

/-- Actual groupification weights; no freely supplied lattice. -/
@[ext] structure Weight (P : CommMonCat.{u}) where
  value : Algebra.GrothendieckGroup P

instance (P : CommMonCat.{u}) : One (Weight P) := ⟨⟨1⟩⟩
instance (P : CommMonCat.{u}) : Mul (Weight P) := ⟨fun x y => ⟨x.value * y.value⟩⟩

/-- The transparent equivalence with the actual groupification. -/
def weightEquiv (P : CommMonCat.{u}) : Weight P ≃ Algebra.GrothendieckGroup P where
  toFun x := x.value
  invFun x := ⟨x⟩
  left_inv _x := rfl
  right_inv _x := rfl

/-- The actual weight attached to a monoid element. -/
def monoidWeight (P : CommMonCat.{u}) (p : P) : Weight P :=
  ⟨Algebra.GrothendieckGroup.of p⟩

/-- Weight arrows retain their monoid label, including nonintegral monoids. -/
structure WeightHom (P : CommMonCat.{u}) (x y : Weight P) where
  label : P
  equation : Algebra.GrothendieckGroup.of label * x.value = y.value

@[ext] theorem WeightHom.ext {P : CommMonCat.{u}} {x y : Weight P}
    {f g : WeightHom P x y} (h : f.label = g.label) : f = g := by
  cases f
  cases g
  cases h
  rfl

instance weightCategory (P : CommMonCat.{u}) : Category (Weight P) where
  Hom x y := WeightHom P x y
  id x := ⟨1, by simp⟩
  comp {x y z} f g := ⟨f.label * g.label, by
    calc
      Algebra.GrothendieckGroup.of (f.label * g.label) * x.value =
          Algebra.GrothendieckGroup.of g.label *
            (Algebra.GrothendieckGroup.of f.label * x.value) := by rw [map_mul]; ac_rfl
      _ = _ := by rw [f.equation]
      _ = _ := g.equation⟩
  id_comp f := by apply WeightHom.ext; exact one_mul _
  comp_id f := by apply WeightHom.ext; exact mul_one _
  assoc f g h := by apply WeightHom.ext; exact mul_assoc _ _ _

end MathlibExt.AlgebraicGeometry.DeligneFaltingsCategories

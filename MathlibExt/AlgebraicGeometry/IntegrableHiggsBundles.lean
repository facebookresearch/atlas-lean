/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Basic.Complex.Basic
public import MathlibExt.AlgebraicGeometry.AlgebraicDifferentialTensor
public import MathlibExt.AlgebraicGeometry.GeometricHiggsFamilies

/-!
# Integrable algebraic Higgs bundles in arbitrary dimension

The coefficient forms are the actual sheafification of sectionwise relative
Kähler exterior powers. Integrability is the literal square formed using
the actual sheaf tensor associator and wedge. Morphisms are all O-linear
field-preserving maps, not only isomorphisms. This gives the category needed
for the ordinary NAH equivalence; moduli groupoids may take its core.

References: Simpson, Higgs bundles and local systems (1992), §1;
Donagi--Gaitsgory, arXiv:math/0005132v3, §17.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.IntegrableHiggsBundles
open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory
open _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.CoherentCurveLinearSeries
open MathlibExt.AlgebraicGeometry.CurveVectorBundles
open MathlibExt.AlgebraicGeometry.AlgebraicLineBundleFamilies
open MathlibExt.AlgebraicGeometry.LineBundleTaskContracts
open MathlibExt.AlgebraicGeometry.NativeTensorComparisons

abbrev ComplexScheme := Over (Spec (CommRingCat.of ℂ))

/-- Actual algebraic differential forms; Omega1 is not assumed invertible. -/
abbrev Omega (X : ComplexScheme) (n : ℕ) :=
  AlgebraicDifferentialSheaves.forms ℂ X n

/-- The actual Higgs square, with its fixed target E tensor Omega2. -/
def square {X : ComplexScheme} {E : X.left.Modules}
    (theta : E ⟶ moduleTensor X.left E (Omega X 1)) :
    E ⟶ moduleTensor X.left E (Omega X 2) :=
  theta ≫ tensorMap theta (𝟙 (Omega X 1)) ≫
    (tensorAssociator X.left E (Omega X 1) (Omega X 1)).hom ≫
      tensorMap (𝟙 E) (AlgebraicDifferentialTensor.wedge ℂ X 1 1)

/-- An actual finite-rank integrable Higgs bundle. -/
structure HiggsBundle (X : ComplexScheme) where
  rank : ℕ
  module : X.left.Modules
  bundle : IsVectorBundle module rank
  theta : module ⟶ moduleTensor X.left module (Omega X 1)
  integrable : square theta = 0

namespace HiggsBundle
variable {X : ComplexScheme}

/-- All field-preserving module maps between actual Higgs bundles. -/
structure Hom (E F : HiggsBundle X) where
  map : E.module ⟶ F.module
  field_eq : map ≫ F.theta = E.theta ≫ tensorMap map (𝟙 (Omega X 1))

@[ext] theorem Hom.ext {E F : HiggsBundle X} {f g : Hom E F}
    (h : f.map = g.map) : f = g := by cases f; cases g; cases h; rfl

instance : Category (HiggsBundle X) where
  Hom E F := Hom E F
  id E := ⟨𝟙 _, by simp⟩
  comp f g := ⟨f.map ≫ g.map, by
    rw [Category.assoc, g.field_eq, ← Category.assoc, f.field_eq]
    simp only [Category.assoc, ← tensorMap_comp, Category.comp_id]⟩
  id_comp f := by apply Hom.ext; exact Category.id_comp _
  comp_id f := by apply Hom.ext; exact Category.comp_id _
  assoc f g h := by apply Hom.ext; exact Category.assoc _ _ _

/-- The actual module forgetful functor is faithful. -/
def forget : HiggsBundle X ⥤ X.left.Modules where
  obj E := E.module
  map f := f.map
  map_id _E := rfl
  map_comp _f _g := rfl

instance : (forget (X := X)).Faithful where
  map_injective h := by apply Hom.ext; exact h

end HiggsBundle

/-- The curve twisted-bundle data embed after the actual integrability proof;
no higher-dimensional zero-square is asserted without that proof. -/
def ofCurveTwisted {X : ComplexScheme} {r : ℕ}
    (E : GeometricHiggsFamilies.TwistedBundle X.left (Omega X 1) r)
    (h : square E.field = 0) : HiggsBundle X :=
  ⟨r, E.module, E.bundle, E.field, h⟩

end MathlibExt.AlgebraicGeometry.IntegrableHiggsBundles

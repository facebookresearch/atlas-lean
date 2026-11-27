/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.RelativeLambdaReindexing

/-!
# Zero-fibre comparison with actual algebraic Higgs bundles

The coefficient comparison identifies the actual inverse-image relative
Kähler sheaf with the actual constant-base Kähler exterior sheaf. Its
universal differential and wedge are fixed on the native generators.
The Higgs field uses the literal zero-parameter connection operator.

Ordinary universal/exterior comparisons are completed source integration:
AxiomMath/Stacks c496df0d9beea9deaeabcea8492605f9a0a2313b,
StacksFrontier/Topology/Sheaves/Modules/Differentials.lean and
StacksFrontier/Algebra/Category/ModuleCat/Sheaf/SectionwiseAlgebras.lean,
Apache 2.0 (no individual author notice). Mathlib sectionwise Kähler and
sheafification constructions at 56a005855ea17e0b0958f73ec801ae140b0a1679
are due to Joël Riou and retain their Apache 2.0 licenses.
Reference: Simpson, alg-geom/9604005v1, section 4.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
@[expose] public noncomputable section

  AlgebraicGeometry.SheafedSpace.sheaf

namespace MathlibExt.AlgebraicGeometry.LambdaZeroHiggsComparison

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open AlgebraicLambdaConnections RelativeDifferentialForms RelativeDeRhamDifferential
open IntegrableHiggsBundles LineBundleTaskContracts AlgebraicLineBundleFamilies
open NativeTensorComparisons
open DeligneFaltingsCategories

variable (X : ComplexScheme)

local instance (U : X.left.Opensᵒᵖ) : CommRing (X.left.ringCatSheaf.obj.obj U) :=
  inferInstanceAs (CommRing (X.left.presheaf.obj U))

def absoluteD0 (U : X.left.Opens) (a : Γ(X.left, U)) : (Omega X 1).val.obj (op U) :=
  (((moduleAdjunction X.left).unit.app
    (AlgebraicDifferentialSheaves.formsPresheaf ℂ X 1)).app (op U)).hom
      ((exteriorPower.oneEquiv (X.left.ringCatSheaf.obj.obj (op U))
        ((AlgebraicDifferentialSheaves.differentials ℂ X).obj (op U))).symm
          ((PresheafOfModulesOfCommRing.DifferentialsConstruction.derivation'
            (AlgebraicDifferentialSheaves.scalarMap ℂ X)).d a))

def absoluteBundleWedge (E : X.left.Modules) :
    moduleTensor X.left (moduleTensor X.left E (Omega X 1)) (Omega X 1) ⟶
      moduleTensor X.left E (Omega X 2) :=
  (tensorAssociator X.left E (Omega X 1) (Omega X 1)).hom ≫
    tensorMap (𝟙 E) (AlgebraicDifferentialTensor.wedge ℂ X 1 1)

structure AbsoluteFormsComparison where
  one : forms X.hom 1 ≅ Omega X 1
  two : forms X.hom 2 ≅ Omega X 2
  universal : ∀ (U : X.left.Opens) (a : Γ(X.left, U)),
    (one.hom.val.app (op U)).hom ((d0 X.hom).d a) = absoluteD0 X U a
  wedge : RelativeDifferentialForms.wedge X.hom ≫ two.hom =
    tensorMap one.hom one.hom ≫ AlgebraicDifferentialTensor.wedge ℂ X 1 1
  bundleWedge : ∀ E : X.left.Modules,
    tensorMap (tensorMap (𝟙 E) one.hom) one.hom ≫ absoluteBundleWedge X E =
      AlgebraicLambdaConnections.bundleWedge X.hom E ≫ tensorMap (𝟙 E) two.hom

variable {X} (C : AbsoluteFormsComparison X)

theorem square_comparison {E : X.left.Modules}
    (theta : E ⟶ moduleTensor X.left E (forms X.hom 1)) :
    IntegrableHiggsBundles.square (theta ≫ tensorMap (𝟙 E) C.one.hom) =
      relativeHiggsSquare theta ≫ tensorMap (𝟙 E) C.two.hom := by
  have h₁ : tensorMap (𝟙 E) C.one.hom ≫
      tensorMap (theta ≫ tensorMap (𝟙 E) C.one.hom) (𝟙 (Omega X 1)) =
      tensorMap theta (𝟙 (forms X.hom 1)) ≫
        tensorMap (tensorMap (𝟙 E) C.one.hom) C.one.hom := by
    simp only [← tensorMap_comp, Category.id_comp, Category.comp_id]
  change theta ≫ tensorMap (𝟙 E) C.one.hom ≫
    tensorMap (theta ≫ tensorMap (𝟙 E) C.one.hom) (𝟙 (Omega X 1)) ≫
      absoluteBundleWedge X E = _
  rw [← Category.assoc (tensorMap (𝟙 E) C.one.hom)
    (tensorMap (theta ≫ tensorMap (𝟙 E) C.one.hom) (𝟙 (Omega X 1)))
    (absoluteBundleWedge X E), h₁]
  simp only [Category.assoc]
  rw [C.bundleWedge]
  simp only [relativeHiggsSquare, Category.assoc]

variable {D : Differential X.hom}

def zeroHiggs (N : LambdaConnection X.hom 0 D) : HiggsBundle X where
  rank := N.rank
  module := N.object
  bundle := N.bundle
  theta := zeroTheta N ≫ tensorMap (𝟙 N.object) C.one.hom
  integrable := by rw [square_comparison, zeroTheta_integrable]; simp

theorem zeroHom_field {E F : LambdaConnection X.hom 0 D} (f : E ⟶ F) :
    f.map ≫ zeroTheta F = zeroTheta E ≫ tensorMap f.map (𝟙 (forms X.hom 1)) := by
  apply SheafOfModules.hom_ext
  ext1 U
  apply ModuleCat.hom_ext
  ext s
  symm
  exact f.connection U.unop s

def zeroFunctor : LambdaConnection X.hom 0 D ⥤ HiggsBundle X where
  obj N := zeroHiggs C N
  map f :=
    { map := f.map
      field_eq := by
        change f.map ≫ zeroTheta _ ≫ tensorMap (𝟙 _) C.one.hom =
          (zeroTheta _ ≫ tensorMap (𝟙 _) C.one.hom) ≫ tensorMap f.map (𝟙 (Omega X 1))
        rw [← Category.assoc, zeroHom_field]
        simp only [Category.assoc, ← tensorMap_comp, Category.comp_id, Category.id_comp] }
  map_id _ := by apply HiggsBundle.Hom.ext; rfl
  map_comp _ _ := by apply HiggsBundle.Hom.ext; rfl

structure ZeroEquivalence where
  equivalence : LambdaConnection X.hom 0 D ≌ HiggsBundle X
  functor_eq : equivalence.functor = zeroFunctor C

end MathlibExt.AlgebraicGeometry.LambdaZeroHiggsComparison

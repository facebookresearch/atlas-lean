/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Author: @toskua, Codex -/
module

import MathlibExt.Algebra.Homology.MappingCylinderQuasiIso
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Homology.Single
meta import Mathlib.Tactic.NormNum

/-!
# Integer mapping-cylinder endpoints and a nonidentity cylinder map

Multiplication by two on the integer complex concentrated in degree zero has a mapping
cylinder. The source endpoint projects with weight two and the target endpoint with weight
one, so the combined points `(2,3)` and `(3,2)` project to seven and eight.

A strict square from multiplication by two to multiplication by four has identity source
map and multiplication-by-two target map. Its cylinder map sends the first combined point
to a point whose projection is fourteen. Degree-zero coefficients use the canonical
single-complex object isomorphism. The target endpoint and projection form the actual
deformation retraction and are quasi-isomorphisms, with no desired-result hypothesis.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped ZeroObject

namespace MathlibExtTest.MappingCylinderClients

private abbrev C := ModuleCat.{0} ℤ
private abbrev Z : C := ModuleCat.of ℤ ℤ
private abbrev K := (ChainComplex.single₀ C).obj Z
private abbrev shape := ComplexShape.down ℕ

private abbrev phi2 : K ⟶ K := (2 : ℕ) • 𝟙 K
private abbrev phi4 : K ⟶ K := (4 : ℕ) • 𝟙 K

private lemma incoming (j : ℕ) : ∃ i, shape.Rel i j := ⟨j + 1, rfl⟩

private def degreeZeroIso : K.X 0 ≅ Z :=
  HomologicalComplex.singleObjXSelf shape 0 Z

private lemma coordinate_inverse (x : ℤ) :
    degreeZeroIso.hom.hom (degreeZeroIso.inv.hom x) = x :=
  ConcreteCategory.congr_hom degreeZeroIso.inv_hom_id x

private lemma twice_coordinate (z : K.X 0) :
    degreeZeroIso.hom.hom ((phi2.f 0).hom z) =
      2 * degreeZeroIso.hom.hom z := by
  rw [phi2, HomologicalComplex.nsmul_f_apply, HomologicalComplex.id_f,
    ModuleCat.hom_nsmul, ModuleCat.hom_id]
  simp only [LinearMap.smul_apply, LinearMap.id_apply, map_nsmul]
  rw [nsmul_eq_mul]

private def sourcePoint (x : ℤ) : (HomologicalComplex.mappingCylinder phi2).X 0 :=
  ((mappingCylinder.source phi2).f 0).hom (degreeZeroIso.inv.hom x)

private def targetPoint (x : ℤ) : (HomologicalComplex.mappingCylinder phi2).X 0 :=
  ((mappingCylinder.target phi2).f 0).hom (degreeZeroIso.inv.hom x)

private def value2 : (HomologicalComplex.mappingCylinder phi2).X 0 →ₗ[ℤ] ℤ :=
  degreeZeroIso.hom.hom.comp ((mappingCylinder.projection phi2).f 0).hom

private def value4 : (HomologicalComplex.mappingCylinder phi4).X 0 →ₗ[ℤ] ℤ :=
  degreeZeroIso.hom.hom.comp ((mappingCylinder.projection phi4).f 0).hom

private lemma source_value (x : ℤ) : value2 (sourcePoint x) = 2 * x := by
  have h : (mappingCylinder.source phi2).f 0 ≫
      (mappingCylinder.projection phi2).f 0 = phi2.f 0 := by
    simpa only [HomologicalComplex.comp_f] using
      congrArg (fun f : K ⟶ K => f.f 0) (mappingCylinder.source_projection phi2)
  have hx := congrArg
    (fun f : K.X 0 ⟶ K.X 0 => degreeZeroIso.hom.hom (f.hom (degreeZeroIso.inv.hom x))) h
  change value2 (sourcePoint x) =
    degreeZeroIso.hom.hom ((phi2.f 0).hom (degreeZeroIso.inv.hom x)) at hx
  exact hx.trans ((twice_coordinate _).trans (congrArg (fun z : ℤ => 2 * z)
    (coordinate_inverse x)))

private lemma target_value (x : ℤ) : value2 (targetPoint x) = x := by
  have h : (mappingCylinder.target phi2).f 0 ≫
      (mappingCylinder.projection phi2).f 0 = 𝟙 (K.X 0) := by
    simpa only [HomologicalComplex.comp_f, HomologicalComplex.id_f] using
      congrArg (fun f : K ⟶ K => f.f 0) (mappingCylinder.target_projection phi2)
  have hx := congrArg
    (fun f : K.X 0 ⟶ K.X 0 => degreeZeroIso.hom.hom (f.hom (degreeZeroIso.inv.hom x))) h
  change value2 (targetPoint x) = degreeZeroIso.hom.hom (degreeZeroIso.inv.hom x) at hx
  exact hx.trans (coordinate_inverse x)

private def combinedPoint (x y : ℤ) : (HomologicalComplex.mappingCylinder phi2).X 0 :=
  sourcePoint x + targetPoint y

private lemma combined_value (x y : ℤ) : value2 (combinedPoint x y) = 2 * x + y := by
  rw [combinedPoint, map_add, source_value, target_value]

example : value2 (combinedPoint 2 3) = (7 : ℤ) := by
  rw [combined_value]
  norm_num

example : value2 (combinedPoint 3 2) = (8 : ℤ) := by
  rw [combined_value]
  norm_num

example : combinedPoint 2 3 ≠ 0 := by
  intro hzero
  have h := combined_value 2 3
  rw [hzero, map_zero] at h
  norm_num at h

private def square : Arrow.mk phi2 ⟶ Arrow.mk phi4 where
  left := 𝟙 K
  right := phi2
  w := by
    simp [phi2, phi4, Preadditive.nsmul_comp, Preadditive.comp_nsmul, smul_smul]

private abbrev cylinderMap := mappingCylinder.map phi2 phi4 incoming square

example : value4 ((cylinderMap.f 0).hom (combinedPoint 2 3)) = (14 : ℤ) := by
  have h : cylinderMap.f 0 ≫ (mappingCylinder.projection phi4).f 0 =
      (mappingCylinder.projection phi2).f 0 ≫ phi2.f 0 := by
    simpa only [cylinderMap, HomologicalComplex.comp_f, square] using
      congrArg (fun f : HomologicalComplex.mappingCylinder phi2 ⟶ K => f.f 0)
        (mappingCylinder.map_projection phi2 phi4 incoming square)
  have hx := congrArg
    (fun f : (HomologicalComplex.mappingCylinder phi2).X 0 ⟶ K.X 0 =>
      degreeZeroIso.hom.hom (f.hom (combinedPoint 2 3))) h
  change value4 ((cylinderMap.f 0).hom (combinedPoint 2 3)) =
    degreeZeroIso.hom.hom ((phi2.f 0).hom
      (((mappingCylinder.projection phi2).f 0).hom (combinedPoint 2 3))) at hx
  have hval : value4 ((cylinderMap.f 0).hom (combinedPoint 2 3)) =
      2 * value2 (combinedPoint 2 3) := hx.trans (twice_coordinate _)
  rw [combined_value] at hval
  norm_num at hval
  exact hval

example : HomotopyEquiv K (HomologicalComplex.mappingCylinder phi2) :=
  mappingCylinder.homotopyEquiv phi2 incoming

example : QuasiIso (mappingCylinder.target phi2) :=
  mappingCylinder.target_quasiIso phi2 incoming

example : QuasiIso (mappingCylinder.projection phi2) :=
  mappingCylinder.projection_quasiIso phi2 incoming

end MathlibExtTest.MappingCylinderClients

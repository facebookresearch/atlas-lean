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
to a point whose projection is fourteen. The target endpoint and projection form the actual
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

private lemma source_value (x : ℤ) :
    ((mappingCylinder.projection phi2).f 0).hom
      (((mappingCylinder.source phi2).f 0).hom x) = 2 * x := by
  have h : (mappingCylinder.source phi2).f 0 ≫
      (mappingCylinder.projection phi2).f 0 = phi2.f 0 := by
    simpa only [HomologicalComplex.comp_f] using
      congrArg (fun f : K ⟶ K => f.f 0) (mappingCylinder.source_projection phi2)
  have hx := congrArg (fun f : K.X 0 ⟶ K.X 0 => f.hom x) h
  simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, phi2,
    HomologicalComplex.nsmul_f_apply, HomologicalComplex.id_f, ModuleCat.hom_nsmul,
    ModuleCat.hom_id, LinearMap.smul_apply, LinearMap.id_apply, nsmul_eq_mul] using hx

private lemma target_value (x : ℤ) :
    ((mappingCylinder.projection phi2).f 0).hom
      (((mappingCylinder.target phi2).f 0).hom x) = x := by
  have h : (mappingCylinder.target phi2).f 0 ≫
      (mappingCylinder.projection phi2).f 0 = 𝟙 (K.X 0) := by
    simpa only [HomologicalComplex.comp_f, HomologicalComplex.id_f] using
      congrArg (fun f : K ⟶ K => f.f 0) (mappingCylinder.target_projection phi2)
  have hx := congrArg (fun f : K.X 0 ⟶ K.X 0 => f.hom x) h
  simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_id,
    LinearMap.id_apply] using hx

private def combinedPoint (x y : ℤ) : (HomologicalComplex.mappingCylinder phi2).X 0 :=
  ((mappingCylinder.source phi2).f 0).hom x + ((mappingCylinder.target phi2).f 0).hom y

private lemma combined_value (x y : ℤ) :
    ((mappingCylinder.projection phi2).f 0).hom (combinedPoint x y) = 2 * x + y := by
  rw [combinedPoint, map_add, source_value, target_value]

example : ((mappingCylinder.projection phi2).f 0).hom (combinedPoint 2 3) = (7 : ℤ) := by
  rw [combined_value]
  norm_num

example : ((mappingCylinder.projection phi2).f 0).hom (combinedPoint 3 2) = (8 : ℤ) := by
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
    simp [phi2, phi4, Preadditive.nsmul_comp, Preadditive.comp_nsmul, nsmul_nsmul]

private abbrev cylinderMap := mappingCylinder.map phi2 phi4 incoming square

example : ((mappingCylinder.projection phi4).f 0).hom
    ((cylinderMap.f 0).hom (combinedPoint 2 3)) = (14 : ℤ) := by
  have h : cylinderMap.f 0 ≫ (mappingCylinder.projection phi4).f 0 =
      (mappingCylinder.projection phi2).f 0 ≫ phi2.f 0 := by
    simpa only [cylinderMap, HomologicalComplex.comp_f] using
      congrArg (fun f : HomologicalComplex.mappingCylinder phi2 ⟶ K => f.f 0)
        (mappingCylinder.map_projection phi2 phi4 incoming square)
  have hx := congrArg
    (fun f : (HomologicalComplex.mappingCylinder phi2).X 0 ⟶ K.X 0 =>
      f.hom (combinedPoint 2 3)) h
  simpa [ModuleCat.hom_comp, LinearMap.comp_apply, phi2,
    HomologicalComplex.nsmul_f_apply, HomologicalComplex.id_f, ModuleCat.hom_nsmul,
    ModuleCat.hom_id, LinearMap.smul_apply, LinearMap.id_apply, nsmul_eq_mul,
    combined_value] using hx

example : HomotopyEquiv K (HomologicalComplex.mappingCylinder phi2) :=
  mappingCylinder.homotopyEquiv phi2 incoming

example : QuasiIso (mappingCylinder.target phi2) :=
  mappingCylinder.target_quasiIso phi2 incoming

example : QuasiIso (mappingCylinder.projection phi2) :=
  mappingCylinder.projection_quasiIso phi2 incoming

end MathlibExtTest.MappingCylinderClients

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import MathlibExt.Algebra.Homology.LinearHomCochainComplexSingle
public import MathlibExt.Algebra.Homology.LinearHomCochainPairingHeterogeneous
public import Mathlib.Algebra.Module.ZMod

/-!
# Torsion coefficients in the degree-zero single-source Hom comparison

The integer chain single and the ZMod 4 coefficient module give an actual degree-zero
Hom cochain. The single-source comparison retains the cochain that sends one to three.
Coefficient doubling then gives two, so the comparison and coefficient map are tested on
nonzero values with a torsion coefficient. No coefficient projectivity or flatness is used.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits Opposite HomologicalComplex
open HomologicalComplex.LinearHomCochainPairingHeterogeneous

namespace HomSingleTorsionCoefficient

private abbrev F : ModuleCat.{0} ℤ := ModuleCat.of ℤ ℤ
private abbrev G : ModuleCat.{0} ℤ := ModuleCat.of ℤ (ZMod 4)
private abbrev S : ChainComplex (ModuleCat.{0} ℤ) ℕ :=
  (ChainComplex.single₀ (ModuleCat.{0} ℤ)).obj F
private abbrev C : CochainComplex (ModuleCat.{0} ℤ) ℕ := linearHomCochainComplex ℤ S G
private abbrev D : CochainComplex (ModuleCat.{0} ℤ) ℕ :=
  (CochainComplex.single₀ (ModuleCat.{0} ℤ)).obj (ModuleCat.of ℤ (F ⟶ G))
private def castThree : F ⟶ G :=
  ModuleCat.ofHom (LinearMap.toSpanSingleton ℤ (ZMod 4) (3 : ZMod 4))
private def double : G ⟶ G := ModuleCat.ofHom (LinearMap.lsmul ℤ (ZMod 4) (2 : ℤ))
private def phi : C.X 0 := castThree
private def compare : C ≅ D := linearHomCochainComplexSingle₀Iso ℤ F G

private theorem compare_value :
    (show F ⟶ G from (compare.hom.f 0).hom phi).hom (1 : ℤ) = (3 : ZMod 4) := by
  have h := congrArg
    (fun f : C.X 0 ⟶ D.X 0 =>
      (show F ⟶ G from f.hom phi).hom (1 : ℤ))
    (linearHomCochainComplexSingle₀Iso_hom_f_zero ℤ F G)
  simpa only [ModuleCat.hom_id, LinearMap.id_apply, phi, castThree,
    LinearMap.toSpanSingleton_apply, one_smul] using! h

example : (show F ⟶ G from (compare.hom.f 0).hom phi).hom (1 : ℤ) ≠ 0 := by
  rw [compare_value]
  decide

private def coefficientMap : C ⟶ C := linearHomCochainComparison ℤ (𝟙 S) double

private theorem coefficient_value :
    (show F ⟶ G from (coefficientMap.f 0).hom phi).hom (1 : ℤ) = (2 : ZMod 4) := by
  have h : @Eq (F ⟶ G) ((coefficientMap.f 0).hom phi) (castThree ≫ double) := by
    simpa only [HomologicalComplex.id_f, Category.id_comp, phi] using!
      (linearHomCochainComparison_f_apply ℤ (𝟙 S) double 0 castThree)
  have hv := congrArg (fun f : F ⟶ G => f.hom (1 : ℤ)) h
  calc
    _ = (castThree ≫ double).hom (1 : ℤ) := hv
    _ = (2 : ℤ) • (3 : ZMod 4) := rfl
    _ = 2 := by decide

example :
    (show F ⟶ G from (coefficientMap.f 0).hom phi).hom (1 : ℤ) ≠
      (show F ⟶ G from (compare.hom.f 0).hom phi).hom (1 : ℤ) := by
  rw [coefficient_value, compare_value]
  decide

example : (4 : ℤ) • (3 : ZMod 4) = 0 := by decide

end HomSingleTorsionCoefficient

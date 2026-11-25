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

public import MathlibExt.Algebra.Category.ModuleCat.RingEquivTensor
public import MathlibExt.Algebra.Category.ModuleCat.Length
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.CategoryTheory.Abelian.Projective.Resolution
public import Mathlib.CategoryTheory.Monoidal.Tor
public import Mathlib.CategoryTheory.Preadditive.Projective.Resolution
public import Mathlib.RingTheory.Length

/-!
# Native Tor and module-length transport along actual ring equivalences

The lightweight `RingEquivTensor` module supplies the original balanced
tensor transport and strong monoidal scalar restriction. Genuine coefficient
isomorphisms then transport every native Tor degree and its literal
extended-natural module length.
No tensor, Tor, length, or resolution-comparison certificate is supplied.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false

open CategoryTheory CategoryTheory.MonoidalCategory Functor.LaxMonoidal
open scoped TensorProduct

namespace ModuleCat

universe u v

variable {R S : Type u} [CommRing R] [CommRing S]

/-- Original native Tor is transported in every degree using the actual scalar equivalence. -/
def restrictScalarsTorIsoOfRingEquiv
    (e : R ≃+* S) (M N : ModuleCat.{u} S) (j : ℕ) :
    (restrictScalars e.toRingHom).obj (((Tor (ModuleCat.{u} S) j).obj M).obj N) ≅
      (((Tor (ModuleCat.{u} R) j).obj ((restrictScalars e.toRingHom).obj M)).obj
        ((restrictScalars e.toRingHom).obj N)) := by
  let F := restrictScalars e.toRingHom
  let T := (tensoringLeft (ModuleCat.{u} S)).obj M
  let T' := (tensoringLeft (ModuleCat.{u} R)).obj (F.obj M)
  let P := projectiveResolution N
  let Q := F.mapProjectiveResolution P
  let K := (T.mapHomologicalComplex (ComplexShape.down ℕ)).obj P.complex
  let c : (T'.mapHomologicalComplex (ComplexShape.down ℕ)).obj Q.complex ≅
      (F.mapHomologicalComplex (ComplexShape.down ℕ)).obj K :=
    (Functor.mapHomologicalComplexCompIso
      (restrictScalarsTensoringLeftIsoOfRingEquiv e M) (ComplexShape.down ℕ)).app P.complex ≪≫
      ((Functor.mapHomologicalComplexCompIso (Iso.refl (T ⋙ F))
        (ComplexShape.down ℕ)).app P.complex).symm
  let h : ((F.mapHomologicalComplex (ComplexShape.down ℕ)).obj K).homology j ≅ F.obj (K.homology j) :=
    (K.sc j).mapHomologyIso F
  exact F.mapIso (P.isoLeftDerivedObj T j) ≪≫ h.symm ≪≫
    (HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (ComplexShape.down ℕ) j).mapIso c.symm ≪≫
    (Q.isoLeftDerivedObj T' j).symm

/-- Actual native Tor transports given genuine coefficient maps and a genuine scalar ring equivalence. -/
def nativeTorIsoFromCoefficientIsos
    {R₁ S₁ : Type u} [CommRing R₁] [CommRing S₁]
    (eR : R₁ ≃+* S₁) (MR ML : ModuleCat.{u} R₁) (NR NL : ModuleCat.{u} S₁)
    (eRight : MR ≅ (ModuleCat.restrictScalars eR.toRingHom).obj NR)
    (eLeft : ML ≅ (ModuleCat.restrictScalars eR.toRingHom).obj NL) (j : ℕ) :
    ((Tor (ModuleCat.{u} R₁) j).obj MR).obj ML ≅
      (ModuleCat.restrictScalars eR.toRingHom).obj
        (((Tor (ModuleCat.{u} S₁) j).obj NR).obj NL) := by
  let F := ModuleCat.restrictScalars eR.toRingHom
  let first : ((Tor (ModuleCat.{u} R₁) j).obj MR).obj ML ≅
      ((Tor (ModuleCat.{u} R₁) j).obj (F.obj NR)).obj ML :=
    ((Tor (ModuleCat.{u} R₁) j).mapIso eRight).app ML
  let second : ((Tor (ModuleCat.{u} R₁) j).obj (F.obj NR)).obj ML ≅
      ((Tor (ModuleCat.{u} R₁) j).obj (F.obj NR)).obj (F.obj NL) :=
    ((Tor (ModuleCat.{u} R₁) j).obj (F.obj NR)).mapIso eLeft
  exact first ≪≫ second ≪≫ (ModuleCat.restrictScalarsTorIsoOfRingEquiv eR NR NL j).symm

/-- Compatibility specialization of the canonical surjective scalar-length API. -/
theorem restrictScalars_length_eq_of_ringEquiv
    {R₁ S₁ : Type u} [Ring R₁] [Ring S₁]
    (eR : R₁ ≃+* S₁) (N : ModuleCat.{v} S₁) :
    Module.length R₁ ((ModuleCat.restrictScalars eR.toRingHom).obj N) = Module.length S₁ N :=
  restrictScalars_length_eq eR.toRingHom eR.surjective N

/-- Genuine coefficient isomorphisms preserve every literal extended-natural native Tor length. -/
theorem nativeTorLength_eq_fromCoefficientIsos
    {R₁ S₁ : Type u} [CommRing R₁] [CommRing S₁]
    (eR : R₁ ≃+* S₁) (MR ML : ModuleCat.{u} R₁) (NR NL : ModuleCat.{u} S₁)
    (eRight : MR ≅ (ModuleCat.restrictScalars eR.toRingHom).obj NR)
    (eLeft : ML ≅ (ModuleCat.restrictScalars eR.toRingHom).obj NL) (j : ℕ) :
    Module.length R₁ (((Tor (ModuleCat.{u} R₁) j).obj MR).obj ML) =
      Module.length S₁ (((Tor (ModuleCat.{u} S₁) j).obj NR).obj NL) :=
  length_eq_of_restrictScalarsIso eR _ _
    (nativeTorIsoFromCoefficientIsos eR MR ML NR NL eRight eLeft j)

/-- The length of the actual native Tor object of the two specified original modules. -/
def nativeTorModuleLength (R₁ : Type u) [CommRing R₁]
    (MR ML : ModuleCat.{u} R₁) (j : ℕ) : ℕ∞ :=
  Module.length R₁ (((Tor (ModuleCat.{u} R₁) j).obj MR).obj ML)

end ModuleCat

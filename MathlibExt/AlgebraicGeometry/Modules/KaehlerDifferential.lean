/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Definitions/Def_AlgebraicGeometry_KaehlerModule.lean`
(https://github.com/anthropics/fermats-last-theorem):
Compared with the source files at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`.
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits:
Mathlib — https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Differentials.Presheaf
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.RingTheory.Kaehler.Polynomial
public import MathlibExt.AlgebraicGeometry.Modules.ExteriorPower

/-!
# The sheaf of relative Kähler differentials

For a morphism of schemes `f : X ⟶ Spec A`, the presheaf of relative
differentials is the pointwise presheaf of Kähler differentials of the
section rings over `A`; `kaehler` is its sheafification and
`topDifferentials d` its `d`-th exterior power.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry.Scheme.Hom

variable {A : Type u} [CommRing A] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of A))

def constToPresheaf : (Functor.const (X.Opens)ᵒᵖ).obj (CommRingCat.of A) ⟶ X.presheaf where
  app U := (Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ f.appLE ⊤ U.unop (by simp)
  naturality U V i := by
    simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.id_comp, Category.assoc]
    rw [Scheme.Hom.appLE_map]

@[reducible] def sectionsAlgebra (U : X.Opens) : Algebra A Γ(X, U) :=
  (f.constToPresheaf.app (op U)).hom.toAlgebra

@[reducible] def kaehlerPresheaf : X.PresheafOfModules :=
  PresheafOfModulesOfCommRing.DifferentialsConstruction.relativeDifferentials' f.constToPresheaf

instance (U : X.Opens) :
    Module Γ(X, U) (f.kaehlerPresheaf.obj (op U) : Type u) :=
  inferInstanceAs (Module Γ(X, U)
    (CommRingCat.KaehlerDifferential (f.constToPresheaf.app (op U)) : Type u))

def kaehler : X.Modules :=
  (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj f.kaehlerPresheaf

def topDifferentials (d : ℕ) : X.Modules :=
  Scheme.Modules.det d f.kaehler

abbrev topPresheaf (d : ℕ) : X.PresheafOfModules :=
  (Scheme.Modules.presheafExteriorPower X d).obj f.kaehlerPresheaf

@[simp] lemma kaehlerPresheaf_obj (U : (X.Opens)ᵒᵖ) :
    f.kaehlerPresheaf.obj U = CommRingCat.KaehlerDifferential (f.constToPresheaf.app U) := rfl

def kaehlerToSections (U : X.Opens) :
    (f.kaehlerPresheaf.obj (op U) : Type u) → (Γ(f.kaehler, U) : Type u) :=
  fun s => (((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app
    f.kaehlerPresheaf).app (op U)).hom s

def kaehlerToSectionsₗ (U : X.Opens) :
    (f.kaehlerPresheaf.obj (op U)) →ₗ[Γ(X, U)] (Γ(f.kaehler, U) : Type u) :=
  (((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app
    f.kaehlerPresheaf).app (op U)).hom

def topToSections (d : ℕ) (U : X.Opens) :
    (⋀[Γ(X, U)]^d (f.kaehlerPresheaf.obj (op U)) : Type u) →
      (Γ(f.topDifferentials d, U) : Type u) :=
  fun s => (((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app
      ((Scheme.Modules.presheafExteriorPower X d).obj f.kaehler.val)).app (op U)).hom
    (exteriorPower.map d (kaehlerToSectionsₗ f U) s)

theorem kaehlerToSections_add (U : X.Opens) (s t : f.kaehlerPresheaf.obj (op U)) :
    f.kaehlerToSections U (s + t) = f.kaehlerToSections U s + f.kaehlerToSections U t :=
  map_add (kaehlerToSectionsₗ f U) s t

theorem kaehlerPresheaf_nontrivial_polynomial (A : Type u) [CommRing A] [Nontrivial A] :
    letI f : Spec (CommRingCat.of (Polynomial A)) ⟶ Spec (CommRingCat.of A) :=
      Spec.map (CommRingCat.ofHom (algebraMap A (Polynomial A)))
    Nontrivial (f.kaehlerPresheaf.obj (op ⊤)) := by
  set f : Spec (CommRingCat.of (Polynomial A)) ⟶ Spec (CommRingCat.of A) :=
    Spec.map (CommRingCat.ofHom (algebraMap A (Polynomial A))) with hf

  let Γ' : Type u := Γ(Spec (CommRingCat.of (Polynomial A)), ⊤)
  letI algA : Algebra A Γ' := f.sectionsAlgebra ⊤
  let e : Γ' ≃+* Polynomial A :=
    (Scheme.ΓSpecIso (CommRingCat.of (Polynomial A))).commRingCatIsoToRingEquiv
  letI : Algebra Γ' (Polynomial A) := e.toRingHom.toAlgebra

  have hcomp : (algebraMap Γ' (Polynomial A)).comp (algebraMap A Γ') =
      algebraMap A (Polynomial A) := by
    refine RingHom.ext fun a => ?_
    change (Scheme.ΓSpecIso (CommRingCat.of (Polynomial A))).hom.hom
      ((f.appLE ⊤ ⊤ (by simp)).hom ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom a)) =
        algebraMap A (Polynomial A) a
    have h1 : f.appLE ⊤ ⊤ (by simp) = f.appTop := by
      simp [Scheme.Hom.appLE, Scheme.Hom.appTop]
      exact Category.comp_id _
    rw [h1]
    have h2 := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (algebraMap A (Polynomial A)))
    rw [← hf] at h2
    have h3 := congrArg (fun φ => φ.hom ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom a)) h2
    simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply] at h3
    rw [h3]
    change algebraMap A (Polynomial A) (((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫
      (Scheme.ΓSpecIso (CommRingCat.of A)).hom).hom a) = _
    rw [Iso.inv_hom_id]; rfl
  haveI : IsScalarTower A Γ' (Polynomial A) := IsScalarTower.of_algebraMap_eq' hcomp.symm
  have hsurj : Function.Surjective (KaehlerDifferential.map A A Γ' (Polynomial A)) :=
    KaehlerDifferential.map_surjective_of_surjective A A (h := e.surjective)
  haveI : Nontrivial (Ω[Polynomial A⁄A]) :=
    (KaehlerDifferential.polynomialEquiv A).toEquiv.nontrivial
  exact hsurj.nontrivial

end AlgebraicGeometry.Scheme.Hom

end

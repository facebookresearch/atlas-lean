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

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Linear
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Algebra.Tower
public import MathlibExt.CategoryTheory.Abelian.Ext.SizeEquiv

/-!
# Scalar actions on Ext through coefficient endomorphisms

A semiring acting by endomorphisms of the coefficient object acts on Ext by
postcomposition. A coefficient morphism intertwining two such actions induces
a linear map on Ext. Source precomposition and change of the Ext carrier
universe preserve these actions.

For a homomorphism of commutative rings `R → S`, an `S`-module coefficient
therefore gives an `S`-module structure on Ext in the category of `R`-modules.
The source retains only its `R`-module structure.
-/

@[expose] public section
noncomputable section

set_option autoImplicit false

open CategoryTheory

universe u v w w' wD s r

namespace CategoryTheory.Abelian.Ext

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]
  {S : Type s} [Semiring S]

/-- Restrict the native coefficient-endomorphism action along a semiring map. -/
@[instance_reducible]
def coefficientModule.{extU, homU, objU, scalarU}
    {C : Type objU} [Category.{homU} C] [Abelian C] [HasExt.{extU} C]
    {S : Type scalarU} [Semiring S] {Y : C} (ρ : S →+* End Y) (X : C) (n : ℕ) :
    Module S (Ext.{extU} X Y n) :=
  Module.compHom (Ext.{extU} X Y n) ρ

/-- Coefficient scalars act by the native degree-zero Ext postcomposition. -/
theorem coefficient_smul_def {X Y : C} (ρ : S →+* End Y) (n : ℕ)
    (s : S) (x : Ext.{w} X Y n) :
    letI := coefficientModule ρ X n
    s • x = x.comp (mk₀ (ρ s).asHom) (add_zero n) := rfl

/-- An equivariant coefficient morphism induces a scalar-linear Ext map. -/
def postcompOfCoefficientScalar {Y Z : C}
    (ρY : S →+* End Y) (ρZ : S →+* End Z) (f : Y ⟶ Z)
    (hf : ∀ s, (ρY s).asHom ≫ f = f ≫ (ρZ s).asHom) (X : C) (n : ℕ) :
    letI := coefficientModule ρY X n
    letI := coefficientModule ρZ X n
    Ext.{w} X Y n →ₗ[S] Ext.{w} X Z n := by
  letI := coefficientModule ρY X n
  letI := coefficientModule ρZ X n
  exact
    { toFun := fun x => x.comp (mk₀ f) (add_zero n)
      map_add' := fun x y => add_comp x y (mk₀ f) (add_zero n)
      map_smul' := fun s x => by
        change (x.comp (mk₀ (ρY s).asHom) (add_zero n)).comp (mk₀ f) (add_zero n) =
          (x.comp (mk₀ f) (add_zero n)).comp (mk₀ (ρZ s).asHom) (add_zero n)
        simp only [comp_assoc_of_second_deg_zero, mk₀_comp_mk₀, hf s] }

@[simp]
theorem postcompOfCoefficientScalar_apply {X Y Z : C}
    (ρY : S →+* End Y) (ρZ : S →+* End Z) (f : Y ⟶ Z)
    (hf : ∀ s, (ρY s).asHom ≫ f = f ≫ (ρZ s).asHom) (n : ℕ)
    (x : Ext.{w} X Y n) :
    postcompOfCoefficientScalar ρY ρZ f hf X n x =
      x.comp (mk₀ f) (add_zero n) := rfl

/-- Source precomposition is linear for every fixed coefficient action. -/
def precompOfCoefficientScalar {X X' Y : C}
    (ρ : S →+* End Y) (k : X' ⟶ X) (n : ℕ) :
    letI := coefficientModule ρ X n
    letI := coefficientModule ρ X' n
    Ext.{w} X Y n →ₗ[S] Ext.{w} X' Y n := by
  letI := coefficientModule ρ X n
  letI := coefficientModule ρ X' n
  exact
    { toFun := fun x => (mk₀ k).comp x (zero_add n)
      map_add' := fun x y => comp_add (mk₀ k) x y (zero_add n)
      map_smul' := fun s x => by
        change (mk₀ k).comp ((ρ s) • x) (zero_add n) =
          (ρ s) • ((mk₀ k).comp x (zero_add n))
        exact comp_end_smul (mk₀ k) x (zero_add n) (ρ s) }

@[simp]
theorem precompOfCoefficientScalar_apply {X X' Y : C}
    (ρ : S →+* End Y) (k : X' ⟶ X) (n : ℕ) (x : Ext.{w} X Y n) :
    precompOfCoefficientScalar ρ k n x = (mk₀ k).comp x (zero_add n) := rfl

/-- Native Ext carrier transport is linear for the same coefficient action. -/
def coefficientSizeEquiv [HasExt.{w'} C] [HasDerivedCategory.{wD} C]
    {Y : C} (ρ : S →+* End Y) (X : C) (n : ℕ) :
    letI : Module S (Ext.{w} X Y n) := coefficientModule.{w, v, u, s} ρ X n
    letI : Module S (Ext.{w'} X Y n) := coefficientModule.{w', v, u, s} ρ X n
    Ext.{w} X Y n ≃ₗ[S] Ext.{w'} X Y n := by
  letI : Module S (Ext.{w} X Y n) := coefficientModule.{w, v, u, s} ρ X n
  letI : Module S (Ext.{w'} X Y n) := coefficientModule.{w', v, u, s} ρ X n
  refine
    { sizeEquiv.{wD, w, w', v, u} X Y n with
      map_smul' := ?_ }
  intro s x
  change sizeEquiv.{wD, w, w', v, u} X Y n
      (x.comp (mk₀ (ρ s).asHom) (add_zero n)) =
    (sizeEquiv.{wD, w, w', v, u} X Y n x).comp (mk₀ (ρ s).asHom) (add_zero n)
  rw [sizeEquiv_comp, sizeEquiv_mk₀]

@[simp]
theorem coefficientSizeEquiv_apply [HasExt.{w'} C] [HasDerivedCategory.{wD} C]
    {Y : C} (ρ : S →+* End Y) (X : C) (n : ℕ) (x : Ext.{w} X Y n) :
    (coefficientSizeEquiv ρ X n x : Ext.{w'} X Y n) =
      sizeEquiv.{wD, w, w', v, u} X Y n x := rfl

@[simp]
theorem coefficientSizeEquiv_symm_apply [HasExt.{w'} C] [HasDerivedCategory.{wD} C]
    {Y : C} (ρ : S →+* End Y) (X : C) (n : ℕ) (x : Ext.{w'} X Y n) :
    ((coefficientSizeEquiv ρ X n).symm x : Ext.{w} X Y n) =
      sizeEquiv.{wD, w', w, v, u} X Y n x := rfl

end CategoryTheory.Abelian.Ext

namespace ModuleCat

variable {R : Type r} {S : Type s} [CommRing R] [CommRing S] (σ : R →+* S)

/-- Coefficient scalars as endomorphisms after restriction to `R`. -/
def extCoefficientRingHom (N : ModuleCat.{v} S) :
    S →+* End ((restrictScalars σ).obj N) := by
  letI : Algebra R S := σ.toAlgebra
  letI : IsScalarTower R S ((restrictScalars σ).obj N) :=
    IsScalarTower.of_algebraMap_smul (fun r n => rfl)
  letI : SMulCommClass S R ((restrictScalars σ).obj N) :=
    { smul_comm := fun s r n => by
        change s • (σ r • n) = σ r • (s • n)
        exact smul_comm s (σ r) n }
  exact (endRingEquiv ((restrictScalars σ).obj N)).symm.toRingHom.comp
    (Algebra.lsmul R R ((restrictScalars σ).obj N)).toRingHom

@[simp]
theorem extCoefficientRingHom_apply (N : ModuleCat.{v} S) (s : S) (n : N) :
    ((extCoefficientRingHom σ N s).asHom).hom n = s • n := rfl

variable [HasExt.{w} (ModuleCat.{v} R)]

/-- The coefficient `S`-action on native `R`-module Ext. -/
@[instance_reducible]
def extCoefficientModule (P : ModuleCat.{v} R) (N : ModuleCat.{v} S) (n : ℕ) :
    Module S (Abelian.Ext.{w} P ((restrictScalars σ).obj N) n) :=
  Abelian.Ext.coefficientModule (extCoefficientRingHom σ N) P n

/-- Coefficient scalar multiplication retains native Ext postcomposition. -/
theorem extCoefficient_smul_def (P : ModuleCat.{v} R) (N : ModuleCat.{v} S)
    (n : ℕ) (s : S) (x : Abelian.Ext.{w} P ((restrictScalars σ).obj N) n) :
    letI := extCoefficientModule σ P N n
    s • x = x.comp (Abelian.Ext.mk₀ (extCoefficientRingHom σ N s).asHom)
      (add_zero n) := rfl

/-- An `S`-linear coefficient map induces an `S`-linear map on native Ext over `R`. -/
def extCoefficientMap (P : ModuleCat.{v} R) {N N' : ModuleCat.{v} S}
    (f : N ⟶ N') (n : ℕ) :
    letI := extCoefficientModule σ P N n
    letI := extCoefficientModule σ P N' n
    Abelian.Ext.{w} P ((restrictScalars σ).obj N) n →ₗ[S]
      Abelian.Ext.{w} P ((restrictScalars σ).obj N') n :=
  Abelian.Ext.postcompOfCoefficientScalar
    (extCoefficientRingHom σ N) (extCoefficientRingHom σ N')
    ((restrictScalars σ).map f) (fun s => by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      change f.hom (s • x) = s • f.hom x
      exact f.hom.map_smul s x) P n

@[simp]
theorem extCoefficientMap_apply (P : ModuleCat.{v} R) {N N' : ModuleCat.{v} S}
    (f : N ⟶ N') (n : ℕ) (x : Abelian.Ext.{w} P ((restrictScalars σ).obj N) n) :
    extCoefficientMap σ P f n x =
      x.comp (Abelian.Ext.mk₀ ((restrictScalars σ).map f)) (add_zero n) := rfl

/-- The coefficient-map assignment is itself linear in the `S`-linear morphism. -/
def extCoefficientHomMap (P : ModuleCat.{v} R) (N N' : ModuleCat.{v} S) (n : ℕ) :
    letI := extCoefficientModule σ P N n
    letI := extCoefficientModule σ P N' n
    (N ⟶ N') →ₗ[S]
      (Abelian.Ext.{w} P ((restrictScalars σ).obj N) n →ₗ[S]
        Abelian.Ext.{w} P ((restrictScalars σ).obj N') n) := by
  letI := extCoefficientModule σ P N n
  letI := extCoefficientModule σ P N' n
  exact
    { toFun := fun f => extCoefficientMap σ P f n
      map_add' := fun f g => by
        apply LinearMap.ext
        intro x
        change x.comp (Abelian.Ext.mk₀ ((restrictScalars σ).map (f + g))) (add_zero n) = _
        simp only [Functor.map_add, Abelian.Ext.mk₀_add, Abelian.Ext.comp_add,
          LinearMap.add_apply, extCoefficientMap_apply]
      map_smul' := fun s f => by
        apply LinearMap.ext
        intro x
        change x.comp (Abelian.Ext.mk₀ ((restrictScalars σ).map (s • f))) (add_zero n) =
          (x.comp (Abelian.Ext.mk₀ ((restrictScalars σ).map f)) (add_zero n)).comp
            (Abelian.Ext.mk₀ (extCoefficientRingHom σ N' s).asHom) (add_zero n)
        have hmap : (restrictScalars σ).map (s • f) =
            (restrictScalars σ).map f ≫ (extCoefficientRingHom σ N' s).asHom := by
          apply ModuleCat.hom_ext
          apply LinearMap.ext
          intro y
          rfl
        rw [hmap, Abelian.Ext.comp_assoc_of_second_deg_zero,
          Abelian.Ext.mk₀_comp_mk₀] }

@[simp]
theorem extCoefficientHomMap_apply (P : ModuleCat.{v} R) (N N' : ModuleCat.{v} S)
    (n : ℕ) (f : N ⟶ N') (x : Abelian.Ext.{w} P ((restrictScalars σ).obj N) n) :
    extCoefficientHomMap σ P N N' n f x =
      x.comp (Abelian.Ext.mk₀ ((restrictScalars σ).map f)) (add_zero n) := rfl

/-- Native source precomposition preserves the coefficient action. -/
def extCoefficientPrecomp {P P' : ModuleCat.{v} R} (k : P' ⟶ P)
    (N : ModuleCat.{v} S) (n : ℕ) :
    letI := extCoefficientModule σ P N n
    letI := extCoefficientModule σ P' N n
    Abelian.Ext.{w} P ((restrictScalars σ).obj N) n →ₗ[S]
      Abelian.Ext.{w} P' ((restrictScalars σ).obj N) n :=
  Abelian.Ext.precompOfCoefficientScalar (extCoefficientRingHom σ N) k n

@[simp]
theorem extCoefficientPrecomp_apply {P P' : ModuleCat.{v} R} (k : P' ⟶ P)
    (N : ModuleCat.{v} S) (n : ℕ)
    (x : Abelian.Ext.{w} P ((restrictScalars σ).obj N) n) :
    extCoefficientPrecomp σ k N n x = (Abelian.Ext.mk₀ k).comp x (zero_add n) := rfl

/-- Restricted coefficient scalars agree with the native ground-ring action. -/
theorem extCoefficient_algebraMap_smul (P : ModuleCat.{v} R) (N : ModuleCat.{v} S)
    (n : ℕ) (r : R) (x : Abelian.Ext.{w} P ((restrictScalars σ).obj N) n) :
    letI := extCoefficientModule σ P N n
    (σ r) • x = r • x := by
  letI := extCoefficientModule σ P N n
  have hmap : (extCoefficientRingHom σ N (σ r)).asHom =
      r • 𝟙 ((restrictScalars σ).obj N) := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro y
    rfl
  rw [extCoefficient_smul_def σ P N n (σ r) x, hmap]
  exact (Abelian.Ext.smul_eq_comp_mk₀ x r).symm

end ModuleCat

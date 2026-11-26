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
# Scalar actions on Ext from coefficient endomorphisms

In an abelian category with Ext, a semiring map ρ : S → End(Y) defines an S-action on
Extⁿ(X,Y) by postcomposition: s·x = x composed with the degree-zero class of ρ(s).
Intertwining coefficient morphisms give S-linear postcomposition maps, while source
precomposition is S-linear for this same action.

The action is preserved by the canonical Ext carrier-universe equivalences under the stated
Ext and derived-category existence assumptions. For a map σ : R → S of commutative rings and
an S-module N, scalar multiplication on N gives the S-action on Ext_Rⁿ(P,N restricted to R).
The source P retains its R-module structure, and restriction of this action along σ is the
native R-action.
-/

@[expose] public section
noncomputable section

set_option autoImplicit false

open CategoryTheory

universe u v w w' wD s r

namespace CategoryTheory.Abelian.Ext

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]
  {S : Type s} [Semiring S]

/-- The scalar module structure on Ext induced by its coefficient.

For ρ : S → End(Y), define the S-module structure on Extⁿ(X,Y) by restricting its
coefficient-endomorphism action along ρ, with independent Ext, category and scalar universes. -/
@[instance_reducible]
def coefficientModule.{extU, homU, objU, scalarU}
    {C : Type objU} [Category.{homU} C] [Abelian C] [HasExt.{extU} C]
    {S : Type scalarU} [Semiring S] {Y : C} (ρ : S →+* End Y) (X : C) (n : ℕ) :
    Module S (Ext.{extU} X Y n) :=
  Module.compHom (Ext.{extU} X Y n) ρ

/-- The coefficient scalar action as degree-zero postcomposition.

The action is s·x = x.comp(mk₀(ρ(s)),n+0=n). -/
theorem coefficient_smul_def {X Y : C} (ρ : S →+* End Y) (n : ℕ)
    (s : S) (x : Ext.{w} X Y n) :
    letI := coefficientModule ρ X n
    s • x = x.comp (mk₀ (ρ s).asHom) (add_zero n) := rfl

/-- Linear postcomposition along an intertwining coefficient map.

If f : Y → Z intertwines the two S-endomorphism actions, postcomposition with mk₀(f) gives an
S-linear map Extⁿ(X,Y) → Extⁿ(X,Z). -/
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

/-- Values of the coefficient-linear postcomposition map.

The map sends x to its composite with the degree-zero class of f. -/
@[simp]
theorem postcompOfCoefficientScalar_apply {X Y Z : C}
    (ρY : S →+* End Y) (ρZ : S →+* End Z) (f : Y ⟶ Z)
    (hf : ∀ s, (ρY s).asHom ≫ f = f ≫ (ρZ s).asHom) (n : ℕ)
    (x : Ext.{w} X Y n) :
    postcompOfCoefficientScalar ρY ρZ f hf X n x =
      x.comp (mk₀ f) (add_zero n) := rfl

/-- Linear source precomposition for a coefficient scalar action.

For k : X′ → X, precomposition with mk₀(k) gives an S-linear map Extⁿ(X,Y) → Extⁿ(X′,Y). -/
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

/-- Values of the coefficient-linear source precomposition.

The map sends x to mk₀(k) composed with x. -/
@[simp]
theorem precompOfCoefficientScalar_apply {X X' Y : C}
    (ρ : S →+* End Y) (k : X' ⟶ X) (n : ℕ) (x : Ext.{w} X Y n) :
    precompOfCoefficientScalar ρ k n x = (mk₀ k).comp x (zero_add n) := rfl

/-- The coefficient-linear Ext universe comparison.

Under the stated Ext and derived-category existence hypotheses, the canonical comparison
between two Ext carrier universes is S-linear for the coefficient action ρ. -/
def coefficientSizeEquiv.{derivedU, sourceU, targetU, homU, objU, scalarU}
    {C : Type objU} [Category.{homU} C] [Abelian C]
    [HasExt.{sourceU} C] [HasExt.{targetU} C] [HasDerivedCategory.{derivedU} C]
    {S : Type scalarU} [Semiring S] {Y : C} (ρ : S →+* End Y) (X : C) (n : ℕ) :
    letI : Module S (Ext.{sourceU} X Y n) :=
      coefficientModule.{sourceU, homU, objU, scalarU} ρ X n
    letI : Module S (Ext.{targetU} X Y n) :=
      coefficientModule.{targetU, homU, objU, scalarU} ρ X n
    Ext.{sourceU} X Y n ≃ₗ[S] Ext.{targetU} X Y n := by
  letI : Module S (Ext.{sourceU} X Y n) :=
    coefficientModule.{sourceU, homU, objU, scalarU} ρ X n
  letI : Module S (Ext.{targetU} X Y n) :=
    coefficientModule.{targetU, homU, objU, scalarU} ρ X n
  refine
    { sizeEquiv.{derivedU, sourceU, targetU, homU, objU} X Y n with
      map_smul' := ?_ }
  intro s x
  change sizeEquiv.{derivedU, sourceU, targetU, homU, objU} X Y n
      (x.comp (mk₀ (ρ s).asHom) (add_zero n)) =
    (sizeEquiv.{derivedU, sourceU, targetU, homU, objU} X Y n x).comp
      (mk₀ (ρ s).asHom) (add_zero n)
  rw [sizeEquiv_comp, sizeEquiv_mk₀]

/-- The forward coefficient-linear universe comparison.

Its underlying function is the canonical Ext sizeEquiv from the source carrier universe to the
target. -/
@[simp]
theorem coefficientSizeEquiv_apply [HasExt.{w'} C] [HasDerivedCategory.{wD} C]
    {Y : C} (ρ : S →+* End Y) (X : C) (n : ℕ) (x : Ext.{w} X Y n) :
    (coefficientSizeEquiv.{wD, w, w', v, u, s} ρ X n x : Ext.{w'} X Y n) =
      sizeEquiv.{wD, w, w', v, u} X Y n x := rfl

/-- The inverse coefficient-linear universe comparison.

Its underlying inverse function is sizeEquiv with the two Ext carrier universes exchanged. -/
@[simp]
theorem coefficientSizeEquiv_symm_apply [HasExt.{w'} C] [HasDerivedCategory.{wD} C]
    {Y : C} (ρ : S →+* End Y) (X : C) (n : ℕ) (x : Ext.{w'} X Y n) :
    ((coefficientSizeEquiv.{wD, w, w', v, u, s} ρ X n).symm x : Ext.{w} X Y n) =
      sizeEquiv.{wD, w', w, v, u} X Y n x := rfl

end CategoryTheory.Abelian.Ext

namespace ModuleCat

variable {R : Type r} {S : Type s} [CommRing R] [CommRing S] (σ : R →+* S)

/-- Coefficient scalar endomorphisms after restriction of scalars.

For σ : R → S and an S-module N, multiplication by s is an R-linear endomorphism of N
restricted along σ, giving S → End_R(N). -/
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

/-- The coefficient endomorphism on an element.

The endomorphism associated to s ∈ S sends n ∈ N to s·n. -/
@[simp]
theorem extCoefficientRingHom_apply (N : ModuleCat.{v} S) (s : S) (n : N) :
    ((extCoefficientRingHom σ N s).asHom).hom n = s • n := rfl

variable [HasExt.{w} (ModuleCat.{v} R)]

/-- The coefficient S-module structure on Ext over R.

For an R-module P and S-module N, the scalar endomorphism map gives an S-module structure on
Ext_Rⁿ(P,res_σ N). -/
@[instance_reducible]
def extCoefficientModule (P : ModuleCat.{v} R) (N : ModuleCat.{v} S) (n : ℕ) :
    Module S (Abelian.Ext.{w} P ((restrictScalars σ).obj N) n) :=
  Abelian.Ext.coefficientModule (extCoefficientRingHom σ N) P n

/-- The S-action on module Ext as coefficient composition.

The action of s on an Ext class is postcomposition with the degree-zero class of
multiplication by s on the restricted coefficient module. -/
theorem extCoefficient_smul_def (P : ModuleCat.{v} R) (N : ModuleCat.{v} S)
    (n : ℕ) (s : S) (x : Abelian.Ext.{w} P ((restrictScalars σ).obj N) n) :
    letI := extCoefficientModule σ P N n
    s • x = x.comp (Abelian.Ext.mk₀ (extCoefficientRingHom σ N s).asHom)
      (add_zero n) := rfl

/-- The S-linear Ext map of an S-module coefficient morphism.

For f : N → N′ S-linear, its restricted R-map induces an S-linear postcomposition map on
Ext_Rⁿ(P,−). -/
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

/-- The coefficient morphism's map on an Ext class.

The map sends x to its composite with mk₀(res_σ f). -/
@[simp]
theorem extCoefficientMap_apply (P : ModuleCat.{v} R) {N N' : ModuleCat.{v} S}
    (f : N ⟶ N') (n : ℕ) (x : Abelian.Ext.{w} P ((restrictScalars σ).obj N) n) :
    extCoefficientMap σ P f n x =
      x.comp (Abelian.Ext.mk₀ ((restrictScalars σ).map f)) (add_zero n) := rfl

/-- Linearity of the Ext coefficient-map assignment.

The assignment f ↦ Ext_Rⁿ(P,res_σ f) is an S-linear map from the coefficient Hom module to
S-linear maps between the corresponding Ext modules. -/
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

/-- Values of the linear coefficient-map assignment.

Applying the assignment to f and then x gives x composed with mk₀(res_σ f). -/
@[simp]
theorem extCoefficientHomMap_apply (P : ModuleCat.{v} R) (N N' : ModuleCat.{v} S)
    (n : ℕ) (f : N ⟶ N') (x : Abelian.Ext.{w} P ((restrictScalars σ).obj N) n) :
    extCoefficientHomMap σ P N N' n f x =
      x.comp (Abelian.Ext.mk₀ ((restrictScalars σ).map f)) (add_zero n) := rfl

/-- The S-linear Ext map of an R-module source morphism.

For k : P′ → P, source precomposition gives an S-linear map Ext_Rⁿ(P,res N) → Ext_Rⁿ(P′,res
N). -/
def extCoefficientPrecomp {P P' : ModuleCat.{v} R} (k : P' ⟶ P)
    (N : ModuleCat.{v} S) (n : ℕ) :
    letI := extCoefficientModule σ P N n
    letI := extCoefficientModule σ P' N n
    Abelian.Ext.{w} P ((restrictScalars σ).obj N) n →ₗ[S]
      Abelian.Ext.{w} P' ((restrictScalars σ).obj N) n :=
  Abelian.Ext.precompOfCoefficientScalar (extCoefficientRingHom σ N) k n

/-- The source morphism's map on a coefficient-linear Ext class.

The map sends x to mk₀(k) composed with x. -/
@[simp]
theorem extCoefficientPrecomp_apply {P P' : ModuleCat.{v} R} (k : P' ⟶ P)
    (N : ModuleCat.{v} S) (n : ℕ)
    (x : Abelian.Ext.{w} P ((restrictScalars σ).obj N) n) :
    extCoefficientPrecomp σ k N n x = (Abelian.Ext.mk₀ k).comp x (zero_add n) := rfl

/-- The coefficient S-action restricts to the native R-action.

For r ∈ R, the scalar action of σ(r) on Ext_Rⁿ(P,res N) equals the R-scalar action of r. -/
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

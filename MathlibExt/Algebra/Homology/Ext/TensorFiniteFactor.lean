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

public import MathlibExt.Algebra.Homology.Ext.CoefficientScalar
public import MathlibExt.Algebra.Homology.SemilinearHomFunctor
public import MathlibExt.Algebra.Category.ModuleCat.TensorBifunctor.Exact
public import MathlibExt.CategoryTheory.Abelian.Ext.ProjectiveLinearComparison
public import MathlibExt.Algebra.Homology.Functor
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
public import Mathlib.Algebra.Category.ModuleCat.Ext.HasExt
public import Mathlib.RingTheory.Flat.Basic

/-!
# Finite projective coefficient tensor factors in Ext

Let `R → S` be a homomorphism of commutative rings, `P` an `R`-module, and
`N,U` `S`-modules. Tensoring an Ext class with `u : U` gives its native
postcomposition along `n ↦ n ⊗ u`. A finite projective `S`-module `U` makes
this comparison bijective in every degree.

The proof uses the Hom complex of a projective resolution over `R`. Its
terms have their coefficient `S`-actions, and the semilinear Hom comparison
is an isomorphism degree by degree. Tensoring over `S` is exact because `U`
is projective over `S`. The source module and the ring map are unrestricted.
-/

@[expose] public section
noncomputable section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct MonoidalCategory

universe r s v w p q t h

namespace ModuleCat

variable {R : Type r} {S : Type s} [CommRing R] [CommRing S] (σ : R →+* S)

section Comparison

variable [HasExt.{w} (ModuleCat.{v} R)]

/-- The canonical coefficient tensor comparison on native Ext over `R`. -/
def extTensorComparison (P : ModuleCat.{v} R) (N U : ModuleCat.{v} S) (n : ℕ) :
    letI := extCoefficientModule σ P N n
    letI := extCoefficientModule σ P (of S (N ⊗[S] U)) n
    Abelian.Ext.{w} P ((restrictScalars σ).obj N) n ⊗[S] U →ₗ[S]
      Abelian.Ext.{w} P ((restrictScalars σ).obj (of S (N ⊗[S] U))) n := by
  letI := extCoefficientModule σ P N n
  letI := extCoefficientModule σ P (of S (N ⊗[S] U)) n
  let c : U →ₗ[S] (N ⟶ of S (N ⊗[S] U)) :=
    (homLinearEquiv (M := N) (N := of S (N ⊗[S] U)) (S := S)).symm.toLinearMap.comp
      (TensorProduct.mk S N U).flip
  exact TensorProduct.lift ((extCoefficientHomMap σ P N (of S (N ⊗[S] U)) n).comp c).flip

/-- A pure tensor is native Ext postcomposition along the coefficient inclusion. -/
@[simp]
theorem extTensorComparison_tmul (P : ModuleCat.{v} R) (N U : ModuleCat.{v} S)
    (n : ℕ) (x : Abelian.Ext.{w} P ((restrictScalars σ).obj N) n) (u : U) :
    letI := extCoefficientModule σ P N n
    letI := extCoefficientModule σ P (of S (N ⊗[S] U)) n
    extTensorComparison σ P N U n (x ⊗ₜ[S] u) =
      x.comp (Abelian.Ext.mk₀ ((restrictScalars σ).map
        (ofHom ((TensorProduct.mk S N U).flip u)))) (add_zero n) := rfl

end Comparison

namespace ExtTensorFactor

/-- The shared semilinear Hom functor applied to the actual `R`-projective resolution. -/
private abbrev coefficientYonedaComplex {P : ModuleCat.{v} R}
    (Q : ProjectiveResolution P) (N : ModuleCat.{v} S) :
    CochainComplex (ModuleCat.{v} S) ℕ :=
  (semilinearHomSourceComplexFunctor σ N (ComplexShape.down ℕ)).obj
    (Opposite.op Q.complex)

/-- The shared finite-factor comparison specialized to that resolution. -/
private def coefficientYonedaTensorIso {P : ModuleCat.{v} R}
    (Q : ProjectiveResolution P) (N U : ModuleCat.{v} S)
    [Module.Finite S U] [Module.Projective S U] :
    (((tensorBifunctorAt.{s, v, v} S).flip.obj U).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj (coefficientYonedaComplex σ Q N) ≅
      coefficientYonedaComplex σ Q (of S (N ⊗[S] U)) :=
  (semilinearHomSourceComplexTensorIso σ N U (ComplexShape.down ℕ)).app
    (Opposite.op Q.complex)

private instance tensorFactorPreservesHomology (U : ModuleCat.{v} S)
    [Module.Projective S U] :
    ((tensorBifunctorAt.{s, v, v} S).flip.obj U).PreservesHomology :=
  tensorBifunctorAt_flip_obj_preservesHomology S U

section Resolution

variable [HasExt.{v} (ModuleCat.{v} R)] {P : ModuleCat.{v} R}
  (Q : ProjectiveResolution P) (N : ModuleCat.{v} S) (n : ℕ)

/-- A semilinear cocycle, read through the native restricted-Hom equivalence. -/
private def coefficientCocycleToNative
    (f : (((coefficientYonedaComplex σ Q N).sc n).g.hom).ker) :
    (((Q.linearYonedaComplex R ((restrictScalars σ).obj N)).sc n).g.hom).ker := by
  refine ⟨semilinearMapLinearEquiv σ (Q.complex.X n) N f.val, ?_⟩
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  have hf := congrArg
    (fun g : Q.complex.X ((ComplexShape.up ℕ).next n) →ₛₗ[σ] N => g x) f.property
  change f.val ((Q.complex.d ((ComplexShape.up ℕ).next n) n).hom x) = 0 at hf ⊢
  exact hf

/-- The existing native Ext class projection is linear for coefficient scalars. -/
private def coefficientCocyclesToExt :
    letI : Module S (Abelian.Ext.{v} P ((restrictScalars σ).obj N) n) :=
      extCoefficientModule σ P N n
    (((coefficientYonedaComplex σ Q N).sc n).g.hom).ker →ₗ[S]
      Abelian.Ext.{v} P ((restrictScalars σ).obj N) n := by
  letI : Module S (Abelian.Ext.{v} P ((restrictScalars σ).obj N) n) :=
    extCoefficientModule σ P N n
  exact
    { toFun := fun f => Q.linearYonedaCocyclesToExt R ((restrictScalars σ).obj N) n
        (coefficientCocycleToNative σ Q N n f)
      map_add' := fun f g => by
        have h : coefficientCocycleToNative σ Q N n (f + g) =
            coefficientCocycleToNative σ Q N n f + coefficientCocycleToNative σ Q N n g :=
          Subtype.ext ((semilinearMapLinearEquiv σ (Q.complex.X n) N).map_add f.val g.val)
        change Q.linearYonedaCocyclesToExt R ((restrictScalars σ).obj N) n
            (coefficientCocycleToNative σ Q N n (f + g)) = _
        rw [h]
        exact (Q.linearYonedaCocyclesToExt R ((restrictScalars σ).obj N) n).map_add
          (coefficientCocycleToNative σ Q N n f) (coefficientCocycleToNative σ Q N n g)
      map_smul' := fun s f => by
        let f₀ := coefficientCocycleToNative σ Q N n f
        let sf₀ := coefficientCocycleToNative σ Q N n (s • f)
        change Q.extMk sf₀.val (n + 1) rfl _ =
          (Q.extMk f₀.val (n + 1) rfl _).comp
            (Abelian.Ext.mk₀ (extCoefficientRingHom σ N s).asHom) (add_zero n)
        have hval : f₀.val ≫ (extCoefficientRingHom σ N s).asHom = sf₀.val := by
          apply ModuleCat.hom_ext
          apply LinearMap.ext
          intro x
          rfl
        have he := Q.extMk_comp_mk₀ f₀.val (n + 1) rfl
          (Q.linearYonedaCocycle_closed R ((restrictScalars σ).obj N) n f₀)
          (extCoefficientRingHom σ N s).asHom
        rw [hval] at he
        exact he.symm }

private theorem coefficientCocyclesToExt_exact :
    letI : Module S (Abelian.Ext.{v} P ((restrictScalars σ).obj N) n) :=
      extCoefficientModule σ P N n
    Function.Exact ((coefficientYonedaComplex σ Q N).sc n).moduleCatToCycles
      (coefficientCocyclesToExt σ Q N n) := by
  letI : Module S (Abelian.Ext.{v} P ((restrictScalars σ).obj N) n) :=
    extCoefficientModule σ P N n
  intro f
  constructor
  · intro hf
    obtain ⟨g, hg⟩ :=
      (Q.linearYonedaCocyclesToExt_exact R ((restrictScalars σ).obj N) n
        (coefficientCocycleToNative σ Q N n f)).mp hf
    let g₀ : Q.complex.X ((ComplexShape.up ℕ).prev n) ⟶ (restrictScalars σ).obj N := g
    refine ⟨(semilinearMapLinearEquiv σ
      (Q.complex.X ((ComplexShape.up ℕ).prev n)) N).symm g₀, Subtype.ext ?_⟩
    apply LinearMap.ext
    intro x
    have hx := congrArg (fun k : Q.complex.X n ⟶ (restrictScalars σ).obj N => k.hom x)
      (congrArg Subtype.val hg)
    change g₀.hom ((Q.complex.d n ((ComplexShape.up ℕ).prev n)).hom x) = f.val x at hx ⊢
    exact hx
  · rintro ⟨g, rfl⟩
    let g₀ : Q.complex.X ((ComplexShape.up ℕ).prev n) ⟶ (restrictScalars σ).obj N :=
      semilinearMapLinearEquiv σ (Q.complex.X ((ComplexShape.up ℕ).prev n)) N g
    have h : coefficientCocycleToNative σ Q N n
          (((coefficientYonedaComplex σ Q N).sc n).moduleCatToCycles g) =
        ((Q.linearYonedaComplex R ((restrictScalars σ).obj N)).sc n).moduleCatToCycles g₀ := by
      apply Subtype.ext
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      rfl
    change Q.linearYonedaCocyclesToExt R ((restrictScalars σ).obj N) n
      (coefficientCocycleToNative σ Q N n
        (((coefficientYonedaComplex σ Q N).sc n).moduleCatToCycles g)) = 0
    rw [h]
    exact (Q.linearYonedaCocyclesToExt_exact R
      ((restrictScalars σ).obj N) n).apply_apply_eq_zero g₀

private theorem coefficientCocyclesToExt_surjective :
    letI : Module S (Abelian.Ext.{v} P ((restrictScalars σ).obj N) n) :=
      extCoefficientModule σ P N n
    Function.Surjective (coefficientCocyclesToExt σ Q N n) := by
  letI : Module S (Abelian.Ext.{v} P ((restrictScalars σ).obj N) n) :=
    extCoefficientModule σ P N n
  intro x
  obtain ⟨f, hf⟩ :=
    Q.linearYonedaCocyclesToExt_surjective R ((restrictScalars σ).obj N) n x
  let f' : (((coefficientYonedaComplex σ Q N).sc n).g.hom).ker :=
    ⟨(semilinearMapLinearEquiv σ (Q.complex.X n) N).symm f.val, by
      apply LinearMap.ext
      intro y
      have h := congrArg
        (fun g : Q.complex.X ((ComplexShape.up ℕ).next n) ⟶ (restrictScalars σ).obj N =>
          g.hom y) f.property
      change f.val.hom ((Q.complex.d ((ComplexShape.up ℕ).next n) n).hom y) = 0 at h ⊢
      exact h⟩
  refine ⟨f', ?_⟩
  have h : coefficientCocycleToNative σ Q N n f' = f :=
    Subtype.ext ((semilinearMapLinearEquiv σ (Q.complex.X n) N).apply_symm_apply f.val)
  change Q.linearYonedaCocyclesToExt R ((restrictScalars σ).obj N) n
    (coefficientCocycleToNative σ Q N n f') = x
  rw [h]
  exact hf

/-- Native kernel/cokernel data with the existing Ext projection and its coefficient action. -/
private def coefficientExtHomologyData :
    letI : Module S (Abelian.Ext.{v} P ((restrictScalars σ).obj N) n) :=
      extCoefficientModule σ P N n
    ((coefficientYonedaComplex σ Q N).sc n).LeftHomologyData := by
  letI : Module S (Abelian.Ext.{v} P ((restrictScalars σ).obj N) n) :=
    extCoefficientModule σ P N n
  let C := (coefficientYonedaComplex σ Q N).sc n
  exact
    { K := C.moduleCatLeftHomologyData.K
      H := of S (Abelian.Ext.{v} P ((restrictScalars σ).obj N) n)
      i := C.moduleCatLeftHomologyData.i
      π := ofHom (coefficientCocyclesToExt σ Q N n)
      wi := C.moduleCatLeftHomologyData.wi
      hi := C.moduleCatLeftHomologyData.hi
      wπ := by
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro f
        exact (coefficientCocyclesToExt_exact σ Q N n).apply_apply_eq_zero f
      hπ := ModuleCat.isColimitCokernelCofork (ofHom C.moduleCatToCycles)
        (ofHom (coefficientCocyclesToExt σ Q N n))
        (coefficientCocyclesToExt_exact σ Q N n)
        (coefficientCocyclesToExt_surjective σ Q N n) }

private def tensorExtHomologyMapData (U : ModuleCat.{v} S)
    [Module.Finite S U] [Module.Projective S U] :
    letI : Module S (Abelian.Ext.{v} P ((restrictScalars σ).obj N) n) :=
      extCoefficientModule σ P N n
    letI : Module S (Abelian.Ext.{v} P
        ((restrictScalars σ).obj (of S (N ⊗[S] U))) n) :=
      extCoefficientModule σ P (of S (N ⊗[S] U)) n
    ShortComplex.LeftHomologyMapData
      ((HomologicalComplex.shortComplexFunctor (ModuleCat.{v} S) (ComplexShape.up ℕ) n).map
        (coefficientYonedaTensorIso σ Q N U).hom)
      ((coefficientExtHomologyData σ Q N n).map ((tensorBifunctorAt.{s, v, v} S).flip.obj U))
      (coefficientExtHomologyData σ Q (of S (N ⊗[S] U)) n) := by
  letI : Module S (Abelian.Ext.{v} P ((restrictScalars σ).obj N) n) :=
    extCoefficientModule σ P N n
  letI : Module S (Abelian.Ext.{v} P
      ((restrictScalars σ).obj (of S (N ⊗[S] U))) n) :=
    extCoefficientModule σ P (of S (N ⊗[S] U)) n
  let ψ := (HomologicalComplex.shortComplexFunctor (ModuleCat.{v} S)
    (ComplexShape.up ℕ) n).map (coefficientYonedaTensorIso σ Q N U).hom
  let h₁ := (coefficientExtHomologyData σ Q N n).map ((tensorBifunctorAt.{s, v, v} S).flip.obj U)
  let h₂ := coefficientExtHomologyData σ Q (of S (N ⊗[S] U)) n
  let γ : ShortComplex.LeftHomologyMapData ψ h₁ h₂ := default
  refine
    { φK := γ.φK
      φH := ofHom (show Abelian.Ext.{v} P ((restrictScalars σ).obj N) n ⊗[S] U →ₗ[S]
          Abelian.Ext.{v} P ((restrictScalars σ).obj (of S (N ⊗[S] U))) n from
        extTensorComparison σ P N U n)
      commi := γ.commi
      commf' := γ.commf'
      commπ := ?_ }
  apply ModuleCat.hom_ext
  apply TensorProduct.ext'
  intro f u
  let f₀ := coefficientCocycleToNative σ Q N n f
  let g₀ := coefficientCocycleToNative σ Q (of S (N ⊗[S] U)) n
    (γ.φK.hom (f ⊗ₜ[S] u))
  have hval : g₀.val = f₀.val ≫ (restrictScalars σ).map
      (ofHom ((TensorProduct.mk S N U).flip u)) := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    have hx := congrArg (fun a : h₁.K ⟶
        ((coefficientYonedaComplex σ Q (of S (N ⊗[S] U))).sc n).X₂ =>
      (a.hom (f ⊗ₜ[S] u)) x) γ.commi
    change (γ.φK.hom (f ⊗ₜ[S] u)).val x = f.val x ⊗ₜ[S] u at hx ⊢
    exact hx
  change (Q.extMk f₀.val (n + 1) rfl _).comp
      (Abelian.Ext.mk₀ ((restrictScalars σ).map
        (ofHom ((TensorProduct.mk S N U).flip u)))) (add_zero n) =
    Q.extMk g₀.val (n + 1) rfl _
  rw [hval]
  exact Q.extMk_comp_mk₀ f₀.val (n + 1) rfl
    (Q.linearYonedaCocycle_closed R ((restrictScalars σ).obj N) n f₀)
    ((restrictScalars σ).map (ofHom ((TensorProduct.mk S N U).flip u)))

private theorem comparison_bijective_of_resolution (U : ModuleCat.{v} S)
    [Module.Finite S U] [Module.Projective S U] :
    letI : Module S (Abelian.Ext.{v} P ((restrictScalars σ).obj N) n) :=
      extCoefficientModule σ P N n
    letI : Module S (Abelian.Ext.{v} P
        ((restrictScalars σ).obj (of S (N ⊗[S] U))) n) :=
      extCoefficientModule σ P (of S (N ⊗[S] U)) n
    Function.Bijective (show Abelian.Ext.{v} P ((restrictScalars σ).obj N) n ⊗[S] U →ₗ[S]
        Abelian.Ext.{v} P ((restrictScalars σ).obj (of S (N ⊗[S] U))) n from
      extTensorComparison σ P N U n) := by
  letI : Module S (Abelian.Ext.{v} P ((restrictScalars σ).obj N) n) :=
    extCoefficientModule σ P N n
  letI : Module S (Abelian.Ext.{v} P
      ((restrictScalars σ).obj (of S (N ⊗[S] U))) n) :=
    extCoefficientModule σ P (of S (N ⊗[S] U)) n
  let T : ModuleCat.{v} S ⥤ ModuleCat.{v} S := (tensorBifunctorAt.{s, v, v} S).flip.obj U
  let K := coefficientYonedaComplex σ Q N
  let h₁ := coefficientExtHomologyData σ Q N n
  let h₂ := coefficientExtHomologyData σ Q (of S (N ⊗[S] U)) n
  let κ : Abelian.Ext.{v} P ((restrictScalars σ).obj N) n ⊗[S] U →ₗ[S]
      Abelian.Ext.{v} P ((restrictScalars σ).obj (of S (N ⊗[S] U))) n :=
    extTensorComparison σ P N U n
  let a := (HomologicalComplex.mapHomologyFunctorIso (c := ComplexShape.up ℕ) n T).app K ≪≫
    T.mapIso h₁.homologyIso
  let b := (HomologicalComplex.homologyFunctor (ModuleCat.{v} S)
    (ComplexShape.up ℕ) n).mapIso (coefficientYonedaTensorIso σ Q N U)
  let e := a.symm ≪≫ b ≪≫ h₂.homologyIso
  have ha : a = (h₁.map T).homologyIso := by
    change (K.sc n).mapHomologyIso T ≪≫ T.mapIso h₁.homologyIso = (h₁.map T).homologyIso
    rw [h₁.mapHomologyIso_eq T]
    apply Iso.ext
    simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, Category.assoc,
      ← T.map_comp, Iso.inv_hom_id, Functor.map_id, Category.comp_id]
  have he : e.hom = ofHom κ := by
    change a.inv ≫ b.hom ≫ h₂.homologyIso.hom = ofHom κ
    rw [ha]
    apply (cancel_epi (h₁.map T).homologyIso.hom).1
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
    exact (tensorExtHomologyMapData σ Q N n U).homologyMap_comm
  have hκ : e.toLinearEquiv.toLinearMap = κ := by
    change e.hom.hom = κ
    exact congrArg ModuleCat.Hom.hom he
  rw [← hκ]
  exact e.toLinearEquiv.bijective

end Resolution

end ExtTensorFactor

section FiniteFactor

variable [EnoughProjectives (ModuleCat.{v} R)] [HasExt.{w} (ModuleCat.{v} R)]

/-- A finite projective `S`-module tensor factor makes native `R`-module Ext
postcomposition bijective, in an independent Ext carrier universe. -/
theorem extTensorComparison_bijective (P : ModuleCat.{v} R) (N U : ModuleCat.{v} S)
    [Module.Finite S U] [Module.Projective S U] (n : ℕ) :
    letI := extCoefficientModule σ P N n
    letI := extCoefficientModule σ P (of S (N ⊗[S] U)) n
    Function.Bijective (extTensorComparison σ P N U n) := by
  letI : HasExt.{v} (ModuleCat.{v} R) := hasExt_of_enoughProjectives (ModuleCat.{v} R)
  letI := HasDerivedCategory.standard (ModuleCat.{v} R)
  letI : Module S (Abelian.Ext.{w} P ((restrictScalars σ).obj N) n) :=
    extCoefficientModule σ P N n
  letI : Module S (Abelian.Ext.{v} P ((restrictScalars σ).obj N) n) :=
    extCoefficientModule σ P N n
  letI : Module S (Abelian.Ext.{w} P
      ((restrictScalars σ).obj (of S (N ⊗[S] U))) n) :=
    extCoefficientModule σ P (of S (N ⊗[S] U)) n
  letI : Module S (Abelian.Ext.{v} P
      ((restrictScalars σ).obj (of S (N ⊗[S] U))) n) :=
    extCoefficientModule σ P (of S (N ⊗[S] U)) n
  let a : Abelian.Ext.{w} P ((restrictScalars σ).obj N) n ≃ₗ[S]
      Abelian.Ext.{v} P ((restrictScalars σ).obj N) n :=
    Abelian.Ext.coefficientSizeEquiv (extCoefficientRingHom σ N) P n
  let b : Abelian.Ext.{w} P ((restrictScalars σ).obj (of S (N ⊗[S] U))) n ≃ₗ[S]
      Abelian.Ext.{v} P ((restrictScalars σ).obj (of S (N ⊗[S] U))) n :=
    Abelian.Ext.coefficientSizeEquiv (extCoefficientRingHom σ (of S (N ⊗[S] U))) P n
  let c : Abelian.Ext.{v} P ((restrictScalars σ).obj N) n ⊗[S] U ≃ₗ[S]
      Abelian.Ext.{v} P ((restrictScalars σ).obj (of S (N ⊗[S] U))) n :=
    LinearEquiv.ofBijective (extTensorComparison σ P N U n)
      (ExtTensorFactor.comparison_bijective_of_resolution σ (projectiveResolution P) N n U)
  let e : Abelian.Ext.{w} P ((restrictScalars σ).obj N) n ⊗[S] U ≃ₗ[S]
      Abelian.Ext.{w} P ((restrictScalars σ).obj (of S (N ⊗[S] U))) n :=
    TensorProduct.congr a (LinearEquiv.refl S U) ≪≫ₗ c ≪≫ₗ b.symm
  have he : e.toLinearMap = extTensorComparison σ P N U n := by
    apply TensorProduct.ext'
    intro x u
    change b.symm ((a x).comp (Abelian.Ext.mk₀ ((restrictScalars σ).map
        (ofHom ((TensorProduct.mk S N U).flip u)))) (add_zero n)) =
      x.comp (Abelian.Ext.mk₀ ((restrictScalars σ).map
        (ofHom ((TensorProduct.mk S N U).flip u)))) (add_zero n)
    rw [Abelian.Ext.coefficientSizeEquiv_symm_apply, Abelian.Ext.sizeEquiv_comp,
      Abelian.Ext.sizeEquiv_mk₀]
    change (a.symm (a x)).comp (Abelian.Ext.mk₀ ((restrictScalars σ).map
        (ofHom ((TensorProduct.mk S N U).flip u)))) (add_zero n) = _
    rw [LinearEquiv.symm_apply_apply]
  rw [← he]
  exact e.bijective

/-- Native Ext with an arbitrary `R`-module source commutes with a finite
projective coefficient tensor factor over `S`. -/
def extTensorFiniteFactorEquiv (P : ModuleCat.{v} R) (N U : ModuleCat.{v} S)
    [Module.Finite S U] [Module.Projective S U] (n : ℕ) :
    letI := extCoefficientModule σ P N n
    letI := extCoefficientModule σ P (of S (N ⊗[S] U)) n
    Abelian.Ext.{w} P ((restrictScalars σ).obj N) n ⊗[S] U ≃ₗ[S]
      Abelian.Ext.{w} P ((restrictScalars σ).obj (of S (N ⊗[S] U))) n :=
  LinearEquiv.ofBijective (extTensorComparison σ P N U n)
    (extTensorComparison_bijective σ P N U n)

@[simp]
theorem extTensorFiniteFactorEquiv_toLinearMap (P : ModuleCat.{v} R) (N U : ModuleCat.{v} S)
    [Module.Finite S U] [Module.Projective S U] (n : ℕ) :
    letI := extCoefficientModule σ P N n
    letI := extCoefficientModule σ P (of S (N ⊗[S] U)) n
    (extTensorFiniteFactorEquiv σ P N U n).toLinearMap =
      extTensorComparison σ P N U n := rfl

@[simp]
theorem extTensorFiniteFactorEquiv_tmul (P : ModuleCat.{v} R) (N U : ModuleCat.{v} S)
    [Module.Finite S U] [Module.Projective S U] (n : ℕ)
    (x : Abelian.Ext.{w} P ((restrictScalars σ).obj N) n) (u : U) :
    letI := extCoefficientModule σ P N n
    letI := extCoefficientModule σ P (of S (N ⊗[S] U)) n
    extTensorFiniteFactorEquiv σ P N U n (x ⊗ₜ[S] u) =
      x.comp (Abelian.Ext.mk₀ ((restrictScalars σ).map
        (ofHom ((TensorProduct.mk S N U).flip u)))) (add_zero n) := rfl

end FiniteFactor

/-- The coefficient tensor comparison at any common lift height, with
independent original module carriers and independent Ext carrier universe. -/
def extTensorFiniteFactorEquivAt.{h, r, s, p, q, t, w}
    {R : Type r} {S : Type s} [CommRing R] [CommRing S] (σ : R →+* S)
    (P : Type p) [AddCommGroup P] [Module R P]
    (N : Type q) [AddCommGroup N] [Module S N]
    (U : Type t) [AddCommGroup U] [Module S U]
    [Module.Finite S U] [Module.Projective S U]
    [HasExt.{w} (ModuleCat.{max h r s p q t} R)] (n : ℕ) :
    let P' := of R (ULift.{max h r s p q t} P)
    let N' := of S (ULift.{max h r s p q t} N)
    let U' := of S (ULift.{max h r s p q t} U)
    letI := extCoefficientModule σ P' N' n
    letI := extCoefficientModule σ P' (of S (N' ⊗[S] U')) n
    Abelian.Ext.{w} P' ((restrictScalars σ).obj N') n ⊗[S] U' ≃ₗ[S]
      Abelian.Ext.{w} P' ((restrictScalars σ).obj (of S (N' ⊗[S] U'))) n := by
  let P' := of R (ULift.{max h r s p q t} P)
  let N' := of S (ULift.{max h r s p q t} N)
  let U' := of S (ULift.{max h r s p q t} U)
  exact extTensorFiniteFactorEquiv σ P' N' U' n

end ModuleCat

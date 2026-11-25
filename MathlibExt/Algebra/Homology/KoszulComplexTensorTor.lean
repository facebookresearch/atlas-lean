/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.Algebra.Homology.KoszulComplexRegularResolution
public import MathlibExt.Algebra.Homology.KoszulComplexFamilyBaseChange
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
public import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
public import MathlibExt.Algebra.Category.ModuleCat.UliftCoherenceSelf

/-!
# Tensor coefficients and Tor of regular Koszul quotients

Tensoring the regular resolution gives the scalar-extended Koszul complex.
Base-change maps and the universe-lift equivalence identify it with the
Koszul complex on the mapped coefficients. Exact scalar restriction then
identifies its homology with Tor.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped TensorProduct

namespace KoszulComplex

universe u

variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]

/-- Remove the canonical augmentation-independent target lift from the
existing actual finite-family scalar-extension isomorphism. -/
def familyBaseChangeUnliftIso {n : ℕ} (a : Fin n → R) :
    baseChangeComplex R S (Fin n → R) (familyFunctional R a) ≅
      familyComplex S (mappedFamily R S a) :=
  familyBaseChangeIso R S a ≪≫
    (NatIso.mapHomologicalComplex (ModuleCat.uliftFunctorSelfIso.{u, 0} S)
      (ComplexShape.down ℕ)).app
      (familyComplex S (mappedFamily R S a)) ≪≫
    (Functor.mapHomologicalComplexIdIso (ModuleCat.{u} S) (ComplexShape.down ℕ)).app
      (familyComplex S (mappedFamily R S a))

/-- The actual scalar-extension tensor module, restricted to R, is the
original R-tensor module. Both maps are literal identity maps on tensors. -/
def tensorModuleRestrictionIso (M : Type u) [AddCommGroup M] [Module R M] :
    ModuleCat.of R (S ⊗[R] M) ≅
      (ModuleCat.restrictScalars.{u} (algebraMap R S)).obj
        (ModuleCat.of S (S ⊗[R] M)) := by
  let f : (ModuleCat.of R (S ⊗[R] M)) →ₗ[R]
      ((ModuleCat.restrictScalars (algebraMap R S)).obj (ModuleCat.of S (S ⊗[R] M))) :=
    { toFun := fun x => x
      map_add' := fun _ _ => rfl
      map_smul' := fun r x => by
        change r • x = algebraMap R S r • x
        exact (IsScalarTower.algebraMap_smul S r x).symm }
  have hf : Function.Bijective f := by
    constructor
    · intro x y h; exact h
    · intro y; exact ⟨y, rfl⟩
  exact (LinearEquiv.ofBijective f hf).toModuleIso

/-- The actual identity on tensor values, linear for the original
restriction-of-scalars action in both directions. -/
def tensorFamilyBaseChangeComponentIso {n : ℕ} (a : Fin n → R) (j : ℕ) :
    ((((tensoringLeft (ModuleCat.{u} R)).obj (ModuleCat.of R S)).mapHomologicalComplex
      (ComplexShape.down ℕ)).obj (familyComplex R a)).X j ≅
        (((ModuleCat.restrictScalars.{u} (algebraMap R S)).mapHomologicalComplex
          (ComplexShape.down ℕ)).obj
            (baseChangeComplex R S (Fin n → R) (familyFunctional R a))).X j :=
  eqToIso (by rfl) ≪≫ tensorModuleRestrictionIso R S (⋀[R]^j (Fin n → R)) ≪≫
    (ModuleCat.restrictScalars (algebraMap R S)).mapIso
      (eqToIso (baseChangeComplex_X R S (Fin n → R) (familyFunctional R a) j)).symm

/-- The forward coefficient comparison is literally the identity on
the original tensor values. -/
theorem tensorFamilyBaseChangeComponentIso_hom_apply
    {n : ℕ} (a : Fin n → R) (j : ℕ)
    (x : ((((tensoringLeft (ModuleCat.{u} R)).obj (ModuleCat.of R S)).mapHomologicalComplex
      (ComplexShape.down ℕ)).obj (familyComplex R a)).X j) :
    (tensorFamilyBaseChangeComponentIso R S a j).hom x = x := rfl

/-- The original native tensor complex and the restriction of the actual
scalar-extension complex have the same original tensor terms and maps. -/
def tensorFamilyComplexIsoRestrictedBaseChange {n : ℕ} (a : Fin n → R) :
    (((tensoringLeft (ModuleCat.{u} R)).obj (ModuleCat.of R S)).mapHomologicalComplex
      (ComplexShape.down ℕ)).obj (familyComplex R a) ≅
        ((ModuleCat.restrictScalars.{u} (algebraMap R S)).mapHomologicalComplex
          (ComplexShape.down ℕ)).obj
            (baseChangeComplex R S (Fin n → R) (familyFunctional R a)) :=
  HomologicalComplex.Hom.isoOfComponents (tensorFamilyBaseChangeComponentIso R S a)
    (fun i j hij => by
      change j + 1 = i at hij
      subst i
      change
        (tensorFamilyBaseChangeComponentIso R S a (j + 1)).hom ≫
          (ModuleCat.restrictScalars (algebraMap R S)).map
            ((baseChangeComplex R S (Fin n → R) (familyFunctional R a)).d (j + 1) j) =
        (((tensoringLeft (ModuleCat.{u} R)).obj (ModuleCat.of R S)).map
          ((complex R (Fin n → R) (familyFunctional R a)).d (j + 1) j)) ≫
            (tensorFamilyBaseChangeComponentIso R S a j).hom
      rw [baseChangeComplex_d_succ, complex_d_succ]
      apply ModuleCat.hom_ext
      apply TensorProduct.ext
      apply LinearMap.ext
      intro s
      apply LinearMap.ext
      intro m
      change
        ((tensorFamilyBaseChangeComponentIso R S a (j + 1)).hom ≫
          (ModuleCat.restrictScalars (algebraMap R S)).map
            (ModuleCat.ofHom
              ((differential R (Fin n → R) (familyFunctional R a) j).baseChange S)))
            (s ⊗ₜ[R] m) =
        ((((tensoringLeft (ModuleCat.{u} R)).obj (ModuleCat.of R S)).map
          (ModuleCat.ofHom (differential R (Fin n → R) (familyFunctional R a) j))) ≫
            (tensorFamilyBaseChangeComponentIso R S a j).hom) (s ⊗ₜ[R] m)
      simp only [ConcreteCategory.comp_apply, tensorFamilyBaseChangeComponentIso_hom_apply]
      let s₀ : S := s
      let m₀ : ⋀[R]^(j + 1) (Fin n → R) := m
      change (differential R (Fin n → R) (familyFunctional R a) j).baseChange S
        (s₀ ⊗ₜ[R] m₀) = s₀ ⊗ₜ[R] differential R (Fin n → R) (familyFunctional R a) j m₀
      exact LinearMap.baseChange_tmul
        (differential R (Fin n → R) (familyFunctional R a) j) s₀ m₀)

/-- The actual native tensor complex is isomorphic to the restriction of
the original Koszul complex on the mapped coefficient family. -/
def tensorFamilyComplexIsoRestrictedMappedFamily {n : ℕ} (a : Fin n → R) :
    (((tensoringLeft (ModuleCat.{u} R)).obj (ModuleCat.of R S)).mapHomologicalComplex
      (ComplexShape.down ℕ)).obj (familyComplex R a) ≅
        ((ModuleCat.restrictScalars.{u} (algebraMap R S)).mapHomologicalComplex
          (ComplexShape.down ℕ)).obj (familyComplex S (mappedFamily R S a)) :=
  tensorFamilyComplexIsoRestrictedBaseChange R S a ≪≫
    ((ModuleCat.restrictScalars.{u} (algebraMap R S)).mapHomologicalComplex
      (ComplexShape.down ℕ)).mapIso (familyBaseChangeUnliftIso R S a)

/-- The exact restriction-of-scalars functor commutes with homology. -/
def restrictedComplexHomologyIso
    (K : ChainComplex (ModuleCat.{u} S) ℕ) (q : ℕ) :
    (((ModuleCat.restrictScalars.{u} (algebraMap R S)).mapHomologicalComplex
      (ComplexShape.down ℕ)).obj K).homology q ≅
        (ModuleCat.restrictScalars.{u} (algebraMap R S)).obj (K.homology q) :=
  (K.sc q).mapHomologyIso (ModuleCat.restrictScalars.{u} (algebraMap R S))

/-- Every native Tor group of the original regular quotient is computed
by the genuine Koszul homology of the original mapped coefficients. -/
def regularFiniteFamilyTorIsoMappedHomology
    {n : ℕ} (a : Fin n → R)
    (ha : RingTheory.Sequence.IsWeaklyRegular R (List.ofFn a)) (q : ℕ) :
    (((Tor (ModuleCat.{u} R) q).obj (ModuleCat.of R S)).obj
      (ModuleCat.of R (R ⧸ ideal R (Fin n → R) (familyFunctional R a)))) ≅
        (ModuleCat.restrictScalars.{u} (algebraMap R S)).obj
          ((familyComplex S (mappedFamily R S a)).homology q) :=
  (regularFiniteFamilyTensorHomologyIsoTorQuotient R a ha (ModuleCat.of R S) q).symm ≪≫
    (HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (ComplexShape.down ℕ) q).mapIso
      (tensorFamilyComplexIsoRestrictedMappedFamily R S a) ≪≫
        restrictedComplexHomologyIso R S (familyComplex S (mappedFamily R S a)) q

end KoszulComplex

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
# Tensor coefficients and Tor of weakly regular Koszul quotients

Let R,S be commutative rings in universe u and S an R-algebra. For a finite family a:Fin n→R,
the Koszul complex K_R(a) has degree-j term Λ^j_R(R^n) and differential contraction by the
functional sending the ith basis vector to a_i. On a decomposable wedge the differential deletes
the tth factor with coefficient (-1)^t a_{i_t}, using positions numbered from zero. Scalar
extension identifies S⊗_R K_R(a) with K_S(algebraMap∘a), and scalar restriction compares these
complexes as R-complexes.

If the ordered family a is weakly regular over R, meaning each a_i acts injectively on the
quotient by its predecessors, K_R(a) resolves R/(a). Thus Tor_q^R(S,R/(a)) is canonically the
R-restriction of H_q(K_S(algebraMap∘a)) for every q∈ℕ. The coefficient algebra S need not be
flat, and no weak regularity of the mapped S-family is assumed.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped TensorProduct

namespace KoszulComplex

universe u

variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]

/-- Let R,S be commutative rings and S an R-algebra, all in universe u. For a family a:Fin n→R, this
S-linear chain isomorphism identifies the scalar-extension complex with degree-j terms
S⊗_RΛ^j_R(R^n) and base-changed contraction differential with K_S(algebraMap∘a). It includes the
canonical exterior-power base-change comparison and removal of the degreewise trivial universe
copy. -/
def familyBaseChangeUnliftIso {n : ℕ} (a : Fin n → R) :
    baseChangeComplex R S (Fin n → R) (familyFunctional R a) ≅
      familyComplex S (mappedFamily R S a) :=
  familyBaseChangeIso R S a ≪≫
    (NatIso.mapHomologicalComplex (ModuleCat.uliftFunctorSelfIso.{u, 0} S)
      (ComplexShape.down ℕ)).app
      (familyComplex S (mappedFamily R S a)) ≪≫
    (Functor.mapHomologicalComplexIdIso (ModuleCat.{u} S) (ComplexShape.down ℕ)).app
      (familyComplex S (mappedFamily R S a))

/-- Let R,S be commutative rings and S an R-algebra, all in universe u. For an R-module M with
carrier in u, the tensor S⊗_R M viewed as an R-module is canonically isomorphic to the
restriction of its S-module scalar-extension structure. Both forward and inverse maps are the
identity on tensor values; the scalar-tower relation identifies the two R-actions. -/
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

/-- Let R,S be commutative rings and S an R-algebra, all in universe u. For a:Fin n→R and j∈ℕ, this
R-module isomorphism compares degree j of S⊗_R K_R(a) with degree j of the restriction of its
scalar-extension Koszul complex. Both terms are S⊗_RΛ^j_R(R^n); the comparison is identity on
those tensor values with the compatible scalar actions. -/
def tensorFamilyBaseChangeComponentIso {n : ℕ} (a : Fin n → R) (j : ℕ) :
    ((((tensoringLeft (ModuleCat.{u} R)).obj (ModuleCat.of R S)).mapHomologicalComplex
      (ComplexShape.down ℕ)).obj (familyComplex R a)).X j ≅
        (((ModuleCat.restrictScalars.{u} (algebraMap R S)).mapHomologicalComplex
          (ComplexShape.down ℕ)).obj
            (baseChangeComplex R S (Fin n → R) (familyFunctional R a))).X j :=
  eqToIso (by rfl) ≪≫ tensorModuleRestrictionIso R S (⋀[R]^j (Fin n → R)) ≪≫
    (ModuleCat.restrictScalars (algebraMap R S)).mapIso
      (eqToIso (baseChangeComplex_X R S (Fin n → R) (familyFunctional R a) j)).symm

/-- Let R,S be commutative rings and S an R-algebra, all in universe u. For a:Fin n→R, degree j and
x∈S⊗_RΛ^j_R(R^n), the forward component of the coefficient-to-restricted-base-change comparison
sends x to x. The equality uses the common tensor carrier of those two degree-j terms. -/
theorem tensorFamilyBaseChangeComponentIso_hom_apply
    {n : ℕ} (a : Fin n → R) (j : ℕ)
    (x : ((((tensoringLeft (ModuleCat.{u} R)).obj (ModuleCat.of R S)).mapHomologicalComplex
      (ComplexShape.down ℕ)).obj (familyComplex R a)).X j) :
    (tensorFamilyBaseChangeComponentIso R S a j).hom x = x := rfl

/-- Let R,S be commutative rings and S an R-algebra, all in universe u. For a:Fin n→R, this R-linear
chain isomorphism identifies S⊗_R K_R(a) with the restriction of the scalar-extension complex.
Its term maps are the tensor identities S⊗_RΛ^j_R(R^n)→S⊗_RΛ^j_R(R^n), and they commute with the
base-changed contraction differential in every degree. -/
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

/-- Let R,S be commutative rings and S an R-algebra, all in universe u. For a:Fin n→R, this R-linear
chain isomorphism S⊗_R K_R(a)≅U(K_S(algebraMap∘a)) is the tensor restriction comparison followed
by the finite-family scalar-extension comparison. It does not require regularity of either
family. -/
def tensorFamilyComplexIsoRestrictedMappedFamily {n : ℕ} (a : Fin n → R) :
    (((tensoringLeft (ModuleCat.{u} R)).obj (ModuleCat.of R S)).mapHomologicalComplex
      (ComplexShape.down ℕ)).obj (familyComplex R a) ≅
        ((ModuleCat.restrictScalars.{u} (algebraMap R S)).mapHomologicalComplex
          (ComplexShape.down ℕ)).obj (familyComplex S (mappedFamily R S a)) :=
  tensorFamilyComplexIsoRestrictedBaseChange R S a ≪≫
    ((ModuleCat.restrictScalars.{u} (algebraMap R S)).mapHomologicalComplex
      (ComplexShape.down ℕ)).mapIso (familyBaseChangeUnliftIso R S a)

/-- Let R,S be commutative rings and S an R-algebra, all in universe u. For an S-module-valued chain
complex K of shape down ℕ and q∈ℕ, restriction of scalars gives the canonical R-module
isomorphism H_q(U(K))≅U(H_q(K)). Exactness of scalar restriction supplies the comparison. -/
def restrictedComplexHomologyIso
    (K : ChainComplex (ModuleCat.{u} S) ℕ) (q : ℕ) :
    (((ModuleCat.restrictScalars.{u} (algebraMap R S)).mapHomologicalComplex
      (ComplexShape.down ℕ)).obj K).homology q ≅
        (ModuleCat.restrictScalars.{u} (algebraMap R S)).obj (K.homology q) :=
  (K.sc q).mapHomologyIso (ModuleCat.restrictScalars.{u} (algebraMap R S))

/-- Let R,S be commutative rings and S an R-algebra, all in universe u. Let a:Fin n→R be weakly
regular in its ordered list, so multiplication by a_i is injective modulo the preceding
coefficients. For q∈ℕ, this is the canonical isomorphism
Tor_q^R(S,R/(a))≅U(H_q(K_S(algebraMap∘a))). It computes Tor using the Koszul projective
resolution of R/(a), the tensor-to-mapped-family complex comparison and exact scalar
restriction. No flatness hypothesis on S or regularity hypothesis on the mapped family is added. -/
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

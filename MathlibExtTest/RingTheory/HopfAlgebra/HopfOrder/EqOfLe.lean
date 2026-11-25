/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RingTheory.HopfAlgebra.HopfOrder.EqOfLe

@[expose] public section

universe u v w w'

open scoped TensorProduct

/-- Exact source statement of the target theorem, with the original binders. -/
example
    {R : Type u} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    {K : Type v} [Field K] [Algebra R K] [IsFractionRing R K]
    {A : Type w} [CommRing A] [HopfAlgebra K A] [Algebra R A] [IsScalarTower R K A]
    {Ā : Type w'} [CommRing Ā] [HopfAlgebra K Ā] [Algebra R Ā] [IsScalarTower R K Ā]
    [Coalgebra.IsCocomm K A]
    {S S' : Subalgebra R A} (hle : S ≤ S')
    (hSfin : Module.Finite R ↥S)
    (hSspan : Submodule.span K (S : Set A) = ⊤)
    (hScomul : ∀ x ∈ S, Coalgebra.comul (R := K) x ∈
        (Algebra.TensorProduct.productMap
          (((Algebra.TensorProduct.includeLeft : A →ₐ[K] A ⊗[K] A).restrictScalars R).comp S.val)
          (((Algebra.TensorProduct.includeRight : A →ₐ[K] A ⊗[K] A).restrictScalars R).comp
              S.val)).range)
    (hSanti : ∀ x ∈ S, HopfAlgebra.antipode K (A := A) x ∈ S)
    (hScounit : ∀ x ∈ S, Coalgebra.counit (R := K) (A := A) x ∈ (algebraMap R K).range)
    (hS'fin : Module.Finite R ↥S')
    (hS'span : Submodule.span K (S' : Set A) = ⊤)
    (hS'comul : ∀ x ∈ S', Coalgebra.comul (R := K) x ∈
        (Algebra.TensorProduct.productMap
          (((Algebra.TensorProduct.includeLeft : A →ₐ[K] A ⊗[K] A).restrictScalars R).comp S'.val)
          (((Algebra.TensorProduct.includeRight : A →ₐ[K] A ⊗[K] A).restrictScalars R).comp
              S'.val)).range)
    (hS'anti : ∀ x ∈ S', HopfAlgebra.antipode K (A := A) x ∈ S')
    (hS'counit : ∀ x ∈ S', Coalgebra.counit (R := K) (A := A) x ∈ (algebraMap R K).range)
    (π : A →ₐc[K] Ā) (hπ : Function.Surjective π)
    (hker : S.comap
        (((HopfAlgebra.hopfKer π).val : ↥(HopfAlgebra.hopfKer π) →ₐ[K] A).restrictScalars R)
      = S'.comap (((HopfAlgebra.hopfKer π).val : ↥(HopfAlgebra.hopfKer π) →ₐ[K] A).restrictScalars
          R))
    (himg : S.map ((π : A →ₐ[K] Ā).restrictScalars R) = S'.map
        ((π : A →ₐ[K] Ā).restrictScalars R)) :
    S = S' :=
  HopfOrder.eq_of_le_of_comap_hopfKer_eq_of_map_eq hle hSfin hSspan hScomul hSanti hScounit
    hS'fin hS'span hS'comul hS'anti hS'counit π hπ hker himg

/-- Exact source statement: images of Hopf orders. -/
example
    {R : Type*} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
    {A : Type*} [CommRing A] [HopfAlgebra K A] [Algebra R A] [IsScalarTower R K A]
    {Ā : Type*} [CommRing Ā] [HopfAlgebra K Ā] [Algebra R Ā] [IsScalarTower R K Ā]
    (S : Subalgebra R A)
    (hfin : Module.Finite R ↥S)
    (hspan : Submodule.span K (S : Set A) = ⊤)
    (hcomul : ∀ x ∈ S, Coalgebra.comul (R := K) x ∈
        (Algebra.TensorProduct.productMap
          (((Algebra.TensorProduct.includeLeft : A →ₐ[K] A ⊗[K] A).restrictScalars R).comp S.val)
          (((Algebra.TensorProduct.includeRight : A →ₐ[K] A ⊗[K] A).restrictScalars R).comp
              S.val)).range)
    (hanti : ∀ x ∈ S, HopfAlgebra.antipode K (A := A) x ∈ S)
    (hcounit : ∀ x ∈ S, Coalgebra.counit (R := K) (A := A) x ∈ (algebraMap R K).range)
    (π : A →ₐc[K] Ā) (hπ : Function.Surjective π) :
    Module.Finite R ↥((S.map ((π : A →ₐ[K] Ā).restrictScalars R))) ∧
    Submodule.span K (((S.map ((π : A →ₐ[K] Ā).restrictScalars R)) : Subalgebra R Ā) : Set Ā) = ⊤ ∧
    (∀ x ∈ (S.map ((π : A →ₐ[K] Ā).restrictScalars R)), Coalgebra.comul (R := K) x ∈
        (Algebra.TensorProduct.productMap
          (((Algebra.TensorProduct.includeLeft : Ā →ₐ[K] Ā ⊗[K] Ā).restrictScalars R).comp
              ((S.map ((π : A →ₐ[K] Ā).restrictScalars R))).val)
          (((Algebra.TensorProduct.includeRight : Ā →ₐ[K] Ā ⊗[K] Ā).restrictScalars R).comp
              ((S.map ((π : A →ₐ[K] Ā).restrictScalars R))).val)).range) ∧
    (∀ x ∈ (S.map ((π : A →ₐ[K] Ā).restrictScalars R)), HopfAlgebra.antipode K (A := Ā) x ∈
        (S.map ((π : A →ₐ[K] Ā).restrictScalars R))) ∧
    (∀ x ∈ (S.map ((π : A →ₐ[K] Ā).restrictScalars R)), Coalgebra.counit (R := K) (A := Ā) x ∈
        (algebraMap R K).range) :=
  HopfOrder.isHopfOrder_map S hfin hspan hcomul hanti hcounit π hπ

/-- Exact source statement: Hopf kernels of integral maps. -/
example
    {R : Type*} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
    {A : Type*} [CommRing A] [HopfAlgebra K A] [Algebra R A] [IsScalarTower R K A]
    {Ā : Type*} [CommRing Ā] [HopfAlgebra K Ā] [Algebra R Ā] [IsScalarTower R K Ā]
    (S : Subalgebra R A)
    {H : Type*} [CommRing H] [HopfAlgebra R H] [Module.Free R H]
    (e : H →ₐ[R] A) (he : Function.Injective e) (heS : e.range = S)
    (he_comul : ∀ h : H, Coalgebra.comul (R := K) (e h) =
        Algebra.TensorProduct.productMap
          (((Algebra.TensorProduct.includeLeft : A →ₐ[K] A ⊗[K] A).restrictScalars R).comp e)
          (((Algebra.TensorProduct.includeRight : A →ₐ[K] A ⊗[K] A).restrictScalars R).comp e)
          (Coalgebra.comul (R := R) h))
    (π : A →ₐc[K] Ā)
    {Hbar : Type*} [CommRing Hbar] [HopfAlgebra R Hbar] [Module.Free R Hbar]
    (q : H →ₐc[R] Hbar) (ebar : Hbar →ₐ[R] Ā) (hebar : Function.Injective ebar)
    (hsq : ∀ h : H, ebar (q h) = π (e h)) :
    (HopfAlgebra.hopfKer q).map e = S ⊓ (HopfAlgebra.hopfKer π).restrictScalars R :=
  HopfOrder.map_hopfKer_eq_inf_hopfKer S e he heS he_comul π q ebar hebar hsq

/-- Exact source statement: surjections onto finite free Hopf algebras are Hopf-Galois. -/
example {R : Type u} [CommRing R] {A : Type v} [CommRing A] [HopfAlgebra R A]
    {B : Type w} [CommRing B] [HopfAlgebra R B] [Module.Finite R B] [Module.Free R B]
    (π : A →ₐc[R] B) (hπ : Function.Surjective π) : HopfAlgebra.IsHopfGalois π :=
  HopfAlgebra.isHopfGalois_of_surjective π hπ

/-- Exact source statement: finite projectivity over the Hopf kernel. -/
example {R : Type u} [CommRing R] {A : Type v} [CommRing A] [HopfAlgebra R A]
    {B : Type w} [CommRing B] [HopfAlgebra R B] [Module.Finite R B] [Module.Free R B]
    (π : A →ₐc[R] B) (hπ : Function.Surjective π) :
    Module.Finite ↥(HopfAlgebra.hopfKer π) A ∧ Module.Projective ↥(HopfAlgebra.hopfKer π) A :=
  HopfAlgebra.finite_projective_hopfKer_of_surjective π hπ

/-- Exact source statement: left integrals on a finite free Hopf algebra. -/
example {R : Type u} [CommRing R] {B : Type v} [CommRing B] [HopfAlgebra R B]
    [Module.Finite R B] [Module.Free R B] :
    ∃ (n : ℕ) (Λ : Fin n → Module.Dual R B) (u : Fin n → B),
      (∀ j (b : B), (TensorProduct.rid R B) ((Λ j).lTensor B (Coalgebra.comul b)) = (Λ j b) •
          (1 : B))
      ∧ ∀ b : B, ∑ j, Λ j (u j * b) = Coalgebra.counit b :=
  HopfAlgebra.exists_leftIntegral_sum_apply_mul_eq_counit

/-- Exact source statement: surjectivity of the canonical map. -/
example {R : Type*} [CommRing R] {A : Type*} [CommRing A] [HopfAlgebra R A]
    {B : Type*} [CommRing B] [Bialgebra R B] (π : A →ₐc[R] B) (hπ : Function.Surjective π) :
    Function.Surjective (HopfAlgebra.canMap π) :=
  HopfAlgebra.canMap_surjective_of_surjective π hπ

/-- The Hopf kernel contains the unit. -/
example {R : Type u} [CommRing R] {A : Type v} [CommRing A] [Bialgebra R A]
    {B : Type w} [CommRing B] [Bialgebra R B] (π : A →ₐc[R] B) :
    (1 : A) ∈ HopfAlgebra.hopfKer π :=
  one_mem _

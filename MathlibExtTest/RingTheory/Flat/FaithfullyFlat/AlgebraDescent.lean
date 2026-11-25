/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RingTheory.Flat.FaithfullyFlat.AlgebraDescent

@[expose] public section

set_option autoImplicit false

open TensorProduct Algebra.TensorProduct

/-- Exact-source consumer, using the original binders verbatim. -/
example {S : Type*} [CommRing S] (S' : Type*) [CommRing S'] [Algebra S S']
    [Module.FaithfullyFlat S S'] (A' : Type*) [CommRing A'] [Algebra S A']
    [Algebra S' A'] [IsScalarTower S S' A']
    (φ : A' ⊗[S] S' ≃ₐ[S] S' ⊗[S] A')
    (hφlin : φ.toAlgHom.comp
      (Algebra.TensorProduct.map (IsScalarTower.toAlgHom S S' A') (AlgHom.id S S')) =
      Algebra.TensorProduct.map (AlgHom.id S S') (IsScalarTower.toAlgHom S S' A'))
    (hφcoc : (Algebra.TensorProduct.map (AlgHom.id S S') φ.toAlgHom).comp
        ((Algebra.TensorProduct.assoc S S S S' A' S').toAlgHom.comp
          (Algebra.TensorProduct.map φ.toAlgHom (AlgHom.id S S'))) =
      (Algebra.TensorProduct.map (AlgHom.id S S')
        (Algebra.TensorProduct.comm S A' S').toAlgHom).comp
        ((Algebra.TensorProduct.assoc S S S S' A' S').toAlgHom.comp
          ((Algebra.TensorProduct.map φ.toAlgHom (AlgHom.id S S')).comp
            ((Algebra.TensorProduct.assoc S S S A' S' S').symm.toAlgHom.comp
              ((Algebra.TensorProduct.map (AlgHom.id S A')
                (Algebra.TensorProduct.comm S S' S').toAlgHom).comp
                (Algebra.TensorProduct.assoc S S S A' S' S').toAlgHom))))) :
    let A : Subalgebra S A' :=
      AlgHom.equalizer
        (φ.toAlgHom.comp (Algebra.TensorProduct.includeLeft : A' →ₐ[S] A' ⊗[S] S'))
        (Algebra.TensorProduct.includeRight : A' →ₐ[S] S' ⊗[S] A')
    Function.Bijective (Algebra.TensorProduct.lift
      (IsScalarTower.toAlgHom S S' A') A.val (fun s a => Commute.all _ _)) :=
  Algebra.bijective_tensorProduct_equalizer_of_faithfullyFlat_of_descentDatum
    S' A' φ hφlin hφcoc

/-- The same consumer in higher universes. -/
example {S : Type 1} [CommRing S] (S' : Type 2) [CommRing S'] [Algebra S S']
    [Module.FaithfullyFlat S S'] (A' : Type 3) [CommRing A'] [Algebra S A']
    [Algebra S' A'] [IsScalarTower S S' A']
    (φ : A' ⊗[S] S' ≃ₐ[S] S' ⊗[S] A')
    (hφlin : φ.toAlgHom.comp
      (Algebra.TensorProduct.map (IsScalarTower.toAlgHom S S' A') (AlgHom.id S S')) =
      Algebra.TensorProduct.map (AlgHom.id S S') (IsScalarTower.toAlgHom S S' A'))
    (hφcoc : (Algebra.TensorProduct.map (AlgHom.id S S') φ.toAlgHom).comp
        ((Algebra.TensorProduct.assoc S S S S' A' S').toAlgHom.comp
          (Algebra.TensorProduct.map φ.toAlgHom (AlgHom.id S S'))) =
      (Algebra.TensorProduct.map (AlgHom.id S S')
        (Algebra.TensorProduct.comm S A' S').toAlgHom).comp
        ((Algebra.TensorProduct.assoc S S S S' A' S').toAlgHom.comp
          ((Algebra.TensorProduct.map φ.toAlgHom (AlgHom.id S S')).comp
            ((Algebra.TensorProduct.assoc S S S A' S' S').symm.toAlgHom.comp
              ((Algebra.TensorProduct.map (AlgHom.id S A')
                (Algebra.TensorProduct.comm S S' S').toAlgHom).comp
                (Algebra.TensorProduct.assoc S S S A' S' S').toAlgHom))))) :
    let A : Subalgebra S A' :=
      AlgHom.equalizer
        (φ.toAlgHom.comp (Algebra.TensorProduct.includeLeft : A' →ₐ[S] A' ⊗[S] S'))
        (Algebra.TensorProduct.includeRight : A' →ₐ[S] S' ⊗[S] A')
    Function.Bijective (Algebra.TensorProduct.lift
      (IsScalarTower.toAlgHom S S' A') A.val (fun s a => Commute.all _ _)) :=
  Algebra.bijective_tensorProduct_equalizer_of_faithfullyFlat_of_descentDatum
    S' A' φ hφlin hφcoc

/-- Boundary specialization to the trivial base change `S' = S`. -/
example {S : Type*} [CommRing S] (A' : Type*) [CommRing A'] [Algebra S A']
    (φ : A' ⊗[S] S ≃ₐ[S] S ⊗[S] A')
    (hφlin : φ.toAlgHom.comp
      (Algebra.TensorProduct.map (IsScalarTower.toAlgHom S S A') (AlgHom.id S S)) =
      Algebra.TensorProduct.map (AlgHom.id S S) (IsScalarTower.toAlgHom S S A'))
    (hφcoc : (Algebra.TensorProduct.map (AlgHom.id S S) φ.toAlgHom).comp
        ((Algebra.TensorProduct.assoc S S S S A' S).toAlgHom.comp
          (Algebra.TensorProduct.map φ.toAlgHom (AlgHom.id S S))) =
      (Algebra.TensorProduct.map (AlgHom.id S S)
        (Algebra.TensorProduct.comm S A' S).toAlgHom).comp
        ((Algebra.TensorProduct.assoc S S S S A' S).toAlgHom.comp
          ((Algebra.TensorProduct.map φ.toAlgHom (AlgHom.id S S)).comp
            ((Algebra.TensorProduct.assoc S S S A' S S).symm.toAlgHom.comp
              ((Algebra.TensorProduct.map (AlgHom.id S A')
                (Algebra.TensorProduct.comm S S S).toAlgHom).comp
                (Algebra.TensorProduct.assoc S S S A' S S).toAlgHom))))) :
    Function.Bijective (Algebra.TensorProduct.lift
      (IsScalarTower.toAlgHom S S A')
      (AlgHom.equalizer
        (φ.toAlgHom.comp (Algebra.TensorProduct.includeLeft : A' →ₐ[S] A' ⊗[S] S))
        (Algebra.TensorProduct.includeRight : A' →ₐ[S] S ⊗[S] A')).val
      (fun s a => Commute.all _ _)) :=
  Algebra.bijective_tensorProduct_equalizer_of_faithfullyFlat_of_descentDatum
    S A' φ hφlin hφcoc

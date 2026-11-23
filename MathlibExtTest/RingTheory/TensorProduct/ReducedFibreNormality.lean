/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RingTheory.TensorProduct.ReducedFibreNormality

@[expose] public section

open scoped TensorProduct

universe u v

-- Consumer with the original binders.
example {R B R' K' k' : Type u} [CommRing R] [CommRing B] [Algebra R B] [Module.Flat R B]
    [CommRing R'] [Algebra R R'] (ϖ : R') (hϖ : ϖ ∈ nonZeroDivisors R')
    [CommRing K'] [Algebra R' K'] [IsLocalization.Away ϖ K'] [Algebra R K'] [IsScalarTower R R' K']
    [IsDomain (K' ⊗[R] B)] [IsIntegrallyClosed (K' ⊗[R] B)]
    [CommRing k'] [Algebra R' k'] [Algebra R k'] [IsScalarTower R R' k']
    (hk : Function.Surjective (algebraMap R' k')) (hker : RingHom.ker (algebraMap R' k') =
      Ideal.span {ϖ})
    (hred : IsReduced (k' ⊗[R] B)) :
    IsDomain (R' ⊗[R] B) ∧ IsIntegrallyClosed (R' ⊗[R] B) :=
  Algebra.TensorProduct.isDomain_and_isIntegrallyClosed_of_isReduced_fibre (K' := K') ϖ hϖ hk hker hred

-- Higher-universe consumer: the same statement in `Type (u+1)`.
example {R B R' K' k' : Type (u + 1)} [CommRing R] [CommRing B] [Algebra R B] [Module.Flat R B]
    [CommRing R'] [Algebra R R'] (ϖ : R') (hϖ : ϖ ∈ nonZeroDivisors R')
    [CommRing K'] [Algebra R' K'] [IsLocalization.Away ϖ K'] [Algebra R K'] [IsScalarTower R R' K']
    [IsDomain (K' ⊗[R] B)] [IsIntegrallyClosed (K' ⊗[R] B)]
    [CommRing k'] [Algebra R' k'] [Algebra R k'] [IsScalarTower R R' k']
    (hk : Function.Surjective (algebraMap R' k')) (hker : RingHom.ker (algebraMap R' k') =
      Ideal.span {ϖ})
    (hred : IsReduced (k' ⊗[R] B)) :
    IsDomain (R' ⊗[R] B) ∧ IsIntegrallyClosed (R' ⊗[R] B) :=
  Algebra.TensorProduct.isDomain_and_isIntegrallyClosed_of_isReduced_fibre (K' := K') ϖ hϖ hk hker hred

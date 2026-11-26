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

public import MathlibExt.Algebra.Homology.CochainComplex.TensorHom.FiniteFactorInverse

/-!
# Hom–tensor isomorphism for a bounded finite projective factor

For integer cochain complexes `P`, `J`, and `U` of modules over a commutative ring, assume
every term of `U` is finite and categorically projective and that `U` vanishes below an
integer `L` and above an integer `N`.

The signed comparison `Hom_R(P,J) ⊗_R U → Hom_R(P,J ⊗_R U)` is then an isomorphism of cochain
complexes. Its degreewise inverse is the sum of the factor-degree inverse pieces over `[L,
N]`. The complexes `P` and `J` have no boundedness or projectivity hypothesis; scalar and
module-carrier universes are independent.
-/

@[expose] public section
noncomputable section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits CochainComplex.HomComplex

namespace CochainComplex.ModuleTensor

universe u v

variable (R : Type u) [CommRing R]
  (P J U : CochainComplex (ModuleCat.{v} R) ℤ)
  [∀ b : ℤ, CategoryTheory.Projective (U.X b)] [∀ b : ℤ, Module.Finite R (U.X b)]

/-- Degreewise Hom–tensor isomorphism for a bounded finite projective factor.

Under finite projectivity of all `U^b` and vanishing below `L` and above `N`, the degree-`n`
signed Hom–tensor comparison is an isomorphism. Its inverse is the finite sum
`homTensorFiniteFactorInverseDegree ... L N n`. -/
def finiteFactorHomTensorXIso (L N : ℤ)
    (hUlo : ∀ b : ℤ, b < L → IsZero (U.X b))
    (hUhi : ∀ b : ℤ, N < b → IsZero (U.X b)) (n : ℤ) :
    (complexAt R (linearComplex R P J) U).X n ≅
      (linearComplex R P (complexAt R J U)).X n :=
  (LinearEquiv.ofLinearMap (homTensorDegree R P J U n).hom
    (homTensorFiniteFactorInverseDegree R P J U L N n)
    (by
      apply LinearMap.ext
      intro z
      exact homTensorFiniteFactorInverseDegree_rightInverse R P J U L N n hUlo hUhi z)
    (by
      apply LinearMap.ext
      intro z
      exact homTensorFiniteFactorInverseDegree_leftInverse R P J U L N n hUlo hUhi z)).toModuleIso

/-- Cochain Hom–tensor isomorphism for a bounded finite projective factor.

The degreewise signed comparison isomorphisms commute with differentials and give `Hom_R(P,J)
⊗_R U ≅ Hom_R(P,J ⊗_R U)`, using bounds and finite projectivity only on `U`. -/
def finiteFactorHomTensorIso (L N : ℤ)
    (hUlo : ∀ b : ℤ, b < L → IsZero (U.X b))
    (hUhi : ∀ b : ℤ, N < b → IsZero (U.X b)) :
    complexAt R (linearComplex R P J) U ≅ linearComplex R P (complexAt R J U) :=
  HomologicalComplex.Hom.isoOfComponents
    (finiteFactorHomTensorXIso R P J U L N hUlo hUhi) (by
      intro n m hnm
      change n + 1 = m at hnm
      subst m
      exact homTensorDegree_comm R P J U n)

/-- Forward bounded-factor isomorphism is the signed Hom–tensor map.

The forward morphism of `finiteFactorHomTensorIso` equals `homTensorComparison R P J U`. -/
theorem finiteFactorHomTensorIso_hom (L N : ℤ)
    (hUlo : ∀ b : ℤ, b < L → IsZero (U.X b))
    (hUhi : ∀ b : ℤ, N < b → IsZero (U.X b)) :
    (finiteFactorHomTensorIso R P J U L N hUlo hUhi).hom = homTensorComparison R P J U := by
  apply HomologicalComplex.hom_ext
  intro n
  rfl

/-- Inverse bounded-factor isomorphism is the finite inverse sum.

In integer degree `n`, the inverse component of the Hom–tensor isomorphism is
`homTensorFiniteFactorInverseDegree R P J U L N n`. -/
theorem finiteFactorHomTensorIso_inv_f (L N : ℤ)
    (hUlo : ∀ b : ℤ, b < L → IsZero (U.X b))
    (hUhi : ∀ b : ℤ, N < b → IsZero (U.X b)) (n : ℤ) :
    ((finiteFactorHomTensorIso R P J U L N hUlo hUhi).inv.f n).hom =
      homTensorFiniteFactorInverseDegree R P J U L N n := rfl

end CochainComplex.ModuleTensor

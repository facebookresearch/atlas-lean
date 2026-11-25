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
# The original Hom–tensor Iso for a bounded finite-projective tensor factor

The concrete signed inverse makes the actual original degree comparison
bijective. Its existing differential square assembles the object Iso, before
taking homology. The first Hom source and Hom target are arbitrary, and the
ring and original module-carrier worlds remain independent.
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

/-- The original signed degree map has its earned bounded-U inverse. -/
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

/-- The actual cochain object Iso uses the same signed original degree maps
and the original differential square. -/
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

/-- Its hom is the actual original unrestricted cochain comparison, including
the original source-index signs and all original noninvertible variable maps. -/
theorem finiteFactorHomTensorIso_hom (L N : ℤ)
    (hUlo : ∀ b : ℤ, b < L → IsZero (U.X b))
    (hUhi : ∀ b : ℤ, N < b → IsZero (U.X b)) :
    (finiteFactorHomTensorIso R P J U L N hUlo hUhi).hom = homTensorComparison R P J U := by
  apply HomologicalComplex.hom_ext
  intro n
  rfl

/-- The inverse component is exactly the signed finite sum of the original
projected integer-product/coefficient inverses and native coprojections. -/
theorem finiteFactorHomTensorIso_inv_f (L N : ℤ)
    (hUlo : ∀ b : ℤ, b < L → IsZero (U.X b))
    (hUhi : ∀ b : ℤ, N < b → IsZero (U.X b)) (n : ℤ) :
    ((finiteFactorHomTensorIso R P J U L N hUlo hUhi).inv.f n).hom =
      homTensorFiniteFactorInverseDegree R P J U L N n := rfl

end CochainComplex.ModuleTensor

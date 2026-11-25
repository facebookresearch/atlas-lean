/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


-- Author: @toskua, Avocado
module

public import MathlibExt.Algebra.Homology.KoszulComplexFamily
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.RingTheory.Length

/-!
# Degree-zero homology of a Koszul complex

The existing Koszul augmentation is a cokernel of the degree-one
differential.  Degree-zero homology is the same cokernel, so uniqueness of
cokernels identifies it with the quotient by the range ideal.  The
universe-lift used by the categorical augmentation is removed in the final
linear equivalence.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace KoszulComplex

universe u v

variable (R : Type u) [CommRing R]
variable (M : Type v) [AddCommGroup M] [Module R M]

/-- Degree-zero Koszul homology as the universe-lifted quotient by the range
ideal of the coefficient functional. -/
noncomputable def homologyZeroIsoQuotientLifted (x : M →ₗ[R] R) :
    (complex R M x).homology 0 ≅
      ModuleCat.of R (ULift.{max u v, u} (R ⧸ ideal R M x)) := by
  let K := complex R M x
  let hOp := K.opcyclesIsCokernel 1 0 (by simp)
  let hAug := augmentationIsCokernel R M x
  exact K.isoHomologyι₀ ≪≫
    IsColimit.coconePointUniqueUpToIso hOp hAug

/-- Linear-equivalence form without the categorical universe lift. -/
noncomputable def homologyZeroLinearEquivQuotient (x : M →ₗ[R] R) :
    (complex R M x).homology 0 ≃ₗ[R] R ⧸ ideal R M x :=
  (homologyZeroIsoQuotientLifted R M x).toLinearEquiv.trans
    ULift.moduleEquiv

/-- Degree-zero Koszul homology has the same module length as the quotient by
the range ideal. -/
theorem homologyZero_length_eq_quotient (x : M →ₗ[R] R) :
    Module.length R ((complex R M x).homology 0) =
      Module.length R (R ⧸ ideal R M x) :=
  (homologyZeroLinearEquivQuotient R M x).length_eq

/-- Finite-family specialization: degree-zero homology is the quotient by
the ideal spanned by the family. -/
noncomputable def familyHomologyZeroLinearEquivQuotient
    {I : Type v} [Fintype I] (a : I → R) :
    (familyComplex R a).homology 0 ≃ₗ[R]
      R ⧸ Ideal.span (Set.range a) := by
  rw [← familyIdeal_eq_span R a]
  exact homologyZeroLinearEquivQuotient R (I → R)
    (familyFunctional R a)

/-- Finite-family degree-zero homology length is the length of the quotient
by the spanned ideal. -/
theorem familyHomologyZero_length_eq_quotient
    {I : Type v} [Fintype I] (a : I → R) :
    Module.length R ((familyComplex R a).homology 0) =
      Module.length R (R ⧸ Ideal.span (Set.range a)) :=
  (familyHomologyZeroLinearEquivQuotient R a).length_eq

end KoszulComplex

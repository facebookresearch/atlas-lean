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

public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.LinearAlgebra.Span.Basic

/-!
# Quotient Hom and annihilators

Evaluation at the class of one identifies R-linear maps from R/I with
elements killed by I. The inverse is `liftQ` of scalar multiplication.
Scalar and coefficient universes are independent.

Weibel, *Homological Algebra*, §4.6.
-/

@[expose] public section
noncomputable section

universe u v w
namespace Ideal

variable {R : Type u} [CommRing R]

/-- The literal class of one in the native module quotient. -/
def quotientOne (I : Ideal R) : R ⧸ (I : Submodule R R) :=
  Submodule.Quotient.mk 1

/-- Scalar multiplication of one is the original quotient class. -/
lemma smul_quotientOne (I : Ideal R) (r : R) :
    r • quotientOne I = Submodule.Quotient.mk r := by
  change r • (Submodule.Quotient.mk (1 : R) : R ⧸ (I : Submodule R R)) = _
  rw [← Submodule.Quotient.mk_smul]
  congr 1
  exact mul_one r

/-- Native quotient descent of the actual scalar-multiplication map. -/
def quotientHomOfAnnihilator (I : Ideal R) (M : Type v)
    [AddCommGroup M] [Module R M] (a : Submodule.torsionBySet R M (I : Set R)) :
    (R ⧸ (I : Submodule R R)) →ₗ[R] M :=
  (I : Submodule R R).liftQ (LinearMap.toSpanSingleton R M a.val) (by
    intro r hr
    rw [LinearMap.mem_ker]
    exact (Submodule.mem_torsionBySet_iff (I : Set R) a.val).mp a.property ⟨r, hr⟩)

/-- The descended map is actual scalar multiplication on representatives. -/
lemma quotientHomOfAnnihilator_mk (I : Ideal R) (M : Type v)
    [AddCommGroup M] [Module R M] (a : Submodule.torsionBySet R M (I : Set R)) (r : R) :
    quotientHomOfAnnihilator I M a (Submodule.Quotient.mk r) = r • a.val := rfl

/-- Evaluation at one and native liftQ give the actual linear equivalence. -/
def quotientHomEquiv (I : Ideal R) (M : Type v) [AddCommGroup M] [Module R M] :
    ((R ⧸ (I : Submodule R R)) →ₗ[R] M) ≃ₗ[R]
      Submodule.torsionBySet R M (I : Set R) where
  toFun φ := ⟨φ (quotientOne I), by
    apply (Submodule.mem_torsionBySet_iff (I : Set R) (φ (quotientOne I))).mpr
    intro r
    have hz : (r : R) • quotientOne I = 0 := by
      rw [smul_quotientOne]
      exact (Submodule.Quotient.mk_eq_zero (I : Submodule R R)).mpr r.property
    rw [← φ.map_smul, hz, φ.map_zero]⟩
  invFun := quotientHomOfAnnihilator I M
  left_inv φ := by
    apply LinearMap.ext
    intro q
    obtain ⟨r, rfl⟩ := Submodule.mkQ_surjective (I : Submodule R R) q
    change r • φ (quotientOne I) = φ (Submodule.Quotient.mk r)
    rw [← φ.map_smul, smul_quotientOne]
  right_inv a := by
    apply Subtype.ext
    change (1 : R) • a.val = a.val
    exact one_smul R a.val
  map_add' φ ψ := Subtype.ext rfl
  map_smul' r φ := Subtype.ext rfl

/-- The forward equivalence retains the original evaluation value. -/
lemma quotientHomEquiv_val (I : Ideal R) (M : Type v) [AddCommGroup M] [Module R M]
    (φ : (R ⧸ (I : Submodule R R)) →ₗ[R] M) :
    (quotientHomEquiv I M φ).val = φ (quotientOne I) := rfl

/-- Coefficient postcomposition preserves the same actual evaluation value. -/
lemma quotientHomEquiv_postcomp_val (I : Ideal R)
    {M : Type v} [AddCommGroup M] [Module R M]
    {N : Type w} [AddCommGroup N] [Module R N] (f : M →ₗ[R] N)
    (φ : (R ⧸ (I : Submodule R R)) →ₗ[R] M) :
    (quotientHomEquiv I N (f.comp φ)).val = f (quotientHomEquiv I M φ).val := rfl

/-- Actual quotient precomposition along an ideal inclusion preserves one. -/
lemma quotientHomEquiv_precomp_val {I J : Ideal R} (h : I ≤ J)
    (M : Type v) [AddCommGroup M] [Module R M]
    (φ : (R ⧸ (J : Submodule R R)) →ₗ[R] M) :
    (quotientHomEquiv I M
      (φ.comp (Submodule.mapQ (I : Submodule R R) (J : Submodule R R)
        (LinearMap.id : R →ₗ[R] R) (by
          rw [Submodule.comap_id]
          exact h)))).val = (quotientHomEquiv J M φ).val := rfl

end Ideal

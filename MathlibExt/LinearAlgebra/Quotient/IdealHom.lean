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
# Hom from an ideal quotient and the ideal annihilator

Let R be a commutative ring, I an ideal, and M an R-module. Evaluation at the module-quotient
class [1] gives an R-linear equivalence Hom_R(R/I,M) ≅ {m∈M | r·m=0 for every r∈I}. Its
inverse maps [r] to r·m.

The equivalence is natural under coefficient postcomposition and under the quotient map for
I≤J, which corresponds to inclusion of the J-annihilator into the I-annihilator. The scalar
and coefficient universes are independent.
-/

@[expose] public section
noncomputable section

universe u v w
namespace Ideal

variable {R : Type u} [CommRing R]

/-- For a commutative ring R and ideal I, define quotientOne(I) to be [1] in the R-module quotient
R/(I:Submodule R R). This uses the module quotient, with its natural scalar action. -/
def quotientOne (I : Ideal R) : R ⧸ (I : Submodule R R) :=
  Submodule.Quotient.mk 1

/-- Let R be a commutative ring, I an ideal, and r∈R. In the module quotient R/I, r·[1]=[r]. The
unit class therefore generates the quotient as an R-module. -/
lemma smul_quotientOne (I : Ideal R) (r : R) :
    r • quotientOne I = Submodule.Quotient.mk r := by
  change r • (Submodule.Quotient.mk (1 : R) : R ⧸ (I : Submodule R R)) = _
  rw [← Submodule.Quotient.mk_smul]
  congr 1
  exact mul_one r

/-- Let R be a commutative ring, I an ideal, and M an R-module. If m∈M is killed by every r∈I,
scalar multiplication descends to an R-linear map R/I → M sending [r] to r·m. The condition is
precisely membership in Submodule.torsionBySet R M I. -/
def quotientHomOfAnnihilator (I : Ideal R) (M : Type v)
    [AddCommGroup M] [Module R M] (a : Submodule.torsionBySet R M (I : Set R)) :
    (R ⧸ (I : Submodule R R)) →ₗ[R] M :=
  (I : Submodule R R).liftQ (LinearMap.toSpanSingleton R M a.val) (by
    intro r hr
    rw [LinearMap.mem_ker]
    exact (Submodule.mem_torsionBySet_iff (I : Set R) a.val).mp a.property ⟨r, hr⟩)

/-- For a commutative ring R, ideal I, R-module M, and m annihilated by I, the descended map
satisfies quotientHomOfAnnihilator(I,M,m)([r])=r·m for every r∈R. -/
lemma quotientHomOfAnnihilator_mk (I : Ideal R) (M : Type v)
    [AddCommGroup M] [Module R M] (a : Submodule.torsionBySet R M (I : Set R)) (r : R) :
    quotientHomOfAnnihilator I M a (Submodule.Quotient.mk r) = r • a.val := rfl

/-- Let R be a commutative ring, I an ideal, and M an R-module. Evaluation φ↦φ([1]) is an R-linear
equivalence Hom_R(R/I,M) ≃ₗ[R] M[I], where M[I]={m | ∀r∈I, r·m=0}. Its inverse is [r]↦r·m. No
finiteness or flatness of M is required. -/
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

/-- For a commutative ring R, ideal I, R-module M, and φ : R/I →ₗ[R] M, the underlying value of
quotientHomEquiv(I,M)(φ) equals φ([1]). -/
lemma quotientHomEquiv_val (I : Ideal R) (M : Type v) [AddCommGroup M] [Module R M]
    (φ : (R ⧸ (I : Submodule R R)) →ₗ[R] M) :
    (quotientHomEquiv I M φ).val = φ (quotientOne I) := rfl

/-- Let R be a commutative ring, I an ideal, f : M →ₗ[R] N an R-linear map between independently
sized modules, and φ : R/I →ₗ[R] M. Evaluation of f∘φ at [1] equals f applied to the
annihilator coordinate of φ. Thus
quotientHomEquiv(I,N)(f∘φ).val=f(quotientHomEquiv(I,M)(φ).val). -/
lemma quotientHomEquiv_postcomp_val (I : Ideal R)
    {M : Type v} [AddCommGroup M] [Module R M]
    {N : Type w} [AddCommGroup N] [Module R N] (f : M →ₗ[R] N)
    (φ : (R ⧸ (I : Submodule R R)) →ₗ[R] M) :
    (quotientHomEquiv I N (f.comp φ)).val = f (quotientHomEquiv I M φ).val := rfl

/-- For ideals I≤J in a commutative ring R, let q : R/I → R/J be the induced quotient map and φ :
R/J →ₗ[R] M. Then the annihilator coordinates of φ∘q and φ have the same underlying value
φ([1]). This precomposition corresponds to including M[J] into M[I]. -/
lemma quotientHomEquiv_precomp_val {I J : Ideal R} (h : I ≤ J)
    (M : Type v) [AddCommGroup M] [Module R M]
    (φ : (R ⧸ (J : Submodule R R)) →ₗ[R] M) :
    (quotientHomEquiv I M
      (φ.comp (Submodule.mapQ (I : Submodule R R) (J : Submodule R R)
        (LinearMap.id : R →ₗ[R] R) (by
          rw [Submodule.comap_id]
          exact h)))).val = (quotientHomEquiv J M φ).val := rfl

end Ideal

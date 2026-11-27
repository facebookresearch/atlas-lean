/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import Mathlib.RingTheory.Length
public import Mathlib.RingTheory.OrderOfVanishing.Basic
public import Mathlib.LinearAlgebra.Pi
public import Mathlib.LinearAlgebra.Isomorphisms

/-!
# Scalar cokernels on arbitrary products

Let R be a commutative ring, I any index type and a∈R. Put C_a(I)=R^I/aR^I and C_a=R/aR, with
quotient projections q_I,q. The scalar quotient equivalence Φ:C_a(I)≃ₗ[R](C_a)^I sends [f] to
(i↦[f_i]). For finite I, ℓ_R(C_a(I))=|I|ℓ_R(C_a)=|I|ord_R(a), where ord_R(a)=ℓ_R(R/(a)).
-/

@[expose] public section
noncomputable section

universe u v

namespace LinearMap

variable {R : Type u} [CommRing R] {ι : Type v}

/-- **Product of full scalar quotient modules.**

Let R be a commutative ring, I any index type and a∈R. Put C_a(I)=R^I/aR^I and C_a=R/aR, with
quotient projections q_I,q. The scalar quotient equivalence Φ:C_a(I)≃ₗ[R](C_a)^I sends [f] to
(i↦[f_i]). The map scalarCokernelPiEquiv a is Φ, an R-linear equivalence for arbitrary I.
-/
def scalarCokernelPiEquiv (a : R) :
    ((ι → R) ⧸ (a • (LinearMap.id : (ι → R) →ₗ[R] (ι → R))).range) ≃ₗ[R]
      (ι → (R ⧸ (a • (LinearMap.id : R →ₗ[R] R)).range)) := by
  classical
  let p := (a • (LinearMap.id : R →ₗ[R] R)).range
  let π : (ι → R) →ₗ[R] (ι → (R ⧸ p)) :=
    LinearMap.pi (fun i => p.mkQ.comp (LinearMap.proj i))
  have hk : π.ker = (a • (LinearMap.id : (ι → R) →ₗ[R] (ι → R))).range := by
    ext f
    constructor
    · intro hf
      change π f = 0 at hf
      have h : ∀ i : ι, ∃ r : R, a * r = f i := by
        intro i
        have hi : p.mkQ (f i) = 0 := congrFun hf i
        rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hi
        obtain ⟨r, hr⟩ := hi
        exact ⟨r, hr⟩
      choose g hg using h
      exact ⟨g, funext hg⟩
    · rintro ⟨f, rfl⟩
      change π (a • f) = 0
      funext i
      change p.mkQ (a * f i) = 0
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact ⟨f i, rfl⟩
  have hs : Function.Surjective π := by
    intro q
    choose f hf using (fun i => Submodule.mkQ_surjective p (q i))
    exact ⟨f, funext hf⟩
  exact (Submodule.quotEquivOfEq _ _ hk.symm).trans (π.quotKerEquivOfSurjective hs)

/-- **Scalar quotient equivalence on a product representative.**

Let R be a commutative ring, I any index type and a∈R. Put C_a(I)=R^I/aR^I and C_a=R/aR, with
quotient projections q_I,q. The scalar quotient equivalence Φ:C_a(I)≃ₗ[R](C_a)^I sends [f] to
(i↦[f_i]). For f∈R^I, Φ(q_I(f))(i)=q(f_i).
-/
@[simp] theorem scalarCokernelPiEquiv_apply_mk (a : R) (f : ι → R) :
    scalarCokernelPiEquiv a (Submodule.Quotient.mk f) =
      fun i => (Submodule.Quotient.mk (f i) :
        R ⧸ (a • (LinearMap.id : R →ₗ[R] R)).range) := rfl

/-- **Scalar product quotient map intertwining.**

Let R be a commutative ring, I any index type and a∈R. Put C_a(I)=R^I/aR^I and C_a=R/aR, with
quotient projections q_I,q. The scalar quotient equivalence Φ:C_a(I)≃ₗ[R](C_a)^I sends [f] to
(i↦[f_i]). For f∈R^I, scalarCokernelPiEquiv a (q_I(f))=(i↦q(f_i)).
-/
theorem scalarCokernelPiEquiv_apply_mkQ (a : R) (f : ι → R) :
    scalarCokernelPiEquiv a
        ((a • (LinearMap.id : (ι → R) →ₗ[R] (ι → R))).range.mkQ f) =
      fun i => (a • (LinearMap.id : R →ₗ[R] R)).range.mkQ (f i) := rfl

/-- **Coordinate of the scalar product quotient equivalence.**

Let R be a commutative ring, I any index type and a∈R. Put C_a(I)=R^I/aR^I and C_a=R/aR, with
quotient projections q_I,q. The scalar quotient equivalence Φ:C_a(I)≃ₗ[R](C_a)^I sends [f] to
(i↦[f_i]). For f∈R^I and i∈I, scalarCokernelPiEquiv a (q_I(f)) i=q(f_i).
-/
theorem scalarCokernelPiEquiv_apply_mkQ_apply (a : R) (f : ι → R) (i : ι) :
    scalarCokernelPiEquiv a
        ((a • (LinearMap.id : (ι → R) →ₗ[R] (ι → R))).range.mkQ f) i =
      (a • (LinearMap.id : R →ₗ[R] R)).range.mkQ (f i) :=
  congrFun (scalarCokernelPiEquiv_apply_mkQ a f) i

/-- **Length of a scalar cokernel on a finite product.**

Let R be a commutative ring, I any index type and a∈R. Put C_a(I)=R^I/aR^I and C_a=R/aR, with
quotient projections q_I,q. The scalar quotient equivalence Φ:C_a(I)≃ₗ[R](C_a)^I sends [f] to
(i↦[f_i]). If I is finite, ℓ_R(C_a(I))=|I|ℓ_R(C_a), in ℕ∪{∞}; for empty I the left side is
zero.
-/
theorem length_scalar_coker_pi [Fintype ι] (a : R) :
    Module.length R ((ι → R) ⧸ (a • (LinearMap.id : (ι → R) →ₗ[R] (ι → R))).range) =
      (Fintype.card ι : ℕ∞) * Module.length R (R ⧸ (a • (LinearMap.id : R →ₗ[R] R)).range) := by
  rw [(scalarCokernelPiEquiv (ι := ι) a).length_eq, Module.length_pi_of_fintype]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

/-- **Scalar quotient length is the order of vanishing.**

Let R be a commutative ring and a∈R. Then ℓ_R(R/range(a•id_R))=Ring.ord R a=ℓ_R(R/(a)).
-/
theorem length_scalar_coker_eq_ord (a : R) :
    Module.length R (R ⧸ (a • (LinearMap.id : R →ₗ[R] R)).range) = Ring.ord R a := by
  have hr : (a • (LinearMap.id : R →ₗ[R] R)).range = (Ideal.span {a} : Submodule R R) := by
    ext x
    change (∃ y : R, a * y = x) ↔ x ∈ Ideal.span {a}
    rw [Ideal.mem_span_singleton, dvd_def]
    constructor
    · rintro ⟨y, hy⟩
      exact ⟨y, hy.symm⟩
    · rintro ⟨y, hy⟩
      exact ⟨y, hy.symm⟩
  exact congrArg (fun I : Submodule R R => Module.length R (R ⧸ I)) hr

/-- **Finite scalar cokernel length in a one-dimensional domain.**

Let R be a commutative Noetherian domain with Krull dimension at most one and a≠0. Then
ℓ_R(R/aR) is finite.
-/
theorem length_scalar_coker_ne_top [IsNoetherianRing R] [Ring.KrullDimLE 1 R] [IsDomain R]
    (a : R) (ha : a ≠ 0) :
    Module.length R (R ⧸ (a • (LinearMap.id : R →ₗ[R] R)).range) ≠ ⊤ := by
  rw [length_scalar_coker_eq_ord]
  exact Ring.ord_ne_top (by simpa using ha)

/-- **Order formula for a finite product scalar cokernel.**

Let R be a commutative ring, I any index type and a∈R. Put C_a(I)=R^I/aR^I and C_a=R/aR, with
quotient projections q_I,q. The scalar quotient equivalence Φ:C_a(I)≃ₗ[R](C_a)^I sends [f] to
(i↦[f_i]). For finite I, ℓ_R(C_a(I))=|I|Ring.ord R a, including empty products and unit a.
-/
theorem length_scalar_coker_pi_eq_ord [Fintype ι] (a : R) :
    Module.length R ((ι → R) ⧸ (a • (LinearMap.id : (ι → R) →ₗ[R] (ι → R))).range) =
      (Fintype.card ι : ℕ∞) * Ring.ord R a := by
  rw [length_scalar_coker_pi, length_scalar_coker_eq_ord]

end LinearMap

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
# The full scalar cokernel on arbitrary products

The equivalence is induced by the actual coordinate quotient maps. Every
coordinate lift is earned by quotient surjectivity; no finite-length premise
or radical quotient is used. Finite products then earn the exact scalar
cokernel length required by arbitrary-size pivot elimination.
-/

@[expose] public section
noncomputable section

universe u v

namespace LinearMap

variable {R : Type u} [CommRing R] {ι : Type v}

/-- The literal scalar cokernel on a product is the product of the full
original scalar cokernels, preserving the actual quotient maps. -/
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

/-- The scalar cokernel equivalence sends every original product
representative to its actual coordinate quotient representatives. -/
@[simp] theorem scalarCokernelPiEquiv_apply_mk (a : R) (f : ι → R) :
    scalarCokernelPiEquiv a (Submodule.Quotient.mk f) =
      fun i => (Submodule.Quotient.mk (f i) :
        R ⧸ (a • (LinearMap.id : R →ₗ[R] R)).range) := rfl

/-- The representative law through the actual linear quotient map. -/
theorem scalarCokernelPiEquiv_apply_mkQ (a : R) (f : ι → R) :
    scalarCokernelPiEquiv a
        ((a • (LinearMap.id : (ι → R) →ₗ[R] (ι → R))).range.mkQ f) =
      fun i => (a • (LinearMap.id : R →ₗ[R] R)).range.mkQ (f i) := rfl

/-- The actual quotient representative is preserved at each product coordinate. -/
theorem scalarCokernelPiEquiv_apply_mkQ_apply (a : R) (f : ι → R) (i : ι) :
    scalarCokernelPiEquiv a
        ((a • (LinearMap.id : (ι → R) →ₗ[R] (ι → R))).range.mkQ f) i =
      (a • (LinearMap.id : R →ₗ[R] R)).range.mkQ (f i) :=
  congrFun (scalarCokernelPiEquiv_apply_mkQ a f) i

/-- Every finite product has the full scalar cokernel length equal to its
actual cardinality times the original scalar quotient length, including
the empty product and unit scalar. -/
theorem length_scalar_coker_pi [Fintype ι] (a : R) :
    Module.length R ((ι → R) ⧸ (a • (LinearMap.id : (ι → R) →ₗ[R] (ι → R))).range) =
      (Fintype.card ι : ℕ∞) * Module.length R (R ⧸ (a • (LinearMap.id : R →ₗ[R] R)).range) := by
  rw [(scalarCokernelPiEquiv (ι := ι) a).length_eq, Module.length_pi_of_fintype]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

/-- The literal scalar image is the full principal ideal, so its cokernel
length is the existing order of vanishing without taking a radical. -/
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

/-- The full nonzero scalar quotient has finite length under the actual
one-dimensional Noetherian domain hypotheses; no finite-length premise or
unit-pivot restriction is supplied. -/
theorem length_scalar_coker_ne_top [IsNoetherianRing R] [Ring.KrullDimLE 1 R] [IsDomain R]
    (a : R) (ha : a ≠ 0) :
    Module.length R (R ⧸ (a • (LinearMap.id : R →ₗ[R] R)).range) ≠ ⊤ := by
  rw [length_scalar_coker_eq_ord]
  exact Ring.ord_ne_top (by simpa using ha)

/-- The finite product scalar cokernel retains its full original
one-dimensional order, with exact cardinality and empty-product cases. -/
theorem length_scalar_coker_pi_eq_ord [Fintype ι] (a : R) :
    Module.length R ((ι → R) ⧸ (a • (LinearMap.id : (ι → R) →ₗ[R] (ι → R))).range) =
      (Fintype.card ι : ℕ∞) * Ring.ord R a := by
  rw [length_scalar_coker_pi, length_scalar_coker_eq_ord]

end LinearMap

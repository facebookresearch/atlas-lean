/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import Mathlib.LinearAlgebra.Basis.Submodule
public import Mathlib.RingTheory.Finiteness.Cardinality
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.Localization.Integer

/-!
# A common denominator puts a finite module image in a basis lattice

Let R be a commutative domain, K its fraction field, V a K-vector space with compatible
R-action and finite K-basis b, M a finitely generated R-module and f:M→V R-linear. There
exists a nonzero a∈R with a•f(M)⊆span_R{b_i}.
-/

@[expose] public section
noncomputable section

universe u v w z t

namespace Module.Basis

variable {R : Type u} [CommRing R] [IsDomain R]
variable {K : Type v} [Field K] [Algebra R K] [IsFractionRing R K]
variable {V : Type w} [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]
variable {M : Type z} [AddCommGroup M] [Module R M] [Module.Finite R M]

/-- **Finite module image has a common lattice-clearing scalar.**

Let R be a commutative domain, K its fraction field, V a K-vector space with compatible
R-action, b:I→V a basis with I finite, M finitely generated over R and f:M→V R-linear. Then
∃a∈R, a≠0 and a•f(x)∈span_R(range b) for every x∈M.
-/
theorem exists_scalar_image_mem_span {ι : Type t} [Finite ι]
    (b : Basis ι K V) (f : M →ₗ[R] V) :
    ∃ a : R, a ≠ 0 ∧ ∀ x : M, a • f x ∈ Submodule.span R (Set.range b) := by
  classical
  obtain ⟨n, s, hs⟩ := Module.Finite.exists_fin (R := R) (M := M)
  obtain ⟨a, ha⟩ := IsLocalization.exist_integer_multiples_of_finite
    (nonZeroDivisors R) (fun p : Fin n × ι => b.repr (f (s p.1)) p.2)
  refine ⟨a, mem_nonZeroDivisors_iff_ne_zero.mp a.property, ?_⟩
  let q : Submodule R M := (Submodule.span R (Set.range b)).comap (a.val • f)
  have hgen : ∀ i : Fin n, s i ∈ q := by
    intro i
    change a.val • f (s i) ∈ Submodule.span R (Set.range b)
    apply (b.mem_span_iff_repr_mem R _).mpr
    intro j
    have h := ha (i, j)
    change b.repr.toLinearMap (a.val • f (s i)) j ∈ Set.range (algebraMap R K)
    rw [b.repr.toLinearMap.map_smul_of_tower]
    exact h
  have hq : ⊤ ≤ q := by
    rw [← hs]
    apply Submodule.span_le.mpr
    rintro x ⟨i, rfl⟩
    exact hgen i
  intro x
  exact hq (show x ∈ (⊤ : Submodule R M) from trivial)

end Module.Basis

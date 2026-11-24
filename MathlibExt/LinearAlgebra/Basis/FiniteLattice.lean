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
# Clearing a finite module into the lattice of a field basis

A single nonzero denominator carries the image of a finite module into
the full span over the original domain of a finite fraction-field basis.
The denominator is derived from the actual generator coordinates.
-/

@[expose] public section
noncomputable section

universe u v w z t

namespace Module.Basis

variable {R : Type u} [CommRing R] [IsDomain R]
variable {K : Type v} [Field K] [Algebra R K] [IsFractionRing R K]
variable {V : Type w} [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]
variable {M : Type z} [AddCommGroup M] [Module R M] [Module.Finite R M]

/-- The actual coordinates of a finite generating family earn a common
nonzero scalar carrying its entire image into the original domain span of
a finite fraction-field basis. Neither freeness of the source module nor
normality of the domain is needed. -/
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

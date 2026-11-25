/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
  Author: @toskua, Avocado
-/
module

public import Mathlib.RingTheory.GradedAlgebra.Basic
public import Mathlib.Data.Finset.NatAntidiagonal

/-!
# Projections in internally graded algebras

This file develops a reusable API for homogeneous projections in an internally
graded algebra `A = ⨁ i, 𝒜 i`. It provides general lemmas for homogeneous
projections governing membership, identity, vanishing, finite reconstruction, and
multiplicative behavior, intended for reuse in arbitrary graded-algebra settings
including tensor algebras and related graded constructions.

Main results:

* `GradedAlgebra.proj_mem`: the `i`-th projection lands in `𝒜 i`.
* `GradedAlgebra.proj_eq_self`: projection fixes elements already in its grade.
* `GradedAlgebra.proj_eq_zero_of_ne`: projection vanishes on a distinct grade.
* `GradedAlgebra.sum_support_proj_eq`: every element is the finite sum of its
  homogeneous projections over its decomposition support.
* `GradedAlgebra.exists_finset_sum_proj_eq`: existential finite reconstruction.
* `GradedAlgebra.proj_mul_eq_sum_antidiagonal`: for `ℕ`-graded algebras, the
  projection of a product is the antidiagonal sum of projected factors.

These are direct consequences of the `DirectSum.Decomposition` and
`GradedAlgebra` APIs.
-/

@[expose] public section

open DirectSum Finset

namespace GradedAlgebra

variable {ι : Type*} {R A : Type*} [DecidableEq ι] [AddMonoid ι] [CommSemiring R]
  [Semiring A] [Algebra R A] {𝒜 : ι → Submodule R A} [GradedAlgebra 𝒜]

/-- The homogeneous projection lands in its grade. -/
theorem proj_mem (i : ι) (x : A) : proj 𝒜 i x ∈ 𝒜 i := by
  rw [proj_apply (𝒜 := 𝒜)]
  exact (decompose 𝒜 x i).2

/-- Projection is the identity on elements already in that grade. -/
theorem proj_eq_self {i : ι} {x : A} (hx : x ∈ 𝒜 i) : proj 𝒜 i x = x := by
  rw [proj_apply (𝒜 := 𝒜)]
  exact decompose_of_mem_same 𝒜 hx

/-- Projection is zero on an element lying in a different homogeneous degree. -/
theorem proj_eq_zero_of_ne {i j : ι} {x : A} (hx : x ∈ 𝒜 i) (hij : i ≠ j) :
    proj 𝒜 j x = 0 := by
  rw [proj_apply (𝒜 := 𝒜)]
  exact decompose_of_mem_ne 𝒜 hx hij

open Classical in
/-- Every element is the finite sum of its homogeneous projections over its
decomposition support. -/
theorem sum_support_proj_eq (x : A) :
    (∑ i ∈ (decompose 𝒜 x).support, proj 𝒜 i x) = x := by
  classical
  have h_eq : ∀ i, proj 𝒜 i x = (decompose 𝒜 x i : A) := by
    intro i
    exact proj_apply (𝒜 := 𝒜) i x
  simp_rw [h_eq]
  exact sum_support_decompose 𝒜 x

open Classical in
/-- Every element equals a finite sum of its homogeneous projections. -/
theorem exists_finset_sum_proj_eq (x : A) :
    ∃ s : Finset ι, (∑ i ∈ s, proj 𝒜 i x) = x := by
  classical
  exact ⟨(decompose 𝒜 x).support, sum_support_proj_eq (𝒜 := 𝒜) x⟩

variable {𝒜 : ℕ → Submodule R A} [GradedAlgebra 𝒜]

/-- For an `ℕ`-graded algebra, projection of a product is the antidiagonal sum
of projected factors. -/
theorem proj_mul_eq_sum_antidiagonal (a b : A) (n : ℕ) :
    proj 𝒜 n (a * b) =
      ∑ ij ∈ antidiagonal n, proj 𝒜 ij.1 a * proj 𝒜 ij.2 b := by
  classical
  have h_proj_eq : ∀ (x : A) (k : ℕ), proj 𝒜 k x = (decompose 𝒜 x k : A) := by
    intro x k
    exact proj_apply (𝒜 := 𝒜) k x
  calc proj 𝒜 n (a * b)
      = (decompose 𝒜 (a * b) n : A) := by
        rw [h_proj_eq]
      _ = ((decompose 𝒜 a * decompose 𝒜 b) n : A) := by
        rw [decompose_mul]
      _ = ∑ ij ∈ antidiagonal n,
          (decompose 𝒜 a ij.1 : A) * (decompose 𝒜 b ij.2 : A) := by
        exact coe_mul_apply_eq_sum_antidiagonal (A := 𝒜) (R := A)
          (decompose 𝒜 a) (decompose 𝒜 b) n
      _ = ∑ ij ∈ antidiagonal n, proj 𝒜 ij.1 a * proj 𝒜 ij.2 b := by
        apply Finset.sum_congr rfl
        intro ij _
        rw [h_proj_eq, h_proj_eq]

end GradedAlgebra

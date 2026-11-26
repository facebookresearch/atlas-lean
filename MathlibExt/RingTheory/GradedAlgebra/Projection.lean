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
# Homogeneous projections in an internally graded semiring algebra

Let R be a commutative semiring, A a semiring R-algebra and A=⨁_{i∈ι}𝒜_i an internal grading by
an additive monoid with decidable equality. The projection π_i:A→A lands in 𝒜_i, fixes elements
of that grade and is zero on an element of a different grade. Every element is the finite sum of
its projections over its decomposition support.

For a natural-number grading, π_n(ab)=∑_{p+q=n}π_p(a)π_q(b). The antidiagonal is finite, and the
order of the two factors is retained; A need not be commutative or have additive inverses.
-/

@[expose] public section

open DirectSum Finset

namespace GradedAlgebra

variable {ι : Type*} {R A : Type*} [DecidableEq ι] [AddMonoid ι] [CommSemiring R]
  [Semiring A] [Algebra R A] {𝒜 : ι → Submodule R A} [GradedAlgebra 𝒜]

/-- Let R be a commutative semiring, A a semiring R-algebra and A=⨁_{i∈ι}𝒜_i an internal grading by
an additive monoid ι with decidable equality. For i∈ι and x∈A, π_i(x)∈𝒜_i. The projection is the
grade-i component of the internal direct-sum decomposition. -/
theorem proj_mem (i : ι) (x : A) : proj 𝒜 i x ∈ 𝒜 i := by
  rw [proj_apply (𝒜 := 𝒜)]
  exact (decompose 𝒜 x i).2

/-- Let R be a commutative semiring, A a semiring R-algebra and A=⨁_{i∈ι}𝒜_i an internal grading by
an additive monoid ι with decidable equality. If x∈𝒜_i, then π_i(x)=x. The internal
decomposition has x as its grade-i component. -/
theorem proj_eq_self {i : ι} {x : A} (hx : x ∈ 𝒜 i) : proj 𝒜 i x = x := by
  rw [proj_apply (𝒜 := 𝒜)]
  exact decompose_of_mem_same 𝒜 hx

/-- Let R be a commutative semiring, A a semiring R-algebra and A=⨁_{i∈ι}𝒜_i an internal grading by
an additive monoid ι with decidable equality. For x∈𝒜_i and i≠j, π_j(x)=0. The homogeneous
decomposition of x is supported at its own grade. -/
theorem proj_eq_zero_of_ne {i j : ι} {x : A} (hx : x ∈ 𝒜 i) (hij : i ≠ j) :
    proj 𝒜 j x = 0 := by
  rw [proj_apply (𝒜 := 𝒜)]
  exact decompose_of_mem_ne 𝒜 hx hij

open Classical in
/-- Let R be a commutative semiring, A a semiring R-algebra and A=⨁_{i∈ι}𝒜_i an internal grading by
an additive monoid ι with decidable equality. For x∈A, let supp(x) be the finite support of its
direct-sum decomposition. Then ∑_{i∈supp(x)}π_i(x)=x. No finiteness condition on the whole
grading monoid is required. -/
theorem sum_support_proj_eq (x : A) :
    (∑ i ∈ (decompose 𝒜 x).support, proj 𝒜 i x) = x := by
  classical
  have h_eq : ∀ i, proj 𝒜 i x = (decompose 𝒜 x i : A) := by
    intro i
    exact proj_apply (𝒜 := 𝒜) i x
  simp_rw [h_eq]
  exact sum_support_decompose 𝒜 x

open Classical in
/-- Let R be a commutative semiring, A a semiring R-algebra and A=⨁_{i∈ι}𝒜_i an internal grading by
an additive monoid ι with decidable equality. For x∈A there is a finite set s⊂ι such that
∑_{i∈s}π_i(x)=x. The decomposition support provides such a set. -/
theorem exists_finset_sum_proj_eq (x : A) :
    ∃ s : Finset ι, (∑ i ∈ s, proj 𝒜 i x) = x := by
  classical
  exact ⟨(decompose 𝒜 x).support, sum_support_proj_eq (𝒜 := 𝒜) x⟩

variable {𝒜 : ℕ → Submodule R A} [GradedAlgebra 𝒜]

/-- Let R be a commutative semiring and A a semiring R-algebra with an internal ℕ-grading 𝒜. For
a,b∈A and n∈ℕ, π_n(ab)=∑_{p+q=n}π_p(a)π_q(b). The finite antidiagonal sum retains the order of a
and b, and neither commutativity of A nor additive inverses are assumed. -/
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

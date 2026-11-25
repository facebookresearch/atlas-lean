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

public import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Submodule
public import Mathlib.Algebra.Module.GradedModule
public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.Algebra.Exact.Basic

/-!
# Fixed-degree pieces of a quotient by a homogeneous submodule

For a graded algebra `S`, a graded `S`-module `M`, and a homogeneous
submodule `N`, this file defines the inherited degree pieces on `N` and the
image degree pieces on the canonical quotient `M ⧸ N.toSubmodule`.  It
also records the component inclusion, quotient map, short exactness, and
graded scalar-action laws.

The constructions here are fixed-degree: they do not choose direct-sum
decompositions of the submodule or quotient.

## Main declarations

* `HomogeneousSubmodule.grade`
* `HomogeneousSubmodule.quotientGrade`
* `HomogeneousSubmodule.gradeInclusion`
* `HomogeneousSubmodule.gradeQuotient`
* `HomogeneousSubmodule.grade_exact`
-/

@[expose] public section

set_option autoImplicit false

namespace HomogeneousSubmodule

universe u v w

variable {A : Type u} [CommRing A]
variable {S : Type v} [CommRing S] [Algebra A S]
variable {M : Type w} [AddCommGroup M]
  [Module A M] [Module S M] [IsScalarTower A S M]

variable (Sgrade : ℕ → Submodule A S) [GradedAlgebra Sgrade]
variable (Mgrade : ℕ → Submodule A M)
  [SetLike.GradedSMul Sgrade Mgrade]
  [DirectSum.Decomposition Mgrade]

variable (N : HomogeneousSubmodule Sgrade Mgrade)

/-- The degree-`n` piece inherited by a homogeneous submodule. -/
def grade (n : ℕ) : Submodule A N.toSubmodule :=
  (Mgrade n).comap ((N.toSubmodule.subtype).restrictScalars A)

/-- Membership in the inherited degree piece is membership of the ambient
carrier in the corresponding degree piece of `M`. -/
@[simp]
theorem mem_grade_iff (n : ℕ) (x : N.toSubmodule) :
    x ∈ N.grade Sgrade Mgrade n ↔ (x : M) ∈ Mgrade n :=
  Iff.rfl

/-- The degree-`n` piece of the quotient is the image of the ambient
degree-`n` piece under the canonical quotient map. -/
def quotientGrade (n : ℕ) : Submodule A (M ⧸ N.toSubmodule) :=
  (Mgrade n).map ((N.toSubmodule.mkQ).restrictScalars A)

/-- A quotient class lies in degree `n` exactly when it has a representative
in the ambient degree-`n` piece. -/
@[simp]
theorem mem_quotientGrade_iff (n : ℕ) (q : M ⧸ N.toSubmodule) :
    q ∈ N.quotientGrade Sgrade Mgrade n ↔
      ∃ x : Mgrade n, N.toSubmodule.mkQ (x : M) = q := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨⟨x, hx⟩, rfl⟩
  · rintro ⟨x, rfl⟩
    exact ⟨x, x.2, rfl⟩

/-- The inclusion of the inherited degree-`n` piece into the ambient
degree-`n` piece. -/
def gradeInclusion (n : ℕ) :
    N.grade Sgrade Mgrade n →ₗ[A] Mgrade n :=
  (((N.toSubmodule.subtype).restrictScalars A).domRestrict
    (N.grade Sgrade Mgrade n)).codRestrict (Mgrade n) (fun x ↦ x.2)

/-- The component inclusion agrees with the underlying subtype inclusion. -/
@[simp]
theorem gradeInclusion_apply (n : ℕ)
    (x : N.grade Sgrade Mgrade n) :
    N.gradeInclusion Sgrade Mgrade n x = ⟨(x : N.toSubmodule), x.2⟩ :=
  rfl

/-- The component inclusion is injective. -/
theorem gradeInclusion_injective (n : ℕ) :
    Function.Injective (N.gradeInclusion Sgrade Mgrade n) := by
  intro x y h
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg (fun z : Mgrade n ↦ (z : M)) h

/-- The canonical projection from the ambient degree-`n` piece onto the
degree-`n` quotient piece. -/
def gradeQuotient (n : ℕ) :
    Mgrade n →ₗ[A] N.quotientGrade Sgrade Mgrade n :=
  (((N.toSubmodule.mkQ).restrictScalars A).domRestrict (Mgrade n)).codRestrict
    (N.quotientGrade Sgrade Mgrade n) (fun x ↦ ⟨x, x.2, rfl⟩)

/-- The component quotient map agrees with the canonical quotient map. -/
@[simp]
theorem gradeQuotient_apply (n : ℕ) (x : Mgrade n) :
    (N.gradeQuotient Sgrade Mgrade n x : M ⧸ N.toSubmodule) =
      N.toSubmodule.mkQ (x : M) :=
  rfl

/-- The component quotient map is surjective onto its image piece. -/
theorem gradeQuotient_surjective (n : ℕ) :
    Function.Surjective (N.gradeQuotient Sgrade Mgrade n) := by
  rintro ⟨q, x, hx, rfl⟩
  exact ⟨⟨x, hx⟩, rfl⟩

/-- In each degree, the inherited submodule piece, ambient piece, and
quotient piece form an exact sequence. -/
theorem grade_exact (n : ℕ) :
    Function.Exact (N.gradeInclusion Sgrade Mgrade n)
      (N.gradeQuotient Sgrade Mgrade n) := by
  rw [LinearMap.exact_iff]
  apply le_antisymm
  · intro x hx
    have hxsub : N.gradeQuotient Sgrade Mgrade n x = 0 :=
      LinearMap.mem_ker.mp hx
    have hx0 : N.toSubmodule.mkQ (x : M) = 0 := by
      have := congrArg
        (fun z : N.quotientGrade Sgrade Mgrade n ↦
          (z : M ⧸ N.toSubmodule)) hxsub
      simpa using this
    have hxN : (x : M) ∈ N.toSubmodule :=
      (Submodule.Quotient.mk_eq_zero N.toSubmodule).mp hx0
    exact ⟨⟨⟨(x : M), hxN⟩, x.2⟩, rfl⟩
  · intro x hx
    rcases hx with ⟨y, rfl⟩
    apply LinearMap.mem_ker.mpr
    apply Subtype.ext
    exact (Submodule.Quotient.mk_eq_zero N.toSubmodule).mpr y.1.2

/-- The inherited degree pieces are stable under the graded scalar action. -/
instance gradeGradedSMul :
    SetLike.GradedSMul Sgrade (N.grade Sgrade Mgrade) where
  smul_mem := by
    intro i j s x hs hx
    change (s • (x : M)) ∈ Mgrade (i + j)
    exact SetLike.GradedSMul.smul_mem (A := Sgrade) (B := Mgrade) hs hx

/-- The image degree pieces on the quotient are stable under the graded
scalar action. -/
instance quotientGradeGradedSMul :
    SetLike.GradedSMul Sgrade (N.quotientGrade Sgrade Mgrade) where
  smul_mem := by
    intro i j s q hs hq
    rcases hq with ⟨x, hx, rfl⟩
    refine ⟨s • x, SetLike.GradedSMul.smul_mem hs hx, ?_⟩
    simp

end HomogeneousSubmodule

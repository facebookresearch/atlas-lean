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
# Degree pieces of a homogeneous submodule quotient

Let S be a graded commutative algebra over a commutative ring A, M an S-module with compatible
A-action, and M = ⨁ₙM_n an internal decomposition compatible with the graded S-action. For a
homogeneous S-submodule H, its inherited grade H_n consists of the elements of H whose
underlying value belongs to M_n. In the quotient Q = M/H, define Q_n as the image of M_n under
q : M → Q.

The inclusion H_n → M_n and projection M_n → Q_n are A-linear, injective and surjective
respectively, and form an exact sequence 0 → H_n → M_n → Q_n → 0. Both inherited and quotient
families satisfy S_i • H_j ⊆ H_{i+j} and S_i • Q_j ⊆ Q_{i+j}. The coefficient, algebra and
module universes are independent.
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

/-- Inherited degree piece of a homogeneous submodule.

For a homogeneous submodule H of a graded S-module M over A, define H_n as the preimage of M_n
under the A-linear inclusion H → M. It is an A-submodule of H. -/
def grade (n : ℕ) : Submodule A N.toSubmodule :=
  (Mgrade n).comap ((N.toSubmodule.subtype).restrictScalars A)

/-- Membership in an inherited homogeneous degree piece.

For x ∈ H, membership x ∈ H_n is equivalent to its underlying value in M belonging to M_n.
Here H is a homogeneous S-submodule and all pieces are A-submodules. -/
@[simp]
theorem mem_grade_iff (n : ℕ) (x : N.toSubmodule) :
    x ∈ N.grade Sgrade Mgrade n ↔ (x : M) ∈ Mgrade n :=
  Iff.rfl

/-- Image degree piece on a homogeneous module quotient.

For Q = M/H with H homogeneous, define Q_n = q(M_n) under the A-linear canonical quotient q :
M → M/H. This is an A-submodule of the quotient. -/
def quotientGrade (n : ℕ) : Submodule A (M ⧸ N.toSubmodule) :=
  (Mgrade n).map ((N.toSubmodule.mkQ).restrictScalars A)

/-- Homogeneous representative criterion for a quotient grade.

A class y ∈ M/H belongs to Q_n exactly when there exists x ∈ M_n with q(x) = y. Thus the
quotient grade is described by homogeneous representatives of degree n. -/
@[simp]
theorem mem_quotientGrade_iff (n : ℕ) (q : M ⧸ N.toSubmodule) :
    q ∈ N.quotientGrade Sgrade Mgrade n ↔
      ∃ x : Mgrade n, N.toSubmodule.mkQ (x : M) = q := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨⟨x, hx⟩, rfl⟩
  · rintro ⟨x, rfl⟩
    exact ⟨x, x.2, rfl⟩

/-- Inclusion of an inherited submodule grade into the ambient grade.

For a homogeneous H ⊆ M, restrict its inclusion to obtain the A-linear map H_n → M_n. It sends
an element to the same underlying value in M. -/
def gradeInclusion (n : ℕ) :
    N.grade Sgrade Mgrade n →ₗ[A] Mgrade n :=
  (((N.toSubmodule.subtype).restrictScalars A).domRestrict
    (N.grade Sgrade Mgrade n)).codRestrict (Mgrade n) (fun x ↦ x.2)

/-- Value of the inherited grade inclusion.

For x ∈ H_n, gradeInclusion maps x to its underlying element of M, equipped with its
membership in M_n. Both nested subtype values retain the given inclusion H → M. -/
@[simp]
theorem gradeInclusion_apply (n : ℕ)
    (x : N.grade Sgrade Mgrade n) :
    N.gradeInclusion Sgrade Mgrade n x = ⟨(x : N.toSubmodule), x.2⟩ :=
  rfl

/-- Injectivity of the inherited grade inclusion.

For every n, the A-linear map H_n → M_n induced by the inclusion H → M is injective. -/
theorem gradeInclusion_injective (n : ℕ) :
    Function.Injective (N.gradeInclusion Sgrade Mgrade n) := by
  intro x y h
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg (fun z : Mgrade n ↦ (z : M)) h

/-- Projection from an ambient grade to its quotient grade.

For homogeneous H ⊆ M and Q = M/H, restrict the canonical quotient q to M_n and its image Q_n.
This defines the A-linear map M_n → Q_n. -/
def gradeQuotient (n : ℕ) :
    Mgrade n →ₗ[A] N.quotientGrade Sgrade Mgrade n :=
  (((N.toSubmodule.mkQ).restrictScalars A).domRestrict (Mgrade n)).codRestrict
    (N.quotientGrade Sgrade Mgrade n) (fun x ↦ ⟨x, x.2, rfl⟩)

/-- Value of the degreewise quotient projection.

For x ∈ M_n, the value of gradeQuotient, viewed in M/H, is the canonical quotient class q(x). -/
@[simp]
theorem gradeQuotient_apply (n : ℕ) (x : Mgrade n) :
    (N.gradeQuotient Sgrade Mgrade n x : M ⧸ N.toSubmodule) =
      N.toSubmodule.mkQ (x : M) :=
  rfl

/-- Surjectivity onto the image quotient grade.

For each n, the degreewise quotient M_n → Q_n is surjective, since Q_n is defined as the image
of M_n under the canonical quotient. -/
theorem gradeQuotient_surjective (n : ℕ) :
    Function.Surjective (N.gradeQuotient Sgrade Mgrade n) := by
  rintro ⟨q, x, hx, rfl⟩
  exact ⟨⟨x, hx⟩, rfl⟩

/-- Exactness of inherited and quotient degree maps.

For homogeneous H ⊆ M, the A-linear pair H_n → M_n → Q_n is exact at M_n. A degree-n element
has zero quotient class exactly when it lies in H_n. -/
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

/-- Graded scalar action on inherited submodule pieces.

For the graded S-module M and homogeneous S-submodule H, multiplication by s ∈ S_i sends H_j
into H_{i+j}. Membership in H follows from its S-submodule structure, and degree membership
follows from the graded action on M. -/
instance gradeGradedSMul :
    SetLike.GradedSMul Sgrade (N.grade Sgrade Mgrade) where
  smul_mem := by
    intro i j s x hs hx
    change (s • (x : M)) ∈ Mgrade (i + j)
    exact SetLike.GradedSMul.smul_mem (A := Sgrade) (B := Mgrade) hs hx

/-- Graded scalar action on quotient image pieces.

For Q = M/H and Q_j = q(M_j), multiplication by s ∈ S_i sends Q_j into Q_{i+j}. Choose a
degree-j representative and multiply it in M, then use the quotient's S-linear action. -/
instance quotientGradeGradedSMul :
    SetLike.GradedSMul Sgrade (N.quotientGrade Sgrade Mgrade) where
  smul_mem := by
    intro i j s q hs hq
    rcases hq with ⟨x, hx, rfl⟩
    refine ⟨s • x, SetLike.GradedSMul.smul_mem hs hx, ?_⟩
    simp

end HomogeneousSubmodule

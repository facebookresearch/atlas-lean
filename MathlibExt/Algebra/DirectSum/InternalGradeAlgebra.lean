/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


-- Author: @toskua, Avocado
module

public import MathlibExt.Algebra.DirectSum.InternalGrade
public import Mathlib.Algebra.Module.GradedModule
public import Mathlib.RingTheory.GradedAlgebra.Basic

/-!
# Internal coordinate gradings of graded algebras

For a graded R-algebra A over a commutative semiring, the ranges of the homogeneous inclusions
into ⨁ i, A i are submodules for the R-action of the total algebra. Their summation map is an
isomorphism, the unit belongs to degree zero, and multiplication sends degrees i and j to
degree i + j. They therefore give an internal graded algebra.

If a graded A-module M is indexed by an I-set J, these algebra components act on the
coordinate submodules of ⨁ j, M j, sending degrees i and j to i +ᵥ j. The module-valued
specialization is also given over a commutative ring.

See Bourbaki, *Algebra*, Chapters II and III, for direct sums and graded algebras.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace DirectSum

universe uR uI uA uJ uM

variable (R : Type uR) [CommSemiring R]
variable {I : Type uI} [DecidableEq I] [AddMonoid I]
variable (A : I → Type uA)
  [∀ i, AddCommMonoid (A i)] [∀ i, Module R (A i)]
variable [DirectSum.GSemiring A] [DirectSum.GAlgebra R A]

/-- Let R be a commutative semiring, I an additive monoid with decidable equality, and A i a
family of R-semimodules forming a graded semiring and graded R-algebra. The submodule
algebraInternalGrade R A i of ⨁ j, A j is the range of DirectSum.lof R I A i, using the
R-module structure induced by the total algebra. Its elements are exactly those supported at
i. -/
noncomputable def algebraInternalGrade (i : I) :
    @Submodule R (DirectSum I A) _ _
      (@Algebra.toModule R (DirectSum I A) _ _
        (DirectSum.instAlgebra R A)) :=
  LinearMap.range (DirectSum.lof R I A i)

/-- Let R be a commutative semiring, I an additive monoid with decidable equality, and A i a
family of R-semimodules forming a graded semiring and graded R-algebra. The family
algebraInternalGrade R A has an internal direct-sum decomposition of ⨁ i, A i: summing the
coordinate inclusions is inverse to the decomposition by external coordinates. -/
noncomputable instance algebraInternalGradeDecomposition :
    DirectSum.Decomposition (algebraInternalGrade R A) := by
  change DirectSum.Decomposition (internalGrade R I A)
  infer_instance

/-- Let R be a commutative semiring, I an additive monoid with decidable equality, and A i a
family of R-semimodules forming a graded semiring and graded R-algebra. For x : ⨁ j, A j and i
: I, membership x ∈ algebraInternalGrade R A i is equivalent to the existence of y : A i with
DirectSum.of A i y = x. -/
@[simp]
theorem mem_algebraInternalGrade_iff (x : DirectSum I A) (i : I) :
    x ∈ algebraInternalGrade R A i ↔
      ∃ y : A i, DirectSum.of A i y = x := by
  change x ∈ internalGrade R I A i ↔ _
  exact mem_internalGrade_iff R I A x i

/-- Let R be a commutative semiring, I an additive monoid with decidable equality, and A i a
family of R-semimodules forming a graded semiring and graded R-algebra. The i-th component of
DirectSum.decompose (algebraInternalGrade R A) x, coerced into ⨁ j, A j, equals DirectSum.of A
i (x i). -/
@[simp]
theorem coe_decompose_algebraInternalGrade
    (x : DirectSum I A) (i : I) :
    ((DirectSum.decompose (algebraInternalGrade R A) x i :
        algebraInternalGrade R A i) : DirectSum I A) =
      DirectSum.of A i (x i) := by
  change ((DirectSum.decompose (internalGrade R I A) x i :
    internalGrade R I A i) : DirectSum I A) = _
  exact coe_decompose_internalGrade R I A x i

/-- Let R be a commutative semiring, I an additive monoid with decidable equality, and A i a
family of R-semimodules forming a graded semiring and graded R-algebra. The coordinate
submodules algebraInternalGrade R A form a graded algebra decomposition of the total R-algebra
⨁ i, A i. Its unit lies in degree 0, and multiplication sends the degree-i and degree-j
submodules into degree i + j. -/
noncomputable instance algebraInternalGradeGradedAlgebra :
    GradedAlgebra (algebraInternalGrade R A) := by
  letI : DirectSum.Decomposition (algebraInternalGrade R A) :=
    algebraInternalGradeDecomposition R A
  letI : SetLike.GradedMonoid (algebraInternalGrade R A) := {
    one_mem := by
      rw [mem_algebraInternalGrade_iff]
      exact ⟨GradedMonoid.GOne.one, (DirectSum.one_def A).symm⟩
    mul_mem := by
      intro i j x y hx hy
      rw [mem_algebraInternalGrade_iff] at hx hy ⊢
      obtain ⟨a, rfl⟩ := hx
      obtain ⟨b, rfl⟩ := hy
      exact ⟨GradedMonoid.GMul.mul a b,
        (DirectSum.of_mul_of a b).symm⟩
  }
  exact GradedRing.mk

variable {J : Type uJ} [DecidableEq J] [AddAction I J]
variable (M : J → Type uM)
  [∀ j, AddCommMonoid (M j)] [∀ j, Module R (M j)]
variable [DirectSum.Gmodule A M]

/-- Let R be a commutative semiring, I an additive monoid with decidable equality, and A i a
family of R-semimodules forming a graded semiring and graded R-algebra. Let J be an I-set with
decidable equality and M j a family of R-semimodules forming a graded A-module. An element of
algebraInternalGrade R A i acting on an element of internalGrade R J M j yields an element of
internalGrade R J M (i +ᵥ j); on homogeneous inclusions the action is inclusion of the graded
scalar product. -/
instance algebraInternalGradeGradedSMul :
    SetLike.GradedSMul
      (algebraInternalGrade R A)
      (internalGrade R J M) := by
  refine { smul_mem := ?_ }
  intro i j x y hx hy
  rw [mem_algebraInternalGrade_iff] at hx
  rw [mem_internalGrade_iff] at hy ⊢
  obtain ⟨a, rfl⟩ := hx
  obtain ⟨m, rfl⟩ := hy
  exact ⟨GradedMonoid.GSMul.smul a m,
    (DirectSum.Gmodule.of_smul_of A M a m).symm⟩

end DirectSum

namespace DirectSum

section Module

universe uR uI uA uJ uM

variable (R : Type uR) [CommRing R]
variable {I : Type uI} [DecidableEq I] [AddMonoid I]
variable (A : I → Type uA)
  [∀ i, AddCommMonoid (A i)] [∀ i, Module R (A i)]
variable [DirectSum.GSemiring A] [DirectSum.GAlgebra R A]
variable {J : Type uJ} [DecidableEq J] [AddAction I J]
variable (M : J → Type uM)
  [∀ j, AddCommGroup (M j)] [∀ j, Module R (M j)]
variable [DirectSum.Gmodule A M]

/-- Let R be a commutative ring, I an additive monoid and J an I-set, both with decidable
equality. Let the R-semimodules A i form a graded semiring and graded R-algebra, and let the
R-modules M j form a graded A-module. Then algebraInternalGrade R A i acts on
internalGrade R J M j into internalGrade R J M (i +ᵥ j), with the action induced
by the homogeneous scalar products. -/
instance algebraInternalGradeModuleInternalGradeGradedSMul :
    SetLike.GradedSMul
      (algebraInternalGrade R A)
      (internalGrade R J M) := by
  refine { smul_mem := ?_ }
  intro i j x y hx hy
  rw [mem_algebraInternalGrade_iff] at hx
  rw [mem_internalGrade_iff] at hy ⊢
  obtain ⟨a, rfl⟩ := hx
  obtain ⟨m, rfl⟩ := hy
  exact ⟨GradedMonoid.GSMul.smul a m,
    (DirectSum.Gmodule.of_smul_of A M a m).symm⟩

end Module

end DirectSum

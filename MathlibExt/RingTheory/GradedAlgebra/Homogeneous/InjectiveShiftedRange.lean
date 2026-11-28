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

public import MathlibExt.RingTheory.GradedAlgebra.Homogeneous.ShiftedLinearMap

/-!
# Source grades and ranges of injective shifted maps

Let S be a graded algebra over a commutative ring A. Let M,N be S-modules with compatible
A-actions and internal decompositions M = ⨁ₙM_n, N = ⨁ₙN_n, with the graded S-action on N. An
S-linear map f of degree d satisfies f(M_n) ⊆ N_{d+n}, and its range is a homogeneous
S-submodule of N.

If f is injective, restriction gives an A-linear equivalence M_n ≃ (Im f)_{d+n}, where the
range grade is inherited from N. It sends x to f(x). Transporting the range inclusion through
this equivalence gives the exact pair M_n → N_{d+n} → (N/Im f)_{d+n}. The coefficient, algebra
and two module universes are independent.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace GradedModule.IsHomogeneousOfDegree

universe uA uS uM uN

variable {A : Type uA} [CommRing A]
variable {S : Type uS} [CommRing S] [Algebra A S]
variable {M : Type uM} [AddCommGroup M]
  [Module A M] [Module S M] [IsScalarTower A S M]
variable {N : Type uN} [AddCommGroup N]
  [Module A N] [Module S N] [IsScalarTower A S N]

variable (Sgrade : ℕ → Submodule A S) [GradedAlgebra Sgrade]
variable (Mgrade : ℕ → Submodule A M) [DirectSum.Decomposition Mgrade]
variable (Ngrade : ℕ → Submodule A N)
  [SetLike.GradedSMul Sgrade Ngrade]
  [DirectSum.Decomposition Ngrade]
variable {d : ℕ} {f : M →ₗ[S] N}
variable (hf : GradedModule.IsHomogeneousOfDegree Mgrade Ngrade d f)

private def rangeGradeMap (n : ℕ) :
    Mgrade n →ₗ[A]
      (hf.rangeHomogeneousSubmodule Sgrade).grade
        Sgrade Ngrade (d + n) where
  toFun x := ⟨⟨f x, ⟨x, rfl⟩⟩, hf n x.property⟩
  map_add' x y := by
    apply Subtype.ext
    apply Subtype.ext
    exact f.map_add x y
  map_smul' a x := by
    apply Subtype.ext
    apply Subtype.ext
    exact f.map_smul_of_tower a x

private theorem rangeGradeMap_injective
    (hinj : Function.Injective f) (n : ℕ) :
    Function.Injective (rangeGradeMap Sgrade Mgrade Ngrade hf n) := by
  intro x y hxy
  apply Subtype.ext
  apply hinj
  exact congrArg (fun q => (q.1.1 : N)) hxy

private theorem rangeGradeMap_surjective (n : ℕ) :
    Function.Surjective (rangeGradeMap Sgrade Mgrade Ngrade hf n) := by
  intro y
  obtain ⟨x, hx⟩ := y.1.2
  refine ⟨DirectSum.decompose Mgrade x n, ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  change f (DirectSum.decompose Mgrade x n : M) = (y.1.1 : N)
  rw [← hf.coe_decompose_apply_add x n, hx]
  exact DirectSum.decompose_of_mem_same Ngrade y.2

/-- Equivalence from a source grade to an injective shifted range grade.

Let f : M →ₗ[S] N be injective and homogeneous of degree d, with internally decomposed
A-submodule families and a compatible graded S-action on N. Restriction of f gives M_n ≃ₗ[A]
(Im f)_{d+n}, where the latter is the inherited degree piece of the homogeneous range
submodule. -/
@[no_expose]
noncomputable def rangeGradeEquiv
    (hinj : Function.Injective f) (n : ℕ) :
    Mgrade n ≃ₗ[A]
      (hf.rangeHomogeneousSubmodule Sgrade).grade
        Sgrade Ngrade (d + n) :=
  LinearEquiv.ofBijective (rangeGradeMap Sgrade Mgrade Ngrade hf n)
    ⟨rangeGradeMap_injective Sgrade Mgrade Ngrade hf hinj n,
      rangeGradeMap_surjective Sgrade Mgrade Ngrade hf n⟩

/-- Underlying value of the shifted range-grade equivalence.

For an injective degree-d map f and x ∈ M_n, its rangeGradeEquiv image, viewed in N, is f(x).
The equivalence lands in the inherited range grade of degree d+n. -/
@[simp]
theorem coe_rangeGradeEquiv_apply
    (hinj : Function.Injective f) (n : ℕ) (x : Mgrade n) :
    ((((rangeGradeEquiv Sgrade Mgrade Ngrade hf hinj n) x :
        (hf.rangeHomogeneousSubmodule Sgrade).toSubmodule) : N)) =
      f (x : M) := by
  rfl

/-- Exact component pair for an injective shifted map.

For an injective homogeneous S-linear map f of degree d, the map M_n → N_{d+n} obtained from
rangeGradeEquiv and range inclusion is exact with the quotient map N_{d+n} → (N/Im f)_{d+n}.
The statement is exactness at the target grade N_{d+n}, using its homogeneous range. -/
theorem rangeGrade_exact
    (hinj : Function.Injective f) (n : ℕ) :
    Function.Exact
      (((hf.rangeHomogeneousSubmodule Sgrade).gradeInclusion
          Sgrade Ngrade (d + n)).comp
        (rangeGradeEquiv Sgrade Mgrade Ngrade hf hinj n).toLinearMap)
      ((hf.rangeHomogeneousSubmodule Sgrade).gradeQuotient
        Sgrade Ngrade (d + n)) := by
  rw [LinearEquiv.precomp_exact_iff_exact]
  exact (hf.rangeHomogeneousSubmodule Sgrade).grade_exact
    Sgrade Ngrade (d + n)

end GradedModule.IsHomogeneousOfDegree

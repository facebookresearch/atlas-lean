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
# Injective shifted maps identify source grades with range grades

An injective degree-`d` linear map identifies the source component in degree
`n` with the inherited component of its homogeneous range in degree `d+n`.
Transporting the existing fixed-degree range/ambient/quotient exact sequence
through this equivalence gives the component exact sequence with source
`M_n`.

This file contains no length, finiteness, Noetherian, Hilbert--Serre,
power-kernel, or associated-graded specialization.

## Main declarations

* `GradedModule.IsHomogeneousOfDegree.rangeGradeEquiv`
* `GradedModule.IsHomogeneousOfDegree.coe_rangeGradeEquiv_apply`
* `GradedModule.IsHomogeneousOfDegree.rangeGrade_exact`
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

/-- An injective degree-`d` map identifies source degree `n` with degree
`d+n` in its inherited homogeneous range. -/
@[no_expose]
noncomputable def rangeGradeEquiv
    (hinj : Function.Injective f) (n : ℕ) :
    Mgrade n ≃ₗ[A]
      (hf.rangeHomogeneousSubmodule Sgrade).grade
        Sgrade Ngrade (d + n) :=
  LinearEquiv.ofBijective (rangeGradeMap Sgrade Mgrade Ngrade hf n)
    ⟨rangeGradeMap_injective Sgrade Mgrade Ngrade hf hinj n,
      rangeGradeMap_surjective Sgrade Mgrade Ngrade hf n⟩

/-- The range-grade equivalence is induced by the original linear map. -/
@[simp]
theorem coe_rangeGradeEquiv_apply
    (hinj : Function.Injective f) (n : ℕ) (x : Mgrade n) :
    ((((rangeGradeEquiv Sgrade Mgrade Ngrade hf hinj n) x :
        (hf.rangeHomogeneousSubmodule Sgrade).toSubmodule) : N)) =
      f (x : M) := by
  rfl

/-- The source grade, target grade, and quotient range grade form an exact
sequence after transporting the inherited range grade through the
equivalence. -/
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

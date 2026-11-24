/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


-- Author: @toskua, Avocado
module

public import Mathlib.Algebra.DirectSum.Decomposition
public import Mathlib.Algebra.Module.GradedModule
public import Mathlib.RingTheory.Finiteness.Basic

/-!
# The canonical internal grading of an external direct sum

The range of each homogeneous inclusion into an external direct sum is a
submodule of the total direct sum.  These coordinate ranges form an internal
direct-sum decomposition whose coordinates agree with the original external
coordinates.

This file is additive and module-theoretic.  It also records the canonical
graded action between two coordinate-range families.  It constructs no graded
ring, graded algebra, associated-graded presentation, degree-shifting kernel
or range, or Hilbert--Serre theorem.

## Main declarations

* `DirectSum.internalGrade`
* `DirectSum.mem_internalGrade_iff`
* `DirectSum.internalGradeEquiv`
* `DirectSum.internalGradeDecomposition`
* `DirectSum.coe_decompose_internalGrade`
* `DirectSum.internalGrade_finite`
* `DirectSum.moduleInternalGrade`
* `DirectSum.moduleInternalGradeEquiv`
* `DirectSum.moduleInternalGradeDecomposition`
* `DirectSum.moduleInternalGrade_finite`
* `DirectSum.internalGradeGradedSMul`
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace DirectSum

section Coordinates

universe uA uι uM

variable (A : Type uA) [Semiring A]
variable (ι : Type uι) [DecidableEq ι]
variable (M : ι → Type uM)
  [∀ i, AddCommMonoid (M i)] [∀ i, Module A (M i)]

/-- The degree-`i` internal component of an external direct sum. -/
def internalGrade (i : ι) : Submodule A (⨁ i, M i) :=
  LinearMap.range (DirectSum.lof A ι M i)

/-- Membership in an internal coordinate is witnessed by an element of the
corresponding external summand. -/
@[simp]
theorem mem_internalGrade_iff (x : ⨁ i, M i) (i : ι) :
    x ∈ internalGrade A ι M i ↔
      ∃ y : M i, DirectSum.of M i y = x := by
  change (∃ y : M i, DirectSum.lof A ι M i y = x) ↔ _
  simp only [DirectSum.lof_eq_of]

private theorem lof_injective (i : ι) :
    Function.Injective (DirectSum.lof A ι M i) := by
  intro x y h
  have hi := congrArg (fun z : ⨁ i, M i ↦ z i) h
  simpa using hi

private noncomputable def lofEquivInternalGrade (i : ι) :
    M i ≃ₗ[A] internalGrade A ι M i :=
  LinearEquiv.ofInjective (DirectSum.lof A ι M i)
    (lof_injective A ι M i)

/-- A summand is canonically linearly equivalent to its coordinate range in
the external direct sum. -/
@[no_expose]
noncomputable def internalGradeEquiv (i : ι) :
    M i ≃ₗ[A] internalGrade A ι M i := by
  exact lofEquivInternalGrade A ι M i

/-- The internal-grade equivalence includes a summand by `DirectSum.of`. -/
@[simp]
theorem coe_internalGradeEquiv_apply (i : ι) (x : M i) :
    ((internalGradeEquiv A ι M i x : internalGrade A ι M i) :
      ⨁ i, M i) = DirectSum.of M i x := by
  rfl

private noncomputable def internalGradeDecompose :
    (⨁ i, M i) →ₗ[A] (⨁ i, internalGrade A ι M i) :=
  (DirectSum.congrLinearEquiv
    (fun i ↦ lofEquivInternalGrade A ι M i)).toLinearMap

private theorem internalGradeDecompose_left :
    (DirectSum.coeLinearMap (internalGrade A ι M)).comp
        (internalGradeDecompose A ι M) = LinearMap.id := by
  apply DirectSum.linearMap_ext A
  intro i
  apply LinearMap.ext
  intro x
  simp only [LinearMap.comp_apply, LinearMap.id_apply]
  rw [show internalGradeDecompose A ι M =
      DirectSum.lmap
        (fun i ↦ (lofEquivInternalGrade A ι M i).toLinearMap) by rfl,
    DirectSum.lmap_lof, DirectSum.coeLinearMap_lof]
  rfl

private theorem internalGradeDecompose_right :
    (internalGradeDecompose A ι M).comp
        (DirectSum.coeLinearMap (internalGrade A ι M)) = LinearMap.id := by
  apply DirectSum.linearMap_ext A
  intro i
  apply LinearMap.ext
  intro q
  obtain ⟨y, rfl⟩ := (lofEquivInternalGrade A ι M i).surjective q
  simp only [LinearMap.comp_apply, LinearMap.id_apply,
    DirectSum.coeLinearMap_lof]
  change internalGradeDecompose A ι M (DirectSum.lof A ι M i y) =
    DirectSum.lof A ι (fun i ↦ (internalGrade A ι M i : Type _)) i
      (lofEquivInternalGrade A ι M i y)
  rw [show internalGradeDecompose A ι M =
      DirectSum.lmap
        (fun i ↦ (lofEquivInternalGrade A ι M i).toLinearMap) by rfl,
    DirectSum.lmap_lof]
  rfl

/-- The coordinate ranges give the canonical internal decomposition of an
external direct sum. -/
@[no_expose]
noncomputable instance internalGradeDecomposition :
    DirectSum.Decomposition (internalGrade A ι M) := by
  exact DirectSum.Decomposition.ofLinearMap
    (internalGrade A ι M)
    (internalGradeDecompose A ι M)
    (internalGradeDecompose_left A ι M)
    (internalGradeDecompose_right A ι M)

/-- The internal decomposition coordinate, coerced back to the external
direct sum, is the corresponding external coordinate. -/
@[simp]
theorem coe_decompose_internalGrade (x : ⨁ i, M i) (i : ι) :
    ((DirectSum.decompose (internalGrade A ι M) x i :
        internalGrade A ι M i) : ⨁ i, M i) =
      DirectSum.of M i (x i) := by
  change ((lofEquivInternalGrade A ι M i (x i) :
    internalGrade A ι M i) : ⨁ i, M i) = _
  rfl

/-- A finite homogeneous summand has a finite internal coordinate range. -/
theorem internalGrade_finite (i : ι) [Module.Finite A (M i)] :
    Module.Finite A (internalGrade A ι M i) :=
  Module.Finite.of_surjective
    (DirectSum.lof A ι M i).rangeRestrict
    (DirectSum.lof A ι M i).surjective_rangeRestrict

end Coordinates

section ModuleCoordinates

universe uA uι uM

variable (A : Type uA) [Ring A]
variable (ι : Type uι) [DecidableEq ι]
variable (M : ι → Type uM)
  [∀ i, AddCommGroup (M i)] [∀ i, Module A (M i)]

/-- The canonical coordinate range specialized to external direct sums of modules. -/
abbrev moduleInternalGrade (i : ι) : Submodule A (⨁ i, M i) :=
  internalGrade A ι M i

/-- Module coordinate membership uses the canonical external summand representative. -/
theorem mem_moduleInternalGrade_iff (x : ⨁ i, M i) (i : ι) :
    x ∈ moduleInternalGrade A ι M i ↔
      ∃ y : M i, DirectSum.of M i y = x :=
  mem_internalGrade_iff A ι M x i

/-- The module coordinate equivalence is the canonical summand-to-range equivalence. -/
noncomputable abbrev moduleInternalGradeEquiv (i : ι) :
    M i ≃ₗ[A] moduleInternalGrade A ι M i :=
  internalGradeEquiv A ι M i

/-- Coercing the module coordinate equivalence gives the external inclusion. -/
theorem coe_moduleInternalGradeEquiv_apply (i : ι) (x : M i) :
    ((moduleInternalGradeEquiv A ι M i x :
      moduleInternalGrade A ι M i) : ⨁ i, M i) = DirectSum.of M i x :=
  coe_internalGradeEquiv_apply A ι M i x

/-- External module coordinates use the canonical internal decomposition. -/
noncomputable abbrev moduleInternalGradeDecomposition :
    DirectSum.Decomposition (moduleInternalGrade A ι M) :=
  internalGradeDecomposition A ι M

/-- The module decomposition has the original external coordinates. -/
theorem coe_decompose_moduleInternalGrade (x : ⨁ i, M i) (i : ι) :
    ((DirectSum.decompose (moduleInternalGrade A ι M) x i :
      moduleInternalGrade A ι M i) : ⨁ i, M i) = DirectSum.of M i (x i) :=
  coe_decompose_internalGrade A ι M x i

/-- Finite module summands give finite canonical coordinate ranges. -/
theorem moduleInternalGrade_finite (i : ι) [Module.Finite A (M i)] :
    Module.Finite A (moduleInternalGrade A ι M i) :=
  internalGrade_finite A ι M i

end ModuleCoordinates

section GradedSMul

universe uR uI uA uJ uM

/-- The internal coordinate ranges of a graded semiring and one of its graded
modules inherit the canonical graded scalar action. -/
instance internalGradeGradedSMul
    (R : Type uR) [Semiring R]
    {I : Type uI} {J : Type uJ}
    [DecidableEq I] [DecidableEq J]
    [AddMonoid I] [AddAction I J]
    (A : I → Type uA)
    [∀ i, AddCommMonoid (A i)] [∀ i, Module R (A i)]
    (M : J → Type uM)
    [∀ j, AddCommMonoid (M j)] [∀ j, Module R (M j)]
    [DirectSum.GSemiring A]
    [DirectSum.Gmodule A M] :
    SetLike.GradedSMul
      (DirectSum.internalGrade R I A)
      (DirectSum.internalGrade R J M) := by
  refine { smul_mem := ?_ }
  intro i j x y hx hy
  rw [mem_internalGrade_iff] at hx hy ⊢
  obtain ⟨a, rfl⟩ := hx
  obtain ⟨m, rfl⟩ := hy
  exact ⟨GradedMonoid.GSMul.smul a m,
    (DirectSum.Gmodule.of_smul_of A M a m).symm⟩

end GradedSMul

end DirectSum

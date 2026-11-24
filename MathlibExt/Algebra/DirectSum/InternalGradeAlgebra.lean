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
# Algebra-coherent internal grading of an external direct sum

The coordinate ranges of an external direct sum can be bundled as submodules
using the canonical total algebra's `Algebra.toModule`.  This family has the
same carrier sets as `DirectSum.internalGrade`, but its explicit module
dictionary is coherent with `GradedAlgebra`.

No new module, algebra, scalar action, semiring, scalar tower, or instance
priority is installed.  The additive D0 family remains unchanged.

## Main declarations

* `DirectSum.algebraInternalGrade`
* `DirectSum.algebraInternalGradeDecomposition`
* `DirectSum.mem_algebraInternalGrade_iff`
* `DirectSum.coe_decompose_algebraInternalGrade`
* `DirectSum.algebraInternalGradeGradedAlgebra`
* `DirectSum.algebraInternalGradeGradedSMul`
* `DirectSum.algebraInternalGradeModuleInternalGradeGradedSMul`
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

/-- The coordinate-range family bundled with the canonical total algebra's
module structure. -/
noncomputable def algebraInternalGrade (i : I) :
    @Submodule R (DirectSum I A) _ _
      (@Algebra.toModule R (DirectSum I A) _ _
        (DirectSum.instAlgebra R A)) :=
  LinearMap.range (DirectSum.lof R I A i)

/-- The algebra-coherent coordinate ranges inherit D0's canonical
decomposition. -/
noncomputable instance algebraInternalGradeDecomposition :
    DirectSum.Decomposition (algebraInternalGrade R A) := by
  change DirectSum.Decomposition (internalGrade R I A)
  infer_instance

/-- Membership in an algebra-coherent coordinate range is witnessed by an
element of the corresponding external summand. -/
@[simp]
theorem mem_algebraInternalGrade_iff (x : DirectSum I A) (i : I) :
    x ∈ algebraInternalGrade R A i ↔
      ∃ y : A i, DirectSum.of A i y = x := by
  change x ∈ internalGrade R I A i ↔ _
  exact mem_internalGrade_iff R I A x i

/-- The algebra-coherent decomposition coordinate coerces to the original
external coordinate. -/
@[simp]
theorem coe_decompose_algebraInternalGrade
    (x : DirectSum I A) (i : I) :
    ((DirectSum.decompose (algebraInternalGrade R A) x i :
        algebraInternalGrade R A i) : DirectSum I A) =
      DirectSum.of A i (x i) := by
  change ((DirectSum.decompose (internalGrade R I A) x i :
    internalGrade R I A i) : DirectSum I A) = _
  exact coe_decompose_internalGrade R I A x i

/-- The algebra-coherent coordinate ranges form the canonical internal
graded algebra. -/
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

/-- The algebra-coherent ring grade acts degreewise on D0's canonical module
coordinate grade. -/
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

/-- The algebra-coherent ring grade acts degreewise on the canonical
additive-group-valued module coordinate grade. -/
instance algebraInternalGradeModuleInternalGradeGradedSMul :
    SetLike.GradedSMul
      (algebraInternalGrade R A)
      (moduleInternalGrade R J M) := by
  refine { smul_mem := ?_ }
  intro i j x y hx hy
  rw [mem_algebraInternalGrade_iff] at hx
  rw [mem_moduleInternalGrade_iff] at hy ⊢
  obtain ⟨a, rfl⟩ := hx
  obtain ⟨m, rfl⟩ := hy
  exact ⟨GradedMonoid.GSMul.smul a m,
    (DirectSum.Gmodule.of_smul_of A M a m).symm⟩

end Module

end DirectSum

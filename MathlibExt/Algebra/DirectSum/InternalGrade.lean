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
# Coordinate ranges in external direct sums

For a family of semimodules M i over a semiring A, the range of the inclusion M i → ⨁ j, M j
is an internal homogeneous component. Each summand is linearly equivalent to its range, and
these ranges decompose the total direct sum: the i-th decomposition coordinate of x, viewed in
the total module, is the element supported at i with value x i.

Finite generation of a summand transfers to its coordinate range by the native range instance.
The semiring construction also applies to modules over rings. For a graded semiring A indexed by an
additive monoid I
and a graded module M indexed by an I-set J, the coordinate ranges carry the graded action:
degree i acting on degree j has degree i +ᵥ j.

See Bourbaki, *Algebra*, Chapter II, for direct sums and their internal decompositions.
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

/-- For a semiring A, an index type ι with decidable equality and A-semimodules M i, define the
degree-i submodule of ⨁ j, M j as the range of DirectSum.lof A ι M i : M i →ₗ[A] ⨁ j, M j.
Thus it consists of elements supported in the coordinate i. -/
def internalGrade (i : ι) : Submodule A (⨁ i, M i) :=
  LinearMap.range (DirectSum.lof A ι M i)

/-- For a semiring A, an index type ι with decidable equality and A-semimodules M i, an element x
of ⨁ j, M j belongs to internalGrade A ι M i if and only if there is y : M i with DirectSum.of
M i y = x. -/
@[simp]
theorem mem_internalGrade_iff (x : ⨁ i, M i) (i : ι) :
    x ∈ internalGrade A ι M i ↔
      ∃ y : M i, DirectSum.of M i y = x := by
  change (∃ y : M i, DirectSum.lof A ι M i y = x) ↔ _
  simp only [DirectSum.lof_eq_of]

private noncomputable def lofEquivInternalGrade (i : ι) :
    M i ≃ₗ[A] internalGrade A ι M i :=
  LinearEquiv.ofInjective (DirectSum.lof A ι M i)
    (by exact DirectSum.of_injective M i)

/-- For a semiring A, an index type ι with decidable equality and A-semimodules M i, the inclusion
at i induces the A-linear equivalence M i ≃ₗ[A] internalGrade A ι M i. It sends y to the
element DirectSum.of M i y equipped with its range-membership proof. -/
@[no_expose]
noncomputable def internalGradeEquiv (i : ι) :
    M i ≃ₗ[A] internalGrade A ι M i := by
  exact lofEquivInternalGrade A ι M i

/-- For a semiring A, an index type ι with decidable equality and A-semimodules M i, coercing
internalGradeEquiv A ι M i y back to ⨁ j, M j gives DirectSum.of M i y, for every i : ι and y
: M i. -/
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

/-- For a semiring A, an index type ι with decidable equality and A-semimodules M i, the
submodules internalGrade A ι M i form an internal direct-sum decomposition of ⨁ i, M i. The
map which sums their inclusions is inverse to the coordinate map obtained from the
summand-to-range equivalences. -/
@[no_expose]
noncomputable instance internalGradeDecomposition :
    DirectSum.Decomposition (internalGrade A ι M) := by
  exact DirectSum.Decomposition.ofLinearMap
    (internalGrade A ι M)
    (internalGradeDecompose A ι M)
    (internalGradeDecompose_left A ι M)
    (internalGradeDecompose_right A ι M)

/-- For a semiring A, an index type ι with decidable equality and A-semimodules M i, the i-th
component of DirectSum.decompose (internalGrade A ι M) x, coerced into ⨁ j, M j, equals
DirectSum.of M i (x i). This holds for every x and every index i. -/
@[simp]
theorem coe_decompose_internalGrade (x : ⨁ i, M i) (i : ι) :
    ((DirectSum.decompose (internalGrade A ι M) x i :
        internalGrade A ι M i) : ⨁ i, M i) =
      DirectSum.of M i (x i) := by
  change ((lofEquivInternalGrade A ι M i (x i) :
    internalGrade A ι M i) : ⨁ i, M i) = _
  rfl

end Coordinates



section GradedSMul

universe uR uI uA uJ uM

/-- Let R be a semiring, I an additive monoid and J an I-set, both with decidable equality. Let A
i and M j be R-semimodules, with A a graded semiring and M a graded A-module. If x belongs to
internalGrade R I A i and y belongs to internalGrade R J M j, then x • y belongs to
internalGrade R J M (i +ᵥ j). For included homogeneous elements a and m, this action is the
inclusion of their graded scalar product. -/
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

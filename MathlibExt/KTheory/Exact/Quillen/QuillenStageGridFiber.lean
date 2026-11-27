/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.CategoryTheory.FiberedCategory.DiscreteFiber
public import MathlibExt.KTheory.Exact.Quillen.QuillenStageGridLiftExistence

/-!
# Strict fibers of the Quillen Stage-grid projection

The strict fiber over a retained Quillen simplex uses Mathlib's standard
`Functor.Fiber`.  The landed all-degree lift theorem makes every such fiber
nonempty.  The finality and initiality theorems below are criteria only: they
reduce those categorical properties to connectedness of all strict fibers but
do not prove connectedness.

No instance, selected grid, fiber contraction, homotopy-finality, nerve or
realization weak equivalence, basepoint comparison, or Q/S statement is
introduced.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

open CategoryTheory Limits
open CategoryTheory.ExactCategory
open SimplexCategory
open scoped Simplicial

universe v u

namespace AlgebraicKTheory

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]

/-- Strict fiber of the retained-Q projection over `q`.  Objects are grid
lifts whose retained simplex is equal to `q`; morphisms lie over its identity
in the discrete target. -/
abbrev QuillenStageGridFiber {a : SimplexCategory}
    (q : QuillenQSimplex C a) :=
  (quillenStageGridQProjection C a).Fiber (Discrete.mk q)

/-- Every retained Quillen simplex has a nonempty strict Stage-grid fiber.
This is exactly the existence theorem repackaged in `Functor.Fiber`. -/
theorem quillenStageGridFiber_nonempty {a : SimplexCategory}
    (q : QuillenQSimplex C a) :
    Nonempty (QuillenStageGridFiber q) := by
  obtain ⟨⟨X, hX⟩⟩ := quillenStageGridLift_exists q
  exact ⟨⟨X, Discrete.ext hX⟩⟩

/-- The retained-Q projection is final exactly when every strict grid fiber
is connected.  This is a criterion, not a proof of either side. -/
theorem quillenStageGridQProjection_final_iff
    (C : Type u) [Category.{v} C] [Preadditive C]
    [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]
    (a : SimplexCategory) :
    (quillenStageGridQProjection C a).Final ↔
      ∀ q : QuillenQSimplex C a,
        IsConnected (QuillenStageGridFiber (C := C) q) := by
  constructor
  · intro h q
    exact (Functor.final_iff_forall_isConnected_fiber_of_isDiscrete
      (quillenStageGridQProjection C a)).mp h (Discrete.mk q)
  · intro h
    apply (Functor.final_iff_forall_isConnected_fiber_of_isDiscrete
      (quillenStageGridQProjection C a)).mpr
    rintro ⟨q⟩
    exact h q

/-- The retained-Q projection is initial exactly when every strict grid fiber
is connected.  This is a criterion, not a proof of either side. -/
theorem quillenStageGridQProjection_initial_iff
    (C : Type u) [Category.{v} C] [Preadditive C]
    [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]
    (a : SimplexCategory) :
    (quillenStageGridQProjection C a).Initial ↔
      ∀ q : QuillenQSimplex C a,
        IsConnected (QuillenStageGridFiber (C := C) q) := by
  constructor
  · intro h q
    exact (Functor.initial_iff_forall_isConnected_fiber_of_isDiscrete
      (quillenStageGridQProjection C a)).mp h (Discrete.mk q)
  · intro h
    apply (Functor.initial_iff_forall_isConnected_fiber_of_isDiscrete
      (quillenStageGridQProjection C a)).mpr
    rintro ⟨q⟩
    exact h q

end AlgebraicKTheory

end

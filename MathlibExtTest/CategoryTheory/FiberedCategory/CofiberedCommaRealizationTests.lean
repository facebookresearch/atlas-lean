/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.FiberedCategory.CofiberedCommaRealization

/-!
# Public use of the actual cofibered comma inclusion

The inverse of the comma/fiber realized equivalence has the original strict-fiber inclusion
as its forward map, with an explicit inverse and full homotopies.
-/

universe u v

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace MathlibExtTest.CategoryTheory.FiberedCategory.CofiberedCommaRealizationTests

/-- The original comma inclusion has a whole-space inverse with its exact forward arrow. -/
theorem actual_fiber_inclusion_has_forward_inverse
    {C : Type (max u v)} [Category.{v} C]
    {D : Type u} [Category.{v} D] (p : C ⥤ D) [p.IsCofibered] (d : D) :
    ∃ e : ContinuousMap.HomotopyEquiv
      (SSet.toTop.obj (nerve (Functor.Fiber p d)))
      (SSet.toTop.obj (nerve (CostructuredArrow p d))),
      e.toFun = (SSet.toTop.map
        (nerveMap (Functor.IsCofibered.fiberToCostructuredArrow (p := p) d))).hom := by
  refine ⟨(Functor.IsCofibered.commaFiberRealizedEquiv (p := p) d).symm, ?_⟩
  exact Functor.IsCofibered.commaFiberRealizedEquiv_invFun (p := p) d

#print axioms actual_fiber_inclusion_has_forward_inverse

end MathlibExtTest.CategoryTheory.FiberedCategory.CofiberedCommaRealizationTests

end

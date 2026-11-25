/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.AlgebraicTopology.ModelCategory.HomotopyPullback
public import Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects

/-!
# Generic homotopy fibers

In a pointed category, the fiber cospan of an arrow `X ⟶ Y` is
`X ⟶ Y ⟵ 0`. This file defines its ordinary pullback and functorial
homotopy pullback, the canonical comparison from the former to the latter,
weak invariance, and sharp or right-proper criteria for that comparison to
be a weak equivalence.

No path-object model, selected-category instance, localization, canonical
isomorphism, or homotopy-category universal property is introduced.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe v u

open CategoryTheory Limits MorphismProperty

namespace HomotopicalAlgebra

variable {C : Type u} [Category.{v} C]

section Categorical

variable [HasZeroObject C]

/-- The walking cospan `X ⟶ Y ⟵ 0` associated to an arrow `X ⟶ Y`. -/
noncomputable def fiberCospan : Arrow C ⥤ (WalkingCospan ⥤ C) where
  obj f := cospan f.hom (initial.to f.right)
  map {f g} sq := cospanHomMk sq.right sq.left (𝟙 _)
    sq.w.symm (by simp)
  map_id f := by
    ext j
    rcases j with (_ | _ | _) <;> simp
  map_comp sq₁ sq₂ := by
    ext j
    rcases j with (_ | _ | _) <;> simp

variable [HasLimitsOfShape WalkingCospan C]

/-- The ordinary categorical fiber, as the limit of `X ⟶ Y ⟵ 0`. -/
noncomputable def ordinaryFiber : Arrow C ⥤ C :=
  fiberCospan (C := C) ⋙ lim

end Categorical

section Model

variable [ModelCategory C] [HasZeroObject C]
variable [HasFunctorialFactorization
  (trivialCofibrations C) (fibrations C)]

/-- The functorial homotopy fiber obtained from the reviewed homotopy
pullback functor. -/
noncomputable def homotopyFiber : Arrow C ⥤ C :=
  fiberCospan (C := C) ⋙ homotopyPullback

/-- Canonical comparison from the ordinary categorical fiber to the
homotopy fiber. -/
noncomputable def homotopyFiberComparison :
    ordinaryFiber (C := C) ⟶ homotopyFiber :=
  Functor.whiskerLeft (fiberCospan (C := C))
    (homotopyPullbackComparison (C := C))

@[simp]
theorem homotopyFiberComparison_app (f : Arrow C) :
    (homotopyFiberComparison (C := C)).app f =
      (homotopyPullbackComparison (C := C)).app
        ((fiberCospan (C := C)).obj f) :=
  rfl

/-- Pointwise weakly equivalent arrows have weakly equivalent homotopy
fibers. -/
theorem homotopyFiber_map_weakEquivalence
    {f g : Arrow C} (sq : f ⟶ g)
    (hleft : WeakEquivalence sq.left)
    (hright : WeakEquivalence sq.right) :
    WeakEquivalence ((homotopyFiber (C := C)).map sq) := by
  apply homotopyPullback_map_weakEquivalence
    ((fiberCospan (C := C)).map sq)
  intro j
  rcases j with (_ | _ | _)
  · change WeakEquivalence sq.right
    exact hright
  · change WeakEquivalence sq.left
    exact hleft
  · change WeakEquivalence (𝟙 (⊥_ C))
    infer_instance

omit [HasFunctorialFactorization
  (trivialCofibrations C) (fibrations C)] in
private theorem isFibrant_initial_of_hasZeroObject :
    IsFibrant (⊥_ C) := by
  rw [isFibrant_iff_of_isTerminal (𝟙 (⊥_ C))
    (((isZero_zero C).of_iso
      HasZeroObject.zeroIsoInitial.symm).isTerminal)]
  infer_instance

/-- A fibration with fibrant target has ordinary fiber weakly equivalent to
its homotopy fiber. The zero-object hypothesis supplies fibrancy of the
other cospan endpoint. -/
theorem weakEquivalence_homotopyFiberComparison_of_fibration_fibrant
    (f : Arrow C) [IsFibrant f.right] [Fibration f.hom] :
    WeakEquivalence ((homotopyFiberComparison (C := C)).app f) := by
  let _ : IsFibrant
      ((fiberCospan (C := C)).obj f |>.obj WalkingCospan.one) := by
    change IsFibrant f.right
    infer_instance
  let _ : IsFibrant
      ((fiberCospan (C := C)).obj f |>.obj WalkingCospan.right) := by
    change IsFibrant (⊥_ C)
    exact isFibrant_initial_of_hasZeroObject (C := C)
  let _ : Fibration
      ((fiberCospan (C := C)).obj f |>.map WalkingCospan.Hom.inl) := by
    change Fibration f.hom
    infer_instance
  apply weakEquivalence_homotopyPullbackComparison_of_inl
    ((fiberCospan (C := C)).obj f)

/-- In a right-proper model category, a fibration has ordinary fiber weakly
equivalent to its homotopy fiber. -/
theorem weakEquivalence_homotopyFiberComparison_of_rightProper
    [IsRightProper C] (f : Arrow C) [Fibration f.hom] :
    WeakEquivalence ((homotopyFiberComparison (C := C)).app f) := by
  let _ : Fibration
      ((fiberCospan (C := C)).obj f |>.map WalkingCospan.Hom.inl) := by
    change Fibration f.hom
    infer_instance
  apply weakEquivalence_homotopyPullbackComparison_of_rightProper_inl
    ((fiberCospan (C := C)).obj f)

end Model

end HomotopicalAlgebra

end

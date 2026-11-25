/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.AlgebraicTopology.ModelCategory.HomotopyPushout
public import MathlibExt.CategoryTheory.Limits.Shapes.Cofiber

/-!
# Generic homotopy cofibers

For an arrow `X ⟶ Y`, its cofiber span is `Y ← X ⟶ *`. The neutral
`CategoryTheory.Limits.Shapes.Cofiber` module defines the span and its ordinary
colimit. This file defines the functorial homotopy pushout, the canonical
comparison, weak invariance, and sharp or left-proper criteria for that
comparison to be a weak equivalence.

No selected-category quotient, mapping cone, localization, or chosen
comparison between replacement objects is introduced.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe v u

open CategoryTheory Limits MorphismProperty

namespace HomotopicalAlgebra

variable {C : Type u} [Category.{v} C]

section Model

variable [ModelCategory C]
variable [HasFunctorialFactorization (cofibrations C) (trivialFibrations C)]

/-- The functorial homotopy cofiber obtained from the reviewed homotopy
pushout functor. -/
noncomputable def homotopyCofiber : Arrow C ⥤ C :=
  cofiberSpan (C := C) ⋙ homotopyPushout

/-- Canonical comparison from the homotopy cofiber to the ordinary
categorical cofiber. -/
noncomputable def homotopyCofiberComparison :
    homotopyCofiber (C := C) ⟶ ordinaryCofiber where
  app f := (homotopyPushoutComparison (C := C)).app
    ((cofiberSpan (C := C)).obj f)
  naturality _ _ sq :=
    (homotopyPushoutComparison (C := C)).naturality
      ((cofiberSpan (C := C)).map sq)

@[simp]
theorem homotopyCofiberComparison_app (f : Arrow C) :
    (homotopyCofiberComparison (C := C)).app f =
      (homotopyPushoutComparison (C := C)).app
        ((cofiberSpan (C := C)).obj f) :=
  rfl

/-- Pointwise weakly equivalent arrows have weakly equivalent homotopy
cofibers. -/
theorem homotopyCofiber_map_weakEquivalence
    {f g : Arrow C} (sq : f ⟶ g)
    (hleft : WeakEquivalence sq.left)
    (hright : WeakEquivalence sq.right) :
    WeakEquivalence ((homotopyCofiber (C := C)).map sq) := by
  apply homotopyPushout_map_weakEquivalence
    ((cofiberSpan (C := C)).map sq)
  intro j
  rcases j with (_ | _ | _)
  · change WeakEquivalence sq.left
    exact hleft
  · change WeakEquivalence sq.right
    exact hright
  · change WeakEquivalence (𝟙 (⊤_ C))
    infer_instance

/-- Sharp comparison criterion using the cofiber arrow as the designated
cofibration. -/
theorem weakEquivalence_homotopyCofiberComparison_of_cofibration
    (f : Arrow C)
    [IsCofibrant f.left] [IsCofibrant (⊤_ C)] [Cofibration f.hom] :
    WeakEquivalence ((homotopyCofiberComparison (C := C)).app f) := by
  let _ : IsCofibrant
      ((cofiberSpan (C := C)).obj f |>.obj WalkingSpan.zero) := by
    change IsCofibrant f.left
    infer_instance
  let _ : IsCofibrant
      ((cofiberSpan (C := C)).obj f |>.obj WalkingSpan.right) := by
    change IsCofibrant (⊤_ C)
    infer_instance
  let _ : Cofibration
      ((cofiberSpan (C := C)).obj f |>.map WalkingSpan.Hom.fst) := by
    change Cofibration f.hom
    infer_instance
  apply weakEquivalence_homotopyPushoutComparison_of_fst
    ((cofiberSpan (C := C)).obj f)

/-- The symmetric sharp criterion, designating the terminal leg. -/
theorem weakEquivalence_homotopyCofiberComparison_of_terminalLeg
    (f : Arrow C)
    [IsCofibrant f.left] [IsCofibrant f.right]
    [Cofibration (terminal.from f.left)] :
    WeakEquivalence ((homotopyCofiberComparison (C := C)).app f) := by
  let _ : IsCofibrant
      ((cofiberSpan (C := C)).obj f |>.obj WalkingSpan.zero) := by
    change IsCofibrant f.left
    infer_instance
  let _ : IsCofibrant
      ((cofiberSpan (C := C)).obj f |>.obj WalkingSpan.left) := by
    change IsCofibrant f.right
    infer_instance
  let _ : Cofibration
      ((cofiberSpan (C := C)).obj f |>.map WalkingSpan.Hom.snd) := by
    change Cofibration (terminal.from f.left)
    infer_instance
  apply weakEquivalence_homotopyPushoutComparison_of_snd
    ((cofiberSpan (C := C)).obj f)

omit [HasFunctorialFactorization (cofibrations C) (trivialFibrations C)] in
private theorem isCofibrant_terminal_of_hasZeroObject
    [HasZeroObject C] : IsCofibrant (⊤_ C) := by
  rw [isCofibrant_iff_of_isInitial (𝟙 (⊤_ C))
    (((isZero_zero C).of_iso
      HasZeroObject.zeroIsoTerminal.symm).isInitial)]
  infer_instance

/-- In a pointed model category, the terminal object is automatically
cofibrant, so a cofibration with cofibrant source satisfies the sharp
criterion. -/
theorem weakEquivalence_homotopyCofiberComparison_of_pointedCofibration
    [HasZeroObject C] (f : Arrow C)
    [IsCofibrant f.left] [Cofibration f.hom] :
    WeakEquivalence ((homotopyCofiberComparison (C := C)).app f) := by
  let _ : IsCofibrant (⊤_ C) :=
    isCofibrant_terminal_of_hasZeroObject (C := C)
  exact weakEquivalence_homotopyCofiberComparison_of_cofibration f

/-- In a left-proper model category, a cofibration has ordinary cofiber
weakly equivalent to its homotopy cofiber. -/
theorem weakEquivalence_homotopyCofiberComparison_of_leftProper
    [IsLeftProper C] (f : Arrow C) [Cofibration f.hom] :
    WeakEquivalence ((homotopyCofiberComparison (C := C)).app f) := by
  let _ : Cofibration
      ((cofiberSpan (C := C)).obj f |>.map WalkingSpan.Hom.fst) := by
    change Cofibration f.hom
    infer_instance
  apply weakEquivalence_homotopyPushoutComparison_of_leftProper_fst
    ((cofiberSpan (C := C)).obj f)

/-- The symmetric left-proper criterion, designating the terminal leg. -/
theorem weakEquivalence_homotopyCofiberComparison_of_leftProper_terminalLeg
    [IsLeftProper C] (f : Arrow C)
    [Cofibration (terminal.from f.left)] :
    WeakEquivalence ((homotopyCofiberComparison (C := C)).app f) := by
  let _ : Cofibration
      ((cofiberSpan (C := C)).obj f |>.map WalkingSpan.Hom.snd) := by
    change Cofibration (terminal.from f.left)
    infer_instance
  apply weakEquivalence_homotopyPushoutComparison_of_leftProper_snd
    ((cofiberSpan (C := C)).obj f)

end Model

end HomotopicalAlgebra

end

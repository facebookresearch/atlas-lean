/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import Mathlib.AlgebraicTopology.ModelCategory.Basic
public import Mathlib.AlgebraicTopology.ModelCategory.IsCofibrant

import MathlibExt.AlgebraicTopology.ModelCategory.CofibrantCube
import MathlibExt.CategoryTheory.MorphismProperty.Limits
import Mathlib.AlgebraicTopology.ModelCategory.Opposite

/-!
# Proper model categories

This file packages left and right properness as thin wrapper classes around
the existing morphism-property base-change predicates.  The wrappers make a
proper model structure an explicit opt-in choice: a raw stability instance
does not by itself install a properness instance.

It also provides the pointwise pushout and pullback clients and the standard
criteria that every object cofibrant implies left properness and every object
fibrant implies right properness.
-/

@[expose] public section

universe v u

open CategoryTheory Limits MorphismProperty

namespace HomotopicalAlgebra

/-- A category is left proper when weak equivalences are stable under
cobase change against cofibrations. -/
class IsLeftProper (C : Type u) [Category.{v} C]
    [CategoryWithWeakEquivalences C] [CategoryWithCofibrations C] : Prop where
  weakEquivalences_isStableUnderCobaseChangeAgainst_cofibrations :
    (weakEquivalences C).IsStableUnderCobaseChangeAgainst (cofibrations C)

/-- A category is right proper when weak equivalences are stable under
base change against fibrations. -/
class IsRightProper (C : Type u) [Category.{v} C]
    [CategoryWithWeakEquivalences C] [CategoryWithFibrations C] : Prop where
  weakEquivalences_isStableUnderBaseChangeAgainst_fibrations :
    (weakEquivalences C).IsStableUnderBaseChangeAgainst (fibrations C)

attribute [instance 100]
  IsLeftProper.weakEquivalences_isStableUnderCobaseChangeAgainst_cofibrations
  IsRightProper.weakEquivalences_isStableUnderBaseChangeAgainst_fibrations

section PointwiseLeft

variable {C : Type u} [Category.{v} C]
  [CategoryWithWeakEquivalences C] [CategoryWithCofibrations C]

/-- In a left proper category, cobase change of a weak equivalence along a
cofibration is a weak equivalence. -/
theorem IsLeftProper.weakEquivalence_of_isPushout
    [IsLeftProper C]
    {A B X Y : C}
    {i : A ⟶ B} {f : A ⟶ X} {f' : B ⟶ Y} {j : X ⟶ Y}
    (sq : IsPushout i f f' j) [Cofibration i] [WeakEquivalence f] :
    WeakEquivalence f' := by
  rw [weakEquivalence_iff]
  exact IsStableUnderCobaseChangeAgainst.of_isPushout
    (inferInstance :
      (weakEquivalences C).IsStableUnderCobaseChangeAgainst (cofibrations C))
    sq (mem_cofibrations i) (mem_weakEquivalences f)

end PointwiseLeft

section PointwiseRight

variable {C : Type u} [Category.{v} C]
  [CategoryWithWeakEquivalences C] [CategoryWithFibrations C]

/-- In a right proper category, base change of a weak equivalence along a
fibration is a weak equivalence. -/
theorem IsRightProper.weakEquivalence_of_isPullback
    [IsRightProper C]
    {A B X Y : C}
    {p' : A ⟶ B} {f' : A ⟶ X} {f : B ⟶ Y} {p : X ⟶ Y}
    (sq : IsPullback p' f' f p) [Fibration p] [WeakEquivalence f] :
    WeakEquivalence f' := by
  rw [weakEquivalence_iff]
  let h : (weakEquivalences C).IsStableUnderBaseChangeAgainst
      (fibrations C) := inferInstance
  exact (h.isStableUnderBaseChangeAlong p (mem_fibrations p)).of_isPullback
    sq (mem_weakEquivalences f)

end PointwiseRight

section Criteria

variable {C : Type u} [Category.{v} C] [ModelCategory C]

/-- A model category in which every object is cofibrant is left proper. -/
theorem isLeftProper_of_all_objects_cofibrant
    (h : ∀ X : C, IsCofibrant X) : IsLeftProper C where
  weakEquivalences_isStableUnderCobaseChangeAgainst_cofibrations := by
    constructor
    intro A B i hi
    constructor
    intro X Y j f' f sq hf
    let _ : Cofibration i := (cofibration_iff i).mpr hi
    let _ : WeakEquivalence f := (weakEquivalence_iff f).mpr hf
    let _ : IsCofibrant A := h A
    let _ : IsCofibrant X := h X
    exact (weakEquivalence_iff f').mp
      (weakEquivalence_of_isPushout_of_cofibrant sq : WeakEquivalence f')

/-- A model category in which every object is fibrant is right proper. -/
theorem isRightProper_of_all_objects_fibrant
    (h : ∀ X : C, IsFibrant X) : IsRightProper C where
  weakEquivalences_isStableUnderBaseChangeAgainst_fibrations := by
    constructor
    intro X Y p hp
    constructor
    intro Z W f' g' g sq hg
    have hCofOp (T : Cᵒᵖ) : IsCofibrant T := by
      apply (isCofibrant_iff_of_isInitial
        ((terminal.from T.unop).op) terminalIsTerminal.op).2
      rw [cofibration_op_iff]
      exact h T.unop
    have hLeft : IsLeftProper Cᵒᵖ :=
      isLeftProper_of_all_objects_cofibrant hCofOp
    have hpOp : cofibrations Cᵒᵖ p.op := by
      rw [cofibrations_op]
      exact hp
    have hgOp : weakEquivalences Cᵒᵖ g.op := by
      rw [weakEquivalences_op]
      exact hg
    have hg'Op : weakEquivalences Cᵒᵖ g'.op :=
      hLeft.weakEquivalences_isStableUnderCobaseChangeAgainst_cofibrations
        |>.of_isPushout sq.op hpOp hgOp
    rw [weakEquivalences_op] at hg'Op
    exact hg'Op

end Criteria

end HomotopicalAlgebra

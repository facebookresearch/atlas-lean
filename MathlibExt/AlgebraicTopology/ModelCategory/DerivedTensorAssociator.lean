/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Codex
module

public import MathlibExt.AlgebraicTopology.ModelCategory.DerivedTensorAdjunction
public import Mathlib.CategoryTheory.Localization.Trifunctor

/-!
# The actual associator of the chosen derived tensor

The source map is the original composite
`Q(QX ⊗ QY) ⊗ QZ ⟶ (QX ⊗ QY) ⊗ QZ ⟶ QX ⊗ (QY ⊗ QZ)`
followed by the inverse of the original right Q-comparison. Both comparisons
are proved weak at their actual cofibrant endpoints. The resulting source
natural isomorphism is lifted to every homotopy-category object and morphism.

Source: Hovey, *Model Categories*, Theorem 4.3.2.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u v

open CategoryTheory Limits MonoidalCategory MorphismProperty Functor
open scoped MonoidalCategory MonoidalClosed

namespace HomotopicalAlgebra.DerivedTensorConstructions

variable {C : Type u} [Category.{v} C] [ModelCategory C]
  [MonoidalCategory C] [SymmetricCategory C] [MonoidalClosed C]
  [IsClosedSymmetricMonoidalModelCategory C]

local notation "Ho" => MorphismProperty.Localization (weakEquivalences C)
local notation "π" => MorphismProperty.Q (weakEquivalences C)

omit [SymmetricCategory C] [MonoidalClosed C] [IsClosedSymmetricMonoidalModelCategory C] in
/-- The original outer left tensor leaves its actual first tensor source unreplaced. -/
def leftOuter (d : GeneratedFunctorialReplacements.Data (C := C)) : C ⥤ C ⥤ C :=
  curriedTensor C ⋙ (whiskeringLeft C C C).obj d.Q

omit [SymmetricCategory C] [MonoidalClosed C] [IsClosedSymmetricMonoidalModelCategory C] in
/-- The original outer right tensor leaves its actual second tensor source unreplaced. -/
def rightOuter (d : GeneratedFunctorialReplacements.Data (C := C)) : C ⥤ C ⥤ C :=
  d.Q ⋙ curriedTensor C

omit [SymmetricCategory C] [MonoidalClosed C] [IsClosedSymmetricMonoidalModelCategory C] in
/-- The original first Q counit gives the complete outer tensor comparison. -/
def leftOuterContraction (d : GeneratedFunctorialReplacements.Data (C := C)) :
    replacedTensor d ⟶ leftOuter d :=
  whiskerRight (whiskerRight d.q (curriedTensor C)) ((whiskeringLeft C C C).obj d.Q) ≫
    (isoWhiskerRight (curriedTensor C).leftUnitor ((whiskeringLeft C C C).obj d.Q)).hom

omit [SymmetricCategory C] [MonoidalClosed C] [IsClosedSymmetricMonoidalModelCategory C] in
/-- The same original Q counit gives the complete outer comparison in the other variable. -/
def rightOuterContraction (d : GeneratedFunctorialReplacements.Data (C := C)) :
    replacedTensor d ⟶ rightOuter d :=
  whiskerLeft (d.Q ⋙ curriedTensor C) ((whiskeringLeft C C C).map d.q) ≫
    (d.Q ⋙ curriedTensor C).rightUnitor.hom

omit [SymmetricCategory C] [MonoidalClosed C] [IsClosedSymmetricMonoidalModelCategory C] in
/-- The actual original left bracketed replacement tensor, projected to Ho. -/
def rawLeftBracket (d : GeneratedFunctorialReplacements.Data (C := C)) : C ⥤ C ⥤ C ⥤ Ho :=
  (postcompose₃.obj π).obj (bifunctorComp₁₂ (replacedTensor d) (replacedTensor d))

omit [SymmetricCategory C] [MonoidalClosed C] [IsClosedSymmetricMonoidalModelCategory C] in
/-- The actual original right bracketed replacement tensor, projected to Ho. -/
def rawRightBracket (d : GeneratedFunctorialReplacements.Data (C := C)) : C ⥤ C ⥤ C ⥤ Ho :=
  (postcompose₃.obj π).obj (bifunctorComp₂₃ (replacedTensor d) (replacedTensor d))

omit [SymmetricCategory C] [MonoidalClosed C] [IsClosedSymmetricMonoidalModelCategory C] in
/-- The same left tensor word before the actual inner Q comparison. -/
def actualLeftBracket (d : GeneratedFunctorialReplacements.Data (C := C)) : C ⥤ C ⥤ C ⥤ Ho :=
  (postcompose₃.obj π).obj (bifunctorComp₁₂ (replacedTensor d) (leftOuter d))

omit [SymmetricCategory C] [MonoidalClosed C] [IsClosedSymmetricMonoidalModelCategory C] in
/-- The same right tensor word before the actual inner Q comparison. -/
def actualRightBracket (d : GeneratedFunctorialReplacements.Data (C := C)) : C ⥤ C ⥤ C ⥤ Ho :=
  (postcompose₃.obj π).obj (bifunctorComp₂₃ (rightOuter d) (replacedTensor d))

omit [SymmetricCategory C] [MonoidalClosed C] [IsClosedSymmetricMonoidalModelCategory C] in
/-- The entire original left contraction is natural in all three original source variables. -/
def leftBracketContraction (d : GeneratedFunctorialReplacements.Data (C := C)) :
    rawLeftBracket d ⟶ actualLeftBracket d :=
  (postcompose₃.obj π).map
      ((bifunctorComp₁₂Functor.obj (replacedTensor d)).map (leftOuterContraction d))

omit [SymmetricCategory C] [MonoidalClosed C] [IsClosedSymmetricMonoidalModelCategory C] in
/-- The entire original right contraction retains all three original source map functions. -/
def rightBracketContraction (d : GeneratedFunctorialReplacements.Data (C := C)) :
    rawRightBracket d ⟶ actualRightBracket d :=
  (postcompose₃.obj π).map
      ((bifunctorComp₂₃Functor.map (rightOuterContraction d)).app (replacedTensor d))

omit [SymmetricCategory C] [MonoidalClosed C] [IsClosedSymmetricMonoidalModelCategory C] in
/-- The left source comparison is the exact original counit tensor map. -/
theorem leftBracketContraction_app (d : GeneratedFunctorialReplacements.Data (C := C)) (X Y Z : C) :
    (((leftBracketContraction d).app X).app Y).app Z =
      (π).map (d.q.app (d.Q.obj X ⊗ d.Q.obj Y) ▷ d.Q.obj Z) := by
  dsimp [leftBracketContraction, leftOuterContraction, replacedTensor]
  simp

omit [SymmetricCategory C] [MonoidalClosed C] [IsClosedSymmetricMonoidalModelCategory C] in
/-- The right source comparison is the same original counit map on the other tensor side. -/
theorem rightBracketContraction_app (d : GeneratedFunctorialReplacements.Data (C := C)) (X Y Z : C)
    :
    (((rightBracketContraction d).app X).app Y).app Z =
      (π).map (d.Q.obj X ◁ d.q.app (d.Q.obj Y ⊗ d.Q.obj Z)) := by
  dsimp [rightBracketContraction, rightOuterContraction, replacedTensor]
  simp

/-- The left comparison is invertible from the original Q counit and both actual cofibrant
endpoints. -/
theorem leftBracketContraction_isIso (d : GeneratedFunctorialReplacements.Data (C := C))
    (X Y Z : C) :
    IsIso ((((leftBracketContraction d).app X).app Y).app Z) := by
  rw [leftBracketContraction_app]
  let _ : IsCofibrant (d.Q.obj X) := d.q_cofibrant X
  let _ : IsCofibrant (d.Q.obj Y) := d.q_cofibrant Y
  let _ : IsCofibrant (d.Q.obj Z) := d.q_cofibrant Z
  let pp := IsClosedSymmetricMonoidalModelCategory.pushoutProductAxiom (C := C)
  let _ : IsCofibrant (d.Q.obj X ⊗ d.Q.obj Y) := pp.isCofibrant_tensorObj _ _
  let _ : IsCofibrant (d.Q.obj (d.Q.obj X ⊗ d.Q.obj Y)) := d.q_cofibrant _
  let q : d.Q.obj (d.Q.obj X ⊗ d.Q.obj Y) ⟶ d.Q.obj X ⊗ d.Q.obj Y := d.q.app _
  let _ : WeakEquivalence q := (weakEquivalence_iff _).mpr (d.q_trivialFibration _).2
  let _ : WeakEquivalence (q ▷ d.Q.obj Z) := pp.whiskerRight_weakEquivalence_of_cofibrant q _
  exact Localization.inverts π (weakEquivalences C) _ WeakEquivalence.mem

/-- The right comparison is invertible from the same original Q counit and actual cofibrant tensor
factors. -/
theorem rightBracketContraction_isIso (d : GeneratedFunctorialReplacements.Data (C := C))
    (X Y Z : C) :
    IsIso ((((rightBracketContraction d).app X).app Y).app Z) := by
  rw [rightBracketContraction_app]
  let _ : IsCofibrant (d.Q.obj X) := d.q_cofibrant X
  let _ : IsCofibrant (d.Q.obj Y) := d.q_cofibrant Y
  let _ : IsCofibrant (d.Q.obj Z) := d.q_cofibrant Z
  let pp := IsClosedSymmetricMonoidalModelCategory.pushoutProductAxiom (C := C)
  let _ : IsCofibrant (d.Q.obj Y ⊗ d.Q.obj Z) := pp.isCofibrant_tensorObj _ _
  let _ : IsCofibrant (d.Q.obj (d.Q.obj Y ⊗ d.Q.obj Z)) := d.q_cofibrant _
  let q : d.Q.obj (d.Q.obj Y ⊗ d.Q.obj Z) ⟶ d.Q.obj Y ⊗ d.Q.obj Z := d.q.app _
  let _ : WeakEquivalence q := (weakEquivalence_iff _).mpr (d.q_trivialFibration _).2
  let _ : WeakEquivalence (d.Q.obj X ◁ q) := pp.whiskerLeft_weakEquivalence_of_cofibrant _ q
  exact Localization.inverts π (weakEquivalences C) _ WeakEquivalence.mem

/-- The whole original left contraction has the actual natural inverse in every source variable. -/
def leftBracketContractionIso (d : GeneratedFunctorialReplacements.Data (C := C)) :
    rawLeftBracket d ≅ actualLeftBracket d := by
  let _ : ∀ X Y Z, IsIso ((((leftBracketContraction d).app X).app Y).app Z) :=
    leftBracketContraction_isIso d
  let _ : ∀ X Y, IsIso (((leftBracketContraction d).app X).app Y) :=
    fun X Y => NatIso.isIso_of_isIso_app _
  let _ : ∀ X, IsIso ((leftBracketContraction d).app X) := fun X => NatIso.isIso_of_isIso_app _
  let _ : IsIso (leftBracketContraction d) := NatIso.isIso_of_isIso_app _
  exact asIso (leftBracketContraction d)

/-- The whole original right contraction is a natural isomorphism with the same original component
inverses. -/
def rightBracketContractionIso (d : GeneratedFunctorialReplacements.Data (C := C)) :
    rawRightBracket d ≅ actualRightBracket d := by
  let _ : ∀ X Y Z, IsIso ((((rightBracketContraction d).app X).app Y).app Z) :=
    rightBracketContraction_isIso d
  let _ : ∀ X Y, IsIso (((rightBracketContraction d).app X).app Y) :=
    fun X Y => NatIso.isIso_of_isIso_app _
  let _ : ∀ X, IsIso ((rightBracketContraction d).app X) := fun X => NatIso.isIso_of_isIso_app _
  let _ : IsIso (rightBracketContraction d) := NatIso.isIso_of_isIso_app _
  exact asIso (rightBracketContraction d)

/-- The original associator is natural on all three actual original Q tensor factors. -/
def actualBracketAssociator (d : GeneratedFunctorialReplacements.Data (C := C)) :
    actualLeftBracket d ≅ actualRightBracket d :=
  NatIso.ofComponents
    (fun X => NatIso.ofComponents
      (fun Y => NatIso.ofComponents
        (fun Z => (π).mapIso (α_ (d.Q.obj X) (d.Q.obj Y) (d.Q.obj Z))) (by
          intro Z Z' f
          change (π).map ((d.Q.obj X ⊗ d.Q.obj Y) ◁ d.Q.map f) ≫
              (π).map (α_ (d.Q.obj X) (d.Q.obj Y) (d.Q.obj Z')).hom =
            (π).map (α_ (d.Q.obj X) (d.Q.obj Y) (d.Q.obj Z)).hom ≫
              (π).map (d.Q.obj X ◁ (d.Q.obj Y ◁ d.Q.map f))
          rw [← (π).map_comp, ← (π).map_comp]
          exact (π).congr_map (associator_naturality_right _ _ (d.Q.map f)))) (by
        intro Y Y' f
        apply NatTrans.ext
        funext Z
        change (π).map ((d.Q.obj X ◁ d.Q.map f) ▷ d.Q.obj Z) ≫
            (π).map (α_ (d.Q.obj X) (d.Q.obj Y') (d.Q.obj Z)).hom =
          (π).map (α_ (d.Q.obj X) (d.Q.obj Y) (d.Q.obj Z)).hom ≫
            (π).map (d.Q.obj X ◁ (d.Q.map f ▷ d.Q.obj Z))
        rw [← (π).map_comp, ← (π).map_comp]
        exact (π).congr_map (associator_naturality_middle _ (d.Q.map f) _))) (by
      intro X X' f
      apply NatTrans.ext
      funext Y
      apply NatTrans.ext
      funext Z
      change (π).map ((d.Q.map f ▷ d.Q.obj Y) ▷ d.Q.obj Z) ≫
          (π).map (α_ (d.Q.obj X') (d.Q.obj Y) (d.Q.obj Z)).hom =
        (π).map (α_ (d.Q.obj X) (d.Q.obj Y) (d.Q.obj Z)).hom ≫
          (π).map (d.Q.map f ▷ (d.Q.obj Y ⊗ d.Q.obj Z))
      rw [← (π).map_comp, ← (π).map_comp]
      exact (π).congr_map (associator_naturality_left (d.Q.map f) _ _))

/-- The entire raw derived associator retains both original Q contractions and the original
associator. -/
def rawBracketAssociator (d : GeneratedFunctorialReplacements.Data (C := C)) :
    rawLeftBracket d ≅ rawRightBracket d :=
  leftBracketContractionIso d ≪≫ actualBracketAssociator d ≪≫ (rightBracketContractionIso d).symm

instance leftBracketLifting (d : GeneratedFunctorialReplacements.Data (C := C)) :
    Localization.Lifting₃ π π π (weakEquivalences C) (weakEquivalences C) (weakEquivalences C)
      (rawLeftBracket d) (bifunctorComp₁₂ (tensor d) (tensor d)) := by
  let _ : Localization.Lifting₂ π π (weakEquivalences C) (weakEquivalences C)
      (replacedTensor d ⋙ (whiskeringRight C C Ho).obj π) (tensor d) := by
    change Localization.Lifting₂ π π (weakEquivalences C) (weakEquivalences C) (raw d) (tensor d)
    infer_instance
  exact Localization.Lifting₃.bifunctorComp₁₂ π π π π π
    (weakEquivalences C) (weakEquivalences C) (weakEquivalences C) (weakEquivalences C)
    (replacedTensor d) (replacedTensor d) (tensor d) (tensor d)

instance rightBracketLifting (d : GeneratedFunctorialReplacements.Data (C := C)) :
    Localization.Lifting₃ π π π (weakEquivalences C) (weakEquivalences C) (weakEquivalences C)
      (rawRightBracket d) (bifunctorComp₂₃ (tensor d) (tensor d)) := by
  let _ : Localization.Lifting₂ π π (weakEquivalences C) (weakEquivalences C)
      (replacedTensor d ⋙ (whiskeringRight C C Ho).obj π) (tensor d) := by
    change Localization.Lifting₂ π π (weakEquivalences C) (weakEquivalences C) (raw d) (tensor d)
    infer_instance
  exact Localization.Lifting₃.bifunctorComp₂₃ π π π π π
    (weakEquivalences C) (weakEquivalences C) (weakEquivalences C) (weakEquivalences C)
    (replacedTensor d) (replacedTensor d) (tensor d) (tensor d)

/-- The full actual derived associator on every homotopy object and every homotopy arrow. -/
def derivedAssociator (d : GeneratedFunctorialReplacements.Data (C := C)) :
    bifunctorComp₁₂ (tensor d) (tensor d) ≅ bifunctorComp₂₃ (tensor d) (tensor d) :=
  Localization.lift₃NatIso π π π (weakEquivalences C) (weakEquivalences C) (weakEquivalences C)
    (rawLeftBracket d) (rawRightBracket d)
    (bifunctorComp₁₂ (tensor d) (tensor d)) (bifunctorComp₂₃ (tensor d) (tensor d))
    (rawBracketAssociator d)

end HomotopicalAlgebra.DerivedTensorConstructions

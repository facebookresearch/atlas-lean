/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Codex
module

public import MathlibExt.AlgebraicTopology.ModelCategory.DerivedTensorConstructions
public import MathlibExt.AlgebraicTopology.ModelCategory.MonoidalUnitReplacementComparison

/-!
# Both actual derived tensor unitors with the original unit replacement

The unit is the image of the actual tensor unit. Its calculation uses the
same chosen `Q(𝟙)` and original Q counit, the actual left/right unitors, and
the original counit on every input. The established monoidal unit witness
is transported to this exact Q-unit map by the existing lifting comparison.
The tensor unit is not assumed cofibrant.

Source: Hovey, *Model Categories*, Theorem 4.3.2 and its explicit unit maps.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u v

open CategoryTheory Limits MonoidalCategory MorphismProperty Functor
open scoped MonoidalClosed

namespace HomotopicalAlgebra.DerivedTensorConstructions

variable {C : Type u} [Category.{v} C] [ModelCategory C]
  [MonoidalCategory C] [SymmetricCategory C] [MonoidalClosed C]
  [IsClosedSymmetricMonoidalModelCategory C]

local notation "Ho" => MorphismProperty.Localization (weakEquivalences C)
local notation "π" => MorphismProperty.Q (weakEquivalences C)

/-- The actual chosen Q-unit replacement inherits the established unit axiom by its original lifting
comparison. -/
def chosenUnitWitness (d : GeneratedFunctorialReplacements.Data (C := C)) :
    MonoidalUnitAxiomWitness C :=
  (IsClosedSymmetricMonoidalModelCategory.pushoutProductAxiom
      (C := C)).unitAxiomWitnessOfReplacementAndWitness
    (Classical.choice (IsClosedSymmetricMonoidalModelCategory.unit_axiom (C := C)))
    (show d.Q.obj (𝟙_ C) ⟶ 𝟙_ C from d.q.app (𝟙_ C))
    (d.q_cofibrant _) (d.q_trivialFibration _)

/-- The source of this unit witness is the exact original Q-unit object. -/
theorem chosenUnitWitness_Q (d : GeneratedFunctorialReplacements.Data (C := C)) :
    (chosenUnitWitness d).Q = d.Q.obj (𝟙_ C) := rfl

/-- Its entire unit map is the exact original chosen Q counit. -/
theorem chosenUnitWitness_q (d : GeneratedFunctorialReplacements.Data (C := C)) :
    (chosenUnitWitness d).q = d.q.app (𝟙_ C) := rfl

omit [SymmetricCategory C] [MonoidalClosed C] [IsClosedSymmetricMonoidalModelCategory C] in
/-- The original left unit transformation uses the Q-unit counit, the original left unitor, and the
input counit. -/
def leftUnitOriginal (d : GeneratedFunctorialReplacements.Data (C := C)) :
    (replacedTensor d).obj (𝟙_ C) ⟶ 𝟭 C :=
  whiskerLeft d.Q ((curriedTensor C).map (d.q.app (𝟙_ C))) ≫
    (isoWhiskerLeft d.Q (leftUnitorNatIso C)).hom ≫ d.Q.rightUnitor.hom ≫ d.q

omit [SymmetricCategory C] [MonoidalClosed C] [IsClosedSymmetricMonoidalModelCategory C] in
/-- The original right unit transformation retains the same original three maps on the other side.
-/
def rightUnitOriginal (d : GeneratedFunctorialReplacements.Data (C := C)) :
    (replacedTensor d).flip.obj (𝟙_ C) ⟶ 𝟭 C :=
  whiskerLeft d.Q ((tensoringRight C).map (d.q.app (𝟙_ C))) ≫
    (isoWhiskerLeft d.Q (rightUnitorNatIso C)).hom ≫ d.Q.rightUnitor.hom ≫ d.q

omit [SymmetricCategory C] [MonoidalClosed C] [IsClosedSymmetricMonoidalModelCategory C] in
/-- Every actual left unit component is the original Q-unit tensor map and original unitor/counit.
-/
theorem leftUnitOriginal_app (d : GeneratedFunctorialReplacements.Data (C := C)) (X : C) :
    (leftUnitOriginal d).app X =
      (d.q.app (𝟙_ C) ▷ d.Q.obj X) ≫ (λ_ (d.Q.obj X)).hom ≫ d.q.app X := by
  dsimp [leftUnitOriginal]
  simp

omit [SymmetricCategory C] [MonoidalClosed C] [IsClosedSymmetricMonoidalModelCategory C] in
/-- Every actual right unit component is the same calculation on the other tensor side. -/
theorem rightUnitOriginal_app (d : GeneratedFunctorialReplacements.Data (C := C)) (X : C) :
    (rightUnitOriginal d).app X =
      (d.Q.obj X ◁ d.q.app (𝟙_ C)) ≫ (ρ_ (d.Q.obj X)).hom ≫ d.q.app X := by
  dsimp [rightUnitOriginal]
  simp

/-- The source monoidal unit axiom proves weakness of the exact left-unit calculation. -/
theorem leftUnitOriginal_weak (d : GeneratedFunctorialReplacements.Data (C := C)) (X : C) :
    weakEquivalences C ((leftUnitOriginal d).app X) := by
  rw [leftUnitOriginal_app]
  apply (weakEquivalences C).comp_mem
  · exact (chosenUnitWitness d).tensor_weak _ (d.q_cofibrant X)
  · exact (weakEquivalences C).comp_mem _ _ (mem_weakEquivalences _) (d.q_trivialFibration X).2

/-- The same established unit witness proves weakness of the exact right-unit calculation. -/
theorem rightUnitOriginal_weak (d : GeneratedFunctorialReplacements.Data (C := C)) (X : C) :
    weakEquivalences C ((rightUnitOriginal d).app X) := by
  rw [rightUnitOriginal_app]
  apply (weakEquivalences C).comp_mem
  · exact (chosenUnitWitness d).tensorLeft_weak _ (d.q_cofibrant X)
  · exact (weakEquivalences C).comp_mem _ _ (mem_weakEquivalences _) (d.q_trivialFibration X).2

omit [SymmetricCategory C] [MonoidalClosed C] [IsClosedSymmetricMonoidalModelCategory C] in
/-- The entire original left-unit map is localized, retaining all input morphisms. -/
def leftUnitRaw (d : GeneratedFunctorialReplacements.Data (C := C)) :
    (raw d).obj (𝟙_ C) ⟶ π :=
  whiskerRight (leftUnitOriginal d) π ≫ (π).leftUnitor.hom

omit [SymmetricCategory C] [MonoidalClosed C] [IsClosedSymmetricMonoidalModelCategory C] in
/-- The entire original right-unit map is localized with the same canonical projection. -/
def rightUnitRaw (d : GeneratedFunctorialReplacements.Data (C := C)) :
    (raw d).flip.obj (𝟙_ C) ⟶ π :=
  whiskerRight (rightUnitOriginal d) π ≫ (π).leftUnitor.hom

omit [SymmetricCategory C] [MonoidalClosed C] [IsClosedSymmetricMonoidalModelCategory C] in
/-- The complete localized left component is the same actual original unit map. -/
theorem leftUnitRaw_app (d : GeneratedFunctorialReplacements.Data (C := C)) (X : C) :
    (leftUnitRaw d).app X = (π).map ((leftUnitOriginal d).app X) := by
  dsimp [leftUnitRaw]
  simp

omit [SymmetricCategory C] [MonoidalClosed C] [IsClosedSymmetricMonoidalModelCategory C] in
/-- The complete localized right component retains the same original unit map. -/
theorem rightUnitRaw_app (d : GeneratedFunctorialReplacements.Data (C := C)) (X : C) :
    (rightUnitRaw d).app X = (π).map ((rightUnitOriginal d).app X) := by
  dsimp [rightUnitRaw]
  simp

/-- The original left-unit comparison is invertible on every actual source object. -/
theorem leftUnitRaw_isIso (d : GeneratedFunctorialReplacements.Data (C := C)) (X : C) :
    IsIso ((leftUnitRaw d).app X) := by
  rw [leftUnitRaw_app]
  exact Localization.inverts (π) (weakEquivalences C) _ (leftUnitOriginal_weak d X)

/-- The original right-unit comparison is invertible on every actual source object. -/
theorem rightUnitRaw_isIso (d : GeneratedFunctorialReplacements.Data (C := C)) (X : C) :
    IsIso ((rightUnitRaw d).app X) := by
  rw [rightUnitRaw_app]
  exact Localization.inverts (π) (weakEquivalences C) _ (rightUnitOriginal_weak d X)

/-- The complete original left-unit comparison is a natural isomorphism. -/
def leftUnitRawIso (d : GeneratedFunctorialReplacements.Data (C := C)) : (raw d).obj (𝟙_ C) ≅ π :=
    by
  let _ : ∀ X, IsIso ((leftUnitRaw d).app X) := leftUnitRaw_isIso d
  let _ : IsIso (leftUnitRaw d) := NatIso.isIso_of_isIso_app _
  exact asIso (leftUnitRaw d)

/-- The complete original right-unit comparison has the actual inverse on all input maps. -/
def rightUnitRawIso (d : GeneratedFunctorialReplacements.Data (C := C)) :
    (raw d).flip.obj (𝟙_ C) ≅ π := by
  let _ : ∀ X, IsIso ((rightUnitRaw d).app X) := rightUnitRaw_isIso d
  let _ : IsIso (rightUnitRaw d) := NatIso.isIso_of_isIso_app _
  exact asIso (rightUnitRaw d)

/-- The actual derived left unitor on the whole original homotopy category. -/
def derivedLeftUnitor (d : GeneratedFunctorialReplacements.Data (C := C)) :
    (tensor d).obj ((π).obj (𝟙_ C)) ≅ 𝟭 Ho := by
  let _ : Localization.Lifting π (weakEquivalences C) ((raw d).obj (𝟙_ C))
      ((tensor d).obj ((π).obj (𝟙_ C))) :=
    Localization.Lifting₂.fst π π (weakEquivalences C) (weakEquivalences C) (raw d) (tensor d)
        (𝟙_ C)
  let _ : Localization.Lifting π (weakEquivalences C) π (𝟭 Ho) := ⟨(π).rightUnitor⟩
  exact Localization.liftNatIso π (weakEquivalences C) ((raw d).obj (𝟙_ C)) π
    ((tensor d).obj ((π).obj (𝟙_ C))) (𝟭 Ho) (leftUnitRawIso d)

/-- The actual derived right unitor on every original homotopy object and morphism. -/
def derivedRightUnitor (d : GeneratedFunctorialReplacements.Data (C := C)) :
    (tensor d).flip.obj ((π).obj (𝟙_ C)) ≅ 𝟭 Ho := by
  let _ : Localization.Lifting π (weakEquivalences C) ((raw d).flip.obj (𝟙_ C))
      ((tensor d).flip.obj ((π).obj (𝟙_ C))) :=
    Localization.Lifting₂.snd π π (weakEquivalences C) (weakEquivalences C) (raw d) (tensor d)
        (𝟙_ C)
  let _ : Localization.Lifting π (weakEquivalences C) π (𝟭 Ho) := ⟨(π).rightUnitor⟩
  exact Localization.liftNatIso π (weakEquivalences C) ((raw d).flip.obj (𝟙_ C)) π
    ((tensor d).flip.obj ((π).obj (𝟙_ C))) (𝟭 Ho) (rightUnitRawIso d)

end HomotopicalAlgebra.DerivedTensorConstructions

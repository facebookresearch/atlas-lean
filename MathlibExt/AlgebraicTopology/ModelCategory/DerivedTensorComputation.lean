/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Codex
module

public import MathlibExt.AlgebraicTopology.ModelCategory.DerivedTensorAssociator
public import MathlibExt.AlgebraicTopology.ModelCategory.DerivedTensorUnit
public import MathlibExt.AlgebraicTopology.ModelCategory.DerivedTensorSymmetry

/-!
# Original computation maps for the full chosen derived tensor coherence

The original Q counits compare both actual nested derived tensor words with
the corresponding ordinary tensor words on cofibrant endpoints. All three
variable naturalities and the associator computation use those same maps.
The unit computations retain the actual Q-unit counit and original unitors.

Source: Hovey, *Model Categories*, Theorem 4.3.2, printed pp. 116–117.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u v

open CategoryTheory Limits MonoidalCategory MorphismProperty Functor BraidedCategory
open scoped MonoidalClosed

namespace HomotopicalAlgebra.DerivedTensorConstructions

variable {C : Type u} [Category.{v} C] [ModelCategory C]
  [MonoidalCategory C] [SymmetricCategory C] [MonoidalClosed C]
  [IsClosedSymmetricMonoidalModelCategory C]

local notation "Ho" => MorphismProperty.Localization (weakEquivalences C)
local notation "π" => MorphismProperty.Q (weakEquivalences C)

/-- Closure uses the actual original pushout-product axiom. -/
theorem tensor_isCofibrant (X Y : C) [IsCofibrant X] [IsCofibrant Y] :
    IsCofibrant (X ⊗ Y) :=
  (IsClosedSymmetricMonoidalModelCategory.pushoutProductAxiom (C := C)).isCofibrant_tensorObj X Y

/-- The actual left nested tensor projection comparison. -/
def leftBracketComparison (d : GeneratedFunctorialReplacements.Data (C := C)) (X Y Z : C) :
    ((tensor d).obj (((tensor d).obj ((π).obj X)).obj ((π).obj Y))).obj ((π).obj Z) ≅
      (π).obj (d.Q.obj (d.Q.obj X ⊗ d.Q.obj Y) ⊗ d.Q.obj Z) :=
  (((Localization.Lifting₃.iso π π π (weakEquivalences C) (weakEquivalences C)
    (weakEquivalences C) (rawLeftBracket d) (bifunctorComp₁₂ (tensor d) (tensor d))).app X).app
        Y).app Z

/-- The actual right nested tensor projection comparison. -/
def rightBracketComparison (d : GeneratedFunctorialReplacements.Data (C := C)) (X Y Z : C) :
    ((tensor d).obj ((π).obj X)).obj (((tensor d).obj ((π).obj Y)).obj ((π).obj Z)) ≅
      (π).obj (d.Q.obj X ⊗ d.Q.obj (d.Q.obj Y ⊗ d.Q.obj Z)) :=
  (((Localization.Lifting₃.iso π π π (weakEquivalences C) (weakEquivalences C)
    (weakEquivalences C) (rawRightBracket d) (bifunctorComp₂₃ (tensor d) (tensor d))).app X).app
        Y).app Z

/-- The left projection uses exactly the two original bifunctor comparisons. -/
theorem leftBracketComparison_hom (d : GeneratedFunctorialReplacements.Data (C := C)) (X Y Z : C) :
    (leftBracketComparison d X Y Z).hom =
      ((tensor d).map (comparison d X Y).hom).app ((π).obj Z) ≫
        (comparison d (d.Q.obj X ⊗ d.Q.obj Y) Z).hom := by
  dsimp [leftBracketComparison, leftBracketLifting, Localization.Lifting₃.bifunctorComp₁₂,
    comparison, projectionIso]
  rfl

/-- The right projection uses the same two comparisons in the other order. -/
theorem rightBracketComparison_hom (d : GeneratedFunctorialReplacements.Data (C := C)) (X Y Z : C) :
    (rightBracketComparison d X Y Z).hom =
      ((tensor d).obj ((π).obj X)).map (comparison d Y Z).hom ≫
        (comparison d X (d.Q.obj Y ⊗ d.Q.obj Z)).hom := by
  dsimp [rightBracketComparison, rightBracketLifting, Localization.Lifting₃.bifunctorComp₂₃,
    comparison, projectionIso]
  rfl

/-- The lifted associator keeps both original Q contractions and the original associator. -/
theorem derivedAssociator_hom_source (d : GeneratedFunctorialReplacements.Data (C := C))
    (X Y Z : C) :
    (((derivedAssociator d).hom.app ((π).obj X)).app ((π).obj Y)).app ((π).obj Z) =
      (leftBracketComparison d X Y Z).hom ≫
        (((rawBracketAssociator d).hom.app X).app Y).app Z ≫
          (rightBracketComparison d X Y Z).inv :=
  Localization.lift₃NatTrans_app_app_app π π π (weakEquivalences C)
    (weakEquivalences C) (weakEquivalences C) (rawLeftBracket d) (rawRightBracket d)
    (bifunctorComp₁₂ (tensor d) (tensor d)) (bifunctorComp₂₃ (tensor d) (tensor d))
    (rawBracketAssociator d).hom X Y Z

/-- Every original map in the first variable commutes with the ordinary cofibrant computation. -/
@[reassoc]
theorem cofibrantComparison_naturality_left (d : GeneratedFunctorialReplacements.Data (C := C))
    {X X' : C} (f : X ⟶ X') (Y : C) [IsCofibrant X] [IsCofibrant X'] [IsCofibrant Y] :
    ((tensor d).map ((π).map f)).app ((π).obj Y) ≫ (cofibrantComparison d X' Y).hom =
      (cofibrantComparison d X Y).hom ≫ (π).map (f ▷ Y) := by
  rw [cofibrantComparison_hom, cofibrantComparison_hom,
    reassoc_of% comparison_naturality_left d f Y]
  have h := cofibrantComparisonMap_naturality d f (𝟙 Y)
  simpa only [CategoryTheory.Functor.map_id, tensorHom_id,
    cofibrantComparisonMap, Category.assoc] using
    (comparison d X Y).hom ≫= h

/-- Every original second-variable map retains both actual Q counits in the computation. -/
@[reassoc]
theorem cofibrantComparison_naturality_right (d : GeneratedFunctorialReplacements.Data (C := C))
    (X : C) {Y Y' : C} (f : Y ⟶ Y') [IsCofibrant X] [IsCofibrant Y] [IsCofibrant Y'] :
    ((tensor d).obj ((π).obj X)).map ((π).map f) ≫ (cofibrantComparison d X Y').hom =
      (cofibrantComparison d X Y).hom ≫ (π).map (X ◁ f) := by
  rw [cofibrantComparison_hom, cofibrantComparison_hom,
    reassoc_of% comparison_naturality_right d X f]
  have h := cofibrantComparisonMap_naturality d (𝟙 X) f
  simpa only [CategoryTheory.Functor.map_id, id_tensorHom,
    cofibrantComparisonMap, Category.assoc] using
    (comparison d X Y).hom ≫= h

/-- The actual original counits define an ordinary comparison at every endpoint.
It is invertible when both endpoints are cofibrant, as proved separately. -/
def ordinaryComparison (d : GeneratedFunctorialReplacements.Data (C := C)) (X Y : C) :
    ((tensor d).obj ((π).obj X)).obj ((π).obj Y) ⟶ (π).obj (X ⊗ Y) :=
  (comparison d X Y).hom ≫ cofibrantComparisonMap d X Y

/-- The full left nested ordinary comparison keeps both actual inner and outer counits. -/
def leftOrdinaryComparison (d : GeneratedFunctorialReplacements.Data (C := C)) (X Y Z : C) :
    ((tensor d).obj (((tensor d).obj ((π).obj X)).obj ((π).obj Y))).obj ((π).obj Z) ⟶
      (π).obj ((X ⊗ Y) ⊗ Z) :=
  ((tensor d).map (ordinaryComparison d X Y)).app ((π).obj Z) ≫
    ordinaryComparison d (X ⊗ Y) Z

/-- The corresponding right nested comparison uses the same Q counits. -/
def rightOrdinaryComparison (d : GeneratedFunctorialReplacements.Data (C := C)) (X Y Z : C) :
    ((tensor d).obj ((π).obj X)).obj (((tensor d).obj ((π).obj Y)).obj ((π).obj Z)) ⟶
      (π).obj (X ⊗ (Y ⊗ Z)) :=
  ((tensor d).obj ((π).obj X)).map (ordinaryComparison d Y Z) ≫
    ordinaryComparison d X (Y ⊗ Z)

/-- The left nested Q counits contract to the original three-factor counit tensor. -/
theorem leftOrdinaryComparison_contract (d : GeneratedFunctorialReplacements.Data (C := C))
    (X Y Z : C) :
    leftOrdinaryComparison d X Y Z = (leftBracketComparison d X Y Z).hom ≫
      (((leftBracketContraction d).app X).app Y).app Z ≫
        (π).map ((d.q.app X ⊗ₘ d.q.app Y) ⊗ₘ d.q.app Z) := by
  let f : d.Q.obj X ⊗ d.Q.obj Y ⟶ X ⊗ Y := d.q.app X ⊗ₘ d.q.app Y
  have hq : d.Q.map f ≫ d.q.app (X ⊗ Y) = d.q.app (d.Q.obj X ⊗ d.Q.obj Y) ≫ f :=
    d.q.naturality f
  have ht : (d.Q.map f ▷ d.Q.obj Z) ≫ (d.q.app (X ⊗ Y) ⊗ₘ d.q.app Z) =
      (d.q.app (d.Q.obj X ⊗ d.Q.obj Y) ▷ d.Q.obj Z) ≫ (f ⊗ₘ d.q.app Z) := by
    simpa only [tensorHom_def, MonoidalCategory.comp_whiskerRight, Category.assoc,
      CategoryTheory.Functor.id_obj] using
      congrArg (fun a => (a ▷ d.Q.obj Z) ≫ ((X ⊗ Y) ◁ d.q.app Z)) hq
  dsimp [leftOrdinaryComparison, ordinaryComparison, cofibrantComparisonMap]
  rw [leftBracketComparison_hom, leftBracketContraction_app]
  simp only [Functor.map_comp, NatTrans.comp_app, Category.assoc]
  rw [reassoc_of% comparison_naturality_left d f Z, ← (π).map_comp, ht, (π).map_comp]

/-- The right nested contractions retain the same original three-factor maps. -/
theorem rightOrdinaryComparison_contract (d : GeneratedFunctorialReplacements.Data (C := C))
    (X Y Z : C) :
    rightOrdinaryComparison d X Y Z = (rightBracketComparison d X Y Z).hom ≫
      (((rightBracketContraction d).app X).app Y).app Z ≫
        (π).map (d.q.app X ⊗ₘ (d.q.app Y ⊗ₘ d.q.app Z)) := by
  let f : d.Q.obj Y ⊗ d.Q.obj Z ⟶ Y ⊗ Z := d.q.app Y ⊗ₘ d.q.app Z
  have hq : d.Q.map f ≫ d.q.app (Y ⊗ Z) = d.q.app (d.Q.obj Y ⊗ d.Q.obj Z) ≫ f :=
    d.q.naturality f
  have ht : (d.Q.obj X ◁ d.Q.map f) ≫ (d.q.app X ⊗ₘ d.q.app (Y ⊗ Z)) =
      (d.Q.obj X ◁ d.q.app (d.Q.obj Y ⊗ d.Q.obj Z)) ≫ (d.q.app X ⊗ₘ f) := by
    simpa only [tensorHom_def', MonoidalCategory.whiskerLeft_comp, Category.assoc,
      CategoryTheory.Functor.id_obj] using
      congrArg (fun a => (d.Q.obj X ◁ a) ≫ (d.q.app X ▷ (Y ⊗ Z))) hq
  dsimp [rightOrdinaryComparison, ordinaryComparison, cofibrantComparisonMap]
  rw [rightBracketComparison_hom, rightBracketContraction_app]
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% comparison_naturality_right d X f, ← (π).map_comp, ht, (π).map_comp]

/-- The raw associator contracts to the original associator with the same source maps. -/
theorem rawBracketAssociator_contract (d : GeneratedFunctorialReplacements.Data (C := C))
    (X Y Z : C) :
    (((rawBracketAssociator d).hom.app X).app Y).app Z ≫
        (((rightBracketContraction d).app X).app Y).app Z =
      (((leftBracketContraction d).app X).app Y).app Z ≫
        (π).map (α_ (d.Q.obj X) (d.Q.obj Y) (d.Q.obj Z)).hom := by
  let L := (((leftBracketContractionIso d).app X).app Y).app Z
  let R := (((rightBracketContractionIso d).app X).app Y).app Z
  change (L.hom ≫ (π).map (α_ (d.Q.obj X) (d.Q.obj Y) (d.Q.obj Z)).hom ≫ R.inv) ≫ R.hom =
    L.hom ≫ (π).map (α_ (d.Q.obj X) (d.Q.obj Y) (d.Q.obj Z)).hom
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- The complete derived associator commutes with the actual ordinary tensor comparison.
This equation uses every original endpoint; invertibility is needed only when cancelling
the ordinary computation on cofibrant endpoints. -/
@[reassoc]
theorem derivedAssociator_ordinaryComparison (d : GeneratedFunctorialReplacements.Data (C := C))
    (X Y Z : C) :
    (((derivedAssociator d).hom.app ((π).obj X)).app ((π).obj Y)).app ((π).obj Z) ≫
        rightOrdinaryComparison d X Y Z =
      leftOrdinaryComparison d X Y Z ≫ (π).map (α_ X Y Z).hom := by
  rw [derivedAssociator_hom_source, leftOrdinaryComparison_contract,
    rightOrdinaryComparison_contract]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [reassoc_of% rawBracketAssociator_contract d X Y Z]
  have h := (π).congr_map (associator_naturality (d.q.app X) (d.q.app Y) (d.q.app Z))
  simp only [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.id_obj] at h
  rw [← h]

/-- The ordinary two-factor map is the same original cofibrant computation map. -/
theorem ordinaryComparison_cofibrant (d : GeneratedFunctorialReplacements.Data (C := C))
    (X Y : C) [IsCofibrant X] [IsCofibrant Y] :
    ordinaryComparison d X Y = (cofibrantComparison d X Y).hom := rfl

/-- The left nested computation is invertible at its actual cofibrant tensor endpoints. -/
def leftCofibrantComparison (d : GeneratedFunctorialReplacements.Data (C := C))
    (X Y Z : C) [IsCofibrant X] [IsCofibrant Y] [IsCofibrant Z] :
    ((tensor d).obj (((tensor d).obj ((π).obj X)).obj ((π).obj Y))).obj ((π).obj Z) ≅
      (π).obj ((X ⊗ Y) ⊗ Z) := by
  let _ : IsCofibrant (X ⊗ Y) := tensor_isCofibrant X Y
  exact ((tensor d).mapIso (cofibrantComparison d X Y)).app ((π).obj Z) ≪≫
    cofibrantComparison d (X ⊗ Y) Z

/-- The right nested computation uses the same actual cofibrant factors and counits. -/
def rightCofibrantComparison (d : GeneratedFunctorialReplacements.Data (C := C))
    (X Y Z : C) [IsCofibrant X] [IsCofibrant Y] [IsCofibrant Z] :
    ((tensor d).obj ((π).obj X)).obj (((tensor d).obj ((π).obj Y)).obj ((π).obj Z)) ≅
      (π).obj (X ⊗ (Y ⊗ Z)) := by
  let _ : IsCofibrant (Y ⊗ Z) := tensor_isCofibrant Y Z
  exact ((tensor d).obj ((π).obj X)).mapIso (cofibrantComparison d Y Z) ≪≫
    cofibrantComparison d X (Y ⊗ Z)

/-- The left nested isomorphism retains the actual ordinary comparison function. -/
theorem leftCofibrantComparison_hom (d : GeneratedFunctorialReplacements.Data (C := C))
    (X Y Z : C) [IsCofibrant X] [IsCofibrant Y] [IsCofibrant Z] :
    (leftCofibrantComparison d X Y Z).hom = leftOrdinaryComparison d X Y Z := rfl

/-- The same ordinary right comparison is the hom of its actual cofibrant isomorphism. -/
theorem rightCofibrantComparison_hom (d : GeneratedFunctorialReplacements.Data (C := C))
    (X Y Z : C) [IsCofibrant X] [IsCofibrant Y] [IsCofibrant Z] :
    (rightCofibrantComparison d X Y Z).hom = rightOrdinaryComparison d X Y Z := rfl

/-- The actual derived associator on cofibrant representatives is exactly the original
associator between both full computation isomorphisms. -/
theorem derivedAssociator_cofibrant (d : GeneratedFunctorialReplacements.Data (C := C))
    (X Y Z : C) [IsCofibrant X] [IsCofibrant Y] [IsCofibrant Z] :
    (((derivedAssociator d).hom.app ((π).obj X)).app ((π).obj Y)).app ((π).obj Z) =
      (leftCofibrantComparison d X Y Z).hom ≫ (π).map (α_ X Y Z).hom ≫
        (rightCofibrantComparison d X Y Z).inv := by
  apply (cancel_mono (rightCofibrantComparison d X Y Z).hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [leftCofibrantComparison_hom, rightCofibrantComparison_hom]
  exact derivedAssociator_ordinaryComparison d X Y Z

/-- The inverse derived associator keeps the inverse original associator and the same
two actual computation isomorphisms in the opposite order. -/
theorem derivedAssociator_inv_cofibrant (d : GeneratedFunctorialReplacements.Data (C := C))
    (X Y Z : C) [IsCofibrant X] [IsCofibrant Y] [IsCofibrant Z] :
    (((derivedAssociator d).inv.app ((π).obj X)).app ((π).obj Y)).app ((π).obj Z) =
      (rightCofibrantComparison d X Y Z).hom ≫ (π).map (α_ X Y Z).inv ≫
        (leftCofibrantComparison d X Y Z).inv := by
  let A := (((derivedAssociator d).app ((π).obj X)).app ((π).obj Y)).app ((π).obj Z)
  have h : A = leftCofibrantComparison d X Y Z ≪≫ (π).mapIso (α_ X Y Z) ≪≫
      (rightCofibrantComparison d X Y Z).symm := by
    apply Iso.ext
    simpa only [A, Iso.app_hom, Iso.trans_hom, Iso.symm_hom, CategoryTheory.Functor.mapIso_hom,
      Category.assoc] using derivedAssociator_cofibrant d X Y Z
  have hi := congrArg (fun e => e.inv) h
  simpa only [A, Iso.app_inv, Iso.trans_inv, Iso.symm_inv, CategoryTheory.Functor.mapIso_inv,
    Category.assoc] using hi

/-- All original first-variable arrows commute with the ordinary comparison, including
the fixed actual unit endpoint when it is not cofibrant. -/
@[reassoc]
theorem ordinaryComparison_naturality_left (d : GeneratedFunctorialReplacements.Data (C := C))
    {X X' : C} (f : X ⟶ X') (Y : C) :
    ((tensor d).map ((π).map f)).app ((π).obj Y) ≫ ordinaryComparison d X' Y =
      ordinaryComparison d X Y ≫ (π).map (f ▷ Y) := by
  unfold ordinaryComparison
  rw [reassoc_of% comparison_naturality_left d f Y]
  have h := cofibrantComparisonMap_naturality d f (𝟙 Y)
  simpa only [CategoryTheory.Functor.map_id, tensorHom_id, Category.assoc] using
    (comparison d X Y).hom ≫= h

/-- The same comparison retains every original second-variable arrow and actual counit. -/
@[reassoc]
theorem ordinaryComparison_naturality_right (d : GeneratedFunctorialReplacements.Data (C := C))
    (X : C) {Y Y' : C} (f : Y ⟶ Y') :
    ((tensor d).obj ((π).obj X)).map ((π).map f) ≫ ordinaryComparison d X Y' =
      ordinaryComparison d X Y ≫ (π).map (X ◁ f) := by
  unfold ordinaryComparison
  rw [reassoc_of% comparison_naturality_right d X f]
  have h := cofibrantComparisonMap_naturality d (𝟙 X) f
  simpa only [CategoryTheory.Functor.map_id, id_tensorHom, Category.assoc] using
    (comparison d X Y).hom ≫= h

omit [SymmetricCategory C] [MonoidalClosed C] [IsClosedSymmetricMonoidalModelCategory C] in
/-- The exact original left-unit point-set map is the ordinary comparison followed by
the original left unitor; its Q-unit source is unchanged. -/
theorem leftUnitOriginal_tensorCounit (d : GeneratedFunctorialReplacements.Data (C := C)) (X : C) :
    (leftUnitOriginal d).app X = (d.q.app (𝟙_ C) ⊗ₘ d.q.app X) ≫ (λ_ X).hom := by
  rw [leftUnitOriginal_app]
  let qX : d.Q.obj X ⟶ X := d.q.app X
  let qUnit : d.Q.obj (𝟙_ C) ⟶ 𝟙_ C := d.q.app (𝟙_ C)
  change (qUnit ▷ d.Q.obj X) ≫ (λ_ (d.Q.obj X)).hom ≫ qX = (qUnit ⊗ₘ qX) ≫ (λ_ X).hom
  rw [tensorHom_def, Category.assoc, leftUnitor_naturality qX]

omit [SymmetricCategory C] [MonoidalClosed C] [IsClosedSymmetricMonoidalModelCategory C] in
/-- The right-unit calculation keeps the same original Q-unit and input counits. -/
theorem rightUnitOriginal_tensorCounit (d : GeneratedFunctorialReplacements.Data (C := C)) (X : C) :
    (rightUnitOriginal d).app X = (d.q.app X ⊗ₘ d.q.app (𝟙_ C)) ≫ (ρ_ X).hom := by
  rw [rightUnitOriginal_app]
  let qX : d.Q.obj X ⟶ X := d.q.app X
  let qUnit : d.Q.obj (𝟙_ C) ⟶ 𝟙_ C := d.q.app (𝟙_ C)
  change (d.Q.obj X ◁ qUnit) ≫ (ρ_ (d.Q.obj X)).hom ≫ qX = (qX ⊗ₘ qUnit) ≫ (ρ_ X).hom
  rw [tensorHom_def', Category.assoc, rightUnitor_naturality qX]

/-- The full derived left unitor retains the actual ordinary comparison and original unitor. -/
theorem derivedLeftUnitor_hom_source (d : GeneratedFunctorialReplacements.Data (C := C)) (X : C) :
    (derivedLeftUnitor d).hom.app ((π).obj X) =
      ordinaryComparison d (𝟙_ C) X ≫ (π).map (λ_ X).hom := by
  dsimp [derivedLeftUnitor]
  rw [Localization.liftNatTrans_app]
  change (comparison d (𝟙_ C) X).hom ≫ (leftUnitRaw d).app X ≫ 𝟙 _ = _
  rw [Category.comp_id, leftUnitRaw_app, leftUnitOriginal_tensorCounit, (π).map_comp]
  simp only [ordinaryComparison, cofibrantComparisonMap, Category.assoc]

/-- The actual derived right unitor uses the same full ordinary comparison on the other side. -/
theorem derivedRightUnitor_hom_source (d : GeneratedFunctorialReplacements.Data (C := C)) (X : C) :
    (derivedRightUnitor d).hom.app ((π).obj X) =
      ordinaryComparison d X (𝟙_ C) ≫ (π).map (ρ_ X).hom := by
  dsimp [derivedRightUnitor]
  rw [Localization.liftNatTrans_app]
  change (comparison d X (𝟙_ C)).hom ≫ (rightUnitRaw d).app X ≫ 𝟙 _ = _
  rw [Category.comp_id, rightUnitRaw_app, rightUnitOriginal_tensorCounit, (π).map_comp]
  simp only [ordinaryComparison, cofibrantComparisonMap, Category.assoc]

/-- The full source unit triangle follows from the original triangle and actual Q-unit witness.
Only the two variable endpoints are cofibrant; the tensor unit is unrestricted. -/
theorem derivedTriangle_cofibrant (d : GeneratedFunctorialReplacements.Data (C := C))
    (X Y : C) [IsCofibrant X] [IsCofibrant Y] :
    (((derivedAssociator d).hom.app ((π).obj X)).app ((π).obj (𝟙_ C))).app ((π).obj Y) ≫
        ((tensor d).obj ((π).obj X)).map ((derivedLeftUnitor d).hom.app ((π).obj Y)) =
      ((tensor d).map ((derivedRightUnitor d).hom.app ((π).obj X))).app ((π).obj Y) := by
  apply (cancel_mono (cofibrantComparison d X Y).hom).mp
  rw [← ordinaryComparison_cofibrant, derivedLeftUnitor_hom_source, derivedRightUnitor_hom_source]
  simp only [CategoryTheory.Functor.map_comp, NatTrans.comp_app, Category.assoc]
  rw [ordinaryComparison_naturality_right]
  rw [← Category.assoc
    (((tensor d).obj ((π).obj X)).map (ordinaryComparison d (𝟙_ C) Y))
    (ordinaryComparison d X (𝟙_ C ⊗ Y)) ((π).map (X ◁ (λ_ Y).hom))]
  change (((derivedAssociator d).hom.app ((π).obj X)).app ((π).obj (𝟙_ C))).app ((π).obj Y) ≫
      rightOrdinaryComparison d X (𝟙_ C) Y ≫ (π).map ((X ◁ (λ_ Y).hom)) = _
  rw [derivedAssociator_ordinaryComparison_assoc, ← (π).map_comp, MonoidalCategory.triangle]
  dsimp [leftOrdinaryComparison]
  simp only [Category.assoc]
  rw [← ordinaryComparison_naturality_left]

/-- The actual derived braid commutes with the original ordinary tensor comparison on all sources.
-/
@[reassoc]
theorem derivedBraiding_ordinaryComparison (d : GeneratedFunctorialReplacements.Data (C := C))
    (X Y : C) :
    ((derivedBraiding d).hom.app ((π).obj X)).app ((π).obj Y) ≫ ordinaryComparison d Y X =
      ordinaryComparison d X Y ≫ (π).map (β_ X Y).hom := by
  rw [derivedBraiding_hom_source]
  unfold ordinaryComparison cofibrantComparisonMap
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  have h := (π).congr_map (braiding_naturality (d.q.app X) (d.q.app Y))
  simp only [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.id_obj] at h
  rw [← h]

/-- The actual source braiding on cofibrant objects is the original braiding between
the two exact ordinary computation isomorphisms. -/
theorem derivedBraiding_cofibrant (d : GeneratedFunctorialReplacements.Data (C := C))
    (X Y : C) [IsCofibrant X] [IsCofibrant Y] :
    ((derivedBraiding d).hom.app ((π).obj X)).app ((π).obj Y) =
      (cofibrantComparison d X Y).hom ≫ (π).map (β_ X Y).hom ≫
        (cofibrantComparison d Y X).inv := by
  apply (cancel_mono (cofibrantComparison d Y X).hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [← ordinaryComparison_cofibrant, ← ordinaryComparison_cofibrant]
  exact derivedBraiding_ordinaryComparison d X Y

end HomotopicalAlgebra.DerivedTensorConstructions

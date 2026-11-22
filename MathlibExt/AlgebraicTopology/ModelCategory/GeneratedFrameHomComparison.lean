/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Attribution for this imported development.
Author: @toskua, Codex
-/

-- Author: @toskua, Codex
module

public import MathlibExt.AlgebraicTopology.ModelCategory.LeftFrameHomWeakEquivalence
public import MathlibExt.AlgebraicTopology.ModelCategory.ResolutionHomBisimplicial
public import MathlibExt.AlgebraicTopology.ModelCategory.GeneratedFrameHomComplex
public import MathlibExt.AlgebraicTopology.ModelCategory.GeneratedRightMappingEnrichment
public import MathlibExt.AlgebraicTopology.ModelCategory.HomotopyCategory
public import MathlibExt.AlgebraicTopology.SimplicialSet.BisimplicialDiagonalWeakEquivalence

/-!
# The original left and right function complexes have the same genuine diagonal

The generic comparison uses the actual bisimplicial coefficient Hom object.
Original augmentation components give outer-row weak equivalences by the bare
right-frame Brown law.  Original coaugmentation components give inner-row weak
equivalences by its ordinary-opposite left-frame law.  The existing diagonal
theorem proves both complete original comparison maps weak.

The generated specializations retain the same original Q/R, both source
factor factories, and the genuine generated left and right frames.  The raw
comparisons use actual cofibrant sources and fibrant targets.  Their whole
source and target naturalities identify the left-frame mapping test with the
original generated derived right-Hom test.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe w u v

open CategoryTheory Limits MorphismProperty Opposite
open scoped Simplicial SSet.modelCategoryQuillen

namespace HomotopicalAlgebra.GeneratedFrameHomComparison

variable {C : Type u} [Category.{v} C] [ModelCategory C]

section Generic

/-- The whole original augmentation comparison is weak by its genuine outer-row maps. -/
theorem fromAugmentation_weak (A : CosimplicialObject C) (B : SimplicialObject C) {X : C}
    (a : A ⟶ (CosimplicialObject.const C).obj X)
    (hA : ∀ j, cofibrations C (ReedyStructure.latchingMap SimplexCategory.reedy A j))
    (hB : ∀ j, fibrations C (ReedyStructure.matchingMap SimplexCategory.reedyOp B j))
    (ha : ∀ j, weakEquivalences C (a.app j)) [IsCofibrant X] :
    WeakEquivalence (ResolutionHomComplex.fromAugmentation a B) := by
  have hd : weakEquivalences SSet.{v}
      (SSet.simplicialDiagonalFunctor.map (ResolutionHomBisimplicial.precomp a B)) := by
    change SSet.realizationWeakEquivalences _
    apply SSet.simplicialDiagonal_map_mem_realizationWeakEquivalences
    intro n
    let _ : IsCofibrant (A.obj ⦋n⦌) :=
      LeftFrameHomWeakEquivalence.coefficient_isCofibrant A hA ⦋n⦌
    let _ : IsCofibrant (((CosimplicialObject.const C).obj X).obj ⦋n⦌) :=
      (inferInstance : IsCofibrant X)
    let _ : WeakEquivalence (a.app ⦋n⦌) := (weakEquivalence_iff _).mpr (ha ⦋n⦌)
    change SSet.realizationWeakEquivalences (RightFrameHomBoundary.precomp (a.app ⦋n⦌) B)
    exact (weakEquivalence_iff _).mp (RightFrameHomBoundary.precomp_weak (a.app ⦋n⦌) B hB)
  exact (weakEquivalence_iff _).mpr
    (((weakEquivalences SSet.{v}).arrow_mk_iso_iff
      (Arrow.isoMk
        (ResolutionHomBisimplicial.diagonalIso ((CosimplicialObject.const C).obj X) B)
        (ResolutionHomBisimplicial.diagonalIso A B)
        (ResolutionHomBisimplicial.diagonal_precomp a B).symm)).mp hd)

/-- The whole original coaugmentation comparison is weak by its genuine inner-row maps. -/
theorem fromCoaugmentation_weak (A : CosimplicialObject C) (B : SimplicialObject C) {Y : C}
    (b : (SimplicialObject.const C).obj Y ⟶ B)
    (hA : ∀ j, cofibrations C (ReedyStructure.latchingMap SimplexCategory.reedy A j))
    (hB : ∀ j, fibrations C (ReedyStructure.matchingMap SimplexCategory.reedyOp B j))
    (hb : ∀ j, weakEquivalences C (b.app j)) [IsFibrant Y] :
    WeakEquivalence (ResolutionHomComplex.fromCoaugmentation A b) := by
  have hd : weakEquivalences SSet.{v}
      (SSet.simplicialDiagonalFunctor.map (ResolutionHomBisimplicial.postcomp A b)) := by
    change SSet.realizationWeakEquivalences _
    apply SSet.simplicialDiagonal_map_mem_realizationWeakEquivalences_of_inner_rows
    intro n
    let _ : IsFibrant (B.obj (op ⦋n⦌)) :=
      RightFrameHornGeometry.degree_isFibrant B hB (op ⦋n⦌)
    let _ : IsFibrant (((SimplicialObject.const C).obj Y).obj (op ⦋n⦌)) :=
      (inferInstance : IsFibrant Y)
    let _ : WeakEquivalence (b.app (op ⦋n⦌)) := (weakEquivalence_iff _).mpr (hb (op ⦋n⦌))
    have hp : WeakEquivalence
        (ResolutionHomComplex.postcomp A ((SimplicialObject.const C).map (b.app (op ⦋n⦌)))) :=
      LeftFrameHomWeakEquivalence.postcomp_weak A hA (b.app (op ⦋n⦌))
    exact ((weakEquivalences SSet.{v}).arrow_mk_iso_iff
      (Arrow.isoMk
        (ResolutionHomBisimplicial.innerRowIso A ((SimplicialObject.const C).obj Y) (op ⦋n⦌))
        (ResolutionHomBisimplicial.innerRowIso A B (op ⦋n⦌))
        (ResolutionHomBisimplicial.innerRowIso_postcomp A b (op ⦋n⦌)).symm)).mpr
      ((weakEquivalence_iff _).mp hp)
  exact (weakEquivalence_iff _).mpr
    (((weakEquivalences SSet.{v}).arrow_mk_iso_iff
      (Arrow.isoMk
        (ResolutionHomBisimplicial.diagonalIso A ((SimplicialObject.const C).obj Y))
        (ResolutionHomBisimplicial.diagonalIso A B)
        (ResolutionHomBisimplicial.diagonal_postcomp A b).symm)).mp hd)

/-- The actual augmentation map into the genuine diagonal is weak. -/
theorem fromAugmentation_diagonal_weak (A : CosimplicialObject C) (B : SimplicialObject C) {X : C}
    (a : A ⟶ (CosimplicialObject.const C).obj X)
    (hA : ∀ j, cofibrations C (ReedyStructure.latchingMap SimplexCategory.reedy A j))
    (hB : ∀ j, fibrations C (ReedyStructure.matchingMap SimplexCategory.reedyOp B j))
    (ha : ∀ j, weakEquivalences C (a.app j)) [IsCofibrant X] :
    WeakEquivalence (ResolutionHomBisimplicial.fromAugmentation a B) := by
  let _ : WeakEquivalence (ResolutionHomComplex.fromAugmentation a B) :=
    fromAugmentation_weak A B a hA hB ha
  unfold ResolutionHomBisimplicial.fromAugmentation
  infer_instance

/-- The actual coaugmentation map into the same genuine diagonal is weak. -/
theorem fromCoaugmentation_diagonal_weak (A : CosimplicialObject C) (B : SimplicialObject C) {Y : C}
    (b : (SimplicialObject.const C).obj Y ⟶ B)
    (hA : ∀ j, cofibrations C (ReedyStructure.latchingMap SimplexCategory.reedy A j))
    (hB : ∀ j, fibrations C (ReedyStructure.matchingMap SimplexCategory.reedyOp B j))
    (hb : ∀ j, weakEquivalences C (b.app j)) [IsFibrant Y] :
    WeakEquivalence (ResolutionHomBisimplicial.fromCoaugmentation A b) := by
  let _ : WeakEquivalence (ResolutionHomComplex.fromCoaugmentation A b) :=
    fromCoaugmentation_weak A B b hA hB hb
  unfold ResolutionHomBisimplicial.fromCoaugmentation
  infer_instance

private theorem weak_test_iff_of_square {K L K' L' : SSet.{v}}
    (f : K ⟶ L) (g : K' ⟶ L') (a : K ⟶ K') (b : L ⟶ L')
    [WeakEquivalence a] [WeakEquivalence b] (h : f ≫ b = a ≫ g) :
    WeakEquivalence f ↔ WeakEquivalence g := by
  constructor
  · intro hf
    let _ : WeakEquivalence f := hf
    let _ : WeakEquivalence (a ≫ g) := h ▸ (inferInstance : WeakEquivalence (f ≫ b))
    exact weakEquivalence_of_precomp a g
  · intro hg
    let _ : WeakEquivalence g := hg
    let _ : WeakEquivalence (f ≫ b) := h.symm ▸ (inferInstance : WeakEquivalence (a ≫ g))
    exact weakEquivalence_of_postcomp f b

end Generic

section Generated

variable {κ : Cardinal.{w}} [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
    (d : CofibrantGenerationData C κ)

open GeneratedFunctorialReplacements GeneratedFramings GeneratedFrameHomComplex

/-- The complete original right-to-two-sided comparison from the generated Q frame is weak. -/
theorem rightToTwoSided_weak (X Y : C) :
    WeakEquivalence (((rightToTwoSided d).app (op X)).app Y) := by
  let _ : IsCofibrant ((Q d).obj X) := Q_isCofibrant d X
  rw [rightToTwoSided_app]
  exact fromAugmentation_weak _ _ ((leftResolution d).app X)
    (leftFrame_latching_cofibration d X) (rightFrame_matching_fibration d Y)
    (leftResolution_weak d X)

/-- The complete original left-to-two-sided comparison from the generated R frame is weak. -/
theorem leftToTwoSided_weak (X Y : C) :
    WeakEquivalence (((leftToTwoSided d).app (op X)).app Y) := by
  let _ : IsFibrant ((R d).obj Y) := R_isFibrant d Y
  rw [leftToTwoSided_app]
  exact fromCoaugmentation_weak _ _ ((rightResolution d).app Y)
    (leftFrame_latching_cofibration d X) (rightFrame_matching_fibration d Y)
    (rightResolution_weak d Y)

/-- The actual source A maps from right Hom into the genuine same generated diagonal. -/
def rawRightComparison (A Z : C) :
    ResolutionHomComplex.right A ((rightFrame d).obj Z) ⟶
      SSet.simplicialDiagonalFunctor.obj
        (ResolutionHomBisimplicial.obj ((leftFrame d).obj A) ((rightFrame d).obj Z)) :=
  ResolutionHomBisimplicial.fromAugmentation ((augmentation d).app A) ((rightFrame d).obj Z)

/-- The actual target Z maps from left Hom into the same genuine generated diagonal. -/
def rawLeftComparison (A Z : C) :
    ResolutionHomComplex.left ((leftFrame d).obj A) Z ⟶
      SSet.simplicialDiagonalFunctor.obj
        (ResolutionHomBisimplicial.obj ((leftFrame d).obj A) ((rightFrame d).obj Z)) :=
  ResolutionHomBisimplicial.fromCoaugmentation ((leftFrame d).obj A) ((coaugmentation d).app Z)

/-- Every original right comparison simplex retains the augmentation and source A. -/
theorem rawRightComparison_app (A Z : C) (n : SimplexCategoryᵒᵖ)
    (f : A ⟶ ((rightFrame d).obj Z).obj n) :
    (rawRightComparison d A Z).app n f = ((augmentation d).app A).app n.unop ≫ f := rfl

/-- Every original left comparison simplex retains the coaugmentation and target Z. -/
theorem rawLeftComparison_app (A Z : C) (n : SimplexCategoryᵒᵖ)
    (f : ((leftFrame d).obj A).obj n.unop ⟶ Z) :
    (rawLeftComparison d A Z).app n f = f ≫ ((coaugmentation d).app Z).app n := rfl

/-- The actual cofibrant source gives a weak right-to-diagonal comparison. -/
theorem rawRightComparison_weak (A Z : C) [IsCofibrant A] :
    WeakEquivalence (rawRightComparison d A Z) :=
  fromAugmentation_diagonal_weak _ _ ((augmentation d).app A)
    (leftFrame_latching_cofibration d A) (rightFrame_matching_fibration d Z)
    (augmentation_weak d A)

/-- The actual fibrant target gives a weak left-to-diagonal comparison. -/
theorem rawLeftComparison_weak (A Z : C) [IsFibrant Z] :
    WeakEquivalence (rawLeftComparison d A Z) :=
  fromCoaugmentation_diagonal_weak _ _ ((coaugmentation d).app Z)
    (leftFrame_latching_cofibration d A) (rightFrame_matching_fibration d Z)
    (coaugmentation_weak d Z)

/-- Both whole original maps into the common genuine diagonal are weak at the original endpoints. -/
theorem rawComparisons_weak (A Z : C) [IsCofibrant A] [IsFibrant Z] :
    WeakEquivalence (rawRightComparison d A Z) ∧ WeakEquivalence (rawLeftComparison d A Z) :=
  ⟨rawRightComparison_weak d A Z, rawLeftComparison_weak d A Z⟩

/-- The actual right comparison retains every original source morphism and frame map. -/
theorem rawRightComparison_source_naturality {A A' : C} (f : A ⟶ A') (Z : C) :
    RightFrameHomBoundary.precomp f ((rightFrame d).obj Z) ≫ rawRightComparison d A Z =
      rawRightComparison d A' Z ≫ SSet.simplicialDiagonalFunctor.map
        (ResolutionHomBisimplicial.precomp ((leftFrame d).map f) ((rightFrame d).obj Z)) :=
  ResolutionHomBisimplicial.fromAugmentation_source_naturality
    ((augmentation d).app A) ((augmentation d).app A') ((leftFrame d).map f) f
    ((augmentation d).naturality f).symm ((rightFrame d).obj Z)

/-- The actual right comparison retains every original target morphism and frame map. -/
theorem rawRightComparison_target_naturality (A : C) {Z Z' : C} (f : Z ⟶ Z') :
    rawRightComparison d A Z ≫ SSet.simplicialDiagonalFunctor.map
        (ResolutionHomBisimplicial.postcomp ((leftFrame d).obj A) ((rightFrame d).map f)) =
      ResolutionHomComplex.postcomp ((CosimplicialObject.const C).obj A) ((rightFrame d).map f) ≫
        rawRightComparison d A Z' :=
  ResolutionHomBisimplicial.fromAugmentation_target_naturality ((augmentation d).app A)
    ((rightFrame d).map f)

/-- The actual left comparison retains every original source morphism and frame map. -/
theorem rawLeftComparison_source_naturality {A A' : C} (f : A ⟶ A') (Z : C) :
    ResolutionHomComplex.precomp ((leftFrame d).map f) ((SimplicialObject.const C).obj Z) ≫
        rawLeftComparison d A Z =
      rawLeftComparison d A' Z ≫ SSet.simplicialDiagonalFunctor.map
        (ResolutionHomBisimplicial.precomp ((leftFrame d).map f) ((rightFrame d).obj Z)) :=
  ResolutionHomBisimplicial.fromCoaugmentation_source_naturality ((leftFrame d).map f)
    ((coaugmentation d).app Z)

/-- The actual left comparison retains every original target morphism and frame map. -/
theorem rawLeftComparison_target_naturality (A : C) {Z Z' : C} (f : Z ⟶ Z') :
    ResolutionHomComplex.postcomp ((leftFrame d).obj A) ((SimplicialObject.const C).map f) ≫
        rawLeftComparison d A Z' =
      rawLeftComparison d A Z ≫ SSet.simplicialDiagonalFunctor.map
        (ResolutionHomBisimplicial.postcomp ((leftFrame d).obj A) ((rightFrame d).map f)) :=
  ResolutionHomBisimplicial.fromCoaugmentation_target_naturality ((leftFrame d).obj A)
    ((coaugmentation d).app Z) ((coaugmentation d).app Z') f ((rightFrame d).map f)
    ((coaugmentation d).naturality f)

/-- The original Q counit precedes the unchanged canonical right-to-two-sided map. -/
theorem rawRightComparison_counit (A Z : C) :
    RightFrameHomBoundary.precomp ((counit d).app A) ((rightFrame d).obj Z) ≫
        ((rightToTwoSided d).app (op A)).app Z =
      rawRightComparison d A Z ≫
        (ResolutionHomBisimplicial.diagonalIso ((leftFrame d).obj A) ((rightFrame d).obj Z)).hom := by
  ext n f
  change A ⟶ ((rightFrame d).obj Z).obj n at f
  change ((leftResolution d).app A).app n.unop ≫ ((counit d).app A ≫ f) =
    ((augmentation d).app A).app n.unop ≫ f
  rw [augmentation_app, Category.assoc]

/-- The original R unit precedes the unchanged canonical left-to-two-sided map. -/
theorem rawLeftComparison_unit (A Z : C) :
    ResolutionHomComplex.postcomp ((leftFrame d).obj A) ((SimplicialObject.const C).map ((unit d).app Z)) ≫
        ((leftToTwoSided d).app (op A)).app Z =
      rawLeftComparison d A Z ≫
        (ResolutionHomBisimplicial.diagonalIso ((leftFrame d).obj A) ((rightFrame d).obj Z)).hom := by
  ext n f
  change ((leftFrame d).obj A).obj n.unop ⟶ Z at f
  change (f ≫ (unit d).app Z) ≫ ((rightResolution d).app Z).app n =
    f ≫ ((coaugmentation d).app Z).app n
  rw [coaugmentation_app, Category.assoc]

/-- Both canonical original source-map tests agree by their whole comparison squares. -/
theorem left_precomp_weak_iff_right {X X' : C} (f : X ⟶ X') (Y : C) :
    WeakEquivalence (((leftBifunctor d).map f.op).app Y) ↔
      WeakEquivalence (((rightBifunctor d).map f.op).app Y) := by
  let _ : WeakEquivalence (((leftToTwoSided d).app (op X')).app Y) := leftToTwoSided_weak d X' Y
  let _ : WeakEquivalence (((leftToTwoSided d).app (op X)).app Y) := leftToTwoSided_weak d X Y
  let _ : WeakEquivalence (((rightToTwoSided d).app (op X')).app Y) := rightToTwoSided_weak d X' Y
  let _ : WeakEquivalence (((rightToTwoSided d).app (op X)).app Y) := rightToTwoSided_weak d X Y
  have hl := weak_test_iff_of_square _ _ _ _ (leftToTwoSided_source_naturality d f Y)
  have hr := weak_test_iff_of_square _ _ _ _ (rightToTwoSided_source_naturality d f Y)
  exact hl.trans hr.symm

/-- The actual original fibrant target unit is weak on the complete left-frame Hom. -/
theorem leftFrame_targetUnit_weak (X Z : C) [IsFibrant Z] :
    WeakEquivalence
      (ResolutionHomComplex.postcomp ((leftFrame d).obj X)
        ((SimplicialObject.const C).map ((unit d).app Z))) := by
  let _ : IsFibrant ((𝟭 C).obj Z) := (inferInstance : IsFibrant Z)
  let _ : IsFibrant ((R d).obj Z) := R_isFibrant d Z
  let _ : WeakEquivalence ((unit d).app Z) := (weakEquivalence_iff _).mpr (unit_weak d Z)
  exact LeftFrameHomWeakEquivalence.postcomp_weak ((leftFrame d).obj X)
    (leftFrame_latching_cofibration d X) ((unit d).app Z)

/-- The original raw left-frame source test agrees with the complete generated right source test. -/
theorem leftFrame_precomp_weak_iff_right {X X' : C} (f : X ⟶ X') (Z : C) [IsFibrant Z] :
    WeakEquivalence
      (ResolutionHomComplex.precomp ((leftFrame d).map f) ((SimplicialObject.const C).obj Z)) ↔
      WeakEquivalence (((rightBifunctor d).map f.op).app Z) := by
  let _ : WeakEquivalence
      (ResolutionHomComplex.postcomp ((leftFrame d).obj X')
        ((SimplicialObject.const C).map ((unit d).app Z))) := leftFrame_targetUnit_weak d X' Z
  let _ : WeakEquivalence
      (ResolutionHomComplex.postcomp ((leftFrame d).obj X)
        ((SimplicialObject.const C).map ((unit d).app Z))) := leftFrame_targetUnit_weak d X Z
  have h := weak_test_iff_of_square _ _ _ _
    (ResolutionHomComplex.precomp_postcomp ((leftFrame d).map f)
      ((SimplicialObject.const C).map ((unit d).app Z)))
  exact h.trans (left_precomp_weak_iff_right d f Z)

/-- The left-frame test is exactly the original whole derived right-Hom test used by localization. -/
theorem leftFrame_precomp_weak_iff_generatedRight_isIso {X X' : C}
    (f : X ⟶ X') (Z : C) [IsFibrant Z] :
    WeakEquivalence
      (ResolutionHomComplex.precomp ((leftFrame d).map f) ((SimplicialObject.const C).obj Z)) ↔
      IsIso (GeneratedRightMappingEnrichment.precomp d f Z) := by
  let _ : HomotopyMappingSpaceCategory.localize.{v}.IsLocalization (weakEquivalences SSet.{v}) := by
    change HomotopyMappingSpaceCategory.localize.{v}.IsLocalization SSet.realizationWeakEquivalences
    infer_instance
  change WeakEquivalence
      (ResolutionHomComplex.precomp ((leftFrame d).map f) ((SimplicialObject.const C).obj Z)) ↔
    IsIso (HomotopyMappingSpaceCategory.localize.map (((rightBifunctor d).map f.op).app Z))
  exact (leftFrame_precomp_weak_iff_right d f Z).trans
    ((weakEquivalence_iff _).trans
      (weakEquivalence_iff_isIso_map_of_isLocalization HomotopyMappingSpaceCategory.localize _))

end Generated

end HomotopicalAlgebra.GeneratedFrameHomComparison

end

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.ModelCategory.CellularLocalEquivalenceClosure
import MathlibExt.AlgebraicTopology.ModelCategory.LeftBousfieldLocalization.OriginalRelativeMapping
import Mathlib.AlgebraicTopology.SimplicialSet.StdSimplex
import MathlibExt.AlgebraicTopology.ModelCategory.CosimplicialHomCornerLifting

/-!
# Cellular recognition of local fibrancy

For cofibrant generation data `d` and a family of arrows `S`, the labelled
attaching class consists of local trivial cofibrations, and its right lifting
property against a terminal map implies `generatedLocalFibrant d S`.
In a left proper model category, `original_terminal_lifting` applies to local
trivial cofibrations with arbitrary source and target, giving the terminal-map
characterization of local fibrancy.
Given `CellularSource d` and the stated smallness of the indexing family,
`hornObjectFunctor` produces local fibrant objects; under left properness its
unit is a local trivial cofibration and it recognizes local equivalences as
weak equivalences between the resulting objects.
-/

set_option autoImplicit false

noncomputable section

universe w wS u v vJ

open CategoryTheory Limits MorphismProperty Opposite
open scoped Simplicial SSet.modelCategoryQuillen

namespace HomotopicalAlgebra.CellularLocalizationRecognition

open CellularLocalizationFactorizations CellularLocalEquivalenceClosure
open CellularLocalizingFamilies QuillenFrameHomComplex GeneratedFramings
open GeneratedFunctorialReplacements

/-- An actual trivial simplicial fibration is surjective on its original zero simplices. -/
theorem trivialFibration_surjective_zero {E B : SSet.{v}} (p : E ⟶ B)
    (hp : trivialFibrations SSet.{v} p) : Function.Surjective (p.app (op ⦋0⦌)) := by
  intro x
  let a : (Δ[0] : SSet.{v}) ⟶ B := SSet.yonedaEquiv.symm x
  let _ : Cofibration (initial.to (Δ[0] : SSet.{v})) :=
    (SSet.modelCategoryQuillen.cofibration_iff _).mpr inferInstance
  let _ : HasLiftingProperty (initial.to (Δ[0] : SSet.{v})) p :=
    hasLiftingProperty_of_wfs _ _ (mem_cofibrations _) hp
  let sq : CommSq (initial.to E) (initial.to (Δ[0] : SSet.{v})) p a :=
    ⟨initial.hom_ext _ _⟩
  refine ⟨SSet.yonedaEquiv sq.lift, ?_⟩
  apply SSet.yonedaEquiv.symm.injective
  rw [← SSet.yonedaEquiv_symm_comp, Equiv.symm_apply_apply, sq.fac_right]

section OriginalLeftHomLimits

variable {C : Type u} [Category.{v} C]

/-- The fixed original cosimplicial source gives its exact covariant left-Hom target functor. -/
def rawLeftFunctor (A : CosimplicialObject C) : C ⥤ SSet.{v} :=
  SimplicialObject.const C ⋙ ResolutionHomComplex.bifunctor.obj (op A)

/-- Every original target map remains the same full postcomposition by its actual constant simplicial map. -/
theorem rawLeftFunctor_map (A : CosimplicialObject C) {X Y : C} (f : X ⟶ Y) :
    (rawLeftFunctor A).map f = ResolutionHomComplex.postcomp A ((SimplicialObject.const C).map f) := rfl

/-- Every original cosimplicial source map gives the actual left-Hom natural transformation. -/
def rawLeftPrecomp {A B : CosimplicialObject C} (h : A ⟶ B) :
    rawLeftFunctor B ⟶ rawLeftFunctor A :=
  Functor.whiskerLeft (SimplicialObject.const C) (ResolutionHomComplex.bifunctor.map h.op)

/-- All components of the whole original source transformation retain the same raw left-Hom map. -/
theorem rawLeftPrecomp_app {A B : CosimplicialObject C} (h : A ⟶ B) (X : C) :
    (rawLeftPrecomp h).app X = ResolutionHomComplex.precomp h ((SimplicialObject.const C).obj X) := rfl

/-- The original left coefficient Hom retains every caller's actual limit cone and its full universal property. -/
def rawLeftImageConeIsLimit {J : Type w} [Category.{vJ} J] {F : J ⥤ C}
    (A : CosimplicialObject C) (c : Cone F) (hc : IsLimit c) :
    IsLimit ((rawLeftFunctor A).mapCone c) := by
  apply evaluationJointlyReflectsLimits
  intro n
  change IsLimit ((coyoneda.obj (op (A.obj n.unop))).mapCone c)
  exact isLimitOfPreserves (coyoneda.obj (op (A.obj n.unop))) hc

/-- Every actual original shape is preserved by fixed-left Hom without global source completeness assumptions. -/
theorem rawLeftPreservesLimitsOfShape (J : Type w) [Category.{vJ} J] (A : CosimplicialObject C) :
    PreservesLimitsOfShape J (rawLeftFunctor A) where
  preservesLimit {F} := { preserves := fun hc => ⟨rawLeftImageConeIsLimit (F := F) A _ hc⟩ }

/-- The relative left-Hom corner keeps the original target projection and source map. -/
def rawLeftCorner {A B : CosimplicialObject C} (h : A ⟶ B) {X Y : C} (p : X ⟶ Y) :
    (rawLeftFunctor B).obj X ⟶
      pullback ((rawLeftFunctor A).map p) ((rawLeftPrecomp h).app Y) :=
  pullback.lift ((rawLeftPrecomp h).app X) ((rawLeftFunctor B).map p)
    ((rawLeftPrecomp h).naturality p).symm

section Matching

variable [HasFiniteLimits C]
  {A B : CosimplicialObject C} (h : A ⟶ B) (R : SimplicialObject C) (j : SimplexCategoryᵒᵖ)

/-- The entire original coefficient diagram gives the same precomposition transformation. -/
def rawLeftMatchingNat : R ⋙ rawLeftFunctor B ⟶ R ⋙ rawLeftFunctor A :=
  Functor.whiskerLeft R (rawLeftPrecomp h)

/-- Each original matching cone retains the exact caller cone after fixed-left Hom. -/
abbrev rawLeftMatchingCone (T : CosimplicialObject C) :
    Cone (SimplexCategory.reedyOp.matchingDiagram (R ⋙ rawLeftFunctor T) j) :=
  ReedyStructure.PostcomposeCorners.matchingCone SimplexCategory.reedyOp (rawLeftFunctor T) j R

/-- The full original matching limit universal property is preserved at the same coefficient object. -/
def rawLeftMatchingIsLimit (T : CosimplicialObject C) : IsLimit (rawLeftMatchingCone R j T) := by
  let _ : PreservesLimitsOfShape (SimplexCategory.reedyOp.Matching j) (rawLeftFunctor T) :=
    rawLeftPreservesLimitsOfShape _ T
  exact ReedyStructure.PostcomposeCorners.matchingIsLimit SimplexCategory.reedyOp (rawLeftFunctor T) j R

/-- The actual original matching comparison remains precomposition at the full original matching object. -/
theorem rawLeftMatchingComparison_eq :
    SimplexCategory.reedyOp.matchingComparisonWith (rawLeftMatchingNat h R) j
      (rawLeftMatchingCone R j B) (rawLeftMatchingCone R j A) (rawLeftMatchingIsLimit R j A) =
        (rawLeftPrecomp h).app (limit (SimplexCategory.reedyOp.matchingDiagram R j)) := by
  apply (rawLeftMatchingIsLimit R j A).hom_ext
  intro a
  rw [SimplexCategory.reedyOp.matchingComparisonWith_π]
  change (rawLeftFunctor B).map (limit.π (SimplexCategory.reedyOp.matchingDiagram R j) a) ≫
      (rawLeftPrecomp h).app (R.obj (SimplexCategory.reedyOp.matchingTarget a)) =
    (rawLeftPrecomp h).app (limit (SimplexCategory.reedyOp.matchingDiagram R j)) ≫
      (rawLeftFunctor A).map (limit.π (SimplexCategory.reedyOp.matchingDiagram R j) a)
  exact (rawLeftPrecomp h).naturality _

/-- Every original complete matching map remains the exact original target postcomposition. -/
theorem rawLeftMatchingMap_eq (T : CosimplicialObject C) :
    SimplexCategory.reedyOp.matchingMapWith (R ⋙ rawLeftFunctor T) j
      (rawLeftMatchingCone R j T) (rawLeftMatchingIsLimit R j T) =
        (rawLeftFunctor T).map (ReedyStructure.matchingMap SimplexCategory.reedyOp R j) := by
  let _ : PreservesLimitsOfShape (SimplexCategory.reedyOp.Matching j) (rawLeftFunctor T) :=
    rawLeftPreservesLimitsOfShape _ T
  exact ReedyStructure.PostcomposeCorners.matchingMapWith_eq SimplexCategory.reedyOp (rawLeftFunctor T) j R

/-- The complete caller pullback uses the original Hom(A,Rj) and Hom(B,matching R) factors. -/
def rawLeftMatchingPullback :
    PullbackCone
      (SimplexCategory.reedyOp.matchingComparisonWith (rawLeftMatchingNat h R) j
        (rawLeftMatchingCone R j B) (rawLeftMatchingCone R j A) (rawLeftMatchingIsLimit R j A))
      (SimplexCategory.reedyOp.matchingMapWith (R ⋙ rawLeftFunctor A) j
        (rawLeftMatchingCone R j A) (rawLeftMatchingIsLimit R j A)) :=
  PullbackCone.mk
    (pullback.snd
      ((rawLeftFunctor A).map (ReedyStructure.matchingMap SimplexCategory.reedyOp R j))
      ((rawLeftPrecomp h).app (limit (SimplexCategory.reedyOp.matchingDiagram R j))))
    (pullback.fst
      ((rawLeftFunctor A).map (ReedyStructure.matchingMap SimplexCategory.reedyOp R j))
      ((rawLeftPrecomp h).app (limit (SimplexCategory.reedyOp.matchingDiagram R j)))) (by
        rw [rawLeftMatchingComparison_eq, rawLeftMatchingMap_eq]
        exact pullback.condition.symm)

/-- The literal swapped original projections retain the complete caller pullback universal property. -/
def rawLeftMatchingPullbackIsLimit : IsLimit (rawLeftMatchingPullback h R j) := by
  apply ReedyStructure.PostcomposeCorners.pullbackMkIsLimitOfEq
    (rawLeftMatchingComparison_eq h R j) (rawLeftMatchingMap_eq R j A)
  exact PullbackCone.flipIsLimit (pullback.isLimit _ _)

/-- The original caller matching corner of the coefficient Hom transformation. -/
def rawLeftMatchingCallerCorner :
    (rawLeftFunctor B).obj (R.obj j) ⟶
      pullback ((rawLeftFunctor A).map (ReedyStructure.matchingMap SimplexCategory.reedyOp R j))
        ((rawLeftPrecomp h).app (limit (SimplexCategory.reedyOp.matchingDiagram R j))) :=
  SimplexCategory.reedyOp.matchingCornerWith (rawLeftMatchingNat h R) j
    (rawLeftMatchingCone R j B) (rawLeftMatchingIsLimit R j B)
    (rawLeftMatchingCone R j A) (rawLeftMatchingIsLimit R j A)
    (rawLeftMatchingPullback h R j) (rawLeftMatchingPullbackIsLimit h R j)

/-- Both original matching-corner projections recover the same relative left-Hom map. -/
theorem rawLeftMatchingCallerCorner_eq :
    rawLeftMatchingCallerCorner h R j =
      rawLeftCorner h (ReedyStructure.matchingMap SimplexCategory.reedyOp R j) := by
  apply pullback.hom_ext
  · change rawLeftMatchingCallerCorner h R j ≫ (rawLeftMatchingPullback h R j).snd = _
    exact (SimplexCategory.reedyOp.matchingCornerWith_snd (rawLeftMatchingNat h R) j
      (rawLeftMatchingCone R j B) (rawLeftMatchingIsLimit R j B)
      (rawLeftMatchingCone R j A) (rawLeftMatchingIsLimit R j A)
      (rawLeftMatchingPullback h R j) (rawLeftMatchingPullbackIsLimit h R j)).trans
        (pullback.lift_fst _ _ _).symm
  · change rawLeftMatchingCallerCorner h R j ≫ (rawLeftMatchingPullback h R j).fst = _
    exact (SimplexCategory.reedyOp.matchingCornerWith_fst (rawLeftMatchingNat h R) j
      (rawLeftMatchingCone R j B) (rawLeftMatchingIsLimit R j B)
      (rawLeftMatchingCone R j A) (rawLeftMatchingIsLimit R j A)
      (rawLeftMatchingPullback h R j) (rawLeftMatchingPullbackIsLimit h R j)).trans
        ((rawLeftMatchingMap_eq R j B).trans (pullback.lift_snd _ _ _).symm)

/-- The full canonical matching corner is the same original relative map up to its actual caller Arrow iso. -/
def rawLeftMatchingCornerArrowIso :
    CategoryTheory.Arrow.mk
        (ReedyStructure.matchingCorner SimplexCategory.reedyOp (rawLeftMatchingNat h R) j) ≅
      CategoryTheory.Arrow.mk
        (rawLeftCorner h (ReedyStructure.matchingMap SimplexCategory.reedyOp R j)) :=
  (ReedyStructure.matchingCornerWithArrowIso SimplexCategory.reedyOp (rawLeftMatchingNat h R) j
    (rawLeftMatchingCone R j B) (rawLeftMatchingIsLimit R j B)
    (rawLeftMatchingCone R j A) (rawLeftMatchingIsLimit R j A)
    (rawLeftMatchingPullback h R j) (rawLeftMatchingPullbackIsLimit h R j)).symm ≪≫
      eqToIso (congrArg (fun f => CategoryTheory.Arrow.mk f) (rawLeftMatchingCallerCorner_eq h R j))

end Matching

section Terminal

variable [HasTerminal C] {A B : CosimplicialObject C}

/-- The original source map acts isomorphically on left Hom into the actual terminal coefficient. -/
def rawLeftTerminalPrecompIso (h : A ⟶ B) :
    (rawLeftFunctor B).obj (⊤_ C) ≅ (rawLeftFunctor A).obj (⊤_ C) where
  hom := (rawLeftPrecomp h).app (⊤_ C)
  inv :=
    { app n := ↾fun _ => terminal.from (B.obj n.unop)
      naturality := by
        intro n m a
        ext f
        apply terminal.hom_ext }
  hom_inv_id := by
    ext n f
    apply terminal.hom_ext
  inv_hom_id := by
    ext n f
    apply terminal.hom_ext

end Terminal

end OriginalLeftHomLimits

section OriginalRightHomLifting

variable {C : Type u} [Category.{v} C] [HasFiniteLimits C]

/-- Full original coefficient-matching lifts give every actual right-Hom boundary lift. -/
theorem rawRightBoundary_hasLift {A B : C} (i : A ⟶ B) (R : SimplicialObject C)
    (hR : ∀ j, HasLiftingProperty i (ReedyStructure.matchingMap SimplexCategory.reedyOp R j))
    (n : ℕ) (a : (SSet.boundary.{v} n : SSet.{v}) ⟶ ResolutionHomComplex.right B R)
    (b : (SSet.stdSimplex.obj ⦋n⦌ : SSet.{v}) ⟶ ResolutionHomComplex.right A R)
    (sq : CommSq a (SSet.boundary.{v} n).ι (rightPrecomp i R) b) : sq.HasLift := by
  let _ : HasLiftingProperty i (ReedyStructure.matchingMap SimplexCategory.reedyOp R (op ⦋n⦌)) := hR _
  let _ := PartialFaceMatching.fromFull_isIso R n
  let _ : HasLiftingProperty i (PartialFaceMatching.map R n Finset.univ) := by
    rw [← PartialFaceMatching.matchingMap_fromFull]
    infer_instance
  let t : A ⟶ R.obj (op ⦋n⦌) := SSet.yonedaEquiv b
  let c : CommSq t i (PartialFaceMatching.map R n Finset.univ)
      (RightFrameHomBoundary.boundaryHomMap B R n a) :=
    RightFrameHomBoundary.coefficientBoundarySquareOfPrecomp i R n a b sq
  let _ : c.HasLift := inferInstance
  refine CommSq.HasLift.mk'
    { l := RightFrameHornGeometry.homSimplex B R n c.lift
      fac_left := RightFrameHomBoundary.homSimplex_boundary_extension B R n a c.lift c.fac_right
      fac_right := ?_ }
  apply SSet.yonedaEquiv.injective
  rw [SSet.yonedaEquiv_comp, RightFrameHornGeometry.homSimplex]
  exact (congrArg (fun f : (ResolutionHomComplex.right B R).obj (op ⦋n⦌) =>
    (rightPrecomp i R).app (op ⦋n⦌) f)
      (SSet.yonedaEquiv.apply_symm_apply c.lift)).trans c.fac_left

/-- Actual lifting against every original matching map derives full right-Hom trivial fibrancy. -/
theorem rawRightPrecomp_trivialFibration_of_matching_lifting {A B : C} (i : A ⟶ B)
    (R : SimplicialObject C)
    (hR : ∀ j, HasLiftingProperty i (ReedyStructure.matchingMap SimplexCategory.reedyOp R j)) :
    trivialFibrations SSet.{v} (rightPrecomp i R) := by
  rw [← cofibrations_rlp SSet.{v}, SSet.modelCategoryQuillen.cofibrations_eq, SSet.rlp_monomorphisms]
  intro K L j hj
  obtain ⟨n⟩ := hj
  exact { sq_hasLift := fun sq => rawRightBoundary_hasLift i R hR n _ _ sq }

end OriginalRightHomLifting

section OriginalFrames

variable {C : Type u} [Category.{v} C] [ModelCategory C]
  {κ : Cardinal.{w}} [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
  (d : CofibrantGenerationData C κ)

/-- The source-constructed original resolution gives fibrations at all actual right-frame Hom matching corners. -/
theorem resolutionMatchingCorner_fibration (p : CategoryTheory.Arrow C) (Z : C)
    (j : SimplexCategoryᵒᵖ) :
    fibrations SSet.{v}
      (ReedyStructure.matchingCorner SimplexCategory.reedyOp
        (rawLeftMatchingNat (cosimplicialFactor d p).i ((rightFrame d).obj Z)) j) := by
  let R := (rightFrame d).obj Z
  let m := ReedyStructure.matchingMap SimplexCategory.reedyOp R j
  let _ : Fibration m := (fibration_iff _).mpr (rightFrame_matching_fibration d Z j)
  have hc : Fibration (CosimplicialHomCorner.map (cosimplicialFactor d p).i m) :=
    CosimplicialHomCorner.map_fibration_of_augmentations
      d.cofibrantFactorizationData d.fibrantFactorizationData (cosimplicialFactor d p).i
      (leftFrame_latching_cofibration d p.left) (cosimplicialFactor d p).hi
      ((Q d).obj p.left) ((Q d).obj p.right) (sourceResolution d p) (targetResolution d p)
      (sourceResolution_weak d p) (targetResolution_weak d p) m
  apply ((fibrations SSet.{v}).arrow_mk_iso_iff
    (rawLeftMatchingCornerArrowIso (cosimplicialFactor d p).i R j)).mpr
  exact (fibration_iff _).mp hc

/-- Original locality makes every complete right-frame Hom matching corner a genuine trivial fibration. -/
theorem resolutionMatchingCorner_local_trivial {K : Type wS} (S : K → CategoryTheory.Arrow C)
    (k : K) (Z : C) (hZ : generatedLocalFibrant d S Z) (j : SimplexCategoryᵒᵖ) :
    trivialFibrations SSet.{v}
      (ReedyStructure.matchingCorner SimplexCategory.reedyOp
        (rawLeftMatchingNat (cosimplicialFactor d (S k)).i ((rightFrame d).obj Z)) j) := by
  apply ReedyModel.matchingCorner_trivialFibration_of_fibration_weak
  · exact resolutionMatchingCorner_fibration d (S k) Z
  · intro a
    exact (weakEquivalence_iff _).mp (resolutionPrecomp_frameCoefficient_local_weak d S k Z hZ a)

/-- Every original local target gives all original coefficient-matching lifts for the actual latching arrow. -/
theorem latchingArrow_matching_lifting {K : Type wS} (S : K → CategoryTheory.Arrow C)
    (k : K) (n : ℕ) (Z : C) (hZ : generatedLocalFibrant d S Z) (j : SimplexCategoryᵒᵖ) :
    HasLiftingProperty (latchingArrow d (S k) n).hom
      (ReedyStructure.matchingMap SimplexCategory.reedyOp ((rightFrame d).obj Z) j) := by
  let R := (rightFrame d).obj Z
  let m := ReedyStructure.matchingMap SimplexCategory.reedyOp R j
  have ht : trivialFibrations SSet.{v} (CosimplicialHomCorner.map (cosimplicialFactor d (S k)).i m) :=
    ((trivialFibrations SSet.{v}).arrow_mk_iso_iff
      (rawLeftMatchingCornerArrowIso (cosimplicialFactor d (S k)).i R j)).mp
      (resolutionMatchingCorner_local_trivial d S k Z hZ j)
  let _ : Cofibration (SSet.boundary.{v} n).ι :=
    (SSet.modelCategoryQuillen.cofibration_iff _).mpr inferInstance
  let _ : HasLiftingProperty (SSet.boundary.{v} n).ι
      (CosimplicialHomCorner.map (cosimplicialFactor d (S k)).i m) :=
    hasLiftingProperty_of_wfs _ _ (mem_cofibrations _) ht
  exact (CosimplicialHomCorner.boundary_lifting_iff (cosimplicialFactor d (S k)).i m ⦋n⦌).mp inferInstance

/-- The actual original latching arrow is weak for the full original derived S-local class. -/
theorem latchingArrow_local {K : Type wS} (S : K → CategoryTheory.Arrow C) (k : K) (n : ℕ) :
    generatedLocalEquivalences d S (latchingArrow d (S k) n).hom := by
  intro Z hZ
  let _ : IsCofibrant (latchingArrow d (S k) n).left := latchingArrow_source_cofibrant d (S k) n
  let _ : IsCofibrant (latchingArrow d (S k) n).right := latchingArrow_target_cofibrant d (S k) n
  let _ : Cofibration (latchingArrow d (S k) n).hom :=
    (cofibration_iff _).mpr (latchingArrow_cofibration d (S k) n)
  exact (generatedPrecomp_iff_raw_trivialFibration d (latchingArrow d (S k) n).hom Z).mpr
    (rawRightPrecomp_trivialFibration_of_matching_lifting _ _ (latchingArrow_matching_lifting d S k n Z hZ))

/-- Every same-source original J factor and actual original S horn factor is local-weak for the original class. -/
theorem attachingFamily_local {K : Type wS} (S : K → CategoryTheory.Arrow C)
    (a : d.J.toSet ⊕ (K × ℕ)) : generatedLocalEquivalences d S (attachingFamily d S a).hom := by
  cases a with
  | inl j =>
    exact baseWeak_le d S _ (originalCellFactor_J_trivialCofibration d j).2
  | inr a =>
    let p := latchingArrow d (S a.1) a.2
    let _ : (generatedLocalEquivalences d S).HasTwoOutOfThreeProperty := weak_twoOutOfThree d S
    apply (generatedLocalEquivalences d S).of_postcomp _ _
      (baseWeak_le d S _ (originalCellProjection_trivialFibration d p).2)
    change generatedLocalEquivalences d S
      ((GeneratedArrowFactorizations.cofibrant d).i.app p ≫
        (GeneratedArrowFactorizations.cofibrant d).p.app p)
    rw [(GeneratedArrowFactorizations.cofibrant d).fac_app]
    exact latchingArrow_local d S a.1 a.2

/-- The complete actual labelled attaching property lies in the entire original local trivial cofibration class. -/
theorem attachingClass_le_localTrivialCofibrations {K : Type wS} (S : K → CategoryTheory.Arrow C) :
    attachingClass d S ≤ localTrivialCofibrations d S := by
  intro X Y f hf
  rcases hf with ⟨a⟩
  exact ⟨attachingFamily_cofibration d S a, attachingFamily_local d S a⟩

/-- The exact original augmented attaching injectivity implies base fibrancy
and every original derived-S locality test. -/
theorem attachingRLP_localFibrant {K : Type wS} (S : K → CategoryTheory.Arrow C) (Z : C)
    (hZ : (attachingClass d S).rlp (terminal.from Z)) : generatedLocalFibrant d S Z := by
  let _ : Fibration (terminal.from Z) := (fibration_iff _).mpr (attachingRLP_le_fibrations d S _ hZ)
  let _ : IsFibrant Z := inferInstance
  refine ⟨inferInstance, ?_⟩
  intro k
  let a := (cosimplicialFactor d (S k)).i
  let p := terminal.from Z
  have ht : trivialFibrations SSet.{v} (CosimplicialHomCorner.map a p) := by
    rw [← cofibrations_rlp SSet.{v}, SSet.modelCategoryQuillen.cofibrations_eq, SSet.rlp_monomorphisms]
    intro K L j hj
    obtain ⟨n⟩ := hj
    apply (CosimplicialHomCorner.boundary_lifting_iff a p ⦋n⦌).mpr
    let q := latchingArrow d (S k) n
    let _ : HasLiftingProperty ((originalCellFactor d).obj q).hom p := by
      apply hZ
      change ofHoms (fun b : d.J.toSet ⊕ (K × ℕ) => (attachingFamily d S b).hom)
        (attachingFamily d S (Sum.inr (k, n))).hom
      exact ofHoms.mk (Sum.inr (k, n))
    exact (originalCellFactorRetract d q (latchingArrow_cofibration d (S k) n)).leftLiftingProperty p
  let _ : IsIso (CosimplicialHomCorner.precomp a (⊤_ C)) :=
    (rawLeftTerminalPrecompIso a).isIso_hom
  let e := pullback.fst (CosimplicialHomCorner.postcomp _ p) (CosimplicialHomCorner.precomp a (⊤_ C))
  let _ : IsIso e := inferInstance
  have hw : weakEquivalences SSet.{v} (CosimplicialHomCorner.precomp a Z) := by
    have he : weakEquivalences SSet.{v} (CosimplicialHomCorner.map a p ≫ e) :=
      (weakEquivalences SSet.{v}).comp_mem _ _ ht.2 ((weakEquivalences SSet.{v}).of_isIso e)
    change weakEquivalences SSet.{v}
      (CosimplicialHomCorner.map a p ≫ pullback.fst _ _) at he
    rw [CosimplicialHomCorner.map_fst] at he
    exact he
  exact (resolutionPrecomp_weak_iff d (S k) Z).mp ((weakEquivalence_iff _).mpr hw)

/-- The original R unit and actual frame-zero isomorphism give a strict retraction onto a fibrant target. -/
def frameZeroRetract (Z : C) [IsFibrant Z] :
    Retract Z (((rightFrame d).obj Z).obj (op ⦋0⦌)) := by
  let u : Z ⟶ (((rightFrame d).obj Z).obj (op ⦋0⦌)) :=
    ((coaugmentation d).app Z).app (op ⦋0⦌)
  have hu : trivialCofibrations C u := by
    dsimp only [u]
    rw [coaugmentation_zero]
    exact (trivialCofibrations C).comp_mem _ _ (unit_trivialCofibration d Z)
      ((trivialCofibrations C).of_isIso _)
  let _ : HasLiftingProperty u (terminal.from Z) :=
    hasLiftingProperty_of_wfs _ _ hu (mem_fibrations _)
  let sq : CommSq (𝟙 Z) u (terminal.from Z)
      (terminal.from (((rightFrame d).obj Z).obj (op ⦋0⦌))) :=
    ⟨terminal.hom_ext _ _⟩
  exact { i := u, r := sq.lift, retract := sq.fac_left }

/-- The chosen actual frame-zero retraction is the right map of the original unit's constructed retract. -/
def frameZeroRetraction (Z : C) [IsFibrant Z] :
    (((rightFrame d).obj Z).obj (op ⦋0⦌)) ⟶ Z := (frameZeroRetract d Z).r

/-- The same original coaugmentation composes with the chosen actual retraction to the identity. -/
theorem frameZeroRetraction_fac (Z : C) [IsFibrant Z] :
    ((coaugmentation d).app Z).app (op ⦋0⦌) ≫ frameZeroRetraction d Z = 𝟙 Z := by
  exact (frameZeroRetract d Z).retract

/-- Actual original right-Hom trivial fibrancy supplies every strict original terminal lift. -/
theorem terminal_lifting_of_rawPrecomp {A B : C} (i : A ⟶ B) (Z : C) [IsFibrant Z]
    (hi : trivialFibrations SSet.{v} (rightPrecomp i ((rightFrame d).obj Z))) :
    HasLiftingProperty i (terminal.from Z) where
  sq_hasLift {a b} _ := by
    let u : Z ⟶ (((rightFrame d).obj Z).obj (op ⦋0⦌)) :=
      ((coaugmentation d).app Z).app (op ⦋0⦌)
    obtain ⟨g, hg⟩ := trivialFibration_surjective_zero _ hi (a ≫ u)
    change B ⟶ (((rightFrame d).obj Z).obj (op ⦋0⦌)) at g
    change i ≫ g = a ≫ u at hg
    exact CommSq.HasLift.mk'
      { l := g ≫ frameZeroRetraction d Z
        fac_left := by
          rw [← Category.assoc, hg, Category.assoc, frameZeroRetraction_fac,
            Category.comp_id]
        fac_right := terminal.hom_ext _ _ }

/-- Original local trivial cofibrations with cofibrant endpoints have strict lifts to each original local target. -/
theorem cofibrant_terminal_lifting {K : Type wS} (S : K → Arrow C)
    {A B : C} [IsCofibrant A] [IsCofibrant B] (i : A ⟶ B)
    (hi : localTrivialCofibrations d S i) (Z : C) (hZ : generatedLocalFibrant d S Z) :
    HasLiftingProperty i (terminal.from Z) := by
  let _ : IsFibrant Z := hZ.1
  exact terminal_lifting_of_rawPrecomp d i Z (rawPrecomp_trivial_of_local d S i hi Z hZ)

end OriginalFrames

section ArbitraryOriginalEndpoints

variable {C : Type u} [Category.{v} C] [ModelCategory C] [IsLeftProper C]
  {κ : Cardinal.{w}} [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
  (d : CofibrantGenerationData C κ) {K : Type wS} (S : K → Arrow C)

/-- The actual original Q/I factor and pushout transfer retain every arbitrary original endpoint. -/
theorem original_terminal_lifting {A B : C} (i : A ⟶ B)
    (hi : localTrivialCofibrations d S i) (Z : C) (hZ : generatedLocalFibrant d S Z) :
    HasLiftingProperty i (terminal.from Z) := by
  let p : CategoryTheory.Arrow C := CategoryTheory.Arrow.mk i
  let j := (cellApproximation d).obj p
  have hj : localTrivialCofibrations d S j.hom := by
    refine ⟨cellApproximation_cofibration d p, ?_⟩
    intro T hT
    exact (nativePrecomp_iff d p T).mpr (hi.2 T hT)
  let _ : IsCofibrant j.left := cellApproximation_source_cofibrant d p
  let _ : IsCofibrant j.right := cellApproximation_target_cofibrant d p
  let _ : HasLiftingProperty j.hom (terminal.from Z) := cofibrant_terminal_lifting d S j.hom hj Z hZ
  let _ : Cofibration j.hom := (cofibration_iff _).mpr hj.1
  let _ : Cofibration i := (cofibration_iff _).mpr hi.1
  let _ : WeakEquivalence ((toOriginal d).app p).left :=
    (weakEquivalence_iff _).mpr (toOriginal_left_trivialFibration d p).2
  let _ : WeakEquivalence ((toOriginal d).app p).right :=
    (weakEquivalence_iff _).mpr (toOriginal_right_trivialFibration d p).2
  let _ : IsFibrant Z := hZ.1
  exact OriginalRelativeMapping.hasLiftingProperty_of_relative_factor
    ((toOriginal d).app p).left j.hom ((toOriginal d).app p).right i
    (toOriginal_square d p).symm (terminal.from Z)

/-- Each actual original derived-local fibrant object is fibrant for the full original local lifting class. -/
theorem localFibrant_terminal_localFibration (Z : C) (hZ : generatedLocalFibrant d S Z) :
    localFibrations d S (terminal.from Z) :=
  fun _ _ i hi => original_terminal_lifting d S i hi Z hZ

/-- The complete original local lifting class has exactly base-fibrant derived-S-local objects. -/
theorem localFibrant_iff_terminal_localFibration (Z : C) :
    generatedLocalFibrant d S Z ↔ localFibrations d S (terminal.from Z) := by
  constructor
  · exact localFibrant_terminal_localFibration d S Z
  · intro hZ
    exact attachingRLP_localFibrant d S Z
      (MorphismProperty.antitone_rlp (attachingClass_le_localTrivialCofibrations d S) _ hZ)

end ArbitraryOriginalEndpoints

section ActualCellularObjectFunctor

variable {C : Type u} [Category.{v} C] [ModelCategory C]
  {κ : Cardinal.{w}} [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
  (d : CofibrantGenerationData C κ) {K : Type wS} [Small.{w} K]
  (S : K → CategoryTheory.Arrow C) (h : CellularSource d)

/-- The actual source-constructed horn approximation satisfies every original derived-S locality test. -/
theorem hornObject_localFibrant (X : C) : generatedLocalFibrant d S ((hornObjectFunctor d S h).obj X) := by
  apply attachingRLP_localFibrant d S
  have hp := hornProjection_rlp d S h X
  rw [show hornProjection d S h X = terminal.from ((hornObjectFunctor d S h).obj X) from
    terminal.hom_ext _ _] at hp
  exact hp

variable [IsLeftProper C]

/-- The actual original attaching cell history and earned generic closure prove the original unit local-weak. -/
theorem hornUnit_localTrivialCofibration (X : C) :
    localTrivialCofibrations d S ((hornUnit d S h).app X) := by
  let _ : (localTrivialCofibrations d S).IsStableUnderCoproducts.{w} := coproducts d S
  let _ : (localTrivialCofibrations d S).IsStableUnderCobaseChange := cobaseChange d S
  let _ : IsStableUnderTransfiniteComposition.{w} (localTrivialCofibrations d S) := transfiniteComposition d S
  let _ : Fact (attachingRank d S h).IsRegular := ⟨attachingRank_regular d S h⟩
  let _ : OrderBot (attachingRank d S h).ord.ToType := attachingRankOrderBot d S h
  let _ : PreservesWellOrderContinuousOfShape (attachingRank d S h).ord.ToType (𝟭 C) :=
    { preservesColimitsOfShape := fun _ _ => inferInstance }
  exact HomotopicalAlgebra.RelativeCellComplex.map_mem_of_le (𝟭 C) (attachingClass d S)
    (localTrivialCofibrations d S) (attachingClass_le_localTrivialCofibrations d S)
    (hornUnitComplex d S h X)

/-- The complete actual object functor recognizes the same original
derived-S-local weak class on all original arrows. -/
theorem localWeak_iff_hornObject_weak {X Y : C} (f : X ⟶ Y) :
    generatedLocalEquivalences d S f ↔
      weakEquivalences C ((hornObjectFunctor d S h).map f) := by
  let _ : (generatedLocalEquivalences d S).HasTwoOutOfThreeProperty := weak_twoOutOfThree d S
  have hX := (hornUnit_localTrivialCofibration d S h X).2
  have hY := (hornUnit_localTrivialCofibration d S h Y).2
  have hn : f ≫ (hornUnit d S h).app Y =
      (hornUnit d S h).app X ≫ (hornObjectFunctor d S h).map f := (hornUnit d S h).naturality f
  have he : generatedLocalEquivalences d S f ↔
      generatedLocalEquivalences d S ((hornObjectFunctor d S h).map f) := by
    constructor
    · intro hf
      apply (generatedLocalEquivalences d S).of_precomp _ _ hX
      rw [← hn]
      exact (generatedLocalEquivalences d S).comp_mem _ _ hf hY
    · intro hf
      apply (generatedLocalEquivalences d S).of_postcomp _ _ hY
      exact hn.symm ▸ (generatedLocalEquivalences d S).comp_mem _ _ hX hf
  exact he.trans (weak_iff_of_local d S ((hornObjectFunctor d S h).map f)
    (hornObject_localFibrant d S h X) (hornObject_localFibrant d S h Y))

end ActualCellularObjectFunctor

end HomotopicalAlgebra.CellularLocalizationRecognition

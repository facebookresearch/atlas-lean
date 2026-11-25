/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Homology.BicomplexTotalAugmentation
public import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
public import Mathlib.CategoryTheory.Retract

/-!
# Actual natural total augmentations of augmented simplicial chain diagrams

The existing alternating single-zero augmentation, native bicomplex flip,
and existing total-augmentation natural transformation give the actual total
augmentation of any augmented simplicial chain diagram. The source uses the
native flipped total; the original unflipped total is compared by the existing
signed total-flip isomorphism.

An actual split pair of augmented diagrams therefore gives a native arrow
retract of their actual total augmentations. This is the generic categorical
transfer for the proper-shuffle projection and earned Eulerian section; it
uses the existing complex, total and retract engines.
-/

@[expose] public section
noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicTopology Opposite
open scoped Simplicial

universe u v

namespace AlgebraicTopology

variable (C : Type u) [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasFiniteCoproducts C]

/-- The actual flipped alternating-face bicomplex of an original augmented simplicial chain diagram. -/
def augmentedChainBicomplexFunctor :
    SimplicialObject.Augmented (ChainComplex C ℕ) ⥤ HomologicalComplex₂ C (.down ℕ) (.down ℕ) :=
  SimplicialObject.Augmented.drop ⋙ alternatingFaceMapComplex (ChainComplex C ℕ) ⋙
    HomologicalComplex₂.flipFunctor C (.down ℕ) (.down ℕ)

/-- The actual original augmentation point of the augmented chain diagram. -/
def augmentedChainPointFunctor : SimplicialObject.Augmented (ChainComplex C ℕ) ⥤ ChainComplex C ℕ :=
  SimplicialObject.Augmented.point

/-- Native evaluation and alternating transport give the actual horizontal
single-zero augmentation, with precisely the original component map. -/
def augmentedChainHorizontalAugmentation (X : SimplicialObject.Augmented (ChainComplex C ℕ)) (q : ℕ) :
    ((HomologicalComplex₂.flipFunctor C (.down ℕ) (.down ℕ)).obj
      ((alternatingFaceMapComplex (ChainComplex C ℕ)).obj X.left)).X q ⟶
      (((ChainComplex.single₀ C).mapHomologicalComplex (.down ℕ)).obj X.right).X q :=
  (ChainComplex.toSingle₀Equiv _ _).symm
    ⟨(X.hom.app (op ⦋0⦌)).f q, by
      change (((alternatingFaceMapComplex (ChainComplex C ℕ)).obj X.left).d 1 0).f q ≫
        (X.hom.app (op ⦋0⦌)).f q = 0
      have h := congrArg (fun t : X.left.obj (op ⦋1⦌) ⟶ X.right => t.f q)
        ((AlternatingFaceMapComplex.ε.app X).comm 1 0)
      rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f,
        AlternatingFaceMapComplex.ε_app_f_zero, AlternatingFaceMapComplex.ε_app_f_succ,
        HomologicalComplex.zero_f, Limits.zero_comp] at h
      exact h.symm⟩

omit [HasFiniteCoproducts C] in
/-- The horizontal augmentation stores the original simplicial degree-zero chain component. -/
theorem augmentedChainHorizontalAugmentation_f_zero
    (X : SimplicialObject.Augmented (ChainComplex C ℕ)) (q : ℕ) :
    (augmentedChainHorizontalAugmentation C X q).f 0 = (X.hom.app (op ⦋0⦌)).f q :=
  ChainComplex.toSingle₀Equiv_symm_apply_f_zero _ _

/-- The original augmented chain square assembles the actual flipped bicomplex map. -/
def augmentedChainBicomplexAugmentationApp (X : SimplicialObject.Augmented (ChainComplex C ℕ)) :
    (HomologicalComplex₂.flipFunctor C (.down ℕ) (.down ℕ)).obj
      ((alternatingFaceMapComplex (ChainComplex C ℕ)).obj X.left) ⟶
      ((ChainComplex.single₀ C).mapHomologicalComplex (.down ℕ)).obj X.right := by
  refine ChainComplex.ofHom (augmentedChainHorizontalAugmentation C X) ?_
  intro q
  apply HomologicalComplex.to_single_hom_ext (j := 0)
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f]
  have h := (X.hom.app (op ⦋0⦌)).comm (q + 1) q
  have hz := augmentedChainHorizontalAugmentation_f_zero C X q
  have hs := augmentedChainHorizontalAugmentation_f_zero C X (q + 1)
  have hsingle :
      ((((ChainComplex.single₀ C).mapHomologicalComplex (.down ℕ)).obj X.right).d (q + 1) q).f 0 =
        X.right.d (q + 1) q :=
    ChainComplex.single₀_map_f_zero (X.right.d (q + 1) q)
  have hflip :
      (((HomologicalComplex₂.flipFunctor C (.down ℕ) (.down ℕ)).obj
        ((alternatingFaceMapComplex (ChainComplex C ℕ)).obj X.left)).d (q + 1) q).f 0 =
          (X.left.obj (op ⦋0⦌)).d (q + 1) q := rfl
  exact (congrArg₂ (fun a b => a ≫ b) hs hsingle).trans
    (h.trans (congrArg₂ (fun a b => a ≫ b) hflip hz).symm)

omit [HasFiniteCoproducts C] in
/-- Every original augmented diagram morphism preserves the original bicomplex augmentation. -/
theorem augmentedChainBicomplexAugmentationApp_naturality
    {X Y : SimplicialObject.Augmented (ChainComplex C ℕ)} (f : X ⟶ Y) :
    (HomologicalComplex₂.flipFunctor C (.down ℕ) (.down ℕ)).map
        ((alternatingFaceMapComplex (ChainComplex C ℕ)).map f.left) ≫
      augmentedChainBicomplexAugmentationApp C Y =
    augmentedChainBicomplexAugmentationApp C X ≫
      ((ChainComplex.single₀ C).mapHomologicalComplex (.down ℕ)).map f.right := by
  apply HomologicalComplex.hom_ext
  intro q
  apply HomologicalComplex.to_single_hom_ext (j := 0)
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f,
    HomologicalComplex.comp_f, HomologicalComplex.comp_f]
  change (f.left.app (op ⦋0⦌)).f q ≫
      (augmentedChainHorizontalAugmentation C Y q).f 0 =
    (augmentedChainHorizontalAugmentation C X q).f 0 ≫
      ((ChainComplex.single₀ C).map (f.right.f q)).f 0
  rw [ChainComplex.single₀_map_f_zero]
  have h := congrArg (fun t : X.left.obj (op ⦋0⦌) ⟶ Y.right => t.f q)
    (SimplicialObject.Augmented.w₀ f)
  exact (congrArg (fun t => (f.left.app (op ⦋0⦌)).f q ≫ t)
    (augmentedChainHorizontalAugmentation_f_zero C Y q)).trans
      (h.trans (congrArg (fun t => t ≫ f.right.f q)
        (augmentedChainHorizontalAugmentation_f_zero C X q).symm))

/-- The original augmentation is natural for every actual augmented-chain diagram morphism. -/
def augmentedChainBicomplexAugmentation : augmentedChainBicomplexFunctor C ⟶
    augmentedChainPointFunctor C ⋙ HomologicalComplex₂.singleMapBicomplexFunctorDownNat where
  app X := augmentedChainBicomplexAugmentationApp C X
  naturality {_X _Y} f := augmentedChainBicomplexAugmentationApp_naturality C f

/-- The original flipped-total functor of augmented simplicial chain diagrams. -/
def augmentedChainTotalFunctor : SimplicialObject.Augmented (ChainComplex C ℕ) ⥤ ChainComplex C ℕ :=
  augmentedChainBicomplexFunctor C ⋙ HomologicalComplex₂.totalFunctor C (.down ℕ) (.down ℕ) (.down ℕ)

/-- The actual total augmentation is native and natural in the original augmented diagram. -/
def augmentedChainTotalAugmentation : augmentedChainTotalFunctor C ⟶ augmentedChainPointFunctor C :=
  HomologicalComplex₂.totalAugmentationNatTransDownNat (augmentedChainBicomplexFunctor C)
    (augmentedChainPointFunctor C) (augmentedChainBicomplexAugmentation C)

/-- Native naturality sends an actual augmented-diagram retraction to the actual augmentation arrow retraction. -/
def augmentedChainTotalAugmentation_retract
    {X Y : SimplicialObject.Augmented (ChainComplex C ℕ)} (h : Retract X Y) :
    RetractArrow ((augmentedChainTotalAugmentation C).app X) ((augmentedChainTotalAugmentation C).app Y) :=
  (augmentedChainTotalAugmentation C).retractArrowApp h

end AlgebraicTopology

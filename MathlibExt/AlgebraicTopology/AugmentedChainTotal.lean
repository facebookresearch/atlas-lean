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
# Total augmentations of augmented simplicial chain diagrams

Let `C` be a preadditive category with a zero object and finite coproducts. An augmented
simplicial chain diagram has chain degree `q` and simplicial degree `p`. Take its alternating-
face bicomplex, interchange the two indices, and form the finite-diagonal total, with
differential `d_chain + (-1)^q d_simp` on bidegree `(q,p)`.

The simplicial augmentation in degree zero defines the total augmentation to the diagram's
augmentation-point chain complex. These maps are natural in augmented diagram morphisms. A
retract of augmented diagrams therefore induces an arrow retract of their total augmentations.
-/

@[expose] public section
noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicTopology Opposite
open scoped Simplicial

universe u v

namespace AlgebraicTopology

variable (C : Type u) [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasFiniteCoproducts C]

/-- The flipped alternating bicomplex of an augmented chain diagram.

Drop the augmentation, take alternating faces in the simplicial direction, and flip the two
indices to obtain a bicomplex with outer chain degree and inner simplicial degree. -/
def augmentedChainBicomplexFunctor :
    SimplicialObject.Augmented (ChainComplex C ℕ) ⥤ HomologicalComplex₂ C (.down ℕ) (.down ℕ) :=
  SimplicialObject.Augmented.drop ⋙ alternatingFaceMapComplex (ChainComplex C ℕ) ⋙
    HomologicalComplex₂.flipFunctor C (.down ℕ) (.down ℕ)

/-- The augmentation-point functor of simplicial chain diagrams.

An augmented simplicial chain diagram is sent to its augmentation target chain complex. -/
def augmentedChainPointFunctor : SimplicialObject.Augmented (ChainComplex C ℕ) ⥤ ChainComplex C ℕ :=
  SimplicialObject.Augmented.point

/-- The horizontal single-zero augmentation in a fixed chain degree.

For chain degree `q`, the simplicial degree-zero augmentation component gives a chain map from
the flipped horizontal complex to the single-zero complex on the target's degree-`q` object. -/
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
/-- The degree-zero component of a horizontal chain-diagram augmentation.

The component is the chain degree-`q` map of the given simplicial degree-zero augmentation. -/
theorem augmentedChainHorizontalAugmentation_f_zero
    (X : SimplicialObject.Augmented (ChainComplex C ℕ)) (q : ℕ) :
    (augmentedChainHorizontalAugmentation C X q).f 0 = (X.hom.app (op ⦋0⦌)).f q :=
  ChainComplex.toSingle₀Equiv_symm_apply_f_zero _ _

/-- The bicomplex augmentation of a simplicial chain diagram.

The horizontal single-zero augmentations assemble into a map from the flipped alternating
bicomplex to the bicomplex of the augmentation target concentrated in inner degree zero. -/
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
/-- Naturality of augmented chain-diagram bicomplex maps.

An augmented diagram morphism commutes with the bicomplex augmentation and the induced map on
the target single-zero bicomplex. -/
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

/-- The natural bicomplex augmentation of simplicial chain diagrams.

The degreewise bicomplex augmentations give a natural transformation to the single-zero
bicomplex functor of the augmentation point. -/
def augmentedChainBicomplexAugmentation : augmentedChainBicomplexFunctor C ⟶
    augmentedChainPointFunctor C ⋙ HomologicalComplex₂.singleMapBicomplexFunctorDownNat where
  app X := augmentedChainBicomplexAugmentationApp C X
  naturality {_X _Y} f := augmentedChainBicomplexAugmentationApp_naturality C f

/-- The flipped total functor of augmented simplicial chain diagrams.

Form the signed finite-diagonal total of the flipped alternating-face bicomplex. -/
def augmentedChainTotalFunctor : SimplicialObject.Augmented (ChainComplex C ℕ) ⥤ ChainComplex C ℕ :=
  augmentedChainBicomplexFunctor C ⋙ HomologicalComplex₂.totalFunctor C (.down ℕ) (.down ℕ) (.down ℕ)

/-- The natural total augmentation of simplicial chain diagrams.

The bicomplex augmentation induces a natural chain map from the flipped total complex to the
augmentation-point chain complex. -/
def augmentedChainTotalAugmentation : augmentedChainTotalFunctor C ⟶ augmentedChainPointFunctor C :=
  HomologicalComplex₂.totalAugmentationNatTransDownNat (augmentedChainBicomplexFunctor C)
    (augmentedChainPointFunctor C) (augmentedChainBicomplexAugmentation C)

/-- The total-augmentation arrow retract of an augmented diagram retract.

A retraction of augmented simplicial chain diagrams gives a retraction of their total-
augmentation arrows by naturality. -/
def augmentedChainTotalAugmentation_retract
    {X Y : SimplicialObject.Augmented (ChainComplex C ℕ)} (h : Retract X Y) :
    RetractArrow ((augmentedChainTotalAugmentation C).app X) ((augmentedChainTotalAugmentation C).app Y) :=
  (augmentedChainTotalAugmentation C).retractArrowApp h

end AlgebraicTopology

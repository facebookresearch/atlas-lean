/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.CategoryTheory.HomologicalComplex.FunctorRelativeResolutionComparison.Coherence
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex

/-!
# Homology of relative comparison maps

An additive functor sends relative comparison maps and their homotopies to maps and homotopies of
complexes. Homotopic comparisons induce the same homology map, giving identity and composition
laws on homology. The comparison homotopy equivalence gives homology isomorphisms wherever the
displayed homologies exist.
-/

@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex
universe uC vC uD vD uE vE
namespace CategoryTheory.Functor

variable {D : Type uD} [Category.{vD} D] [Preadditive D] [HasZeroObject D] [HasKernels D]
  {C : Type uC} [Category.{vC} C] [Preadditive C]
  {E : Type uE} [Category.{vE} E] [Preadditive E]
  (U : D ⥤ C) [U.Additive] (T : D ⥤ E) [T.Additive]

/-- Application of T to an original resolution complex. -/
abbrev mappedResolution (Q : ChainComplex D ℕ) : ChainComplex E ℕ :=
  (T.mapHomologicalComplex (ComplexShape.down ℕ)).obj Q

/-- The T-image of the original constructed endpoint comparison. -/
def mappedRelativeComparison (Q P : ChainComplex D ℕ) (X Y : D)
    (α : Q ⟶ (ChainComplex.single₀ D).obj X) (β : P ⟶ (ChainComplex.single₀ D).obj Y)
    (σP : AugmentationSplit U P Y β) (hQ : ∀ n, U.IsRelativeProjective (Q.X n))
    [PreservesLimit (parallelPair (β.f 0) 0) U]
    (kP : ∀ n, PreservesLimit (parallelPair (P.d (n + 1) n) 0) U) (f : X ⟶ Y) :
    mappedResolution T Q ⟶ mappedResolution T P :=
  (T.mapHomologicalComplex (ComplexShape.down ℕ)).map
    (comparison U Q P X Y α β σP hQ kP f)

/-- The homology comparison uses the mapped original chain comparison. -/
def comparisonHomologyMap (Q P : ChainComplex D ℕ) (X Y : D)
    (α : Q ⟶ (ChainComplex.single₀ D).obj X) (β : P ⟶ (ChainComplex.single₀ D).obj Y)
    (σP : AugmentationSplit U P Y β) (hQ : ∀ n, U.IsRelativeProjective (Q.X n))
    [PreservesLimit (parallelPair (β.f 0) 0) U]
    (kP : ∀ n, PreservesLimit (parallelPair (P.d (n + 1) n) 0) U) (f : X ⟶ Y) (n : ℕ)
    [(mappedResolution T Q).HasHomology n] [(mappedResolution T P).HasHomology n] :
    (mappedResolution T Q).homology n ⟶ (mappedResolution T P).homology n :=
  homologyMap (mappedRelativeComparison U T Q P X Y α β σP hQ kP f) n

/-- Every pair of original augmentation-compatible maps induces the same mapped homology map. -/
theorem mappedHomologyMap_independent (Q P : ChainComplex D ℕ) (X Y : D)
    (α : Q ⟶ (ChainComplex.single₀ D).obj X) (β : P ⟶ (ChainComplex.single₀ D).obj Y)
    (σP : AugmentationSplit U P Y β) (hQ : ∀ n, U.IsRelativeProjective (Q.X n))
    [PreservesLimit (parallelPair (β.f 0) 0) U]
    (kP : ∀ n, PreservesLimit (parallelPair (P.d (n + 1) n) 0) U)
    (f : X ⟶ Y) (g h : Q ⟶ P)
    (hg : g ≫ β = α ≫ (ChainComplex.single₀ D).map f)
    (hh : h ≫ β = α ≫ (ChainComplex.single₀ D).map f) (n : ℕ)
    [(mappedResolution T Q).HasHomology n] [(mappedResolution T P).HasHomology n] :
    homologyMap ((T.mapHomologicalComplex (ComplexShape.down ℕ)).map g) n =
      homologyMap ((T.mapHomologicalComplex (ComplexShape.down ℕ)).map h) n :=
  (T.mapHomotopy (comparisonHomotopy U Q P X Y α β σP hQ kP f g h hg hh)).homologyMap_eq n

/-- The computed comparison homology map agrees with every original map over the same endpoint. -/
theorem comparisonHomologyMap_eq_of_augmentation (Q P : ChainComplex D ℕ) (X Y : D)
    (α : Q ⟶ (ChainComplex.single₀ D).obj X) (β : P ⟶ (ChainComplex.single₀ D).obj Y)
    (σP : AugmentationSplit U P Y β) (hQ : ∀ n, U.IsRelativeProjective (Q.X n))
    [PreservesLimit (parallelPair (β.f 0) 0) U]
    (kP : ∀ n, PreservesLimit (parallelPair (P.d (n + 1) n) 0) U)
    (f : X ⟶ Y) (g : Q ⟶ P) (hg : g ≫ β = α ≫ (ChainComplex.single₀ D).map f) (n : ℕ)
    [(mappedResolution T Q).HasHomology n] [(mappedResolution T P).HasHomology n] :
    comparisonHomologyMap U T Q P X Y α β σP hQ kP f n =
      homologyMap ((T.mapHomologicalComplex (ComplexShape.down ℕ)).map g) n :=
  mappedHomologyMap_independent U T Q P X Y α β σP hQ kP f _ g
    (comparison_augmentation U Q P X Y α β σP hQ kP f) hg n

/-- The identity comparison induces the identity on mapped homology in every available degree. -/
theorem comparisonHomologyMap_id (Q : ChainComplex D ℕ) (X : D)
    (α : Q ⟶ (ChainComplex.single₀ D).obj X) (σQ : AugmentationSplit U Q X α)
    (hQ : ∀ n, U.IsRelativeProjective (Q.X n))
    [PreservesLimit (parallelPair (α.f 0) 0) U]
    (kQ : ∀ n, PreservesLimit (parallelPair (Q.d (n + 1) n) 0) U) (n : ℕ)
    [(mappedResolution T Q).HasHomology n] :
    comparisonHomologyMap U T Q Q X X α α σQ hQ kQ (𝟙 X) n = 𝟙 _ := by
  have h := (T.mapHomotopy (comparisonIdHomotopy U Q X α σQ hQ kQ)).homologyMap_eq n
  dsimp only [comparisonHomologyMap, mappedRelativeComparison]
  simpa only [Functor.map_id, homologyMap_id] using h

/-- Mapped comparison coherence proves the homology composition law. -/
theorem comparisonHomologyMap_comp (Q P R : ChainComplex D ℕ) (X Y Z : D)
    (α : Q ⟶ (ChainComplex.single₀ D).obj X) (β : P ⟶ (ChainComplex.single₀ D).obj Y)
    (γ : R ⟶ (ChainComplex.single₀ D).obj Z)
    (σP : AugmentationSplit U P Y β) (σR : AugmentationSplit U R Z γ)
    (hQ : ∀ n, U.IsRelativeProjective (Q.X n)) (hP : ∀ n, U.IsRelativeProjective (P.X n))
    [PreservesLimit (parallelPair (β.f 0) 0) U] [PreservesLimit (parallelPair (γ.f 0) 0) U]
    (kP : ∀ n, PreservesLimit (parallelPair (P.d (n + 1) n) 0) U)
    (kR : ∀ n, PreservesLimit (parallelPair (R.d (n + 1) n) 0) U)
    (f : X ⟶ Y) (g : Y ⟶ Z) (n : ℕ)
    [(mappedResolution T Q).HasHomology n] [(mappedResolution T P).HasHomology n]
    [(mappedResolution T R).HasHomology n] :
    comparisonHomologyMap U T Q R X Z α γ σR hQ kR (f ≫ g) n =
      comparisonHomologyMap U T Q P X Y α β σP hQ kP f n ≫
        comparisonHomologyMap U T P R Y Z β γ σR hP kR g n := by
  have h := (T.mapHomotopy
    (comparisonCompHomotopy U Q P R X Y Z α β γ σP σR hQ hP kP kR f g)).homologyMap_eq n
  dsimp only [comparisonHomologyMap, mappedRelativeComparison]
  simpa only [Functor.map_comp, homologyMap_comp] using h

/-- The mapped inverse comparisons earn a homology isomorphism. -/
def comparisonHomologyIso (Q P : ChainComplex D ℕ) (X : D)
    (α : Q ⟶ (ChainComplex.single₀ D).obj X) (β : P ⟶ (ChainComplex.single₀ D).obj X)
    (σQ : AugmentationSplit U Q X α) (σP : AugmentationSplit U P X β)
    (hQ : ∀ n, U.IsRelativeProjective (Q.X n)) (hP : ∀ n, U.IsRelativeProjective (P.X n))
    [PreservesLimit (parallelPair (α.f 0) 0) U] [PreservesLimit (parallelPair (β.f 0) 0) U]
    (kQ : ∀ n, PreservesLimit (parallelPair (Q.d (n + 1) n) 0) U)
    (kP : ∀ n, PreservesLimit (parallelPair (P.d (n + 1) n) 0) U) (n : ℕ)
    [(mappedResolution T Q).HasHomology n] [(mappedResolution T P).HasHomology n] :
    (mappedResolution T Q).homology n ≅ (mappedResolution T P).homology n :=
  (T.mapHomotopyEquiv (comparisonHomotopyEquiv U Q P X α β σQ σP hQ hP kQ kP)).toHomologyIso n

/-- The homology isomorphism's forward map is the computed identity comparison. -/
theorem comparisonHomologyIso_hom (Q P : ChainComplex D ℕ) (X : D)
    (α : Q ⟶ (ChainComplex.single₀ D).obj X) (β : P ⟶ (ChainComplex.single₀ D).obj X)
    (σQ : AugmentationSplit U Q X α) (σP : AugmentationSplit U P X β)
    (hQ : ∀ n, U.IsRelativeProjective (Q.X n)) (hP : ∀ n, U.IsRelativeProjective (P.X n))
    [PreservesLimit (parallelPair (α.f 0) 0) U] [PreservesLimit (parallelPair (β.f 0) 0) U]
    (kQ : ∀ n, PreservesLimit (parallelPair (Q.d (n + 1) n) 0) U)
    (kP : ∀ n, PreservesLimit (parallelPair (P.d (n + 1) n) 0) U) (n : ℕ)
    [(mappedResolution T Q).HasHomology n] [(mappedResolution T P).HasHomology n] :
    (comparisonHomologyIso U T Q P X α β σQ σP hQ hP kQ kP n).hom =
      comparisonHomologyMap U T Q P X X α β σP hQ kP (𝟙 X) n := rfl

/-- T applied to the original comparison retains the full mapped augmentation square. -/
theorem mappedRelativeComparison_augmentation (Q P : ChainComplex D ℕ) (X Y : D)
    (α : Q ⟶ (ChainComplex.single₀ D).obj X) (β : P ⟶ (ChainComplex.single₀ D).obj Y)
    (σP : AugmentationSplit U P Y β) (hQ : ∀ n, U.IsRelativeProjective (Q.X n))
    [PreservesLimit (parallelPair (β.f 0) 0) U]
    (kP : ∀ n, PreservesLimit (parallelPair (P.d (n + 1) n) 0) U) (f : X ⟶ Y) :
    mappedRelativeComparison U T Q P X Y α β σP hQ kP f ≫
        (T.mapHomologicalComplex (ComplexShape.down ℕ)).map β =
      (T.mapHomologicalComplex (ComplexShape.down ℕ)).map α ≫
        (T.mapHomologicalComplex (ComplexShape.down ℕ)).map ((ChainComplex.single₀ D).map f) := by
  have h := congrArg ((T.mapHomologicalComplex (ComplexShape.down ℕ)).map)
    (comparison_augmentation U Q P X Y α β σP hQ kP f)
  dsimp only [mappedRelativeComparison]
  simpa only [Functor.map_comp] using h

/-- The homology comparison retains the T-image augmentations in every available degree. -/
theorem comparisonHomologyMap_augmentation (Q P : ChainComplex D ℕ) (X Y : D)
    (α : Q ⟶ (ChainComplex.single₀ D).obj X) (β : P ⟶ (ChainComplex.single₀ D).obj Y)
    (σP : AugmentationSplit U P Y β) (hQ : ∀ n, U.IsRelativeProjective (Q.X n))
    [PreservesLimit (parallelPair (β.f 0) 0) U]
    (kP : ∀ n, PreservesLimit (parallelPair (P.d (n + 1) n) 0) U) (f : X ⟶ Y) (n : ℕ)
    [(mappedResolution T Q).HasHomology n] [(mappedResolution T P).HasHomology n]
    [(mappedResolution T ((ChainComplex.single₀ D).obj X)).HasHomology n]
    [(mappedResolution T ((ChainComplex.single₀ D).obj Y)).HasHomology n] :
    comparisonHomologyMap U T Q P X Y α β σP hQ kP f n ≫
        homologyMap ((T.mapHomologicalComplex (ComplexShape.down ℕ)).map β) n =
      homologyMap ((T.mapHomologicalComplex (ComplexShape.down ℕ)).map α) n ≫
        homologyMap ((T.mapHomologicalComplex (ComplexShape.down ℕ)).map ((ChainComplex.single₀ D).map f)) n := by
  have h := congrArg (fun z => homologyMap z n)
    (mappedRelativeComparison_augmentation U T Q P X Y α β σP hQ kP f)
  dsimp only [comparisonHomologyMap]
  simpa only [homologyMap_comp] using h

omit [HasKernels D] in
/-- The mapped original augmentation has its literal original degree-zero component under T. -/
theorem mappedAugmentation_f_zero (Q : ChainComplex D ℕ) (X : D)
    (α : Q ⟶ (ChainComplex.single₀ D).obj X) :
    ((T.mapHomologicalComplex (ComplexShape.down ℕ)).map α).f 0 = T.map (α.f 0) := rfl

end CategoryTheory.Functor

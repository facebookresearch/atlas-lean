/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.CategoryTheory.HomologicalComplex.FunctorRelativeResolutionComparison

/-!
# Coherence of relative comparison maps

Identity and composition comparison maps are compatible up to chain homotopy. The identity
comparison maps in both directions give a homotopy equivalence of split relative resolutions. No
strictly functorial choice of chain lifts is needed.
-/

@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Limits
universe uC vC uD vD
namespace CategoryTheory.Functor

variable {D : Type uD} [Category.{vD} D] [Preadditive D] [HasZeroObject D] [HasKernels D]
  {C : Type uC} [Category.{vC} C] [Preadditive C]
  (U : D ⥤ C) [U.Additive]

/-- The comparison lifting the identity is homotopic to the original identity map. -/
def comparisonIdHomotopy (Q : ChainComplex D ℕ) (X : D)
    (α : Q ⟶ (ChainComplex.single₀ D).obj X) (σ : AugmentationSplit U Q X α)
    (hQ : ∀ n, U.IsRelativeProjective (Q.X n))
    [PreservesLimit (parallelPair (α.f 0) 0) U]
    (hker : ∀ n, PreservesLimit (parallelPair (Q.d (n + 1) n) 0) U) :
    Homotopy (comparison U Q Q X X α α σ hQ hker (𝟙 X)) (𝟙 Q) :=
  comparisonHomotopy U Q Q X X α α σ hQ hker (𝟙 X)
    (comparison U Q Q X X α α σ hQ hker (𝟙 X)) (𝟙 Q)
    (comparison_augmentation U Q Q X X α α σ hQ hker (𝟙 X))
    (by rw [Category.id_comp, Functor.map_id, Category.comp_id])

/-- The composite preserves the original complete augmentation square. -/
theorem comparison_composite_augmentation (Q P R : ChainComplex D ℕ) (X Y Z : D)
    (α : Q ⟶ (ChainComplex.single₀ D).obj X)
    (β : P ⟶ (ChainComplex.single₀ D).obj Y)
    (γ : R ⟶ (ChainComplex.single₀ D).obj Z)
    (σP : AugmentationSplit U P Y β) (σR : AugmentationSplit U R Z γ)
    (hQ : ∀ n, U.IsRelativeProjective (Q.X n)) (hP : ∀ n, U.IsRelativeProjective (P.X n))
    [PreservesLimit (parallelPair (β.f 0) 0) U] [PreservesLimit (parallelPair (γ.f 0) 0) U]
    (kP : ∀ n, PreservesLimit (parallelPair (P.d (n + 1) n) 0) U)
    (kR : ∀ n, PreservesLimit (parallelPair (R.d (n + 1) n) 0) U)
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    (comparison U Q P X Y α β σP hQ kP f ≫ comparison U P R Y Z β γ σR hP kR g) ≫ γ =
      α ≫ (ChainComplex.single₀ D).map (f ≫ g) := by
  rw [Category.assoc, comparison_augmentation, ← Category.assoc, comparison_augmentation,
    Category.assoc, ← Functor.map_comp]

/-- The constructed comparison of a composition is homotopic to the two original comparison maps. -/
def comparisonCompHomotopy (Q P R : ChainComplex D ℕ) (X Y Z : D)
    (α : Q ⟶ (ChainComplex.single₀ D).obj X)
    (β : P ⟶ (ChainComplex.single₀ D).obj Y)
    (γ : R ⟶ (ChainComplex.single₀ D).obj Z)
    (σP : AugmentationSplit U P Y β) (σR : AugmentationSplit U R Z γ)
    (hQ : ∀ n, U.IsRelativeProjective (Q.X n)) (hP : ∀ n, U.IsRelativeProjective (P.X n))
    [PreservesLimit (parallelPair (β.f 0) 0) U] [PreservesLimit (parallelPair (γ.f 0) 0) U]
    (kP : ∀ n, PreservesLimit (parallelPair (P.d (n + 1) n) 0) U)
    (kR : ∀ n, PreservesLimit (parallelPair (R.d (n + 1) n) 0) U)
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    Homotopy (comparison U Q R X Z α γ σR hQ kR (f ≫ g))
      (comparison U Q P X Y α β σP hQ kP f ≫ comparison U P R Y Z β γ σR hP kR g) :=
  comparisonHomotopy U Q R X Z α γ σR hQ kR (f ≫ g) _ _
    (comparison_augmentation U Q R X Z α γ σR hQ kR (f ≫ g))
    (comparison_composite_augmentation U Q P R X Y Z α β γ σP σR hQ hP kP kR f g)

/-- Inverse original identity comparisons give an homotopy equivalence. -/
def comparisonHomotopyEquiv (Q P : ChainComplex D ℕ) (X : D)
    (α : Q ⟶ (ChainComplex.single₀ D).obj X) (β : P ⟶ (ChainComplex.single₀ D).obj X)
    (σQ : AugmentationSplit U Q X α) (σP : AugmentationSplit U P X β)
    (hQ : ∀ n, U.IsRelativeProjective (Q.X n)) (hP : ∀ n, U.IsRelativeProjective (P.X n))
    [PreservesLimit (parallelPair (α.f 0) 0) U] [PreservesLimit (parallelPair (β.f 0) 0) U]
    (kQ : ∀ n, PreservesLimit (parallelPair (Q.d (n + 1) n) 0) U)
    (kP : ∀ n, PreservesLimit (parallelPair (P.d (n + 1) n) 0) U) : HomotopyEquiv Q P where
  hom := comparison U Q P X X α β σP hQ kP (𝟙 X)
  inv := comparison U P Q X X β α σQ hP kQ (𝟙 X)
  homotopyHomInvId :=
    (comparisonCompHomotopy U Q P Q X X X α β α σP σQ hQ hP kP kQ (𝟙 X) (𝟙 X)).symm.trans
      ((Homotopy.ofEq (congrArg (comparison U Q Q X X α α σQ hQ kQ) (Category.id_comp (𝟙 X)))).trans
        (comparisonIdHomotopy U Q X α σQ hQ kQ))
  homotopyInvHomId :=
    (comparisonCompHomotopy U P Q P X X X β α β σQ σP hP hQ kQ kP (𝟙 X) (𝟙 X)).symm.trans
      ((Homotopy.ofEq (congrArg (comparison U P P X X β β σP hP kP) (Category.id_comp (𝟙 X)))).trans
        (comparisonIdHomotopy U P X β σP hP kP))

/-- The equivalence's forward comparison retains the original augmentation. -/
theorem comparisonHomotopyEquiv_hom_augmentation (Q P : ChainComplex D ℕ) (X : D)
    (α : Q ⟶ (ChainComplex.single₀ D).obj X) (β : P ⟶ (ChainComplex.single₀ D).obj X)
    (σQ : AugmentationSplit U Q X α) (σP : AugmentationSplit U P X β)
    (hQ : ∀ n, U.IsRelativeProjective (Q.X n)) (hP : ∀ n, U.IsRelativeProjective (P.X n))
    [PreservesLimit (parallelPair (α.f 0) 0) U] [PreservesLimit (parallelPair (β.f 0) 0) U]
    (kQ : ∀ n, PreservesLimit (parallelPair (Q.d (n + 1) n) 0) U)
    (kP : ∀ n, PreservesLimit (parallelPair (P.d (n + 1) n) 0) U) :
    (comparisonHomotopyEquiv U Q P X α β σQ σP hQ hP kQ kP).hom ≫ β = α := by
  have h := comparison_augmentation U Q P X X α β σP hQ kP (𝟙 X)
  dsimp only [comparisonHomotopyEquiv]
  simpa only [Functor.map_id, Category.comp_id] using h

end CategoryTheory.Functor

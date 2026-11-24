/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


/- UNEXECUTED source proposal. Comparison uses native projective resolutions. -/
module

public import MathlibExt.Algebra.Homology.Hochschild.AdjacentBarCoefficientComparison

/-!
# Computing coefficient Hochschild homology by resolutions

For a ground-projective algebra, the adjacent enveloping bar can be
compared with any projective resolution of the regular enveloping
module. Tensoring the comparison with an arbitrary bimodule M gives
a chain homotopy equivalence computing its Hochschild complex.
The coefficient module need not be flat or projective.
-/

@[expose] public section
noncomputable section

open CategoryTheory

universe u v w

namespace ModuleCat.Algebra.Hochschild.AdjacentBar

variable (k : Type u) [CommRing k] (A : Type v) [Ring A] [Algebra k A]
  [Module.Projective k A]

/-- Compare the original bar with an resolution of its original target. -/
def envelopingBarResolutionComparison
    (P : ProjectiveResolution (regularEnvelopingTarget k A)) :
    HomotopyEquiv (envelopingBar k A) P.complex :=
  ProjectiveResolution.homotopyEquiv (envelopingBarProjectiveResolution k A) P

/-- The native forward comparison covers the original multiplication augmentation. -/
@[reassoc]
theorem envelopingBarResolutionComparison_hom_π
    (P : ProjectiveResolution (regularEnvelopingTarget k A)) :
    (envelopingBarResolutionComparison k A P).hom ≫ P.π =
      envelopingBarAugmentationMap k A :=
  ProjectiveResolution.homotopyEquiv_hom_π (envelopingBarProjectiveResolution k A) P

/-- The native inverse comparison covers the same original multiplication augmentation. -/
@[reassoc]
theorem envelopingBarResolutionComparison_inv_π
    (P : ProjectiveResolution (regularEnvelopingTarget k A)) :
    (envelopingBarResolutionComparison k A P).inv ≫ envelopingBarAugmentationMap k A = P.π :=
  ProjectiveResolution.homotopyEquiv_inv_π (envelopingBarProjectiveResolution k A) P

/-- Any lift of the identity augmentation is homotopic to the native bar comparison. -/
def envelopingBarResolutionComparisonLiftHomotopy
    (P : ProjectiveResolution (regularEnvelopingTarget k A))
    (f : envelopingBar k A ⟶ P.complex)
    (hf : f ≫ P.π = envelopingBarAugmentationMap k A) :
    Homotopy f (envelopingBarResolutionComparison k A P).hom :=
  ProjectiveResolution.liftHomotopy (𝟙 (regularEnvelopingTarget k A))
    (P := envelopingBarProjectiveResolution k A) (Q := P) f
    (envelopingBarResolutionComparison k A P).hom
    (by
      simp only [Functor.map_id, Category.comp_id, envelopingBarProjectiveResolution_π] at ⊢
      have htarget := (ChainComplex.single₀ (ModuleCat.{max u v} (EnvelopingAlgebra k A))).map_id
        (regularEnvelopingTarget k A)
      erw [htarget, Category.comp_id]
      exact hf)
    (by
      simp only [Functor.map_id, Category.comp_id, envelopingBarProjectiveResolution_π] at ⊢
      have htarget := (ChainComplex.single₀ (ModuleCat.{max u v} (EnvelopingAlgebra k A))).map_id
        (regularEnvelopingTarget k A)
      erw [htarget, Category.comp_id]
      exact envelopingBarResolutionComparison_hom_π k A P)

variable (M : Type w) [AddCommGroup M] [Module k M] [Module A M] [Module Aᵐᵒᵖ M]
  [SMulCommClass A Aᵐᵒᵖ M] [SMulCommClass k A M] [SMulCommClass k Aᵐᵒᵖ M]
  [IsScalarTower k A M] [IsScalarTower k Aᵐᵒᵖ M]

/-- Apply the original coefficient tensor functor to the resolving complex. -/
def coefficientResolutionTensorComplex
    (P : ProjectiveResolution (regularEnvelopingTarget k A)) :
    ChainComplex (ModuleCat.{max u v w} k) ℕ :=
  ((coefficientTensorFunctor k A M).mapHomologicalComplex (ComplexShape.down ℕ)).obj P.complex

/-- Additivity of the balanced tensor functor preserves the native resolution homotopies. -/
def coefficientResolutionTensorComparison
    (P : ProjectiveResolution (regularEnvelopingTarget k A)) :
    HomotopyEquiv (coefficientTensorComplex k A M) (coefficientResolutionTensorComplex k A M P) :=
  (coefficientTensorFunctor k A M).mapHomotopyEquiv (envelopingBarResolutionComparison k A P)

omit [SMulCommClass k A M] [SMulCommClass k Aᵐᵒᵖ M] in
/-- Its forward map is the functor image of the augmentation-preserving bar comparison. -/
theorem coefficientResolutionTensorComparison_hom
    (P : ProjectiveResolution (regularEnvelopingTarget k A)) :
    (coefficientResolutionTensorComparison k A M P).hom =
      ((coefficientTensorFunctor k A M).mapHomologicalComplex (ComplexShape.down ℕ)).map
        (envelopingBarResolutionComparison k A P).hom := rfl

omit [SMulCommClass k A M] [SMulCommClass k Aᵐᵒᵖ M] in
/-- Its inverse is the functor image of the native inverse resolution comparison. -/
theorem coefficientResolutionTensorComparison_inv
    (P : ProjectiveResolution (regularEnvelopingTarget k A)) :
    (coefficientResolutionTensorComparison k A M P).inv =
      ((coefficientTensorFunctor k A M).mapHomologicalComplex (ComplexShape.down ℕ)).map
        (envelopingBarResolutionComparison k A P).inv := rfl

/-- The original coefficient Hochschild complex is homotopy equivalent to the tensor of any
projective resolution of the original regular enveloping module. -/
def coefficientHochschildResolutionComparison
    (P : ProjectiveResolution (regularEnvelopingTarget k A)) :
    HomotopyEquiv (ModuleCat.Algebra.Hochschild.chainComplex k A M)
      (coefficientResolutionTensorComplex k A M P) :=
  (HomotopyEquiv.ofIso (coefficientTensorChainIso k A M).symm).trans
    (coefficientResolutionTensorComparison k A M P)

/-- The forward comparison first inserts the original unit outer factors and then applies
the tensor of the augmentation-preserving native bar comparison. -/
theorem coefficientHochschildResolutionComparison_hom
    (P : ProjectiveResolution (regularEnvelopingTarget k A)) :
    (coefficientHochschildResolutionComparison k A M P).hom =
      (coefficientTensorChainIso k A M).inv ≫
        ((coefficientTensorFunctor k A M).mapHomologicalComplex (ComplexShape.down ℕ)).map
          (envelopingBarResolutionComparison k A P).hom := rfl

/-- The inverse comparison uses the native inverse resolution comparison followed by the
original endpoint-sensitive balanced cancellation. -/
theorem coefficientHochschildResolutionComparison_inv
    (P : ProjectiveResolution (regularEnvelopingTarget k A)) :
    (coefficientHochschildResolutionComparison k A M P).inv =
      ((coefficientTensorFunctor k A M).mapHomologicalComplex (ComplexShape.down ℕ)).map
        (envelopingBarResolutionComparison k A P).inv ≫ (coefficientTensorChainIso k A M).hom := rfl

/-- An augmentation-preserving concrete comparison has the same chain homotopy class as
the native comparison after tensoring and inserting the original outer units. -/
def coefficientHochschildResolutionComparisonLiftHomotopy
    (P : ProjectiveResolution (regularEnvelopingTarget k A))
    (f : envelopingBar k A ⟶ P.complex)
    (hf : f ≫ P.π = envelopingBarAugmentationMap k A) :
    Homotopy ((coefficientTensorChainIso k A M).inv ≫
      ((coefficientTensorFunctor k A M).mapHomologicalComplex (ComplexShape.down ℕ)).map f)
      (coefficientHochschildResolutionComparison k A M P).hom :=
  ((coefficientTensorFunctor k A M).mapHomotopy
    (envelopingBarResolutionComparisonLiftHomotopy k A P f hf)).compLeft
      (coefficientTensorChainIso k A M).inv

/-- Homology of the chain homotopy comparison computes Hochschild homology with
the chosen resolution, without any comparison or isomorphism premise. -/
def coefficientHochschildHomologyIsoForResolution
    (P : ProjectiveResolution (regularEnvelopingTarget k A)) (n : ℕ) :
    (ModuleCat.Algebra.Hochschild.chainComplex k A M).homology n ≅
      (coefficientResolutionTensorComplex k A M P).homology n :=
  (coefficientHochschildResolutionComparison k A M P).toHomologyIso n

/-- The computed homology comparison is homology of the original constructed chain map. -/
theorem coefficientHochschildHomologyIsoForResolution_hom
    (P : ProjectiveResolution (regularEnvelopingTarget k A)) (n : ℕ) :
    (coefficientHochschildHomologyIsoForResolution k A M P n).hom =
      HomologicalComplex.homologyMap (coefficientHochschildResolutionComparison k A M P).hom n := rfl

/-- The inverse homology comparison comes from the constructed native inverse chain map. -/
theorem coefficientHochschildHomologyIsoForResolution_inv
    (P : ProjectiveResolution (regularEnvelopingTarget k A)) (n : ℕ) :
    (coefficientHochschildHomologyIsoForResolution k A M P n).inv =
      HomologicalComplex.homologyMap (coefficientHochschildResolutionComparison k A M P).inv n := rfl

omit [SMulCommClass k A M] [SMulCommClass k Aᵐᵒᵖ M] in
/-- Native derived-functor resolution comparison agrees with the tensor of the bar lift. -/
theorem coefficientResolutionTensorComparison_homology
    (P : ProjectiveResolution (regularEnvelopingTarget k A)) (n : ℕ) :
    ((envelopingBarProjectiveResolution k A).isoLeftDerivedObj (coefficientTensorFunctor k A M) n).inv ≫
        (P.isoLeftDerivedObj (coefficientTensorFunctor k A M) n).hom =
      HomologicalComplex.homologyMap (coefficientResolutionTensorComparison k A M P).hom n := by
  have hπ := congrArg (fun f => f.f 0) (envelopingBarResolutionComparison_hom_π k A P)
  have hcomm : (envelopingBarResolutionComparison k A P).hom.f 0 ≫ P.π.f 0 =
      (envelopingBarProjectiveResolution k A).π.f 0 ≫ 𝟙 (regularEnvelopingTarget k A) := by
    simp only [HomologicalComplex.comp_f, Category.comp_id, envelopingBarProjectiveResolution_π] at hπ ⊢
    exact hπ
  have h := ProjectiveResolution.isoLeftDerivedObj_hom_naturality
    (𝟙 (regularEnvelopingTarget k A)) (envelopingBarProjectiveResolution k A) P
    (envelopingBarResolutionComparison k A P).hom hcomm (coefficientTensorFunctor k A M) n
  apply (cancel_epi
    ((envelopingBarProjectiveResolution k A).isoLeftDerivedObj (coefficientTensorFunctor k A M) n).hom).mp
  rw [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
  have hid := ((coefficientTensorFunctor k A M).leftDerived n).map_id (regularEnvelopingTarget k A)
  erw [hid, Category.id_comp] at h
  exact h

/-- The original Hochschild–derived-tensor isomorphism followed by computation with the
chosen resolution is exactly homology of the constructed chain homotopy comparison. -/
theorem coefficientHochschildHomologyIsoForResolution_derived
    (P : ProjectiveResolution (regularEnvelopingTarget k A)) (n : ℕ) :
    (coefficientHochschildHomologyIsoDerived k A M n).hom ≫
        (P.isoLeftDerivedObj (coefficientTensorFunctor k A M) n).hom =
      (coefficientHochschildHomologyIsoForResolution k A M P n).hom := by
  change (HomologicalComplex.homologyMap (coefficientTensorChainIso k A M).inv n ≫
      ((envelopingBarProjectiveResolution k A).isoLeftDerivedObj
        (coefficientTensorFunctor k A M) n).inv) ≫
      (P.isoLeftDerivedObj (coefficientTensorFunctor k A M) n).hom = _
  erw [Category.assoc, coefficientResolutionTensorComparison_homology,
    ← HomologicalComplex.homologyMap_comp]
  rfl

/-- Changing the resolving complex along a map covering its original augmentation
preserves the constructed comparison up to a native chain homotopy. -/
def coefficientHochschildResolutionComparisonNaturalityHomotopy
    (P Q : ProjectiveResolution (regularEnvelopingTarget k A))
    (f : P.complex ⟶ Q.complex) (hf : f ≫ Q.π = P.π) :
    Homotopy ((coefficientHochschildResolutionComparison k A M P).hom ≫
      ((coefficientTensorFunctor k A M).mapHomologicalComplex (ComplexShape.down ℕ)).map f)
      (coefficientHochschildResolutionComparison k A M Q).hom := by
  have h := ProjectiveResolution.liftHomotopy (𝟙 (regularEnvelopingTarget k A))
    (P := envelopingBarProjectiveResolution k A) (Q := Q)
    ((envelopingBarResolutionComparison k A P).hom ≫ f)
    (envelopingBarResolutionComparison k A Q).hom
    (by
        simp only [Functor.map_id, Category.comp_id, envelopingBarProjectiveResolution_π] at ⊢
        have htarget := (ChainComplex.single₀ (ModuleCat.{max u v} (EnvelopingAlgebra k A))).map_id
          (regularEnvelopingTarget k A)
        erw [htarget, Category.comp_id]
        exact (Category.assoc _ _ _).trans
          ((congrArg (fun a => (envelopingBarResolutionComparison k A P).hom ≫ a) hf).trans
            (envelopingBarResolutionComparison_hom_π k A P)))
    (by
        simp only [Functor.map_id, Category.comp_id, envelopingBarProjectiveResolution_π] at ⊢
        have htarget := (ChainComplex.single₀ (ModuleCat.{max u v} (EnvelopingAlgebra k A))).map_id
          (regularEnvelopingTarget k A)
        erw [htarget, Category.comp_id]
        exact envelopingBarResolutionComparison_hom_π k A Q)
  have hmap := ((coefficientTensorFunctor k A M).mapHomotopy h).compLeft (coefficientTensorChainIso k A M).inv
  let F := (coefficientTensorFunctor k A M).mapHomologicalComplex (ComplexShape.down ℕ)
  have hx : ((coefficientTensorChainIso k A M).inv ≫ F.map (envelopingBarResolutionComparison k A P).hom) ≫
      F.map f = (coefficientTensorChainIso k A M).inv ≫ F.map ((envelopingBarResolutionComparison k A P).hom ≫ f) :=
    (Category.assoc _ _ _).trans
      (congrArg (fun g => (coefficientTensorChainIso k A M).inv ≫ g)
        (F.map_comp (envelopingBarResolutionComparison k A P).hom f).symm)
  exact (Homotopy.ofEq hx).trans hmap

/-- Resolution naturality holds for the homology maps, not only for abstract
existence of isomorphic Hochschild and Tor objects. -/
@[reassoc]
theorem coefficientHochschildHomologyIsoForResolution_naturality
    (P Q : ProjectiveResolution (regularEnvelopingTarget k A))
    (f : P.complex ⟶ Q.complex) (hf : f ≫ Q.π = P.π) (n : ℕ) :
    (coefficientHochschildHomologyIsoForResolution k A M P n).hom ≫
      HomologicalComplex.homologyMap
        (((coefficientTensorFunctor k A M).mapHomologicalComplex (ComplexShape.down ℕ)).map f) n =
      (coefficientHochschildHomologyIsoForResolution k A M Q n).hom := by
  erw [coefficientHochschildHomologyIsoForResolution_hom,
    coefficientHochschildHomologyIsoForResolution_hom, ← HomologicalComplex.homologyMap_comp]
  exact (coefficientHochschildResolutionComparisonNaturalityHomotopy k A M P Q f hf).homologyMap_eq n

end ModuleCat.Algebra.Hochschild.AdjacentBar

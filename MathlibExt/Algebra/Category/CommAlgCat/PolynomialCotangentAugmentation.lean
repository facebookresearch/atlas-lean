/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Algebra.Category.CommAlgCat.CotangentSimplicial
public import MathlibExt.AlgebraicTopology.SimplicialObject.AugmentedOver
public import MathlibExt.CategoryTheory.Comonad.BarResolutionAsphericity

/-!
# Polynomial cotangent augmentation and its genuine contraction

The polynomial cotangent simplicial object has its actual augmentation to the
linearization of the source algebra. For a polynomial algebra the variables
construct an algebra section of polynomial evaluation. The existing comonad
right extra degeneracy, its slice lift, linearization and native normalization
then construct a homotopy equivalence of the actual cotangent row with its point.

The input polynomial presentation is an ordinary algebra isomorphism. No
cotangent comparison, exactness or resolution-independence certificate is input.
All commutative rings and polynomial variable sets have the indicated independent
universes. Reference: Stacks Project 92.3 and 92.4.7; Weibel Example 8.6.16.

-/

@[expose] public section

noncomputable section

open CategoryTheory Opposite AlgebraicTopology
open scoped Simplicial

universe u v

namespace CommAlgCat

variable (k : Type u) [CommRing k] (A : CommAlgCat.{max u v} k)

/-- Linearize the actual polynomial augmentation in the slice over `A`. -/
def polynomialCotangentAugmented (P : Over A) :
    SimplicialObject.Augmented (ModuleCat.{max u v} A) :=
  (SimplicialObject.Augmented.whiskeringObj _ _ (cotangentFunctor.{u, v} k A)).obj
    ((polynomialResolution.{u, v} k P.left).overPoint P.hom)

@[simp]
theorem polynomialCotangentAugmented_left (P : Over A) :
    (polynomialCotangentAugmented.{u, v} k A P).left =
      (polynomialCotangentSimplicialFunctor.{u, v} k A).obj P := rfl

@[simp]
theorem polynomialCotangentAugmented_point (P : Over A) :
    (polynomialCotangentAugmented.{u, v} k A P).right = cotangent k A P := rfl

/-- The same actual polynomial augmentation is functorial in the algebra over A. -/
def polynomialCotangentAugmentedFunctor :
    Over A ⥤ SimplicialObject.Augmented (ModuleCat.{max u v} A) where
  obj := polynomialCotangentAugmented.{u, v} k A
  map f := (SimplicialObject.Augmented.whiskeringObj _ _ (cotangentFunctor.{u, v} k A)).map
    (SimplicialObject.Augmented.overPointMap
      (polynomialResolutionMap.{u, v} k f.left) f.w)
  map_id P := by
    let W := SimplicialObject.Augmented.whiskeringObj (Over A) (ModuleCat.{max u v} A)
      (cotangentFunctor.{u, v} k A)
    have h : SimplicialObject.Augmented.overPointMap
        ((polynomialResolutionFunctor.{u, v} k).map (𝟙 P.left)) (by exact Category.id_comp P.hom) =
        𝟙 ((polynomialResolution.{u, v} k P.left).overPoint P.hom) := by
      apply SimplicialObject.Augmented.hom_ext
      · apply NatTrans.ext
        funext i
        apply Over.OverMorphism.ext
        exact congrArg (fun f => f.left.app i)
          ((polynomialResolutionFunctor.{u, v} k).map_id P.left)
      · apply Over.OverMorphism.ext
        rfl
    exact (congrArg W.map h).trans (W.map_id _)
  map_comp {P Q T} f g := by
    let W := SimplicialObject.Augmented.whiskeringObj (Over A) (ModuleCat.{max u v} A)
      (cotangentFunctor.{u, v} k A)
    let pf := polynomialResolutionMap.{u, v} k f.left
    let pg := polynomialResolutionMap.{u, v} k g.left
    have h : SimplicialObject.Augmented.overPointMap
        (polynomialResolutionMap.{u, v} k (f ≫ g).left) (f ≫ g).w =
        SimplicialObject.Augmented.overPointMap pf f.w ≫
          SimplicialObject.Augmented.overPointMap pg g.w := by
      apply SimplicialObject.Augmented.hom_ext
      · apply NatTrans.ext
        funext i
        apply Over.OverMorphism.ext
        exact congrArg (fun f => f.left.app i)
          ((polynomialResolutionFunctor.{u, v} k).map_comp f.left g.left)
      · apply Over.OverMorphism.ext
        rfl
    exact (congrArg W.map h).trans (W.map_comp _ _)

@[simp]
theorem polynomialCotangentAugmentedFunctor_map_left {P Q : Over A} (f : P ⟶ Q) :
    ((polynomialCotangentAugmentedFunctor.{u, v} k A).map f).left =
      (polynomialCotangentSimplicialFunctor.{u, v} k A).map f := rfl

@[simp]
theorem polynomialCotangentAugmentedFunctor_map_right {P Q : Over A} (f : P ⟶ Q) :
    ((polynomialCotangentAugmentedFunctor.{u, v} k A).map f).right = cotangentMap.{u, v} k A f := rfl

/-- The genuine whole polynomial cotangent augmentation is natural. -/
@[reassoc]
theorem polynomialCotangentAugmentation_naturality {P Q : Over A} (f : P ⟶ Q) :
    (polynomialCotangentSimplicialFunctor.{u, v} k A).map f ≫
        (polynomialCotangentAugmented.{u, v} k A Q).hom =
      (polynomialCotangentAugmented.{u, v} k A P).hom ≫
        (SimplicialObject.const (ModuleCat.{max u v} A)).map (cotangentMap.{u, v} k A f) := by
  have h := ((polynomialCotangentAugmentedFunctor.{u, v} k A).map f).w
  change (polynomialCotangentSimplicialFunctor.{u, v} k A).map f ≫
      (polynomialCotangentAugmented.{u, v} k A Q).hom =
    (polynomialCotangentAugmented.{u, v} k A P).hom ≫
      (SimplicialObject.const (ModuleCat.{max u v} A)).map (cotangentMap.{u, v} k A f) at h
  exact h

/-- The augmentation is the actual polynomial evaluation-induced differential map. -/
def polynomialCotangentAugmentationAt (P : Over A) (n : ℕ) :
    ((polynomialCotangentSimplicialFunctor.{u, v} k A).obj P).obj (op ⦋n⦌) ⟶
      cotangent k A P :=
  (polynomialCotangentAugmented.{u, v} k A P).hom.app (op ⦋n⦌)

/-- The augmentation sends every actual differential tensor through the
actual degreewise polynomial evaluation map. -/
theorem polynomialCotangentAugmentationAt_tensor (P : Over A) (n : ℕ)
    (a : A) (p : (polynomialResolution.{u, v} k P.left).left.obj (op ⦋n⦌)) :
    (polynomialCotangentAugmentationAt.{u, v} k A P n).hom
        (cotangentTensor.{u, v} k A (Over.mk
          (((polynomialResolution.{u, v} k P.left).hom.app (op ⦋n⦌)) ≫ P.hom)) a p) =
      cotangentTensor.{u, v} k A P a
        (((polynomialResolution.{u, v} k P.left).hom.app (op ⦋n⦌)).hom p) := by
  let e := (polynomialResolution.{u, v} k P.left).hom.app (op ⦋n⦌)
  let f : Over.mk (e ≫ P.hom) ⟶ P := Over.homMk e rfl
  change (cotangentMap.{u, v} k A f).hom
      (cotangentTensor.{u, v} k A (Over.mk (e ≫ P.hom)) a p) =
    cotangentTensor.{u, v} k A P a (e.hom p)
  exact cotangentMap_tensor.{u, v} k A f a p

/-- The actual normalized augmentation, with the native Moore inclusion. -/
def polynomialCotangentNormalizedAugmentation (P : Over A) :
    (polynomialCotangentChainFunctor k A).obj P ⟶
      (ChainComplex.single₀ (ModuleCat.{max u v} A)).obj (cotangent k A P) :=
  inclusionOfMooreComplexMap ((polynomialCotangentSimplicialFunctor.{u, v} k A).obj P) ≫
    AlternatingFaceMapComplex.ε.app (polynomialCotangentAugmented.{u, v} k A P)

variable {A}

/-- Formal variables give a genuine algebra section of polynomial evaluation. -/
def polynomialCounitSection (σ : Type (max u v)) :
    (free.{u, v} k).obj σ ⟶
      (polynomialComonad.{u, v} k).obj ((free.{u, v} k).obj σ) :=
  (free.{u, v} k).map ((freeForgetAdjunction.{u, v} k).unit.app σ)

@[reassoc]
theorem polynomialCounitSection_counit (σ : Type (max u v)) :
    polynomialCounitSection.{u, v} k σ ≫
      (polynomialComonad.{u, v} k).ε.app ((free.{u, v} k).obj σ) =
      𝟙 ((free.{u, v} k).obj σ) :=
  (freeForgetAdjunction.{u, v} k).left_triangle_components σ

/-- Transport the constructed polynomial section by an actual algebra presentation. -/
def polynomialCounitSectionOfIso (P : CommAlgCat.{max u v} k)
    (σ : Type (max u v)) (e : (free.{u, v} k).obj σ ≅ P) :
    P ⟶ (polynomialComonad.{u, v} k).obj P :=
  e.inv ≫ polynomialCounitSection.{u, v} k σ ≫
    (polynomialComonad.{u, v} k).map e.hom

@[reassoc]
theorem polynomialCounitSectionOfIso_counit (P : CommAlgCat.{max u v} k)
    (σ : Type (max u v)) (e : (free.{u, v} k).obj σ ≅ P) :
    polynomialCounitSectionOfIso.{u, v} k P σ e ≫
      (polynomialComonad.{u, v} k).ε.app P = 𝟙 P := by
  simp only [polynomialCounitSectionOfIso, Category.assoc]
  rw [(polynomialComonad.{u, v} k).ε.naturality e.hom,
    ← Category.assoc (polynomialCounitSection.{u, v} k σ),
    polynomialCounitSection_counit, Category.id_comp, Functor.id_map, Iso.inv_hom_id]

variable (A)

/-- The cotangent contraction is constructed from the polynomial variables,
the native comonad contraction, the slice lift and the actual linearization. -/
def polynomialCotangentRightExtra (P : Over A) (σ : Type (max u v))
    (e : (free.{u, v} k).obj σ ≅ P.left) :
    SimplicialObject.Augmented.RightExtraDegeneracy
      (polynomialCotangentAugmented.{u, v} k A P) :=
  ((Comonad.resolutionRightExtraOfCounitSection (polynomialComonad.{u, v} k) P.left
      (polynomialCounitSectionOfIso.{u, v} k P.left σ e)
      (polynomialCounitSectionOfIso_counit.{u, v} k P.left σ e)).overPoint P.hom).map
    (cotangentFunctor.{u, v} k A)

/-- The genuine polynomial cotangent row is homotopy equivalent to its
linearization point, with the actual normalized augmentation as forward map. -/
def polynomialCotangentAugmentationHomotopyEquiv (P : Over A)
    (σ : Type (max u v)) (e : (free.{u, v} k).obj σ ≅ P.left) :
    HomotopyEquiv ((polynomialCotangentChainFunctor k A).obj P)
      ((ChainComplex.single₀ (ModuleCat.{max u v} A)).obj (cotangent k A P)) :=
  (polynomialCotangentNormalizationHomotopyEquiv.{u, v} k A P).trans
    (polynomialCotangentRightExtra.{u, v} k A P σ e).homotopyEquiv

@[simp]
theorem polynomialCotangentAugmentationHomotopyEquiv_hom (P : Over A)
    (σ : Type (max u v)) (e : (free.{u, v} k).obj σ ≅ P.left) :
    (polynomialCotangentAugmentationHomotopyEquiv k A P σ e).hom =
      polynomialCotangentNormalizedAugmentation.{u, v} k A P := rfl

/-- The actual polynomial cotangent row augmentation is a quasi-isomorphism. -/
theorem polynomialCotangentNormalizedAugmentation_quasiIso (P : Over A)
    (σ : Type (max u v)) (e : (free.{u, v} k).obj σ ≅ P.left) :
    QuasiIso (polynomialCotangentNormalizedAugmentation.{u, v} k A P) :=
  (polynomialCotangentAugmentationHomotopyEquiv k A P σ e).quasiIso_hom

end CommAlgCat

end

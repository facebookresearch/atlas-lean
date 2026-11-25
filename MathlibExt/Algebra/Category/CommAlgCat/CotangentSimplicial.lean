/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Category.CommAlgCat.Cotangent
public import MathlibExt.CategoryTheory.Comma.Over.Diagram
public import MathlibExt.Algebra.Category.CommAlgCat.PolynomialResolution
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.AlgebraicTopology.DoldKan.HomotopyEquivalence

/-!
# Simplicial cotangent modules and normalized chain models

Compose an augmented simplicial commutative algebra diagram in `Over A`
with linearization. Its operators send `a ⊗ dp` to `a ⊗ d(f p)`.
The polynomial comonad provides a canonical augmented diagram; normalized
Moore chains give its cotangent chain model. The Dold–Kan homotopy
equivalence compares it with the alternating face map complex.

References: Stacks Project, Definitions 92.3.1–92.3.2 and Remark 92.3.3;
Loday, *Cyclic Homology*, second edition, Definitions 3.5.3–3.5.4.
-/

@[expose] public section

noncomputable section

open CategoryTheory Opposite AlgebraicTopology
open scoped Simplicial

universe u v

namespace CommAlgCat

variable (k : Type u) [CommRing k] (A : CommAlgCat.{max u v} k)

/-- A simplicial algebra with its actual augmentation to `A` gives a
diagram in `Over A`; linearize that diagram. -/
def cotangentSimplicial
    (P : Over ((SimplicialObject.const (CommAlgCat.{max u v} k)).obj A)) :
    SimplicialObject (ModuleCat.{max u v} A) :=
  Over.lift P.left P.hom ⋙ cotangentFunctor.{u, v} k A

/-- The cotangent simplicial map induced by a map of the actual augmented
simplicial algebras over their fixed target. -/
def cotangentSimplicialMap
    {P Q : Over ((SimplicialObject.const (CommAlgCat.{max u v} k)).obj A)}
    (f : P ⟶ Q) : cotangentSimplicial.{u, v} k A P ⟶ cotangentSimplicial.{u, v} k A Q :=
  Functor.whiskerRight (Over.liftDiagramMap A f) (cotangentFunctor.{u, v} k A)

/-- The induced cotangent map is the identity when the augmented algebra map is. -/
@[simp]
theorem cotangentSimplicialMap_id
    (P : Over ((SimplicialObject.const (CommAlgCat.{max u v} k)).obj A)) :
    cotangentSimplicialMap.{u, v} k A (𝟙 P) = 𝟙 (cotangentSimplicial.{u, v} k A P) := by
  simpa only [cotangentSimplicialMap, Over.liftDiagramMap_id, cotangentSimplicial] using
    Functor.whiskerRight_id' (G := Over.lift P.left P.hom) (cotangentFunctor.{u, v} k A)

/-- The induced cotangent maps compose. -/
theorem cotangentSimplicialMap_comp
    {P Q T : Over ((SimplicialObject.const (CommAlgCat.{max u v} k)).obj A)}
    (f : P ⟶ Q) (g : Q ⟶ T) :
    cotangentSimplicialMap.{u, v} k A (f ≫ g) =
      cotangentSimplicialMap.{u, v} k A f ≫ cotangentSimplicialMap.{u, v} k A g := by
  simp only [cotangentSimplicialMap, Over.liftDiagramMap_comp, Functor.whiskerRight_comp]
  rfl

/-- Linearization of actual augmented simplicial algebras is functorial. -/
def cotangentSimplicialFunctor :
    Over ((SimplicialObject.const (CommAlgCat.{max u v} k)).obj A) ⥤
      SimplicialObject (ModuleCat.{max u v} A) where
  obj := cotangentSimplicial.{u, v} k A
  map := cotangentSimplicialMap.{u, v} k A
  map_id := cotangentSimplicialMap_id.{u, v} k A
  map_comp := cotangentSimplicialMap_comp.{u, v} k A

/-- Every simplicial operator is the actual linearization of its given
algebra map, with the augmentation triangle supplied by naturality. -/
@[simp]
theorem cotangentSimplicial_map_tensor
    (P : Over ((SimplicialObject.const (CommAlgCat.{max u v} k)).obj A))
    {i j : SimplexCategoryᵒᵖ} (θ : i ⟶ j) (a : A) (p : P.left.obj i) :
    ((cotangentSimplicial.{u, v} k A P).map θ).hom
        (cotangentTensor.{u, v} k A (Over.mk (P.hom.app i)) a p) =
      cotangentTensor.{u, v} k A (Over.mk (P.hom.app j)) a ((P.left.map θ).hom p) :=
  cotangentMap_tensor.{u, v} k A ((Over.lift P.left P.hom).map θ) a p

/-- The canonical polynomial object of an algebra over `A`, with its
augmentation composed with the given map into `A`. -/
def polynomialResolutionOverFunctor :
    Over A ⥤ Over ((SimplicialObject.const (CommAlgCat.{max u v} k)).obj A) where
  obj P := Over.mk ((polynomialResolution.{u, v} k P.left).hom ≫
    (SimplicialObject.const (CommAlgCat.{max u v} k)).map P.hom)
  map {P Q} f := Over.homMk (polynomialResolutionMap.{u, v} k f.left).left (by
    let c := SimplicialObject.const (CommAlgCat.{max u v} k)
    let m := polynomialResolutionMap.{u, v} k f.left
    have h := m.w
    change m.left ≫ (polynomialResolution.{u, v} k Q.left).hom =
      (polynomialResolution.{u, v} k P.left).hom ≫ c.map f.left at h
    change m.left ≫ ((polynomialResolution.{u, v} k Q.left).hom ≫ c.map Q.hom) =
      (polynomialResolution.{u, v} k P.left).hom ≫ c.map P.hom
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (fun g => g ≫ c.map Q.hom) h).trans
        ((Category.assoc _ _ _).trans
          ((congrArg (fun g => (polynomialResolution.{u, v} k P.left).hom ≫ g)
            (c.map_comp f.left Q.hom).symm).trans
            (congrArg (fun g => (polynomialResolution.{u, v} k P.left).hom ≫ c.map g) f.w)))))
  map_id P := by
    apply Over.OverMorphism.ext
    exact congrArg (fun f => f.left) ((polynomialResolutionFunctor.{u, v} k).map_id P.left)
  map_comp f g := by
    apply Over.OverMorphism.ext
    exact congrArg (fun f => f.left) ((polynomialResolutionFunctor.{u, v} k).map_comp f.left g.left)

/-- The genuine polynomial cotangent simplicial module, functorial in
the source algebra over the fixed coefficient target. -/
def polynomialCotangentSimplicialFunctor :
    Over A ⥤ SimplicialObject (ModuleCat.{max u v} A) :=
  polynomialResolutionOverFunctor k A ⋙ cotangentSimplicialFunctor.{u, v} k A

/-- The normalized chain model constructed by the native Moore functor. -/
def polynomialCotangentChainFunctor : Over A ⥤ ChainComplex (ModuleCat.{max u v} A) ℕ :=
  polynomialCotangentSimplicialFunctor.{u, v} k A ⋙ normalizedMooreComplex (ModuleCat.{max u v} A)

/-- The alternating chain model with the actual signed sum of face maps. -/
def polynomialCotangentAlternatingFunctor :
    Over A ⥤ ChainComplex (ModuleCat.{max u v} A) ℕ :=
  polynomialCotangentSimplicialFunctor.{u, v} k A ⋙ alternatingFaceMapComplex (ModuleCat.{max u v} A)

/-- Native normalization gives a homotopy equivalence of the two genuine
cotangent chain models. -/
def polynomialCotangentNormalizationHomotopyEquiv (P : Over A) :
    HomotopyEquiv ((polynomialCotangentChainFunctor k A).obj P)
      ((polynomialCotangentAlternatingFunctor k A).obj P) :=
  DoldKan.homotopyEquivNormalizedMooreComplexAlternatingFaceMapComplex
    (Y := (polynomialCotangentSimplicialFunctor.{u, v} k A).obj P)

/-- The canonical normalized chain model of `L_{A/k}`, using the actual
terminal augmented algebra `id_A` and the actual polynomial resolution. -/
def cotangentComplex : ChainComplex (ModuleCat.{max u v} A) ℕ :=
  (polynomialCotangentChainFunctor k A).obj (Over.mk (𝟙 A))

end CommAlgCat

end

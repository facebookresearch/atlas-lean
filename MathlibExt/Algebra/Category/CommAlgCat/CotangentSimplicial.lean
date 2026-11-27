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
# Simplicial cotangent modules and their chain models

Let `k` be a commutative ring, `A` a commutative `k`-algebra, and `P_• → A` an augmented
simplicial commutative algebra. Applying `P → A ↦ A ⊗[P] Ω[P/k]` degreewise gives a simplicial
`A`-module whose operators send `a ⊗ dp` to `a ⊗ d(f(p))`.

The polynomial comonad supplies an augmented simplicial resolution. Its cotangent simplicial
module has a normalized Moore chain complex and an alternating-face complex, with differential
`∑ᵢ (-1)^i dᵢ`. The Dold–Kan comparison gives a chain homotopy equivalence between these
complexes. At the identity augmentation of `A`, the normalized complex is the polynomial model
of `L_{A/k}`.

References: Stacks Project, Section 92.3; Loday, *Cyclic Homology*, second edition,
Definitions 3.5.3–3.5.4.
-/

@[expose] public section

noncomputable section

open CategoryTheory Opposite AlgebraicTopology
open scoped Simplicial

universe u v

namespace CommAlgCat

variable (k : Type u) [CommRing k] (A : CommAlgCat.{max u v} k)

/-- The cotangent module of an augmented simplicial algebra.

For `P_• → A`, this is the simplicial `A`-module with degreewise module `A ⊗[P_n] Ω[P_n/k]`
and operators induced by the algebra operators over `A`. -/
def cotangentSimplicial
    (P : Over ((SimplicialObject.const (CommAlgCat.{max u v} k)).obj A)) :
    SimplicialObject (ModuleCat.{max u v} A) :=
  Over.lift P.left P.hom ⋙ cotangentFunctor.{u, v} k A

/-- The cotangent simplicial map of an augmented algebra map.

A map `P_• → Q_•` commuting with the augmentations to `A` induces the degreewise cotangent
maps, hence a map of simplicial `A`-modules. -/
def cotangentSimplicialMap
    {P Q : Over ((SimplicialObject.const (CommAlgCat.{max u v} k)).obj A)}
    (f : P ⟶ Q) : cotangentSimplicial.{u, v} k A P ⟶ cotangentSimplicial.{u, v} k A Q :=
  Functor.whiskerRight (Over.liftDiagramMap A f) (cotangentFunctor.{u, v} k A)

/-- The cotangent simplicial map of an identity.

The identity of an augmented simplicial algebra induces the identity on its simplicial
cotangent module. -/
@[simp]
theorem cotangentSimplicialMap_id
    (P : Over ((SimplicialObject.const (CommAlgCat.{max u v} k)).obj A)) :
    cotangentSimplicialMap.{u, v} k A (𝟙 P) = 𝟙 (cotangentSimplicial.{u, v} k A P) := by
  simpa only [cotangentSimplicialMap, Over.liftDiagramMap_id, cotangentSimplicial] using
    Functor.whiskerRight_id' (G := Over.lift P.left P.hom) (cotangentFunctor.{u, v} k A)

/-- Composition of cotangent simplicial maps.

The cotangent simplicial map induced by a composite of augmented algebra maps equals the
composite of the induced cotangent simplicial maps. -/
theorem cotangentSimplicialMap_comp
    {P Q T : Over ((SimplicialObject.const (CommAlgCat.{max u v} k)).obj A)}
    (f : P ⟶ Q) (g : Q ⟶ T) :
    cotangentSimplicialMap.{u, v} k A (f ≫ g) =
      cotangentSimplicialMap.{u, v} k A f ≫ cotangentSimplicialMap.{u, v} k A g := by
  simp only [cotangentSimplicialMap, Over.liftDiagramMap_comp, Functor.whiskerRight_comp]
  rfl

/-- The simplicial cotangent functor over a fixed algebra.

For fixed `A`, this functor sends an augmented simplicial commutative `k`-algebra over `A` to
its degreewise extended module of Kähler differentials. -/
def cotangentSimplicialFunctor :
    Over ((SimplicialObject.const (CommAlgCat.{max u v} k)).obj A) ⥤
      SimplicialObject (ModuleCat.{max u v} A) where
  obj := cotangentSimplicial.{u, v} k A
  map := cotangentSimplicialMap.{u, v} k A
  map_id := cotangentSimplicialMap_id.{u, v} k A
  map_comp := cotangentSimplicialMap_comp.{u, v} k A

/-- The differential formula for a simplicial cotangent operator.

For an operator `θ : i → j`, the induced module map sends `a ⊗ dp` in degree `i` to `a ⊗
d(P(θ)(p))` in degree `j`. -/
@[simp]
theorem cotangentSimplicial_map_tensor
    (P : Over ((SimplicialObject.const (CommAlgCat.{max u v} k)).obj A))
    {i j : SimplexCategoryᵒᵖ} (θ : i ⟶ j) (a : A) (p : P.left.obj i) :
    ((cotangentSimplicial.{u, v} k A P).map θ).hom
        (cotangentTensor.{u, v} k A (Over.mk (P.hom.app i)) a p) =
      cotangentTensor.{u, v} k A (Over.mk (P.hom.app j)) a ((P.left.map θ).hom p) :=
  cotangentMap_tensor.{u, v} k A ((Over.lift P.left P.hom).map θ) a p

/-- Polynomial resolutions of algebras over a fixed target.

For `P → A`, take the augmented polynomial resolution of `P` and compose its augmentation with
`P → A`. Maps over `A` induce augmented resolution maps. -/
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

/-- The polynomial cotangent simplicial functor.

For `P → A`, apply the cotangent functor degreewise to the polynomial resolution of `P`
augmented to `A`. -/
def polynomialCotangentSimplicialFunctor :
    Over A ⥤ SimplicialObject (ModuleCat.{max u v} A) :=
  polynomialResolutionOverFunctor k A ⋙ cotangentSimplicialFunctor.{u, v} k A

/-- The normalized polynomial cotangent chain functor.

For `P → A`, this is the normalized Moore chain complex of its polynomial cotangent simplicial
`A`-module, in degrees `ℕ`. -/
def polynomialCotangentChainFunctor : Over A ⥤ ChainComplex (ModuleCat.{max u v} A) ℕ :=
  polynomialCotangentSimplicialFunctor.{u, v} k A ⋙ normalizedMooreComplex (ModuleCat.{max u v} A)

/-- The alternating polynomial cotangent chain functor.

For `P → A`, this is the chain complex of its polynomial cotangent simplicial module with
differential `∑ᵢ (-1)^i dᵢ`. -/
def polynomialCotangentAlternatingFunctor :
    Over A ⥤ ChainComplex (ModuleCat.{max u v} A) ℕ :=
  polynomialCotangentSimplicialFunctor.{u, v} k A ⋙ alternatingFaceMapComplex (ModuleCat.{max u v} A)

/-- The normalization equivalence for polynomial cotangent chains.

For `P → A`, the Dold–Kan comparison is a chain homotopy equivalence from its normalized Moore
cotangent complex to its alternating-face cotangent complex. -/
def polynomialCotangentNormalizationHomotopyEquiv (P : Over A) :
    HomotopyEquiv ((polynomialCotangentChainFunctor k A).obj P)
      ((polynomialCotangentAlternatingFunctor k A).obj P) :=
  DoldKan.homotopyEquivNormalizedMooreComplexAlternatingFaceMapComplex
    (Y := (polynomialCotangentSimplicialFunctor.{u, v} k A).obj P)

/-- The normalized polynomial cotangent complex of an algebra.

For a commutative `k`-algebra `A`, this is the normalized cotangent chain complex of the
polynomial resolution at the identity augmentation `A → A`. -/
def cotangentComplex : ChainComplex (ModuleCat.{max u v} A) ℕ :=
  (polynomialCotangentChainFunctor k A).obj (Over.mk (𝟙 A))

end CommAlgCat

end

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialObject.RightExtraDegeneracyPrism
public import MathlibExt.AlgebraicTopology.SimplicialObject.NormalizedChainHomotopy
public import MathlibExt.Algebra.Category.CommAlgCat.CotangentWeightZero
public import MathlibExt.Algebra.Category.CommAlgCat.PolynomialCotangentComparison

/-!
# Polynomial resolution contractions and cotangent prisms

A polynomial presentation of a commutative `k`-algebra `A` gives a section of the
polynomial counit. It determines a right extra degeneracy on the canonical augmented
polynomial resolution, a simplicial section of its augmentation, and a homotopy from
the identity to augmentation followed by that section.

Applying the cotangent functor yields cotangent prism operators and their tensor
coordinates. Normalization gives a chain homotopy and a homotopy equivalence with the
normalized constant cotangent-module diagram. The polynomial variable carrier has
height `max u v`, with ground-ring and algebra-carrier universes independent.

For polynomial comparison homotopies, see Loday, §3.5.2, and the Stacks Project's
discussion of simplicial homotopies.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicTopology
open scoped Simplicial TensorProduct

universe u v

namespace CommAlgCat

variable (k : Type u) [CommRing k] (σ : Type (max u v))
  (A : CommAlgCat.{max u v} k) (e : A ≅ (free.{u, v} k).obj σ)

/--
The right extra degeneracy on the augmented polynomial resolution of `A` determined
by its polynomial presentation and the induced section of the polynomial counit.
-/
def polynomialResolutionRightExtraOfPresentation :
    SimplicialObject.Augmented.RightExtraDegeneracy (polynomialResolution.{u, v} k A) :=
  Comonad.resolutionRightExtraOfCounitSection (polynomialComonad.{u, v} k) A
    (polynomialCounitSectionOfIso.{u, v} k A σ e.symm)
    (polynomialCounitSectionOfIso_counit.{u, v} k A σ e.symm)

/--
The simplicial section `const A → polynomialResolution(A)` determined by the
presentation-induced right extra degeneracy.
-/
def polynomialResolutionSectionOfPresentation :
    (SimplicialObject.const (CommAlgCat.{max u v} k)).obj A ⟶
      (polynomialResolution.{u, v} k A).left :=
  SimplicialObject.Augmented.RightExtraDegeneracy.section_
    (polynomialResolutionRightExtraOfPresentation.{u, v} k σ A e)

/--
The presentation-induced simplicial section followed by the polynomial resolution
augmentation is the identity on the constant diagram on `A`.
-/
@[reassoc (attr := simp)]
theorem polynomialResolutionSectionOfPresentation_augmentation :
    polynomialResolutionSectionOfPresentation.{u, v} k σ A e ≫
      (polynomialResolution.{u, v} k A).hom = 𝟙 _ :=
  SimplicialObject.Augmented.RightExtraDegeneracy.section_comp_augmentation
    (polynomialResolutionRightExtraOfPresentation.{u, v} k σ A e)

/--
The simplicial homotopy from the identity of the polynomial resolution to its
augmentation followed by the presentation-induced section.
-/
def polynomialResolutionPrismOfPresentation :
    SimplicialObject.Homotopy (𝟙 (polynomialResolution.{u, v} k A).left)
      ((polynomialResolution.{u, v} k A).hom ≫
        polynomialResolutionSectionOfPresentation.{u, v} k σ A e) :=
  SimplicialObject.Augmented.RightExtraDegeneracy.prism
    (polynomialResolutionRightExtraOfPresentation.{u, v} k σ A e)

/--
The simplicial homotopy from the identity of the canonical cotangent diagram to its
cotangent augmentation followed by the section induced by the polynomial presentation.
-/
def polynomialCotangentPrismOfPresentation :
    SimplicialObject.Homotopy
      (𝟙 (polynomialCotangentSimplicialFunctor.{u, v} k A).obj (Over.mk (𝟙 A)))
      ((polynomialCotangentAugmented.{u, v} k A (Over.mk (𝟙 A))).hom ≫
        (polynomialCotangentRightExtra.{u, v} k A (Over.mk (𝟙 A)) σ e.symm).section_) :=
  SimplicialObject.Augmented.RightExtraDegeneracy.prism
    (polynomialCotangentRightExtra.{u, v} k A (Over.mk (𝟙 A)) σ e.symm)

/--
The degree-`n` prism operator sends `a ⊗ d p` to `a ⊗ d h_i(p)`, where `h_i` is
the corresponding algebra prism over the augmentation target; the coefficient `a` is
unchanged.
-/
theorem polynomialCotangentPrism_tensor {n : ℕ} (i : Fin (n + 1)) (a : A)
    (p : (polynomialResolution.{u, v} k A).left.obj (op ⦋n⦌)) :
    ((polynomialCotangentPrismOfPresentation.{u, v} k σ A e).h i).hom
      (cotangentTensor.{u, v} k A (Over.mk (((polynomialResolution.{u, v} k A).hom.app (op ⦋n⦌)) ≫ 𝟙 A)) a p) =
    cotangentTensor.{u, v} k A (Over.mk (((polynomialResolution.{u, v} k A).hom.app (op ⦋n + 1⦌)) ≫ 𝟙 A)) a
      (((((polynomialResolutionRightExtraOfPresentation.{u, v} k σ A e).overPoint (𝟙 A)).prism.h i).left).hom p) := by
  let R := (polynomialResolutionRightExtraOfPresentation.{u, v} k σ A e).overPoint (𝟙 A)
  let F := cotangentFunctor.{u, v} k A
  have h := SimplicialObject.Augmented.RightExtraDegeneracy.prism_map_h R F i
  have hT := cotangentMap_tensor.{u, v} k A (R.prism.h i) a p
  exact (congrArg (fun f => f.hom (cotangentTensor.{u, v} k A
    (Over.mk ((polynomialResolution.{u, v} k A).hom.app (op ⦋n⦌) ≫ 𝟙 A)) a p)) h).trans hT

/--
The chain homotopy from the identity of the cotangent complex to the composite of
the normalized cotangent augmentation and its presentation-induced section.
-/
def polynomialCotangentPrismChainHomotopy :
    _root_.Homotopy (𝟙 (cotangentComplex k A))
      ((normalizedMooreComplex (ModuleCat.{max u v} A)).map
        (polynomialCotangentAugmented.{u, v} k A (Over.mk (𝟙 A))).hom ≫
       (normalizedMooreComplex (ModuleCat.{max u v} A)).map
        (polynomialCotangentRightExtra.{u, v} k A (Over.mk (𝟙 A)) σ e.symm).section_) := by
  let N := normalizedMooreComplex (ModuleCat.{max u v} A)
  let P := polynomialCotangentAugmented.{u, v} k A (Over.mk (𝟙 A))
  let R := polynomialCotangentRightExtra.{u, v} k A (Over.mk (𝟙 A)) σ e.symm
  let h := SimplicialObject.Homotopy.toNormalizedChainHomotopy
    (polynomialCotangentPrismOfPresentation.{u, v} k σ A e)
  exact (_root_.Homotopy.ofEq (N.map_id P.left).symm).trans
    (h.trans (_root_.Homotopy.ofEq (N.map_comp P.hom R.section_)))

/--
The chain homotopy equivalence between the canonical cotangent complex and the
normalization of the constant diagram on the cotangent module of the polynomial
algebra `A`.
-/
def polynomialCotangentPrismConstantHomotopyEquiv :
    HomotopyEquiv (cotangentComplex k A)
      ((normalizedMooreComplex (ModuleCat.{max u v} A)).obj
        ((SimplicialObject.const (ModuleCat.{max u v} A)).obj
          (cotangent.{u, v} k A (Over.mk (𝟙 A))))) where
  hom := (normalizedMooreComplex (ModuleCat.{max u v} A)).map
    (polynomialCotangentAugmented.{u, v} k A (Over.mk (𝟙 A))).hom
  inv := (normalizedMooreComplex (ModuleCat.{max u v} A)).map
    (polynomialCotangentRightExtra.{u, v} k A (Over.mk (𝟙 A)) σ e.symm).section_
  homotopyHomInvId := (polynomialCotangentPrismChainHomotopy k σ A e).symm
  homotopyInvHomId := _root_.Homotopy.ofEq (by
    let N := normalizedMooreComplex (ModuleCat.{max u v} A)
    let R := polynomialCotangentRightExtra.{u, v} k A (Over.mk (𝟙 A)) σ e.symm
    have h := R.section_comp_augmentation
    exact (N.map_comp R.section_ (polynomialCotangentAugmented.{u, v} k A (Over.mk (𝟙 A))).hom).symm.trans
      ((congrArg N.map h).trans (N.map_id _)))

/--
The forward map of the constant-diagram comparison, followed by the standard
constant normalization map, is the polynomial cotangent normalized augmentation.
-/
theorem polynomialCotangentPrismConstantHomotopyEquiv_augmentation :
    (polynomialCotangentPrismConstantHomotopyEquiv k σ A e).hom ≫
      (cotangentWeightZeroCoefficientHomotopyEquiv k A (cotangent.{u, v} k A (Over.mk (𝟙 A)))).hom =
        polynomialCotangentNormalizedAugmentation k A (Over.mk (𝟙 A)) :=
  by
    let P := polynomialCotangentAugmented.{u, v} k A (Over.mk (𝟙 A))
    change (normalizedMooreComplex (ModuleCat.{max u v} A)).map P.hom ≫
      (inclusionOfMooreComplexMap ((SimplicialObject.const (ModuleCat.{max u v} A)).obj P.right) ≫
        AlternatingFaceMapComplex.ε.app
          ((SimplicialObject.Augmented.const (C := ModuleCat.{max u v} A)).obj P.right)) =
      inclusionOfMooreComplexMap P.left ≫ AlternatingFaceMapComplex.ε.app P
    exact SimplicialObject.normalized_augmentation_to_constant P

end CommAlgCat

end

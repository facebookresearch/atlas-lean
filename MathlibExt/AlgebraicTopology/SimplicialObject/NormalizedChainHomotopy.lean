/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.AlgebraicTopology.SimplicialObject.ChainHomotopy
public import Mathlib.AlgebraicTopology.DoldKan.HomotopyEquivalence

/-!
# Simplicial homotopies on normalized Moore complexes

Let C be an abelian category, X and Y simplicial objects, and f,g : X ⟶ Y. Write A for the
alternating face-map complex and N for the normalized Moore complex. The Moore inclusion i_X :
N(X) → A(X) and normalization projection p_Y : A(Y) → N(Y) satisfy N(f) = i_X ≫ A(f) ≫ p_Y.

A simplicial homotopy H from f to g induces an alternating chain homotopy whose degree n
component is −Σᵢ₌₀ⁿ (−1)ⁱHᵢ. Composing it with i_X and p_Y gives a chain homotopy from N(f) to
N(g), so their homology maps agree in every natural degree. The construction also identifies
the normalized augmentation with the augmentation of the alternating complex after Moore
inclusion.

The alternating homotopy and the normalization maps are those of
Mathlib.AlgebraicTopology.SimplicialObject.ChainHomotopy and
Mathlib.AlgebraicTopology.DoldKan.HomotopyEquivalence.
-/

@[expose] public section

noncomputable section

open CategoryTheory AlgebraicTopology
open scoped Simplicial

universe u v

namespace CategoryTheory.SimplicialObject

variable {C : Type u} [Category.{v} C] [Abelian C]
  {X Y : SimplicialObject C}

/-- Factorization of the normalized simplicial map.

Let C be abelian and f : X ⟶ Y a simplicial morphism. Its normalized Moore chain map is (i_X ≫
A(f)) ≫ p_Y, where i_X includes N(X) in the alternating face-map complex A(X) and p_Y projects
A(Y) onto N(Y). -/
theorem inclusion_alternating_projection (f : X ⟶ Y) :
    (inclusionOfMooreComplexMap X ≫ (alternatingFaceMapComplex C).map f) ≫
      DoldKan.PInftyToNormalizedMooreComplex Y = (normalizedMooreComplex C).map f := by
  have h := (inclusionOfMooreComplex C).naturality f
  dsimp only [inclusionOfMooreComplex] at h
  have hid : inclusionOfMooreComplexMap Y ≫ DoldKan.PInftyToNormalizedMooreComplex Y =
      𝟙 ((normalizedMooreComplex C).obj Y) :=
    (DoldKan.splitMonoInclusionOfMooreComplexMap Y).id
  exact (congrArg (fun m => m ≫ DoldKan.PInftyToNormalizedMooreComplex Y) h.symm).trans
    ((Category.assoc _ _ _).trans
      ((congrArg (fun m => (normalizedMooreComplex C).map f ≫ m) hid).trans
        (Category.comp_id _)))

/-- Normalization of an augmented simplicial object.

Let X be an augmented simplicial object in an abelian category, with augmentation a : X.left →
const(X.right). Apply normalization to a, then Moore inclusion and the alternating
augmentation of const(X.right). The resulting map to the chain complex concentrated in degree
zero at X.right is i_X ≫ ε_X, the Moore inclusion followed by the alternating augmentation of
X itself. -/
@[reassoc]
theorem normalized_augmentation_to_constant (X : SimplicialObject.Augmented C) :
    (normalizedMooreComplex C).map X.hom ≫
      (inclusionOfMooreComplexMap ((SimplicialObject.const C).obj X.right) ≫
        AlternatingFaceMapComplex.ε.app ((SimplicialObject.Augmented.const (C := C)).obj X.right)) =
      inclusionOfMooreComplexMap X.left ≫ AlternatingFaceMapComplex.ε.app X := by
  let q : X ⟶ (SimplicialObject.Augmented.const (C := C)).obj X.right :=
    { left := X.hom
      right := 𝟙 X.right
      w := by
        dsimp only [SimplicialObject.Augmented.const]
        change X.hom ≫ 𝟙 ((SimplicialObject.const C).obj X.right) =
          X.hom ≫ (SimplicialObject.const C).map (𝟙 X.right)
        exact congrArg (fun f => X.hom ≫ f) ((SimplicialObject.const C).map_id X.right).symm }
  have hε := AlternatingFaceMapComplex.ε.naturality q
  change (alternatingFaceMapComplex C).map X.hom ≫
      AlternatingFaceMapComplex.ε.app ((SimplicialObject.Augmented.const (C := C)).obj X.right) =
    AlternatingFaceMapComplex.ε.app X ≫ (ChainComplex.single₀ C).map (𝟙 X.right) at hε
  have hid := (ChainComplex.single₀ C).map_id X.right
  have hε' := hε.trans
    ((congrArg (fun f => AlternatingFaceMapComplex.ε.app X ≫ f) hid).trans
      (Category.comp_id _))
  have h := (inclusionOfMooreComplex C).naturality X.hom
  dsimp only [inclusionOfMooreComplex] at h
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun m => m ≫ AlternatingFaceMapComplex.ε.app
      ((SimplicialObject.Augmented.const (C := C)).obj X.right)) h).trans
      ((Category.assoc _ _ _).trans
        (congrArg (fun m => inclusionOfMooreComplexMap X.left ≫ m) hε')))

namespace Homotopy

variable {f g : X ⟶ Y}

/-- Normalized chain homotopy from a simplicial prism.

Let C be abelian and H a simplicial homotopy from f : X ⟶ Y to g. Its alternating chain
homotopy is composed on the left with the Moore inclusion i_X and on the right with the
normalization projection p_Y. The factorization N(f) = i_X ≫ A(f) ≫ p_Y and its analogue for g
identify the endpoints with the normalized maps. The signed component before normalization is
−Σᵢ₌₀ⁿ (−1)ⁱHᵢ in degree n to n+1. -/
def toNormalizedChainHomotopy (H : SimplicialObject.Homotopy f g) :
    _root_.Homotopy ((normalizedMooreComplex C).map f)
      ((normalizedMooreComplex C).map g) :=
  (_root_.Homotopy.ofEq (inclusion_alternating_projection f).symm).trans
    (((H.toChainHomotopy.compLeft (inclusionOfMooreComplexMap X)).compRight
      (DoldKan.PInftyToNormalizedMooreComplex Y)).trans
        (_root_.Homotopy.ofEq (inclusion_alternating_projection g)))

/-- Equality of normalized homology maps under simplicial homotopy.

For simplicial morphisms f,g : X ⟶ Y in an abelian category and a simplicial homotopy H from f
to g, their normalized Moore maps induce equal maps on homology in every natural degree n. The
equality follows from the normalized chain homotopy obtained by composing the alternating
prism with the Moore inclusion and projection. -/
theorem normalized_homologyMap_eq (H : SimplicialObject.Homotopy f g) (n : ℕ) :
    HomologicalComplex.homologyMap ((normalizedMooreComplex C).map f) n =
      HomologicalComplex.homologyMap ((normalizedMooreComplex C).map g) n :=
  H.toNormalizedChainHomotopy.homologyMap_eq n

end Homotopy

end CategoryTheory.SimplicialObject

end

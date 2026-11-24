/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Homology.Hochschild.ProperShuffleAugmentedAlgebra
public import MathlibExt.Algebra.Homology.Hochschild.PolynomialProperShuffleAcyclicity
public import MathlibExt.CategoryTheory.Comma.Over.Diagram

/-!
# Polynomial columns of the cotangent comparison

For polynomial algebras over a rational ground ring
augmented into a coefficient algebra, the proper
quotient cotangent augmentations are columnwise
quasi-isomorphisms. Their quotient and coefficient
cotangent complexes form simplicial diagrams, and the
augmentations commute with every simplicial operator.
-/

@[expose] public section
noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct Simplicial

universe u v w

namespace ModuleCat.Algebra.Hochschild.Symmetric.RationalProperShuffle.AugmentedAlgebra

variable (k : Type u) [CommRing k] [Algebra ℚ k] (B : CommAlgCat.{max u v} k)
  (M : Type w) [AddCommGroup M] [Module k M] [Module B M]
  [SMulCommClass k B M] [IsScalarTower k B M]

/-- The simplicial shifted proper-shuffle diagram of an original augmented algebra diagram. -/
def simplicialDiagram
    (P : Over ((SimplicialObject.const (CommAlgCat.{max u v} k)).obj B)) :
    SimplicialObject (ChainComplex (ModuleCat.{max u v w} k) ℕ) :=
  Over.lift P.left P.hom ⋙ functor k B M

/-- The original coefficient cotangents of those same augmented algebra levels. -/
def simplicialCotangentDiagram
    (P : Over ((SimplicialObject.const (CommAlgCat.{max u v} k)).obj B)) : SimplicialObject (ModuleCat.{max u v w} k) :=
  Over.lift P.left P.hom ⋙ cotangentFunctor k B M

/-- Every original simplicial operator preserves the all-degree cotangent chain augmentation. -/
def simplicialAugmentation
    (P : Over ((SimplicialObject.const (CommAlgCat.{max u v} k)).obj B)) :
    simplicialDiagram k B M P ⟶ simplicialCotangentDiagram k B M P ⋙ ChainComplex.single₀ (ModuleCat.{max u v w} k) :=
  Functor.whiskerLeft (Over.lift P.left P.hom) (augmentationNat k B M)

/-- The simplicial comparison uses the original cotangent augmentation of the level. -/
theorem simplicialAugmentation_app
    (P : Over ((SimplicialObject.const (CommAlgCat.{max u v} k)).obj B)) (i : SimplexCategoryᵒᵖ) :
    @Eq ((simplicialDiagram k B M P).obj i ⟶
      ((simplicialCotangentDiagram k B M P) ⋙ ChainComplex.single₀ (ModuleCat.{max u v w} k)).obj i)
      ((simplicialAugmentation k B M P).app i)
      ((augmentationNat k B M).app ((Over.lift P.left P.hom).obj i)) := rfl

/-- A literal polynomial algebra over k, augmented into B, has the cotangent augmentation
quasi-isomorphism. -/
instance polynomialAugmentation_quasiIso (σ : Type (max u v))
    (g : CommAlgCat.of k (MvPolynomial σ k) ⟶ B) :
    _root_.QuasiIso ((augmentationNat k B M).app (Over.mk g)) := by
  let _ : Module (MvPolynomial σ k) M := coefficientModule k B M (Over.mk g)
  let _ : SMulCommClass k (MvPolynomial σ k) M := coefficientCommutes k B M (Over.mk g)
  let _ : IsScalarTower k (MvPolynomial σ k) M := coefficientTower k B M (Over.mk g)
  change _root_.QuasiIso (properShuffleCotangentMap k (MvPolynomial σ k) M)
  exact ModuleCat.Algebra.Hochschild.PolynomialDiagonal.polynomialProperShuffleCotangentMap_quasiIso k σ M

/-- An original polynomial presentation earns the same column quasi-isomorphism
by native isomorphism transport. -/
theorem augmentation_quasiIso_of_polynomialPresentation (P : Over B) (σ : Type (max u v))
    (e : P.left ≅ CommAlgCat.of k (MvPolynomial σ k)) :
    _root_.QuasiIso ((augmentationNat k B M).app P) := by
  let Q : Over B := Over.mk (e.inv ≫ P.hom)
  let eOver : P ≅ Q := Over.isoMk e (by
    change e.hom ≫ (e.inv ≫ P.hom) = P.hom
    exact e.hom_inv_id_assoc P.hom)
  let F := functor k B M
  let G := cotangentFunctor k B M ⋙ ChainComplex.single₀ (ModuleCat.{max u v w} k)
  let α := augmentationNat k B M
  let eF := F.mapIso eOver
  let eG := G.mapIso eOver
  have hnat : eF.hom ≫ α.app Q = α.app P ≫ eG.hom := α.naturality eOver.hom
  have h : α.app P = eF.hom ≫ α.app Q ≫ eG.inv := by
    have h' := congrArg (fun t => t ≫ eG.inv) hnat
    simpa only [Category.assoc, Iso.hom_inv_id, Category.comp_id] using h'.symm
  let _ : _root_.QuasiIso (α.app Q) := polynomialAugmentation_quasiIso k B M σ (e.inv ≫ P.hom)
  change _root_.QuasiIso (α.app P)
  rw [h]
  infer_instance

/-- Every polynomial-presented level of an original simplicial algebra diagram has the comparison. -/
theorem simplicialAugmentation_app_quasiIso_of_polynomialPresentation
    (P : Over ((SimplicialObject.const (CommAlgCat.{max u v} k)).obj B))
    (i : SimplexCategoryᵒᵖ) (σ : Type (max u v))
    (e : P.left.obj i ≅ CommAlgCat.of k (MvPolynomial σ k)) :
    _root_.QuasiIso ((simplicialAugmentation k B M P).app i) :=
  augmentation_quasiIso_of_polynomialPresentation k B M ((Over.lift P.left P.hom).obj i) σ e

end ModuleCat.Algebra.Hochschild.Symmetric.RationalProperShuffle.AugmentedAlgebra

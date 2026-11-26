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
# Polynomial columns of the proper-shuffle cotangent comparison

Let k be a commutative ℚ-algebra, B a commutative k-algebra, and M a B-module whose B-action
commutes with its k-action. An augmented simplicial k-algebra P → B gives a simplicial diagram
of proper-shuffle cotangent complexes and the diagram M ⊗[Pₚ] Ω¹(Pₚ/k). The cotangent
augmentation sends the class of m ⊗ a to m ⊗ da in shifted degree zero. In a polynomial column
this augmentation is a quasi-isomorphism, for arbitrary sets of polynomial generators.

For the proper both-positive shuffle relations and rational Harrison/cotangent comparison, see
J.-L. Loday, Cyclic Homology, 2nd ed., §4.5.
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

/-- The simplicial diagram of proper-shuffle cotangent columns.

For a commutative ℚ-algebra k, an augmented simplicial commutative k-algebra P → B, and a
compatible B-module M, its pth column is the proper-shuffle cotangent complex of Pₚ with
coefficients M. Cotangent degree q uses Hochschild degree q+1; both shuffle input degrees are
positive. -/
def simplicialDiagram
    (P : Over ((SimplicialObject.const (CommAlgCat.{max u v} k)).obj B)) :
    SimplicialObject (ChainComplex (ModuleCat.{max u v w} k) ℕ) :=
  Over.lift P.left P.hom ⋙ functor k B M

/-- The simplicial diagram of coefficient differential modules.

For a commutative ℚ-algebra k, an augmentation P → B and a compatible B-module M, the pth
object is the coefficient cotangent module M ⊗[Pₚ] Ω¹(Pₚ/k), with the maps induced by the
simplicial algebra maps over B. -/
def simplicialCotangentDiagram
    (P : Over ((SimplicialObject.const (CommAlgCat.{max u v} k)).obj B)) : SimplicialObject (ModuleCat.{max u v w} k) :=
  Over.lift P.left P.hom ⋙ cotangentFunctor k B M

/-- The columnwise proper-shuffle cotangent augmentation.

For a commutative ℚ-algebra k, P → B and a compatible B-module M, these chain maps assemble
naturally over all simplicial operators. In shifted degree zero they send [m ⊗ a] to m ⊗ da;
the target column is the coefficient cotangent module concentrated in degree zero. -/
def simplicialAugmentation
    (P : Over ((SimplicialObject.const (CommAlgCat.{max u v} k)).obj B)) :
    simplicialDiagram k B M P ⟶ simplicialCotangentDiagram k B M P ⋙ ChainComplex.single₀ (ModuleCat.{max u v w} k) :=
  Functor.whiskerLeft (Over.lift P.left P.hom) (augmentationNat k B M)

/-- The component of the simplicial cotangent augmentation.

For a commutative ℚ-algebra k, P → B and a compatible B-module M, the component at i ∈ Δᵒᵖ is
augmentationNat on the augmented algebra Pᵢ → B. The source remains its proper-shuffle
cotangent complex. -/
theorem simplicialAugmentation_app
    (P : Over ((SimplicialObject.const (CommAlgCat.{max u v} k)).obj B)) (i : SimplexCategoryᵒᵖ) :
    @Eq ((simplicialDiagram k B M P).obj i ⟶
      ((simplicialCotangentDiagram k B M P) ⋙ ChainComplex.single₀ (ModuleCat.{max u v w} k)).obj i)
      ((simplicialAugmentation k B M P).app i)
      ((augmentationNat k B M).app ((Over.lift P.left P.hom).obj i)) := rfl

/-- The proper-shuffle augmentation of an augmented polynomial algebra is a quasi-isomorphism.

For a commutative ℚ-algebra k, a compatible B-module M and a k-algebra map k[σ] → B,
augmentationNat induces isomorphisms on all homology groups. The set σ may be infinite. -/
instance polynomialAugmentation_quasiIso (σ : Type (max u v))
    (g : CommAlgCat.of k (MvPolynomial σ k) ⟶ B) :
    _root_.QuasiIso ((augmentationNat k B M).app (Over.mk g)) := by
  let _ : Module (MvPolynomial σ k) M := coefficientModule k B M (Over.mk g)
  let _ : SMulCommClass k (MvPolynomial σ k) M := coefficientCommutes k B M (Over.mk g)
  let _ : IsScalarTower k (MvPolynomial σ k) M := coefficientTower k B M (Over.mk g)
  change _root_.QuasiIso (properShuffleCotangentMap k (MvPolynomial σ k) M)
  exact ModuleCat.Algebra.Hochschild.PolynomialDiagonal.polynomialProperShuffleCotangentMap_quasiIso k σ M

/-- A polynomial presentation gives a cotangent-column quasi-isomorphism.

For a commutative ℚ-algebra k, a compatible B-module M and an augmented algebra A → B, an
algebra isomorphism A ≅ k[σ] implies that its proper-shuffle cotangent augmentation is a
quasi-isomorphism. -/
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

/-- A polynomial presentation of one simplicial column gives its augmentation quasi-isomorphism.

For a commutative ℚ-algebra k, P → B and a compatible B-module M, if Pᵢ ≅ k[σ] as k-algebras,
then the component of simplicialAugmentation at i is a quasi-isomorphism. -/
theorem simplicialAugmentation_app_quasiIso_of_polynomialPresentation
    (P : Over ((SimplicialObject.const (CommAlgCat.{max u v} k)).obj B))
    (i : SimplexCategoryᵒᵖ) (σ : Type (max u v))
    (e : P.left.obj i ≅ CommAlgCat.of k (MvPolynomial σ k)) :
    _root_.QuasiIso ((simplicialAugmentation k B M P).app i) :=
  augmentation_quasiIso_of_polynomialPresentation k B M ((Over.lift P.left P.hom).obj i) σ e

end ModuleCat.Algebra.Hochschild.Symmetric.RationalProperShuffle.AugmentedAlgebra

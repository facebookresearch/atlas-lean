/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Homology.Hochschild.ProperShuffleAugmentedAlgebra
public import MathlibExt.CategoryTheory.Comma.Over.Diagram

/-!
# Augmented-algebra Hochschild diagrams with coefficients

A B-module M becomes a coefficient module for each algebra
P augmented into B. Coefficient-first tensor maps form a
Hochschild chain functor, and the augmentation fixes M
while acting on the algebra tails.
-/

@[expose] public section
noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct Simplicial

universe u v w

namespace ModuleCat.Algebra.Hochschild.Symmetric.AugmentedCoefficients

open RationalProperShuffle.AugmentedAlgebra

attribute [local instance] coefficientModule coefficientCommutes coefficientTower

variable (k : Type u) [CommRing k] [Algebra ℚ k] (B : CommAlgCat.{max u v} k)
  (M : Type w) [AddCommGroup M] [Module k M] [Module B M]
  [SMulCommClass k B M] [IsScalarTower k B M]

/-- The original Hochschild complex with the original coefficient acted on by the augmentation. -/
def complex (P : Over B) : ChainComplex (ModuleCat.{max u v w} k) ℕ := chainComplex k P.left M

/-- The original algebra map acts on the tails and fixes the original coefficient head. -/
def map {P Q : Over B} (f : P ⟶ Q) : complex k B M P ⟶ complex k B M Q :=
  originalAlgebraCoefficientChainMap k f.left.hom (LinearMap.id : M →ₗ[k] M)
    (coefficientCompatibility k B M f)

/-- The original coefficient/algebra Hochschild functor for arbitrary M. -/
def functor : Over B ⥤ ChainComplex (ModuleCat.{max u v w} k) ℕ where
  obj := complex k B M
  map := map k B M
  map_id P := by
    apply HomologicalComplex.hom_ext
    intro q
    apply ModuleCat.hom_ext
    change ((originalAlgebraCoefficientChainMap k (AlgHom.id k P.left)
      (LinearMap.id : M →ₗ[k] M) (coefficientCompatibility k B M (𝟙 P))).f q).hom = LinearMap.id
    rw [originalAlgebraCoefficientChainMap_f]
    change ModuleCat.Algebra.Hochschild.linearMap (NonUnitalAlgHom.id k P.left)
      (LinearMap.id : M →ₗ[k] M) q = LinearMap.id
    exact ModuleCat.Algebra.Hochschild.linearMap_id q
  map_comp {P Q S} f g := by
    apply HomologicalComplex.hom_ext
    intro q
    apply ModuleCat.hom_ext
    change ((originalAlgebraCoefficientChainMap k (g.left.hom.comp f.left.hom)
        (LinearMap.id : M →ₗ[k] M) (coefficientCompatibility k B M (f ≫ g))).f q).hom =
      ((originalAlgebraCoefficientChainMap k g.left.hom (LinearMap.id : M →ₗ[k] M)
        (coefficientCompatibility k B M g)).f q).hom.comp
          ((originalAlgebraCoefficientChainMap k f.left.hom (LinearMap.id : M →ₗ[k] M)
            (coefficientCompatibility k B M f)).f q).hom
    rw [originalAlgebraCoefficientChainMap_f, originalAlgebraCoefficientChainMap_f,
      originalAlgebraCoefficientChainMap_f]
    change ModuleCat.Algebra.Hochschild.linearMap (g.left.hom.comp f.left.hom).toNonUnitalAlgHom
        (LinearMap.id : M →ₗ[k] M) q =
      (ModuleCat.Algebra.Hochschild.linearMap g.left.hom.toNonUnitalAlgHom (LinearMap.id : M →ₗ[k] M) q).comp
        (ModuleCat.Algebra.Hochschild.linearMap f.left.hom.toNonUnitalAlgHom (LinearMap.id : M →ₗ[k] M) q)
    apply ModuleCat.Algebra.Hochschild.tensorPower_ext
    intro m a
    simp only [LinearMap.comp_apply, ModuleCat.Algebra.Hochschild.linearMap_tprod,
      LinearMap.id_apply]
    rfl

omit [Algebra ℚ k] in
/-- Every morphism retains its literal original coefficient-first tensor formula. -/
theorem map_tprod {P Q : Over B} (f : P ⟶ Q) (q : ℕ) (m : M) (a : Fin q → P.left) :
    ((map k B M f).f q).hom (m ⊗ₜ[k] PiTensorProduct.tprod k a) =
      m ⊗ₜ[k] PiTensorProduct.tprod k (fun j => f.left.hom (a j)) :=
  originalAlgebraCoefficientChainMap_tprod k f.left.hom (LinearMap.id : M →ₗ[k] M)
    (coefficientCompatibility k B M f) q m a

/-- The terminal algebra is the original coefficient algebra with its identity augmentation. -/
abbrev terminalAlgebra : Over B := Over.mk (𝟙 B)

/-- The original regular algebra point retains the original arbitrary coefficient M. -/
def terminalComplex : ChainComplex (ModuleCat.{max u v w} k) ℕ :=
  (functor k B M).obj (terminalAlgebra k B)

/-- An augmentation is its arrow to the original identity-augmented algebra. -/
def toTerminal (P : Over B) : P ⟶ terminalAlgebra k B :=
  Over.homMk P.hom (by
    change P.hom ≫ 𝟙 B = P.hom
    exact Category.comp_id P.hom)

omit [Algebra ℚ k] in
/-- The original stored Over equation proves naturality of the terminal augmentation. -/
theorem toTerminal_naturality {P Q : Over B} (f : P ⟶ Q) :
    f ≫ toTerminal k B Q = toTerminal k B P := by
  apply Over.OverMorphism.ext
  exact f.w

/-- The original Hochschild augmentation is a natural transformation, for every original coefficient M. -/
def augmentationNat : functor k B M ⟶ (CategoryTheory.Functor.const (Over B)).obj (terminalComplex k B M) where
  app P := (functor k B M).map (toTerminal k B P)
  naturality {P Q} f := by
    change (functor k B M).map f ≫ (functor k B M).map (toTerminal k B Q) =
      (functor k B M).map (toTerminal k B P) ≫ 𝟙 _
    exact ((functor k B M).map_comp f (toTerminal k B Q)).symm.trans
      ((congrArg (functor k B M).map (toTerminal_naturality k B f)).trans (Category.comp_id _).symm)

/-- The simplicial Hochschild diagram of the original augmented algebra, with arbitrary coefficient M. -/
def simplicialDiagram
    (P : Over ((SimplicialObject.const (CommAlgCat.{max u v} k)).obj B)) :
    SimplicialObject (ChainComplex (ModuleCat.{max u v w} k) ℕ) :=
  Over.lift P.left P.hom ⋙ functor k B M

/-- The original simplicial augmentation maps every original tail and keeps the coefficient head. -/
def simplicialAugmentation
    (P : Over ((SimplicialObject.const (CommAlgCat.{max u v} k)).obj B)) :
    simplicialDiagram k B M P ⟶
      (SimplicialObject.const (ChainComplex (ModuleCat.{max u v w} k) ℕ)).obj (terminalComplex k B M) :=
  Functor.whiskerLeft (Over.lift P.left P.hom) (augmentationNat k B M)

omit [Algebra ℚ k] in
/-- Every original simplicial operator retains its coefficient-first tensor map. -/
theorem simplicialDiagram_map_tprod
    (P : Over ((SimplicialObject.const (CommAlgCat.{max u v} k)).obj B))
    {i j : SimplexCategoryᵒᵖ} (f : i ⟶ j) (q : ℕ) (m : M) (a : Fin q → P.left.obj i) :
    ((((simplicialDiagram k B M P).map f).f q).hom (m ⊗ₜ[k] PiTensorProduct.tprod k a)) =
      m ⊗ₜ[k] PiTensorProduct.tprod k (fun r => ((P.left.map f).hom (a r))) :=
  map_tprod k B M ((Over.lift P.left P.hom).map f) q m a

omit [Algebra ℚ k] in
/-- An original augmentation is the literal coefficient-first tensor of its algebra augmentation. -/
theorem simplicialAugmentation_tprod
    (P : Over ((SimplicialObject.const (CommAlgCat.{max u v} k)).obj B))
    (i : SimplexCategoryᵒᵖ) (q : ℕ) (m : M) (a : Fin q → P.left.obj i) :
    ((((simplicialAugmentation k B M P).app i).f q).hom (m ⊗ₜ[k] PiTensorProduct.tprod k a)) =
      m ⊗ₜ[k] PiTensorProduct.tprod k (fun r => (P.hom.app i).hom (a r)) :=
  map_tprod k B M (toTerminal k B ((Over.lift P.left P.hom).obj i)) q m a

end ModuleCat.Algebra.Hochschild.Symmetric.AugmentedCoefficients

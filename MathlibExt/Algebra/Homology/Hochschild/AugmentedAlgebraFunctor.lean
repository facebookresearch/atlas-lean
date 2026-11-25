/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Homology.Hochschild.DifferentialFormAlgebraNaturality
public import MathlibExt.CategoryTheory.Comma.Over.Diagram
public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import Mathlib.CategoryTheory.Whiskering

/-!
# Hochschild chains over a coefficient algebra

An algebra augmented into B acts on coefficient B through
the augmentation. Algebra maps over B act on the Hochschild
tensor tails and preserve the coefficient. These maps form
a functor and a natural chain augmentation.
-/

@[expose] public section
noncomputable section

open CategoryTheory Opposite
open scoped TensorProduct Simplicial

universe u v

namespace ModuleCat.Algebra.Hochschild.Symmetric.AugmentedAlgebra

variable (k : Type u) [CommRing k] (B : CommAlgCat.{max u v} k)

/-- The original symmetric coefficient `B` acts through the given algebra
augmentation, with its original ground module retained. -/
def complex (P : Over B) : ChainComplex (ModuleCat.{max u v} k) ℕ := by
  letI : Algebra P.left B := P.hom.hom.toRingHom.toAlgebra
  letI : IsScalarTower k P.left B := inferInstance
  exact Symmetric.chainComplex k P.left B

/-- An original morphism over `B` earns coefficient action compatibility. -/
theorem coefficientCompatibility {P Q : Over B} (f : P ⟶ Q) :
    letI : Algebra P.left B := P.hom.hom.toRingHom.toAlgebra
    letI : Algebra Q.left B := Q.hom.hom.toRingHom.toAlgebra
    ∀ p : P.left, ∀ b : B, (LinearMap.id : B →ₗ[k] B) (p • b) =
      f.left.hom p • (LinearMap.id : B →ₗ[k] B) b := by
  let : Algebra P.left B := P.hom.hom.toRingHom.toAlgebra
  let : Algebra Q.left B := Q.hom.hom.toRingHom.toAlgebra
  intro p b
  change P.hom.hom p * b = Q.hom.hom (f.left.hom p) * b
  exact congrArg (fun a : B => a * b) (ConcreteCategory.congr_hom f.w p).symm

/-- The coefficient-first Hochschild map of an original algebra
morphism over its fixed coefficient algebra. -/
def map {P Q : Over B} (f : P ⟶ Q) : complex k B P ⟶ complex k B Q := by
  letI : Algebra P.left B := P.hom.hom.toRingHom.toAlgebra
  letI : Algebra Q.left B := Q.hom.hom.toRingHom.toAlgebra
  letI : IsScalarTower k P.left B := inferInstance
  letI : IsScalarTower k Q.left B := inferInstance
  exact Symmetric.originalAlgebraCoefficientChainMap k f.left.hom
    (LinearMap.id : B →ₗ[k] B) (coefficientCompatibility k B f)

/-- Every tail factor is mapped by the algebra map and the original
coefficient head is unchanged. -/
theorem map_tprod {P Q : Over B} (f : P ⟶ Q)
    (q : ℕ) (b : B) (a : Fin q → P.left) :
    ((map k B f).f q).hom (b ⊗ₜ[k] PiTensorProduct.tprod k a) =
      b ⊗ₜ[k] PiTensorProduct.tprod k (fun j => f.left.hom (a j)) := by
  let : Algebra P.left B := P.hom.hom.toRingHom.toAlgebra
  let : Algebra Q.left B := Q.hom.hom.toRingHom.toAlgebra
  let : IsScalarTower k P.left B := inferInstance
  let : IsScalarTower k Q.left B := inferInstance
  exact Symmetric.originalAlgebraCoefficientChainMap_tprod k f.left.hom
    (LinearMap.id : B →ₗ[k] B) (coefficientCompatibility k B f) q b a

/-- The Hochschild chain functor on original algebras over `B`. -/
def functor : Over B ⥤ ChainComplex (ModuleCat.{max u v} k) ℕ where
  obj := complex k B
  map := map k B
  map_id P := by
    apply HomologicalComplex.hom_ext
    intro q
    apply ModuleCat.hom_ext
    apply ModuleCat.Algebra.Hochschild.tensorPower_ext
    intro b a
    have h := map_tprod k B (𝟙 P) q b a
    have hTail : (fun j => (𝟙 P : P ⟶ P).left.hom (a j)) = a := by
      funext j
      rfl
    have hValue : ((map k B (𝟙 P)).f q).hom (b ⊗ₜ[k] PiTensorProduct.tprod k a) =
        b ⊗ₜ[k] PiTensorProduct.tprod k a :=
      h.trans (congrArg (fun t => b ⊗ₜ[k] PiTensorProduct.tprod k t) hTail)
    exact hValue.trans (by rfl)
  map_comp f g := by
    apply HomologicalComplex.hom_ext
    intro q
    apply ModuleCat.hom_ext
    apply ModuleCat.Algebra.Hochschild.tensorPower_ext
    intro b a
    have hfg := map_tprod k B (f ≫ g) q b a
    have hf := map_tprod k B f q b a
    have hg := map_tprod k B g q b (fun j => f.left.hom (a j))
    have hTail : (fun j => (f ≫ g).left.hom (a j)) =
        (fun j => g.left.hom (f.left.hom (a j))) := by
      funext j
      rfl
    have hValue : ((map k B (f ≫ g)).f q).hom (b ⊗ₜ[k] PiTensorProduct.tprod k a) =
        ((map k B g).f q).hom (((map k B f).f q).hom (b ⊗ₜ[k] PiTensorProduct.tprod k a)) :=
      hfg.trans ((congrArg (fun t => b ⊗ₜ[k] PiTensorProduct.tprod k t) hTail).trans
        (hg.symm.trans (congrArg ((map k B g).f q).hom hf.symm)))
    exact hValue.trans (by rfl)

/-- The terminal original augmentation is the identity on `B`. -/
abbrev terminalAlgebra : Over B := Over.mk (𝟙 B)

/-- The original Hochschild complex of the coefficient algebra. -/
def regularComplex : ChainComplex (ModuleCat.{max u v} k) ℕ :=
  (functor k B).obj (terminalAlgebra k B)

/-- The terminal augmentation supplies the native regular symmetric action. -/
theorem regularComplex_eq : regularComplex k B = Symmetric.chainComplex k B B := rfl

/-- An original augmentation is its algebra morphism to `id_B`. -/
def toTerminal (P : Over B) : P ⟶ terminalAlgebra k B :=
  Over.homMk P.hom (by
    change P.hom ≫ 𝟙 B = P.hom
    exact Category.comp_id P.hom)

/-- The original augmentation maps form a natural transformation of
algebras over `B`. -/
theorem toTerminal_naturality {P Q : Over B} (f : P ⟶ Q) :
    f ≫ toTerminal k B Q = toTerminal k B P := by
  apply Over.OverMorphism.ext
  exact f.w

/-- Native Hochschild augmentation into the regular coefficient complex. -/
def augmentationNat : functor k B ⟶ (Functor.const (Over B)).obj (regularComplex k B) where
  app P := (functor k B).map (toTerminal k B P)
  naturality {P Q} f := by
    change (functor k B).map f ≫ (functor k B).map (toTerminal k B Q) =
      (functor k B).map (toTerminal k B P) ≫ 𝟙 _
    rw [← Functor.map_comp, toTerminal_naturality, Category.comp_id]

/-- The simplicial Hochschild chain diagram of an original augmented
simplicial algebra, with its original coefficient `B`. -/
def simplicialDiagram
    (P : Over ((SimplicialObject.const (CommAlgCat.{max u v} k)).obj B)) :
    SimplicialObject (ChainComplex (ModuleCat.{max u v} k) ℕ) :=
  Over.lift P.left P.hom ⋙ functor k B

/-- The original simplicial augmentation gives a literal natural map to
the constant Hochschild chain diagram of `B`. -/
def simplicialAugmentation
    (P : Over ((SimplicialObject.const (CommAlgCat.{max u v} k)).obj B)) :
    simplicialDiagram k B P ⟶
      (SimplicialObject.const (ChainComplex (ModuleCat.{max u v} k) ℕ)).obj (regularComplex k B) :=
  Functor.whiskerLeft (Over.lift P.left P.hom) (augmentationNat k B)

/-- Every original simplicial operator is its coefficient-first
Hochschild tensor map. -/
theorem simplicialDiagram_map_tprod
    (P : Over ((SimplicialObject.const (CommAlgCat.{max u v} k)).obj B))
    {i j : SimplexCategoryᵒᵖ} (θ : i ⟶ j) (q : ℕ) (b : B) (a : Fin q → P.left.obj i) :
    ((((simplicialDiagram k B P).map θ).f q).hom (b ⊗ₜ[k] PiTensorProduct.tprod k a)) =
      b ⊗ₜ[k] PiTensorProduct.tprod k (fun r => (P.left.map θ).hom (a r)) :=
  map_tprod k B ((Over.lift P.left P.hom).map θ) q b a

/-- The original augmentation acts on all tail factors. -/
theorem simplicialAugmentation_tprod
    (P : Over ((SimplicialObject.const (CommAlgCat.{max u v} k)).obj B))
    (i : SimplexCategoryᵒᵖ) (q : ℕ) (b : B) (a : Fin q → P.left.obj i) :
    (((simplicialAugmentation k B P).app i).f q).hom (b ⊗ₜ[k] PiTensorProduct.tprod k a) =
      b ⊗ₜ[k] PiTensorProduct.tprod k (fun r => (P.hom.app i).hom (a r)) :=
  map_tprod k B (toTerminal k B ((Over.lift P.left P.hom).obj i)) q b a

end ModuleCat.Algebra.Hochschild.Symmetric.AugmentedAlgebra

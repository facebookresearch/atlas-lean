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
# Hochschild chains of algebras augmented to fixed coefficients

Let `k` be a commutative ring and `B` a commutative `k`-algebra. An augmentation `P → B` makes
`B` a symmetric coefficient module for `P`. Its Hochschild term in degree `q` is `B ⊗[k]
P^⊗q`, with coefficient factor first and the usual signed Hochschild boundary.

A map `f : P → Q` over `B` induces `b ⊗ (a₀ ⊗ ⋯ ⊗ a_(q-1)) ↦ b ⊗ (f(a₀) ⊗ ⋯ ⊗ f(a_(q-1)))`.
These maps form a functor on algebras over `B`. Augmentation to the terminal object `id_B`
gives a natural chain map to the regular Hochschild complex of `B`. Applied degreewise to an
augmented simplicial algebra, it gives a simplicial diagram of complexes and its simplicial
augmentation.
-/

@[expose] public section
noncomputable section

open CategoryTheory Opposite
open scoped TensorProduct Simplicial

universe u v

namespace ModuleCat.Algebra.Hochschild.Symmetric.AugmentedAlgebra

variable (k : Type u) [CommRing k] (B : CommAlgCat.{max u v} k)

/-- The Hochschild complex of an algebra augmented to its coefficient algebra.

For `P → B`, the coefficient algebra `B` acts through the augmentation on both sides, and the
degree-`q` chain term is `B ⊗[k] P^⊗q`. -/
def complex (P : Over B) : ChainComplex (ModuleCat.{max u v} k) ℕ := by
  letI : Algebra P.left B := P.hom.hom.toRingHom.toAlgebra
  letI : IsScalarTower k P.left B := inferInstance
  exact Symmetric.chainComplex k P.left B

/-- Compatibility of fixed coefficients for a map of augmented algebras.

For `f : P → Q` over `B`, the identity coefficient map on `B` intertwines the source and
target actions: `P.hom(p) * b = Q.hom(f(p)) * b`. -/
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

/-- The Hochschild chain map of a map over fixed coefficients.

For `f : P → Q` over `B`, apply `f` to each algebra tensor factor and retain the coefficient
factor in `B`. -/
def map {P Q : Over B} (f : P ⟶ Q) : complex k B P ⟶ complex k B Q := by
  letI : Algebra P.left B := P.hom.hom.toRingHom.toAlgebra
  letI : Algebra Q.left B := Q.hom.hom.toRingHom.toAlgebra
  letI : IsScalarTower k P.left B := inferInstance
  letI : IsScalarTower k Q.left B := inferInstance
  exact Symmetric.originalAlgebraCoefficientChainMap k f.left.hom
    (LinearMap.id : B →ₗ[k] B) (coefficientCompatibility k B f)

/-- The tensor-coordinate formula for a map over fixed coefficients.

In Hochschild degree `q`, the map induced by `f` sends `b ⊗ ⊗ᵢ aᵢ` to `b ⊗ ⊗ᵢ f(aᵢ)`. -/
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

/-- The Hochschild chain functor on algebras over a coefficient algebra.

For fixed `B`, this sends an augmentation `P → B` to the Hochschild complex of `P` with
symmetric coefficients `B`. -/
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

/-- The terminal augmented algebra over a coefficient algebra.

The terminal object of `Over B` is the identity augmentation `B → B`. -/
abbrev terminalAlgebra : Over B := Over.mk (𝟙 B)

/-- The regular Hochschild complex at the terminal augmentation.

At `id_B`, the augmented-algebra Hochschild functor has value the Hochschild complex of `B`
with coefficient module `B`. -/
def regularComplex : ChainComplex (ModuleCat.{max u v} k) ℕ :=
  (functor k B).obj (terminalAlgebra k B)

/-- The terminal augmented complex as the regular symmetric Hochschild complex.

The complex at `id_B` equals the symmetric Hochschild chain complex with algebra and
coefficient module both `B`. -/
theorem regularComplex_eq : regularComplex k B = Symmetric.chainComplex k B B := rfl

/-- The map of an augmented algebra to the terminal augmentation.

For `P → B`, its augmentation defines the map in `Over B` from `P` to `id_B`. -/
def toTerminal (P : Over B) : P ⟶ terminalAlgebra k B :=
  Over.homMk P.hom (by
    change P.hom ≫ 𝟙 B = P.hom
    exact Category.comp_id P.hom)

/-- Naturality of maps to the terminal augmented algebra.

For `f : P → Q` over `B`, composing `f` with the terminal map of `Q` gives the terminal map of
`P`. -/
theorem toTerminal_naturality {P Q : Over B} (f : P ⟶ Q) :
    f ≫ toTerminal k B Q = toTerminal k B P := by
  apply Over.OverMorphism.ext
  exact f.w

/-- The natural Hochschild augmentation to the coefficient algebra.

The maps `P → id_B` induce a natural transformation from the augmented-algebra Hochschild
functor to the constant functor with value the regular Hochschild complex of `B`. -/
def augmentationNat : functor k B ⟶ (Functor.const (Over B)).obj (regularComplex k B) where
  app P := (functor k B).map (toTerminal k B P)
  naturality {P Q} f := by
    change (functor k B).map f ≫ (functor k B).map (toTerminal k B Q) =
      (functor k B).map (toTerminal k B P) ≫ 𝟙 _
    rw [← Functor.map_comp, toTerminal_naturality, Category.comp_id]

/-- The Hochschild diagram of an augmented simplicial algebra.

For `P_• → B`, apply the fixed-coefficient Hochschild functor in each simplicial degree to
obtain a simplicial diagram of chain complexes. -/
def simplicialDiagram
    (P : Over ((SimplicialObject.const (CommAlgCat.{max u v} k)).obj B)) :
    SimplicialObject (ChainComplex (ModuleCat.{max u v} k) ℕ) :=
  Over.lift P.left P.hom ⋙ functor k B

/-- The Hochschild simplicial augmentation to fixed coefficients.

For `P_• → B`, the algebra augmentations induce a simplicial map from its Hochschild diagram
to the constant diagram on the regular Hochschild complex of `B`. -/
def simplicialAugmentation
    (P : Over ((SimplicialObject.const (CommAlgCat.{max u v} k)).obj B)) :
    simplicialDiagram k B P ⟶
      (SimplicialObject.const (ChainComplex (ModuleCat.{max u v} k) ℕ)).obj (regularComplex k B) :=
  Functor.whiskerLeft (Over.lift P.left P.hom) (augmentationNat k B)

/-- The tensor formula for a simplicial Hochschild operator.

For a simplicial operator `θ`, its map in Hochschild degree `q` retains the coefficient `b ∈
B` and applies the algebra operator `P(θ)` to each of the `q` tensor factors. -/
theorem simplicialDiagram_map_tprod
    (P : Over ((SimplicialObject.const (CommAlgCat.{max u v} k)).obj B))
    {i j : SimplexCategoryᵒᵖ} (θ : i ⟶ j) (q : ℕ) (b : B) (a : Fin q → P.left.obj i) :
    ((((simplicialDiagram k B P).map θ).f q).hom (b ⊗ₜ[k] PiTensorProduct.tprod k a)) =
      b ⊗ₜ[k] PiTensorProduct.tprod k (fun r => (P.left.map θ).hom (a r)) :=
  map_tprod k B ((Over.lift P.left P.hom).map θ) q b a

/-- The tensor formula for a simplicial Hochschild augmentation.

In a fixed simplicial degree, the augmentation retains the coefficient `b ∈ B` and applies
that degree's algebra augmentation `P_i → B` to every Hochschild tail factor. -/
theorem simplicialAugmentation_tprod
    (P : Over ((SimplicialObject.const (CommAlgCat.{max u v} k)).obj B))
    (i : SimplexCategoryᵒᵖ) (q : ℕ) (b : B) (a : Fin q → P.left.obj i) :
    (((simplicialAugmentation k B P).app i).f q).hom (b ⊗ₜ[k] PiTensorProduct.tprod k a) =
      b ⊗ₜ[k] PiTensorProduct.tprod k (fun r => (P.hom.app i).hom (a r)) :=
  map_tprod k B (toTerminal k B ((Over.lift P.left P.hom).obj i)) q b a

end ModuleCat.Algebra.Hochschild.Symmetric.AugmentedAlgebra

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
# Augmented Hochschild diagrams with module coefficients

Let `k` be a commutative ring, `B` a commutative `k`-algebra, and `M` a `B`-module with
compatible `k`-action. An augmentation `P → B` makes `M` a symmetric `P`-coefficient module,
giving degree-`q` Hochschild chains `M ⊗[k] P^⊗q`.

Maps over `B` retain the coefficient `m ∈ M` and apply the algebra map to each tail factor.
They form a functor and a natural augmentation to the Hochschild complex of `B` with
coefficients `M`. Applying these constructions to an augmented simplicial algebra gives a
simplicial chain diagram and its augmentation. The tensor-coordinate and terminal naturality
formulas are integral; the coefficient carrier universe is independent.
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

/-- The Hochschild complex with coefficients along an algebra augmentation.

For `P → B` and a compatible `B`-module `M`, this is the Hochschild complex with degree `q`
equal to `M ⊗[k] P^⊗q`, using the augmentation-induced symmetric action. -/
def complex (P : Over B) : ChainComplex (ModuleCat.{max u v w} k) ℕ := chainComplex k P.left M

/-- The augmented Hochschild map with a fixed module coefficient.

For `f : P → Q` over `B`, the induced chain map retains `M` and applies `f` to the algebra
tail factors. -/
def map {P Q : Over B} (f : P ⟶ Q) : complex k B M P ⟶ complex k B M Q :=
  originalAlgebraCoefficientChainMap k f.left.hom (LinearMap.id : M →ₗ[k] M)
    (coefficientCompatibility k B M f)

/-- The augmented Hochschild functor with module coefficients.

For fixed `B` and `M`, this functor sends `P → B` to its Hochschild complex with coefficient
action through `P → B`. -/
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
/-- The integral tensor formula for an augmented coefficient map.

For `f : P → Q` over `B`, the degree-`q` map sends `m ⊗ ⊗ᵢ aᵢ` to `m ⊗ ⊗ᵢ f(aᵢ)`. This formula
is stated without a rational scalar assumption. -/
theorem map_tprod {P Q : Over B} (f : P ⟶ Q) (q : ℕ) (m : M) (a : Fin q → P.left) :
    ((map k B M f).f q).hom (m ⊗ₜ[k] PiTensorProduct.tprod k a) =
      m ⊗ₜ[k] PiTensorProduct.tprod k (fun j => f.left.hom (a j)) :=
  originalAlgebraCoefficientChainMap_tprod k f.left.hom (LinearMap.id : M →ₗ[k] M)
    (coefficientCompatibility k B M f) q m a

/-- The terminal algebra for an augmented module-coefficient diagram.

The terminal object of `Over B` is `B` with its identity augmentation. -/
abbrev terminalAlgebra : Over B := Over.mk (𝟙 B)

/-- The Hochschild coefficient complex at the terminal algebra.

At the identity augmentation of `B`, the augmented coefficient functor gives the Hochschild
complex of `B` with the given coefficient module `M`. -/
def terminalComplex : ChainComplex (ModuleCat.{max u v w} k) ℕ :=
  (functor k B M).obj (terminalAlgebra k B)

/-- The terminal map of an algebra with fixed module coefficients.

For `P → B`, its augmentation gives the arrow in `Over B` to the identity-augmented algebra
`B`. -/
def toTerminal (P : Over B) : P ⟶ terminalAlgebra k B :=
  Over.homMk P.hom (by
    change P.hom ≫ 𝟙 B = P.hom
    exact Category.comp_id P.hom)

omit [Algebra ℚ k] in
/-- The terminal naturality equation for augmented coefficients.

For `f : P → Q` over `B`, composing `f` with the terminal map of `Q` equals the terminal map
of `P`. The equation does not require a rational scalar structure. -/
theorem toTerminal_naturality {P Q : Over B} (f : P ⟶ Q) :
    f ≫ toTerminal k B Q = toTerminal k B P := by
  apply Over.OverMorphism.ext
  exact f.w

/-- The natural Hochschild augmentation with arbitrary module coefficients.

The terminal algebra maps induce a natural transformation to the constant chain complex of `B`
with coefficients `M`, retaining the coefficient value. -/
def augmentationNat : functor k B M ⟶ (CategoryTheory.Functor.const (Over B)).obj (terminalComplex k B M) where
  app P := (functor k B M).map (toTerminal k B P)
  naturality {P Q} f := by
    change (functor k B M).map f ≫ (functor k B M).map (toTerminal k B Q) =
      (functor k B M).map (toTerminal k B P) ≫ 𝟙 _
    exact ((functor k B M).map_comp f (toTerminal k B Q)).symm.trans
      ((congrArg (functor k B M).map (toTerminal_naturality k B f)).trans (Category.comp_id _).symm)

/-- The augmented simplicial Hochschild diagram with module coefficients.

For `P_• → B`, applying the fixed-module-coefficient Hochschild functor in each simplicial
degree gives a simplicial diagram of chain complexes in the joint coefficient universe. -/
def simplicialDiagram
    (P : Over ((SimplicialObject.const (CommAlgCat.{max u v} k)).obj B)) :
    SimplicialObject (ChainComplex (ModuleCat.{max u v w} k) ℕ) :=
  Over.lift P.left P.hom ⋙ functor k B M

/-- The simplicial Hochschild augmentation with module coefficients.

For `P_• → B`, its algebra augmentation induces a map to the constant simplicial diagram on
the Hochschild complex of `B` with coefficients `M`. -/
def simplicialAugmentation
    (P : Over ((SimplicialObject.const (CommAlgCat.{max u v} k)).obj B)) :
    simplicialDiagram k B M P ⟶
      (SimplicialObject.const (ChainComplex (ModuleCat.{max u v w} k) ℕ)).obj (terminalComplex k B M) :=
  Functor.whiskerLeft (Over.lift P.left P.hom) (augmentationNat k B M)

omit [Algebra ℚ k] in
/-- The integral tensor formula for a module-coefficient simplicial operator.

A simplicial algebra operator acts on every Hochschild tail factor and retains the coefficient
`m ∈ M`. The tensor formula is stated without a rational scalar assumption. -/
theorem simplicialDiagram_map_tprod
    (P : Over ((SimplicialObject.const (CommAlgCat.{max u v} k)).obj B))
    {i j : SimplexCategoryᵒᵖ} (f : i ⟶ j) (q : ℕ) (m : M) (a : Fin q → P.left.obj i) :
    ((((simplicialDiagram k B M P).map f).f q).hom (m ⊗ₜ[k] PiTensorProduct.tprod k a)) =
      m ⊗ₜ[k] PiTensorProduct.tprod k (fun r => ((P.left.map f).hom (a r))) :=
  map_tprod k B M ((Over.lift P.left P.hom).map f) q m a

omit [Algebra ℚ k] in
/-- The integral tensor formula for a module-coefficient simplicial augmentation.

In degree `i`, the augmentation retains `m ∈ M` and applies `P_i → B` to each Hochschild tail
factor. The formula does not require rational scalars. -/
theorem simplicialAugmentation_tprod
    (P : Over ((SimplicialObject.const (CommAlgCat.{max u v} k)).obj B))
    (i : SimplexCategoryᵒᵖ) (q : ℕ) (m : M) (a : Fin q → P.left.obj i) :
    ((((simplicialAugmentation k B M P).app i).f q).hom (m ⊗ₜ[k] PiTensorProduct.tprod k a)) =
      m ⊗ₜ[k] PiTensorProduct.tprod k (fun r => (P.hom.app i).hom (a r)) :=
  map_tprod k B M (toTerminal k B ((Over.lift P.left P.hom).obj i)) q m a

end ModuleCat.Algebra.Hochschild.Symmetric.AugmentedCoefficients

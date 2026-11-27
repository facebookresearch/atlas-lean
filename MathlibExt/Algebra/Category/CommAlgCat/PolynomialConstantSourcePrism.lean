/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialObject.ConstantSourcePrism
public import MathlibExt.AlgebraicTopology.SimplicialObject.NormalizedChainHomotopy
public import MathlibExt.Algebra.Category.CommAlgCat.PolynomialBoundaryComparison
public import MathlibExt.Algebra.Category.CommAlgCat.CotangentSimplicial
public import MathlibExt.Algebra.Category.ModuleCat.TensorBifunctor
public import MathlibExt.CategoryTheory.Comma.Over.Diagram
public import Mathlib.Algebra.Homology.Additive

/-!
# Relative homotopies from a constant polynomial source

Let `B → A` be a commutative `k`-algebra over `A`, with a polynomial presentation of
`B`. Suppose the augmented simplicial algebra `Q → const A` has an additively
aspherical augmentation. Two augmented-algebra maps from the constant diagram on `B`
to `Q` admit an algebra edge over `A` with zero face the second map and last face the
first map.

The edge induces a simplicial homotopy on the whole constant source, including its
face and degeneracy identities. Applying the cotangent functor and normalization gives
a chain homotopy, and applying `M ⊗[A] −` preserves that homotopy for arbitrary
coefficients in an independent universe.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicTopology
open scoped Simplicial

universe u v t

namespace CommAlgCat.PolynomialConstantSourcePrism

variable (k : Type u) [CommRing k] (A B : CommAlgCat.{max u v} k)
  (α : B ⟶ A)

/--
The constant simplicial algebra on `B`, augmented to the constant diagram on `A`
by the fixed algebra map `α : B ⟶ A`.
-/
def source : Over ((SimplicialObject.const (CommAlgCat.{max u v} k)).obj A) :=
  Over.mk ((SimplicialObject.const (CommAlgCat.{max u v} k)).map α)

variable {k A B α}
  {Q : Over ((SimplicialObject.const (CommAlgCat.{max u v} k)).obj A)}
  (σ : Type (max u v)) (e : B ≅ (free.{u, v} k).obj σ)
  (f g : source k A B α ⟶ Q) (hQ : additiveResolutionCondition k A Q)

/--
The algebra map `k[σ] → A` obtained by composing the inverse polynomial presentation
of `B` with its augmentation `α`.
-/
def generatorAugmentation : MvPolynomial σ k →ₐ[k] A := (e.inv ≫ α).hom
/--
The degree-zero first endpoint map `f`, precomposed with the inverse polynomial
presentation of the constant source `B`.
-/
def generatorF : MvPolynomial σ k →ₐ[k] Q.left.obj (op ⦋0⦌) :=
  (e.inv ≫ f.left.app (op ⦋0⦌)).hom
/--
The degree-zero second endpoint map `g`, precomposed with the inverse polynomial
presentation of the constant source `B`.
-/
def generatorG : MvPolynomial σ k →ₐ[k] Q.left.obj (op ⦋0⦌) :=
  (e.inv ≫ g.left.app (op ⦋0⦌)).hom

/--
The first endpoint in polynomial coordinates has the prescribed generator augmentation.
-/
theorem generatorF_augmentation :
    (Q.hom.app (op ⦋0⦌)).hom.comp (generatorF σ e f) =
      generatorAugmentation (α := α) σ e := by
  have h : f.left.app (op ⦋0⦌) ≫ Q.hom.app (op ⦋0⦌) = α :=
    NatTrans.congr_app f.w (op ⦋0⦌)
  exact congrArg CommAlgCat.Hom.hom
    ((Category.assoc e.inv (f.left.app (op ⦋0⦌)) (Q.hom.app (op ⦋0⦌))).trans
      (congrArg (fun z => e.inv ≫ z) h))

/--
The second endpoint in polynomial coordinates has the prescribed generator augmentation.
-/
theorem generatorG_augmentation :
    (Q.hom.app (op ⦋0⦌)).hom.comp (generatorG σ e g) =
      generatorAugmentation (α := α) σ e := by
  have h : g.left.app (op ⦋0⦌) ≫ Q.hom.app (op ⦋0⦌) = α :=
    NatTrans.congr_app g.w (op ⦋0⦌)
  exact congrArg CommAlgCat.Hom.hom
    ((Category.assoc e.inv (g.left.app (op ⦋0⦌)) (Q.hom.app (op ⦋0⦌))).trans
      (congrArg (fun z => e.inv ≫ z) h))

/--
The algebra edge `B → Q₁` between augmented maps `f` and `g`, constructed from the
polynomial presentation of `B` and additive asphericity of the target. Its faces are
`d₀(edge) = g₀` and `d₁(edge) = f₀`.
-/
def edge : B ⟶ Q.left.obj (op ⦋1⦌) :=
  e.hom ≫ CommAlgCat.ofHom
    (PolynomialBoundaryComparison.firstPrism k A Q σ hQ
      (generatorAugmentation (α := α) σ e) (generatorF σ e f) (generatorG σ e g)
      (generatorF_augmentation σ e f) (generatorG_augmentation σ e g))

/--
The zero face of the constructed algebra edge is the degree-zero component of the
second endpoint map `g`.
-/
@[reassoc]
theorem edge_zero_face : edge σ e f g hQ ≫ Q.left.δ (0 : Fin 2) = g.left.app (op ⦋0⦌) := by
  have h : CommAlgCat.ofHom
      (PolynomialBoundaryComparison.firstPrism k A Q σ hQ
        (generatorAugmentation (α := α) σ e) (generatorF σ e f) (generatorG σ e g)
        (generatorF_augmentation σ e f) (generatorG_augmentation σ e g)) ≫ Q.left.δ (0 : Fin 2) =
      e.inv ≫ g.left.app (op ⦋0⦌) := by
    apply CommAlgCat.hom_ext
    exact PolynomialBoundaryComparison.firstPrism_zero_face k A Q σ hQ
      (generatorAugmentation (α := α) σ e) (generatorF σ e f) (generatorG σ e g)
      (generatorF_augmentation σ e f) (generatorG_augmentation σ e g)
  let z : (free.{u, v} k).obj σ ⟶ Q.left.obj (op ⦋1⦌) := CommAlgCat.ofHom
    (PolynomialBoundaryComparison.firstPrism k A Q σ hQ
      (generatorAugmentation (α := α) σ e) (generatorF σ e f) (generatorG σ e g)
      (generatorF_augmentation σ e f) (generatorG_augmentation σ e g))
  exact (Category.assoc e.hom z (Q.left.δ (0 : Fin 2))).trans
    ((congrArg (fun a => e.hom ≫ a) h).trans
      ((Category.assoc e.hom e.inv (g.left.app (op ⦋0⦌))).symm.trans
        ((congrArg (fun a => a ≫ g.left.app (op ⦋0⦌)) e.hom_inv_id).trans
          (Category.id_comp _))))

/--
The one face of the constructed algebra edge is the degree-zero component of the
first endpoint map `f`.
-/
@[reassoc]
theorem edge_one_face : edge σ e f g hQ ≫ Q.left.δ (1 : Fin 2) = f.left.app (op ⦋0⦌) := by
  have h : CommAlgCat.ofHom
      (PolynomialBoundaryComparison.firstPrism k A Q σ hQ
        (generatorAugmentation (α := α) σ e) (generatorF σ e f) (generatorG σ e g)
        (generatorF_augmentation σ e f) (generatorG_augmentation σ e g)) ≫ Q.left.δ (1 : Fin 2) =
      e.inv ≫ f.left.app (op ⦋0⦌) := by
    apply CommAlgCat.hom_ext
    exact PolynomialBoundaryComparison.firstPrism_one_face k A Q σ hQ
      (generatorAugmentation (α := α) σ e) (generatorF σ e f) (generatorG σ e g)
      (generatorF_augmentation σ e f) (generatorG_augmentation σ e g)
  let z : (free.{u, v} k).obj σ ⟶ Q.left.obj (op ⦋1⦌) := CommAlgCat.ofHom
    (PolynomialBoundaryComparison.firstPrism k A Q σ hQ
      (generatorAugmentation (α := α) σ e) (generatorF σ e f) (generatorG σ e g)
      (generatorF_augmentation σ e f) (generatorG_augmentation σ e g))
  exact (Category.assoc e.hom z (Q.left.δ (1 : Fin 2))).trans
    ((congrArg (fun a => e.hom ≫ a) h).trans
      ((Category.assoc e.hom e.inv (f.left.app (op ⦋0⦌))).symm.trans
        ((congrArg (fun a => a ≫ f.left.app (op ⦋0⦌)) e.hom_inv_id).trans
          (Category.id_comp _))))

/--
The constructed edge has the fixed augmentation `α : B ⟶ A`.
-/
@[reassoc]
theorem edge_augmentation : edge σ e f g hQ ≫ Q.hom.app (op ⦋1⦌) = α := by
  have hδ : Q.left.δ (0 : Fin 2) ≫ Q.hom.app (op ⦋0⦌) = Q.hom.app (op ⦋1⦌) :=
    (Q.hom.naturality (SimplexCategory.δ (0 : Fin 2)).op).trans (Category.comp_id _)
  rw [← hδ, ← Category.assoc, edge_zero_face]
  exact NatTrans.congr_app g.w (op ⦋0⦌)

/--
The algebra edge as a morphism over `A`, from `B → A` to the degree-one object of
the lifted target augmentation.
-/
def sliceEdge : Over.mk α ⟶ (Over.lift Q.left Q.hom).obj (op ⦋1⦌) :=
  Over.homMk (edge σ e f g hQ) (edge_augmentation σ e f g hQ)

/--
The simplicial homotopy over `A` between the lifted augmented-algebra maps `f` and
`g`, determined by the constructed edge on the constant polynomial source.
-/
def homotopy : SimplicialObject.Homotopy (Over.liftDiagramMap A f) (Over.liftDiagramMap A g) :=
  SimplicialObject.ConstantSourcePrism.homotopy
    (Over.liftDiagramMap A f) (Over.liftDiagramMap A g) (sliceEdge σ e f g hQ)
    (by apply Over.OverMorphism.ext; exact edge_one_face σ e f g hQ)
    (by apply Over.OverMorphism.ext; exact edge_zero_face σ e f g hQ)

/--
The simplicial algebra homotopy between `f.left` and `g.left` obtained by forgetting
the slice structure from the relative homotopy.
-/
def algebraHomotopy : SimplicialObject.Homotopy f.left g.left :=
  (homotopy σ e f g hQ).whiskerRight (Over.forget A)

/--
The simplicial homotopy between the cotangent maps induced by `f` and `g`, obtained
by applying the cotangent functor to the relative algebra homotopy.
-/
def cotangentHomotopy : SimplicialObject.Homotopy
    (cotangentSimplicialMap k A f) (cotangentSimplicialMap k A g) :=
  (homotopy σ e f g hQ).whiskerRight (cotangentFunctor k A)

/--
The chain homotopy between the normalized cotangent maps induced by the two
constant-source augmented maps `f` and `g`.
-/
def normalizedCotangentHomotopy : _root_.Homotopy
    ((normalizedMooreComplex (ModuleCat.{max u v} A)).map (cotangentSimplicialMap k A f))
    ((normalizedMooreComplex (ModuleCat.{max u v} A)).map (cotangentSimplicialMap k A g)) :=
  SimplicialObject.Homotopy.toNormalizedChainHomotopy (cotangentHomotopy σ e f g hQ)

/--
The chain homotopy obtained by applying `M ⊗[A] −` to the normalized cotangent
homotopy, with `M` as first tensor factor in an independent coefficient universe.
-/
def coefficientHomotopy (M : ModuleCat.{t} A) :
    _root_.Homotopy
      ((((ModuleCat.tensorBifunctorAt.{max u v, t, max u v} A).obj M).mapHomologicalComplex
        (ComplexShape.down ℕ)).map ((normalizedMooreComplex (ModuleCat.{max u v} A)).map
          (cotangentSimplicialMap k A f)))
      ((((ModuleCat.tensorBifunctorAt.{max u v, t, max u v} A).obj M).mapHomologicalComplex
        (ComplexShape.down ℕ)).map ((normalizedMooreComplex (ModuleCat.{max u v} A)).map
          (cotangentSimplicialMap k A g))) :=
  ((ModuleCat.tensorBifunctorAt.{max u v, t, max u v} A).obj M).mapHomotopy
    (normalizedCotangentHomotopy σ e f g hQ)

end CommAlgCat.PolynomialConstantSourcePrism

end

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Algebra.Category.CommAlgCat.PolynomialConstantSourcePrism
public import MathlibExt.Algebra.Category.CommAlgCat.PolynomialSplitting

/-!
# Relative homotopies on the zero-generated polynomial diagram

Let k be a commutative ring and P an augmented simplicial k-algebra over A with compatible
polynomial splitting. Its degree-zero nondegenerate algebra N₀(P), with augmentation through P₀,
defines a constant augmented simplicial diagram and a canonical morphism to P.

For maps f,g:P→Q over A, assume that Q's normalized additive augmentation is a
quasi-isomorphism. Their restrictions to this constant source are simplicially homotopic in Over
A. Forgetting to algebras, applying the cotangent functor and normalized Moore chains, then
tensoring with any A-module M transports the same homotopy.

Ground-ring and algebra carrier parameters are independent. Algebra and cotangent carriers use
max(u,v); M may have any carrier universe t and the coefficient tensor has carrier max(t,u,v).
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicTopology
open scoped Simplicial

universe u v t

namespace CommAlgCat.PolynomialZeroGeneratedPrism

variable {k : Type u} [CommRing k] {A : CommAlgCat.{max u v} k}
  {P Q : Over ((SimplicialObject.const (CommAlgCat.{max u v} k)).obj A)}
  (s : PolynomialSplitting k P.left)

/-- Let k be a commutative ring and P an augmented simplicial k-algebra over A with compatible
polynomial splitting s. The point over A is N₀(P) with augmentation ι₀≫εP₀:N₀(P)→A. -/
def point : Over A := Over.mk (s.splitting.ι 0 ≫ P.hom.app (op ⦋0⦌))

/-- Let k be a commutative ring and P an augmented simplicial k-algebra over A with compatible
polynomial splitting s. Form the constant simplicial algebra on N₀(P), with augmentation induced
by ι₀≫εP₀. -/
def source : Over ((SimplicialObject.const (CommAlgCat.{max u v} k)).obj A) :=
  PolynomialConstantSourcePrism.source k A (s.splitting.N 0) (point s).hom

/-- Let k be a commutative ring and P an augmented simplicial k-algebra over A with compatible
polynomial splitting s. The summand inclusion ι₀:N₀(P)→P₀ is a morphism over A from the chosen
augmented point to the degree-zero object of P. -/
def inclusionAtZero : point s ⟶ (Over.lift P.left P.hom).obj (op ⦋0⦌) :=
  Over.homMk (s.splitting.ι 0) rfl

/-- Let k be a commutative ring and P an augmented simplicial k-algebra over A with compatible
polynomial splitting s. The degree-zero inclusion extends along the unique degeneracies from
degree zero to a morphism from the constant diagram on N₀(P) to the diagram P in Over A. -/
def inclusionOver : (SimplicialObject.const (Over A)).obj (point s) ⟶ Over.lift P.left P.hom :=
  SimplicialObject.ConstantSourcePrism.fromZero (inclusionAtZero s)

/-- Let k be a commutative ring and P an augmented simplicial k-algebra over A with compatible
polynomial splitting s. Forgetting the slice diagram gives an augmented simplicial morphism from
the constant N₀(P) source to P. -/
def inclusion : source s ⟶ P :=
  Over.homMk
    (((SimplicialObject.whiskering (Over A) (CommAlgCat.{max u v} k)).obj
      (Over.forget A)).map (inclusionOver s)) (by
        apply NatTrans.ext
        funext Δ
        exact ((inclusionOver s).app Δ).w)

/-- Let k be a commutative ring and P an augmented simplicial k-algebra over A with compatible
polynomial splitting s. The degree-zero component of the constant-source inclusion is
ι₀:N₀(P)→P₀. -/
@[simp]
theorem inclusion_zero : (inclusion s).left.app (op ⦋0⦌) = s.splitting.ι 0 := by
  change ((inclusionOver s).app (op ⦋0⦌)).left = _
  rw [inclusionOver, SimplicialObject.ConstantSourcePrism.fromZero_zero]
  rfl

variable (f g : P ⟶ Q) (hQ : additiveResolutionCondition k A Q)

/-- Let k be a commutative ring and P an augmented simplicial k-algebra over A with compatible
polynomial splitting s. Fix maps f,g:P→Q over A and assume that Q's normalized additive
augmentation is a quasi-isomorphism. Restrict f and g to the constant N₀(P) source. Their
induced diagrams in Over A have a simplicial homotopy. -/
def homotopy : SimplicialObject.Homotopy
    (Over.liftDiagramMap A (inclusion s ≫ f)) (Over.liftDiagramMap A (inclusion s ≫ g)) :=
  PolynomialConstantSourcePrism.homotopy (s.variables 0) (s.polynomialIso 0)
    (inclusion s ≫ f) (inclusion s ≫ g) hQ

/-- Let k be a commutative ring and P an augmented simplicial k-algebra over A with compatible
polynomial splitting s. Fix maps f,g:P→Q over A and assume that Q's normalized additive
augmentation is a quasi-isomorphism. The restricted underlying simplicial algebra maps from the
constant N₀(P) source to Q are homotopic. -/
def algebraHomotopy : SimplicialObject.Homotopy
    (inclusion s ≫ f).left (inclusion s ≫ g).left :=
  PolynomialConstantSourcePrism.algebraHomotopy (s.variables 0) (s.polynomialIso 0)
    (inclusion s ≫ f) (inclusion s ≫ g) hQ

/-- Let k be a commutative ring and P an augmented simplicial k-algebra over A with compatible
polynomial splitting s. Fix maps f,g:P→Q over A and assume that Q's normalized additive
augmentation is a quasi-isomorphism. Linearize the restricted maps by B→A ↦ A ⊗[B] Ω(B/k), then
take normalized Moore chains. The resulting cotangent chain maps are homotopic. -/
def normalizedCotangentHomotopy : _root_.Homotopy
    ((normalizedMooreComplex (ModuleCat.{max u v} A)).map (cotangentSimplicialMap k A (inclusion s ≫ f)))
    ((normalizedMooreComplex (ModuleCat.{max u v} A)).map (cotangentSimplicialMap k A (inclusion s ≫ g))) :=
  PolynomialConstantSourcePrism.normalizedCotangentHomotopy (s.variables 0) (s.polynomialIso 0)
    (inclusion s ≫ f) (inclusion s ≫ g) hQ

/-- Let k be a commutative ring and P an augmented simplicial k-algebra over A with compatible
polynomial splitting s. Fix maps f,g:P→Q over A and assume that Q's normalized additive
augmentation is a quasi-isomorphism. For any A-module M in carrier universe t, the functor M
⊗[A] − sends the normalized cotangent homotopy to a homotopy of the corresponding coefficient
chain maps. The tensor carrier is max(t,u,v). -/
def coefficientHomotopy (M : ModuleCat.{t} A) : _root_.Homotopy
    ((((ModuleCat.tensorBifunctorAt.{max u v, t, max u v} A).obj M).mapHomologicalComplex
      (ComplexShape.down ℕ)).map ((normalizedMooreComplex (ModuleCat.{max u v} A)).map
        (cotangentSimplicialMap k A (inclusion s ≫ f))))
    ((((ModuleCat.tensorBifunctorAt.{max u v, t, max u v} A).obj M).mapHomologicalComplex
      (ComplexShape.down ℕ)).map ((normalizedMooreComplex (ModuleCat.{max u v} A)).map
        (cotangentSimplicialMap k A (inclusion s ≫ g)))) :=
  PolynomialConstantSourcePrism.coefficientHomotopy (s.variables 0) (s.polynomialIso 0)
    (inclusion s ≫ f) (inclusion s ≫ g) hQ M

end CommAlgCat.PolynomialZeroGeneratedPrism

end

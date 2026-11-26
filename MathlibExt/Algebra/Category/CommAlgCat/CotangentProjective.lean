/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Algebra.Category.CommAlgCat.CotangentSimplicial
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.LinearAlgebra.TensorProduct.Basis
public import Mathlib.RingTheory.Kaehler.Polynomial
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.CategoryTheory.Retract

/-!
# Projective terms of polynomial cotangent models

Let `k : Type u` be a commutative ring and `A : CommAlgCat.{max u v} k`. A polynomial
presentation `Free_k(σ) ≅ P.left` of an algebra over `A` gives an `A`-basis of its cotangent
linearization, indexed by `σ`. Each simplicial degree of the canonical polynomial resolution
has such a presentation.

The normalized Moore complex is a retract of the alternating-face complex. Hence its terms are
projective over `A`. At the identity algebra over `A`, every term of `cotangentComplex k A` is
projective and therefore flat.

## References

* Stacks Project, Sections 92.3–92.4.
-/

@[expose] public section

noncomputable section

open CategoryTheory Opposite AlgebraicTopology
open scoped Simplicial

universe u v

namespace CommAlgCat

variable (k : Type u) [CommRing k] (A : CommAlgCat.{max u v} k)

attribute [local instance] cotangentAlgebra cotangentScalarTower

/-- Let `k` be a commutative ring, `A` a `k`-algebra, `P=(P.left→A)` an object of `Over A`, and `e
: Free_k(σ) ≅ P.left` a polynomial presentation. The object `polynomialPresentationOver k A P
σ e` is `Free_k(σ)` over `A` via the composite `e.hom ≫ P.hom`. -/
def polynomialPresentationOver (P : Over A) (σ : Type (max u v))
    (e : (free.{u, v} k).obj σ ≅ P.left) : Over A :=
  Over.mk (e.hom ≫ P.hom)

/-- Let `k : Type u` be a commutative ring, `A : CommAlgCat.{max u v} k`, `P∈Over A`, `σ :
Type(max u v)`, and `e : Free_k(σ) ≅ P.left`. The linearization of `polynomialPresentationOver
k A P σ e` has an `A`-basis indexed by `σ`, obtained by extending the polynomial differential
basis `dX_x` along the presented algebra's map to `A`. -/
def polynomialCotangentBasis (P : Over A) (σ : Type (max u v))
    (e : (free.{u, v} k).obj σ ≅ P.left) :
    Module.Basis σ A (cotangent k A (polynomialPresentationOver k A P σ e)) := by
  letI : Algebra (MvPolynomial σ k) A := (e.hom ≫ P.hom).hom.toRingHom.toAlgebra
  exact (KaehlerDifferential.mvPolynomialBasis k σ).baseChange A

/-- Let `k` be a commutative ring, `A` a `k`-algebra, and `P∈Over A` with polynomial presentation
`e : Free_k(σ) ≅ P.left`. Then `cotangent k A P` is a projective object of `ModuleCat A`. The
basis of the presented linearization transports along the algebra presentation. -/
theorem polynomialCotangent_projective (P : Over A) (σ : Type (max u v))
    (e : (free.{u, v} k).obj σ ≅ P.left) : Projective (cotangent k A P) := by
  let eOver : polynomialPresentationOver k A P σ e ≅ P := Over.isoMk e rfl
  have hpoly : Projective (cotangent k A (polynomialPresentationOver k A P σ e)) :=
    ModuleCat.projective_of_free (polynomialCotangentBasis k A P σ e)
  exact Projective.of_iso ((cotangentFunctor k A).mapIso eOver) hpoly

/-- Let `k` be a commutative ring, `A` a `k`-algebra, `P∈Over A`, and `n : ℕ`. The object
`polynomialResolutionDegreeOver k A P n` is the degree-`n` algebra of the polynomial
resolution of `P.left`, over `A` via its resolution augmentation `P_n→P.left` followed by
`P.hom`. -/
def polynomialResolutionDegreeOver (P : Over A) (n : ℕ) : Over A :=
  (Over.lift (polynomialResolution.{u, v} k P.left).left
    ((polynomialResolution.{u, v} k P.left).hom ≫
      (SimplicialObject.const (CommAlgCat.{max u v} k)).map P.hom)).obj (op ⦋n⦌)

/-- Let `k` be a commutative ring, `A` a `k`-algebra, `P∈Over A`, and `n : ℕ`. The degree-`n`
module of `polynomialCotangentSimplicialFunctor k A P` is projective over `A`. Its algebra
source is the polynomial degree `T^{n+1}(P.left)` with its composed augmentation to `A`. -/
theorem polynomialCotangentDegree_projective (P : Over A) (n : ℕ) :
    Projective (((polynomialCotangentSimplicialFunctor k A).obj P).obj (op ⦋n⦌)) :=
  polynomialCotangent_projective k A (polynomialResolutionDegreeOver k A P n)
    ((polynomialPower.{u, v} k n).obj P.left)
    (polynomialResolutionObjIso.{u, v} k P.left n).symm

/-- Let `k` be a commutative ring, `A` a `k`-algebra, and `P∈Over A`. The normalized polynomial
cotangent chain complex is a retract of its alternating-face chain complex. The inclusion is
`inclusionOfMooreComplexMap`, the retraction is `DoldKan.PInftyToNormalizedMooreComplex`, and
their composite on the normalized complex is the identity. -/
def polynomialCotangentNormalizationRetract (P : Over A) :
    Retract ((polynomialCotangentChainFunctor k A).obj P)
      ((polynomialCotangentAlternatingFunctor k A).obj P) where
  i := inclusionOfMooreComplexMap ((polynomialCotangentSimplicialFunctor k A).obj P)
  r := DoldKan.PInftyToNormalizedMooreComplex ((polynomialCotangentSimplicialFunctor k A).obj P)
  retract := (DoldKan.splitMonoInclusionOfMooreComplexMap
    ((polynomialCotangentSimplicialFunctor k A).obj P)).id

/-- Let `k` be a commutative ring, `A` a `k`-algebra, `P∈Over A`, and `n : ℕ`. The term
`((polynomialCotangentChainFunctor k A).obj P).X n` is a projective `A`-module. It is a
retract of the degree-`n` simplicial polynomial cotangent module, which is projective. -/
theorem polynomialCotangentNormalizedDegree_projective (P : Over A) (n : ℕ) :
    Projective (((polynomialCotangentChainFunctor k A).obj P).X n) := by
  letI : Projective (((polynomialCotangentAlternatingFunctor k A).obj P).X n) :=
    polynomialCotangentDegree_projective k A P n
  letI : Projective
      ((HomologicalComplex.eval (ModuleCat.{max u v} A) (ComplexShape.down ℕ) n).obj
        ((polynomialCotangentAlternatingFunctor.{u, v} k A).obj P)) := by
    change Projective (((polynomialCotangentAlternatingFunctor.{u, v} k A).obj P).X n)
    exact polynomialCotangentDegree_projective.{u, v} k A P n
  exact ((polynomialCotangentNormalizationRetract.{u, v} k A P).map
    (HomologicalComplex.eval (ModuleCat.{max u v} A) (ComplexShape.down ℕ) n)).projective

/-- For a commutative ring `k : Type u`, `A : CommAlgCat.{max u v} k`, and every `n : ℕ`, the term
`(cotangentComplex k A).X n` is a projective object of `ModuleCat A`. This is the normalized
polynomial model at the identity algebra `A→A`. -/
theorem cotangentComplex_term_projective (n : ℕ) :
    Projective ((cotangentComplex k A).X n) :=
  polynomialCotangentNormalizedDegree_projective k A (Over.mk (𝟙 A)) n

/-- For a commutative ring `k : Type u`, `A : CommAlgCat.{max u v} k`, and every `n : ℕ`,
`Module.Flat A ((cotangentComplex k A).X n)` holds. Flatness is obtained from the projectivity
of each normalized term over `A`. -/
theorem cotangentComplex_term_flat (n : ℕ) :
    Module.Flat A ((cotangentComplex k A).X n) := by
  letI : Projective ((cotangentComplex k A).X n) := cotangentComplex_term_projective k A n
  letI : Module.Projective A ((cotangentComplex k A).X n) := inferInstance
  infer_instance

end CommAlgCat

end

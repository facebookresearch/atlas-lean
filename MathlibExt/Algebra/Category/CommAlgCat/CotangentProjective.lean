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
# Projectivity of the actual normalized polynomial cotangent terms

An actual polynomial presentation of `P` gives a basis of its linearization
over an arbitrary target `A`. Each degree of the canonical polynomial cotangent
simplicial object has such a presentation supplied by the native polynomial
resolution. The native split Moore inclusion exhibits each normalized term as
a retract of the corresponding free term. This proves projectivity and flatness
without a condition on the coefficient module.

Reference: Stacks Project 92.3–92.4, the actual free polynomial differential
modules. Candidate source; UNEXECUTED.
-/

@[expose] public section

noncomputable section

open CategoryTheory Opposite AlgebraicTopology
open scoped Simplicial

universe u v

namespace CommAlgCat

variable (k : Type u) [CommRing k] (A : CommAlgCat.{max u v} k)

attribute [local instance] cotangentAlgebra cotangentScalarTower

/-- The polynomial source with the actual augmentation of its presentation. -/
def polynomialPresentationOver (P : Over A) (σ : Type (max u v))
    (e : (free.{u, v} k).obj σ ≅ P.left) : Over A :=
  Over.mk (e.hom ≫ P.hom)

/-- The native basis after extension along the actual presented augmentation. -/
def polynomialCotangentBasis (P : Over A) (σ : Type (max u v))
    (e : (free.{u, v} k).obj σ ≅ P.left) :
    Module.Basis σ A (cotangent k A (polynomialPresentationOver k A P σ e)) := by
  letI : Algebra (MvPolynomial σ k) A := (e.hom ≫ P.hom).hom.toRingHom.toAlgebra
  exact (KaehlerDifferential.mvPolynomialBasis k σ).baseChange A

/-- Polynomial linearization is projective over an arbitrary final target. -/
theorem polynomialCotangent_projective (P : Over A) (σ : Type (max u v))
    (e : (free.{u, v} k).obj σ ≅ P.left) : Projective (cotangent k A P) := by
  let eOver : polynomialPresentationOver k A P σ e ≅ P := Over.isoMk e rfl
  have hpoly : Projective (cotangent k A (polynomialPresentationOver k A P σ e)) :=
    ModuleCat.projective_of_free (polynomialCotangentBasis k A P σ e)
  exact Projective.of_iso ((cotangentFunctor k A).mapIso eOver) hpoly

/-- The actual degree object with its composed augmentation over `A`. -/
def polynomialResolutionDegreeOver (P : Over A) (n : ℕ) : Over A :=
  (Over.lift (polynomialResolution.{u, v} k P.left).left
    ((polynomialResolution.{u, v} k P.left).hom ≫
      (SimplicialObject.const (CommAlgCat.{max u v} k)).map P.hom)).obj (op ⦋n⦌)

/-- Each actual polynomial cotangent degree is projective. -/
theorem polynomialCotangentDegree_projective (P : Over A) (n : ℕ) :
    Projective (((polynomialCotangentSimplicialFunctor k A).obj P).obj (op ⦋n⦌)) :=
  polynomialCotangent_projective k A (polynomialResolutionDegreeOver k A P n)
    ((polynomialPower.{u, v} k n).obj P.left)
    (polynomialResolutionObjIso.{u, v} k P.left n).symm

/-- Native normalization is an actual retract of the alternating complex. -/
def polynomialCotangentNormalizationRetract (P : Over A) :
    Retract ((polynomialCotangentChainFunctor k A).obj P)
      ((polynomialCotangentAlternatingFunctor k A).obj P) where
  i := inclusionOfMooreComplexMap ((polynomialCotangentSimplicialFunctor k A).obj P)
  r := DoldKan.PInftyToNormalizedMooreComplex ((polynomialCotangentSimplicialFunctor k A).obj P)
  retract := (DoldKan.splitMonoInclusionOfMooreComplexMap
    ((polynomialCotangentSimplicialFunctor k A).obj P)).id

/-- Every normalized polynomial cotangent term is projective, by its actual
degreewise retract from a free polynomial differential module. -/
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

/-- The actual canonical cotangent complex has projective terms. -/
theorem cotangentComplex_term_projective (n : ℕ) :
    Projective ((cotangentComplex k A).X n) :=
  polynomialCotangentNormalizedDegree_projective k A (Over.mk (𝟙 A)) n

/-- Each actual cotangent term is flat; no coefficient flatness is assumed. -/
theorem cotangentComplex_term_flat (n : ℕ) :
    Module.Flat A ((cotangentComplex k A).X n) := by
  letI : Projective ((cotangentComplex k A).X n) := cotangentComplex_term_projective k A n
  letI : Module.Projective A ((cotangentComplex k A).X n) := inferInstance
  infer_instance

end CommAlgCat

end

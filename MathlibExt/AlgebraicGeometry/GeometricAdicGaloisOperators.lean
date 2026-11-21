/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions are adapted from AxiomMath/Stacks at
c496df0d9beea9deaeabcea8492605f9a0a2313b, licensed under Apache 2.0:
StacksFrontier/AlgebraicGeometry/EtaleCohomology/Trace/ArithmeticFrobeniusInverse.lean,
StacksFrontier/AlgebraicGeometry/EtaleCohomology/Trace/GaloisActionFibreCohomology.lean.
These source files have no individual author or copyright notice.
Modification notice: retain the actual scheme pullback and contravariant
Spec convention; apply native continuous-coefficient pro-étale cohomology.
-/

module

public import MathlibExt.AlgebraicGeometry.ProEtaleCohomologyFunctoriality
public import MathlibExt.AlgebraicGeometry.FrobeniusGeometry
public import Mathlib.Algebra.Module.ULift
public import Mathlib.FieldTheory.KrullTopology
public import Mathlib.NumberTheory.Padics.PadicNumbers

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

/-!
# Actual Galois and geometric Frobenius operators on adic cohomology

The scheme automorphism attached to σ is id_X × Spec σ. The arithmetic
Frobenius convention is σ(x)=x^q; its inverse is geometric Galois Frobenius.
The geometric scheme Frobenius is π_X × id on the geometric fibre. Each
cohomology operator is the actual normalized inverse-image map, not a
separately selected representation or endomorphism.
-/

namespace MathlibExt.AlgebraicGeometry.GeometricAdicGaloisOperators

open CategoryTheory CategoryTheory.Limits Opposite
open _root_.AlgebraicGeometry _root_.AlgebraicGeometry.Scheme
open MathlibExt.AlgebraicGeometry.ContinuousAdicCoefficients
open MathlibExt.AlgebraicGeometry.ProEtaleCohomologyFunctoriality
open MathlibExt.AlgebraicGeometry.FrobeniusGeometry

universe u

/-- The actual map of spectra induced by the coefficient field inclusion. -/
abbrev fieldMap (k K : Type u) [Field k] [Field K] [Algebra k K] :
    Spec (.of K) ⟶ Spec (.of k) :=
  Spec.map (CommRingCat.ofHom (algebraMap k K))

variable {k : Type u} [Field k] (X : Over (Spec (.of k)))
  (K : Type u) [Field K] [Algebra k K]

/-- The actual geometric base change X_K. -/
abbrev geometricFibre : Scheme.{u} := Limits.pullback X.hom (fieldMap k K)

/-- The actual scheme automorphism id_X × Spec σ. -/
def galoisSchemeOperator (σ : K ≃ₐ[k] K) : geometricFibre X K ⟶ geometricFibre X K :=
  Limits.pullback.lift (Limits.pullback.fst _ _)
    (Limits.pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom σ.toAlgHom.toRingHom))
    (by
      have h : CommRingCat.ofHom (algebraMap k K) ≫
          CommRingCat.ofHom σ.toAlgHom.toRingHom =
            CommRingCat.ofHom (algebraMap k K) := by
        ext x
        exact σ.commutes x
      rw [Category.assoc, ← Spec.map_comp, h]
      exact Limits.pullback.condition)

@[reassoc (attr := simp)]
theorem galoisSchemeOperator_fst (σ : K ≃ₐ[k] K) :
    galoisSchemeOperator X K σ ≫ Limits.pullback.fst X.hom (fieldMap k K) =
      Limits.pullback.fst X.hom (fieldMap k K) := Limits.pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem galoisSchemeOperator_snd (σ : K ≃ₐ[k] K) :
    galoisSchemeOperator X K σ ≫ Limits.pullback.snd X.hom (fieldMap k K) =
      Limits.pullback.snd X.hom (fieldMap k K) ≫
        Spec.map (CommRingCat.ofHom σ.toAlgHom.toRingHom) :=
  Limits.pullback.lift_snd _ _ _

@[simp]
theorem galoisSchemeOperator_one : galoisSchemeOperator X K (1 : K ≃ₐ[k] K) = 𝟙 _ := by
  refine Limits.pullback.hom_ext ?_ ?_
  · simp
  · rw [galoisSchemeOperator_snd, Category.id_comp,
      show CommRingCat.ofHom (AlgEquiv.toAlgHom (1 : K ≃ₐ[k] K)).toRingHom =
        𝟙 (CommRingCat.of K) from rfl, Spec.map_id, Category.comp_id]

/-- Spec reverses ordinary composition, so cohomological inverse image
along this convention gives a left Galois action. -/
theorem galoisSchemeOperator_mul (σ τ : K ≃ₐ[k] K) :
    galoisSchemeOperator X K (σ * τ) =
      galoisSchemeOperator X K σ ≫ galoisSchemeOperator X K τ := by
  refine Limits.pullback.hom_ext ?_ ?_
  · simp
  · rw [galoisSchemeOperator_snd, Category.assoc, galoisSchemeOperator_snd,
      galoisSchemeOperator_snd_assoc, ← Spec.map_comp]
    rfl

def galoisSchemeIso (σ : K ≃ₐ[k] K) : geometricFibre X K ≅ geometricFibre X K where
  hom := galoisSchemeOperator X K σ
  inv := galoisSchemeOperator X K σ⁻¹
  hom_inv_id := by rw [← galoisSchemeOperator_mul, mul_inv_cancel, galoisSchemeOperator_one]
  inv_hom_id := by rw [← galoisSchemeOperator_mul, inv_mul_cancel, galoisSchemeOperator_one]

/-- The actual geometric q-Frobenius on X_K, fixing K on the second factor. -/
def geometricFrobeniusSchemeOperator [Fintype k] (p f : ℕ) [Fact p.Prime]
    [CharP k p] (hcard : Fintype.card k = p ^ f) :
    geometricFibre X K ⟶ geometricFibre X K :=
  Limits.pullback.lift
    (Limits.pullback.fst _ _ ≫ (geometricFrobenius X p f hcard).left)
    (Limits.pullback.snd _ _)
    (by rw [Category.assoc, Over.w]; exact Limits.pullback.condition)

section Coefficients

variable (ell : ℕ) [Fact ell.Prime]

/-- The actual topological rational coefficient module in the site universe. -/
abbrev RationalCoefficients := ULift.{u + 1} ℚ_[ell]

instance rationalCoefficientContinuousSMul :
    ContinuousConstSMul ℚ_[ell] (RationalCoefficients.{u} ell) where
  continuous_const_smul r :=
    continuous_uliftUp.comp ((continuous_const_smul (T := ℚ_[ell]) r).comp
      continuous_uliftDown)

/-- Rational adic cohomology of the actual continuous coefficient sheaf. -/
abbrev AdicCohomology (Y : Scheme.{u}) (n : ℕ) :=
  Cohomology ℚ_[ell] Y
    (continuousModuleSheaf ℚ_[ell] (RationalCoefficients.{u} ell) Y) n

/-- Galois operator, fixed by the scheme automorphism and actual inverse image. -/
def galoisCohomologyOperator (σ : K ≃ₐ[k] K) (n : ℕ) :
    AdicCohomology ell (geometricFibre X K) n →+
      AdicCohomology ell (geometricFibre X K) n :=
  continuousCohomologyPullback ℚ_[ell] (RationalCoefficients.{u} ell)
    (galoisSchemeOperator X K σ) n

/-- Geometric scheme Frobenius operator on actual continuous adic cohomology. -/
def geometricFrobeniusCohomologyOperator [Fintype k] (p f : ℕ) [Fact p.Prime]
    [CharP k p] (hcard : Fintype.card k = p ^ f) (n : ℕ) :
    AdicCohomology ell (geometricFibre X K) n →+
      AdicCohomology ell (geometricFibre X K) n :=
  continuousCohomologyPullback ℚ_[ell] (RationalCoefficients.{u} ell)
    (geometricFrobeniusSchemeOperator X K p f hcard) n

end Coefficients

end MathlibExt.AlgebraicGeometry.GeometricAdicGaloisOperators

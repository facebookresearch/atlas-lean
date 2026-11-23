/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`StacksFrontier/AlgebraicGeometry/EtaleCohomology/Trace/ArithmeticFrobeniusInverse.lean` and
`StacksFrontier/AlgebraicGeometry/EtaleCohomology/Trace/GaloisActionFibreCohomology.lean`
(AxiomMath/Stacks, revision c496df0d9beea9deaeabcea8492605f9a0a2313b):
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
Modifications: use the scheme pullback and the contravariant `Spec` convention, with
continuous-coefficient pro-étale cohomology.
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
# Galois and geometric Frobenius operators on `ℓ`-adic cohomology

For a scheme `X` over a field `k` and an extension `K/k`, an automorphism `σ` of `K` over `k` acts
on the base change `X_K` by `id_X × Spec σ` (`galoisSchemeOperator`), and on its rational `ℓ`-adic
cohomology (the cohomology of the pro-étale sheaf `C(-, ℚ_ℓ)`) by inverse image
(`galoisCohomologyOperator`), an additive endomorphism. The identity and composition laws are
proved for the scheme automorphisms (`galoisSchemeOperator_one`, `galoisSchemeOperator_mul`): since
`Spec` reverses composition, the operators on cohomology form a left action once inverse image is
known to be functorial on cohomology, which is not proved here. For `k` finite with `q` elements,
the geometric Frobenius of `X` induces `π_X × id` on `X_K` (`geometricFrobeniusSchemeOperator`) and
an additive endomorphism of cohomology. When `K` is a separable closure of `k`, the arithmetic
Frobenius `x ↦ x ^ q` is an automorphism of `K` over `k`, and its inverse is the geometric Frobenius
element of the Galois group.
-/

namespace MathlibExt.AlgebraicGeometry.GeometricAdicGaloisOperators

open CategoryTheory CategoryTheory.Limits Opposite
open _root_.AlgebraicGeometry _root_.AlgebraicGeometry.Scheme
open MathlibExt.AlgebraicGeometry.ContinuousAdicCoefficients
open MathlibExt.AlgebraicGeometry.ProEtaleCohomologyFunctoriality
open MathlibExt.AlgebraicGeometry.FrobeniusGeometry

universe u

/-- The morphism `Spec K ⟶ Spec k` induced by a field extension. -/
abbrev fieldMap (k K : Type u) [Field k] [Field K] [Algebra k K] :
    Spec (.of K) ⟶ Spec (.of k) :=
  Spec.map (CommRingCat.ofHom (algebraMap k K))

variable {k : Type u} [Field k] (X : Over (Spec (.of k)))
  (K : Type u) [Field K] [Algebra k K]

/-- The base change `X_K` of `X` to `K`. -/
abbrev geometricFibre : Scheme.{u} := Limits.pullback X.hom (fieldMap k K)

/-- The automorphism `id_X × Spec σ` of `X_K`. -/
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

/-- `id_X × Spec σ` as an automorphism of `X_K`, with inverse `id_X × Spec σ⁻¹`. -/
def galoisSchemeIso (σ : K ≃ₐ[k] K) : geometricFibre X K ≅ geometricFibre X K where
  hom := galoisSchemeOperator X K σ
  inv := galoisSchemeOperator X K σ⁻¹
  hom_inv_id := by rw [← galoisSchemeOperator_mul, mul_inv_cancel, galoisSchemeOperator_one]
  inv_hom_id := by rw [← galoisSchemeOperator_mul, inv_mul_cancel, galoisSchemeOperator_one]

/-- The geometric Frobenius `π_X × id` of `X_K`, for `k` finite with `q = p ^ f` elements. -/
def geometricFrobeniusSchemeOperator [Fintype k] (p f : ℕ) [Fact p.Prime]
    [CharP k p] (hcard : Fintype.card k = p ^ f) :
    geometricFibre X K ⟶ geometricFibre X K :=
  Limits.pullback.lift
    (Limits.pullback.fst _ _ ≫ (geometricFrobenius X p f hcard).left)
    (Limits.pullback.snd _ _)
    (by rw [Category.assoc, Over.w]; exact Limits.pullback.condition)

section Coefficients

variable (ell : ℕ) [Fact ell.Prime]

/-- The topological coefficient module `ℚ_ℓ`, lifted to the universe of the site. -/
abbrev RationalCoefficients := ULift.{u + 1} ℚ_[ell]

/-- Rational `ℓ`-adic cohomology: the cohomology of the pro-étale sheaf `C(-, ℚ_ℓ)`. -/
abbrev AdicCohomology (Y : Scheme.{u}) (n : ℕ) :=
  Cohomology ℚ_[ell] Y
    (continuousModuleSheaf ℚ_[ell] (RationalCoefficients.{u} ell) Y) n

/-- The action of `σ` on cohomology: inverse image along `id_X × Spec σ`. -/
def galoisCohomologyOperator (σ : K ≃ₐ[k] K) (n : ℕ) :
    AdicCohomology ell (geometricFibre X K) n →+
      AdicCohomology ell (geometricFibre X K) n :=
  continuousCohomologyPullback ℚ_[ell] (RationalCoefficients.{u} ell)
    (galoisSchemeOperator X K σ) n

/-- The geometric Frobenius on cohomology: inverse image along `π_X × id`. -/
def geometricFrobeniusCohomologyOperator [Fintype k] (p f : ℕ) [Fact p.Prime]
    [CharP k p] (hcard : Fintype.card k = p ^ f) (n : ℕ) :
    AdicCohomology ell (geometricFibre X K) n →+
      AdicCohomology ell (geometricFibre X K) n :=
  continuousCohomologyPullback ℚ_[ell] (RationalCoefficients.{u} ell)
    (geometricFrobeniusSchemeOperator X K p f hcard) n

end Coefficients

end MathlibExt.AlgebraicGeometry.GeometricAdicGaloisOperators

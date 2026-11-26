/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
The closure-norm proof is adapted from TauCetiProject/TauCeti at
62bbc0596dc3539d488232e4e924a338548ea0a9,
TauCeti/NumberTheory/Padics/AlgebraicClosure.lean, AlgEquiv.norm_apply.
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in that repository's LICENSE.
Authors: The Tau Ceti contributors.
Modification: retain the norm/isometry argument and use Mathlib's actual
completion ring-equivalence construction to obtain the C_p Galois action.
-/
module

public import Mathlib.NumberTheory.Padics.Complex
public import Mathlib.NumberTheory.Cyclotomic.CyclotomicCharacter
public import Mathlib.Topology.Algebra.UniformRing
public import Mathlib.LinearAlgebra.TensorProduct.Map
public import MathlibExt.AlgebraicGeometry.AlgebraicDifferentialSheaves
public import MathlibExt.AlgebraicGeometry.AdicLinearFunctoriality
public import MathlibExt.AlgebraicGeometry.GeometricAdicGaloisOperators
public import MathlibExt.AlgebraicGeometry.CoherentCurveLinearSeries

/-!
# Actual carriers and actions for Hodge–Tate comparison

The left side is C_p tensored with actual continuous rational pro-étale
cohomology of the geometric scheme fibre. The right side is a finite
product of C_p tensored with actual coherent cohomology of the constructed
algebraic differential-form sheaves. Tate twists use Mathlib's constructed
cyclotomic character, characterized by its actual roots-of-unity action.

Galois acts on C_p by completing its actual norm-preserving action on
the algebraic closure; this is a group action (`completionGaloisHom`). It
acts on étale cohomology by inverse image along the scheme automorphism
`id_X × Spec σ` of `GeometricAdicGaloisOperators`, and on the Hodge side
by the completed action twisted by `χ^(-i)` in Hodge degree `i`. The Hodge
operators form a semilinear group action (`completedHodgeGalois_one`,
`completedHodgeGalois_mul`, `completedHodgeGalois_smul`). The completed
étale operators are semilinear (`completedEtaleGalois_smul`) and inherit
the action laws from those of the étale operators
(`completedEtaleGalois_one`, `completedEtaleGalois_mul`); the identity law
of the étale inverse images themselves is proved in
`HodgeTateComparisonEtaleGaloisOne`, and their composition law is
`WantedExt.AlgebraicGeometry.HodgeTateComparison.etaleGalois_mul`. The
geometric comparison is a separate construction.
-/

@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.HodgeTateComparison

open _root_.CategoryTheory _root_.AlgebraicGeometry
open GeometricAdicGaloisOperators AdicLinearFunctoriality
open CoherentCurveLinearSeries
open scoped TensorProduct

variable (p : ℕ) [Fact p.Prime]

abbrev Galois := PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p

/-- Galois preserves the actual spectral norm on the algebraic closure. -/
theorem closure_norm_apply (σ : Galois p) (x : PadicAlgCl p) :
    ‖σ x‖ = ‖x‖ := by
  rw [← PadicAlgCl.spectralNorm_eq, ← PadicAlgCl.spectralNorm_eq]
  exact (spectralNorm_eq_of_equiv σ x).symm

theorem closure_isometry (σ : Galois p) : Isometry σ := by
  refine isometry_iff_dist_eq.mpr fun x y => ?_
  rw [dist_eq_norm, ← map_sub σ, closure_norm_apply, dist_eq_norm]

/-- Complete the actual field automorphism, fixing Q_p. -/
def completionGalois (σ : Galois p) :
    PadicComplex p ≃ₐ[ℚ_[p]] PadicComplex p := by
  let e : PadicComplex p ≃+* PadicComplex p :=
    UniformSpace.Completion.mapRingEquiv σ.toRingEquiv
      (closure_isometry p σ).continuous (closure_isometry p σ.symm).continuous
  refine AlgEquiv.ofBijective
    ({ toRingHom := e.toRingHom
       commutes' := ?_ } : PadicComplex p →ₐ[ℚ_[p]] PadicComplex p)
    e.bijective
  intro r
  change UniformSpace.Completion.mapRingHom σ.toRingEquiv.toRingHom
      (closure_isometry p σ).continuous
      ((algebraMap ℚ_[p] (PadicAlgCl p) r : PadicAlgCl p) :
        PadicComplex p) = algebraMap ℚ_[p] (PadicComplex p) r
  exact (UniformSpace.Completion.mapRingHom_coe
    (f := σ.toRingEquiv.toRingHom) (closure_isometry p σ).continuous
    (algebraMap ℚ_[p] (PadicAlgCl p) r)).trans
      (congrArg (algebraMap (PadicAlgCl p) (PadicComplex p)) (σ.commutes r))

/-- The completed action is fixed on every algebraic-closure element. -/
theorem completionGalois_coe (σ : Galois p) (x : PadicAlgCl p) :
    completionGalois p σ (algebraMap (PadicAlgCl p) (PadicComplex p) x) =
      algebraMap (PadicAlgCl p) (PadicComplex p) (σ x) :=
  UniformSpace.Completion.mapRingHom_coe
    (f := σ.toRingEquiv.toRingHom) (closure_isometry p σ).continuous x

/-- The completed action is continuous. -/
theorem continuous_completionGalois (σ : Galois p) :
    Continuous (completionGalois p σ) :=
  UniformSpace.Completion.continuous_map

/-- The completed action of the identity is the identity. -/
theorem completionGalois_one_apply (x : PadicComplex p) :
    completionGalois p 1 x = x := by
  induction x using UniformSpace.Completion.induction_on with
  | hp => exact isClosed_eq (continuous_completionGalois p 1) continuous_id
  | ih a => exact completionGalois_coe p 1 a

/-- The completed action is multiplicative. -/
theorem completionGalois_mul_apply (σ τ : Galois p) (x : PadicComplex p) :
    completionGalois p (σ * τ) x = completionGalois p σ (completionGalois p τ x) := by
  induction x using UniformSpace.Completion.induction_on with
  | hp =>
    exact isClosed_eq (continuous_completionGalois p (σ * τ))
      ((continuous_completionGalois p σ).comp (continuous_completionGalois p τ))
  | ih a =>
    change completionGalois p (σ * τ) (algebraMap (PadicAlgCl p) (PadicComplex p) a) =
      completionGalois p σ (completionGalois p τ (algebraMap (PadicAlgCl p) (PadicComplex p) a))
    rw [completionGalois_coe, completionGalois_coe, completionGalois_coe, AlgEquiv.mul_apply]

/-- The completed Galois action on `C_p`, as a group homomorphism. -/
def completionGaloisHom : Galois p →* (PadicComplex p ≃ₐ[ℚ_[p]] PadicComplex p) where
  toFun := completionGalois p
  map_one' := AlgEquiv.ext (completionGalois_one_apply p)
  map_mul' σ τ := AlgEquiv.ext (completionGalois_mul_apply p σ τ)

@[simp]
theorem completionGaloisHom_apply (σ : Galois p) :
    completionGaloisHom p σ = completionGalois p σ := rfl

/-- The coefficient is the actual p-adic cyclotomic character. -/
def cyclotomicScalar (σ : Galois p) : ℚ_[p] :=
  algebraMap ℤ_[p] ℚ_[p]
    (cyclotomicCharacter (PadicAlgCl p) p σ.toRingEquiv).val

theorem cyclotomicScalar_ne_zero (σ : Galois p) :
    cyclotomicScalar p σ ≠ 0 :=
  ((cyclotomicCharacter (PadicAlgCl p) p σ.toRingEquiv).isUnit.map
    (algebraMap ℤ_[p] ℚ_[p])).ne_zero

@[simp]
theorem cyclotomicScalar_one : cyclotomicScalar p 1 = 1 := by
  have h : (1 : Galois p).toRingEquiv = 1 := rfl
  simp [cyclotomicScalar, h]

theorem cyclotomicScalar_mul (σ τ : Galois p) :
    cyclotomicScalar p (σ * τ) = cyclotomicScalar p σ * cyclotomicScalar p τ := by
  have h : (σ * τ).toRingEquiv = σ.toRingEquiv * τ.toRingEquiv := rfl
  simp [cyclotomicScalar, h]

/-- The coefficient of the negative Tate twist C_p(-i). -/
def tateScalar (σ : Galois p) (i : ℕ) : ℚ_[p] :=
  cyclotomicScalar p σ ^ (-(i : ℤ))

@[simp]
theorem tateScalar_one (i : ℕ) : tateScalar p 1 i = 1 := by
  simp [tateScalar]

theorem tateScalar_mul (σ τ : Galois p) (i : ℕ) :
    tateScalar p (σ * τ) i = tateScalar p σ i * tateScalar p τ i := by
  rw [tateScalar, tateScalar, tateScalar, cyclotomicScalar_mul, mul_zpow]

variable (X : Over (Spec (CommRingCat.of.{0} ℚ_[p])))

/-- Rational pro-étale cohomology of the geometric fibre $X_{\bar{\mathbb{Q}}_p}$. It is a
separate definition with its own additive and $\mathbb{Q}_p$-module instances, so that the kernel
compares these instances by name instead of unfolding the pro-étale `Ext` instances in every
declaration that mentions them. -/
def Etale (n : ℕ) :=
  AdicCohomology p (geometricFibre X (PadicAlgCl p)) n

instance (n : ℕ) : AddCommGroup (Etale p X n) :=
  inferInstanceAs (AddCommGroup (AdicCohomology p (geometricFibre X (PadicAlgCl p)) n))

instance (n : ℕ) : Module ℚ_[p] (Etale p X n) :=
  inferInstanceAs (Module ℚ_[p] (AdicCohomology p (geometricFibre X (PadicAlgCl p)) n))

abbrev CompletedEtale (n : ℕ) :=
  PadicComplex p ⊗[ℚ_[p]] Etale p X n

/-- Hodge cohomology is the actual right-derived global-section module. -/
abbrev Hodge (n i : ℕ) :=
  cohomology X.hom (AlgebraicDifferentialSheaves.forms ℚ_[p] X i) (n - i)

/-- A finite product realizes the direct sum of cohomological Hodge pieces. -/
abbrev CompletedHodge (n : ℕ) :=
  ∀ i : Fin (n + 1), PadicComplex p ⊗[ℚ_[p]] Hodge p X n i

/-- This is the actual Q_p-linear scheme-cohomology operator. -/
def etaleGalois (σ : Galois p) (n : ℕ) :
    Etale p X n →ₗ[ℚ_[p]] Etale p X n :=
  continuousPullbackLinear ℚ_[p] (RationalCoefficients.{0} p)
    (galoisSchemeOperator X (PadicAlgCl p) σ) n

theorem etaleGalois_apply (σ : Galois p) (n : ℕ) (a : Etale p X n) :
    etaleGalois p X σ n a =
      galoisCohomologyOperator X (PadicAlgCl p) p σ n a := rfl

/-- The diagonal action uses the actual two factors' operators. -/
def completedEtaleGalois (σ : Galois p) (n : ℕ) :
    CompletedEtale p X n →ₗ[ℚ_[p]] CompletedEtale p X n :=
  TensorProduct.map (completionGalois p σ).toLinearMap (etaleGalois p X σ n)

/-- The completed étale operators are semilinear over the completed action on `C_p`. -/
theorem completedEtaleGalois_smul (σ : Galois p) (n : ℕ) (c : PadicComplex p)
    (a : CompletedEtale p X n) :
    completedEtaleGalois p X σ n (c • a) =
      completionGalois p σ c • completedEtaleGalois p X σ n a := by
  induction a using TensorProduct.inductionOn with
  | tmul x m =>
    rw [TensorProduct.smul_tmul', completedEtaleGalois, TensorProduct.map_tmul,
      TensorProduct.map_tmul, TensorProduct.smul_tmul']
    simp
  | add a b ha hb => rw [smul_add, map_add, ha, hb, map_add, smul_add]

/-- The completed étale operators inherit the identity law of the étale operators. -/
theorem completedEtaleGalois_one (n : ℕ) (h : etaleGalois p X 1 n = LinearMap.id) :
    completedEtaleGalois p X 1 n = LinearMap.id := by
  rw [completedEtaleGalois, h]
  have hc : (completionGalois p 1).toLinearMap = LinearMap.id :=
    LinearMap.ext (completionGalois_one_apply p)
  rw [hc, TensorProduct.map_id]

/-- The completed étale operators inherit the composition law of the étale operators. -/
theorem completedEtaleGalois_mul (σ τ : Galois p) (n : ℕ)
    (h : etaleGalois p X (σ * τ) n = etaleGalois p X σ n ∘ₗ etaleGalois p X τ n) :
    completedEtaleGalois p X (σ * τ) n =
      completedEtaleGalois p X σ n ∘ₗ completedEtaleGalois p X τ n := by
  rw [completedEtaleGalois, completedEtaleGalois, completedEtaleGalois, ← TensorProduct.map_comp, h]
  congr 1
  exact LinearMap.ext (completionGalois_mul_apply p σ τ)

/-- Galois acts on Hodge degree i by its actual C_p action and χ^(-i). -/
def completedHodgeGalois (σ : Galois p) (n : ℕ) :
    CompletedHodge p X n →ₗ[ℚ_[p]] CompletedHodge p X n :=
  LinearMap.pi fun i =>
    (TensorProduct.map
      (tateScalar p σ i • (completionGalois p σ).toLinearMap)
      (LinearMap.id : Hodge p X n i →ₗ[ℚ_[p]] Hodge p X n i)).comp
        (LinearMap.proj i)

/-- The Hodge-side operator of the identity is the identity. -/
theorem completedHodgeGalois_one (n : ℕ) :
    completedHodgeGalois p X 1 n = LinearMap.id := by
  apply LinearMap.ext
  intro a
  funext i
  have hc : tateScalar p 1 i • (completionGalois p 1).toLinearMap = LinearMap.id := by
    ext c
    simp [completionGalois_one_apply]
  simp only [completedHodgeGalois, LinearMap.pi_apply, LinearMap.comp_apply, LinearMap.proj_apply,
    LinearMap.id_apply, hc, TensorProduct.map_id]

/-- The Hodge-side operators compose as a left action. -/
theorem completedHodgeGalois_mul (σ τ : Galois p) (n : ℕ) :
    completedHodgeGalois p X (σ * τ) n =
      completedHodgeGalois p X σ n ∘ₗ completedHodgeGalois p X τ n := by
  apply LinearMap.ext
  intro a
  funext i
  have hc : tateScalar p (σ * τ) i • (completionGalois p (σ * τ)).toLinearMap =
      (tateScalar p σ i • (completionGalois p σ).toLinearMap) ∘ₗ
        (tateScalar p τ i • (completionGalois p τ).toLinearMap) := by
    ext c
    change tateScalar p (σ * τ) i • completionGalois p (σ * τ) c =
      tateScalar p σ i • completionGalois p σ (tateScalar p τ i • completionGalois p τ c)
    rw [completionGalois_mul_apply, tateScalar_mul,
      Algebra.smul_def (tateScalar p τ i) (completionGalois p τ c), map_mul,
      AlgEquiv.commutes, ← Algebra.smul_def, smul_smul]
  have hmap : TensorProduct.map (tateScalar p (σ * τ) i • (completionGalois p (σ * τ)).toLinearMap)
      (LinearMap.id : Hodge p X n i →ₗ[ℚ_[p]] Hodge p X n i) =
      TensorProduct.map (tateScalar p σ i • (completionGalois p σ).toLinearMap) LinearMap.id ∘ₗ
        TensorProduct.map (tateScalar p τ i • (completionGalois p τ).toLinearMap) LinearMap.id := by
    rw [← TensorProduct.map_comp, ← hc, LinearMap.id_comp]
  simp only [completedHodgeGalois, LinearMap.pi_apply, LinearMap.comp_apply, LinearMap.proj_apply]
  rw [hmap, LinearMap.comp_apply]

/-- The Hodge-side operators are semilinear over the completed action on `C_p`. -/
theorem completedHodgeGalois_smul (σ : Galois p) (n : ℕ) (c : PadicComplex p)
    (a : CompletedHodge p X n) :
    completedHodgeGalois p X σ n (c • a) =
      completionGalois p σ c • completedHodgeGalois p X σ n a := by
  funext i
  simp only [completedHodgeGalois, LinearMap.pi_apply, LinearMap.comp_apply,
    LinearMap.proj_apply, Pi.smul_apply]
  induction a i using TensorProduct.inductionOn with
  | tmul x m =>
    rw [TensorProduct.smul_tmul', TensorProduct.map_tmul, TensorProduct.map_tmul,
      TensorProduct.smul_tmul']
    simp
  | add a b ha hb => rw [smul_add, map_add, ha, hb, map_add, smul_add]

/-- A geometric comparison on the actual carriers, with all Galois
operators fixed before the comparison is supplied. The Hodge-side
operators form a semilinear group action, and the completed étale
operators are semilinear; equivariance is stated against these fixed
operators. -/
structure Comparison (n : ℕ) where
  equivalence : CompletedEtale p X n ≃ₗ[PadicComplex p] CompletedHodge p X n
  equivariant : ∀ (σ : Galois p) (a : CompletedEtale p X n),
    equivalence (completedEtaleGalois p X σ n a) =
      completedHodgeGalois p X σ n (equivalence a)

end MathlibExt.AlgebraicGeometry.HodgeTateComparison

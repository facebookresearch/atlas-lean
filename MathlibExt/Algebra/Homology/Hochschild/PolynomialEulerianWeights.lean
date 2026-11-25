/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/



module

public import MathlibExt.Algebra.Homology.Hochschild.PolynomialEulerianRepresentatives
public import MathlibExt.Algebra.Homology.Hochschild.PolynomialNormalizedExterior
public import MathlibExt.Algebra.Homology.Hochschild.NormalizedEulerianHodge
public import MathlibExt.LinearAlgebra.TensorPower.EulerianAntisymmetrization

/-!
# Eulerian weights of polynomial Hochschild homology

Signed polynomial antisymmetric
representatives in degree n have Eulerian
weight n. The polynomial homology
comparison identifies the raw and
normalized projectors with that weight.
The projectors require a rational
ground algebra; the polynomial comparison
itself is characteristic free.
-/

@[expose] public section
noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

universe u v w

namespace ModuleCat.Algebra.Hochschild.PolynomialDiagonal

variable (k : Type u) [CommRing k] [Algebra ℚ k] (σ : Type v)
  (M : Type w) [AddCommGroup M] [Module k M] [Module (MvPolynomial σ k) M]
  [SMulCommClass k (MvPolynomial σ k) M] [IsScalarTower k (MvPolynomial σ k) M]

local notation "A" => MvPolynomial σ k
local notation "V" => σ →₀ k

local instance polynomialEulerianWeightsOpModule : Module Aᵐᵒᵖ M := Symmetric.opModule A M
local instance polynomialEulerianWeightsActionsComm : SMulCommClass A Aᵐᵒᵖ M := Symmetric.actionsComm A M
local instance polynomialEulerianWeightsKOpComm : SMulCommClass k Aᵐᵒᵖ M := Symmetric.kOpComm k A M
local instance polynomialEulerianWeightsKOpTower : IsScalarTower k Aᵐᵒᵖ M := Symmetric.kOpTower k A M

private theorem nativeCycleClass_congr
    {C : ChainComplex (ModuleCat.{max u v w} k) ℕ} (n : ℕ)
    (s t : C.X n) (hs : (C.sc n).g s = 0) (ht : (C.sc n).g t = 0) (hst : s = t) :
    HomologicalComplex.moduleCatCycleClass C n s hs =
      HomologicalComplex.moduleCatCycleClass C n t ht := by
  subst t
  rfl

/-- The rational convolution on an original polynomial signed degree-n tensor has eigenvalue a^n. -/
theorem polynomialSignedRepresentative_convolution
    (n : ℕ) (a : ℚ) (x : M ⊗[k] (⋀[k]^n V)) :
    Symmetric.rationalConvolutionOperator k A M n a (polynomialSignedRepresentative k σ M n x) =
      algebraMap ℚ k (a ^ n) • polynomialSignedRepresentative k σ M n x := by
  classical
  let n₀ : Fin (n + 1) := Fin.last n
  rw [Symmetric.rationalConvolutionOperator_eq_sum, LinearMap.sum_apply]
  simp only [LinearMap.smul_apply, polynomialSignedRepresentative_eulerian]
  rw [Finset.sum_eq_single n₀]
  · simp [n₀]
  · intro j _ hj
    have hne : j.val ≠ n := fun he => hj (Fin.ext he)
    simp only [if_neg hne, smul_zero]
  · simp

/-- The native convolution homology map has the homogeneous eigenvalue on each original polynomial
  class. -/
theorem rationalConvolutionHomology_polynomialClass
    (n : ℕ) (a : ℚ) (x : M ⊗[k] (⋀[k]^n V)) :
    Symmetric.rationalConvolutionHomologyMap k A M n a (polynomialAntisymmetricExteriorClass k σ M n x) =
      algebraMap ℚ k (a ^ n) • polynomialAntisymmetricExteriorClass k σ M n x := by
  let K := Symmetric.chainComplex k A M
  let f : K ⟶ K := Symmetric.rationalConvolutionChainMap k A M a
  let y : K.X n := polynomialSignedRepresentative k σ M n x
  have hy : (K.sc n).g y = 0 := polynomialSignedRepresentative_cycle k σ M n x
  have hClass : polynomialAntisymmetricExteriorClass k σ M n x =
      HomologicalComplex.moduleCatCycleClass K n y hy :=
    polynomialAntisymmetricExteriorClass_eq_cycle k σ M n x
  have hMap := HomologicalComplex.moduleCatCycleClass_naturality f n y hy
  have hf : (f.f n).hom y = algebraMap ℚ k (a ^ n) • y := by
    change Symmetric.rationalConvolutionOperator k A M n a (polynomialSignedRepresentative k σ M n x) =
      algebraMap ℚ k (a ^ n) • polynomialSignedRepresentative k σ M n x
    exact polynomialSignedRepresentative_convolution k σ M n a x
  change (HomologicalComplex.homologyMap f n).hom (polynomialAntisymmetricExteriorClass k σ M n x) =
    algebraMap ℚ k (a ^ n) • polynomialAntisymmetricExteriorClass k σ M n x
  refine (congrArg (HomologicalComplex.homologyMap f n).hom hClass).trans (hMap.trans ?_)
  change HomologicalComplex.moduleCatCycleClass K n ((f.f n).hom y) _ =
    algebraMap ℚ k (a ^ n) • polynomialAntisymmetricExteriorClass k σ M n x
  have hz' : (K.sc n).g (algebraMap ℚ k (a ^ n) • y) = 0 :=
    ((K.sc n).g.hom.map_smul (algebraMap ℚ k (a ^ n)) y).trans (by rw [hy, smul_zero])
  have hz : (K.sc n).g ((f.f n).hom y) = 0 :=
    (congrArg (K.sc n).g.hom hf).trans hz'
  exact (nativeCycleClass_congr.{u, v, w} (k := k) (C := K) n ((f.f n).hom y)
      (algebraMap ℚ k (a ^ n) • y) hz hz' hf).trans
    ((HomologicalComplex.moduleCatCycleClass_smul K n (algebraMap ℚ k (a ^ n)) y hy).trans
      (congrArg (algebraMap ℚ k (a ^ n) • ·) hClass.symm))

/-- Native normalization preserves the top Eulerian weight of the signed polynomial representative. -/
theorem normalizedPolynomialSignedRepresentative_eulerian
    (n i : ℕ) (x : M ⊗[k] (⋀[k]^n V)) :
    Symmetric.normalizedEulerianOperator k A M n i
      (normalizedPolynomialSignedRepresentative k σ M n x) =
        if i = n then normalizedPolynomialSignedRepresentative k σ M n x else 0 := by
  let K := Symmetric.chainComplex k A M
  let L := Symmetric.normalizedChainComplex k A M
  let y : K.X n := polynomialSignedRepresentative k σ M n x
  let P : K.X n →ₗ[k] L.X n := ((Symmetric.normalizationProjection k A M).f n).hom
  let E₀ : K.X n →ₗ[k] K.X n := Symmetric.coefficientEulerianOperator k A M n i
  let E : L.X n →ₗ[k] L.X n := Symmetric.normalizedEulerianOperator k A M n i
  have h := congrArg (fun f : K ⟶ L => (f.f n).hom y)
    (Symmetric.normalizationProjection_eulerian k A M i)
  change P (E₀ y) = E (P y) at h
  have he : E₀ y = if i = n then y else 0 := polynomialSignedRepresentative_eulerian k σ M n i x
  rw [he] at h
  change E (P y) = if i = n then P y else 0
  by_cases hi : i = n
  · rw [if_pos hi] at h ⊢
    exact h.symm
  · rw [if_neg hi] at h ⊢
    exact h.symm.trans P.map_zero

/-- The original homology projector has the exact top weight on every polynomial signed class. -/
theorem eulerianHomologyProjector_polynomialClass
    (n i : ℕ) (x : M ⊗[k] (⋀[k]^n V)) :
    Symmetric.eulerianHomologyProjector k A M n i (polynomialAntisymmetricExteriorClass k σ M n x) =
      if i = n then polynomialAntisymmetricExteriorClass k σ M n x else 0 := by
  let K := Symmetric.chainComplex k A M
  let f : K ⟶ K := Symmetric.eulerianChainMap k A M i
  let y : K.X n := polynomialSignedRepresentative k σ M n x
  have hy : (K.sc n).g y = 0 := polynomialSignedRepresentative_cycle k σ M n x
  have hClass : polynomialAntisymmetricExteriorClass k σ M n x =
      HomologicalComplex.moduleCatCycleClass K n y hy :=
    polynomialAntisymmetricExteriorClass_eq_cycle k σ M n x
  have hMap := HomologicalComplex.moduleCatCycleClass_naturality f n y hy
  have hf : (f.f n).hom y = if i = n then y else 0 := by
    change Symmetric.coefficientEulerianOperator k A M n i (polynomialSignedRepresentative k σ M n x) =
      if i = n then polynomialSignedRepresentative k σ M n x else 0
    exact polynomialSignedRepresentative_eulerian k σ M n i x
  change (HomologicalComplex.homologyMap f n).hom (polynomialAntisymmetricExteriorClass k σ M n x) =
    if i = n then polynomialAntisymmetricExteriorClass k σ M n x else 0
  refine (congrArg (HomologicalComplex.homologyMap f n).hom hClass).trans (hMap.trans ?_)
  change HomologicalComplex.moduleCatCycleClass K n ((f.f n).hom y) _ =
    if i = n then polynomialAntisymmetricExteriorClass k σ M n x else 0
  by_cases hi : i = n
  · rw [if_pos hi]
    have hf' : (f.f n).hom y = y := hf.trans (if_pos hi)
    have hz : (K.sc n).g ((f.f n).hom y) = 0 := (congrArg (K.sc n).g.hom hf').trans hy
    exact (nativeCycleClass_congr.{u, v, w} (k := k) (C := K) n ((f.f n).hom y) y hz hy hf').trans hClass.symm
  · rw [if_neg hi]
    have hf' : (f.f n).hom y = 0 := hf.trans (if_neg hi)
    have hz' : (K.sc n).g (0 : K.X n) = 0 := (K.sc n).g.hom.map_zero
    have hz : (K.sc n).g ((f.f n).hom y) = 0 := (congrArg (K.sc n).g.hom hf').trans hz'
    exact (nativeCycleClass_congr.{u, v, w} (k := k) (C := K) n ((f.f n).hom y) 0 hz hz' hf').trans
      (HomologicalComplex.moduleCatCycleClass_zero K n hz')

/-- The canonical polynomial epsilon isomorphism proves full raw HH purity in every degree. -/
theorem polynomialEulerianHomologyProjector (n i : ℕ) :
    Symmetric.eulerianHomologyProjector k A M n i =
      if i = n then 𝟙 ((Symmetric.chainComplex k A M).homology n) else 0 := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  obtain ⟨ω, rfl⟩ := (polynomialAntisymmetrizationHomologyEquiv k σ M n).surjective z
  let e := polynomialAntisymmetrizationHomologyEquiv k σ M n
  let d := (KaehlerDifferential.mvPolynomialCoefficientExteriorEquiv k σ M n).symm
  have he : e ω = polynomialAntisymmetrizationHomology k σ M n ω :=
    (congrFun (LinearEquiv.coe_toLinearMap e) ω).symm.trans
      (LinearMap.congr_fun (polynomialAntisymmetrizationHomologyEquiv_toLinearMap k σ M n) ω)
  have hd : (d.restrictScalars k).toLinearMap ω = d ω :=
    (congrFun (LinearEquiv.coe_toLinearMap (d.restrictScalars k)) ω).trans
      (LinearEquiv.restrictScalars_apply k d ω)
  have hval : e ω = polynomialAntisymmetricExteriorClass k σ M n (d ω) := by
    refine he.trans ?_
    change polynomialAntisymmetricExteriorClass k σ M n ((d.restrictScalars k).toLinearMap ω) =
      polynomialAntisymmetricExteriorClass k σ M n (d ω)
    exact congrArg (polynomialAntisymmetricExteriorClass k σ M n) hd
  have h := eulerianHomologyProjector_polynomialClass k σ M n i (d ω)
  by_cases hi : i = n
  · rw [if_pos hi, ModuleCat.hom_id, LinearMap.id_apply]
    exact (congrArg (Symmetric.eulerianHomologyProjector k A M n i).hom hval).trans
      ((h.trans (if_pos hi)).trans hval.symm)
  · rw [if_neg hi, ModuleCat.hom_zero, LinearMap.zero_apply]
    exact (congrArg (Symmetric.eulerianHomologyProjector k A M n i).hom hval).trans
      (h.trans (if_neg hi))

/-- Native normalization earns the same full polynomial HH purity on the original normalized homology. -/
theorem normalizedPolynomialEulerianHomologyProjector (n i : ℕ) :
    Symmetric.normalizedEulerianHomologyProjector k A M n i =
      if i = n then 𝟙 ((Symmetric.normalizedChainComplex k A M).homology n) else 0 := by
  apply (cancel_epi (polynomialNormalizationHomologyIso k σ M n).hom).mp
  rw [polynomialNormalizationHomologyIso_hom, ← Symmetric.normalizationHomology_eulerian,
    polynomialEulerianHomologyProjector]
  split_ifs <;> simp only [Category.id_comp, Category.comp_id, zero_comp, comp_zero]

/-- The normalized signed polynomial class has its original top Eulerian homology weight. -/
theorem normalizedEulerianHomologyProjector_polynomialClass
    (n i : ℕ) (x : M ⊗[k] (⋀[k]^n V)) :
    Symmetric.normalizedEulerianHomologyProjector k A M n i
      (normalizedPolynomialExteriorClass k σ M n x) =
        if i = n then normalizedPolynomialExteriorClass k σ M n x else 0 := by
  rw [normalizedPolynomialEulerianHomologyProjector]
  split_ifs <;> rfl

end ModuleCat.Algebra.Hochschild.PolynomialDiagonal

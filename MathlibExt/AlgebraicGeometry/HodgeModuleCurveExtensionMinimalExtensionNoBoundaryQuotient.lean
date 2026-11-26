/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.HodgeModuleCurveExtension
import Mathlib.RingTheory.Nilpotent.Basic
import Mathlib.Tactic.Ring

/-!
# No boundary-supported quotient of the minimal extension

For unipotent rational monodromy `(T - 1)^b = 0` with `b > 0`, the connection
uses the logarithm truncated below degree `b`. A connection-stable submodule
of the constructed minimal extension that agrees with it after inverting
the actual parameter equals the minimal extension.

Sources: M. Saito, *Modules de Hodge polarisables*, Publ. RIMS 24 (1988), §3.2;
C. Schnell, *An overview of Morihiko Saito's theory of mixed Hodge modules*,
https://arxiv.org/abs/1405.3096, §18, Parts 1 and 2.
-/

@[expose] public noncomputable section

open CategoryTheory
open MathlibExt.Geometry.RationalHodgeStructures
open MathlibExt.Geometry.LimitingHodgeStructures
open MathlibExt.AlgebraicGeometry.HodgeModuleCurveExtension

namespace MathlibExt.AlgebraicGeometry.HodgeModuleCurveExtension

private theorem deck_nilpotent
    (V : ModuleCat.{0} ℚ) (C : RationalComplexification V) (r : ℕ)
    (e : C.complexSpace ≃ₗ[ℂ] EuclideanSpace ℂ (Fin r)) (w : ℤ)
    (H : PolarizedPeriodVariation C e w) (b : ℕ)
    (hT : (H.rationalDeck.toLinearMap - 1) ^ b = 0) :
    IsNilpotent (H.complexDeck.toLinearMap - 1) := by
  have hpow (n : ℕ) (v : V) :
      ((H.complexDeck.toLinearMap - 1) ^ n) (C.comparisonMap v) =
        C.comparisonMap (((H.rationalDeck.toLinearMap - 1) ^ n) v) := by
    induction n with
    | zero => simp
    | succ n ih =>
      simp only [pow_succ', mul_apply_eq_comp, ih, LinearMap.sub_apply,
        LinearEquiv.coe_coe, one_apply_eq_self, H.deck_comparison, map_sub]
  refine ⟨b, ?_⟩
  ext x
  induction x using C.baseChange.inductionOn with
  | add x y hx hy => simp [hx, hy]
  | smul c x hx => simp [hx]
  | tmul v => simp [hpow, hT]

private theorem log_nilpotent
    (V : ModuleCat.{0} ℚ) (C : RationalComplexification V) (r : ℕ)
    (e : C.complexSpace ≃ₗ[ℂ] EuclideanSpace ℂ (Fin r)) (w : ℤ)
    (H : PolarizedPeriodVariation C e w) (b : ℕ) (hb : 0 < b)
    (hT : (H.rationalDeck.toLinearMap - 1) ^ b = 0) :
    IsNilpotent (truncatedComplexLog C e H b) := by
  classical
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hb)
  have hN := deck_nilpotent V C r e w H (k + 1) hT
  unfold truncatedComplexLog
  apply Commute.isNilpotent_sum
  · intro i hi
    split_ifs with h
    · exact IsNilpotent.zero
    · exact (hN.pow_of_pos h).smul _
  · intro i j hi hj
    split_ifs <;> first
    | exact Commute.zero_left _
    | exact Commute.zero_right _
    | exact ((Commute.refl _).pow_pow i j).smul_left _ |>.smul_right _

private def constantSection
    (V : ModuleCat.{0} ℚ) (C : RationalComplexification V) (r : ℕ)
    (e : C.complexSpace ≃ₗ[ℂ] EuclideanSpace ℂ (Fin r)) :
    C.complexSpace →ₗ[ℂ] (Fin r → LocalMeromorphicSeries) where
  toFun x i := algebraMap ℂ LocalMeromorphicSeries (e x i)
  map_add' x y := by ext i; simp
  map_smul' c x := by
    funext i
    simp only [map_smul, PiLp.smul_apply, smul_eq_mul, map_mul, Pi.smul_apply]
    rw [LaurentSeries.algebraMap_apply]
    exact HahnSeries.C_mul_eq_smul

private theorem residue_apply
    (V : ModuleCat.{0} ℚ) (C : RationalComplexification V) (r : ℕ)
    (e : C.complexSpace ≃ₗ[ℂ] EuclideanSpace ℂ (Fin r)) (w : ℤ)
    (H : PolarizedPeriodVariation C e w) (b : ℕ) (x : C.complexSpace) (i : Fin r) :
    ∑ j : Fin r, residueMatrix C e H b i j * e x j =
      e (((2 * Real.pi * Complex.I)⁻¹ : ℂ) • truncatedComplexLog C e H b x) i := by
  classical
  have hx : x = ∑ j : Fin r, e x j • e.symm (EuclideanSpace.single j 1) := by
    apply e.injective
    simpa only [map_sum, map_smul, LinearEquiv.apply_symm_apply,
      EuclideanSpace.basisFun_apply, EuclideanSpace.basisFun_repr] using
      ((EuclideanSpace.basisFun (Fin r) ℂ).sum_repr (e x)).symm
  conv_rhs => rw [hx]
  simp only [map_sum, map_smul, PiLp.smul_apply, WithLp.ofLp_sum, Finset.sum_apply, smul_eq_mul,
    residueMatrix, div_eq_mul_inv, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  ring

private def parameter : LocalMeromorphicSeries :=
  algebraMap LocalPowerSeries LocalMeromorphicSeries PowerSeries.X

private theorem parameter_ne_zero : parameter ≠ 0 := by
  change HahnSeries.ofPowerSeries ℤ ℂ PowerSeries.X ≠ 0
  intro h
  have hx : PowerSeries.X = (0 : LocalPowerSeries) :=
    HahnSeries.ofPowerSeries_injective (h.trans (map_zero _).symm)
  exact PowerSeries.X_ne_zero hx

private theorem parameter_monomial (n : ℕ) (c : ℂ) :
    parameter ^ n * algebraMap ℂ LocalMeromorphicSeries c = HahnSeries.single (n : ℤ) c := by
  simp [parameter, LaurentSeries.coe_algebraMap, HahnSeries.ofPowerSeries_X,
    LaurentSeries.algebraMap_apply, HahnSeries.C_apply]

private theorem connection_constant
    (V : ModuleCat.{0} ℚ) (C : RationalComplexification V) (r : ℕ)
    (e : C.complexSpace ≃ₗ[ℂ] EuclideanSpace ℂ (Fin r)) (w : ℤ)
    (H : PolarizedPeriodVariation C e w) (b n : ℕ) (x : C.complexSpace) :
    formalConnection C e H b (parameter ^ (n + 1) • constantSection V C r e x) =
      parameter ^ n • constantSection V C r e
        (((n + 1 : ℕ) : ℂ) • x +
          ((2 * Real.pi * Complex.I)⁻¹ : ℂ) • truncatedComplexLog C e H b x) := by
  funext i
  change LaurentSeries.derivative ℂ
      (parameter ^ (n + 1) * algebraMap ℂ LocalMeromorphicSeries (e x i)) +
      parameter⁻¹ * ∑ j : Fin r,
        algebraMap ℂ LocalMeromorphicSeries (residueMatrix C e H b i j) *
          (parameter ^ (n + 1) * algebraMap ℂ LocalMeromorphicSeries (e x j)) = _
  have hd : LaurentSeries.derivative ℂ
      (parameter ^ (n + 1) * algebraMap ℂ LocalMeromorphicSeries (e x i)) =
      parameter ^ n * algebraMap ℂ LocalMeromorphicSeries (((n + 1 : ℕ) : ℂ) * e x i) := by
    rw [parameter_monomial, parameter_monomial]
    simp [LaurentSeries.derivative_apply, LaurentSeries.hasseDeriv_single,
      sub_eq_add_neg, add_assoc]
  rw [hd]
  simp_rw [mul_left_comm _ (parameter ^ (n + 1)), ← map_mul]
  rw [← Finset.mul_sum, ← map_sum, residue_apply]
  change _ = parameter ^ n * algebraMap ℂ LocalMeromorphicSeries _
  simp only [map_add, map_smul, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  rw [mul_add, pow_succ]
  have hc : parameter⁻¹ * (parameter ^ n * parameter) = parameter ^ n := by
    rw [mul_comm (parameter ^ n) parameter, ← mul_assoc,
      inv_mul_cancel₀ parameter_ne_zero, one_mul]
  rw [← mul_assoc parameter⁻¹, hc]

private theorem constant_mem_lattice
    (V : ModuleCat.{0} ℚ) (C : RationalComplexification V) (r : ℕ)
    (e : C.complexSpace ≃ₗ[ℂ] EuclideanSpace ℂ (Fin r)) (x : C.complexSpace) :
    constantSection V C r e x ∈ deligneLattice r := by
  refine ⟨fun i ↦ PowerSeries.C (e x i), ?_⟩
  funext i
  simp [latticeEmbedding, constantSection, LaurentSeries.coe_algebraMap,
    HahnSeries.ofPowerSeries_C, LaurentSeries.algebraMap_apply]

private theorem lattice_le_of_constants
    (V : ModuleCat.{0} ℚ) (C : RationalComplexification V) (r : ℕ)
    (e : C.complexSpace ≃ₗ[ℂ] EuclideanSpace ℂ (Fin r))
    (P : Submodule LocalPowerSeries (Fin r → LocalMeromorphicSeries))
    (h : ∀ x, constantSection V C r e x ∈ P) : deligneLattice r ≤ P := by
  classical
  rintro v ⟨f, rfl⟩
  have hf : f = ∑ i : Fin r, f i • Pi.single i 1 := by
    ext j
    simp [Pi.single_apply]
  rw [hf, map_sum]
  apply P.sum_mem
  intro i hi
  rw [map_smul]
  apply P.smul_mem
  convert h (e.symm (EuclideanSpace.single i 1)) using 1
  funext j
  by_cases hj : j = i <;>
    simp [latticeEmbedding, constantSection, EuclideanSpace.single, hj]

private theorem descend_constants
    (V : ModuleCat.{0} ℚ) (C : RationalComplexification V) (r : ℕ)
    (e : C.complexSpace ≃ₗ[ℂ] EuclideanSpace ℂ (Fin r)) (w : ℤ)
    (H : PolarizedPeriodVariation C e w) (b : ℕ)
    (hlog : IsNilpotent (truncatedComplexLog C e H b))
    (P : Submodule LocalPowerSeries (Fin r → LocalMeromorphicSeries))
    (hstable : ∀ v, v ∈ P → formalConnection C e H b v ∈ P)
    (n : ℕ) (hn : ∀ x, parameter ^ n • constantSection V C r e x ∈ P) :
    ∀ x, constantSection V C r e x ∈ P := by
  induction n with
  | zero => simpa using hn
  | succ n ih =>
    apply ih
    intro x
    let A : Module.End ℂ C.complexSpace :=
      ((2 * Real.pi * Complex.I)⁻¹ : ℂ) • truncatedComplexLog C e H b
    have hA : IsNilpotent A := hlog.smul _
    have hu : IsUnit (((n + 1 : ℕ) : ℂ) • (1 : Module.End ℂ C.complexSpace)) := by
      rw [← Algebra.algebraMap_eq_smul_one]
      exact (isUnit_iff_ne_zero.mpr (Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n))).map _
    have hunit : IsUnit (((n + 1 : ℕ) : ℂ) • (1 : Module.End ℂ C.complexSpace) + A) :=
      hA.isUnit_add_left_of_commute hu ((Commute.one_right A).smul_right _)
    obtain ⟨y, hy⟩ := (Module.End.isUnit_iff _).mp hunit |>.2 x
    have hp := hstable _ (hn y)
    rw [connection_constant] at hp
    simpa only [A, LinearMap.add_apply, LinearMap.smul_apply, one_apply_eq_self] using
      (hy ▸ hp)

end MathlibExt.AlgebraicGeometry.HodgeModuleCurveExtension

namespace WantedExt.AlgebraicGeometry.HodgeModuleCurveExtensionWanted

/-- The constructed differential module has no nonzero boundary-supported
quotient: a stable submodule agreeing after inverting the actual parameter
is already the entire minimal extension. -/
public theorem minimal_extension_no_boundary_quotient
    (V : ModuleCat.{0} ℚ) [FiniteDimensional ℚ V]
    (C : RationalComplexification V) (r : ℕ)
    (e : C.complexSpace ≃ₗ[ℂ] EuclideanSpace ℂ (Fin r)) (w : ℤ)
    (H : PolarizedPeriodVariation C e w) (b : ℕ) (hb : 0 < b)
    (hT : (H.rationalDeck.toLinearMap - 1) ^ b = 0)
    (P : Submodule LocalPowerSeries (Fin r → LocalMeromorphicSeries))
    (hP : P ≤ minimalModule C e H b)
    (hstable : ∀ v, v ∈ P → formalConnection C e H b v ∈ P)
    (hgeneric : ∀ v, v ∈ minimalModule C e H b → ∃ n : ℕ,
      (algebraMap LocalPowerSeries LocalMeromorphicSeries PowerSeries.X) ^ n • v ∈ P) :
    P = minimalModule C e H b
    := by
  classical
  have hg (i : Fin r) : ∃ n : ℕ,
      parameter ^ n • constantSection V C r e
        (e.symm (EuclideanSpace.single i 1)) ∈ P :=
    hgeneric _ (lattice_le_minimal C e H b (constant_mem_lattice V C r e _))
  choose n hn using hg
  let N := Finset.univ.sup n
  have hbasis (i : Fin r) : parameter ^ N • constantSection V C r e
      (e.symm (EuclideanSpace.single i 1)) ∈ P := by
    have hi : n i ≤ N := Finset.le_sup (Finset.mem_univ i)
    have hp := P.smul_mem (PowerSeries.X ^ (N - n i)) (hn i)
    rw [← IsScalarTower.algebraMap_smul (R := LocalPowerSeries)
      LocalMeromorphicSeries, map_pow] at hp
    change parameter ^ (N - n i) • (parameter ^ n i • _) ∈ P at hp
    simpa only [smul_smul, ← pow_add, Nat.sub_add_cancel hi] using hp
  have hall (x : C.complexSpace) : parameter ^ N • constantSection V C r e x ∈ P := by
    have hx : x = ∑ j : Fin r, e x j • e.symm (EuclideanSpace.single j 1) := by
      apply e.injective
      simpa only [map_sum, map_smul, LinearEquiv.apply_symm_apply,
        EuclideanSpace.basisFun_apply, EuclideanSpace.basisFun_repr] using
        ((EuclideanSpace.basisFun (Fin r) ℂ).sum_repr (e x)).symm
    rw [hx, map_sum, Finset.smul_sum]
    apply P.sum_mem
    intro i hi
    rw [map_smul]
    have hc (c : ℂ) (v : Fin r → LocalMeromorphicSeries) :
        parameter ^ N • (c • v) = c • (parameter ^ N • v) := by
      funext j
      change parameter ^ N * (c • v j) = c • (parameter ^ N * v j)
      simp only [← HahnSeries.C_mul_eq_smul]
      ring
    rw [hc]
    exact (P.restrictScalars ℂ).smul_mem _ (hbasis i)
  have hlattice : deligneLattice r ≤ P :=
    lattice_le_of_constants V C r e P
      (descend_constants V C r e w H b (log_nilpotent V C r e w H b hb hT) P hstable N hall)
  exact le_antisymm hP (sInf_le ⟨hlattice, hstable⟩)

end WantedExt.AlgebraicGeometry.HodgeModuleCurveExtensionWanted

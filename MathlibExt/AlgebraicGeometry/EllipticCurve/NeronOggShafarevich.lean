/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
public import Mathlib.AlgebraicGeometry.EllipticCurve.Reduction
public import Mathlib.RingTheory.Valuation.RamificationGroup

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Mathlib.RingTheory.Valuation.LocalSubring

/-!
# The easy direction of the Néron–Ogg–Shafarevich criterion

This file proves that prime-to-residue-characteristic torsion of an elliptic curve with good
reduction is fixed by inertia, using the elementary valuation filtration at the origin.
-/

namespace MetaMathlibExt

@[expose] public section

open scoped WeierstrassCurve.Affine

private lemma nos_mem_of_mem_range {R k K : Type*} [CommRing R] [Field k] [Field K]
    [Algebra R k] [Algebra k K] (A : ValuationSubring K)
    (hA : (A.comap (algebraMap k K)).toSubring = (algebraMap R k).range)
    {x : k} (hx : x ∈ (algebraMap R k).range) : algebraMap k K x ∈ A := by
  rw [← ValuationSubring.mem_comap]
  change x ∈ (A.comap (algebraMap k K)).toSubring
  rw [hA]
  exact hx

private def nosToValuationSubring {R k K : Type*} [CommRing R] [Field k] [Field K]
    [Algebra R k] [Algebra k K] (A : ValuationSubring K)
    (hA : (A.comap (algebraMap k K)).toSubring = (algebraMap R k).range) : R →+* A :=
  ((algebraMap k K).comp (algebraMap R k)).codRestrict A.toSubring fun r ↦ by
    apply nos_mem_of_mem_range A hA
    exact ⟨r, rfl⟩

private lemma nos_coefficients_mem {R k K : Type*} [CommRing R] [Field k] [Field K]
    [Algebra R k] [Algebra k K] (E : WeierstrassCurve k) [E.IsIntegral R]
    (A : ValuationSubring K)
    (hA : (A.comap (algebraMap k K)).toSubring = (algebraMap R k).range) :
    algebraMap k K E.a₁ ∈ A ∧ algebraMap k K E.a₂ ∈ A ∧
      algebraMap k K E.a₃ ∈ A ∧ algebraMap k K E.a₄ ∈ A ∧
      algebraMap k K E.a₆ ∈ A ∧ algebraMap k K E.Δ ∈ A := by
  constructor
  · apply nos_mem_of_mem_range A hA
    exact ⟨(E.integralModel R).a₁, E.integralModel_a₁_eq R⟩
  constructor
  · apply nos_mem_of_mem_range A hA
    exact ⟨(E.integralModel R).a₂, E.integralModel_a₂_eq R⟩
  constructor
  · apply nos_mem_of_mem_range A hA
    exact ⟨(E.integralModel R).a₃, E.integralModel_a₃_eq R⟩
  constructor
  · apply nos_mem_of_mem_range A hA
    exact ⟨(E.integralModel R).a₄, E.integralModel_a₄_eq R⟩
  constructor
  · apply nos_mem_of_mem_range A hA
    exact ⟨(E.integralModel R).a₆, E.integralModel_a₆_eq R⟩
  · apply nos_mem_of_mem_range A hA
    exact ⟨(E.integralModel R).Δ, E.integralModel_Δ_eq R⟩

private lemma nos_discriminant_unit {R k K : Type*} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [Field k] [Algebra R k] [IsFractionRing R k]
    [Field K] [Algebra k K] (E : WeierstrassCurve k) [E.HasGoodReduction R]
    (A : ValuationSubring K)
    (hA : (A.comap (algebraMap k K)).toSubring = (algebraMap R k).range) :
    ∃ d : A, (d : K) = algebraMap k K E.Δ ∧ IsUnit d := by
  let r : R := (E.integralModel R).Δ
  have hrval :
      IsDedekindDomain.HeightOneSpectrum.valuation
        k (IsDiscreteValuationRing.maximalIdeal R) (algebraMap R k r) = 1 := by
    rw [show algebraMap R k r = E.Δ from E.integralModel_Δ_eq R]
    exact WeierstrassCurve.HasGoodReduction.goodReduction
  have hrnot : r ∉ (IsDiscreteValuationRing.maximalIdeal R).asIdeal :=
    (IsDedekindDomain.HeightOneSpectrum.valuation_eq_one_iff_notMem (K := k)
      (IsDiscreteValuationRing.maximalIdeal R)).mp hrval
  have hr : IsUnit r := IsLocalRing.notMem_maximalIdeal.mp (by
    simpa [IsDiscreteValuationRing.maximalIdeal] using hrnot)
  let f := nosToValuationSubring A hA
  refine ⟨f r, ?_, hr.map f⟩
  change algebraMap k K (algebraMap R k r) = algebraMap k K E.Δ
  rw [show algebraMap R k r = E.Δ from E.integralModel_Δ_eq R]

private lemma nos_nat_unit {R k K : Type*} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [Field k] [Algebra R k] [IsFractionRing R k]
    [Field K] [Algebra k K] (n : ℕ) [NeZero (n : IsLocalRing.ResidueField R)]
    (A : ValuationSubring K)
    (hA : (A.comap (algebraMap k K)).toSubring = (algebraMap R k).range) :
    ∃ u : A, (u : K) = (n : K) ∧ IsUnit u := by
  have hnres : IsLocalRing.residue R (n : R) ≠ 0 := by
    simpa using (NeZero.ne (n : IsLocalRing.ResidueField R))
  have hnnot : (n : R) ∉ IsLocalRing.maximalIdeal R := fun hn ↦
    hnres ((IsLocalRing.residue_eq_zero_iff (n : R)).mpr hn)
  have hn : IsUnit (n : R) := IsLocalRing.notMem_maximalIdeal.mp hnnot
  let f := nosToValuationSubring A hA
  refine ⟨f (n : R), ?_, hn.map f⟩
  change algebraMap k K (algebraMap R k (n : R)) = (n : K)
  simp

private def nosLocalEquation {K : Type*} [CommRing K] (W : WeierstrassCurve K)
    (z w : K) : Prop :=
  w = z ^ 3 + W.a₁ * z * w + W.a₂ * z ^ 2 * w + W.a₃ * w ^ 2 +
    W.a₄ * z * w ^ 2 + W.a₆ * w ^ 3

private def nosChordU {K : Type*} [CommRing K] (W : WeierstrassCurve K)
    (z₁ w₁ w₂ : K) : K :=
  1 - W.a₁ * z₁ - W.a₂ * z₁ ^ 2 - W.a₃ * (w₂ + w₁) -
    W.a₄ * z₁ * (w₂ + w₁) - W.a₆ * (w₂ ^ 2 + w₂ * w₁ + w₁ ^ 2)

private def nosChordV {K : Type*} [CommRing K] (W : WeierstrassCurve K)
    (z₁ z₂ w₂ : K) : K :=
  z₂ ^ 2 + z₂ * z₁ + z₁ ^ 2 + W.a₁ * w₂ +
    W.a₂ * (z₂ + z₁) * w₂ + W.a₄ * w₂ ^ 2

private def nosLineC₃ {K : Type*} [CommRing K] (W : WeierstrassCurve K) (a : K) : K :=
  1 + W.a₂ * a + W.a₄ * a ^ 2 + W.a₆ * a ^ 3

private def nosLineC₂ {K : Type*} [CommRing K] (W : WeierstrassCurve K) (a b : K) : K :=
  W.a₁ * a + W.a₂ * b + W.a₃ * a ^ 2 + 2 * W.a₄ * a * b +
    3 * W.a₆ * a ^ 2 * b

private def nosLineQ₂ {K : Type*} [CommRing K] (W : WeierstrassCurve K) (l : K) : K :=
  l ^ 2 + W.a₁ * l - W.a₂

private def nosLineQ₁ {K : Type*} [CommRing K] (W : WeierstrassCurve K) (l c : K) : K :=
  2 * l * c + W.a₁ * c + W.a₃ * l - W.a₄

private def nosLineQ₀ {K : Type*} [CommRing K] (W : WeierstrassCurve K) (c : K) : K :=
  c ^ 2 + W.a₃ * c - W.a₆

private lemma nos_local_equation {F : Type*} [Field F] (W : WeierstrassCurve F)
    {x y : F} (h : WeierstrassCurve.Affine.Equation W x y) (hy : y ≠ 0) :
    let z := -x / y
    let w := -1 / y
    nosLocalEquation W z w := by
  rw [WeierstrassCurve.Affine.equation_iff (W := W) x y] at h
  dsimp [nosLocalEquation]
  field_simp [hy]
  linear_combination -h

private lemma nos_chord_identity {K : Type*} [CommRing K] (W : WeierstrassCurve K)
    {z₁ z₂ w₁ w₂ : K} (h₁ : nosLocalEquation W z₁ w₁)
    (h₂ : nosLocalEquation W z₂ w₂) :
    (w₂ - w₁) * nosChordU W z₁ w₁ w₂ =
      (z₂ - z₁) * nosChordV W z₁ z₂ w₂ := by
  dsimp [nosLocalEquation, nosChordU, nosChordV] at h₁ h₂ ⊢
  linear_combination h₂ - h₁

private lemma nos_line_root {K : Type*} [Field K] (W : WeierstrassCurve K)
    {x y l c : K} (h : WeierstrassCurve.Affine.Equation W x y)
    (hline : y = l * x + c) :
    -x ^ 3 + nosLineQ₂ W l * x ^ 2 + nosLineQ₁ W l c * x + nosLineQ₀ W c = 0 := by
  rw [WeierstrassCurve.Affine.equation_iff (W := W) x y] at h
  rw [hline] at h
  dsimp [nosLineQ₂, nosLineQ₁, nosLineQ₀]
  linear_combination h

private lemma nos_secant_symmetric {K : Type*} [Field K] (W : WeierstrassCurve K)
    {x₁ x₂ l c : K}
    (h₁ : -x₁ ^ 3 + nosLineQ₂ W l * x₁ ^ 2 + nosLineQ₁ W l c * x₁ +
      nosLineQ₀ W c = 0)
    (h₂ : -x₂ ^ 3 + nosLineQ₂ W l * x₂ ^ 2 + nosLineQ₁ W l c * x₂ +
      nosLineQ₀ W c = 0)
    (hx : x₁ ≠ x₂) :
    let x₃ := nosLineQ₂ W l - x₁ - x₂
    nosLineQ₁ W l c = -(x₁ * x₂ + x₁ * x₃ + x₂ * x₃) ∧
      nosLineQ₀ W c = x₁ * x₂ * x₃ := by
  dsimp
  have hdx : x₁ - x₂ ≠ 0 := sub_ne_zero.mpr hx
  have hdiff : (x₁ - x₂) *
      (-(x₁ ^ 2 + x₁ * x₂ + x₂ ^ 2) + nosLineQ₂ W l * (x₁ + x₂) +
        nosLineQ₁ W l c) = 0 := by
    linear_combination h₁ - h₂
  have hs := (mul_eq_zero.mp hdiff).resolve_left hdx
  constructor
  · linear_combination hs
  · linear_combination h₁ - x₁ * hs

private lemma nos_transformed_vieta {K : Type*} [Field K] (W : WeierstrassCurve K)
    {x₁ x₂ x₃ y₁ y₂ y₃ l c : K}
    (hs₁ : nosLineQ₂ W l = x₁ + x₂ + x₃)
    (hs₂ : nosLineQ₁ W l c = -(x₁ * x₂ + x₁ * x₃ + x₂ * x₃))
    (hs₃ : nosLineQ₀ W c = x₁ * x₂ * x₃)
    (hy₁eq : y₁ = l * x₁ + c) (hy₂eq : y₂ = l * x₂ + c)
    (hy₃eq : y₃ = l * x₃ + c)
    (hy₁ : y₁ ≠ 0) (hy₂ : y₂ ≠ 0) (hy₃ : y₃ ≠ 0) (hc : c ≠ 0) :
    nosLineC₃ W (-l / c) * (-x₁ / y₁ + -x₂ / y₂ + -x₃ / y₃) +
      nosLineC₂ W (-l / c) (-1 / c) = 0 := by
  have hD : (l * x₁ + c) * (l * x₂ + c) * (l * x₃ + c) =
      c ^ 3 - W.a₂ * l * c ^ 2 + W.a₄ * l ^ 2 * c - W.a₆ * l ^ 3 := by
    dsimp [nosLineQ₂, nosLineQ₁, nosLineQ₀] at hs₁ hs₂ hs₃
    linear_combination -l * c ^ 2 * hs₁ + l ^ 2 * c * hs₂ - l ^ 3 * hs₃
  have hN :
      x₁ * (l * x₂ + c) * (l * x₃ + c) +
          x₂ * (l * x₁ + c) * (l * x₃ + c) +
          x₃ * (l * x₁ + c) * (l * x₂ + c) =
        -W.a₁ * l * c ^ 2 - W.a₂ * c ^ 2 + W.a₃ * l ^ 2 * c +
          2 * W.a₄ * l * c - 3 * W.a₆ * l ^ 2 := by
    dsimp [nosLineQ₂, nosLineQ₁, nosLineQ₀] at hs₁ hs₂ hs₃
    linear_combination -c ^ 2 * hs₁ + 2 * l * c * hs₂ - 3 * l ^ 2 * hs₃
  have hC₃ : nosLineC₃ W (-l / c) =
      ((l * x₁ + c) * (l * x₂ + c) * (l * x₃ + c)) / c ^ 3 := by
    rw [hD]
    dsimp [nosLineC₃]
    field_simp [hc]
    ring
  have hC₂ : nosLineC₂ W (-l / c) (-1 / c) =
      (x₁ * (l * x₂ + c) * (l * x₃ + c) +
          x₂ * (l * x₁ + c) * (l * x₃ + c) +
          x₃ * (l * x₁ + c) * (l * x₂ + c)) / c ^ 3 := by
    rw [hN]
    dsimp [nosLineC₂]
    field_simp [hc]
    ring
  rw [hy₁eq] at hy₁ ⊢
  rw [hy₂eq] at hy₂ ⊢
  rw [hy₃eq] at hy₃ ⊢
  rw [hC₃, hC₂]
  field_simp [hy₁, hy₂, hy₃, hc]
  ring

private lemma nos_secant_vieta {K : Type*} [Field K] (W : WeierstrassCurve K)
    {x₁ x₂ x₃ y₁ y₂ y₃ l c : K}
    (h₁ : WeierstrassCurve.Affine.Equation W x₁ y₁)
    (h₂ : WeierstrassCurve.Affine.Equation W x₂ y₂) (hx : x₁ ≠ x₂)
    (hy₁eq : y₁ = l * x₁ + c) (hy₂eq : y₂ = l * x₂ + c)
    (hy₃eq : y₃ = l * x₃ + c) (hx₃ : x₃ = nosLineQ₂ W l - x₁ - x₂)
    (hy₁ : y₁ ≠ 0) (hy₂ : y₂ ≠ 0) (hy₃ : y₃ ≠ 0) (hc : c ≠ 0) :
    nosLineC₃ W (-l / c) * (-x₁ / y₁ + -x₂ / y₂ + -x₃ / y₃) +
      nosLineC₂ W (-l / c) (-1 / c) = 0 := by
  have hr₁ := nos_line_root W h₁ hy₁eq
  have hr₂ := nos_line_root W h₂ hy₂eq
  obtain ⟨hs₂, hs₃⟩ := nos_secant_symmetric W hr₁ hr₂ hx
  apply nos_transformed_vieta W (x₁ := x₁) (x₂ := x₂) (x₃ := x₃)
    (y₁ := y₁) (y₂ := y₂) (y₃ := y₃) (l := l) (c := c)
  · rw [hx₃]
    ring
  · simpa only [hx₃] using hs₂
  · simpa only [hx₃] using hs₃
  · exact hy₁eq
  · exact hy₂eq
  · exact hy₃eq
  · exact hy₁
  · exact hy₂
  · exact hy₃
  · exact hc

private lemma nos_tangent_symmetric {K : Type*} [Field K] (W : WeierstrassCurve K)
    {x l c : K}
    (hroot : -x ^ 3 + nosLineQ₂ W l * x ^ 2 + nosLineQ₁ W l c * x +
      nosLineQ₀ W c = 0)
    (hderiv : -3 * x ^ 2 + 2 * nosLineQ₂ W l * x + nosLineQ₁ W l c = 0) :
    let x₃ := nosLineQ₂ W l - 2 * x
    nosLineQ₁ W l c = -(x * x + x * x₃ + x * x₃) ∧
      nosLineQ₀ W c = x * x * x₃ := by
  dsimp
  constructor
  · linear_combination hderiv
  · linear_combination hroot - x * hderiv

private lemma nos_tangent_derivative_of_mul {K : Type*} [Field K] (W : WeierstrassCurve K)
    {x y l c : K} (hc : c = y - l * x)
    (hl : l * (2 * y + W.a₁ * x + W.a₃) =
      3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ - W.a₁ * y) :
    -3 * x ^ 2 + 2 * nosLineQ₂ W l * x + nosLineQ₁ W l c = 0 := by
  rw [hc]
  dsimp [nosLineQ₂, nosLineQ₁]
  linear_combination hl

private lemma nos_tangent_vieta {K : Type*} [Field K] (W : WeierstrassCurve K)
    {x x₃ y y₃ l c : K} (h : WeierstrassCurve.Affine.Equation W x y)
    (hyEq : y = l * x + c) (hy₃eq : y₃ = l * x₃ + c)
    (hx₃ : x₃ = nosLineQ₂ W l - 2 * x)
    (hderiv : -3 * x ^ 2 + 2 * nosLineQ₂ W l * x + nosLineQ₁ W l c = 0)
    (hy : y ≠ 0) (hy₃ : y₃ ≠ 0) (hc : c ≠ 0) :
    nosLineC₃ W (-l / c) * (-x / y + -x / y + -x₃ / y₃) +
      nosLineC₂ W (-l / c) (-1 / c) = 0 := by
  have hr := nos_line_root W h hyEq
  obtain ⟨hs₂, hs₃⟩ := nos_tangent_symmetric W hr hderiv
  apply nos_transformed_vieta W (x₁ := x) (x₂ := x) (x₃ := x₃)
    (y₁ := y) (y₂ := y) (y₃ := y₃) (l := l) (c := c)
  · rw [hx₃]
    ring
  · simpa only [hx₃] using hs₂
  · simpa only [hx₃] using hs₃
  · exact hyEq
  · exact hyEq
  · exact hy₃eq
  · exact hy
  · exact hy
  · exact hy₃
  · exact hc

private lemma nos_transformed_line {K : Type*} [Field K]
    {x y l c : K} (hy : y ≠ 0) (hc : c ≠ 0) (hline : y = l * x + c) :
    -1 / y = (-l / c) * (-x / y) + -1 / c := by
  field_simp [hy, hc]
  linear_combination hline

private lemma nos_line_slope {K : Type*} [Field K]
    {z₁ z₂ w₁ w₂ a b : K} (hz : z₁ ≠ z₂)
    (h₁ : w₁ = a * z₁ + b) (h₂ : w₂ = a * z₂ + b) :
    a = (w₂ - w₁) / (z₂ - z₁) ∧ b = w₁ - a * z₁ := by
  have hdz : z₂ - z₁ ≠ 0 := sub_ne_zero.mpr hz.symm
  constructor
  · apply (eq_div_iff hdz).mpr
    linear_combination h₁ - h₂
  · linear_combination -h₁

private lemma nos_tangent_transform {K : Type*} [Field K] (W : WeierstrassCurve K)
    {x y z w l c : K} (h : WeierstrassCurve.Affine.Equation W x y) (hy : y ≠ 0)
    (hden : 2 * y + W.a₁ * x + W.a₃ ≠ 0)
    (hz : z = -x / y) (hw : w = -1 / y)
    (hl : l = (3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ - W.a₁ * y) /
      (2 * y + W.a₁ * x + W.a₃))
    (hc : c = y - l * x) (hU : nosChordU W z w w ≠ 0) :
    c ≠ 0 ∧ -l / c = nosChordV W z z w / nosChordU W z w w ∧
      -1 / c = w - (nosChordV W z z w / nosChordU W z w w) * z := by
  have hlmul : l * (2 * y + W.a₁ * x + W.a₃) =
      3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ - W.a₁ * y := by
    rw [hl]
    exact div_mul_cancel₀ _ hden
  have hcurve := (WeierstrassCurve.Affine.equation_iff (W := W) x y).mp h
  have hUy : nosChordU W z w w * y ^ 2 = x ^ 3 - W.a₄ * x - 2 * W.a₆ + W.a₃ * y := by
    rw [hz, hw]
    dsimp [nosChordU]
    field_simp [hy]
    linear_combination hcurve
  have hVy : nosChordV W z z w * y ^ 2 =
      3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ - W.a₁ * y := by
    rw [hz, hw]
    dsimp [nosChordV]
    field_simp [hy]
    ring
  have hcD : c * (2 * y + W.a₁ * x + W.a₃) = -(nosChordU W z w w * y ^ 2) := by
    rw [hc]
    linear_combination 2 * hcurve + hUy - x * hlmul
  have hc0 : c ≠ 0 := by
    intro hczero
    rw [hczero, zero_mul] at hcD
    have hzero : nosChordU W z w w * y ^ 2 = 0 := by
      linear_combination hcD
    exact (mul_ne_zero hU (pow_ne_zero 2 hy)) hzero
  refine ⟨hc0, ?_, ?_⟩
  · apply (div_eq_div_iff hc0 hU).mpr
    apply mul_right_cancel₀ hden
    linear_combination -nosChordU W z w w * hlmul - nosChordV W z z w * hcD +
      nosChordU W z w w * hVy
  · have hline : y = l * x + c := by
      rw [hc]
      ring
    have htrans := nos_transformed_line hy hc0 hline
    have ha : -l / c = nosChordV W z z w / nosChordU W z w w := by
      apply (div_eq_div_iff hc0 hU).mpr
      apply mul_right_cancel₀ hden
      linear_combination -nosChordU W z w w * hlmul - nosChordV W z z w * hcD +
        nosChordU W z w w * hVy
    rw [← ha, hw, hz]
    linear_combination -htrans

private lemma nos_chord_z_ne {K : Type*} [Field K] (W : WeierstrassCurve K)
    {x₁ x₂ y₁ y₂ z₁ z₂ w₁ w₂ : K} (hx : x₁ ≠ x₂)
    (hy₁ : y₁ ≠ 0) (hy₂ : y₂ ≠ 0)
    (hz₁ : z₁ = -x₁ / y₁) (hz₂ : z₂ = -x₂ / y₂)
    (hw₁ : w₁ = -1 / y₁) (hw₂ : w₂ = -1 / y₂)
    (h₁ : nosLocalEquation W z₁ w₁) (h₂ : nosLocalEquation W z₂ w₂)
    (hU : nosChordU W z₁ w₁ w₂ ≠ 0) : z₁ ≠ z₂ := by
  intro hz
  have hid := nos_chord_identity W h₁ h₂
  have hzsub : z₂ - z₁ = 0 := sub_eq_zero.mpr hz.symm
  rw [hzsub, zero_mul] at hid
  have hwsub : w₂ - w₁ = 0 := (mul_eq_zero.mp hid).resolve_right hU
  have hw : w₁ = w₂ := (sub_eq_zero.mp hwsub).symm
  apply hx
  rw [hz₁, hz₂] at hz
  rw [hw₁, hw₂] at hw
  field_simp [hy₁, hy₂] at hz hw
  have hyEq : y₁ = y₂ := by
    linear_combination hw
  rw [hyEq] at hz
  apply mul_right_cancel₀ hy₂
  simpa only [neg_inj, mul_comm] using hz

private lemma nos_line_intercept_ne {K : Type*} [Field K]
    {x₁ x₂ y₁ y₂ l c : K} (hy₁ : y₁ ≠ 0) (hy₂ : y₂ ≠ 0)
    (hy₁eq : y₁ = l * x₁ + c) (hy₂eq : y₂ = l * x₂ + c)
    (hz : -x₁ / y₁ ≠ -x₂ / y₂) : c ≠ 0 := by
  intro hc
  apply hz
  apply (div_eq_div_iff hy₁ hy₂).mpr
  rw [hy₁eq, hy₂eq, hc]
  ring

private lemma nos_transformed_leading {K : Type*} [Field K] (W : WeierstrassCurve K)
    {x₁ x₂ x₃ y₁ y₂ y₃ l c : K}
    (hs₁ : nosLineQ₂ W l = x₁ + x₂ + x₃)
    (hs₂ : nosLineQ₁ W l c = -(x₁ * x₂ + x₁ * x₃ + x₂ * x₃))
    (hs₃ : nosLineQ₀ W c = x₁ * x₂ * x₃)
    (hy₁eq : y₁ = l * x₁ + c) (hy₂eq : y₂ = l * x₂ + c)
    (hy₃eq : y₃ = l * x₃ + c) (hc : c ≠ 0) :
    nosLineC₃ W (-l / c) = y₁ * y₂ * y₃ / c ^ 3 := by
  have hD : (l * x₁ + c) * (l * x₂ + c) * (l * x₃ + c) =
      c ^ 3 - W.a₂ * l * c ^ 2 + W.a₄ * l ^ 2 * c - W.a₆ * l ^ 3 := by
    dsimp [nosLineQ₂, nosLineQ₁, nosLineQ₀] at hs₁ hs₂ hs₃
    linear_combination -l * c ^ 2 * hs₁ + l ^ 2 * c * hs₂ - l ^ 3 * hs₃
  rw [hy₁eq, hy₂eq, hy₃eq, hD]
  dsimp [nosLineC₃]
  field_simp [hc]
  ring

private lemma nos_chord_U_unit {K : Type*} [Field K] (W : WeierstrassCurve K)
    (A : ValuationSubring K) {z₁ z₂ w₁ w₂ : K}
    (ha₁ : W.a₁ ∈ A) (ha₂ : W.a₂ ∈ A) (ha₃ : W.a₃ ∈ A)
    (ha₄ : W.a₄ ∈ A) (ha₆ : W.a₆ ∈ A)
    (hz₁ : A.valuation z₁ < 1) (hz₂ : A.valuation z₂ ≤ A.valuation z₁)
    (hw₁ : A.valuation w₁ = A.valuation z₁ ^ 3)
    (hw₂ : A.valuation w₂ = A.valuation z₂ ^ 3) :
    A.valuation (nosChordU W z₁ w₁ w₂) = 1 := by
  let v := A.valuation
  have ha₁v : v W.a₁ ≤ 1 := (A.valuation_le_one_iff W.a₁).mpr ha₁
  have ha₂v : v W.a₂ ≤ 1 := (A.valuation_le_one_iff W.a₂).mpr ha₂
  have ha₃v : v W.a₃ ≤ 1 := (A.valuation_le_one_iff W.a₃).mpr ha₃
  have ha₄v : v W.a₄ ≤ 1 := (A.valuation_le_one_iff W.a₄).mpr ha₄
  have ha₆v : v W.a₆ ≤ 1 := (A.valuation_le_one_iff W.a₆).mpr ha₆
  have hz₂' : v z₂ < 1 := hz₂.trans_lt hz₁
  have hw₁' : v w₁ < 1 := by
    rw [hw₁]
    exact pow_lt_one₀ zero_le hz₁ (by decide)
  have hw₂' : v w₂ < 1 := by
    rw [hw₂]
    exact pow_lt_one₀ zero_le hz₂' (by decide)
  have hwadd : v (w₂ + w₁) < 1 := v.map_add_lt hw₂' hw₁'
  have hwquad : v (w₂ ^ 2 + w₂ * w₁ + w₁ ^ 2) < 1 := by
    apply v.map_add_lt
    · apply v.map_add_lt <;> simp only [v, Valuation.map_mul, Valuation.map_pow]
      · exact pow_lt_one₀ zero_le hw₂' (by decide)
      · exact (mul_le_of_le_one_right zero_le hw₁'.le).trans_lt hw₂'
    · simp only [v, Valuation.map_pow]
      exact pow_lt_one₀ zero_le hw₁' (by decide)
  have hsmall : v (W.a₁ * z₁ + W.a₂ * z₁ ^ 2 + W.a₃ * (w₂ + w₁) +
      W.a₄ * z₁ * (w₂ + w₁) + W.a₆ * (w₂ ^ 2 + w₂ * w₁ + w₁ ^ 2)) < 1 := by
    apply v.map_add_lt
    · apply v.map_add_lt
      · apply v.map_add_lt
        · apply v.map_add_lt
          · simp only [v, Valuation.map_mul]
            exact (mul_le_of_le_one_left zero_le ha₁v).trans_lt hz₁
          · simp only [v, Valuation.map_mul, Valuation.map_pow]
            exact (mul_le_of_le_one_left zero_le ha₂v).trans_lt
              (pow_lt_one₀ zero_le hz₁ (by decide))
        · simp only [v, Valuation.map_mul]
          exact (mul_le_of_le_one_left zero_le ha₃v).trans_lt hwadd
      · simp only [v, Valuation.map_mul]
        apply (mul_le_of_le_one_left zero_le ?_).trans_lt hwadd
        exact (mul_le_of_le_one_left zero_le ha₄v).trans hz₁.le
    · simp only [v, Valuation.map_mul]
      exact (mul_le_of_le_one_left zero_le ha₆v).trans_lt hwquad
  rw [show nosChordU W z₁ w₁ w₂ =
      1 - (W.a₁ * z₁ + W.a₂ * z₁ ^ 2 + W.a₃ * (w₂ + w₁) +
        W.a₄ * z₁ * (w₂ + w₁) +
          W.a₆ * (w₂ ^ 2 + w₂ * w₁ + w₁ ^ 2)) by
      simp only [nosChordU]
      ring]
  exact v.map_one_sub_of_lt hsmall

private lemma nos_chord_V_bound {K : Type*} [Field K] (W : WeierstrassCurve K)
    (A : ValuationSubring K) {z₁ z₂ w₂ : K}
    (ha₁ : W.a₁ ∈ A) (ha₂ : W.a₂ ∈ A) (ha₄ : W.a₄ ∈ A)
    (hz₁ : A.valuation z₁ < 1) (hz₂ : A.valuation z₂ ≤ A.valuation z₁)
    (hw₂ : A.valuation w₂ = A.valuation z₂ ^ 3) :
    A.valuation (nosChordV W z₁ z₂ w₂) ≤ A.valuation z₁ ^ 2 := by
  let v := A.valuation
  have ha₁v : v W.a₁ ≤ 1 := (A.valuation_le_one_iff W.a₁).mpr ha₁
  have ha₂v : v W.a₂ ≤ 1 := (A.valuation_le_one_iff W.a₂).mpr ha₂
  have ha₄v : v W.a₄ ≤ 1 := (A.valuation_le_one_iff W.a₄).mpr ha₄
  have hw₂b : v w₂ ≤ v z₁ ^ 2 := by
    rw [hw₂]
    exact (pow_le_pow_left₀ zero_le hz₂ 3).trans
      (pow_right_anti₀ zero_le hz₁.le (by decide : 2 ≤ 3))
  have hw₂one : v w₂ ≤ 1 := hw₂b.trans (pow_le_one₀ zero_le hz₁.le)
  have hzsum : v (z₂ + z₁) ≤ v z₁ :=
    (v.map_add z₂ z₁).trans (max_le hz₂ le_rfl)
  have h₁ : v (z₂ ^ 2) ≤ v z₁ ^ 2 := by
    simp only [v, Valuation.map_pow]
    exact pow_le_pow_left₀ zero_le hz₂ 2
  have h₂ : v (z₂ * z₁) ≤ v z₁ ^ 2 := by
    simp only [v, Valuation.map_mul, pow_two]
    exact mul_le_mul_of_nonneg_right hz₂ zero_le
  have h₃ : v (z₁ ^ 2) ≤ v z₁ ^ 2 := by
    simp only [v, Valuation.map_pow]
    exact le_rfl
  have h₄ : v (W.a₁ * w₂) ≤ v z₁ ^ 2 := by
    simp only [v, Valuation.map_mul]
    exact (mul_le_of_le_one_left zero_le ha₁v).trans hw₂b
  have h₅ : v (W.a₂ * (z₂ + z₁) * w₂) ≤ v z₁ ^ 2 := by
    simp only [v, Valuation.map_mul]
    apply (mul_le_of_le_one_left zero_le ?_).trans hw₂b
    exact (mul_le_of_le_one_left zero_le ha₂v).trans (hzsum.trans hz₁.le)
  have h₆ : v (W.a₄ * w₂ ^ 2) ≤ v z₁ ^ 2 := by
    simp only [v, Valuation.map_mul, Valuation.map_pow]
    exact (mul_le_of_le_one_left zero_le ha₄v).trans
      ((sq_le zero_le hw₂one).trans hw₂b)
  have hadd {a b : K} (ha : v a ≤ v z₁ ^ 2) (hb : v b ≤ v z₁ ^ 2) :
      v (a + b) ≤ v z₁ ^ 2 :=
    (v.map_add a b).trans (max_le ha hb)
  exact hadd (hadd (hadd (hadd (hadd h₁ h₂) h₃) h₄) h₅) h₆

private lemma nos_chord_slope_bound {K : Type*} [Field K] (W : WeierstrassCurve K)
    (A : ValuationSubring K) {z₁ z₂ w₁ w₂ : K}
    (ha₁ : W.a₁ ∈ A) (ha₂ : W.a₂ ∈ A) (ha₃ : W.a₃ ∈ A)
    (ha₄ : W.a₄ ∈ A) (ha₆ : W.a₆ ∈ A)
    (hz₁ : A.valuation z₁ < 1) (hz₂ : A.valuation z₂ ≤ A.valuation z₁)
    (hw₁ : A.valuation w₁ = A.valuation z₁ ^ 3)
    (hw₂ : A.valuation w₂ = A.valuation z₂ ^ 3)
    (h₁ : nosLocalEquation W z₁ w₁) (h₂ : nosLocalEquation W z₂ w₂)
    (hz : z₁ ≠ z₂) :
    A.valuation ((w₂ - w₁) / (z₂ - z₁)) ≤ A.valuation z₁ ^ 2 := by
  let v := A.valuation
  have hU := nos_chord_U_unit W A ha₁ ha₂ ha₃ ha₄ ha₆ hz₁ hz₂ hw₁ hw₂
  have hV := nos_chord_V_bound W A ha₁ ha₂ ha₄ hz₁ hz₂ hw₂
  have hU0 : nosChordU W z₁ w₁ w₂ ≠ 0 := by
    apply v.ne_zero_iff.mp
    rw [hU]
    exact one_ne_zero
  have hdz : z₂ - z₁ ≠ 0 := sub_ne_zero.mpr hz.symm
  have hslope : (w₂ - w₁) / (z₂ - z₁) =
      nosChordV W z₁ z₂ w₂ / nosChordU W z₁ w₁ w₂ := by
    field_simp [hdz, hU0]
    simpa only [mul_comm] using nos_chord_identity W h₁ h₂
  rw [hslope, v.map_div, hU, div_one]
  exact hV

private lemma nos_tangent_U_unit {K : Type*} [Field K] (W : WeierstrassCurve K)
    (A : ValuationSubring K) {z w : K}
    (ha₁ : W.a₁ ∈ A) (ha₂ : W.a₂ ∈ A) (ha₃ : W.a₃ ∈ A)
    (ha₄ : W.a₄ ∈ A) (ha₆ : W.a₆ ∈ A)
    (hz : A.valuation z < 1) (hw : A.valuation w = A.valuation z ^ 3) :
    A.valuation (nosChordU W z w w) = 1 :=
  nos_chord_U_unit W A ha₁ ha₂ ha₃ ha₄ ha₆ hz le_rfl hw hw

private lemma nos_tangent_V_bound {K : Type*} [Field K] (W : WeierstrassCurve K)
    (A : ValuationSubring K) {z w : K}
    (ha₁ : W.a₁ ∈ A) (ha₂ : W.a₂ ∈ A) (ha₄ : W.a₄ ∈ A)
    (hz : A.valuation z < 1) (hw : A.valuation w = A.valuation z ^ 3) :
    A.valuation (nosChordV W z z w) ≤ A.valuation z ^ 2 :=
  nos_chord_V_bound W A ha₁ ha₂ ha₄ hz le_rfl hw

private lemma nos_tangent_slope_bound {K : Type*} [Field K] (W : WeierstrassCurve K)
    (A : ValuationSubring K) {z w : K}
    (ha₁ : W.a₁ ∈ A) (ha₂ : W.a₂ ∈ A) (ha₃ : W.a₃ ∈ A)
    (ha₄ : W.a₄ ∈ A) (ha₆ : W.a₆ ∈ A)
    (hz : A.valuation z < 1) (hw : A.valuation w = A.valuation z ^ 3) :
    A.valuation (nosChordV W z z w / nosChordU W z w w) ≤ A.valuation z ^ 2 := by
  rw [A.valuation.map_div, nos_tangent_U_unit W A ha₁ ha₂ ha₃ ha₄ ha₆ hz hw,
    div_one]
  exact nos_tangent_V_bound W A ha₁ ha₂ ha₄ hz hw

private lemma nos_line_coefficients_bound {K : Type*} [Field K] (W : WeierstrassCurve K)
    (A : ValuationSubring K) {a b : K} {s : A.ValueGroup}
    (ha₁ : W.a₁ ∈ A) (ha₂ : W.a₂ ∈ A) (ha₃ : W.a₃ ∈ A)
    (ha₄ : W.a₄ ∈ A) (ha₆ : W.a₆ ∈ A)
    (hs : s < 1) (ha : A.valuation a ≤ s ^ 2)
    (hb : A.valuation b ≤ s ^ 3) :
    A.valuation (nosLineC₃ W a) = 1 ∧
      A.valuation (nosLineC₂ W a b) ≤ s ^ 2 := by
  let v := A.valuation
  have ha₁v : v W.a₁ ≤ 1 := (A.valuation_le_one_iff W.a₁).mpr ha₁
  have ha₂v : v W.a₂ ≤ 1 := (A.valuation_le_one_iff W.a₂).mpr ha₂
  have ha₃v : v W.a₃ ≤ 1 := (A.valuation_le_one_iff W.a₃).mpr ha₃
  have ha₄v : v W.a₄ ≤ 1 := (A.valuation_le_one_iff W.a₄).mpr ha₄
  have ha₆v : v W.a₆ ≤ 1 := (A.valuation_le_one_iff W.a₆).mpr ha₆
  have hs₂one : s ^ 2 ≤ 1 := pow_le_one₀ zero_le hs.le
  have hs₃₂ : s ^ 3 ≤ s ^ 2 := pow_right_anti₀ zero_le hs.le (by decide)
  have haone : v a ≤ 1 := ha.trans hs₂one
  have hbone : v b ≤ 1 := hb.trans (hs₃₂.trans hs₂one)
  have haa : v (a ^ 2) ≤ v a := by
    simp only [v, Valuation.map_pow]
    exact sq_le zero_le haone
  have haaa : v (a ^ 3) ≤ v a := by
    simp only [v, Valuation.map_pow]
    exact pow_le_of_le_one zero_le haone (by decide)
  have h₂a₄v : v ((2 : K) * W.a₄) ≤ 1 :=
    (A.valuation_le_one_iff _).mpr (A.mul_mem (2 : K) W.a₄ (natCast_mem A 2) ha₄)
  have h₃a₆v : v ((3 : K) * W.a₆) ≤ 1 :=
    (A.valuation_le_one_iff _).mpr (A.mul_mem (3 : K) W.a₆ (natCast_mem A 3) ha₆)
  have halt : v a < 1 := ha.trans_lt (pow_lt_one₀ zero_le hs (by decide))
  have hc₃₂ : v (W.a₂ * a) < 1 := by
    simp only [v, Valuation.map_mul]
    exact (mul_le_of_le_one_left zero_le ha₂v).trans_lt (ha.trans_lt
      (pow_lt_one₀ zero_le hs (by decide)))
  have hc₃₄ : v (W.a₄ * a ^ 2) < 1 := by
    simp only [v, Valuation.map_mul]
    exact (mul_le_of_le_one_left zero_le ha₄v).trans_lt
      (haa.trans_lt halt)
  have hc₃₆ : v (W.a₆ * a ^ 3) < 1 := by
    simp only [v, Valuation.map_mul]
    exact (mul_le_of_le_one_left zero_le ha₆v).trans_lt
      (haaa.trans_lt halt)
  constructor
  · rw [show nosLineC₃ W a =
        1 + (W.a₂ * a + W.a₄ * a ^ 2 + W.a₆ * a ^ 3) by
      simp only [nosLineC₃]
      ring]
    exact v.map_one_add_of_lt (v.map_add_lt (v.map_add_lt hc₃₂ hc₃₄) hc₃₆)
  · have h₁ : v (W.a₁ * a) ≤ s ^ 2 := by
      simp only [v, Valuation.map_mul]
      exact (mul_le_of_le_one_left zero_le ha₁v).trans ha
    have h₂ : v (W.a₂ * b) ≤ s ^ 2 := by
      simp only [v, Valuation.map_mul]
      exact (mul_le_of_le_one_left zero_le ha₂v).trans (hb.trans hs₃₂)
    have h₃ : v (W.a₃ * a ^ 2) ≤ s ^ 2 := by
      simp only [v, Valuation.map_mul]
      exact (mul_le_of_le_one_left zero_le ha₃v).trans (haa.trans ha)
    have h₄ : v (2 * W.a₄ * a * b) ≤ s ^ 2 := by
      simp only [v, Valuation.map_mul]
      exact (mul_le_of_le_one_right zero_le hbone).trans
        ((mul_le_of_le_one_left zero_le h₂a₄v).trans ha)
    have h₆ : v (3 * W.a₆ * a ^ 2 * b) ≤ s ^ 2 := by
      simp only [v, Valuation.map_mul]
      exact (mul_le_of_le_one_right zero_le hbone).trans
        ((mul_le_of_le_one_left zero_le h₃a₆v).trans (haa.trans ha))
    have hadd {x y : K} (hx : v x ≤ s ^ 2) (hy : v y ≤ s ^ 2) :
        v (x + y) ≤ s ^ 2 := (v.map_add x y).trans (max_le hx hy)
    exact hadd (hadd (hadd (hadd h₁ h₂) h₃) h₄) h₆

private lemma nos_line_intercept_bound {K : Type*} [Field K]
    (A : ValuationSubring K) {z w a : K} {s : A.ValueGroup}
    (hz : A.valuation z = s) (hw : A.valuation w = s ^ 3)
    (ha : A.valuation a ≤ s ^ 2) :
    A.valuation (w - a * z) ≤ s ^ 3 := by
  let v := A.valuation
  apply (v.map_sub w (a * z)).trans
  apply max_le
  · exact hw.le
  · simp only [v, Valuation.map_mul, hz]
    calc
      A.valuation a * s ≤ s ^ 2 * s := mul_le_mul_of_nonneg_right ha zero_le
      _ = s ^ 3 := (pow_succ s 2).symm

private lemma nos_vieta_sum_bound {K : Type*} [Field K] (W : WeierstrassCurve K)
    (A : ValuationSubring K) {z₁ z₂ z₃ a b : K} {s : A.ValueGroup}
    (ha₁ : W.a₁ ∈ A) (ha₂ : W.a₂ ∈ A) (ha₃ : W.a₃ ∈ A)
    (ha₄ : W.a₄ ∈ A) (ha₆ : W.a₆ ∈ A) (hs : s < 1)
    (ha : A.valuation a ≤ s ^ 2) (hb : A.valuation b ≤ s ^ 3)
    (hvieta : nosLineC₃ W a * (z₁ + z₂ + z₃) + nosLineC₂ W a b = 0) :
    A.valuation (z₁ + z₂ + z₃) ≤ s ^ 2 := by
  let v := A.valuation
  obtain ⟨hC₃, hC₂⟩ := nos_line_coefficients_bound W A ha₁ ha₂ ha₃ ha₄ ha₆ hs ha hb
  have heq : nosLineC₃ W a * (z₁ + z₂ + z₃) = -nosLineC₂ W a b := by
    linear_combination hvieta
  have hval := congrArg v heq
  simp only [Valuation.map_mul, Valuation.map_neg] at hval
  change v (nosLineC₃ W a) = 1 at hC₃
  rw [hC₃, one_mul] at hval
  change v (z₁ + z₂ + z₃) ≤ s ^ 2
  rw [hval]
  exact hC₂

private lemma nos_neg_z_formula {K : Type*} [Field K] (W : WeierstrassCurve K)
    {x y : K} (hy : y ≠ 0) (hneg : WeierstrassCurve.Affine.negY W x y ≠ 0) :
    -x / WeierstrassCurve.Affine.negY W x y =
      -(-x / y) / (1 - W.a₁ * (-x / y) - W.a₃ * (-1 / y)) := by
  simp only [WeierstrassCurve.Affine.negY] at hneg ⊢
  have hpos : x * W.a₁ + y + W.a₃ ≠ 0 := by
    intro h
    apply hneg
    linear_combination -h
  field_simp [hy, hneg, hpos]
  rw [show -y - x * W.a₁ - W.a₃ = -(x * W.a₁ + y + W.a₃) by ring,
    show y - -(x * W.a₁) - -W.a₃ = x * W.a₁ + y + W.a₃ by ring, div_neg]
  ring

private lemma nos_neg_parameter {K : Type*} [Field K] (W : WeierstrassCurve K)
    (A : ValuationSubring K) {z w : K}
    (ha₁ : W.a₁ ∈ A) (ha₃ : W.a₃ ∈ A)
    (hz : A.valuation z < 1) (hz0 : z ≠ 0)
    (hw : A.valuation w = A.valuation z ^ 3) :
    let d := 1 - W.a₁ * z - W.a₃ * w
    A.valuation d = 1 ∧ A.valuation (-z / d + z) < A.valuation z ∧
      A.valuation (-z / d) = A.valuation z := by
  let v := A.valuation
  let d := 1 - W.a₁ * z - W.a₃ * w
  have ha₁v : v W.a₁ ≤ 1 := (A.valuation_le_one_iff W.a₁).mpr ha₁
  have ha₃v : v W.a₃ ≤ 1 := (A.valuation_le_one_iff W.a₃).mpr ha₃
  have hw' : v w < 1 := by
    rw [hw]
    exact pow_lt_one₀ zero_le hz (by decide)
  have ha₁z : v (W.a₁ * z) < 1 := by
    simp only [v, Valuation.map_mul]
    exact (mul_le_of_le_one_left zero_le ha₁v).trans_lt hz
  have ha₃w : v (W.a₃ * w) < 1 := by
    simp only [v, Valuation.map_mul]
    exact (mul_le_of_le_one_left zero_le ha₃v).trans_lt hw'
  have ht : v (W.a₁ * z + W.a₃ * w) < 1 := v.map_add_lt ha₁z ha₃w
  have hd : v d = 1 := by
    change v (1 - W.a₁ * z - W.a₃ * w) = 1
    rw [show 1 - W.a₁ * z - W.a₃ * w = 1 - (W.a₁ * z + W.a₃ * w) by ring]
    exact v.map_one_sub_of_lt ht
  have hd0 : d ≠ 0 := by
    apply v.ne_zero_iff.mp
    rw [hd]
    exact one_ne_zero
  have hdsub : v (d - 1) < 1 := by
    change v ((1 - W.a₁ * z - W.a₃ * w) - 1) < 1
    rw [show (1 - W.a₁ * z - W.a₃ * w) - 1 =
      -(W.a₁ * z + W.a₃ * w) by ring, v.map_neg]
    exact ht
  refine ⟨hd, ?_, ?_⟩
  · rw [show -z / d + z = z * (d - 1) / d by field_simp [hd0]; ring,
      v.map_div, v.map_mul, hd, div_one]
    simpa only [mul_one] using mul_lt_mul_of_pos_left hdsub (v.pos_iff.mpr hz0)
  · change v (-z / d) = v z
    rw [v.map_div, v.map_neg, hd, div_one]

private lemma nos_y_mem_of_x_mem {K : Type*} [Field K] (W : WeierstrassCurve K)
    (A : ValuationSubring K) {x y : K}
    (ha₁ : W.a₁ ∈ A) (ha₂ : W.a₂ ∈ A) (ha₃ : W.a₃ ∈ A)
    (ha₄ : W.a₄ ∈ A) (ha₆ : W.a₆ ∈ A) (hx : x ∈ A)
    (hxy : WeierstrassCurve.Affine.Equation W x y) : y ∈ A := by
  let a₁ : A := ⟨W.a₁, ha₁⟩
  let a₂ : A := ⟨W.a₂, ha₂⟩
  let a₃ : A := ⟨W.a₃, ha₃⟩
  let a₄ : A := ⟨W.a₄, ha₄⟩
  let a₆ : A := ⟨W.a₆, ha₆⟩
  let xA : A := ⟨x, hx⟩
  let p : Polynomial A := Polynomial.X ^ 2 + Polynomial.C (a₁ * xA + a₃) * Polynomial.X -
    Polynomial.C (xA ^ 3 + a₂ * xA ^ 2 + a₄ * xA + a₆)
  have hp : p.Monic := by
    dsimp [p]
    monicity!
  have hpy : Polynomial.aeval y p = 0 := by
    rw [WeierstrassCurve.Affine.equation_iff (W := W) x y] at hxy
    simp only [p, map_sub, map_add, map_mul, map_pow, Polynomial.aeval_X,
      Polynomial.aeval_C]
    change y ^ 2 + (W.a₁ * x + W.a₃) * y -
      (x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆) = 0
    linear_combination hxy
  have hy : IsIntegral A y := ⟨p, hp, hpy⟩
  obtain ⟨yA, hyA⟩ := IsIntegrallyClosed.isIntegral_iff.mp hy
  rw [← hyA]
  exact yA.property

private lemma nos_x_mem_of_y_mem {K : Type*} [Field K] (W : WeierstrassCurve K)
    (A : ValuationSubring K) {x y : K}
    (ha₁ : W.a₁ ∈ A) (ha₂ : W.a₂ ∈ A) (ha₃ : W.a₃ ∈ A)
    (ha₄ : W.a₄ ∈ A) (ha₆ : W.a₆ ∈ A) (hy : y ∈ A)
    (hxy : WeierstrassCurve.Affine.Equation W x y) : x ∈ A := by
  let a₁ : A := ⟨W.a₁, ha₁⟩
  let a₂ : A := ⟨W.a₂, ha₂⟩
  let a₃ : A := ⟨W.a₃, ha₃⟩
  let a₄ : A := ⟨W.a₄, ha₄⟩
  let a₆ : A := ⟨W.a₆, ha₆⟩
  let yA : A := ⟨y, hy⟩
  let p : Polynomial A := Polynomial.X ^ 3 + Polynomial.C a₂ * Polynomial.X ^ 2 +
    Polynomial.C (a₄ - a₁ * yA) * Polynomial.X +
      Polynomial.C (a₆ - yA ^ 2 - a₃ * yA)
  have hp : p.Monic := by
    dsimp [p]
    monicity!
  have hpx : Polynomial.aeval x p = 0 := by
    rw [WeierstrassCurve.Affine.equation_iff (W := W) x y] at hxy
    simp only [p, map_sub, map_add, map_mul, map_pow, Polynomial.aeval_X,
      Polynomial.aeval_C]
    change x ^ 3 + W.a₂ * x ^ 2 + (W.a₄ - W.a₁ * y) * x +
      (W.a₆ - y ^ 2 - W.a₃ * y) = 0
    linear_combination -hxy
  have hx : IsIntegral A x := ⟨p, hp, hpx⟩
  obtain ⟨xA, hxA⟩ := IsIntegrallyClosed.isIntegral_iff.mp hx
  rw [← hxA]
  exact xA.property

private lemma nos_cubic_dominant {K : Type*} [Field K] (W : WeierstrassCurve K)
    (A : ValuationSubring K) {x : K} (ha₂ : W.a₂ ∈ A) (ha₄ : W.a₄ ∈ A)
    (ha₆ : W.a₆ ∈ A) (hx : x ∉ A) :
    A.valuation (x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆) =
      A.valuation (x ^ 3) := by
  let v := A.valuation
  have hxv : 1 < v x := by
    rw [← not_le]
    exact fun h ↦ hx ((A.valuation_le_one_iff x).mp h)
  have ha₂v : v W.a₂ ≤ 1 := (A.valuation_le_one_iff W.a₂).mpr ha₂
  have ha₄v : v W.a₄ ≤ 1 := (A.valuation_le_one_iff W.a₄).mpr ha₄
  have ha₆v : v W.a₆ ≤ 1 := (A.valuation_le_one_iff W.a₆).mpr ha₆
  have h₂ : v (W.a₂ * x ^ 2) < v (x ^ 3) := by
    simp only [v, Valuation.map_mul, Valuation.map_pow]
    exact mul_lt_of_le_one_of_lt ha₂v (pow_lt_pow_right₀ hxv (by decide))
  have h₄ : v (W.a₄ * x) < v (x ^ 3) := by
    simp only [v, Valuation.map_mul, Valuation.map_pow]
    exact mul_lt_of_le_one_of_lt ha₄v (by
      simpa only [pow_one] using pow_lt_pow_right₀ hxv (by decide : 1 < 3))
  have h₆ : v W.a₆ < v (x ^ 3) := by
    simp only [v, Valuation.map_pow]
    exact ha₆v.trans_lt (by
      simpa only [pow_zero] using pow_lt_pow_right₀ hxv (by decide : 0 < 3))
  have h₃₂ : v (x ^ 3 + W.a₂ * x ^ 2) = v (x ^ 3) :=
    v.map_add_eq_of_lt_left h₂
  have h₃₂₄ : v (x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x) = v (x ^ 3) := by
    rw [v.map_add_eq_of_lt_left]
    · exact h₃₂
    · rwa [h₃₂]
  rw [v.map_add_eq_of_lt_left]
  · exact h₃₂₄
  · rwa [h₃₂₄]

private lemma nos_nonintegral_valuations {K : Type*} [Field K] (W : WeierstrassCurve K)
    (A : ValuationSubring K) {x y : K}
    (ha₁ : W.a₁ ∈ A) (ha₂ : W.a₂ ∈ A) (ha₃ : W.a₃ ∈ A)
    (ha₄ : W.a₄ ∈ A) (ha₆ : W.a₆ ∈ A) (hx : x ∉ A)
    (hxy : WeierstrassCurve.Affine.Equation W x y) :
    y ∉ A ∧ A.valuation x < A.valuation y ∧
      A.valuation (y ^ 2) = A.valuation (x ^ 3) := by
  let v := A.valuation
  have hy : y ∉ A := fun hy ↦ hx (nos_x_mem_of_y_mem W A ha₁ ha₂ ha₃ ha₄ ha₆ hy hxy)
  have hxv : 1 < v x := by
    rw [← not_le]
    exact fun h ↦ hx ((A.valuation_le_one_iff x).mp h)
  have hyv : 1 < v y := by
    rw [← not_le]
    exact fun h ↦ hy ((A.valuation_le_one_iff y).mp h)
  have ha₁v : v W.a₁ ≤ 1 := (A.valuation_le_one_iff W.a₁).mpr ha₁
  have ha₃v : v W.a₃ ≤ 1 := (A.valuation_le_one_iff W.a₃).mpr ha₃
  have hrhs := nos_cubic_dominant W A ha₂ ha₄ ha₆ hx
  have heq := congrArg v ((WeierstrassCurve.Affine.equation_iff (W := W) x y).mp hxy)
  have hvxy : v x < v y := by
    by_contra h
    have hyx : v y ≤ v x := le_of_not_gt h
    have hy2 : v (y ^ 2) < v (x ^ 3) := by
      simp only [v, Valuation.map_pow]
      exact (pow_le_pow_left₀ zero_le hyx 2).trans_lt
        (pow_lt_pow_right₀ hxv (by decide : 2 < 3))
    have ha₁xy : v (W.a₁ * x * y) < v (x ^ 3) := by
      simp only [v, Valuation.map_mul, Valuation.map_pow]
      calc
        v W.a₁ * v x * v y ≤ 1 * v x * v y :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ha₁v zero_le) zero_le
        _ = v x * v y := by rw [one_mul]
        _ ≤ v x * v x := mul_le_mul_of_nonneg_left hyx zero_le
        _ = (v x) ^ 2 := (pow_two _).symm
        _ < (v x) ^ 3 := pow_lt_pow_right₀ hxv (by decide)
    have ha₃y : v (W.a₃ * y) < v (x ^ 3) := by
      simp only [v, Valuation.map_mul, Valuation.map_pow]
      calc
        v W.a₃ * v y ≤ 1 * v y := mul_le_mul_of_nonneg_right ha₃v zero_le
        _ = v y := one_mul _
        _ ≤ v x := hyx
        _ = (v x) ^ 1 := (pow_one _).symm
        _ < (v x) ^ 3 := pow_lt_pow_right₀ hxv (by decide)
    have hlhs : v (y ^ 2 + W.a₁ * x * y + W.a₃ * y) < v (x ^ 3) :=
      v.map_add_lt (v.map_add_lt hy2 ha₁xy) ha₃y
    rw [hrhs] at heq
    exact (ne_of_lt hlhs) heq
  have ha₁xy : v (W.a₁ * x * y) < v (y ^ 2) := by
    simp only [v, Valuation.map_mul, Valuation.map_pow]
    calc
      v W.a₁ * v x * v y ≤ 1 * v x * v y :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ha₁v zero_le) zero_le
      _ = v x * v y := by rw [one_mul]
      _ < v y * v y := mul_lt_mul_of_pos_right hvxy (zero_lt_one.trans hyv)
      _ = (v y) ^ 2 := (pow_two _).symm
  have ha₃y : v (W.a₃ * y) < v (y ^ 2) := by
    simp only [v, Valuation.map_mul, Valuation.map_pow]
    calc
      v W.a₃ * v y ≤ 1 * v y := mul_le_mul_of_nonneg_right ha₃v zero_le
      _ = v y := one_mul _
      _ < v y * v y := lt_mul_self hyv
      _ = (v y) ^ 2 := (pow_two _).symm
  have hlhs : v (y ^ 2 + W.a₁ * x * y + W.a₃ * y) = v (y ^ 2) := by
    rw [v.map_add_eq_of_lt_left]
    · exact v.map_add_eq_of_lt_left ha₁xy
    · rwa [v.map_add_eq_of_lt_left ha₁xy]
  refine ⟨hy, hvxy, ?_⟩
  rw [← hlhs, heq, hrhs]

private lemma nos_local_coordinate_valuations {K : Type*} [Field K]
    (W : WeierstrassCurve K) (A : ValuationSubring K) {x y : K}
    (ha₁ : W.a₁ ∈ A) (ha₂ : W.a₂ ∈ A) (ha₃ : W.a₃ ∈ A)
    (ha₄ : W.a₄ ∈ A) (ha₆ : W.a₆ ∈ A) (hx : x ∉ A)
    (hxy : WeierstrassCurve.Affine.Equation W x y) :
    y ≠ 0 ∧ -x / y ∈ A.nonunits ∧
      A.valuation (-1 / y) = A.valuation (-x / y) ^ 3 := by
  let v := A.valuation
  obtain ⟨hy, hvxy, hpow⟩ := nos_nonintegral_valuations W A ha₁ ha₂ ha₃ ha₄ ha₆ hx hxy
  have hy0 : y ≠ 0 := fun h ↦ hy (h ▸ A.zero_mem)
  have hvy0 : v y ≠ 0 := v.ne_zero_iff.mpr hy0
  refine ⟨hy0, ?_, ?_⟩
  · rw [A.mem_nonunits_iff]
    simp only [Valuation.map_div, Valuation.map_neg]
    exact (div_lt_one₀ (v.pos_iff.mpr hy0)).mpr hvxy
  · simp only [Valuation.map_div, Valuation.map_neg, Valuation.map_one]
    rw [div_pow]
    have hpow' : (v y) ^ 2 = (v x) ^ 3 := by
      simpa only [v, Valuation.map_pow] using hpow
    rw [← hpow']
    apply (div_eq_div_iff hvy0 (pow_ne_zero 3 hvy0)).mpr
    simp only [one_mul, pow_succ]

private lemma nos_finish_add {K : Type*} [Field K] (W : WeierstrassCurve K)
    (A : ValuationSubring K) {x₃ y₃ z₁ z₂ z₃ a b : K} {s : A.ValueGroup}
    (ha₁ : W.a₁ ∈ A) (ha₂ : W.a₂ ∈ A) (ha₃ : W.a₃ ∈ A)
    (ha₄ : W.a₄ ∈ A) (ha₆ : W.a₆ ∈ A)
    (h₃ : WeierstrassCurve.Affine.Equation W x₃ y₃) (hy₃ : y₃ ≠ 0)
    (hz₃ : z₃ = -x₃ / y₃) (hline₃ : -1 / y₃ = a * z₃ + b)
    (hs0 : 0 < s) (hs : s < 1) (hz₁ : A.valuation z₁ = s)
    (hz₂ : A.valuation z₂ ≤ s) (ha : A.valuation a ≤ s ^ 2)
    (hb : A.valuation b ≤ s ^ 3)
    (hsum : A.valuation (z₁ + z₂ + z₃) ≤ s ^ 2) :
    x₃ ∉ A ∧ A.valuation
      (-x₃ / WeierstrassCurve.Affine.negY W x₃ y₃ - z₁ - z₂) < s := by
  let v := A.valuation
  have hs₂s : s ^ 2 < s := pow_lt_self_of_lt_one₀ hs0 hs (by decide)
  have hz₃le : v z₃ ≤ s := by
    rw [show z₃ = (z₁ + z₂ + z₃) - z₁ - z₂ by ring]
    exact (v.map_sub _ _).trans (max_le
      ((v.map_sub _ _).trans (max_le (hsum.trans hs₂s.le) hz₁.le)) hz₂)
  have haw : v (a * z₃) ≤ s ^ 3 := by
    simp only [v, Valuation.map_mul]
    calc
      v a * v z₃ ≤ s ^ 2 * s :=
        mul_le_mul ha hz₃le zero_le (pow_nonneg zero_le 2)
      _ = s ^ 3 := (pow_succ s 2).symm
  have hw₃ : v (-1 / y₃) ≤ s ^ 3 := by
    rw [hline₃]
    exact (v.map_add _ _).trans (max_le haw hb)
  have hw₃lt : v (-1 / y₃) < 1 :=
    hw₃.trans_lt (pow_lt_one₀ zero_le hs (by decide))
  have hy₃not : y₃ ∉ A := by
    intro hyA
    have hyv : v y₃ ≤ 1 := (A.valuation_le_one_iff y₃).mpr hyA
    have hyv0 : 0 < v y₃ := v.pos_iff.mpr hy₃
    have hone : 1 ≤ v (-1 / y₃) := by
      simp only [v, Valuation.map_div, Valuation.map_neg, Valuation.map_one]
      simpa only [one_div] using (one_le_inv₀ hyv0).mpr hyv
    exact (not_lt_of_ge hone) hw₃lt
  have hx₃not : x₃ ∉ A := fun hxA ↦ hy₃not
    (nos_y_mem_of_x_mem W A ha₁ ha₂ ha₃ ha₄ ha₆ hxA h₃)
  refine ⟨hx₃not, ?_⟩
  obtain ⟨_, hz₃nonunit, hwz₃⟩ :=
    nos_local_coordinate_valuations W A ha₁ ha₂ ha₃ ha₄ ha₆ hx₃not h₃
  have hz₃lt : v z₃ < 1 := by
    rw [hz₃]
    exact (A.mem_nonunits_iff.mpr hz₃nonunit)
  have hx₃0 : x₃ ≠ 0 := fun hx ↦ hx₃not (hx ▸ A.zero_mem)
  have hz₃0 : z₃ ≠ 0 := by
    rw [hz₃]
    exact div_ne_zero (neg_ne_zero.mpr hx₃0) hy₃
  have hneg : WeierstrassCurve.Affine.negY W x₃ y₃ ≠ 0 := by
    intro hzero
    have hyneg : WeierstrassCurve.Affine.negY W x₃ y₃ ∈ A := hzero ▸ A.zero_mem
    exact hx₃not (nos_x_mem_of_y_mem W A ha₁ ha₂ ha₃ ha₄ ha₆ hyneg
      ((WeierstrassCurve.Affine.equation_neg x₃ y₃).mpr h₃))
  have hform := nos_neg_z_formula W hy₃ hneg
  rw [← hz₃] at hwz₃
  obtain ⟨_, hnegerr, _⟩ := nos_neg_parameter W A ha₁ ha₃ hz₃lt hz₃0 hwz₃
  rw [hform, ← hz₃]
  rw [show -z₃ / (1 - W.a₁ * z₃ - W.a₃ * (-1 / y₃)) - z₁ - z₂ =
      (-z₃ / (1 - W.a₁ * z₃ - W.a₃ * (-1 / y₃)) + z₃) -
        (z₁ + z₂ + z₃) by ring]
  exact v.map_sub_lt (hnegerr.trans_le hz₃le) (hsum.trans_lt hs₂s)

private lemma nos_secant_add {K : Type*} [Field K] [DecidableEq K]
    (W : WeierstrassCurve K) (A : ValuationSubring K) {x₁ x₂ y₁ y₂ : K}
    {s : A.ValueGroup} (ha₁ : W.a₁ ∈ A) (ha₂ : W.a₂ ∈ A) (ha₃ : W.a₃ ∈ A)
    (ha₄ : W.a₄ ∈ A) (ha₆ : W.a₆ ∈ A)
    (h₁ : WeierstrassCurve.Affine.Equation W x₁ y₁)
    (h₂ : WeierstrassCurve.Affine.Equation W x₂ y₂)
    (hx₁ : x₁ ∉ A) (hx₂ : x₂ ∉ A) (hx : x₁ ≠ x₂) (hs0 : 0 < s)
    (hz₁val : A.valuation (-x₁ / y₁) = s) (hz₂val : A.valuation (-x₂ / y₂) ≤ s) :
    let l := WeierstrassCurve.Affine.slope W x₁ x₂ y₁ y₂
    let x₃ := WeierstrassCurve.Affine.addX W x₁ x₂ l
    let y₃ := WeierstrassCurve.Affine.negAddY W x₁ x₂ y₁ l
    x₃ ∉ A ∧ A.valuation
      (-x₃ / WeierstrassCurve.Affine.negY W x₃ y₃ - (-x₁ / y₁) - (-x₂ / y₂)) < s := by
  let v := A.valuation
  let z₁ := -x₁ / y₁
  let z₂ := -x₂ / y₂
  let w₁ := -1 / y₁
  let w₂ := -1 / y₂
  let l := WeierstrassCurve.Affine.slope W x₁ x₂ y₁ y₂
  let c := y₁ - l * x₁
  let a := -l / c
  let b := -1 / c
  let x₃ := WeierstrassCurve.Affine.addX W x₁ x₂ l
  let y₃ := WeierstrassCurve.Affine.negAddY W x₁ x₂ y₁ l
  let z₃ := -x₃ / y₃
  dsimp only
  change x₃ ∉ A ∧ v (-x₃ / WeierstrassCurve.Affine.negY W x₃ y₃ - z₁ - z₂) < s
  obtain ⟨hy₁, hz₁nonunit, hw₁⟩ :=
    nos_local_coordinate_valuations W A ha₁ ha₂ ha₃ ha₄ ha₆ hx₁ h₁
  obtain ⟨hy₂, _, hw₂⟩ :=
    nos_local_coordinate_valuations W A ha₁ ha₂ ha₃ ha₄ ha₆ hx₂ h₂
  have hs : s < 1 := by
    rw [← hz₁val]
    exact A.mem_nonunits_iff.mpr hz₁nonunit
  have hl : l = (y₁ - y₂) / (x₁ - x₂) := by
    exact WeierstrassCurve.Affine.slope_of_X_ne hx
  have hy₁line : y₁ = l * x₁ + c := by simp only [c]; ring
  have hy₂line : y₂ = l * x₂ + c := by
    simp only [c]
    rw [hl]
    field_simp [sub_ne_zero.mpr hx]
    ring
  have hx₃line : x₃ = nosLineQ₂ W l - x₁ - x₂ := by
    simp only [x₃, WeierstrassCurve.Affine.addX, nosLineQ₂]
  have hy₃line : y₃ = l * x₃ + c := by
    simp only [y₃, WeierstrassCurve.Affine.negAddY, x₃, c]
    ring
  have hlocal₁ := nos_local_equation W h₁ hy₁
  have hlocal₂ := nos_local_equation W h₂ hy₂
  change nosLocalEquation W z₁ w₁ at hlocal₁
  change nosLocalEquation W z₂ w₂ at hlocal₂
  have hz₁lt : v z₁ < 1 := by rw [hz₁val]; exact hs
  have hz₂le : v z₂ ≤ v z₁ := by rw [hz₁val]; exact hz₂val
  have hUval := nos_chord_U_unit W A ha₁ ha₂ ha₃ ha₄ ha₆ hz₁lt hz₂le hw₁ hw₂
  have hU0 : nosChordU W z₁ w₁ w₂ ≠ 0 := by
    apply v.ne_zero_iff.mp
    change v (nosChordU W z₁ w₁ w₂) ≠ 0
    rw [hUval]
    exact one_ne_zero
  have hzneq := nos_chord_z_ne W hx hy₁ hy₂ rfl rfl rfl rfl hlocal₁ hlocal₂ hU0
  have hc0 := nos_line_intercept_ne hy₁ hy₂ hy₁line hy₂line hzneq
  have hw₁line : w₁ = a * z₁ + b := nos_transformed_line hy₁ hc0 hy₁line
  have hw₂line : w₂ = a * z₂ + b := nos_transformed_line hy₂ hc0 hy₂line
  obtain ⟨haeq, hbeq⟩ := nos_line_slope hzneq hw₁line hw₂line
  have habound : v a ≤ s ^ 2 := by
    rw [haeq]
    have hbound := nos_chord_slope_bound W A ha₁ ha₂ ha₃ ha₄ ha₆ hz₁lt hz₂le hw₁ hw₂
      hlocal₁ hlocal₂ hzneq
    change v ((w₂ - w₁) / (z₂ - z₁)) ≤ v z₁ ^ 2 at hbound
    rw [hz₁val] at hbound
    exact hbound
  have hbbound : v b ≤ s ^ 3 := by
    rw [hbeq]
    have hw₁s : v w₁ = s ^ 3 := by
      change v (-1 / y₁) = s ^ 3
      rw [hw₁, hz₁val]
    apply nos_line_intercept_bound A hz₁val hw₁s
    · exact habound
  have hr₁ := nos_line_root W h₁ hy₁line
  have hr₂ := nos_line_root W h₂ hy₂line
  obtain ⟨hs₂, hs₃⟩ := nos_secant_symmetric W hr₁ hr₂ hx
  have hs₁ : nosLineQ₂ W l = x₁ + x₂ + x₃ := by rw [hx₃line]; ring
  have hs₂' : nosLineQ₁ W l c = -(x₁ * x₂ + x₁ * x₃ + x₂ * x₃) := by
    simpa only [hx₃line] using hs₂
  have hs₃' : nosLineQ₀ W c = x₁ * x₂ * x₃ := by
    simpa only [hx₃line] using hs₃
  obtain ⟨hC₃, _⟩ := nos_line_coefficients_bound W A ha₁ ha₂ ha₃ ha₄ ha₆ hs habound hbbound
  have hC₃0 : nosLineC₃ W a ≠ 0 := by
    apply v.ne_zero_iff.mp
    change v (nosLineC₃ W a) ≠ 0
    rw [hC₃]
    exact one_ne_zero
  have hlead := nos_transformed_leading W hs₁ hs₂' hs₃' hy₁line hy₂line hy₃line hc0
  change nosLineC₃ W a = y₁ * y₂ * y₃ / c ^ 3 at hlead
  have hy₃ : y₃ ≠ 0 := by
    intro hyzero
    rw [hyzero, mul_zero, zero_div] at hlead
    exact hC₃0 hlead
  have hvieta := nos_secant_vieta W h₁ h₂ hx hy₁line hy₂line hy₃line hx₃line
    hy₁ hy₂ hy₃ hc0
  change nosLineC₃ W a * (z₁ + z₂ + z₃) + nosLineC₂ W a b = 0 at hvieta
  have hsum := nos_vieta_sum_bound W A ha₁ ha₂ ha₃ ha₄ ha₆ hs habound hbbound hvieta
  have h₃ := WeierstrassCurve.Affine.equation_negAdd h₁ h₂ (fun h ↦ hx h.1)
  have hw₃line : -1 / y₃ = a * z₃ + b := nos_transformed_line hy₃ hc0 hy₃line
  exact nos_finish_add W A ha₁ ha₂ ha₃ ha₄ ha₆ h₃ hy₃ rfl hw₃line hs0 hs
    hz₁val hz₂val habound hbbound hsum

private lemma nos_tangent_add {K : Type*} [Field K] [DecidableEq K]
    (W : WeierstrassCurve K) (A : ValuationSubring K) {x y : K} {s : A.ValueGroup}
    (ha₁ : W.a₁ ∈ A) (ha₂ : W.a₂ ∈ A) (ha₃ : W.a₃ ∈ A)
    (ha₄ : W.a₄ ∈ A) (ha₆ : W.a₆ ∈ A)
    (h : WeierstrassCurve.Affine.Equation W x y) (hx : x ∉ A)
    (hyneg : y ≠ WeierstrassCurve.Affine.negY W x y) (hs0 : 0 < s)
    (hzval : A.valuation (-x / y) = s) :
    let l := WeierstrassCurve.Affine.slope W x x y y
    let x₃ := WeierstrassCurve.Affine.addX W x x l
    let y₃ := WeierstrassCurve.Affine.negAddY W x x y l
    x₃ ∉ A ∧ A.valuation
      (-x₃ / WeierstrassCurve.Affine.negY W x₃ y₃ - (-x / y) - (-x / y)) < s := by
  let v := A.valuation
  let z := -x / y
  let w := -1 / y
  let l := WeierstrassCurve.Affine.slope W x x y y
  let c := y - l * x
  let a := -l / c
  let b := -1 / c
  let x₃ := WeierstrassCurve.Affine.addX W x x l
  let y₃ := WeierstrassCurve.Affine.negAddY W x x y l
  let z₃ := -x₃ / y₃
  dsimp only
  change x₃ ∉ A ∧ v (-x₃ / WeierstrassCurve.Affine.negY W x₃ y₃ - z - z) < s
  obtain ⟨hy, hznonunit, hw⟩ :=
    nos_local_coordinate_valuations W A ha₁ ha₂ ha₃ ha₄ ha₆ hx h
  have hs : s < 1 := by
    rw [← hzval]
    exact A.mem_nonunits_iff.mpr hznonunit
  have hden : 2 * y + W.a₁ * x + W.a₃ ≠ 0 := by
    intro hzero
    apply hyneg
    simp only [WeierstrassCurve.Affine.negY]
    linear_combination hzero
  have hl : l = (3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ - W.a₁ * y) /
      (2 * y + W.a₁ * x + W.a₃) := by
    change WeierstrassCurve.Affine.slope W x x y y = _
    rw [WeierstrassCurve.Affine.slope_of_Y_ne rfl hyneg]
    congr 1
    simp only [WeierstrassCurve.Affine.negY]
    ring
  have hyline : y = l * x + c := by simp only [c]; ring
  have hx₃line : x₃ = nosLineQ₂ W l - 2 * x := by
    simp only [x₃, WeierstrassCurve.Affine.addX, nosLineQ₂]
    ring
  have hy₃line : y₃ = l * x₃ + c := by
    simp only [y₃, WeierstrassCurve.Affine.negAddY, x₃, c]
    ring
  have hlmul : l * (2 * y + W.a₁ * x + W.a₃) =
      3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ - W.a₁ * y := by
    rw [hl]
    exact div_mul_cancel₀ _ hden
  have hderiv := nos_tangent_derivative_of_mul W rfl hlmul
  have hlocal := nos_local_equation W h hy
  change nosLocalEquation W z w at hlocal
  have hzlt : v z < 1 := by rw [hzval]; exact hs
  have hUval := nos_tangent_U_unit W A ha₁ ha₂ ha₃ ha₄ ha₆ hzlt hw
  have hU0 : nosChordU W z w w ≠ 0 := by
    apply v.ne_zero_iff.mp
    change v (nosChordU W z w w) ≠ 0
    rw [hUval]
    exact one_ne_zero
  obtain ⟨hc0, haeq, hbeq⟩ := nos_tangent_transform W h hy hden rfl rfl hl rfl hU0
  have habound : v a ≤ s ^ 2 := by
    change v (-l / c) ≤ s ^ 2
    rw [haeq]
    have hbound := nos_tangent_slope_bound W A ha₁ ha₂ ha₃ ha₄ ha₆ hzlt hw
    change v (nosChordV W z z w / nosChordU W z w w) ≤ v z ^ 2 at hbound
    rw [hzval] at hbound
    exact hbound
  have hbbound : v b ≤ s ^ 3 := by
    change v (-1 / c) ≤ s ^ 3
    rw [hbeq]
    have hws : v w = s ^ 3 := by
      change v (-1 / y) = s ^ 3
      rw [hw, hzval]
    have habound' : v (nosChordV W z z w / nosChordU W z w w) ≤ s ^ 2 := by
      rw [← haeq]
      exact habound
    exact nos_line_intercept_bound A hzval hws habound'
  have hroot := nos_line_root W h hyline
  obtain ⟨hs₂, hs₃⟩ := nos_tangent_symmetric W hroot hderiv
  have hs₁ : nosLineQ₂ W l = x + x + x₃ := by rw [hx₃line]; ring
  have hs₂' : nosLineQ₁ W l c = -(x * x + x * x₃ + x * x₃) := by
    simpa only [hx₃line] using hs₂
  have hs₃' : nosLineQ₀ W c = x * x * x₃ := by
    simpa only [hx₃line] using hs₃
  obtain ⟨hC₃, _⟩ := nos_line_coefficients_bound W A ha₁ ha₂ ha₃ ha₄ ha₆ hs habound hbbound
  have hC₃0 : nosLineC₃ W a ≠ 0 := by
    apply v.ne_zero_iff.mp
    change v (nosLineC₃ W a) ≠ 0
    rw [hC₃]
    exact one_ne_zero
  have hlead := nos_transformed_leading W hs₁ hs₂' hs₃' hyline hyline hy₃line hc0
  change nosLineC₃ W a = y * y * y₃ / c ^ 3 at hlead
  have hy₃ : y₃ ≠ 0 := by
    intro hyzero
    rw [hyzero, mul_zero, zero_div] at hlead
    exact hC₃0 hlead
  have hvieta := nos_tangent_vieta W h hyline hy₃line hx₃line hderiv hy hy₃ hc0
  change nosLineC₃ W a * (z + z + z₃) + nosLineC₂ W a b = 0 at hvieta
  have hsum := nos_vieta_sum_bound W A ha₁ ha₂ ha₃ ha₄ ha₆ hs habound hbbound hvieta
  have h₃ := WeierstrassCurve.Affine.equation_negAdd h h (fun hxy ↦ hyneg hxy.2)
  have hw₃line : -1 / y₃ = a * z₃ + b := nos_transformed_line hy₃ hc0 hy₃line
  exact nos_finish_add W A ha₁ ha₂ ha₃ ha₄ ha₆ h₃ hy₃ rfl hw₃line hs0 hs
    hzval hzval.le habound hbbound hsum

private def nosNear {K : Type*} [Field K] (W : WeierstrassCurve K)
    (A : ValuationSubring K) : WeierstrassCurve.Affine.Point W → Prop
  | .zero => True
  | .some x _ _ => x ∉ A

private def nosZ {K : Type*} [Field K] (W : WeierstrassCurve K) :
    WeierstrassCurve.Affine.Point W → K
  | .zero => 0
  | .some x y _ => -x / y

private lemma nos_neg_coordinate {K : Type*} [Field K] (W : WeierstrassCurve K)
    (A : ValuationSubring K) {x y : K}
    (ha₁ : W.a₁ ∈ A) (ha₂ : W.a₂ ∈ A) (ha₃ : W.a₃ ∈ A)
    (ha₄ : W.a₄ ∈ A) (ha₆ : W.a₆ ∈ A) (hx : x ∉ A)
    (h : WeierstrassCurve.Affine.Equation W x y) :
    A.valuation (-x / WeierstrassCurve.Affine.negY W x y + -x / y) <
      A.valuation (-x / y) := by
  obtain ⟨hy, hznonunit, hw⟩ :=
    nos_local_coordinate_valuations W A ha₁ ha₂ ha₃ ha₄ ha₆ hx h
  have hzlt : A.valuation (-x / y) < 1 := A.mem_nonunits_iff.mpr hznonunit
  have hx0 : x ≠ 0 := fun hzero ↦ hx (hzero ▸ A.zero_mem)
  have hz0 : -x / y ≠ 0 := div_ne_zero (neg_ne_zero.mpr hx0) hy
  have hneg : WeierstrassCurve.Affine.negY W x y ≠ 0 := by
    intro hzero
    have hyneg : WeierstrassCurve.Affine.negY W x y ∈ A := hzero ▸ A.zero_mem
    exact hx (nos_x_mem_of_y_mem W A ha₁ ha₂ ha₃ ha₄ ha₆ hyneg
      ((WeierstrassCurve.Affine.equation_neg x y).mpr h))
  have hform := nos_neg_z_formula W hy hneg
  obtain ⟨_, herr, _⟩ := nos_neg_parameter W A ha₁ ha₃ hzlt hz0 hw
  rw [hform]
  exact herr

private lemma nos_add_parameter {K : Type*} [Field K] [DecidableEq K]
    (W : WeierstrassCurve K) [W.IsElliptic] (A : ValuationSubring K)
    (ha₁ : W.a₁ ∈ A) (ha₂ : W.a₂ ∈ A) (ha₃ : W.a₃ ∈ A)
    (ha₄ : W.a₄ ∈ A) (ha₆ : W.a₆ ∈ A)
    {P Q : WeierstrassCurve.Affine.Point W} {s : A.ValueGroup}
    (hP : nosNear W A P) (hQ : nosNear W A Q) (hs0 : 0 < s)
    (hzP : A.valuation (nosZ W P) = s) (hzQ : A.valuation (nosZ W Q) ≤ s) :
    nosNear W A (P + Q) ∧
      A.valuation (nosZ W (P + Q) - nosZ W P - nosZ W Q) < s := by
  let v := A.valuation
  cases P with
  | zero =>
      exfalso
      have hz : (0 : A.ValueGroup) = s := by simpa only [nosZ, Valuation.map_zero] using hzP
      exact (ne_of_gt hs0) hz.symm
  | some x₁ y₁ hp₁ =>
    change x₁ ∉ A at hP
    change v (-x₁ / y₁) = s at hzP
    cases Q with
    | zero =>
        constructor
        · exact hP
        · change v ((-x₁ / y₁) - (-x₁ / y₁) - 0) < s
          simpa only [sub_self, zero_sub, Valuation.map_zero] using hs0
    | some x₂ y₂ hp₂ =>
      change x₂ ∉ A at hQ
      change v (-x₂ / y₂) ≤ s at hzQ
      have h₁ : WeierstrassCurve.Affine.Equation W x₁ y₁ := hp₁.1
      have h₂ : WeierstrassCurve.Affine.Equation W x₂ y₂ := hp₂.1
      by_cases hver : x₁ = x₂ ∧ y₁ = WeierstrassCurve.Affine.negY W x₂ y₂
      · rw [WeierstrassCurve.Affine.Point.add_of_Y_eq hver.1 hver.2]
        constructor
        · trivial
        · have herr := nos_neg_coordinate W A ha₁ ha₂ ha₃ ha₄ ha₆ hQ h₂
          have herrs := herr.trans_le hzQ
          change v (0 - (-x₁ / y₁) - (-x₂ / y₂)) < s
          rw [hver.1, hver.2]
          rw [show 0 - (-x₂ / WeierstrassCurve.Affine.negY W x₂ y₂) - (-x₂ / y₂) =
            -((-x₂ / WeierstrassCurve.Affine.negY W x₂ y₂) + -x₂ / y₂) by ring,
            v.map_neg]
          exact herrs
      · by_cases hx : x₁ = x₂
        · have hyne : y₁ ≠ WeierstrassCurve.Affine.negY W x₂ y₂ := fun hy ↦ hver ⟨hx, hy⟩
          have hyeq : y₁ = y₂ := WeierstrassCurve.Affine.Y_eq_of_Y_ne h₁ h₂ hx hyne
          subst x₂
          subst y₂
          have hadd := nos_tangent_add W A ha₁ ha₂ ha₃ ha₄ ha₆ h₁ hP hyne hs0 hzP
          rw [WeierstrassCurve.Affine.Point.add_self_of_Y_ne hyne]
          simpa only [nosNear, nosZ, WeierstrassCurve.Affine.addY] using hadd
        · have hadd := nos_secant_add W A ha₁ ha₂ ha₃ ha₄ ha₆ h₁ h₂ hP hQ hx hs0 hzP hzQ
          rw [WeierstrassCurve.Affine.Point.add_of_X_ne hx]
          simpa only [nosNear, nosZ, WeierstrassCurve.Affine.addY] using hadd

private lemma nos_nsmul_parameter {K : Type*} [Field K] [DecidableEq K]
    (W : WeierstrassCurve K) [W.IsElliptic] (A : ValuationSubring K)
    (ha₁ : W.a₁ ∈ A) (ha₂ : W.a₂ ∈ A) (ha₃ : W.a₃ ∈ A)
    (ha₄ : W.a₄ ∈ A) (ha₆ : W.a₆ ∈ A)
    {P : WeierstrassCurve.Affine.Point W} {s : A.ValueGroup}
    (hP : nosNear W A P) (hs0 : 0 < s) (hzP : A.valuation (nosZ W P) = s) :
    ∀ m : ℕ, nosNear W A (m • P) ∧
      A.valuation (nosZ W (m • P) - (m : K) * nosZ W P) < s ∧
      A.valuation (nosZ W (m • P)) ≤ s := by
  let v := A.valuation
  intro m
  induction m with
  | zero =>
      constructor
      · trivial
      constructor
      · simpa only [zero_nsmul, nosZ, Nat.cast_zero, zero_mul, sub_zero,
          Valuation.map_zero] using hs0
      · simpa only [zero_nsmul, nosZ, Valuation.map_zero] using hs0.le
  | succ m ih =>
      obtain ⟨hnear, herr, hzle⟩ := ih
      obtain ⟨haddnear, hadderr⟩ :=
        nos_add_parameter W A ha₁ ha₂ ha₃ ha₄ ha₆ hP hnear hs0 hzP hzle
      have htotal : v (nosZ W (P + m • P) - ((m + 1 : ℕ) : K) * nosZ W P) < s := by
        rw [show nosZ W (P + m • P) - ((m + 1 : ℕ) : K) * nosZ W P =
          (nosZ W (P + m • P) - nosZ W P - nosZ W (m • P)) +
            (nosZ W (m • P) - (m : K) * nosZ W P) by
          rw [Nat.cast_add, Nat.cast_one]
          ring]
        exact v.map_add_lt hadderr herr
      have hnat : v ((m + 1 : ℕ) : K) ≤ 1 :=
        (A.valuation_le_one_iff _).mpr (natCast_mem A (m + 1))
      have hcoeff : v (((m + 1 : ℕ) : K) * nosZ W P) ≤ s := by
        simp only [v, Valuation.map_mul]
        rw [hzP]
        exact mul_le_of_le_one_left zero_le hnat
      have hnextle : v (nosZ W (P + m • P)) ≤ s := by
        rw [show nosZ W (P + m • P) =
          (nosZ W (P + m • P) - ((m + 1 : ℕ) : K) * nosZ W P) +
            ((m + 1 : ℕ) : K) * nosZ W P by ring]
        exact (v.map_add _ _).trans (max_le htotal.le hcoeff)
      rw [succ_nsmul, add_comm]
      exact ⟨haddnear, htotal, hnextle⟩

private lemma nos_no_torsion {K : Type*} [Field K] [DecidableEq K]
    (W : WeierstrassCurve K) [W.IsElliptic] (A : ValuationSubring K)
    (ha₁ : W.a₁ ∈ A) (ha₂ : W.a₂ ∈ A) (ha₃ : W.a₃ ∈ A)
    (ha₄ : W.a₄ ∈ A) (ha₆ : W.a₆ ∈ A) (n : ℕ)
    (hn : ∃ u : A, (u : K) = (n : K) ∧ IsUnit u)
    {P : WeierstrassCurve.Affine.Point W} (hP : nosNear W A P)
    (htors : n • P = 0) : P = 0 := by
  let v := A.valuation
  obtain ⟨u, hu, huunit⟩ := hn
  have hnval : v (n : K) = 1 := by
    rw [← hu]
    exact (A.valuation_eq_one_iff u).mp huunit
  cases P with
  | zero => rfl
  | some x y hp =>
      have hPnear : nosNear W A (.some x y hp) := hP
      change x ∉ A at hP
      have h := hp.1
      obtain ⟨hy, _, _⟩ :=
        nos_local_coordinate_valuations W A ha₁ ha₂ ha₃ ha₄ ha₆ hP h
      let z : K := -x / y
      let s : A.ValueGroup := v z
      have hz0 : z ≠ 0 := by
        apply div_ne_zero
        · exact neg_ne_zero.mpr fun hx ↦ hP (hx ▸ A.zero_mem)
        · exact hy
      have hs0 : 0 < s := by
        change 0 < v z
        exact (v.ne_zero_iff.mpr hz0).bot_lt
      have hzP : v (nosZ W (.some x y hp)) = s := rfl
      obtain ⟨_, herr, _⟩ :=
        nos_nsmul_parameter W A ha₁ ha₂ ha₃ ha₄ ha₆ hPnear hs0 hzP n
      rw [htors] at herr
      change v (0 - (n : K) * z) < s at herr
      rw [zero_sub, v.map_neg, v.map_mul, hnval, one_mul] at herr
      exact (lt_irrefl s herr).elim

private def nosIntegralCurve {K : Type*} [Field K] (W : WeierstrassCurve K)
    (A : ValuationSubring K) (ha₁ : W.a₁ ∈ A) (ha₂ : W.a₂ ∈ A)
    (ha₃ : W.a₃ ∈ A) (ha₄ : W.a₄ ∈ A) (ha₆ : W.a₆ ∈ A) : WeierstrassCurve A :=
  ⟨⟨W.a₁, ha₁⟩, ⟨W.a₂, ha₂⟩, ⟨W.a₃, ha₃⟩, ⟨W.a₄, ha₄⟩, ⟨W.a₆, ha₆⟩⟩

private lemma nos_integral_curve_map {K : Type*} [Field K] (W : WeierstrassCurve K)
    (A : ValuationSubring K) (ha₁ : W.a₁ ∈ A) (ha₂ : W.a₂ ∈ A)
    (ha₃ : W.a₃ ∈ A) (ha₄ : W.a₄ ∈ A) (ha₆ : W.a₆ ∈ A) :
    (nosIntegralCurve W A ha₁ ha₂ ha₃ ha₄ ha₆).map A.subtype = W := by
  ext <;> rfl

private lemma nos_partial_unit {K : Type*} [Field K] (W : WeierstrassCurve K)
    (A : ValuationSubring K) (ha₁ : W.a₁ ∈ A) (ha₂ : W.a₂ ∈ A)
    (ha₃ : W.a₃ ∈ A) (ha₄ : W.a₄ ∈ A) (ha₆ : W.a₆ ∈ A)
    (hΔ : ∃ d : A, (d : K) = W.Δ ∧ IsUnit d) {x y : K}
    (hx : x ∈ A) (hy : y ∈ A) (h : WeierstrassCurve.Affine.Equation W x y) :
    (∃ t : A, (t : K) = W.a₁ * y - (3 * x ^ 2 + 2 * W.a₂ * x + W.a₄) ∧ IsUnit t) ∨
      ∃ t : A, (t : K) = 2 * y + W.a₁ * x + W.a₃ ∧ IsUnit t := by
  let WA := nosIntegralCurve W A ha₁ ha₂ ha₃ ha₄ ha₆
  let xA : A := ⟨x, hx⟩
  let yA : A := ⟨y, hy⟩
  let fX : A := WA.a₁ * yA - (3 * xA ^ 2 + 2 * WA.a₂ * xA + WA.a₄)
  let fY : A := 2 * yA + WA.a₁ * xA + WA.a₃
  have hmap : WA.map A.subtype = W :=
    nos_integral_curve_map W A ha₁ ha₂ ha₃ ha₄ ha₆
  have heqA : WeierstrassCurve.Affine.Equation WA xA yA := by
    rw [WeierstrassCurve.Affine.equation_iff] at h ⊢
    apply Subtype.ext
    exact h
  have hΔcoe : ((WA.Δ : A) : K) = W.Δ := by
    calc
      ((WA.Δ : A) : K) = (WA.map A.subtype).Δ := (WA.map_Δ A.subtype).symm
      _ = W.Δ := congrArg WeierstrassCurve.Δ hmap
  obtain ⟨d, hd, hdunit⟩ := hΔ
  have hdWA : d = WA.Δ := Subtype.ext (hd.trans hΔcoe.symm)
  have hWAunit : IsUnit WA.Δ := by
    rw [← hdWA]
    exact hdunit
  let Wred := WA.map (IsLocalRing.residue A)
  have hredΔ : Wred.Δ ≠ 0 := by
    change (WA.map (IsLocalRing.residue A)).Δ ≠ 0
    rw [WA.map_Δ]
    exact (hWAunit.map (IsLocalRing.residue A)).ne_zero
  have heqred : WeierstrassCurve.Affine.Equation Wred
      (IsLocalRing.residue A xA) (IsLocalRing.residue A yA) :=
    heqA.map (IsLocalRing.residue A)
  have hns := (WeierstrassCurve.Affine.equation_iff_nonsingular_of_Δ_ne_zero
    (W := Wred) hredΔ).mp heqred
  rcases ((WeierstrassCurve.Affine.nonsingular_iff' (W := Wred) _ _).mp hns).2 with hX | hY
  · left
    refine ⟨fX, ?_, (IsLocalRing.residue_ne_zero_iff_isUnit fX).mp ?_⟩
    · rfl
    · simpa only [fX, Wred, WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂,
        WeierstrassCurve.map_a₄, map_sub, map_add, map_mul, map_pow, map_ofNat] using hX
  · right
    refine ⟨fY, ?_, (IsLocalRing.residue_ne_zero_iff_isUnit fY).mp ?_⟩
    · rfl
    · simpa only [fY, Wred, WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₃,
        map_add, map_mul, map_ofNat] using hY

private lemma nos_secant_alternative {K : Type*} [Field K] (W : WeierstrassCurve K)
    {x₁ y₁ x₂ y₂ : K} (h₁ : WeierstrassCurve.Affine.Equation W x₁ y₁)
    (h₂ : WeierstrassCurve.Affine.Equation W x₂ y₂) :
    (y₂ - y₁) * (-(y₂ + y₁ + W.a₁ * x₂ + W.a₃)) =
      (x₂ - x₁) * (W.a₁ * y₁ -
        (x₂ ^ 2 + x₂ * x₁ + x₁ ^ 2 + W.a₂ * (x₂ + x₁) + W.a₄)) := by
  rw [WeierstrassCurve.Affine.equation_iff (W := W) x₁ y₁] at h₁
  rw [WeierstrassCurve.Affine.equation_iff (W := W) x₂ y₂] at h₂
  linear_combination h₁ - h₂

private lemma nos_addX_nonintegral {K : Type*} [Field K] (W : WeierstrassCurve K)
    (A : ValuationSubring K) {x₁ x₂ l : K}
    (ha₁ : W.a₁ ∈ A) (ha₂ : W.a₂ ∈ A) (hx₁ : x₁ ∈ A) (hx₂ : x₂ ∈ A)
    (hl : 1 < A.valuation l) : WeierstrassCurve.Affine.addX W x₁ x₂ l ∉ A := by
  let v := A.valuation
  have ha₁v : v W.a₁ ≤ 1 := (A.valuation_le_one_iff W.a₁).mpr ha₁
  have ha₂v : v W.a₂ ≤ 1 := (A.valuation_le_one_iff W.a₂).mpr ha₂
  have hx₁v : v x₁ ≤ 1 := (A.valuation_le_one_iff x₁).mpr hx₁
  have hx₂v : v x₂ ≤ 1 := (A.valuation_le_one_iff x₂).mpr hx₂
  have hl0 : 0 < v l := zero_lt_one.trans hl
  have hll : v l < (v l) ^ 2 := by
    rw [pow_two]
    exact lt_mul_of_one_lt_right hl0 hl
  have ha₁l : v (W.a₁ * l) < (v l) ^ 2 := by
    rw [v.map_mul]
    exact (mul_le_mul_of_nonneg_right ha₁v zero_le).trans_lt (by simpa using hll)
  have hone : (1 : A.ValueGroup) < (v l) ^ 2 := by
    exact hl.trans hll
  have hrest : v (W.a₁ * l - W.a₂ - x₁ - x₂) < (v l) ^ 2 :=
    v.map_sub_lt (v.map_sub_lt (v.map_sub_lt ha₁l (ha₂v.trans_lt hone))
      (hx₁v.trans_lt hone)) (hx₂v.trans_lt hone)
  have hval : v (WeierstrassCurve.Affine.addX W x₁ x₂ l) = (v l) ^ 2 := by
    change v (l ^ 2 + W.a₁ * l - W.a₂ - x₁ - x₂) = (v l) ^ 2
    rw [show l ^ 2 + W.a₁ * l - W.a₂ - x₁ - x₂ =
      l ^ 2 + (W.a₁ * l - W.a₂ - x₁ - x₂) by ring]
    rw [v.map_add_eq_of_lt_left]
    · rw [v.map_pow]
    · rwa [v.map_pow]
  rw [← A.valuation_le_one_iff]
  rw [hval]
  exact (not_le_of_gt hone)

private lemma nos_secant_slope {K : Type*} [Field K] [DecidableEq K]
    (W : WeierstrassCurve K) (A : ValuationSubring K)
    (ha₁ : W.a₁ ∈ A) (ha₂ : W.a₂ ∈ A) (ha₃ : W.a₃ ∈ A)
    (ha₄ : W.a₄ ∈ A) (ha₆ : W.a₆ ∈ A)
    (hΔ : ∃ d : A, (d : K) = W.Δ ∧ IsUnit d)
    {x₁ y₁ x₂ y₂ : K} (h₁ : WeierstrassCurve.Affine.Equation W x₁ y₁)
    (h₂ : WeierstrassCurve.Affine.Equation W x₂ y₂)
    (hx₁ : x₁ ∈ A) (hy₁ : y₁ ∈ A) (hx₂ : x₂ ∈ A)
    (hx : x₁ ≠ x₂) (hxc : A.valuation (x₂ - x₁) < 1)
    (hyc : A.valuation (y₂ - y₁) < 1) :
    1 < A.valuation
      (WeierstrassCurve.Affine.slope W x₁ x₂ y₁
        (WeierstrassCurve.Affine.negY W x₂ y₂)) := by
  let v := A.valuation
  let N := -(y₂ + y₁ + W.a₁ * x₂ + W.a₃)
  let M := W.a₁ * y₁ -
    (x₂ ^ 2 + x₂ * x₁ + x₁ ^ 2 + W.a₂ * (x₂ + x₁) + W.a₄)
  let fX := W.a₁ * y₁ - (3 * x₁ ^ 2 + 2 * W.a₂ * x₁ + W.a₄)
  let fY := 2 * y₁ + W.a₁ * x₁ + W.a₃
  have ha₁v : v W.a₁ ≤ 1 := (A.valuation_le_one_iff W.a₁).mpr ha₁
  have hdx0 : x₂ - x₁ ≠ 0 := sub_ne_zero.mpr hx.symm
  have hslope : WeierstrassCurve.Affine.slope W x₁ x₂ y₁
      (WeierstrassCurve.Affine.negY W x₂ y₂) = N / (x₂ - x₁) := by
    rw [WeierstrassCurve.Affine.slope_of_X_ne hx]
    simp only [N, WeierstrassCurve.Affine.negY]
    field_simp [hdx0, sub_ne_zero.mpr hx]
    ring
  rcases nos_partial_unit W A ha₁ ha₂ ha₃ ha₄ ha₆ hΔ hx₁ hy₁ h₁ with hXu | hYu
  · obtain ⟨t, ht, htunit⟩ := hXu
    have hfX : v fX = 1 := by
      change v (W.a₁ * y₁ - (3 * x₁ ^ 2 + 2 * W.a₂ * x₁ + W.a₄)) = 1
      rw [← ht]
      exact (A.valuation_eq_one_iff t).mp htunit
    have hfactor : x₂ + 2 * x₁ + W.a₂ ∈ A :=
      A.toSubring.add_mem
        (A.toSubring.add_mem hx₂ (A.toSubring.mul_mem (natCast_mem A 2) hx₁)) ha₂
    have hfactorv : v (x₂ + 2 * x₁ + W.a₂) ≤ 1 :=
      (A.valuation_le_one_iff _).mpr hfactor
    have hMerr : v (M - fX) < 1 := by
      rw [show M - fX = -(x₂ - x₁) * (x₂ + 2 * x₁ + W.a₂) by
        simp only [M, fX]
        ring,
        v.map_mul, v.map_neg]
      exact mul_lt_one_of_lt_of_le hxc hfactorv
    have hM : v M = 1 := by
      calc
        v M = v fX := v.map_eq_of_sub_lt (by rwa [hfX])
        _ = 1 := hfX
    have hM0 : M ≠ 0 := by
      apply v.ne_zero_iff.mp
      rw [hM]
      exact one_ne_zero
    have halt := nos_secant_alternative W h₁ h₂
    change (y₂ - y₁) * N = (x₂ - x₁) * M at halt
    have hdy0 : y₂ - y₁ ≠ 0 := by
      intro hdy
      rw [hdy, zero_mul] at halt
      exact (mul_ne_zero hdx0 hM0) halt.symm
    have hratio : N / (x₂ - x₁) = M / (y₂ - y₁) := by
      apply (div_eq_div_iff hdx0 hdy0).mpr
      rw [mul_comm N, halt, mul_comm]
    rw [hslope, hratio, v.map_div, hM]
    exact (one_lt_div₀ (v.pos_iff.mpr hdy0)).mpr hyc
  · obtain ⟨t, ht, htunit⟩ := hYu
    have hfY : v fY = 1 := by
      change v (2 * y₁ + W.a₁ * x₁ + W.a₃) = 1
      rw [← ht]
      exact (A.valuation_eq_one_iff t).mp htunit
    have ha₁dx : v (W.a₁ * (x₂ - x₁)) < 1 := by
      rw [v.map_mul]
      exact mul_lt_of_le_one_of_lt ha₁v hxc
    have hNerr : v (N - (-fY)) < 1 := by
      rw [show N - (-fY) = -(y₂ - y₁) - W.a₁ * (x₂ - x₁) by
        simp only [N, fY]
        ring]
      exact v.map_sub_lt ((v.map_neg _).trans_lt hyc) ha₁dx
    have hN : v N = 1 := by
      calc
        v N = v (-fY) := v.map_eq_of_sub_lt (by
          rw [v.map_neg, hfY]
          exact hNerr)
        _ = 1 := by rw [v.map_neg, hfY]
    rw [hslope, v.map_div, hN]
    exact (one_lt_div₀ (v.pos_iff.mpr hdx0)).mpr hxc

private lemma nos_tangent_slope {K : Type*} [Field K] [DecidableEq K]
    (W : WeierstrassCurve K) (A : ValuationSubring K)
    (ha₁ : W.a₁ ∈ A) (ha₂ : W.a₂ ∈ A) (ha₃ : W.a₃ ∈ A)
    (ha₄ : W.a₄ ∈ A) (ha₆ : W.a₆ ∈ A)
    (hΔ : ∃ d : A, (d : K) = W.Δ ∧ IsUnit d)
    {x y₁ y₂ : K} (h₁ : WeierstrassCurve.Affine.Equation W x y₁)
    (h₂ : WeierstrassCurve.Affine.Equation W x y₂)
    (hx : x ∈ A) (hy₁ : y₁ ∈ A) (hyne : y₁ ≠ y₂)
    (hyc : A.valuation (y₂ - y₁) < 1) :
    1 < A.valuation (WeierstrassCurve.Affine.slope W x x y₁ y₁) := by
  let v := A.valuation
  let fX := W.a₁ * y₁ - (3 * x ^ 2 + 2 * W.a₂ * x + W.a₄)
  let fY := 2 * y₁ + W.a₁ * x + W.a₃
  have hrel : y₁ = WeierstrassCurve.Affine.negY W x y₂ := by
    by_contra hrel
    exact hyne (WeierstrassCurve.Affine.Y_eq_of_Y_ne h₁ h₂ rfl hrel)
  have hrel' : WeierstrassCurve.Affine.negY W x y₁ = y₂ := by
    rw [hrel, WeierstrassCurve.Affine.negY_negY]
  have hyself : y₁ ≠ WeierstrassCurve.Affine.negY W x y₁ := by
    rwa [hrel']
  have hdeneq : fY = y₁ - WeierstrassCurve.Affine.negY W x y₁ := by
    simp only [fY, WeierstrassCurve.Affine.negY]
    ring
  have hden : v fY < 1 := by
    rw [hdeneq, hrel', v.map_sub_swap]
    exact hyc
  have hden0 : fY ≠ 0 := by
    rw [hdeneq, hrel']
    exact sub_ne_zero.mpr hyne
  rcases nos_partial_unit W A ha₁ ha₂ ha₃ ha₄ ha₆ hΔ hx hy₁ h₁ with hXu | hYu
  · obtain ⟨t, ht, htunit⟩ := hXu
    have hfX : v fX = 1 := by
      change v (W.a₁ * y₁ - (3 * x ^ 2 + 2 * W.a₂ * x + W.a₄)) = 1
      rw [← ht]
      exact (A.valuation_eq_one_iff t).mp htunit
    rw [WeierstrassCurve.Affine.slope_of_Y_ne_eq_evalEval rfl hyself,
      WeierstrassCurve.Affine.evalEval_polynomialX,
      WeierstrassCurve.Affine.evalEval_polynomialY]
    change 1 < v (-fX / fY)
    rw [v.map_div, v.map_neg, hfX]
    exact (one_lt_div₀ (v.pos_iff.mpr hden0)).mpr hden
  · obtain ⟨t, ht, htunit⟩ := hYu
    have hfY : v fY = 1 := by
      change v (2 * y₁ + W.a₁ * x + W.a₃) = 1
      rw [← ht]
      exact (A.valuation_eq_one_iff t).mp htunit
    rw [hfY] at hden
    exact (lt_irrefl 1 hden).elim

private lemma nos_congruent_sub_near {K : Type*} [Field K] [DecidableEq K]
    (W : WeierstrassCurve K) [W.IsElliptic] (A : ValuationSubring K)
    (ha₁ : W.a₁ ∈ A) (ha₂ : W.a₂ ∈ A) (ha₃ : W.a₃ ∈ A)
    (ha₄ : W.a₄ ∈ A) (ha₆ : W.a₆ ∈ A)
    (hΔ : ∃ d : A, (d : K) = W.Δ ∧ IsUnit d)
    {x₁ y₁ x₂ y₂ : K} {hp₁ : WeierstrassCurve.Affine.Nonsingular W x₁ y₁}
    {hp₂ : WeierstrassCurve.Affine.Nonsingular W x₂ y₂}
    (hx₁ : x₁ ∈ A) (hy₁ : y₁ ∈ A) (hx₂ : x₂ ∈ A) (hy₂ : y₂ ∈ A)
    (hxc : A.valuation (x₂ - x₁) < 1) (hyc : A.valuation (y₂ - y₁) < 1) :
    nosNear W A
      (WeierstrassCurve.Affine.Point.some x₁ y₁ hp₁ -
        WeierstrassCurve.Affine.Point.some x₂ y₂ hp₂) := by
  by_cases hsame : x₁ = x₂ ∧ y₁ = y₂
  · obtain ⟨rfl, rfl⟩ := hsame
    simp only [sub_self]
    trivial
  by_cases hx : x₁ = x₂
  · subst x₂
    have hyne : y₁ ≠ y₂ := fun hy ↦ hsame ⟨rfl, hy⟩
    have hrel : y₁ = WeierstrassCurve.Affine.negY W x₁ y₂ := by
      by_contra hrel
      exact hyne (WeierstrassCurve.Affine.Y_eq_of_Y_ne hp₁.1 hp₂.1 rfl hrel)
    have hrel' : WeierstrassCurve.Affine.negY W x₁ y₁ = y₂ := by
      rw [hrel, WeierstrassCurve.Affine.negY_negY]
    have hyself : y₁ ≠ WeierstrassCurve.Affine.negY W x₁ y₁ := by
      rwa [hrel']
    have hneg : -WeierstrassCurve.Affine.Point.some x₁ y₂ hp₂ =
        WeierstrassCurve.Affine.Point.some x₁ y₁ hp₁ := by
      rw [WeierstrassCurve.Affine.Point.neg_some]
      simp only [WeierstrassCurve.Affine.Point.some.injEq, true_and]
      exact hrel.symm
    rw [sub_eq_add_neg, hneg,
      WeierstrassCurve.Affine.Point.add_self_of_Y_ne hyself]
    change WeierstrassCurve.Affine.addX W x₁ x₁
      (WeierstrassCurve.Affine.slope W x₁ x₁ y₁ y₁) ∉ A
    apply nos_addX_nonintegral W A ha₁ ha₂ hx₁ hx₁
    exact nos_tangent_slope W A ha₁ ha₂ ha₃ ha₄ ha₆ hΔ hp₁.1 hp₂.1
      hx₁ hy₁ hyne hyc
  · rw [sub_eq_add_neg, WeierstrassCurve.Affine.Point.neg_some,
      WeierstrassCurve.Affine.Point.add_of_X_ne hx]
    change WeierstrassCurve.Affine.addX W x₁ x₂
      (WeierstrassCurve.Affine.slope W x₁ x₂ y₁
        (WeierstrassCurve.Affine.negY W x₂ y₂)) ∉ A
    apply nos_addX_nonintegral W A ha₁ ha₂ hx₁ hx₂
    exact nos_secant_slope W A ha₁ ha₂ ha₃ ha₄ ha₆ hΔ hp₁.1 hp₂.1
      hx₁ hy₁ hx₂ hx hxc hyc

private lemma nos_inertia_congruent {k K : Type*} [Field k] [Field K] [Algebra k K]
    (A : ValuationSubring K) {σ : A.decompositionSubgroup k}
    (hσ : σ ∈ A.inertiaSubgroup k) {a : K} (ha : a ∈ A) :
    (σ : K ≃ₐ[k] K) a ∈ A ∧ A.valuation ((σ : K ≃ₐ[k] K) a - a) < 1 := by
  let aA : A := ⟨a, ha⟩
  let bA : A := σ • aA
  have hb : (bA : K) = (σ : K ≃ₐ[k] K) a := rfl
  have htriv : ∀ z : IsLocalRing.ResidueField A, σ • z = z := by
    intro z
    change MulSemiringAction.toRingAut (A.decompositionSubgroup k)
      (IsLocalRing.ResidueField A) σ = 1 at hσ
    have hz := DFunLike.congr_fun hσ z
    change σ • z = (1 : RingAut (IsLocalRing.ResidueField A)) z at hz
    simpa only [RingAut.one_apply] using hz
  have hres : IsLocalRing.residue A bA = IsLocalRing.residue A aA := by
    rw [show bA = σ • aA from rfl, IsLocalRing.ResidueField.residue_smul, htriv]
  have hmax : bA - aA ∈ IsLocalRing.maximalIdeal A := by
    rw [← IsLocalRing.residue_eq_zero_iff]
    simp only [map_sub, hres, sub_self]
  constructor
  · rw [← hb]
    exact bA.2
  · rw [← hb]
    exact A.mem_nonunits_iff.mp (A.coe_mem_nonunits_iff.mpr hmax)

/-- **Néron–Ogg–Shafarevich criterion, easy direction.** Let $R$ be a discrete valuation ring
with fraction field $k$, and let $E$ be an elliptic curve over $k$ given by a Weierstrass
equation with good reduction at $R$. Let $n$ be a natural number whose image in the residue
field of $R$ is nonzero, let $k^{\mathrm{sep}}$ be a separable closure of $k$, and let
$\mathcal{O}$ be a valuation subring of $k^{\mathrm{sep}}$ whose intersection with $k$ is $R$.
Then every element $\sigma$ of the inertia subgroup of $\mathcal{O}$ in
$\mathrm{Gal}(k^{\mathrm{sep}}/k)$ fixes every point $P \in E(k^{\mathrm{sep}})$ with $nP = 0$.

Proves `Wanted` entry `good_reduction_torsion_unramified`.

Proof: We use Silverman's elementary valuation filtration at the origin in $(z, w)$ coordinates,
together with reduction to the nonsingular residue curve; see *The Arithmetic of Elliptic Curves*,
IV.1, VII.3, and VII.7.

Source: J. H. Silverman, *The Arithmetic of Elliptic Curves*, 2nd ed.,
GTM 106, Springer, Theorem VII.7.1.
-/
theorem good_reduction_torsion_unramified (R : Type*)
    [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (k : Type*) [Field k] [Algebra R k] [IsFractionRing R k]
    (E : WeierstrassCurve k) [E.IsElliptic] [E.HasGoodReduction R]
    (n : ℕ) [NeZero (n : IsLocalRing.ResidueField R)]
    (ksep : Type*) [Field ksep] [Algebra k ksep]
    [IsSepClosure k ksep] [DecidableEq ksep]
    (𝒪 : ValuationSubring ksep)
    (h𝒪 : (𝒪.comap (algebraMap k ksep)).toSubring = (algebraMap R k).range) :
    ∀ σ ∈ 𝒪.inertiaSubgroup k, ∀ P : (E⁄ksep).Point, (n : ℤ) • P = 0 →
      WeierstrassCurve.Affine.Point.map (σ : ksep ≃ₐ[k] ksep).toAlgHom P = P := by
  intro σ hσ P htors
  let W : WeierstrassCurve ksep := E⁄ksep
  let _ : W.IsElliptic :=
    ⟨by
      simpa only [W, WeierstrassCurve.Affine.baseChange, WeierstrassCurve.baseChange,
        WeierstrassCurve.map_Δ] using E.isUnit_Δ.map (algebraMap k ksep)⟩
  have hcoeff : W.a₁ ∈ 𝒪 ∧ W.a₂ ∈ 𝒪 ∧ W.a₃ ∈ 𝒪 ∧ W.a₄ ∈ 𝒪 ∧
      W.a₆ ∈ 𝒪 ∧ W.Δ ∈ 𝒪 := by
    simpa only [W, WeierstrassCurve.Affine.baseChange, WeierstrassCurve.baseChange,
      WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₃,
      WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₆, WeierstrassCurve.map_Δ] using
      nos_coefficients_mem E 𝒪 h𝒪
  obtain ⟨ha₁, ha₂, ha₃, ha₄, ha₆, _⟩ := hcoeff
  have hΔ : ∃ d : 𝒪, (d : ksep) = W.Δ ∧ IsUnit d := by
    simpa only [W, WeierstrassCurve.Affine.baseChange, WeierstrassCurve.baseChange,
      WeierstrassCurve.map_Δ] using nos_discriminant_unit E 𝒪 h𝒪
  have hn := nos_nat_unit n 𝒪 h𝒪
  have hnP : n • P = 0 := by
    simpa only [Int.ofNat_eq_natCast, natCast_zsmul] using htors
  cases P with
  | zero => rfl
  | some x y hp =>
      by_cases hx : x ∈ 𝒪
      · have hy := nos_y_mem_of_x_mem W 𝒪 ha₁ ha₂ ha₃ ha₄ ha₆ hx hp.1
        obtain ⟨hσx, hxc'⟩ := nos_inertia_congruent 𝒪 hσ hx
        obtain ⟨hσy, hyc'⟩ := nos_inertia_congruent 𝒪 hσ hy
        let f := (σ : ksep ≃ₐ[k] ksep).toAlgHom
        let Q := WeierstrassCurve.Affine.Point.map f
          (WeierstrassCurve.Affine.Point.some x y hp)
        have hxc : 𝒪.valuation (x - f x) < 1 :=
          (𝒪.valuation.map_sub_swap x (f x)).trans_lt hxc'
        have hyc : 𝒪.valuation (y - f y) < 1 :=
          (𝒪.valuation.map_sub_swap y (f y)).trans_lt hyc'
        have hnear : nosNear W 𝒪
            (Q - WeierstrassCurve.Affine.Point.some x y hp) := by
          change nosNear W 𝒪
            (WeierstrassCurve.Affine.Point.map f
              (WeierstrassCurve.Affine.Point.some x y hp) -
              WeierstrassCurve.Affine.Point.some x y hp)
          rw [WeierstrassCurve.Affine.Point.map_some]
          exact nos_congruent_sub_near W 𝒪 ha₁ ha₂ ha₃ ha₄ ha₆ hΔ
            hσx hσy hx hy hxc hyc
        have hnQ : n • Q = 0 := by
          change n • WeierstrassCurve.Affine.Point.map f
            (WeierstrassCurve.Affine.Point.some x y hp) = 0
          rw [← map_nsmul, hnP, map_zero]
        have hnD : n • (Q - WeierstrassCurve.Affine.Point.some x y hp) = 0 := by
          rw [nsmul_sub, hnQ, hnP, sub_self]
        have hD := nos_no_torsion W 𝒪 ha₁ ha₂ ha₃ ha₄ ha₆ n hn hnear hnD
        exact sub_eq_zero.mp hD
      · have hnear : nosNear W 𝒪 (WeierstrassCurve.Affine.Point.some x y hp) := hx
        have hP := nos_no_torsion W 𝒪 ha₁ ha₂ ha₃ ha₄ ha₆ n hn hnear hnP
        rw [hP, WeierstrassCurve.Affine.Point.map_zero]

end

end MetaMathlibExt

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_MvPowerSeries_exists_apply_eq_mul_pow_mul_add_of_mem_span_X_pow_of_
apply_X_eq_mul.lean`
and
`P2M/Sol/S_MvPowerSeries_exists_apply_eq_mul_pow_mul_add_of_mem_span_X_pow_of_
apply_X_eq_mul.lean`
(https://github.com/anthropics/fermats-last-theorem):
Compared with the source files at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`.
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits:
Mathlib — https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.
-/

module

public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
public import Mathlib.RingTheory.MvPowerSeries.Basic

@[expose] public section

open IsLocalRing MvPowerSeries

universe u v

/-- The degree-`d` initial form of a two-variable power series, evaluated at
`(p₀, p₁)`: the finite sum of its total-degree-`d` coefficients weighted by
powers of `p₀` and `p₁`. -/
public noncomputable def MvPowerSeries.initialForm {W : Type u} [CommRing W] (d : ℕ)
    (g : MvPowerSeries (Fin 2) W) (p₀ p₁ : W) : W :=
  ∑ i ∈ Finset.range (d + 1),
    MvPowerSeries.coeff (Finsupp.single (0 : Fin 2) i +
      Finsupp.single (1 : Fin 2) (d - i)) g * p₀ ^ i * p₁ ^ (d - i)

/-- Characterization of `initialForm` as the displayed finite sum. -/
public theorem MvPowerSeries.initialForm_eq_sum {W : Type u} [CommRing W]
    (d : ℕ) (g : MvPowerSeries (Fin 2) W) (p₀ p₁ : W) :
    MvPowerSeries.initialForm d g p₀ p₁ =
      ∑ i ∈ Finset.range (d + 1),
        MvPowerSeries.coeff (Finsupp.single (0 : Fin 2) i +
          Finsupp.single (1 : Fin 2) (d - i)) g * p₀ ^ i * p₁ ^ (d - i) :=
  rfl

/-- `initialForm` is additive in the power series. -/
public theorem MvPowerSeries.initialForm_add {W : Type u} [CommRing W]
    (d : ℕ) (g g' : MvPowerSeries (Fin 2) W) (p₀ p₁ : W) :
    MvPowerSeries.initialForm d (g + g') p₀ p₁ =
      MvPowerSeries.initialForm d g p₀ p₁ +
        MvPowerSeries.initialForm d g' p₀ p₁ := by
  simp only [MvPowerSeries.initialForm, map_add, add_mul, Finset.sum_add_distrib]

/-- The degree-zero initial form is the constant coefficient. -/
public theorem MvPowerSeries.initialForm_zero {W : Type u} [CommRing W]
    (g : MvPowerSeries (Fin 2) W) (p₀ p₁ : W) :
    MvPowerSeries.initialForm 0 g p₀ p₁ = MvPowerSeries.coeff 0 g := by
  simp [MvPowerSeries.initialForm]

private theorem coeff_X_mul' {W : Type u} [CommRing W] (s : Fin 2)
    (f : MvPowerSeries (Fin 2) W) (m : Fin 2 →₀ ℕ) :
    MvPowerSeries.coeff m (MvPowerSeries.X s * f) =
      if 1 ≤ m s then MvPowerSeries.coeff (m - Finsupp.single s 1) f else 0 := by
  rw [MvPowerSeries.X_def, MvPowerSeries.coeff_monomial_mul]
  simp only [Finsupp.single_le_iff, one_mul]

private theorem initialForm_X_zero_mul {W : Type u} [CommRing W] (d : ℕ)
    (b : MvPowerSeries (Fin 2) W) (p₀ p₁ : W) :
    MvPowerSeries.initialForm (d + 1) (MvPowerSeries.X 0 * b) p₀ p₁ =
      p₀ * MvPowerSeries.initialForm d b p₀ p₁ := by
  simp only [MvPowerSeries.initialForm]
  rw [Finset.sum_range_succ', Finset.mul_sum]
  have h0 : MvPowerSeries.coeff (Finsupp.single (0 : Fin 2) 0 +
      Finsupp.single (1 : Fin 2) (d + 1 - 0)) (MvPowerSeries.X 0 * b) = 0 := by
    rw [coeff_X_mul', ite_eq_right (by simp)]
  rw [h0, zero_mul, zero_mul, add_zero]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [coeff_X_mul', ite_eq_left (by simp)]
  have hsub : Finsupp.single (0 : Fin 2) (i + 1) +
        Finsupp.single (1 : Fin 2) (d + 1 - (i + 1)) - Finsupp.single 0 1 =
      Finsupp.single (0 : Fin 2) i + Finsupp.single (1 : Fin 2) (d - i) := by
    ext s; fin_cases s <;> simp
  rw [hsub, show d + 1 - (i + 1) = d - i from by omega]; ring

private theorem initialForm_X_one_mul {W : Type u} [CommRing W] (d : ℕ)
    (b : MvPowerSeries (Fin 2) W) (p₀ p₁ : W) :
    MvPowerSeries.initialForm (d + 1) (MvPowerSeries.X 1 * b) p₀ p₁ =
      p₁ * MvPowerSeries.initialForm d b p₀ p₁ := by
  simp only [MvPowerSeries.initialForm]
  rw [Finset.sum_range_succ, Finset.mul_sum]
  have hlast : MvPowerSeries.coeff (Finsupp.single (0 : Fin 2) (d + 1) +
      Finsupp.single (1 : Fin 2) (d + 1 - (d + 1))) (MvPowerSeries.X 1 * b) = 0 := by
    rw [coeff_X_mul', ite_eq_right (by simp)]
  rw [hlast, zero_mul, zero_mul, add_zero]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hid : i ≤ d := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  rw [coeff_X_mul', ite_eq_left (by simp; omega)]
  have hsub : Finsupp.single (0 : Fin 2) i +
        Finsupp.single (1 : Fin 2) (d + 1 - i) - Finsupp.single 1 1 =
      Finsupp.single (0 : Fin 2) i + Finsupp.single (1 : Fin 2) (d - i) := by
    ext s; fin_cases s <;> simp <;> omega
  rw [hsub, show d + 1 - i = (d - i) + 1 by omega, pow_succ]; ring

private theorem mem_span_X_of_coeff_zero {W : Type u} [CommRing W]
    (f : MvPowerSeries (Fin 2) W) (hf : MvPowerSeries.coeff 0 f = 0) :
    f ∈ Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W),
      MvPowerSeries.X 1} := by
  classical
  let f₀ : MvPowerSeries (Fin 2) W :=
    fun n => MvPowerSeries.coeff (n + Finsupp.single 0 1) f
  let f₁ : MvPowerSeries (Fin 2) W :=
    fun n => if n 0 = 0 then MvPowerSeries.coeff (n + Finsupp.single 1 1) f else 0
  have hdec : f = MvPowerSeries.X 0 * f₀ + MvPowerSeries.X 1 * f₁ := by
    ext m
    rw [map_add, coeff_X_mul', coeff_X_mul']
    by_cases h0 : 1 ≤ m 0
    · rw [ite_eq_left h0]
      have heq : MvPowerSeries.coeff (m - Finsupp.single 0 1) f₀ =
          MvPowerSeries.coeff m f := by
        show MvPowerSeries.coeff (m - Finsupp.single 0 1 + Finsupp.single 0 1) f =
          MvPowerSeries.coeff m f
        rw [tsub_add_cancel_of_le (Finsupp.single_le_iff.mpr h0)]
      rw [heq]
      by_cases h1 : 1 ≤ m 1
      · rw [ite_eq_left h1]
        have hz : MvPowerSeries.coeff (m - Finsupp.single 1 1) f₁ = 0 := by
          show (if ((m - Finsupp.single (1 : Fin 2) 1 : Fin 2 →₀ ℕ) 0) = 0
            then MvPowerSeries.coeff (m - Finsupp.single 1 1 + Finsupp.single 1 1) f
            else 0) = 0
          rw [ite_eq_right]; simp; omega
        rw [hz, add_zero]
      · rw [ite_eq_right h1, add_zero]
    · rw [ite_eq_right h0, zero_add]
      push Not at h0
      have hm0 : m 0 = 0 := by omega
      by_cases h1 : 1 ≤ m 1
      · rw [ite_eq_left h1]
        show MvPowerSeries.coeff m f =
          if ((m - Finsupp.single (1 : Fin 2) 1 : Fin 2 →₀ ℕ) 0) = 0
            then MvPowerSeries.coeff (m - Finsupp.single 1 1 + Finsupp.single 1 1) f
            else 0
        rw [ite_eq_left (by simp [hm0]),
          tsub_add_cancel_of_le (Finsupp.single_le_iff.mpr h1)]
      · rw [ite_eq_right h1]
        have hm : m = 0 := by ext s; fin_cases s <;> simp <;> omega
        rw [hm]; exact hf
  rw [hdec]
  exact Ideal.add_mem _ (Ideal.mul_mem_right _ _
      (Ideal.subset_span (by simp)))
    (Ideal.mul_mem_right _ _ (Ideal.subset_span (by simp)))

/-- Local-ring evaluation of a two-variable initial form: if `g` lies in the
`d`-th power of the ideal generated by the two variables, then its image
under `Φ` is `v ^ d` times the image of its degree-`d` initial form,
up to an error term in the maximal ideal. -/
public theorem
    MvPowerSeries.exists_apply_eq_mul_pow_mul_add_of_mem_span_X_pow_of_apply_X_eq_mul
    (W : Type u) [CommRing W] (M : Type v) [CommRing M] [IsLocalRing M]
    (Φ : MvPowerSeries (Fin 2) W →+* M) (ρ : W →+* M)
    (hC : ∀ w : W, Φ (MvPowerSeries.C w) = ρ w)
    (v α β : M) (p₀ p₁ : W)
    (hX0 : Φ (MvPowerSeries.X 0) = v * α) (hX1 : Φ (MvPowerSeries.X 1) = v * β)
    (hv : v ∈ maximalIdeal M)
    (hα : α - ρ p₀ ∈ maximalIdeal M) (hβ : β - ρ p₁ ∈ maximalIdeal M)
    (d : ℕ) (g : MvPowerSeries (Fin 2) W)
    (hg : g ∈ (Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W),
      MvPowerSeries.X 1}) ^ d) :
    ∃ r ∈ maximalIdeal M,
      Φ g = v ^ d * (ρ (MvPowerSeries.initialForm d g p₀ p₁) + r) := by
  classical
  have hbase : ∀ f : MvPowerSeries (Fin 2) W,
      ∃ r ∈ maximalIdeal M, Φ f = ρ (MvPowerSeries.coeff 0 f) + r := by
    intro f
    have hmem := mem_span_X_of_coeff_zero
      (f - MvPowerSeries.C (MvPowerSeries.coeff 0 f)) (by simp)
    obtain ⟨a, b, hab⟩ := Ideal.mem_span_pair.mp hmem
    refine ⟨Φ (f - MvPowerSeries.C (MvPowerSeries.coeff 0 f)), ?_, ?_⟩
    · rw [← hab, map_add, map_mul, map_mul, hX0, hX1]
      exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ (Ideal.mul_mem_right _ _ hv))
        (Ideal.mul_mem_left _ _ (Ideal.mul_mem_right _ _ hv))
    · rw [map_sub, hC]; ring
  suffices key : ∀ (d : ℕ) (g : MvPowerSeries (Fin 2) W),
      g ∈ (Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W),
        MvPowerSeries.X 1}) ^ d →
      ∃ r ∈ maximalIdeal M,
        Φ g = v ^ d * (ρ (MvPowerSeries.initialForm d g p₀ p₁) + r) by
    exact key d g hg
  intro d
  induction d with
  | zero =>
    intro g _
    obtain ⟨r, hr, h⟩ := hbase g
    exact ⟨r, hr, by rw [pow_zero, one_mul, MvPowerSeries.initialForm_zero, h]⟩
  | succ d ih =>
    intro g hg
    rw [pow_succ'] at hg
    refine Submodule.mul_induction_on hg ?_ ?_
    · intro a ha b hb
      obtain ⟨c₀, c₁, rfl⟩ := Ideal.mem_span_pair.mp ha
      obtain ⟨r₀, hr₀, h₀⟩ := ih (c₀ * b) (Ideal.mul_mem_left _ _ hb)
      obtain ⟨r₁, hr₁, h₁⟩ := ih (c₁ * b) (Ideal.mul_mem_left _ _ hb)
      refine ⟨(α - ρ p₀) * (ρ (MvPowerSeries.initialForm d (c₀ * b) p₀ p₁) + r₀) +
        ρ p₀ * r₀ + ((β - ρ p₁) *
          (ρ (MvPowerSeries.initialForm d (c₁ * b) p₀ p₁) + r₁) + ρ p₁ * r₁),
        ?_, ?_⟩
      · refine Ideal.add_mem _ (Ideal.add_mem _
          (Ideal.mul_mem_right _ _ hα) (Ideal.mul_mem_left _ _ hr₀))
          (Ideal.add_mem _ (Ideal.mul_mem_right _ _ hβ)
            (Ideal.mul_mem_left _ _ hr₁))
      · have e : (c₀ * MvPowerSeries.X 0 + c₁ * MvPowerSeries.X 1) * b =
            MvPowerSeries.X 0 * (c₀ * b) + MvPowerSeries.X 1 * (c₁ * b) := by ring
        rw [e, map_add, map_mul Φ (MvPowerSeries.X 0) (c₀ * b),
          map_mul Φ (MvPowerSeries.X 1) (c₁ * b), hX0, hX1, h₀, h₁,
          MvPowerSeries.initialForm_add, initialForm_X_zero_mul,
          initialForm_X_one_mul, map_add, map_mul, map_mul, pow_succ]
        ring
    · intro x y hx hy
      obtain ⟨r, hr, h⟩ := hx
      obtain ⟨r', hr', h'⟩ := hy
      exact ⟨r + r', Ideal.add_mem _ hr hr', by
        rw [map_add, h, h', MvPowerSeries.initialForm_add, map_add]; ring⟩

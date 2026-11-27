/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.Fourier.BooleanCubeBLR
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# The Friedgut–Kalai–Naor theorem

On a cube of positive dimension, `BooleanCube.fkn_theorem` bounds the relative Hamming distance
from a Boolean function to a signed coordinate by four times the Fourier weight off level one.
The proof detects a large singleton coefficient by averaging the cosine of the linear part,
then uses the influence of that coordinate.
-/

public section

namespace BooleanCube

open scoped BigOperators
open Finset (univ)
open Real (cos)

variable {n : ℕ}

/-- Averaging over each coordinate factors the cosine transform of a sum of signs. -/
private theorem expect_cos_sign_sum (a : Fin n → ℝ) (s : Finset (Fin n)) :
    (𝔼 x : BoolCube n, cos (∑ j ∈ s, a j * cubeVal (x j))) = ∏ j ∈ s, cos (a j) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    let t (x : BoolCube n) := ∑ j ∈ s, a j * cubeVal (x j)
    have ht (x : BoolCube n) : t (flipCoord x i) = t x := by
      refine Finset.sum_congr rfl fun j hj => ?_
      have hji : j ≠ i := fun h => hi (h ▸ hj)
      rw [flipCoord_apply_of_ne x hji]
    let g (x : BoolCube n) := cos (a i * cubeVal (x i) + t x)
    have hpair (x : BoolCube n) :
        g x + g (flipCoord x i) = (2 * cos (a i)) * cos (t x) := by
      simp only [g, ht, flipCoord_apply_self, cubeVal_not, mul_neg, Real.cos_add,
        Real.cos_neg, Real.sin_neg]
      cases x i <;> simp <;> ring
    have h := Finset.expect_congr (s := univ) rfl fun x _ => hpair x
    rw [Finset.expect_add_distrib, expect_comp_flipCoord, ← Finset.mul_expect] at h
    simp only [Finset.prod_insert hi, Finset.sum_insert hi, ← ih]
    change (𝔼 x, g x) = cos (a i) * 𝔼 x, cos (t x)
    linarith only [h]

private noncomputable def linearPart (f : BoolCube n → ℝ) (x : BoolCube n) : ℝ :=
  ∑ i, boolFourierCoeff n f {i} * cubeVal (x i)

private theorem coeff_linearPart (f : BoolCube n → ℝ) (S : Finset (Fin n)) :
    boolFourierCoeff n (linearPart f) S =
      if S.card = 1 then boolFourierCoeff n f S else 0 := by
  rw [← boolFourierCoeff_sum_mul_cubeChi
    (fun T => if T.card = 1 then boolFourierCoeff n f T else 0) S]
  congr 1
  funext x
  have hs : univ.filter (fun T : Finset (Fin n) => T.card = 1) = univ.powersetCard 1 := by
    ext
    simp
  simp_rw [ite_mul, zero_mul, ← Finset.sum_filter, hs, Finset.powersetCard_one, Finset.sum_map]
  simp [linearPart]

/-- Parseval identifies the squared projection error with the weight off level one. -/
private theorem linearPart_error {f : BoolCube n → ℝ} (hf : ∀ x, f x = 1 ∨ f x = -1) :
    (𝔼 x, (f x - linearPart f x) ^ 2) +
      (∑ S with S.card = 1, boolFourierCoeff n f S ^ 2) = 1 := by
  have hsq (x) : f x ^ 2 = 1 := by rcases hf x with h | h <;> simp [h]
  have h := expect_sq_eq_sum_boolFourierCoeff_sq f
  simp only [hsq, Fintype.expect_const] at h
  rw [h, expect_sq_eq_sum_boolFourierCoeff_sq (fun x => f x - linearPart f x),
    Finset.sum_filter, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun S _ => ?_
  rw [boolFourierCoeff_sub, coeff_linearPart]
  split_ifs <;> simp

/-- Near a Boolean function, the cosine of π times the projection is near minus one.
If every singleton coefficient had size at most one half, its average would be nonnegative. -/
private theorem exists_large_coeff {f : BoolCube n → ℝ} (hf : ∀ x, f x = 1 ∨ f x = -1)
    (hsmall : (𝔼 x, (f x - linearPart f x) ^ 2) < 1 / 8) :
    ∃ i, 1 / 2 < |boolFourierCoeff n f {i}| := by
  by_contra! h
  have hprod : (𝔼 x, cos (Real.pi * linearPart f x)) =
      ∏ i, cos (Real.pi * boolFourierCoeff n f {i}) := by
    simpa only [linearPart, Finset.mul_sum, mul_assoc] using
      expect_cos_sign_sum (fun i => Real.pi * boolFourierCoeff n f {i}) univ
  have hpos : 0 ≤ 𝔼 x, cos (Real.pi * linearPart f x) := by
    rw [hprod]
    refine Finset.prod_nonneg fun i _ => Real.cos_nonneg_of_mem_Icc ?_
    have hb := abs_le.mp (h i)
    constructor <;> nlinarith [mul_le_mul_of_nonneg_left hb.1 Real.pi_pos.le,
      mul_le_mul_of_nonneg_left hb.2 Real.pi_pos.le]
  have hpt (x : BoolCube n) :
      cos (Real.pi * linearPart f x) ≤ 8 * (f x - linearPart f x) ^ 2 - 1 := by
    have hcos : cos (Real.pi * linearPart f x - Real.pi * f x) =
        -cos (Real.pi * linearPart f x) := by
      rcases hf x with hx | hx <;> simp [hx, Real.cos_sub_pi, Real.cos_add_pi]
    have hb := Real.one_sub_sq_div_two_le_cos (x := Real.pi * linearPart f x - Real.pi * f x)
    rw [hcos] at hb
    have hπ : Real.pi ^ 2 ≤ 4 ^ 2 := pow_le_pow_left₀ Real.pi_pos.le Real.pi_lt_four.le 2
    nlinarith only [hb, mul_le_mul_of_nonneg_right hπ (sq_nonneg (f x - linearPart f x))]
  have havg := Finset.expect_le_expect (s := univ) fun x _ => hpt x
  rw [Finset.expect_sub_distrib, Fintype.expect_const, ← Finset.mul_expect] at havg
  linarith

/-- The coordinate derivative has absolute value zero or one. Its correlation with that
coordinate is thus bounded by its second moment, the influence. -/
private theorem abs_coeff_le_influence {f : BoolCube n → ℝ} (hf : ∀ x, f x = 1 ∨ f x = -1)
    (i : Fin n) : |boolFourierCoeff n f {i}| ≤ boolInfluence f i := by
  let d (x : BoolCube n) := (f x - f (flipCoord x i)) / 2
  have hd : boolFourierCoeff n d {i} = boolFourierCoeff n f {i} := by
    simp [d, boolFourierCoeff_derivative]
  rw [← hd, boolFourierCoeff_eq_expect]
  refine (Finset.abs_expect_le _ _).trans (Finset.expect_le_expect fun x _ => ?_)
  change |d x * cubeChi n {i} x| ≤ d x ^ 2
  rw [abs_mul, cubeChi_singleton, abs_cubeVal, mul_one]
  rcases hf x with hx | hx <;> rcases hf (flipCoord x i) with hy | hy <;> norm_num [d, hx, hy]

/-- All Fourier weight contributing to the influence apart from the singleton is part of the
projection error. -/
private theorem influence_le_coeff_sq_add_error (f : BoolCube n → ℝ) (i : Fin n) :
    boolInfluence f i ≤ boolFourierCoeff n f {i} ^ 2 + 𝔼 x, (f x - linearPart f x) ^ 2 := by
  rw [boolInfluence_eq_sum_sq, Finset.sum_filter,
    expect_sq_eq_sum_boolFourierCoeff_sq (fun x => f x - linearPart f x)]
  have hsingle : (∑ S, if S = {i} then boolFourierCoeff n f S ^ 2 else 0) =
      boolFourierCoeff n f {i} ^ 2 := by simp
  rw [← hsingle, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun S _ => ?_
  rw [boolFourierCoeff_sub, coeff_linearPart]
  by_cases hS : S.card = 1
  · obtain ⟨j, rfl⟩ := Finset.card_eq_one.mp hS
    by_cases hij : i = j <;> simp_all [eq_comm]
  · have hne : S ≠ {i} := by rintro rfl; simp at hS
    simp only [hS, hne, ite_false, sub_zero, zero_add]
    split_ifs
    · exact le_rfl
    · exact sq_nonneg _

/-- Choosing the sign of a coordinate according to its correlation gives the smaller distance. -/
private theorem signed_distance {f : BoolCube n → ℝ} (hf : ∀ x, f x = 1 ∨ f x = -1)
    (i : Fin n) {r : ℝ} (hr : (1 - |boolFourierCoeff n f {i}|) / 2 ≤ r) :
    boolDist f (fun x => cubeVal (x i)) ≤ r ∨ boolDist f (fun x => -cubeVal (x i)) ≤ r := by
  rcases le_total 0 (boolFourierCoeff n f {i}) with h | h
  · left
    rw [abs_of_nonneg h] at hr
    have hd := boolDist_cubeChi_eq hf {i}
    rw [funext (cubeChi_singleton n i)] at hd
    linarith
  · right
    rw [abs_of_nonpos h] at hr
    have hneg (x) : -1 * f x = 1 ∨ -1 * f x = -1 := by
      rcases hf x with hx | hx <;> simp [hx]
    have hd := boolDist_cubeChi_eq hneg {i}
    rw [boolFourierCoeff_const_mul] at hd
    have heq : boolDist (fun x => -1 * f x) (cubeChi n {i}) =
        boolDist f (fun x => -cubeVal (x i)) := by
      unfold boolDist
      simp [neg_eq_iff_eq_neg]
    linarith [heq]

/-- **Friedgut–Kalai–Naor (FKN) Theorem.** There is a universal constant `C` such that for every
`n ≥ 1` and every `f : BoolCube n → ℝ` with values `±1`, if `W¹[f] ≥ 1 - δ` then `f` is
`Cδ`-close to a dictator `χ_i` or a negated dictator `-χ_i` for some coordinate `i` (E. Friedgut,
G. Kalai and A. Naor, 2002; R. O'Donnell, *Analysis of Boolean Functions*, 2014, FKN Theorem,
stated in Section 2.5 with closeness `O(δ)` and proved in Section 9.1). The hypothesis `n ≥ 1`
is implicit in the source: for `n = 0` there is no coordinate to name. -/
theorem fkn_theorem :
    ∃ C : ℝ, ∀ (n : ℕ), 0 < n → ∀ f : BoolCube n → ℝ, (∀ x, f x = 1 ∨ f x = -1) →
      ∀ δ : ℝ, 1 - δ ≤ ∑ S with S.card = 1, boolFourierCoeff n f S ^ 2 →
        ∃ i : Fin n, boolDist f (fun x => cubeVal (x i)) ≤ C * δ ∨
          boolDist f (fun x => -cubeVal (x i)) ≤ C * δ := by
  refine ⟨4, ?_⟩
  intro n hn f hf δ hδ
  have herr := linearPart_error hf
  have hnonneg : 0 ≤ 𝔼 x, (f x - linearPart f x) ^ 2 :=
    Finset.expect_nonneg fun _ _ => sq_nonneg _
  have hδ₀ : 0 ≤ δ := by linarith
  by_cases hsmall : δ < 1 / 8
  · obtain ⟨i, hi⟩ := exists_large_coeff hf (by linarith)
    refine ⟨i, signed_distance hf i ?_⟩
    have hinf := (abs_coeff_le_influence hf i).trans (influence_le_coeff_sq_add_error f i)
    rw [← sq_abs (boolFourierCoeff n f {i})] at hinf
    by_cases hle : |boolFourierCoeff n f {i}| ≤ 1
    · nlinarith [mul_nonneg (sub_nonneg.mpr hi.le) (sub_nonneg.mpr hle)]
    · linarith
  · refine ⟨⟨0, hn⟩, signed_distance hf _ ?_⟩
    linarith [abs_nonneg (boolFourierCoeff n f {⟨0, hn⟩})]

end BooleanCube

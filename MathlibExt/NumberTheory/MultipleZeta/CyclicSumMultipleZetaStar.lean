/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.MultipleZeta.Series
import Mathlib.Data.List.Rotate
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Analysis.PSeries
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

@[expose] public section

open scoped ENNReal

open Topology

section
open scoped BigOperators

namespace MetaMathlibExt

namespace StarCyclic

/-- Nested finite sums over weakly decreasing chains; bottom weight `w`. -/
private noncomputable def tailWS : List ℕ → (ℕ → ℝ≥0∞) → ℕ → ℝ≥0∞
  | [], w, A => w A
  | e :: t, w, A => ∑ y ∈ Finset.Icc 1 A, ((y : ℝ≥0∞) ^ e)⁻¹ * tailWS t w y

/-- Top-level sum over the largest variable (weak chains). -/
private noncomputable def topSumS (e : ℕ) (t : List ℕ) (w : ℕ → ℕ → ℝ≥0∞) : ℝ≥0∞ :=
  ∑' x : ℕ, if 0 < x then ((x : ℝ≥0∞) ^ e)⁻¹ * tailWS t (w x) x else 0

/-- ENNReal multiple zeta-star value in recursive form. -/
private noncomputable def zetaRS : List ℕ → ℝ≥0∞
  | [] => 1
  | e :: t => topSumS e t (fun _ _ => 1)

/-- Harmonic bottom weight for `B` (weak chains, diagonal excluded). -/
private noncomputable def harmStar (x y : ℕ) : ℝ≥0∞ :=
  ∑ c ∈ Finset.Icc 1 y, (if c < x then (((x - c : ℕ) : ℝ≥0∞))⁻¹ else 0)

/-- Remainder weight for `A` (weak chains, diagonal excluded). -/
private noncomputable def wWeightS (L x y : ℕ) : ℝ≥0∞ :=
  ∑ c ∈ Finset.Icc 1 y,
    (if c < x then (x : ℝ≥0∞)⁻¹ * ((c : ℝ≥0∞) ^ (L - 1))⁻¹ *
      (((x - c : ℕ) : ℝ≥0∞))⁻¹ else 0)

/-- Auxiliary series `B`. -/
private noncomputable def cycB : List ℕ → ℝ≥0∞
  | [] => 0
  | e :: t => topSumS e t harmStar

/-- ENNReal multiple zeta-star value in tuple form. -/
private noncomputable def zetaEStar (l : List ℕ) : ℝ≥0∞ :=
  ∑' n : Fin l.length → ℕ,
    if (∀ a b : Fin l.length, a < b → n b ≤ n a) ∧ (∀ a, 0 < n a) then
      ∏ a, ((n a : ℝ≥0∞) ^ l.get a)⁻¹
    else 0

private lemma tailWS_sum (t : List ℕ) {ι : Type*} (s : Finset ι)
    (v : ι → ℕ → ℝ≥0∞) (A : ℕ) :
    tailWS t (fun y => ∑ i ∈ s, v i y) A = ∑ i ∈ s, tailWS t (v i) A := by
  induction t generalizing A with
  | nil => rfl
  | cons e t ih =>
    unfold tailWS
    trans ∑ y ∈ Finset.Icc 1 A, ∑ i ∈ s, ((y : ℝ≥0∞) ^ e)⁻¹ * tailWS t (v i) y
    · apply Finset.sum_congr rfl
      intro y _
      rw [ih, Finset.mul_sum]
    · exact Finset.sum_comm

private lemma tailWS_add (t : List ℕ) (w w' : ℕ → ℝ≥0∞) (A : ℕ) :
    tailWS t (fun y => w y + w' y) A = tailWS t w A + tailWS t w' A := by
  induction t generalizing A with
  | nil => rfl
  | cons e t ih =>
    unfold tailWS
    trans ∑ y ∈ Finset.Icc 1 A, (((y : ℝ≥0∞) ^ e)⁻¹ * tailWS t w y
      + ((y : ℝ≥0∞) ^ e)⁻¹ * tailWS t w' y)
    · apply Finset.sum_congr rfl
      intro y _
      rw [ih, mul_add]
    · exact Finset.sum_add_distrib

private lemma tailWS_const_mul (t : List ℕ) (r : ℝ≥0∞) (w : ℕ → ℝ≥0∞) (A : ℕ) :
    tailWS t (fun y => r * w y) A = r * tailWS t w A := by
  induction t generalizing A with
  | nil => rfl
  | cons e t ih =>
    unfold tailWS
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro y _
    rw [ih, mul_left_comm]

private lemma tailWS_congr (t : List ℕ) (w w' : ℕ → ℝ≥0∞) (A : ℕ) (hA : 0 < A)
    (h : ∀ y, 0 < y → y ≤ A → w y = w' y) : tailWS t w A = tailWS t w' A := by
  induction t generalizing A with
  | nil => exact h A hA (le_refl A)
  | cons e t ih =>
    unfold tailWS
    apply Finset.sum_congr rfl
    intro y hy
    have hy0 : 0 < y := (Finset.mem_Icc.mp hy).1
    have hyA : y ≤ A := (Finset.mem_Icc.mp hy).2
    congr 1
    exact ih y hy0 (fun z hz0 hz => h z hz0 (le_trans hz hyA))

private lemma tailWS_mono (t : List ℕ) (w w' : ℕ → ℝ≥0∞) (A : ℕ) (hA : 0 < A)
    (h : ∀ y, 0 < y → y ≤ A → w y ≤ w' y) : tailWS t w A ≤ tailWS t w' A := by
  induction t generalizing A with
  | nil => exact h A hA (le_refl A)
  | cons e t ih =>
    unfold tailWS
    apply Finset.sum_le_sum
    intro y hy
    have hy0 : 0 < y := (Finset.mem_Icc.mp hy).1
    have hyA : y ≤ A := (Finset.mem_Icc.mp hy).2
    exact mul_le_mul_right (ih y hy0 (fun z hz0 hz => h z hz0 (le_trans hz hyA))) _

private lemma tailWS_append (t : List ℕ) (e : ℕ) (w : ℕ → ℝ≥0∞) (A : ℕ) :
    tailWS (t ++ [e]) w A
      = tailWS t (fun y => ∑ c ∈ Finset.Icc 1 y, ((c : ℝ≥0∞) ^ e)⁻¹ * w c) A := by
  induction t generalizing A with
  | nil => rfl
  | cons e' t ih =>
    rw [List.cons_append]
    unfold tailWS
    apply Finset.sum_congr rfl
    intro y _
    congr 1
    exact ih y

private lemma tailWS_tsum (t : List ℕ) {ι : Type*} (v : ι → ℕ → ℝ≥0∞) (A : ℕ) :
    (∑' i, tailWS t (v i) A) = tailWS t (fun y => ∑' i, v i y) A := by
  induction t generalizing A with
  | nil => rfl
  | cons e t ih =>
    unfold tailWS
    rw [Summable.tsum_finsetSum (fun i _ => ENNReal.summable)]
    apply Finset.sum_congr rfl
    intro y _
    rw [ENNReal.tsum_mul_left, ih]

private lemma tailWS_zero (t : List ℕ) (A : ℕ) : tailWS t (fun _ => 0) A = 0 := by
  induction t generalizing A with
  | nil => rfl
  | cons e t' ih =>
    unfold tailWS
    simp only [ih, mul_zero, Finset.sum_const_zero]

/-- Strict harmonic tail weight (for the telescoping lemma only). -/
private noncomputable def harmTailLt (x y : ℕ) : ℝ≥0∞ :=
  ∑ c ∈ Finset.range y, (((x - c : ℕ) : ℝ≥0∞))⁻¹

private lemma tsum_Icc_swap (F : ℕ → ℕ → ℝ≥0∞) :
    (∑' x : ℕ, (if 0 < x then ∑ y ∈ Finset.Icc 1 x, F x y else 0))
      = ∑' y : ℕ, (if 0 < y then ∑' x : ℕ, (if y ≤ x then F x y else 0) else 0) := by
  have h1 : ∀ x : ℕ, (∑ y ∈ Finset.Icc 1 x, F x y)
      = ∑' y : ℕ, (if y ∈ Finset.Icc 1 x then F x y else 0) := by
    intro x
    have hsupp : Function.support (fun y => if y ∈ Finset.Icc 1 x then F x y else 0)
        ⊆ ↑(Finset.Icc 1 x) := by
      intro y hy
      rw [Finset.mem_coe]
      simp only [Function.mem_support, ne_eq] at hy
      by_contra hm
      exact hy (ite_eq_right hm)
    have h2 : (∑' y : ℕ, (if y ∈ Finset.Icc 1 x then F x y else 0))
        = ∑ y ∈ Finset.Icc 1 x, (if y ∈ Finset.Icc 1 x then F x y else 0) :=
      tsum_eq_sum' hsupp
    rw [h2]
    apply Finset.sum_congr rfl
    intro y hy
    rw [ite_eq_left hy]
  have hJ : ∀ x : ℕ, (if 0 < x then ∑ y ∈ Finset.Icc 1 x, F x y else 0)
      = ∑' y : ℕ, (if 0 < x ∧ 0 < y ∧ y ≤ x then F x y else 0) := by
    intro x
    by_cases hx : 0 < x
    · rw [ite_eq_left hx, h1 x]
      apply tsum_congr
      intro y
      by_cases hy : y ∈ Finset.Icc 1 x
      · obtain ⟨hy0, hyx⟩ := Finset.mem_Icc.mp hy
        rw [ite_eq_left hy, ite_eq_left ⟨hx, hy0, hyx⟩]
      · rw [ite_eq_right hy, ite_eq_right (fun h => hy (Finset.mem_Icc.mpr ⟨h.2.1, h.2.2⟩))]
    · rw [ite_eq_right hx]
      rw [tsum_congr (fun y => ite_eq_right (fun h : 0 < x ∧ 0 < y ∧ y ≤ x => hx h.1)),
        tsum_zero]
  rw [tsum_congr hJ, ENNReal.tsum_comm]
  apply tsum_congr
  intro y
  by_cases hy : 0 < y
  · rw [ite_eq_left hy]
    apply tsum_congr
    intro x
    by_cases hxy : y ≤ x
    · have hx : 0 < x := lt_of_lt_of_le hy hxy
      rw [ite_eq_left ⟨hx, hy, hxy⟩, ite_eq_left hxy]
    · rw [ite_eq_right (fun h => hxy h.2.2), ite_eq_right hxy]
  · rw [ite_eq_right hy]
    rw [tsum_congr (fun x => ite_eq_right (fun h : 0 < x ∧ 0 < y ∧ y ≤ x => hy h.2.1)),
      tsum_zero]

private lemma partial_fraction_real (x c : ℝ) (n : ℕ) (hx : 0 < x) (hc : 0 < c)
    (hcx : c < x) :
    1 / (x ^ (n + 1) * (x - c)) + ∑ i ∈ Finset.Icc 1 n, 1 / (x ^ (n + 1 - i + 1) * c ^ i)
      = 1 / (x * c ^ n * (x - c)) := by
  have hx0 : x ≠ 0 := ne_of_gt hx
  have hc0 : c ≠ 0 := ne_of_gt hc
  have hxc : x - c ≠ 0 := sub_ne_zero.mpr (ne_of_gt hcx)
  induction n with
  | zero => simp
  | succ n ih =>
    have h1 : 1 ≤ n + 1 := Nat.succ_le_succ (Nat.zero_le n)
    rw [Finset.sum_Icc_succ_top h1 (fun i => 1 / (x ^ (n + 1 + 1 - i + 1) * c ^ i))]
    have hS : (∑ i ∈ Finset.Icc 1 n, 1 / (x ^ (n + 1 + 1 - i + 1) * c ^ i))
        = (1 / x) * (∑ i ∈ Finset.Icc 1 n, 1 / (x ^ (n + 1 - i + 1) * c ^ i)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      have him : i ≤ n := (Finset.mem_Icc.mp hi).2
      have hexp : n + 1 + 1 - i + 1 = (n + 1 - i + 1) + 1 := by omega
      rw [hexp, pow_succ]
      field_simp
    have hT : (1 : ℝ) / (x ^ (n + 1 + 1 - (n + 1) + 1) * c ^ (n + 1))
        = 1 / (x ^ 2 * c ^ (n + 1)) := by
      have hexp2 : n + 1 + 1 - (n + 1) + 1 = 2 := by omega
      rw [hexp2]
    have hA : (1 : ℝ) / (x ^ (n + 1 + 1) * (x - c))
        = (1 / x) * (1 / (x ^ (n + 1) * (x - c))) := by
      rw [pow_succ]
      field_simp
    have hB : (1 : ℝ) / (x * c ^ (n + 1) * (x - c))
        = (1 / x) * (1 / (x * c ^ n * (x - c))) + 1 / (x ^ 2 * c ^ (n + 1)) := by
      field_simp
      ring
    rw [hS, hT, hA, hB]
    linear_combination (1 / x) * ih

private lemma partial_fraction_cyclic (x c L : ℕ) (hc : 1 ≤ c) (hcx : c < x)
    (hL : 1 ≤ L) :
    ((x : ℝ≥0∞) ^ L)⁻¹ * (((x - c : ℕ) : ℝ≥0∞))⁻¹
      + ∑ i ∈ Finset.Icc 1 (L - 1),
        ((x : ℝ≥0∞) ^ (L - i + 1))⁻¹ * ((c : ℝ≥0∞) ^ i)⁻¹
      = (x : ℝ≥0∞)⁻¹ * ((c : ℝ≥0∞) ^ (L - 1))⁻¹ * (((x - c : ℕ) : ℝ≥0∞))⁻¹ := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : L ≠ 0)
  simp only [Nat.succ_eq_add_one] at *
  rw [Nat.add_sub_cancel]
  have hx0 : x ≠ 0 := by omega
  have hc0' : c ≠ 0 := by omega
  have hsub0 : x - c ≠ 0 := by omega
  have hxE0 : (x : ℝ≥0∞) ≠ 0 := by exact_mod_cast hx0
  have hcE0 : (c : ℝ≥0∞) ≠ 0 := by exact_mod_cast hc0'
  have hsubE0 : ((x - c : ℕ) : ℝ≥0∞) ≠ 0 := by exact_mod_cast hsub0
  have hpowE_ne_zero : ∀ (a : ℝ≥0∞) (k : ℕ), a ≠ 0 → a ^ k ≠ 0 :=
    fun a k ha => ENNReal.pow_ne_zero ha k
  have hA_ne : ((x : ℝ≥0∞) ^ (n + 1))⁻¹ * (((x - c : ℕ) : ℝ≥0∞))⁻¹ ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.inv_ne_top.mpr (hpowE_ne_zero _ _ hxE0))
      (ENNReal.inv_ne_top.mpr hsubE0)
  have hS_ne : ∀ i ∈ Finset.Icc 1 n,
      ((x : ℝ≥0∞) ^ (n + 1 - i + 1))⁻¹ * ((c : ℝ≥0∞) ^ i)⁻¹ ≠ ⊤ := by
    intro i _
    exact ENNReal.mul_ne_top
      (ENNReal.inv_ne_top.mpr (hpowE_ne_zero _ _ hxE0))
      (ENNReal.inv_ne_top.mpr (hpowE_ne_zero _ _ hcE0))
  have hLHS_ne : ((x : ℝ≥0∞) ^ (n + 1))⁻¹ * (((x - c : ℕ) : ℝ≥0∞))⁻¹
      + ∑ i ∈ Finset.Icc 1 n,
        ((x : ℝ≥0∞) ^ (n + 1 - i + 1))⁻¹ * ((c : ℝ≥0∞) ^ i)⁻¹ ≠ ⊤ :=
    ENNReal.add_ne_top.mpr ⟨hA_ne, ENNReal.sum_ne_top.mpr hS_ne⟩
  have hRHS_ne : (x : ℝ≥0∞)⁻¹ * ((c : ℝ≥0∞) ^ n)⁻¹ * (((x - c : ℕ) : ℝ≥0∞))⁻¹ ≠ ⊤ :=
    ENNReal.mul_ne_top
      (ENNReal.mul_ne_top (ENNReal.inv_ne_top.mpr hxE0)
        (ENNReal.inv_ne_top.mpr (hpowE_ne_zero _ _ hcE0)))
      (ENNReal.inv_ne_top.mpr hsubE0)
  rw [← ENNReal.toReal_eq_toReal_iff' hLHS_ne hRHS_ne]
  rw [ENNReal.toReal_add hA_ne (ENNReal.sum_ne_top.mpr hS_ne)]
  rw [ENNReal.toReal_sum hS_ne]
  simp only [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_pow,
    ENNReal.toReal_natCast]
  have hxR : (0 : ℝ) < (x : ℝ) := by exact_mod_cast (by omega : 0 < x)
  have hcR : (0 : ℝ) < (c : ℝ) := by exact_mod_cast (by omega : 0 < c)
  have hcxR : (c : ℝ) < (x : ℝ) := by exact_mod_cast hcx
  have hsub : ((((x - c : ℕ))) : ℝ) = (x : ℝ) - (c : ℝ) :=
    Nat.cast_sub (le_of_lt hcx)
  have hreal := partial_fraction_real (x : ℝ) (c : ℝ) n hxR hcR hcxR
  simp only [one_div, mul_inv] at hreal
  rw [hsub]
  exact hreal

private lemma tele_inv_sub (y : ℝ) (c : ℕ) :
    ∑ d ∈ Finset.range c, (((y - d : ℝ))⁻¹ - ((y + 1 - d : ℝ))⁻¹)
      = ((y + 1 - c : ℝ))⁻¹ - ((y + 1 : ℝ))⁻¹ := by
  induction c with
  | zero => simp
  | succ c ih =>
    rw [Finset.sum_range_succ, ih]
    have harg : (y : ℝ) - (c : ℝ) = y + 1 - ((c : ℝ) + 1) := by ring
    have hcc : ((((c + 1 : ℕ))) : ℝ) = (c : ℝ) + 1 := by
      rw [Nat.cast_add, Nat.cast_one]
    rw [hcc, harg]
    ring

private lemma N6_partial (c A : ℕ) (hc : 1 ≤ c) (hca : c ≤ A) (N : ℕ) :
    ∑ m ∈ Finset.range N, ((A + 1 + m : ℝ))⁻¹ * ((((A + 1 + m - c : ℕ)) : ℝ))⁻¹
      = (c : ℝ)⁻¹ * ((∑ d ∈ Finset.range c, ((((A - d : ℕ)) : ℝ))⁻¹)
        - ∑ d ∈ Finset.range c, ((((A + N - d : ℕ)) : ℝ))⁻¹) := by
  have hcast : ∀ u v : ℕ, v ≤ u → ((((u - v : ℕ)) : ℝ)) = (u : ℝ) - (v : ℝ) := by
    intro u v h
    rw [Nat.cast_sub h]
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, ih]
    have htele : (∑ d ∈ Finset.range c, ((((A + N - d : ℕ)) : ℝ))⁻¹)
          - ∑ d ∈ Finset.range c, ((((A + N + 1 - d : ℕ)) : ℝ))⁻¹
        = ((((A + N + 1 - c : ℕ)) : ℝ))⁻¹ - ((((A + N + 1 : ℕ)) : ℝ))⁻¹ := by
      have e : ∀ d ∈ Finset.range c,
            ((((A + N - d : ℕ)) : ℝ))⁻¹ - ((((A + N + 1 - d : ℕ)) : ℝ))⁻¹
            = (((A:ℝ) + N - d))⁻¹ - (((A:ℝ) + N + 1 - d))⁻¹ := by
        intro d hd
        have hdc : d < c := Finset.mem_range.mp hd
        have h1 : d ≤ A + N := by omega
        have h2 : d ≤ A + N + 1 := by omega
        have hAN : ((((A + N : ℕ))) : ℝ) = (A : ℝ) + (N : ℝ) := by
          rw [Nat.cast_add]
        have hAN1 : ((((A + N + 1 : ℕ))) : ℝ) = (A : ℝ) + (N : ℝ) + 1 := by
          rw [Nat.cast_add, Nat.cast_add, Nat.cast_one]
        rw [hcast _ _ h1, hcast _ _ h2, hAN, hAN1]
      rw [← Finset.sum_sub_distrib]
      trans ∑ d ∈ Finset.range c, ((((A:ℝ) + N - d))⁻¹ - (((A:ℝ) + N + 1 - d))⁻¹)
      · exact Finset.sum_congr rfl (fun d hd => e d hd)
      · have eT1 : ((((A + N + 1 - c : ℕ)) : ℝ)) = (A:ℝ) + N + 1 - (c : ℝ) := by
          have hle : c ≤ A + N + 1 := by omega
          have hAN1 : ((((A + N + 1 : ℕ))) : ℝ) = (A : ℝ) + (N : ℝ) + 1 := by
            rw [Nat.cast_add, Nat.cast_add, Nat.cast_one]
          rw [hcast _ _ hle, hAN1]
        have eT2 : ((((A + N + 1 : ℕ)) : ℝ)) = (A:ℝ) + N + 1 := by
          rw [Nat.cast_add, Nat.cast_add, Nat.cast_one]
        rw [eT1, eT2]
        exact tele_inv_sub _ _
    have hterm : ((A + 1 + N : ℝ))⁻¹ * ((((A + 1 + N - c : ℕ)) : ℝ))⁻¹
        = (c : ℝ)⁻¹ * ((((A + N + 1 - c : ℕ)) : ℝ))⁻¹
          - (c : ℝ)⁻¹ * ((((A + N + 1 : ℕ)) : ℝ))⁻¹ := by
      have hle : c ≤ A + 1 + N := by omega
      have hle2 : c ≤ A + N + 1 := by omega
      have hAN1 : ((((A + 1 + N : ℕ))) : ℝ) = (A : ℝ) + 1 + (N : ℝ) := by
        rw [Nat.cast_add, Nat.cast_add, Nat.cast_one]
      have hAN1' : ((((A + N + 1 : ℕ))) : ℝ) = (A : ℝ) + (N : ℝ) + 1 := by
        rw [Nat.cast_add, Nat.cast_add, Nat.cast_one]
      have hnorm : (A : ℝ) + (N : ℝ) + 1 = (A : ℝ) + 1 + (N : ℝ) := by ring
      have hc0 : (c : ℝ) ≠ 0 := by exact_mod_cast (by omega : c ≠ 0)
      have hx0 : (A : ℝ) + 1 + (N : ℝ) ≠ 0 := by positivity
      have hxc0 : (A : ℝ) + 1 + (N : ℝ) - (c : ℝ) ≠ 0 := by
        have hcA : (c : ℝ) ≤ (A : ℝ) := by exact_mod_cast hca
        have hN : (0:ℝ) ≤ (N:ℝ) := Nat.cast_nonneg N
        have hpos : (0:ℝ) < (A:ℝ) + 1 + (N:ℝ) - (c:ℝ) := by linarith
        exact ne_of_gt hpos
      rw [hcast _ _ hle, hAN1, hcast _ _ hle2, hAN1', hnorm]
      field_simp
      ring
    rw [hterm]
    linear_combination (c : ℝ)⁻¹ * htele.symm

private lemma N6_reindex (c A : ℕ) :
    (∑' x : ℕ, (if A < x then ((x : ℝ))⁻¹ * ((((x - c : ℕ)) : ℝ))⁻¹ else 0))
      = ∑' m : ℕ, ((A + 1 + m : ℝ))⁻¹ * ((((A + 1 + m - c : ℕ)) : ℝ))⁻¹ := by
  have hinj : Function.Injective (fun m : ℕ => A + 1 + m) := by
    intro a b h
    simp only [] at h
    omega
  have hsupp : Function.support
        (fun x : ℕ => (if A < x then ((x : ℝ))⁻¹ * ((((x - c : ℕ)) : ℝ))⁻¹ else 0))
        ⊆ Set.range (fun m : ℕ => A + 1 + m) := by
    intro x hx
    simp only [Function.mem_support, ne_eq] at hx
    have hAx : A < x := by
      by_contra hcon
      apply hx
      exact ite_eq_right hcon
    refine ⟨x - (A + 1), ?_⟩
    change A + 1 + (x - (A + 1)) = x
    omega
  have h := Function.Injective.tsum_eq hinj hsupp
  rw [← h]
  apply tsum_congr
  intro m
  rw [ite_eq_left (by omega : A < A + 1 + m)]
  rw [Nat.cast_add, Nat.cast_add, Nat.cast_one]

private lemma N6_tendsto (c A : ℕ) (hca : c ≤ A) :
    Filter.Tendsto (fun N : ℕ => ∑ d ∈ Finset.range c, ((((A + N - d : ℕ)) : ℝ))⁻¹)
      Filter.atTop (nhds 0) := by
  have hcast : ∀ u v : ℕ, v ≤ u → ((((u - v : ℕ)) : ℝ)) = (u : ℝ) - (v : ℝ) := by
    intro u v h
    rw [Nat.cast_sub h]
  have hshift : Filter.Tendsto (fun N : ℕ => N + 1) Filter.atTop Filter.atTop :=
    StrictMono.tendsto_atTop (fun _ b h => Nat.succ_lt_succ h)
  have hglim : Filter.Tendsto (fun N : ℕ => (c : ℝ) / ((N : ℝ) + 1)) Filter.atTop (nhds 0) := by
    have hcomp := (tendsto_const_div_atTop_nhds_zero_nat (c : ℝ)).comp hshift
    apply Filter.Tendsto.congr _ hcomp
    intro N
    simp only [Function.comp_apply, Nat.cast_add, Nat.cast_one]
  have hbound : ∀ N : ℕ,
      (∑ d ∈ Finset.range c, ((((A + N - d : ℕ)) : ℝ))⁻¹) ≤ (c : ℝ) / ((N : ℝ) + 1) := by
    intro N
    have hNN : ∀ d ∈ Finset.range c,
        ((((A + N - d : ℕ)) : ℝ))⁻¹ ≤ (1 : ℝ) / ((N : ℝ) + 1) := by
      intro d hd
      have hdc : d < c := Finset.mem_range.mp hd
      have hle : d ≤ A + N := by omega
      have hdA1 : (d : ℝ) + 1 ≤ (A : ℝ) := by exact_mod_cast (by omega : d + 1 ≤ A)
      have hAN : ((((A + N : ℕ))) : ℝ) = (A : ℝ) + (N : ℝ) := by
        rw [Nat.cast_add]
      have hle2 : (N : ℝ) + 1 ≤ (A : ℝ) + (N : ℝ) - (d : ℝ) := by
        have hNp : (0:ℝ) ≤ (N:ℝ) := Nat.cast_nonneg N
        linarith
      have hNp1 : (0:ℝ) < (N : ℝ) + 1 := by
        have hNp : (0:ℝ) ≤ (N:ℝ) := Nat.cast_nonneg N
        linarith
      rw [hcast _ _ hle, hAN, inv_eq_one_div]
      exact one_div_le_one_div_of_le hNp1 hle2
    calc ∑ d ∈ Finset.range c, ((((A + N - d : ℕ)) : ℝ))⁻¹
        ≤ ∑ _d ∈ Finset.range c, (1 : ℝ) / ((N : ℝ) + 1) := Finset.sum_le_sum hNN
      _ = (c : ℝ) / ((N : ℝ) + 1) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          ring
  have hnn : ∀ N : ℕ,
      0 ≤ ∑ d ∈ Finset.range c, ((((A + N - d : ℕ)) : ℝ))⁻¹ := by
    intro N
    exact Finset.sum_nonneg (fun d _ => by positivity)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hglim hnn hbound

private lemma N6_hasSum (c A : ℕ) (hc : 1 ≤ c) (hca : c ≤ A) :
    HasSum (fun m : ℕ => ((A + 1 + m : ℝ))⁻¹ * ((((A + 1 + m - c : ℕ)) : ℝ))⁻¹)
      ((c : ℝ)⁻¹ * ∑ d ∈ Finset.range c, ((((A - d : ℕ)) : ℝ))⁻¹) := by
  have hnonneg : ∀ m : ℕ,
      0 ≤ ((A + 1 + m : ℝ))⁻¹ * ((((A + 1 + m - c : ℕ)) : ℝ))⁻¹ := by
    intro m
    positivity
  rw [hasSum_iff_tendsto_nat_of_nonneg hnonneg]
  have hpart := N6_partial c A hc hca
  have hfun : (fun N : ℕ => ∑ m ∈ Finset.range N,
        ((A + 1 + m : ℝ))⁻¹ * ((((A + 1 + m - c : ℕ)) : ℝ))⁻¹)
      = (fun N : ℕ => (c : ℝ)⁻¹ * ((∑ d ∈ Finset.range c, ((((A - d : ℕ)) : ℝ))⁻¹)
        - ∑ d ∈ Finset.range c, ((((A + N - d : ℕ)) : ℝ))⁻¹)) :=
    funext hpart
  rw [hfun]
  have hR := N6_tendsto c A hca
  have hlim : Filter.Tendsto
      (fun N : ℕ => (c : ℝ)⁻¹ * ((∑ d ∈ Finset.range c, ((((A - d : ℕ)) : ℝ))⁻¹)
        - ∑ d ∈ Finset.range c, ((((A + N - d : ℕ)) : ℝ))⁻¹))
      Filter.atTop
      (nhds ((c : ℝ)⁻¹ * ((∑ d ∈ Finset.range c, ((((A - d : ℕ)) : ℝ))⁻¹) - 0))) :=
    tendsto_const_nhds.mul (tendsto_const_nhds.sub hR)
  simpa using hlim

private lemma N6_real_tsum (c A : ℕ) (hc : 1 ≤ c) (hca : c ≤ A) :
    (∑' m : ℕ, ((A + 1 + m : ℝ))⁻¹ * ((((A + 1 + m - c : ℕ)) : ℝ))⁻¹)
      = (c : ℝ)⁻¹ * ∑ d ∈ Finset.range c, ((((A - d : ℕ)) : ℝ))⁻¹ :=
  HasSum.tsum_eq (N6_hasSum c A hc hca)

private lemma tsum_inv_mul_inv_sub_eq (c A : ℕ) (hc : 1 ≤ c) (hca : c ≤ A) :
    (∑' x : ℕ, (if A < x then (x : ℝ≥0∞)⁻¹ * (((x - c : ℕ) : ℝ≥0∞))⁻¹ else 0))
      = (c : ℝ≥0∞)⁻¹ * harmTailLt A c := by
  have hne : ∀ x : ℕ,
      (if A < x then (x : ℝ≥0∞)⁻¹ * (((x - c : ℕ) : ℝ≥0∞))⁻¹ else 0) ≠ ⊤ := by
    intro x
    split_ifs with hx
    · apply ENNReal.mul_ne_top
      · rw [ENNReal.inv_ne_top]
        have : x ≠ 0 := by omega
        exact_mod_cast this
      · rw [ENNReal.inv_ne_top]
        have : x - c ≠ 0 := by omega
        exact_mod_cast this
    · exact bot_ne_top
  have hmain : (∑' x : ℕ,
        (if A < x then (x : ℝ≥0∞)⁻¹ * (((x - c : ℕ) : ℝ≥0∞))⁻¹ else 0)).toReal
      = (c : ℝ)⁻¹ * ∑ d ∈ Finset.range c, ((((A - d : ℕ)) : ℝ))⁻¹ := by
    rw [ENNReal.tsum_toReal_eq hne]
    have hterm : ∀ x : ℕ,
        ((if A < x then (x : ℝ≥0∞)⁻¹ * (((x - c : ℕ) : ℝ≥0∞))⁻¹ else 0)).toReal
        = (if A < x then ((x : ℝ))⁻¹ * ((((x - c : ℕ)) : ℝ))⁻¹ else 0) := by
      intro x
      split_ifs with hx
      · rw [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_inv,
          ENNReal.toReal_natCast, ENNReal.toReal_natCast]
      · exact ENNReal.toReal_zero
    rw [tsum_congr hterm, N6_reindex c A, N6_real_tsum c A hc hca]
  have hval0 : (c : ℝ)⁻¹ * ∑ d ∈ Finset.range c, ((((A - d : ℕ)) : ℝ))⁻¹ ≠ 0 := by
    apply mul_ne_zero
    · have hcR : (0:ℝ) < (c : ℝ) := by exact_mod_cast (by omega : 0 < c)
      exact inv_ne_zero (ne_of_gt hcR)
    · apply ne_of_gt
      apply Finset.sum_pos
      · intro d hd
        have hdc : d < c := Finset.mem_range.mp hd
        have hpos : (0:ℝ) < ((((A - d : ℕ)) : ℝ)) := by
          have h1 : 0 < A - d := by omega
          exact_mod_cast h1
        exact inv_pos.mpr hpos
      · exact Finset.nonempty_range_iff.mpr (by omega : c ≠ 0)
  have hfin : (∑' x : ℕ,
      (if A < x then (x : ℝ≥0∞)⁻¹ * (((x - c : ℕ) : ℝ≥0∞))⁻¹ else 0)) ≠ ⊤ := by
    intro hcon
    apply hval0
    have h0 : (∑' x : ℕ,
      (if A < x then (x : ℝ≥0∞)⁻¹ * (((x - c : ℕ) : ℝ≥0∞))⁻¹ else 0)).toReal = 0 := by
      rw [hcon]
      exact ENNReal.toReal_top
    rw [hmain] at h0
    exact h0
  have hof := congrArg ENNReal.ofReal hmain
  rw [ENNReal.ofReal_toReal hfin] at hof
  have hfin_eq : ∀ d ∈ Finset.range c,
      ENNReal.ofReal ((((A - d : ℕ)) : ℝ))⁻¹ = ((((A - d : ℕ)) : ℝ≥0∞))⁻¹ := by
    intro d hd
    have hdc : d < c := Finset.mem_range.mp hd
    have hpos : (0:ℝ) < ((((A - d : ℕ)) : ℝ)) := by
      have h1 : 0 < A - d := by omega
      exact_mod_cast h1
    rw [ENNReal.ofReal_inv_of_pos hpos, ENNReal.ofReal_natCast]
  have hcR : (0:ℝ) < (c : ℝ) := by exact_mod_cast (by omega : 0 < c)
  rw [hof]
  rw [ENNReal.ofReal_mul (inv_nonneg.mpr (Nat.cast_nonneg c))]
  rw [ENNReal.ofReal_inv_of_pos hcR]
  rw [ENNReal.ofReal_natCast]
  unfold harmTailLt
  have hnn2 : ∀ d ∈ Finset.range c, (0:ℝ) ≤ ((((A - d : ℕ)) : ℝ))⁻¹ := by
    intro d hd
    positivity
  rw [ENNReal.ofReal_sum_of_nonneg hnn2]
  congr 1
  exact Finset.sum_congr rfl (fun d hd => hfin_eq d hd)

private lemma rotate_eq_get_cons_tail (k : List ℕ) (j : Fin k.length) :
    k.rotate j.1 = k.get j :: (k.rotate j.1).tail := by
  have hhead : (k.rotate j.1).head? = some (k.get j) := by
    rw [List.head?_rotate j.2, List.getElem?_eq_getElem j.2, List.get_eq_getElem]
  have hne : k.rotate j.1 ≠ [] := by
    intro h
    rw [h] at hhead
    simp at hhead
  obtain ⟨b, l', hcons⟩ := List.exists_cons_of_ne_nil hne
  have hb : b = k.get j := by
    have h1 : (b :: l').head? = some b := rfl
    rw [hcons] at hhead
    rw [h1] at hhead
    exact Option.some_inj.mp hhead
  rw [hcons, List.tail_cons, hb]

private lemma rotate_tail_append_get (k : List ℕ) (j : Fin k.length) :
    (k.rotate j.1).tail ++ [k.get j] = k.rotate (j.1 + 1) := by
  have h := rotate_eq_get_cons_tail k j
  have hrr : k.rotate (j.1 + 1) = (k.rotate j.1).tail ++ [k.get j] := by
    conv_lhs => rw [← List.rotate_rotate]
    conv_lhs => rw [h]
    rw [show (1 : ℕ) = 0 + 1 from rfl, List.rotate_cons_succ, List.rotate_zero]
  exact hrr.symm

private lemma sum_rotate_succ (k : List ℕ) (f : List ℕ → ℝ≥0∞) :
    ∑ j : Fin k.length, f (k.rotate (j.1 + 1)) = ∑ j : Fin k.length, f (k.rotate j.1) := by
  rcases eq_or_ne k [] with rfl | hne
  · simp
  · have hne0 : k.length ≠ 0 := fun h => hne (List.length_eq_zero_iff.mp h)
    have hpos : 0 < k.length := Nat.pos_of_ne_zero hne0
    have hlen : ∃ m, k.length = m + 1 := ⟨k.length - 1, by omega⟩
    obtain ⟨m, hm⟩ := hlen
    rw [Fin.sum_univ_eq_sum_range (fun n => f (k.rotate (n + 1))) k.length,
      Fin.sum_univ_eq_sum_range (fun n => f (k.rotate n)) k.length,
      hm, Finset.sum_range_succ, Finset.sum_range_succ']
    congr 1
    rw [← hm, List.rotate_length, List.rotate_zero]

private lemma chain_cons_iff_weak (n y : ℕ) (n' : Fin n → ℕ) :
    (∀ a b : Fin (n + 1), a < b →
      Fin.cons (α := fun _ => ℕ) y n' b ≤ Fin.cons (α := fun _ => ℕ) y n' a)
    ↔ (∀ a b : Fin n, a < b → n' b ≤ n' a) ∧ (∀ i, n' i ≤ y) := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · intro a b hab
      have hss : a.succ < b.succ := Fin.succ_lt_succ_iff.mpr hab
      have h2 := h a.succ b.succ hss
      simp only [Fin.cons_succ] at h2
      exact h2
    · intro i
      have h0s : (0 : Fin (n + 1)) < i.succ :=
        Fin.pos_iff_ne_zero.mpr (Fin.succ_ne_zero i)
      have h2 := h 0 i.succ h0s
      simp only [Fin.cons_succ, Fin.cons_zero] at h2
      exact h2
  · intro h a b hab
    obtain ⟨hc', hb'⟩ := h
    rcases Fin.eq_zero_or_eq_succ a with rfl | ⟨i, rfl⟩
    · rcases Fin.eq_zero_or_eq_succ b with rfl | ⟨j, rfl⟩
      · exact absurd hab (lt_irrefl 0)
      · simp only [Fin.cons_succ, Fin.cons_zero]
        exact hb' j
    · rcases Fin.eq_zero_or_eq_succ b with rfl | ⟨j, rfl⟩
      · exact absurd hab (not_lt_of_ge (Fin.zero_le _))
      · have hij : i < j := Fin.succ_lt_succ_iff.mp hab
        simp only [Fin.cons_succ]
        exact hc' i j hij

private lemma pos_cons_iff (n y : ℕ) (n' : Fin n → ℕ) :
    (∀ a : Fin (n + 1), 0 < Fin.cons (α := fun _ => ℕ) y n' a) ↔ (0 < y ∧ ∀ a, 0 < n' a) := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · have h2 := h 0
      rwa [Fin.cons_zero] at h2
    · intro a
      have h2 := h a.succ
      rwa [Fin.cons_succ] at h2
  · intro h a
    obtain ⟨hy0, hp'⟩ := h
    rcases Fin.eq_zero_or_eq_succ a with rfl | ⟨i, rfl⟩
    · rw [Fin.cons_zero]
      exact hy0
    · rw [Fin.cons_succ]
      exact hp' i

private lemma bnd_cons_iff_le (n y A : ℕ) (n' : Fin n → ℕ) :
    (∀ a : Fin (n + 1), Fin.cons (α := fun _ => ℕ) y n' a ≤ A) ↔ (y ≤ A ∧ ∀ a, n' a ≤ A) := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · have h2 := h 0
      rwa [Fin.cons_zero] at h2
    · intro a
      have h2 := h a.succ
      rwa [Fin.cons_succ] at h2
  · intro h a
    obtain ⟨hyA, hb'⟩ := h
    rcases Fin.eq_zero_or_eq_succ a with rfl | ⟨i, rfl⟩
    · rw [Fin.cons_zero]
      exact hyA
    · rw [Fin.cons_succ]
      exact hb' i

private lemma prod_cons_split_star (h : ℕ) (tl : List ℕ) (y : ℕ)
    (n' : Fin tl.length → ℕ) :
    (∏ a : Fin (tl.length + 1), ((Fin.cons (α := fun _ => ℕ) y n' a : ℝ≥0∞) ^ (h :: tl).get a)⁻¹)
    = ((y : ℝ≥0∞) ^ h)⁻¹ * ∏ a', ((n' a' : ℝ≥0∞) ^ tl.get a')⁻¹ := by
  have hget0 : (h :: tl).get (0 : Fin (tl.length + 1)) = h := rfl
  have hgetS : ∀ i : Fin tl.length, (h :: tl).get i.succ = tl.get i := fun i => rfl
  rw [Fin.prod_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ, hget0, hgetS]

private lemma zetaEStar_bounded_eq_tailWS (t : List ℕ) (A : ℕ) :
    (∑' n : Fin t.length → ℕ,
      if (∀ a b : Fin t.length, a < b → n b ≤ n a) ∧ (∀ a, 0 < n a) ∧ (∀ a, n a ≤ A)
      then ∏ a, ((n a : ℝ≥0∞) ^ t.get a)⁻¹ else 0)
    = tailWS t (fun _ => 1) A := by
  induction t generalizing A with
  | nil =>
    rw [tsum_eq_single default]
    · rw [ite_eq_left ⟨fun a => Fin.elim0 a, fun a => Fin.elim0 a, fun a => Fin.elim0 a⟩]
      rfl
    · intro b hb
      exfalso
      apply hb
      funext i
      exact Fin.elim0 i
  | cons h tl ih =>
    refine (Equiv.tsum_eq (Fin.consEquiv (n := tl.length) (fun _ => ℕ)) _).symm.trans ?_
    rw [ENNReal.tsum_prod']
    simp only [Fin.consEquiv_apply]
    have hcond : ∀ (y : ℕ) (n' : Fin tl.length → ℕ),
        ((∀ a b : Fin (tl.length + 1), a < b →
            Fin.cons (α := fun _ => ℕ) y n' b ≤ Fin.cons (α := fun _ => ℕ) y n' a)
          ∧ (∀ a, 0 < Fin.cons (α := fun _ => ℕ) y n' a)
          ∧ (∀ a, Fin.cons (α := fun _ => ℕ) y n' a ≤ A))
        ↔ (0 < y ∧ y ≤ A) ∧
          ((∀ a b : Fin tl.length, a < b → n' b ≤ n' a) ∧ (∀ a, 0 < n' a) ∧
            (∀ a, n' a ≤ y)) := by
      intro y n'
      rw [chain_cons_iff_weak, pos_cons_iff, bnd_cons_iff_le]
      constructor
      · intro hh
        obtain ⟨⟨hc', hb'⟩, ⟨hy0, hp'⟩, ⟨hyA, _⟩⟩ := hh
        exact ⟨⟨hy0, hyA⟩, hc', hp', hb'⟩
      · intro hh
        obtain ⟨⟨hy0, hyA⟩, hc', hp', hb'⟩ := hh
        refine ⟨⟨hc', hb'⟩, ⟨hy0, hp'⟩, hyA, ?_⟩
        intro i
        exact le_trans (hb' i) hyA
    have hpoint : ∀ y : ℕ, (∑' n' : Fin tl.length → ℕ,
        (if (∀ a b : Fin (tl.length + 1), a < b →
              Fin.cons (α := fun _ => ℕ) y n' b ≤ Fin.cons (α := fun _ => ℕ) y n' a)
            ∧ (∀ a, 0 < Fin.cons (α := fun _ => ℕ) y n' a)
            ∧ (∀ a, Fin.cons (α := fun _ => ℕ) y n' a ≤ A)
          then ∏ a : Fin (tl.length + 1),
            ((Fin.cons (α := fun _ => ℕ) y n' a : ℝ≥0∞) ^ (h :: tl).get a)⁻¹ else 0))
        = (if 0 < y ∧ y ≤ A then ((y : ℝ≥0∞) ^ h)⁻¹ * tailWS tl (fun _ => 1) y else 0) := by
      intro y
      by_cases hQ : 0 < y ∧ y ≤ A
      · rw [ite_eq_left hQ]
        trans ((y : ℝ≥0∞) ^ h)⁻¹ * ∑' n' : Fin tl.length → ℕ,
          (if (∀ a b : Fin tl.length, a < b → n' b ≤ n' a) ∧ (∀ a, 0 < n' a) ∧
            (∀ a, n' a ≤ y)
           then ∏ a', ((n' a' : ℝ≥0∞) ^ tl.get a')⁻¹ else 0)
        · rw [← ENNReal.tsum_mul_left]
          apply tsum_congr
          intro n'
          simp only [hcond y n', and_iff_right hQ, prod_cons_split_star h tl y n']
          split_ifs with hP
          · rfl
          · exact (mul_zero _).symm
        · rw [ih y]
      · rw [ite_eq_right hQ]
        trans (∑' _ : Fin tl.length → ℕ, (0 : ℝ≥0∞))
        · apply tsum_congr
          intro n'
          simp only [hcond y n']
          exact ite_eq_right (fun h => hQ h.1)
        · exact tsum_zero
    trans ∑' y : ℕ, (if 0 < y ∧ y ≤ A then ((y : ℝ≥0∞) ^ h)⁻¹ * tailWS tl (fun _ => 1) y else 0)
    · exact tsum_congr hpoint
    · have hsupp : Function.support
          (fun y : ℕ => if 0 < y ∧ y ≤ A then ((y : ℝ≥0∞) ^ h)⁻¹ * tailWS tl (fun _ => 1) y else 0)
          ⊆ ↑(Finset.Icc 1 A) := by
        intro y hy
        simp only [Function.mem_support, ne_eq] at hy
        rw [Finset.mem_coe, Finset.mem_Icc]
        by_contra hcon
        exact hy (ite_eq_right hcon)
      rw [tsum_eq_sum' hsupp]
      have hRHS : tailWS (h :: tl) (fun _ => 1) A
          = ∑ y ∈ Finset.Icc 1 A, ((y : ℝ≥0∞) ^ h)⁻¹ * tailWS tl (fun _ => 1) y := rfl
      rw [hRHS]
      apply Finset.sum_congr rfl
      intro y hy
      rw [Finset.mem_Icc] at hy
      have hy' : 0 < y ∧ y ≤ A := ⟨hy.1, hy.2⟩
      rw [ite_eq_left hy']

/-- Bundle a positive list as a multiple-zeta index. -/
private noncomputable def toIndexS (l : List ℕ) (hpos : ∀ x ∈ l, 0 < x) :
    MultipleZeta.Index :=
  ⟨l.sum, ⟨l, fun {x} hx => hpos x hx, rfl⟩⟩

private lemma zetaEStar_term_ne_top (l : List ℕ) (n : Fin l.length → ℕ) :
    (if (∀ a b : Fin l.length, a < b → n b ≤ n a) ∧ (∀ a, 0 < n a) then
      ∏ a, ((n a : ℝ≥0∞) ^ l.get a)⁻¹ else 0) ≠ ⊤ := by
  split_ifs with h
  · obtain ⟨_, hpos⟩ := h
    apply ENNReal.prod_ne_top
    intro a _
    apply ENNReal.inv_ne_top.mpr
    apply ENNReal.pow_ne_zero _ _
    have hpos' : 0 < n a := hpos a
    exact_mod_cast (ne_of_gt hpos')
  · exact bot_ne_top

private theorem starValue_toIndexS_eq (l : List ℕ)
    (hpos : ∀ x ∈ l, 0 < x) (hAdm : (toIndexS l hpos).IsAdmissibleOrEmpty) :
    MultipleZeta.starValue (toIndexS l hpos) hAdm = (zetaEStar l).toReal := by
  unfold MultipleZeta.starValue zetaEStar
  set index : MultipleZeta.Index := toIndexS l hpos with hindex
  have hdepth : index.depth = l.length := rfl
  have hterm : ∀ n : Fin l.length → ℕ,
      ((if (∀ a b : Fin l.length, a < b → n b ≤ n a) ∧ (∀ a, 0 < n a) then
        ∏ a, ((n a : ℝ≥0∞) ^ l.get a)⁻¹ else 0)).toReal
      = if (∀ a b : Fin l.length, a < b → n b ≤ n a) ∧ (∀ a, 0 < n a) then
        ∏ a, (((n a : ℕ) : ℝ) ^ l.get a)⁻¹ else 0 := by
    intro n
    split_ifs with h
    · rw [ENNReal.toReal_prod]
      apply Finset.prod_congr rfl
      intro a _
      rw [ENNReal.toReal_inv, ENNReal.toReal_pow, ENNReal.toReal_natCast]
    · exact ENNReal.toReal_zero
  rw [ENNReal.tsum_toReal_eq (fun n => zetaEStar_term_ne_top l n), tsum_congr hterm]
  set f : (Fin l.length → ℕ) → ℝ := fun n =>
    if (∀ a b : Fin l.length, a < b → n b ≤ n a) ∧ (∀ a, 0 < n a) then
      ∏ a, ((((n a : ℕ) : ℝ)) ^ l.get a)⁻¹
    else 0 with hf
  set g : MultipleZeta.WeaklyDecreasingTuple index.depth → (Fin l.length → ℕ) :=
    fun m a => (m.1 (Fin.cast hdepth.symm a) : ℕ) with hg
  have hg_inj : Function.Injective g := by
    intro m1 m2 h
    apply Subtype.ext
    funext i
    apply PNat.eq
    have hai := congrFun h (Fin.cast hdepth i)
    simp only [hg] at hai
    have hcast : Fin.cast hdepth.symm (Fin.cast hdepth i) = i :=
      Fin.leftInverse_cast hdepth i
    rw [hcast] at hai
    exact hai
  have hf_out : ∀ n ∉ Set.range g, f n = 0 := by
    intro n hn
    have hnot : ¬ ((∀ a b : Fin l.length, a < b → n b ≤ n a)
        ∧ (∀ a, 0 < n a)) := by
      intro hP
      apply hn
      refine ⟨⟨fun i => ⟨n (Fin.cast hdepth i), hP.2 _⟩, ?_⟩, ?_⟩
      · intro a b hab
        by_cases heq : a = b
        · subst heq
          exact le_rfl
        · have hlt : a < b := lt_of_le_of_ne hab heq
          have hab' : Fin.cast hdepth a < Fin.cast hdepth b := hlt
          have hle := hP.1 _ _ hab'
          exact_mod_cast hle
      · funext a
        change n (Fin.cast hdepth (Fin.cast hdepth.symm a)) = n a
        rw [Fin.rightInverse_cast hdepth a]
    simp only [hf, ite_eq_right hnot]
  have hfg : f ∘ g = MultipleZeta.starSummand index := by
    funext m
    simp only [Function.comp_apply]
    have hP : (∀ a b : Fin l.length, a < b → g m b ≤ g m a)
        ∧ (∀ a, 0 < g m a) := by
      constructor
      · intro a b hab
        have hab' : Fin.cast hdepth.symm a < Fin.cast hdepth.symm b := hab
        have hle : m.1 (Fin.cast hdepth.symm b) ≤ m.1 (Fin.cast hdepth.symm a) :=
          m.2 (le_of_lt hab')
        exact_mod_cast hle
      · intro a
        exact PNat.pos _
    simp only [hf, ite_eq_left hP]
    unfold MultipleZeta.starSummand
    rw [← Finset.prod_inv_distrib]
    refine Fintype.prod_equiv (Fin.castOrderIso hdepth.symm).toEquiv _ _ (fun a => ?_)
    rfl
  have hsupp : Function.support f ⊆ Set.range g := by
    intro n hn
    rw [Function.mem_support] at hn
    by_contra hcon
    exact hn (hf_out n hcon)
  have htsum := Function.Injective.tsum_eq hg_inj hsupp
  rw [← htsum]
  apply tsum_congr
  intro m
  exact (congrFun hfg m).symm

private theorem strictValue_singleton_toIndexS_eq (e : ℕ)
    (hpos : ∀ x ∈ [e], 0 < x) (hAdm : (toIndexS [e] hpos).IsAdmissibleOrEmpty) :
    MultipleZeta.strictValue (toIndexS [e] hpos) hAdm = (zetaEStar [e]).toReal := by
  unfold MultipleZeta.strictValue zetaEStar
  set index : MultipleZeta.Index := toIndexS [e] hpos with hindex
  have hdepth : index.depth = [e].length := rfl
  have hterm : ∀ n : Fin [e].length → ℕ,
      ((if (∀ a b : Fin [e].length, a < b → n b ≤ n a) ∧ (∀ a, 0 < n a) then
        ∏ a, ((n a : ℝ≥0∞) ^ [e].get a)⁻¹ else 0)).toReal
      = if (∀ a b : Fin [e].length, a < b → n b ≤ n a) ∧ (∀ a, 0 < n a) then
        ∏ a, ((((n a : ℕ) : ℝ)) ^ [e].get a)⁻¹ else 0 := by
    intro n
    split_ifs with h
    · rw [ENNReal.toReal_prod]
      apply Finset.prod_congr rfl
      intro a _
      rw [ENNReal.toReal_inv, ENNReal.toReal_pow, ENNReal.toReal_natCast]
    · exact ENNReal.toReal_zero
  rw [ENNReal.tsum_toReal_eq (fun n => zetaEStar_term_ne_top [e] n), tsum_congr hterm]
  set f : (Fin [e].length → ℕ) → ℝ := fun n =>
    if (∀ a b : Fin [e].length, a < b → n b ≤ n a) ∧ (∀ a, 0 < n a) then
      ∏ a, ((((n a : ℕ) : ℝ)) ^ [e].get a)⁻¹
    else 0 with hf
  set g : MultipleZeta.StrictDecreasingTuple index.depth → (Fin [e].length → ℕ) :=
    fun m a => (m.1 (Fin.cast hdepth.symm a) : ℕ) with hg
  have hg_inj : Function.Injective g := by
    intro m1 m2 h
    apply Subtype.ext
    funext i
    apply PNat.eq
    have hai := congrFun h (Fin.cast hdepth i)
    simp only [hg] at hai
    have hcast : Fin.cast hdepth.symm (Fin.cast hdepth i) = i :=
      Fin.leftInverse_cast hdepth i
    rw [hcast] at hai
    exact hai
  have hf_out : ∀ n ∉ Set.range g, f n = 0 := by
    intro n hn
    have hnot : ¬ ((∀ a b : Fin [e].length, a < b → n b ≤ n a)
        ∧ (∀ a, 0 < n a)) := by
      intro hP
      apply hn
      refine ⟨⟨fun i => ⟨n (Fin.cast hdepth i), hP.2 _⟩, ?_⟩, ?_⟩
      · intro a b hab
        exfalso
        have ha := a.isLt
        have hb := b.isLt
        have hlen : index.depth = 1 := hdepth.trans rfl
        have habv : a.val < b.val := hab
        omega
      · funext a
        change n (Fin.cast hdepth (Fin.cast hdepth.symm a)) = n a
        rw [Fin.rightInverse_cast hdepth a]
    simp only [hf, ite_eq_right hnot]
  have hfg : f ∘ g = MultipleZeta.strictSummand index := by
    funext m
    simp only [Function.comp_apply]
    have hP : (∀ a b : Fin [e].length, a < b → g m b ≤ g m a)
        ∧ (∀ a, 0 < g m a) := by
      constructor
      · intro a b hab
        have hab' : Fin.cast hdepth.symm a < Fin.cast hdepth.symm b := hab
        have hlt : m.1 (Fin.cast hdepth.symm b) < m.1 (Fin.cast hdepth.symm a) :=
          m.2 hab'
        have hle : (m.1 (Fin.cast hdepth.symm b) : ℕ)
            ≤ (m.1 (Fin.cast hdepth.symm a) : ℕ) := le_of_lt hlt
        exact_mod_cast hle
      · intro a
        exact PNat.pos _
    simp only [hf, ite_eq_left hP]
    unfold MultipleZeta.strictSummand
    rw [← Finset.prod_inv_distrib]
    refine Fintype.prod_equiv (Fin.castOrderIso hdepth.symm).toEquiv _ _ (fun a => ?_)
    rfl
  have hsupp : Function.support f ⊆ Set.range g := by
    intro n hn
    rw [Function.mem_support] at hn
    by_contra hcon
    exact hn (hf_out n hcon)
  have htsum := Function.Injective.tsum_eq hg_inj hsupp
  rw [← htsum]
  apply tsum_congr
  intro m
  exact (congrFun hfg m).symm

private theorem index_eq_toIndexS_of_entries (idx : MultipleZeta.Index) (l : List ℕ)
    (hl : idx.entries = l) (hpos : ∀ x ∈ l, 0 < x) : idx = toIndexS l hpos := by
  rcases idx with ⟨w, comp⟩
  simp only [MultipleZeta.Index.entries] at hl
  apply Composition.sigma_eq_iff_blocks_eq.mpr
  change comp.blocks = (toIndexS l hpos).2.blocks
  rw [hl]
  rfl

private theorem starValue_eq_zetaEStar_of_entries (idx : MultipleZeta.Index)
    (l : List ℕ) (hl : idx.entries = l) (hpos : ∀ x ∈ l, 0 < x)
    (hAdm : idx.IsAdmissibleOrEmpty) :
    MultipleZeta.starValue idx hAdm = (zetaEStar l).toReal := by
  have heq : idx = toIndexS l hpos := index_eq_toIndexS_of_entries idx l hl hpos
  have hgen : ∀ (idx' : MultipleZeta.Index) (h : idx'.IsAdmissibleOrEmpty),
      idx' = toIndexS l hpos →
        MultipleZeta.starValue idx' h = (zetaEStar l).toReal := by
    intro idx' h heq'
    subst heq'
    exact starValue_toIndexS_eq l hpos h
  exact hgen _ _ heq

private theorem strictValue_singleton_eq_zetaEStar_of_entries
    (idx : MultipleZeta.Index) (e : ℕ) (hl : idx.entries = [e])
    (hpos : ∀ x ∈ [e], 0 < x) (hAdm : idx.IsAdmissibleOrEmpty) :
    MultipleZeta.strictValue idx hAdm = (zetaEStar [e]).toReal := by
  have heq : idx = toIndexS [e] hpos := index_eq_toIndexS_of_entries idx [e] hl hpos
  have hgen : ∀ (idx' : MultipleZeta.Index) (h : idx'.IsAdmissibleOrEmpty),
      idx' = toIndexS [e] hpos →
        MultipleZeta.strictValue idx' h = (zetaEStar [e]).toReal := by
    intro idx' h heq'
    subst heq'
    exact strictValue_singleton_toIndexS_eq e hpos h
  exact hgen _ _ heq

private lemma pow_inv_mul_pow_inv (x : ℕ) (hx : 0 < x) (a b : ℕ) :
    ((x : ℝ≥0∞) ^ a)⁻¹ * ((x : ℝ≥0∞) ^ b)⁻¹ = ((x : ℝ≥0∞) ^ (a + b))⁻¹ := by
  have hx0 : (x : ℝ≥0∞) ≠ 0 := by exact_mod_cast (ne_of_gt hx)
  have hxT : (x : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top x
  have ha0 : ((x : ℝ≥0∞) ^ a) ≠ 0 := ENNReal.pow_ne_zero hx0 a
  have haT : ((x : ℝ≥0∞) ^ a) ≠ ⊤ := ENNReal.pow_ne_top hxT
  rw [pow_add, ENNReal.mul_inv (Or.inl ha0) (Or.inl haT)]

private lemma tailWS_dirac_zero (t : List ℕ) (x y : ℕ) (v : ℝ≥0∞) (hyx : y < x) :
    tailWS t (fun z => if z = x then v else 0) y = 0 := by
  induction t generalizing y with
  | nil =>
    simp only [tailWS]
    rw [ite_eq_right (by omega : ¬ y = x)]
  | cons e t' ih =>
    unfold tailWS
    apply Finset.sum_eq_zero
    intro z hz
    have hzy : z ≤ y := (Finset.mem_Icc.mp hz).2
    rw [ih z (by omega : z < x), mul_zero]

private lemma tailWS_dirac_eq (rest : List ℕ) (x : ℕ) (hx : 0 < x) (v : ℝ≥0∞) :
    tailWS rest (fun y => if y = x then v else 0) x
      = ((x : ℝ≥0∞) ^ rest.sum)⁻¹ * v := by
  induction rest generalizing v with
  | nil =>
    unfold tailWS
    simp
  | cons r rest' ih =>
    unfold tailWS
    have hsingle : ∀ y ∈ Finset.Icc 1 x,
        ((y : ℝ≥0∞) ^ r)⁻¹ * tailWS rest' (fun z => if z = x then v else 0) y
        = if y = x then ((x : ℝ≥0∞) ^ r)⁻¹ * (((x : ℝ≥0∞) ^ rest'.sum)⁻¹ * v) else 0 := by
      intro y hy
      by_cases hyx : y = x
      · subst hyx
        rw [ite_eq_left rfl]
        exact congrArg _ (ih v)
      · rw [ite_eq_right hyx]
        have hylt : y < x := by
          have h1 : 1 ≤ y := (Finset.mem_Icc.mp hy).1
          have h2 : y ≤ x := (Finset.mem_Icc.mp hy).2
          omega
        rw [tailWS_dirac_zero rest' x y v hylt, mul_zero]
    rw [Finset.sum_congr rfl hsingle]
    rw [Finset.sum_eq_single x]
    · rw [ite_eq_left rfl, List.sum_cons, ← mul_assoc,
        pow_inv_mul_pow_inv x hx r rest'.sum]
    · intro y hy hyx
      rw [ite_eq_right hyx]
    · intro hxmem
      have hx1 : x ∈ Finset.Icc 1 x := Finset.mem_Icc.mpr ⟨hx, le_rfl⟩
      exact absurd hx1 hxmem

private lemma diag_sum_single (L x : ℕ) (hL : 1 ≤ L) (hx : 0 < x) :
    ∑ i ∈ Finset.Icc 1 (L - 1), ((x : ℝ≥0∞) ^ (L - i + 1))⁻¹ * ((x : ℝ≥0∞) ^ i)⁻¹
      = ((L - 1 : ℕ) : ℝ≥0∞) * ((x : ℝ≥0∞) ^ (L + 1))⁻¹ := by
  have hterm : ∀ i ∈ Finset.Icc 1 (L - 1),
      ((x : ℝ≥0∞) ^ (L - i + 1))⁻¹ * ((x : ℝ≥0∞) ^ i)⁻¹
        = ((x : ℝ≥0∞) ^ (L + 1))⁻¹ := by
    intro i hi
    have hi2 : i ≤ L - 1 := (Finset.mem_Icc.mp hi).2
    have hexp : L - i + 1 + i = L + 1 := by omega
    rw [pow_inv_mul_pow_inv x hx (L - i + 1) i, hexp]
  have hcard : (Finset.Icc 1 (L - 1)).card = L - 1 := by
    rw [Nat.card_Icc]
    omega
  have hconst : (∑ _i ∈ Finset.Icc 1 (L - 1), ((x : ℝ≥0∞) ^ (L + 1))⁻¹)
      = ((L - 1 : ℕ) : ℝ≥0∞) * ((x : ℝ≥0∞) ^ (L + 1))⁻¹ := by
    rw [Finset.sum_const, hcard, nsmul_eq_mul]
  exact (Finset.sum_congr rfl (fun i hi => hterm i hi)).trans hconst

private lemma split_pointwise (L x y : ℕ) (hL : 1 ≤ L) (hx : 0 < x)
    (hyx : y ≤ x) :
    (∑ i ∈ Finset.Icc 1 (L - 1), ((x : ℝ≥0∞) ^ (L - i + 1))⁻¹ *
      (∑ c ∈ Finset.Icc 1 y, ((c : ℝ≥0∞) ^ i)⁻¹))
      + ((x : ℝ≥0∞) ^ L)⁻¹ * harmStar x y
    = wWeightS L x y
      + (if y = x then ((L - 1 : ℕ) : ℝ≥0∞) * ((x : ℝ≥0∞) ^ (L + 1))⁻¹ else 0) := by
  have hS : (∑ i ∈ Finset.Icc 1 (L - 1), ((x : ℝ≥0∞) ^ (L - i + 1))⁻¹ *
      (∑ c ∈ Finset.Icc 1 y, ((c : ℝ≥0∞) ^ i)⁻¹))
      = ∑ c ∈ Finset.Icc 1 y, ∑ i ∈ Finset.Icc 1 (L - 1),
        ((x : ℝ≥0∞) ^ (L - i + 1))⁻¹ * ((c : ℝ≥0∞) ^ i)⁻¹ := by
    simp only [Finset.mul_sum]
    exact Finset.sum_comm
  have hB : ((x : ℝ≥0∞) ^ L)⁻¹ * harmStar x y
      = ∑ c ∈ Finset.Icc 1 y,
        ((x : ℝ≥0∞) ^ L)⁻¹ * (if c < x then (((x - c : ℕ) : ℝ≥0∞))⁻¹ else 0) := by
    unfold harmStar
    rw [Finset.mul_sum]
  have hD : (if y = x then ((L - 1 : ℕ) : ℝ≥0∞) * ((x : ℝ≥0∞) ^ (L + 1))⁻¹ else 0)
      = ∑ c ∈ Finset.Icc 1 y,
        (if c = x then ((L - 1 : ℕ) : ℝ≥0∞) * ((x : ℝ≥0∞) ^ (L + 1))⁻¹ else 0) := by
    by_cases hyx' : y = x
    · rw [ite_eq_left hyx', hyx']
      rw [Finset.sum_eq_single x]
      · rw [ite_eq_left rfl]
      · intro c _ hcx
        rw [ite_eq_right hcx]
      · intro hxmem
        have hx1 : x ∈ Finset.Icc 1 x := Finset.mem_Icc.mpr ⟨hx, le_rfl⟩
        exact absurd hx1 hxmem
    · rw [ite_eq_right hyx']
      symm
      apply Finset.sum_eq_zero
      intro c hc
      have hcy : c ≤ y := (Finset.mem_Icc.mp hc).2
      have hne : ¬ c = x := by omega
      rw [ite_eq_right hne]
  unfold wWeightS
  rw [hS, hB, hD, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro c hc
  have hc1 : 1 ≤ c := (Finset.mem_Icc.mp hc).1
  have hcy : c ≤ y := (Finset.mem_Icc.mp hc).2
  have hcx_le : c ≤ x := le_trans hcy hyx
  by_cases hcx : c < x
  · have hne : ¬ c = x := by omega
    rw [ite_eq_left hcx, ite_eq_left hcx, ite_eq_right hne, add_zero]
    have hpf := partial_fraction_cyclic x c L hc1 hcx hL
    rw [add_comm (∑ i ∈ Finset.Icc 1 (L - 1),
      ((x : ℝ≥0∞) ^ (L - i + 1))⁻¹ * ((c : ℝ≥0∞) ^ i)⁻¹)]
    exact hpf
  · have hceq : c = x := by omega
    have hnc : ¬ c < x := by omega
    rw [ite_eq_right hnc, ite_eq_right hnc, ite_eq_left hceq]
    simp only [mul_zero, add_zero, zero_add]
    rw [hceq]
    exact diag_sum_single L x hL hx

private lemma split_fixed (L : ℕ) (rest : List ℕ) (x : ℕ) (hL : 1 ≤ L)
    (hx : 0 < x) :
    (∑ i ∈ Finset.Icc 1 (L - 1), ((x : ℝ≥0∞) ^ (L - i + 1))⁻¹ *
      tailWS (rest ++ [i]) (fun _ => 1) x)
      + ((x : ℝ≥0∞) ^ L)⁻¹ * tailWS rest (harmStar x) x
    = tailWS rest (wWeightS L x) x
      + tailWS rest
        (fun y => if y = x then ((L - 1 : ℕ) : ℝ≥0∞) * ((x : ℝ≥0∞) ^ (L + 1))⁻¹
          else 0) x := by
  have e1 : ∀ i ∈ Finset.Icc 1 (L - 1),
      ((x : ℝ≥0∞) ^ (L - i + 1))⁻¹ * tailWS (rest ++ [i]) (fun _ => 1) x
      = tailWS rest
        (fun y => ((x : ℝ≥0∞) ^ (L - i + 1))⁻¹ *
          (∑ c ∈ Finset.Icc 1 y, ((c : ℝ≥0∞) ^ i)⁻¹)) x := by
    intro i _
    have happ : tailWS (rest ++ [i]) (fun _ => 1) x
        = tailWS rest (fun y => ∑ c ∈ Finset.Icc 1 y, ((c : ℝ≥0∞) ^ i)⁻¹) x := by
      rw [tailWS_append rest i (fun _ => 1) x]
      exact tailWS_congr rest _ _ x hx (fun y _ _ => by simp [mul_one])
    rw [happ, ← tailWS_const_mul]
  have eS : (∑ i ∈ Finset.Icc 1 (L - 1), ((x : ℝ≥0∞) ^ (L - i + 1))⁻¹ *
      tailWS (rest ++ [i]) (fun _ => 1) x)
      = tailWS rest (fun y => ∑ i ∈ Finset.Icc 1 (L - 1),
        ((x : ℝ≥0∞) ^ (L - i + 1))⁻¹ *
          (∑ c ∈ Finset.Icc 1 y, ((c : ℝ≥0∞) ^ i)⁻¹)) x := by
    calc (∑ i ∈ Finset.Icc 1 (L - 1), ((x : ℝ≥0∞) ^ (L - i + 1))⁻¹ *
          tailWS (rest ++ [i]) (fun _ => 1) x)
        = ∑ i ∈ Finset.Icc 1 (L - 1), tailWS rest
            (fun y => ((x : ℝ≥0∞) ^ (L - i + 1))⁻¹ *
              (∑ c ∈ Finset.Icc 1 y, ((c : ℝ≥0∞) ^ i)⁻¹)) x :=
          Finset.sum_congr rfl (fun i hi => e1 i hi)
      _ = tailWS rest (fun y => ∑ i ∈ Finset.Icc 1 (L - 1),
            ((x : ℝ≥0∞) ^ (L - i + 1))⁻¹ *
              (∑ c ∈ Finset.Icc 1 y, ((c : ℝ≥0∞) ^ i)⁻¹)) x :=
          (tailWS_sum rest _ _ _).symm
  have eB : ((x : ℝ≥0∞) ^ L)⁻¹ * tailWS rest (harmStar x) x
      = tailWS rest (fun y => ((x : ℝ≥0∞) ^ L)⁻¹ * harmStar x y) x :=
    (tailWS_const_mul rest _ _ _).symm
  rw [eS, eB, ← tailWS_add, ← tailWS_add]
  exact tailWS_congr rest _ _ x hx
    (fun y _ hyx => split_pointwise L x y hL hx hyx)

private lemma split_add (L : ℕ) (hL : 1 ≤ L) (rest : List ℕ) :
    (∑ i ∈ Finset.Icc 1 (L - 1), zetaRS ((L - i + 1) :: (rest ++ [i])))
      + cycB (L :: rest)
    = ((L - 1 : ℕ) : ℝ≥0∞) * zetaRS [L + rest.sum + 1]
      + topSumS 0 rest (wWeightS L) := by
  have hZ : zetaRS [L + rest.sum + 1]
      = (∑' x : ℕ, (if 0 < x then ((x : ℝ≥0∞) ^ (L + rest.sum + 1))⁻¹ * 1 else 0)) :=
    rfl
  have hD : ∀ x : ℕ, 0 < x →
      tailWS rest
        (fun y => if y = x then ((L - 1 : ℕ) : ℝ≥0∞) * ((x : ℝ≥0∞) ^ (L + 1))⁻¹
          else 0) x
      = ((L - 1 : ℕ) : ℝ≥0∞) * (((x : ℝ≥0∞) ^ (L + rest.sum + 1))⁻¹ * 1) := by
    intro x hx
    rw [tailWS_dirac_eq rest x hx]
    have hexp : L + rest.sum + 1 = rest.sum + (L + 1) := by omega
    rw [hexp, ← pow_inv_mul_pow_inv x hx rest.sum (L + 1), mul_one]
    ring
  rw [hZ]
  unfold cycB zetaRS topSumS
  simp only [pow_zero, inv_one, one_mul]
  rw [← ENNReal.tsum_mul_left]
  rw [← Summable.tsum_finsetSum (fun i _ => ENNReal.summable)]
  rw [← ENNReal.tsum_add, ← ENNReal.tsum_add]
  apply tsum_congr
  intro x
  split_ifs with hx
  · have h := split_fixed L rest x hL hx
    rw [hD x hx] at h
    exact h.trans (add_comm _ _)
  · simp

private lemma cpow_succ_inv (L c : ℕ) (hL : 1 ≤ L) (hc : 1 ≤ c) :
    ((c : ℝ≥0∞) ^ (L - 1))⁻¹ * (c : ℝ≥0∞)⁻¹ = ((c : ℝ≥0∞) ^ L)⁻¹ := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hL
  rw [Nat.add_sub_cancel]
  have hc0 : (c : ℝ≥0∞) ≠ 0 := by
    have hc0' : c ≠ 0 := by omega
    exact_mod_cast hc0'
  have hcT : (c : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top c
  have ha : ((c : ℝ≥0∞) ^ k) ≠ 0 ∨ (c : ℝ≥0∞) ≠ ⊤ := Or.inr hcT
  have hb : ((c : ℝ≥0∞) ^ k) ≠ ⊤ ∨ (c : ℝ≥0∞) ≠ 0 := Or.inr hc0
  rw [pow_succ, ENNReal.mul_inv ha hb]

private lemma sum_Icc_one_eq_sum_range (g : ℕ → ℝ≥0∞) (c : ℕ) :
    ∑ c' ∈ Finset.Icc 1 c, g c' = ∑ i ∈ Finset.range c, g (i + 1) := by
  have h1 : Finset.Icc 1 c = Finset.Ico 1 (c + 1) := by
    ext i
    simp only [Finset.mem_Icc, Finset.mem_Ico]
    omega
  rw [h1, Finset.sum_Ico_eq_sum_range]
  simp only [Nat.add_sub_cancel]
  apply Finset.sum_congr rfl
  intro i _
  rw [add_comm (1 : ℕ) i]

private lemma bridge_sub_one (y c : ℕ) (hcy : c < y) :
    harmTailLt (y - 1) c = harmStar y c := by
  have hS : harmStar y c = ∑ c' ∈ Finset.Icc 1 c, (((y - c' : ℕ) : ℝ≥0∞))⁻¹ := by
    unfold harmStar
    apply Finset.sum_congr rfl
    intro c' hc'
    have hlt : c' < y := by
      have h2 := (Finset.mem_Icc.mp hc').2
      omega
    rw [ite_eq_left hlt]
  rw [hS, sum_Icc_one_eq_sum_range]
  unfold harmTailLt
  apply Finset.sum_congr rfl
  intro d hd
  have hdc : d < c := Finset.mem_range.mp hd
  have heq : y - 1 - d = y - (d + 1) := by omega
  rw [heq]

private lemma bridge_self (y : ℕ) (hy : 0 < y) :
    harmTailLt y y = harmStar y y + ((y : ℝ≥0∞))⁻¹ := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : y ≠ 0)
  have hS : harmStar (m + 1) (m + 1)
      = ∑ c' ∈ Finset.Icc 1 m, ((((m + 1) - c' : ℕ)) : ℝ≥0∞)⁻¹ := by
    unfold harmStar
    rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ m + 1)]
    rw [ite_eq_right (lt_irrefl _)]
    simp only [add_zero]
    apply Finset.sum_congr rfl
    intro c' hc'
    have hlt : c' < m + 1 := by
      have h2 := (Finset.mem_Icc.mp hc').2
      omega
    rw [ite_eq_left hlt]
  have hT : harmTailLt (m + 1) (m + 1)
      = ((((m + 1 : ℕ))) : ℝ≥0∞)⁻¹
        + ∑ c' ∈ Finset.Icc 1 m, ((((m + 1) - c' : ℕ)) : ℝ≥0∞)⁻¹ := by
    unfold harmTailLt
    rw [Finset.sum_range_succ']
    have hf0 : ((((m + 1) - 0 : ℕ))) = ((m + 1 : ℕ)) := by rw [Nat.sub_zero]
    rw [hf0, sum_Icc_one_eq_sum_range, add_comm]
  rw [hT, hS]
  exact add_comm _ _

private lemma guard_collapse (x y c A : ℕ) (hA : A = max (y - 1) c) (hcy : c ≤ y)
    (G : ℕ → ℝ≥0∞) :
    (if y ≤ x then (if c < x then G x else 0) else 0)
      = (if A < x then G x else 0) := by
  by_cases h1 : y ≤ x
  · rw [ite_eq_left h1]
    by_cases h2 : c < x
    · rw [ite_eq_left h2]
      have h3 : A < x := by omega
      rw [ite_eq_left h3]
    · rw [ite_eq_right h2]
      have h3 : ¬ A < x := by omega
      rw [ite_eq_right h3]
  · rw [ite_eq_right h1]
    by_cases h3 : A < x
    · rw [ite_eq_left h3]
      exfalso
      omega
    · rw [ite_eq_right h3]

private lemma inner_single_star (L c y : ℕ) (hL : 1 ≤ L) (hc : 1 ≤ c)
    (hcy : c ≤ y) (hy : 0 < y) :
    (∑' x : ℕ, (if y ≤ x then (if c < x then (x : ℝ≥0∞)⁻¹ *
      ((c : ℝ≥0∞) ^ (L - 1))⁻¹ * (((x - c : ℕ)) : ℝ≥0∞)⁻¹ else 0) else 0))
    = ((c : ℝ≥0∞) ^ L)⁻¹ * harmStar y c
      + (if c = y then ((y : ℝ≥0∞) ^ (L + 1))⁻¹ else 0) := by
  have hfactor : ∀ x : ℕ,
      (if y ≤ x then (if c < x then (x : ℝ≥0∞)⁻¹ * ((c : ℝ≥0∞) ^ (L - 1))⁻¹ *
        (((x - c : ℕ)) : ℝ≥0∞)⁻¹ else 0) else 0)
      = ((c : ℝ≥0∞) ^ (L - 1))⁻¹ *
        (if y ≤ x then (if c < x then (x : ℝ≥0∞)⁻¹ * (((x - c : ℕ)) : ℝ≥0∞)⁻¹
          else 0) else 0) := by
    intro x
    by_cases h1 : y ≤ x
    · rw [ite_eq_left h1]
      by_cases h2 : c < x
      · rw [ite_eq_left h2, ite_eq_left h1, ite_eq_left h2]
        ring
      · rw [ite_eq_right h2, ite_eq_right h2, ite_eq_left h1]
        exact (mul_zero _).symm
    · rw [ite_eq_right h1, ite_eq_right h1]
      exact (mul_zero _).symm
  rw [tsum_congr hfactor, ENNReal.tsum_mul_left]
  by_cases hcy_lt : c < y
  · have hAeq : max (y - 1) c = y - 1 := by omega
    have hguard : ∀ x : ℕ, (if y ≤ x then (if c < x then (x : ℝ≥0∞)⁻¹ *
        (((x - c : ℕ)) : ℝ≥0∞)⁻¹ else 0) else 0)
        = (if y - 1 < x then (x : ℝ≥0∞)⁻¹ * (((x - c : ℕ)) : ℝ≥0∞)⁻¹ else 0) := by
      intro x
      have h := guard_collapse x y c (max (y - 1) c) rfl hcy
        (fun t => (t : ℝ≥0∞)⁻¹ * ((((t - c : ℕ))) : ℝ≥0∞)⁻¹)
      rw [hAeq] at h
      exact h
    rw [tsum_congr hguard, tsum_inv_mul_inv_sub_eq c (y - 1) hc (by omega : c ≤ y - 1)]
    rw [bridge_sub_one y c hcy_lt, ← mul_assoc, cpow_succ_inv L c hL hc]
    rw [ite_eq_right (by omega : ¬ c = y), add_zero]
  · have hceq : c = y := by omega
    have hAeq : max (y - 1) c = y := by omega
    have hguard : ∀ x : ℕ, (if y ≤ x then (if c < x then (x : ℝ≥0∞)⁻¹ *
        (((x - c : ℕ)) : ℝ≥0∞)⁻¹ else 0) else 0)
        = (if y < x then (x : ℝ≥0∞)⁻¹ * (((x - c : ℕ)) : ℝ≥0∞)⁻¹ else 0) := by
      intro x
      have h := guard_collapse x y c (max (y - 1) c) rfl hcy
        (fun t => (t : ℝ≥0∞)⁻¹ * ((((t - c : ℕ))) : ℝ≥0∞)⁻¹)
      rw [hAeq] at h
      exact h
    rw [tsum_congr hguard, tsum_inv_mul_inv_sub_eq c y hc hcy]
    rw [ite_eq_left hceq, hceq]
    have hbr := bridge_self y hy
    rw [hbr, mul_add, mul_add]
    congr 1
    · rw [← mul_assoc, cpow_succ_inv L y hL (by omega : 1 ≤ y)]
    · have hy1 : ((y : ℝ≥0∞))⁻¹ = ((y : ℝ≥0∞) ^ 1)⁻¹ := by rw [pow_one]
      rw [← mul_assoc, cpow_succ_inv L y hL (by omega : 1 ≤ y), hy1,
        pow_inv_mul_pow_inv y hy L 1]

private lemma inner_tsum_wWeightS (L y z : ℕ) (hL : 1 ≤ L) (hy : 0 < y)
    (hzy : z ≤ y) :
    (∑' x : ℕ, (if y ≤ x then wWeightS L x z else 0))
    = (∑ c ∈ Finset.Icc 1 z, ((c : ℝ≥0∞) ^ L)⁻¹ * harmStar y c)
      + (if z = y then ((y : ℝ≥0∞) ^ (L + 1))⁻¹ else 0) := by
  have hpush : ∀ x : ℕ, (if y ≤ x then wWeightS L x z else 0)
      = ∑ c ∈ Finset.Icc 1 z,
        (if y ≤ x then (if c < x then (x : ℝ≥0∞)⁻¹ * ((c : ℝ≥0∞) ^ (L - 1))⁻¹ *
          ((((x - c : ℕ))) : ℝ≥0∞)⁻¹ else 0) else 0) := by
    intro x
    unfold wWeightS
    by_cases h : y ≤ x
    · rw [ite_eq_left h]
      apply Finset.sum_congr rfl
      intro c _
      rw [ite_eq_left h]
    · rw [ite_eq_right h]
      symm
      apply Finset.sum_eq_zero
      intro c _
      rw [ite_eq_right h]
  have hE : (if z = y then ((y : ℝ≥0∞) ^ (L + 1))⁻¹ else 0)
      = ∑ c ∈ Finset.Icc 1 z,
        (if c = y then ((y : ℝ≥0∞) ^ (L + 1))⁻¹ else 0) := by
    by_cases hzy' : z = y
    · rw [ite_eq_left hzy', hzy']
      rw [Finset.sum_eq_single y]
      · rw [ite_eq_left rfl]
      · intro c _ hcy2
        rw [ite_eq_right hcy2]
      · intro hymem
        have hmem : y ∈ Finset.Icc 1 y := Finset.mem_Icc.mpr ⟨hy, le_rfl⟩
        exact absurd hmem hymem
    · rw [ite_eq_right hzy']
      symm
      apply Finset.sum_eq_zero
      intro c hc
      have hcz : c ≤ z := (Finset.mem_Icc.mp hc).2
      have hne : ¬ c = y := by omega
      rw [ite_eq_right hne]
  simp only [hpush]
  rw [Summable.tsum_finsetSum (fun c _ => ENNReal.summable)]
  rw [hE, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro c hc
  have hc1 : 1 ≤ c := (Finset.mem_Icc.mp hc).1
  have hcz : c ≤ z := (Finset.mem_Icc.mp hc).2
  exact inner_single_star L c y hL hc1 (le_trans hcz hzy) hy

private lemma rotate_nil (L : ℕ) (hL : 1 ≤ L) :
    topSumS 0 [] (wWeightS L) = cycB [L] + zetaRS [L + 1] := by
  have hnil : ∀ (w : ℕ → ℝ≥0∞) (A : ℕ), tailWS [] w A = w A := fun w A => rfl
  have hZ1 : zetaRS [L + 1]
      = (∑' c : ℕ, (if 0 < c then ((c : ℝ≥0∞) ^ (L + 1))⁻¹ * 1 else 0)) := rfl
  have eSwap : (∑' x : ℕ, (if 0 < x then wWeightS L x x else 0))
      = (∑' a : ℕ, ((if 0 < a then ((a : ℝ≥0∞) ^ L)⁻¹ * harmStar a a else 0)
        + (if 0 < a then ((a : ℝ≥0∞) ^ (L + 1))⁻¹ * 1 else 0))) := by
    have hU : ∀ x : ℕ, (if 0 < x then wWeightS L x x else 0)
        = (if 0 < x then ∑ c ∈ Finset.Icc 1 x, (if c < x then (x : ℝ≥0∞)⁻¹ *
          ((c : ℝ≥0∞) ^ (L - 1))⁻¹ * (((x - c : ℕ)) : ℝ≥0∞)⁻¹ else 0) else 0) := by
      intro x
      unfold wWeightS
      by_cases hx : 0 < x <;> simp [hx]
    rw [tsum_congr hU, tsum_Icc_swap]
    apply tsum_congr
    intro c
    split_ifs with hc0
    · have h := inner_single_star L c c hL (by omega) le_rfl hc0
      rw [h, ite_eq_left rfl, mul_one]
    · simp
  unfold cycB topSumS
  simp only [pow_zero, inv_one, one_mul, hnil]
  rw [hZ1, eSwap, ← ENNReal.tsum_add]

private lemma rotate_cons (L e : ℕ) (r : List ℕ) (hL : 1 ≤ L) :
    topSumS 0 (e :: r) (wWeightS L)
      = cycB ((e :: r) ++ [L]) + zetaRS [L + (e :: r).sum + 1] := by
  simp only [List.cons_append, List.sum_cons]
  have htail : ∀ x : ℕ, tailWS (e :: r) (wWeightS L x) x
      = ∑ y ∈ Finset.Icc 1 x, ((y : ℝ≥0∞) ^ e)⁻¹ * tailWS r (wWeightS L x) y :=
    fun x => rfl
  have hZ : zetaRS [L + (e + r.sum) + 1]
      = (∑' y : ℕ, (if 0 < y then ((y : ℝ≥0∞) ^ (L + (e + r.sum) + 1))⁻¹ * 1
        else 0)) := rfl
  have hB : cycB (e :: (r ++ [L]))
      = (∑' y : ℕ, (if 0 < y then ((y : ℝ≥0∞) ^ e)⁻¹ *
        tailWS (r ++ [L]) (harmStar y) y else 0)) := rfl
  have hLHS : topSumS 0 (e :: r) (wWeightS L)
      = (∑' y : ℕ, (if 0 < y then ∑' x : ℕ, (if y ≤ x then ((y : ℝ≥0∞) ^ e)⁻¹ *
        tailWS r (wWeightS L x) y else 0) else 0)) := by
    unfold topSumS
    simp only [pow_zero, inv_one, one_mul, htail]
    exact tsum_Icc_swap _
  rw [hLHS, hB, hZ, ← ENNReal.tsum_add]
  apply tsum_congr
  intro y
  split_ifs with hy
  · have hf : ∀ x : ℕ, (if y ≤ x then ((y : ℝ≥0∞) ^ e)⁻¹ * tailWS r (wWeightS L x) y
        else 0)
        = ((y : ℝ≥0∞) ^ e)⁻¹ * (if y ≤ x then tailWS r (wWeightS L x) y else 0) := by
      intro x
      by_cases h : y ≤ x
      · rw [ite_eq_left h, ite_eq_left h]
      · rw [ite_eq_right h, ite_eq_right h]
        exact (mul_zero _).symm
    have hmove : ∀ x : ℕ, (if y ≤ x then tailWS r (wWeightS L x) y else 0)
        = tailWS r (fun z => if y ≤ x then wWeightS L x z else 0) y := by
      intro x
      split_ifs with h
      · rfl
      · rw [tailWS_zero]
    simp only [hf, hmove]
    rw [ENNReal.tsum_mul_left, tailWS_tsum]
    have hIn : ∀ z : ℕ, 0 < z → z ≤ y →
        (∑' x : ℕ, (if y ≤ x then wWeightS L x z else 0))
        = (∑ c ∈ Finset.Icc 1 z, ((c : ℝ≥0∞) ^ L)⁻¹ * harmStar y c)
          + (if z = y then ((y : ℝ≥0∞) ^ (L + 1))⁻¹ else 0) :=
      fun z _ hzy => inner_tsum_wWeightS L y z hL hy hzy
    have hcongr := tailWS_congr r _ _ y hy hIn
    rw [hcongr, tailWS_add, mul_add]
    congr 1
    · have happ0 : tailWS r
          (fun z => ∑ c ∈ Finset.Icc 1 z, ((c : ℝ≥0∞) ^ L)⁻¹ * harmStar y c) y
          = tailWS (r ++ [L]) (harmStar y) y := by
        rw [tailWS_append r L (harmStar y) y]
      rw [happ0]
    · rw [tailWS_dirac_eq r y hy]
      have hexp : L + (e + r.sum) + 1 = e + (r.sum + (L + 1)) := by omega
      rw [hexp, mul_one, ← pow_inv_mul_pow_inv y hy e (r.sum + (L + 1)),
        pow_inv_mul_pow_inv y hy r.sum (L + 1)]
  · simp

private lemma rotate_add (L : ℕ) (hL : 1 ≤ L) (rest : List ℕ) :
    topSumS 0 rest (wWeightS L) = cycB (rest ++ [L]) + zetaRS [L + rest.sum + 1] := by
  cases rest with
  | nil =>
    simp only [List.nil_append, List.sum_nil, Nat.add_zero]
    exact rotate_nil L hL
  | cons e r =>
    exact rotate_cons L e r hL

/-- Real harmonic numbers. -/
private noncomputable def hR (x : ℕ) : ℝ := ∑ m ∈ Finset.Icc 1 x, ((m : ℝ))⁻¹

private lemma hR_eq_harmonic (x : ℕ) : hR x = ((harmonic x : ℚ) : ℝ) := by
  unfold hR
  rw [harmonic_eq_sum_Icc]
  push_cast
  rfl

private lemma hR_nonneg (x : ℕ) : 0 ≤ hR x := by
  unfold hR
  exact Finset.sum_nonneg (fun i _ => by positivity)

/-- ENNReal harmonic numbers. -/
private noncomputable def Hstar (x : ℕ) : ℝ≥0∞ :=
  ∑ m ∈ Finset.Icc 1 x, ((m : ℝ≥0∞))⁻¹

private lemma Hstar_eq_ofReal (x : ℕ) : Hstar x = ENNReal.ofReal (hR x) := by
  unfold Hstar hR
  rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => by positivity)]
  apply Finset.sum_congr rfl
  intro i hi
  have hi1 : 1 ≤ i := (Finset.mem_Icc.mp hi).1
  have hpos : (0:ℝ) < ((i : ℝ)) := by exact_mod_cast (by omega : 0 < i)
  rw [ENNReal.ofReal_inv_of_pos hpos, ENNReal.ofReal_natCast]

private lemma Hstar_mono {a b : ℕ} (h : a ≤ b) : Hstar a ≤ Hstar b := by
  unfold Hstar
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro x hx
    rw [Finset.mem_Icc] at hx ⊢
    omega
  · intro i _ _
    exact bot_le

private noncomputable def eps (p : ℕ) : ℝ := 1 / (2 * (p : ℝ) + 2)

private noncomputable def capC (p : ℕ) : ℝ := 1 + 1 / eps p

private lemma eps_pos (p : ℕ) : 0 < eps p := by
  unfold eps
  positivity

private lemma hR_le (p : ℕ) (x : ℕ) (hx : 1 ≤ x) :
    hR x ≤ capC p * (x : ℝ) ^ (eps p) := by
  have hxR : (1:ℝ) ≤ (x:ℝ) := by exact_mod_cast hx
  have hxnn : (0:ℝ) ≤ (x:ℝ) := le_trans zero_le_one hxR
  have hlog : Real.log (x:ℝ) ≤ (x:ℝ) ^ (eps p) / (eps p) :=
    Real.log_le_rpow_div hxnn (eps_pos p)
  have h1 : (1:ℝ) ≤ (x:ℝ) ^ (eps p) :=
    Real.one_le_rpow hxR (le_of_lt (eps_pos p))
  have hbase : hR x ≤ 1 + Real.log (x:ℝ) := by
    rw [hR_eq_harmonic]
    exact harmonic_le_one_add_log x
  unfold capC
  linear_combination hbase + hlog + h1

private lemma eps_mul_le (p : ℕ) : eps p * (p : ℝ) ≤ 1 / 2 := by
  have h2p : (0:ℝ) < 2 * (p:ℝ) + 2 := by positivity
  have heq : eps p * (p:ℝ) = (p:ℝ) / (2 * (p:ℝ) + 2) := by
    unfold eps
    ring
  rw [heq, div_le_iff₀ h2p]
  have hnn : (0:ℝ) ≤ (p:ℝ) := Nat.cast_nonneg _
  linarith

private lemma summable_harm_rpow (p : ℕ) :
    Summable (fun x : ℕ => (hR x) ^ p / (x : ℝ) ^ 2) := by
  rw [← summable_nat_add_iff 1]
  have h32 : Summable (fun x : ℕ => (((((x + 1 : ℕ)) : ℝ) ^ ((3/2 : ℝ))))⁻¹) :=
    (summable_nat_add_iff 1).mpr (Real.summable_nat_rpow_inv.mpr (by norm_num))
  have hle : ∀ x : ℕ, (hR (x + 1)) ^ p / ((((x + 1 : ℕ))) : ℝ) ^ 2
      ≤ (capC p) ^ p * (((((x + 1 : ℕ))) : ℝ) ^ ((3/2 : ℝ)))⁻¹ := by
    intro x
    set t : ℝ := (((x + 1 : ℕ)) : ℝ) with ht
    have hx : 1 ≤ x + 1 := by omega
    have hxR : (1:ℝ) ≤ t := by rw [ht]; exact_mod_cast hx
    have hxpos : (0:ℝ) < t := lt_of_lt_of_le zero_lt_one hxR
    have hH : hR (x + 1) ≤ capC p * t ^ (eps p) := hR_le p (x + 1) hx
    have hHnn := hR_nonneg (x + 1)
    have hpow : (hR (x + 1)) ^ p ≤ ((capC p) * t ^ (eps p)) ^ p :=
      pow_le_pow_left₀ hHnn hH p
    rw [mul_pow] at hpow
    have hpow_rpow : (t ^ (eps p)) ^ p = t ^ (eps p * (p:ℝ)) := by
      rw [← Real.rpow_natCast _ p, ← Real.rpow_mul (le_of_lt hxpos)]
    have hle_rpow : t ^ (eps p * (p:ℝ)) ≤ (t ^ ((3/2 : ℝ)))⁻¹ * t ^ 2 := by
      have e2 : (t ^ ((3/2 : ℝ)))⁻¹ = t ^ (-(3/2 : ℝ)) :=
        (Real.rpow_neg (le_of_lt hxpos) _).symm
      rw [e2, ← Real.rpow_natCast t 2, ← Real.rpow_add hxpos]
      have e3 : (-(3/2 : ℝ)) + (((2:ℕ)):ℝ) = 1/2 := by norm_num
      rw [e3]
      exact Real.rpow_le_rpow_of_exponent_le hxR (by linarith [eps_mul_le p])
    have hC : 0 ≤ capC p := by
      unfold capC
      have he := eps_pos p
      positivity
    calc (hR (x + 1)) ^ p / t ^ 2
        ≤ ((capC p) ^ p * t ^ (eps p * (p:ℝ))) / t ^ 2 := by
          apply (div_le_div_iff_of_pos_right (pow_pos hxpos 2)).mpr
          rw [← hpow_rpow]
          exact hpow
      _ ≤ (capC p) ^ p * (t ^ ((3/2 : ℝ)))⁻¹ := by
          have h2 : t ^ (eps p * (p:ℝ)) / t ^ 2 ≤ (t ^ ((3/2 : ℝ)))⁻¹ :=
            (div_le_iff₀ (pow_pos hxpos 2)).mpr hle_rpow
          calc ((capC p) ^ p * t ^ (eps p * (p:ℝ))) / t ^ 2
              = (capC p) ^ p * (t ^ (eps p * (p:ℝ)) / t ^ 2) := by ring
            _ ≤ (capC p) ^ p * (t ^ ((3/2 : ℝ)))⁻¹ :=
                mul_le_mul_of_nonneg_left h2 (pow_nonneg hC p)
  exact Summable.of_nonneg_of_le
    (fun x => div_nonneg (pow_nonneg (hR_nonneg _) _) (by positivity))
    hle (h32.mul_left _)

private lemma enn_harm_ne_top (p : ℕ) :
    (∑' x : ℕ, (if 0 < x then (Hstar x) ^ p * (((x : ℝ≥0∞) ^ 2))⁻¹ else 0)) ≠ ⊤ := by
  have hterm : ∀ x : ℕ, (if 0 < x then (Hstar x) ^ p * (((x : ℝ≥0∞) ^ 2))⁻¹ else 0)
      = ENNReal.ofReal ((hR x) ^ p / (x : ℝ) ^ 2) := by
    intro x
    by_cases hx : 0 < x
    · rw [ite_eq_left hx]
      have hxR : (0:ℝ) < (x:ℝ) := by exact_mod_cast hx
      rw [Hstar_eq_ofReal, ← ENNReal.ofReal_pow (hR_nonneg x),
        ← ENNReal.ofReal_natCast x, ← ENNReal.ofReal_pow (by positivity),
        div_eq_mul_inv, ENNReal.ofReal_mul (pow_nonneg (hR_nonneg x) _)]
      congr 1
      exact (ENNReal.ofReal_inv_of_pos (pow_pos hxR 2)).symm
    · rw [ite_eq_right hx]
      have hx0 : x = 0 := by omega
      subst hx0
      have e0 : hR 0 = 0 := by simp [hR]
      rw [e0]
      by_cases hp : p = 0
      · subst hp
        simp
      · simp [hp]
  rw [tsum_congr hterm, ← ENNReal.ofReal_tsum_of_nonneg
    (fun x => div_nonneg (pow_nonneg (hR_nonneg _) _) (by positivity))
    (summable_harm_rpow p)]
  exact ENNReal.ofReal_ne_top

private lemma pow_inv_le_one (y e : ℕ) (hy : 1 ≤ y) (he : 1 ≤ e) :
    (((y : ℝ≥0∞) ^ e))⁻¹ ≤ ((y : ℝ≥0∞))⁻¹ := by
  have hy1 : (1:ℝ≥0∞) ≤ ((y : ℝ≥0∞)) := by exact_mod_cast hy
  have hpow : ((y : ℝ≥0∞)) ^ 1 ≤ ((y : ℝ≥0∞)) ^ e := pow_le_pow_right₀ hy1 he
  rw [pow_one] at hpow
  exact ENNReal.inv_le_inv.mpr hpow

private lemma tailWS_one_le (t : List ℕ) (ht : ∀ e ∈ t, 1 ≤ e) (A : ℕ) :
    tailWS t (fun _ => 1) A ≤ (Hstar A) ^ t.length := by
  induction t generalizing A with
  | nil =>
    simp [tailWS]
  | cons f fs ih =>
    simp only [List.length_cons]
    have hf : 1 ≤ f := ht f (by simp)
    have hfs : ∀ e ∈ fs, 1 ≤ e := fun e he => ht e (by simp [he])
    calc tailWS (f :: fs) (fun _ => 1) A
        = ∑ y ∈ Finset.Icc 1 A, ((y : ℝ≥0∞) ^ f)⁻¹ * tailWS fs (fun _ => 1) y :=
          rfl
      _ ≤ ∑ y ∈ Finset.Icc 1 A, ((y : ℝ≥0∞))⁻¹ * (Hstar A) ^ fs.length := by
          apply Finset.sum_le_sum
          intro y hy
          have hy1 : 1 ≤ y := (Finset.mem_Icc.mp hy).1
          have hyA : y ≤ A := (Finset.mem_Icc.mp hy).2
          have e1 : ((y : ℝ≥0∞) ^ f)⁻¹ ≤ ((y : ℝ≥0∞))⁻¹ :=
            pow_inv_le_one y f hy1 hf
          have e2 : tailWS fs (fun _ => 1) y ≤ (Hstar A) ^ fs.length :=
            (ih hfs y).trans (pow_le_pow_left₀ bot_le (Hstar_mono hyA) _)
          exact mul_le_mul e1 e2 bot_le bot_le
      _ = (Hstar A) ^ (fs.length + 1) := by
          rw [← Finset.sum_mul]
          have hH : (∑ y ∈ Finset.Icc 1 A, ((y : ℝ≥0∞))⁻¹) = Hstar A := rfl
          rw [hH, pow_succ']

private lemma zetaRS_ne_top_of (e : ℕ) (t : List ℕ) (he : 2 ≤ e)
    (ht : ∀ x ∈ t, 1 ≤ x) : zetaRS (e :: t) ≠ ⊤ := by
  have hle : ∀ x : ℕ, (if 0 < x then ((x : ℝ≥0∞) ^ e)⁻¹ * tailWS t (fun _ => 1) x
      else 0)
      ≤ (if 0 < x then (Hstar x) ^ t.length * (((x : ℝ≥0∞) ^ 2))⁻¹ else 0) := by
    intro x
    by_cases hx : 0 < x
    · rw [ite_eq_left hx, ite_eq_left hx]
      have hx1 : 1 ≤ x := hx
      have e1 : ((x : ℝ≥0∞) ^ e)⁻¹ ≤ ((x : ℝ≥0∞) ^ 2)⁻¹ := by
        have hxE1 : (1:ℝ≥0∞) ≤ ((x : ℝ≥0∞)) := by exact_mod_cast hx1
        have hpow : ((x : ℝ≥0∞)) ^ 2 ≤ ((x : ℝ≥0∞)) ^ e :=
          pow_le_pow_right₀ hxE1 he
        exact ENNReal.inv_le_inv.mpr hpow
      have e2 : tailWS t (fun _ => 1) x ≤ (Hstar x) ^ t.length :=
        tailWS_one_le t ht x
      calc ((x : ℝ≥0∞) ^ e)⁻¹ * tailWS t (fun _ => 1) x
          ≤ ((x : ℝ≥0∞) ^ 2)⁻¹ * (Hstar x) ^ t.length :=
            mul_le_mul e1 e2 bot_le bot_le
        _ = (Hstar x) ^ t.length * (((x : ℝ≥0∞) ^ 2))⁻¹ := mul_comm _ _
    · rw [ite_eq_right hx, ite_eq_right hx]
  have hZ := enn_harm_ne_top t.length
  unfold zetaRS topSumS
  exact ne_top_of_le_ne_top hZ (ENNReal.tsum_le_tsum hle)

private lemma harmStar_le_H (x y : ℕ) : harmStar x y ≤ Hstar x := by
  have e1 : harmStar x y
      = ∑ c ∈ (Finset.Icc 1 y).filter (· < x), ((((x - c : ℕ))) : ℝ≥0∞)⁻¹ := by
    unfold harmStar
    exact (Finset.sum_filter _ _).symm
  have hinj : ∀ a ∈ (Finset.Icc 1 y).filter (· < x),
      ∀ b ∈ (Finset.Icc 1 y).filter (· < x), (x - a) = (x - b) → a = b := by
    intro a ha b hb hab
    rw [Finset.mem_filter] at ha hb
    have ha1 : a ≤ x := le_of_lt ha.2
    have hb1 : b ≤ x := le_of_lt hb.2
    omega
  have e2 : (∑ c ∈ (Finset.Icc 1 y).filter (· < x), ((((x - c : ℕ))) : ℝ≥0∞)⁻¹)
      = ∑ r ∈ ((Finset.Icc 1 y).filter (· < x)).image (fun c => x - c),
        ((r : ℝ≥0∞))⁻¹ :=
    (Finset.sum_image (s := (Finset.Icc 1 y).filter (· < x)) (g := fun c => x - c)
      (f := fun r : ℕ => ((r : ℝ≥0∞))⁻¹) hinj).symm
  have hsub : ((Finset.Icc 1 y).filter (· < x)).image (fun c => x - c)
      ⊆ Finset.Icc 1 x := by
    intro r hr
    rw [Finset.mem_image] at hr
    obtain ⟨c, hc, rfl⟩ := hr
    rw [Finset.mem_filter, Finset.mem_Icc] at hc
    rw [Finset.mem_Icc]
    constructor <;> omega
  rw [e1, e2]
  unfold Hstar
  exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ => bot_le)

private lemma tailWS_harm_le (t : List ℕ) (ht : ∀ e ∈ t, 1 ≤ e) (x A : ℕ)
    (hAx : A ≤ x) : tailWS t (harmStar x) A ≤ (Hstar x) ^ (t.length + 1) := by
  induction t generalizing A with
  | nil =>
    simp only [tailWS, List.length]
    calc tailWS [] (harmStar x) A = harmStar x A := rfl
      _ ≤ Hstar x := harmStar_le_H x A
      _ = (Hstar x) ^ (0 + 1) := by rw [Nat.zero_add, pow_one]
  | cons f fs ih =>
    simp only [List.length_cons]
    have hf : 1 ≤ f := ht f (by simp)
    have hfs : ∀ e ∈ fs, 1 ≤ e := fun e he => ht e (by simp [he])
    calc tailWS (f :: fs) (harmStar x) A
        = ∑ y ∈ Finset.Icc 1 A, ((y : ℝ≥0∞) ^ f)⁻¹ * tailWS fs (harmStar x) y :=
          rfl
      _ ≤ ∑ y ∈ Finset.Icc 1 A, ((y : ℝ≥0∞))⁻¹ * (Hstar x) ^ (fs.length + 1) := by
          apply Finset.sum_le_sum
          intro y hy
          have hy1 : 1 ≤ y := (Finset.mem_Icc.mp hy).1
          have hyA : y ≤ A := (Finset.mem_Icc.mp hy).2
          have e1 : ((y : ℝ≥0∞) ^ f)⁻¹ ≤ ((y : ℝ≥0∞))⁻¹ :=
            pow_inv_le_one y f hy1 hf
          have e2 : tailWS fs (harmStar x) y ≤ (Hstar x) ^ (fs.length + 1) :=
            ih hfs y (le_trans hyA hAx)
          exact mul_le_mul e1 e2 bot_le bot_le
      _ ≤ (Hstar x) ^ (fs.length + 1 + 1) := by
          rw [← Finset.sum_mul]
          have hSeq : (∑ y ∈ Finset.Icc 1 A, ((y : ℝ≥0∞))⁻¹) = Hstar A := rfl
          calc (∑ y ∈ Finset.Icc 1 A, ((y : ℝ≥0∞))⁻¹) * (Hstar x) ^ (fs.length + 1)
              = (Hstar A) * (Hstar x) ^ (fs.length + 1) := by rw [hSeq]
            _ ≤ (Hstar x) * (Hstar x) ^ (fs.length + 1) :=
                mul_le_mul (Hstar_mono hAx) le_rfl bot_le bot_le
            _ = (Hstar x) ^ (fs.length + 1 + 1) := (pow_succ' _ _).symm

private lemma cycB_ne_top_of (L : ℕ) (rest : List ℕ) (hL : 2 ≤ L)
    (ht : ∀ x ∈ rest, 1 ≤ x) : cycB (L :: rest) ≠ ⊤ := by
  have hle : ∀ x : ℕ, (if 0 < x then ((x : ℝ≥0∞) ^ L)⁻¹ * tailWS rest (harmStar x) x
      else 0)
      ≤ (if 0 < x then (Hstar x) ^ (rest.length + 1) * (((x : ℝ≥0∞) ^ 2))⁻¹
        else 0) := by
    intro x
    by_cases hx : 0 < x
    · rw [ite_eq_left hx, ite_eq_left hx]
      have hx1 : 1 ≤ x := hx
      have e1 : ((x : ℝ≥0∞) ^ L)⁻¹ ≤ ((x : ℝ≥0∞) ^ 2)⁻¹ := by
        have hxE1 : (1:ℝ≥0∞) ≤ ((x : ℝ≥0∞)) := by exact_mod_cast hx1
        have hpow : ((x : ℝ≥0∞)) ^ 2 ≤ ((x : ℝ≥0∞)) ^ L :=
          pow_le_pow_right₀ hxE1 hL
        exact ENNReal.inv_le_inv.mpr hpow
      have e2 : tailWS rest (harmStar x) x ≤ (Hstar x) ^ (rest.length + 1) :=
        tailWS_harm_le rest ht x x le_rfl
      calc ((x : ℝ≥0∞) ^ L)⁻¹ * tailWS rest (harmStar x) x
          ≤ ((x : ℝ≥0∞) ^ 2)⁻¹ * (Hstar x) ^ (rest.length + 1) :=
            mul_le_mul e1 e2 bot_le bot_le
        _ = (Hstar x) ^ (rest.length + 1) * (((x : ℝ≥0∞) ^ 2))⁻¹ := mul_comm _ _
    · rw [ite_eq_right hx, ite_eq_right hx]
  have hZ := enn_harm_ne_top (rest.length + 1)
  unfold cycB topSumS
  exact ne_top_of_le_ne_top hZ (ENNReal.tsum_le_tsum hle)

private lemma zetaEStar_cons_eq_zetaRS (e : ℕ) (t : List ℕ) :
    zetaEStar (e :: t) = zetaRS (e :: t) := by
  unfold zetaEStar zetaRS topSumS
  refine (Equiv.tsum_eq (Fin.consEquiv (n := t.length) (fun _ => ℕ)) _).symm.trans ?_
  rw [ENNReal.tsum_prod']
  simp only [Fin.consEquiv_apply]
  have hcond : ∀ (x : ℕ) (n' : Fin t.length → ℕ),
      ((∀ a b : Fin (t.length + 1), a < b →
          Fin.cons (α := fun _ => ℕ) x n' b ≤ Fin.cons (α := fun _ => ℕ) x n' a)
        ∧ (∀ a, 0 < Fin.cons (α := fun _ => ℕ) x n' a))
      ↔ (0 < x) ∧
        ((∀ a b : Fin t.length, a < b → n' b ≤ n' a) ∧ (∀ a, 0 < n' a) ∧
          (∀ a, n' a ≤ x)) := by
    intro x n'
    rw [chain_cons_iff_weak, pos_cons_iff]
    constructor
    · intro h
      obtain ⟨⟨hc', hb'⟩, ⟨hx0, hp'⟩⟩ := h
      exact ⟨hx0, hc', hp', hb'⟩
    · intro h
      obtain ⟨hx0, hc', hp', hb'⟩ := h
      exact ⟨⟨hc', hb'⟩, hx0, hp'⟩
  have hpoint : ∀ x : ℕ, (∑' n' : Fin t.length → ℕ,
      (if (∀ a b : Fin (t.length + 1), a < b →
            Fin.cons (α := fun _ => ℕ) x n' b ≤ Fin.cons (α := fun _ => ℕ) x n' a)
          ∧ (∀ a, 0 < Fin.cons (α := fun _ => ℕ) x n' a)
        then ∏ a : Fin (t.length + 1),
          ((Fin.cons (α := fun _ => ℕ) x n' a : ℝ≥0∞) ^ (e :: t).get a)⁻¹ else 0))
      = (if 0 < x then ((x : ℝ≥0∞) ^ e)⁻¹ * tailWS t (fun _ => 1) x else 0) := by
    intro x
    by_cases hQ : 0 < x
    · rw [ite_eq_left hQ]
      trans ((x : ℝ≥0∞) ^ e)⁻¹ * ∑' n' : Fin t.length → ℕ,
        (if (∀ a b : Fin t.length, a < b → n' b ≤ n' a) ∧ (∀ a, 0 < n' a) ∧
          (∀ a, n' a ≤ x)
         then ∏ a', ((n' a' : ℝ≥0∞) ^ t.get a')⁻¹ else 0)
      · rw [← ENNReal.tsum_mul_left]
        apply tsum_congr
        intro n'
        simp only [hcond x n', and_iff_right hQ, prod_cons_split_star e t x n']
        split_ifs with hP
        · rfl
        · exact (mul_zero _).symm
      · rw [zetaEStar_bounded_eq_tailWS t x]
    · rw [ite_eq_right hQ]
      trans (∑' _ : Fin t.length → ℕ, (0 : ℝ≥0∞))
      · apply tsum_congr
        intro n'
        simp only [hcond x n']
        exact ite_eq_right (fun h => hQ h.1)
      · exact tsum_zero
  exact tsum_congr hpoint

/-! ## Step 5d: rotation bookkeeping and `B` finiteness -/

private lemma kl_len (l : ℕ) (k : Fin l → ℕ) : (List.ofFn k).length = l :=
  List.length_ofFn

private lemma kl_sum_eq (l : ℕ) (k : Fin l → ℕ) :
    (List.ofFn k).sum = ∑ j, k j := by
  have hlen : (List.ofFn k).length = l := List.length_ofFn
  have h1 : (List.ofFn k).take l = List.ofFn k :=
    List.take_of_length_le (by omega)
  rw [← h1, List.sum_take_ofFn]
  have hfil : (Finset.univ.filter (fun j : Fin l => j.val < l)) = Finset.univ :=
    Finset.filter_true_of_mem (fun j _ => j.2)
  rw [hfil]

private lemma rot_len (l : ℕ) (k : Fin l → ℕ) (j : Fin l) :
    ((List.ofFn k).rotate j.val).length = l := by
  rw [List.length_rotate, List.length_ofFn]

private lemma rot_sum (l : ℕ) (k : Fin l → ℕ) (j : Fin l) :
    ((List.ofFn k).rotate j.val).sum = (List.ofFn k).sum :=
  (List.rotate_perm _ _).sum_eq

/-- Indexing into a list tail. -/
private lemma tail_getElem (l : List ℕ) (m : ℕ) (h1 : m < l.tail.length)
    (h2 : m + 1 < l.length) : l.tail[m]'h1 = l[m + 1]'h2 := by
  cases l with
  | nil => simp at h1
  | cons a t => rfl

/-- Split off leading 1's (star version of the strict decomposition). -/
private lemma decomp_leading_onesS (l : List ℕ) :
    (∀ x ∈ l, 1 ≤ x) → (∃ x ∈ l, x ≠ 1) →
    ∃ p L s, l = List.replicate p 1 ++ L :: s ∧ 2 ≤ L ∧ (∀ x ∈ s, 1 ≤ x) := by
  induction l with
  | nil =>
    intro hpos hne
    obtain ⟨x, hx, _⟩ := hne
    simp at hx
  | cons h t ih =>
    intro hpos hne
    by_cases hh : h = 1
    · subst hh
      have hpos_t : ∀ x ∈ t, 1 ≤ x :=
        fun x hx => hpos x (List.mem_cons_of_mem _ hx)
      obtain ⟨x, hx, hx1⟩ := hne
      rw [List.mem_cons] at hx
      have hne_t : ∃ x ∈ t, x ≠ 1 := by
        rcases hx with rfl | hx
        · exact absurd rfl hx1
        · exact ⟨x, hx, hx1⟩
      obtain ⟨p, L, s, hl, hL, hs⟩ := ih hpos_t hne_t
      refine ⟨p + 1, L, s, ?_, hL, hs⟩
      rw [hl, List.replicate_succ, List.cons_append]
    · have h2 : 2 ≤ h := by
        have h1 := hpos h List.mem_cons_self
        omega
      exact ⟨0, h, t, rfl, h2,
        fun x hx => hpos x (List.mem_cons_of_mem _ hx)⟩

/-- `B` is finite on every rotation when some entry exceeds 1. -/
private lemma cycB_ne_top (e : List ℕ) (hpos : ∀ x ∈ e, 1 ≤ x)
    (hne1 : ∃ x ∈ e, x ≠ 1) : cycB e ≠ ⊤ := by
  obtain ⟨p, L, s, hl, hL, hs⟩ := decomp_leading_onesS e hpos hne1
  subst hl
  clear hpos hne1
  induction p generalizing s with
  | zero =>
    simp only [List.replicate_zero, List.nil_append]
    exact cycB_ne_top_of L s hL hs
  | succ p ih =>
    have hrep : List.replicate (p + 1) 1 ++ L :: s
        = 1 :: (List.replicate p 1 ++ L :: s) := by
      rw [List.replicate_succ, List.cons_append]
    rw [hrep]
    set R : List ℕ := List.replicate p 1 ++ L :: s with hR
    have hstep := split_add 1 (by omega : 1 ≤ 1) R
    have hIcc : Finset.Icc 1 (1 - 1) = ∅ := by decide
    rw [hIcc, Finset.sum_empty, zero_add] at hstep
    have hrot := rotate_add 1 (by omega : 1 ≤ 1) R
    rw [hrot] at hstep
    have hR1 : R ++ [1] = List.replicate p 1 ++ L :: (s ++ [1]) := by
      rw [hR, List.append_assoc, List.cons_append]
    rw [hR1] at hstep
    have hcast : ((1 - 1 : ℕ) : ℝ≥0∞) = 0 := by simp
    rw [hcast, zero_mul, zero_add] at hstep
    rw [hstep]
    apply ENNReal.add_ne_top.mpr
    refine ⟨?_, ?_⟩
    · exact ih _ (fun x hx => by
        rw [List.mem_append] at hx
        rcases hx with hx | hx
        · exact hs x hx
        · rw [List.mem_singleton] at hx
          subst hx
          exact le_rfl)
    · exact zetaRS_ne_top_of _ [] (by omega) (fun x hx => by simp at hx)

/-- One rotation step: `split_add` + `rotate_add` reassembled at `L * Z`. -/
private lemma rot_step (kl : List ℕ) (hpos : ∀ x ∈ kl, 1 ≤ x) (j : Fin kl.length) :
    (∑ i ∈ Finset.Icc 1 (kl.get j - 1),
      zetaRS ((kl.get j - i + 1) :: ((kl.rotate j.val).tail ++ [i])))
      + cycB (kl.rotate j.val)
    = (kl.get j : ℝ≥0∞) * zetaRS [kl.sum + 1] + cycB (kl.rotate (j.val + 1)) := by
  have hLpos : 1 ≤ kl.get j := hpos _ (List.get_mem kl j)
  have hLa : kl.rotate j.val = kl.get j :: (kl.rotate j.val).tail :=
    rotate_eq_get_cons_tail kl j
  have hLb : (kl.rotate j.val).tail ++ [kl.get j] = kl.rotate (j.val + 1) :=
    rotate_tail_append_get kl j
  have hsum : kl.get j + ((kl.rotate j.val).tail).sum = kl.sum := by
    have hperm : (kl.rotate j.val).sum = kl.sum := (List.rotate_perm _ _).sum_eq
    rw [hLa, List.sum_cons] at hperm
    exact hperm
  have h9 := split_add (kl.get j) hLpos ((kl.rotate j.val).tail)
  have h10 := rotate_add (kl.get j) hLpos ((kl.rotate j.val).tail)
  rw [hsum] at h9 h10
  have hsub : kl.get j - 1 + 1 = kl.get j := Nat.sub_add_cancel hLpos
  have hL_eq : (kl.get j : ℝ≥0∞) = ((kl.get j - 1 : ℕ) : ℝ≥0∞) + 1 := by
    conv_lhs => rw [← hsub]
    rw [Nat.cast_add, Nat.cast_one]
  have hmul : ((kl.get j - 1 : ℕ) : ℝ≥0∞) * zetaRS [kl.sum + 1]
      + zetaRS [kl.sum + 1]
      = (kl.get j : ℝ≥0∞) * zetaRS [kl.sum + 1] := by
    have hbase : (((kl.get j - 1 : ℕ) : ℝ≥0∞) + 1) * zetaRS [kl.sum + 1]
        = (kl.get j : ℝ≥0∞) * zetaRS [kl.sum + 1] := by rw [← hL_eq]
    calc ((kl.get j - 1 : ℕ) : ℝ≥0∞) * zetaRS [kl.sum + 1]
          + zetaRS [kl.sum + 1]
        = (((kl.get j - 1 : ℕ) : ℝ≥0∞) + 1) * zetaRS [kl.sum + 1] := by
          rw [add_mul, one_mul]
      _ = (kl.get j : ℝ≥0∞) * zetaRS [kl.sum + 1] := hbase
  calc (∑ i ∈ Finset.Icc 1 (kl.get j - 1),
        zetaRS ((kl.get j - i + 1) :: ((kl.rotate j.val).tail ++ [i])))
        + cycB (kl.rotate j.val)
      = (∑ i ∈ Finset.Icc 1 (kl.get j - 1),
        zetaRS ((kl.get j - i + 1) :: ((kl.rotate j.val).tail ++ [i])))
        + cycB (kl.get j :: (kl.rotate j.val).tail) := by rw [← hLa]
    _ = ((kl.get j - 1 : ℕ) : ℝ≥0∞) * zetaRS [kl.sum + 1]
        + topSumS 0 ((kl.rotate j.val).tail) (wWeightS (kl.get j)) := h9
    _ = ((kl.get j - 1 : ℕ) : ℝ≥0∞) * zetaRS [kl.sum + 1]
        + (cycB ((kl.rotate j.val).tail ++ [kl.get j])
          + zetaRS [kl.sum + 1]) := by rw [h10]
    _ = ((kl.get j : ℝ≥0∞) * zetaRS [kl.sum + 1])
        + cycB (kl.rotate (j.val + 1)) := by
          rw [← hLb, ← hmul]
          ac_rfl

/-- Summed `ℝ≥0∞` identity after cancelling the `B`-terms. -/
private lemma enn_sum_eq (kl : List ℕ) (hpos : ∀ x ∈ kl, 1 ≤ x)
    (hne : ∃ x ∈ kl, x ≠ 1) :
    ∑ j : Fin kl.length, ∑ i ∈ Finset.Icc 1 (kl.get j - 1),
      zetaRS ((kl.get j - i + 1) :: ((kl.rotate j.val).tail ++ [i]))
    = (kl.sum : ℝ≥0∞) * zetaRS [kl.sum + 1] := by
  have hstep : ∀ j : Fin kl.length,
      (∑ i ∈ Finset.Icc 1 (kl.get j - 1),
        zetaRS ((kl.get j - i + 1) :: ((kl.rotate j.val).tail ++ [i])))
        + cycB (kl.rotate j.val)
      = (kl.get j : ℝ≥0∞) * zetaRS [kl.sum + 1]
        + cycB (kl.rotate (j.val + 1)) :=
    fun j => rot_step kl hpos j
  have hsum : (∑ j : Fin kl.length, ∑ i ∈ Finset.Icc 1 (kl.get j - 1),
          zetaRS ((kl.get j - i + 1) :: ((kl.rotate j.val).tail ++ [i])))
        + ∑ j : Fin kl.length, cycB (kl.rotate j.val)
      = (∑ j : Fin kl.length, (kl.get j : ℝ≥0∞) * zetaRS [kl.sum + 1])
        + ∑ j : Fin kl.length, cycB (kl.rotate (j.val + 1)) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun j _ => hstep j)
  have hreidx : (∑ j : Fin kl.length, cycB (kl.rotate (j.val + 1)))
      = ∑ j : Fin kl.length, cycB (kl.rotate j.val) :=
    sum_rotate_succ kl (fun l => cycB l)
  have hSne : (∑ j : Fin kl.length, cycB (kl.rotate j.val)) ≠ ⊤ := by
    apply ENNReal.sum_ne_top.mpr
    intro j _
    apply cycB_ne_top
    · intro x hx
      rw [List.mem_rotate] at hx
      exact hpos x hx
    · obtain ⟨x, hx, hx1⟩ := hne
      exact ⟨x, List.mem_rotate.mpr hx, hx1⟩
  have hcancel : (∑ j : Fin kl.length, ∑ i ∈ Finset.Icc 1 (kl.get j - 1),
          zetaRS ((kl.get j - i + 1) :: ((kl.rotate j.val).tail ++ [i])))
      = ∑ j : Fin kl.length, (kl.get j : ℝ≥0∞) * zetaRS [kl.sum + 1] := by
    rw [hreidx] at hsum
    exact (ENNReal.add_left_inj hSne).mp hsum
  have hget_nat : ∑ j : Fin kl.length, kl.get j = kl.sum := by
    conv_rhs => rw [← List.ofFn_get kl]
    rw [List.sum_ofFn]
  have hget : ∑ j : Fin kl.length, (kl.get j : ℝ≥0∞)
      = (kl.sum : ℝ≥0∞) := by
    rw [← Nat.cast_sum, hget_nat]
  have hmul : (∑ j : Fin kl.length, (kl.get j : ℝ≥0∞) * zetaRS [kl.sum + 1])
      = (kl.sum : ℝ≥0∞) * zetaRS [kl.sum + 1] := by
    rw [← Finset.sum_mul, hget]
  rw [hcancel, hmul]

/-- Entries of the cyclic index as a cons-append list. -/
private lemma ofFn_entries_eq (l : ℕ) (hl : 0 < l) (k : Fin l → ℕ)
    (j : Fin l) (a i : ℕ) :
    List.ofFn (fun t : Fin (l + 1) =>
      if t.val = 0 then a
      else if t.val = l then i
      else k ⟨(j.val + t.val) % l, Nat.mod_lt _ hl⟩)
    = a :: (((List.ofFn k).rotate j.val).tail ++ [i]) := by
  have hkl : (List.ofFn k).length = l := List.length_ofFn
  have hrot : ((List.ofFn k).rotate j.val).length = l := by
    rw [List.length_rotate, hkl]
  have htail : ((List.ofFn k).rotate j.val).tail.length = l - 1 := by
    rw [List.length_tail, hrot]
  have hlenL : (List.ofFn (fun t : Fin (l + 1) =>
      if t.val = 0 then a
      else if t.val = l then i
      else k ⟨(j.val + t.val) % l, Nat.mod_lt _ hl⟩)).length = l + 1 :=
    List.length_ofFn
  have hlenR : (a :: (((List.ofFn k).rotate j.val).tail ++ [i])).length
      = l + 1 := by
    simp [htail]
    omega
  apply List.ext_getElem
  · rw [hlenL, hlenR]
  · intro n h1 h2
    have h1' : n < l + 1 := hlenL ▸ h1
    have h2' : n < l + 1 := hlenR ▸ h2
    have hLHS : (List.ofFn (fun t : Fin (l + 1) =>
        if t.val = 0 then a
        else if t.val = l then i
        else k ⟨(j.val + t.val) % l, Nat.mod_lt _ hl⟩))[n]'h1
        = (if n = 0 then a
          else if n = l then i
          else k ⟨(j.val + n) % l, Nat.mod_lt _ hl⟩) := by
      rw [List.getElem_ofFn]
    rw [hLHS]
    by_cases hn0 : n = 0
    · subst hn0
      simp
    · have hnPos : 0 < n := Nat.pos_of_ne_zero hn0
      have hRHS_succ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
      obtain ⟨m, rfl⟩ := hRHS_succ
      simp only [List.getElem_cons_succ]
      by_cases hml : m + 1 = l
      · have hmeq : m = l - 1 := by omega
        have hle : ((List.ofFn k).rotate j.val).tail.length ≤ m := by
          rw [htail]
          omega
        have hidx : m - (((List.ofFn k).rotate j.val).tail.length) = 0 := by
          rw [htail]
          omega
        simp only [List.getElem_append_right hle, hidx,
          List.getElem_singleton]
        have hif1 : ¬ (m + 1 = 0) := by omega
        have hif2 : m + 1 = l := hml
        rw [ite_eq_right hif1, ite_eq_left hif2]
      · have hm_lt : m < ((List.ofFn k).rotate j.val).tail.length := by
          rw [htail]
          omega
        simp only [List.getElem_append_left hm_lt]
        have hrot_mem : (((List.ofFn k).rotate j.val).tail[m]'hm_lt)
            = ((List.ofFn k).rotate j.val)[m + 1]'(by
              rw [hrot]
              omega) := by
          exact tail_getElem _ m hm_lt (by rw [hrot]; omega)
        rw [hrot_mem]
        have hrot_get : ((List.ofFn k).rotate j.val)[m + 1]'(by
              rw [hrot]
              omega)
            = k ⟨(j.val + (m + 1)) % l, Nat.mod_lt _ hl⟩ := by
          simp only [List.getElem_rotate, List.getElem_ofFn, hkl,
            add_comm (m + 1) j.val]
        rw [hrot_get]
        have hif1 : ¬ (m + 1 = 0) := by omega
        have hif2 : ¬ (m + 1 = l) := hml
        rw [ite_eq_right hif1, ite_eq_right hif2]

end StarCyclic

/--
**Cyclic sum formula for multiple zeta-star values.** Let $l \ge 1$ and let $k_0, \dots, k_{l-1}$
be positive integers, not all equal to $1$, with subscripts read modulo $l$, and put
$K = k_0 + \cdots + k_{l-1}$. Write $\zeta^\star$ for the multiple zeta-star value and $\zeta$ for
the strict multiple zeta value. Suppose that for each $0 \le j \le l - 1$ and each natural number
$i$ an index $\mathbf{c}_{j,i}$ is given that is admissible or empty, and that for
$1 \le i \le k_j - 1$ its entries are $(k_j - i + 1, k_{j+1}, \dots, k_{j+l-1}, i)$, the run
$k_{j+1}, \dots, k_{j+l-1}$ being empty when $l = 1$. Let $\mathbf{t}$ be an index, admissible
or empty, whose only entry is $K + 1$. Then
$$
\sum_{j=0}^{l-1} \sum_{i=1}^{k_j - 1} \zeta^\star(\mathbf{c}_{j,i}) = K \, \zeta(\mathbf{t}).
$$

Proves `Wanted` entry `cyclic_sum_formula_multiple_zeta_star_values`.

Source: S. Saito, T. Tanaka, and N. Wakabayashi, "Combinatorial Remarks on the Cyclic
Sum Formula for Multiple Zeta Values", Journal of Integer Sequences 14 (2011),
Article 11.2.4, Theorem `thm:CSF_MZSVs`, line 869,
<https://cs.uwaterloo.ca/journals/JIS/VOL14/Saito/saito22.tex>.
-/
theorem cyclic_sum_formula_multiple_zeta_star_values
    (l : ℕ) (hl : 0 < l)
    (k : Fin l → ℕ)
    (hk : ∀ j, 0 < k j)
    (hne : ∃ j, k j ≠ 1)
    (cyclicIndex : Fin l → ℕ → MultipleZeta.Index)
    (hcyclicEntries : ∀ j i, i ∈ Finset.Icc 1 (k j - 1) →
      (cyclicIndex j i).entries = List.ofFn (fun t : Fin (l + 1) =>
        if t.val = 0 then k j - i + 1
        else if t.val = l then i
        else k ⟨(j.val + t.val) % l, Nat.mod_lt _ hl⟩))
    (hcyclicAdmissible : ∀ j i, (cyclicIndex j i).IsAdmissibleOrEmpty)
    (totalIndex : MultipleZeta.Index)
    (htotalEntries : totalIndex.entries = [(∑ j : Fin l, k j) + 1])
    (htotalAdmissible : totalIndex.IsAdmissibleOrEmpty) :
    ∑ j : Fin l, ∑ i ∈ Finset.Icc 1 (k j - 1),
      MultipleZeta.starValue (cyclicIndex j i) (hcyclicAdmissible j i) =
      ((∑ j : Fin l, k j : ℕ) : ℝ) *
        MultipleZeta.strictValue totalIndex htotalAdmissible := by
  have hlen : (List.ofFn k).length = l := StarCyclic.kl_len l k
  have hsum_nat : (List.ofFn k).sum = ∑ j, k j := StarCyclic.kl_sum_eq l k
  have hpos : ∀ x ∈ List.ofFn k, 1 ≤ x := by
    intro x hx
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hx
    exact hk j
  have hne1 : ∃ x ∈ List.ofFn k, x ≠ 1 := by
    obtain ⟨j, hj⟩ := hne
    exact ⟨k j, List.mem_ofFn.mpr ⟨j, rfl⟩, hj⟩
  have hE := StarCyclic.enn_sum_eq (List.ofFn k) hpos hne1
  have hfinA : ∀ j' : Fin (List.ofFn k).length,
      ∀ i ∈ Finset.Icc 1 ((List.ofFn k).get j' - 1),
      StarCyclic.zetaRS
        (((List.ofFn k).get j' - i + 1)
          :: (((List.ofFn k).rotate j'.val).tail ++ [i]))
        ≠ ⊤ := by
    intro j' i hi
    have hi1 : 1 ≤ i := (Finset.mem_Icc.mp hi).1
    have hi2 : i ≤ (List.ofFn k).get j' - 1 := (Finset.mem_Icc.mp hi).2
    apply StarCyclic.zetaRS_ne_top_of
    · omega
    · intro x hx
      rw [List.mem_append] at hx
      rcases hx with hx | hx
      · have hxR : x ∈ (List.ofFn k).rotate j'.val :=
          List.mem_of_mem_tail hx
        rw [List.mem_rotate] at hxR
        exact hpos x hxR
      · rw [List.mem_singleton] at hx
        subst hx
        exact hi1
  have hsum_pos : 0 < (List.ofFn k).sum := by
    rw [hsum_nat]
    apply Finset.sum_pos (fun j _ => hk j)
    exact Finset.univ_nonempty_iff.mpr ⟨⟨0, hl⟩⟩
  have hfinZ : StarCyclic.zetaRS [(List.ofFn k).sum + 1] ≠ ⊤ := by
    apply StarCyclic.zetaRS_ne_top_of _ [] (by omega) (fun x hx => by simp at hx)
  have hneA : ∀ j' ∈ (Finset.univ : Finset (Fin (List.ofFn k).length)),
      (∑ i ∈ Finset.Icc 1 ((List.ofFn k).get j' - 1),
        StarCyclic.zetaRS
          (((List.ofFn k).get j' - i + 1)
            :: (((List.ofFn k).rotate j'.val).tail ++ [i])))
        ≠ ⊤ :=
    fun j' _ => ENNReal.sum_ne_top.mpr (fun i hi => hfinA j' i hi)
  have hcongr := congrArg ENNReal.toReal hE
  rw [ENNReal.toReal_sum hneA, ENNReal.toReal_mul,
    ENNReal.toReal_natCast] at hcongr
  have hinner : ∀ j' : Fin (List.ofFn k).length,
      (∑ i ∈ Finset.Icc 1 ((List.ofFn k).get j' - 1),
        StarCyclic.zetaRS
          (((List.ofFn k).get j' - i + 1)
            :: (((List.ofFn k).rotate j'.val).tail ++ [i]))).toReal
      = ∑ i ∈ Finset.Icc 1 ((List.ofFn k).get j' - 1),
        (StarCyclic.zetaRS
          (((List.ofFn k).get j' - i + 1)
            :: (((List.ofFn k).rotate j'.val).tail ++ [i]))).toReal :=
    fun j' => ENNReal.toReal_sum (fun i hi => hfinA j' i hi)
  simp only [hinner] at hcongr
  have hval : ∀ j' : Fin (List.ofFn k).length,
      ((finCongr hlen j').val = j'.val) := fun j' => rfl
  have hget_eq : ∀ j' : Fin (List.ofFn k).length,
      (List.ofFn k).get j' = k (finCongr hlen j') := by
    intro j'
    have h1 : (List.ofFn k).get j' = k ⟨j'.val, by omega⟩ := by
      rw [List.get_eq_getElem, List.getElem_ofFn]
    have h2 : finCongr hlen j' = ⟨j'.val, by omega⟩ :=
      Fin.val_injective rfl
    rw [h1, h2]
  have hsumm : ∀ j' : Fin (List.ofFn k).length,
      ∀ i ∈ Finset.Icc 1 ((List.ofFn k).get j' - 1),
      (StarCyclic.zetaRS
        (((List.ofFn k).get j' - i + 1)
          :: (((List.ofFn k).rotate j'.val).tail ++ [i]))).toReal
      = MultipleZeta.starValue (cyclicIndex (finCongr hlen j') i)
        (hcyclicAdmissible (finCongr hlen j') i) := by
    intro j' i hi
    have hj : k (finCongr hlen j') = (List.ofFn k).get j' :=
      (hget_eq j').symm
    have hi' : i ∈ Finset.Icc 1 (k (finCongr hlen j') - 1) := by
      rw [hj]
      exact hi
    have hentries := hcyclicEntries (finCongr hlen j') i hi'
    have hof := StarCyclic.ofFn_entries_eq l hl k (finCongr hlen j')
      (k (finCongr hlen j') - i + 1) i
    have hrot_eq : ((List.ofFn k).rotate (finCongr hlen j').val).tail
        = ((List.ofFn k).rotate j'.val).tail := by
      rw [hval j']
    rw [hof, hrot_eq, hj] at hentries
    have hposL : ∀ x ∈ (((List.ofFn k).get j' - i + 1)
        :: (((List.ofFn k).rotate j'.val).tail ++ [i])),
        0 < x := by
      intro x hx
      rw [List.mem_cons] at hx
      rcases hx with rfl | hx
      · have hi1 : 1 ≤ i := (Finset.mem_Icc.mp hi).1
        omega
      · rw [List.mem_append] at hx
        rcases hx with hx | hx
        · have hxR : x ∈ (List.ofFn k).rotate j'.val :=
            List.mem_of_mem_tail hx
          rw [List.mem_rotate] at hxR
          have h1 := hpos x hxR
          omega
        · rw [List.mem_singleton] at hx
          subst hx
          exact (Finset.mem_Icc.mp hi).1
    have hstar := StarCyclic.starValue_eq_zetaEStar_of_entries
      (cyclicIndex (finCongr hlen j') i)
      (((List.ofFn k).get j' - i + 1)
        :: (((List.ofFn k).rotate j'.val).tail ++ [i])) hentries
      hposL (hcyclicAdmissible (finCongr hlen j') i)
    have hcons := StarCyclic.zetaEStar_cons_eq_zetaRS
      ((List.ofFn k).get j' - i + 1)
      (((List.ofFn k).rotate j'.val).tail ++ [i])
    rw [hcons] at hstar
    exact hstar.symm
  have htotal : (StarCyclic.zetaRS [(List.ofFn k).sum + 1]).toReal
      = MultipleZeta.strictValue totalIndex htotalAdmissible := by
    have htot : totalIndex.entries = [(List.ofFn k).sum + 1] := by
      rw [htotalEntries, hsum_nat]
    have hposT : ∀ x ∈ [(List.ofFn k).sum + 1], 0 < x := by
      intro x hx
      rw [List.mem_singleton] at hx
      subst hx
      omega
    have hstrict := StarCyclic.strictValue_singleton_eq_zetaEStar_of_entries
      totalIndex ((List.ofFn k).sum + 1) htot hposT htotalAdmissible
    have hcons := StarCyclic.zetaEStar_cons_eq_zetaRS
      ((List.ofFn k).sum + 1) []
    rw [hcons] at hstrict
    exact hstrict.symm
  have hLHS_eq : (∑ j' : Fin (List.ofFn k).length,
        ∑ i ∈ Finset.Icc 1 ((List.ofFn k).get j' - 1),
        (StarCyclic.zetaRS
          (((List.ofFn k).get j' - i + 1)
            :: (((List.ofFn k).rotate j'.val).tail ++ [i]))).toReal)
      = ∑ j : Fin l, ∑ i ∈ Finset.Icc 1 (k j - 1),
        MultipleZeta.starValue (cyclicIndex j i)
          (hcyclicAdmissible j i) := by
    apply Fintype.sum_equiv (finCongr hlen)
    intro j'
    have hj := hget_eq j'
    have hIcc : Finset.Icc 1 ((List.ofFn k).get j' - 1)
        = Finset.Icc 1 (k (finCongr hlen j') - 1) := by rw [hj]
    rw [hIcc]
    apply Finset.sum_congr rfl
    intro i hi
    exact hsumm j' i (by rw [hj]; exact hi)
  have hRHS_eq : ((List.ofFn k).sum : ℝ)
      * (StarCyclic.zetaRS [(List.ofFn k).sum + 1]).toReal
      = ((∑ j : Fin l, k j : ℕ) : ℝ) *
        MultipleZeta.strictValue totalIndex htotalAdmissible := by
    rw [htotal, hsum_nat]
  rw [hLHS_eq, hRHS_eq] at hcongr
  exact hcongr

end MetaMathlibExt
end

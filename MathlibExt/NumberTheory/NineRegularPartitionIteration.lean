/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Combinatorics.Enumerative.Partition.Basic
public import Mathlib.Data.Int.ModEq
import Mathlib.Algebra.CharP.Algebra
import Mathlib.Combinatorics.Enumerative.Partition.Glaisher
import Mathlib.RingTheory.PowerSeries.Expand
import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
import Mathlib.Tactic.LinearCombination
import MathlibExt.Combinatorics.Enumerative.Partition.Counting
import MathlibExt.Combinatorics.Enumerative.Partition.ReciprocalEulerDissection

/-!
# Iterated congruences for 9-regular partitions

The eighth power of Euler's product gives the 9-regular partition counts modulo three.
Its odd coefficients give the recurrence iterated in `card_nine_regular_iterate_modEq`.
-/

namespace MetaMathlibExt

namespace card_nine_regular_iterate_modEq

open PowerSeries
open scoped PowerSeries.WithPiTopology Topology

local notation "𝔣" => qEulerProduct
local notation "σ" => rescale (-1 : ℤ)

private theorem eulerProduct_expand (k : ℕ) (hk : k ≠ 0) :
    𝔣 k = expand k hk (𝔣 1) := by
  have cont : Continuous (expand k hk : ℤ⟦X⟧ → ℤ⟦X⟧) := by
    rw [continuous_iff_continuousAt]
    intro F
    rw [ContinuousAt, WithPiTopology.tendsto_iff_coeff_tendsto]
    intro n
    by_cases hd : k ∣ n
    · simpa [coeff_expand, hd] using (WithPiTopology.continuous_coeff ℤ (n / k)).tendsto F
    · simp [coeff_expand, hd]
  have h := (WithPiTopology.hasProd_one_sub_X_pow ℤ).map (expand k hk) cont
  rw [qEulerProduct_one]
  simpa [qEulerProduct, Function.comp_def, pow_mul] using h.tprod_eq

private theorem multipliable_factors (e : ℕ → ℕ) (he : ∀ i, i < e i) :
    Multipliable (fun i ↦ (1 : ℤ⟦X⟧) - X ^ e i) := by
  simp_rw [sub_eq_add_neg]
  apply WithPiTopology.multipliable_one_add_of_tendsto_order_atTop_nhds_top
  apply ENat.tendsto_nhds_top_iff_natCast_lt.mpr
  intro n
  filter_upwards [Filter.eventually_ge_atTop n] with i hi
  rw [order_neg, order_X_pow, Nat.cast_lt]
  exact hi.trans_lt (he i)

private theorem hasProd_eulerProduct (k : ℕ) (hk : k ≠ 0) :
    HasProd (fun i : ℕ ↦ (1 : ℤ⟦X⟧) - X ^ (k * (i + 1))) (𝔣 k) :=
  (multipliable_factors _ fun i ↦
    (Nat.lt_succ_self i).trans_le (Nat.le_mul_of_pos_left _ (Nat.pos_of_ne_zero hk))).hasProd

private theorem rescale_even (k : ℕ) (hk : k ≠ 0) (he : Even k) : σ (𝔣 k) = 𝔣 k := by
  rw [eulerProduct_expand k hk]
  ext n
  rw [coeff_rescale, coeff_expand]
  split_ifs with h
  · rw [(he.trans_dvd h).neg_one_pow, one_mul]
  · simp

-- Pair the factors at X and -X. Odd exponents give a difference of squares,
-- while at an even exponent the two factors coincide.
private theorem reflected_product : 𝔣 1 * σ (𝔣 1) * 𝔣 4 = 𝔣 2 ^ 3 := by
  have cont : Continuous (σ : ℤ⟦X⟧ → ℤ⟦X⟧) := by
    rw [continuous_iff_continuousAt]
    intro F
    rw [ContinuousAt, WithPiTopology.tendsto_iff_coeff_tendsto]
    intro n
    simpa using ((WithPiTopology.continuous_coeff ℤ n).const_mul ((-1 : ℤ) ^ n)).tendsto F
  have h := hasProd_eulerProduct 1 one_ne_zero
  simp only [one_mul] at h
  have hg := h.map σ cont
  simp only [Function.comp_def, map_sub, map_one, map_pow, rescale_neg_one_X] at hg
  let H : ℤ⟦X⟧ := ∏' i : ℕ, (1 - X ^ (2 * (2 * i + 1)))
  have hH : HasProd (fun i : ℕ ↦ 1 - X ^ (2 * (2 * i + 1))) H :=
    (multipliable_factors (fun i ↦ 2 * (2 * i + 1)) (fun i ↦ by omega)).hasProd
  have he := hasProd_eulerProduct 2 two_ne_zero
  have hf := hasProd_eulerProduct 4 (by decide)
  have hsplit : H * 𝔣 4 = 𝔣 2 := by
    apply HasProd.unique _ he
    apply HasProd.even_mul_odd hH
    convert hf using 2 with i
    congr 2
    omega
  have hpair : H * 𝔣 2 ^ 2 = 𝔣 1 * σ (𝔣 1) := by
    apply HasProd.unique _ (h.mul hg)
    apply HasProd.even_mul_odd
    · convert hH using 2 with i
      rw [(show Odd (2 * i + 1) from ⟨i, rfl⟩).neg_pow]
      rw [mul_comm 2 (2 * i + 1), pow_mul]
      ring
    · convert he.pow 2 using 2 with i
      rw [show 2 * i + 1 + 1 = 2 * (i + 1) by omega, Even.neg_pow (even_two_mul _)]
      ring
  rw [← hpair, mul_right_comm, hsplit]
  ring

-- Subtract the reciprocal eighth-power dissection at X and at -X, after
-- clearing both denominators with the reflected product.
private theorem odd_part :
    𝔣 1 ^ 8 - σ (𝔣 1 ^ 8) = -(16 * (X * 𝔣 4 ^ 8)) := by
  have h := one_div_f1_pow_four_eight_twelve_two_dissection.2.1
  have hneg := congrArg σ h
  simp only [map_add, map_mul, map_pow, map_ofNat, rescale_neg_one_X,
    rescale_even 2 (by decide) (by decide), rescale_even 4 (by decide) (by decide),
    rescale_even 8 (by decide) (by decide)] at hneg
  have hne (k : ℕ) (hk : 1 ≤ k) : 𝔣 k ≠ 0 := fun hz ↦ by
    simpa [hz] using constantCoeff_qEulerProduct hk
  rw [map_pow]
  apply mul_left_cancel₀ (mul_ne_zero (pow_ne_zero 28 (hne 2 (by decide)))
    (pow_ne_zero 8 (hne 8 (by decide))))
  calc
    _ = -(16 * X * (𝔣 1 * σ (𝔣 1) * 𝔣 4) ^ 8 * 𝔣 2 ^ 4 * 𝔣 4 ^ 8 * 𝔣 8 ^ 8) := by
      linear_combination (norm := ring) 𝔣 1 ^ 8 * hneg - σ (𝔣 1) ^ 8 * h
    _ = _ := by rw [reflected_product]; ring

private theorem coeff_four_mul_add_one (n : ℕ) :
    coeff (4 * n + 1) (𝔣 1 ^ 8) = -8 * coeff n (𝔣 1 ^ 8) := by
  have h := congrArg (coeff (4 * n + 1)) odd_part
  have hodd : Odd (4 * n + 1) := ⟨2 * n, by omega⟩
  rw [map_sub, coeff_rescale, hodd.neg_one_pow, map_neg, coeff_ofNat_mul,
    coeff_succ_X_mul, eulerProduct_expand 4 (by decide), ← map_pow, coeff_expand_mul] at h
  linarith

private abbrev count (n : ℕ) := (Nat.Partition.restricted n (¬ 9 ∣ ·)).card

-- Glaisher's theorem permits each part to appear zero through eight times.
-- Modulo three the corresponding geometric sum is the eighth power of 1 - Xᵏ.
private theorem count_eq_coeff (n : ℕ) : (count n : ZMod 3) = (coeff n (𝔣 1 ^ 8) : ℤ) := by
  let : TopologicalSpace (ZMod 3) := ⊥
  have : DiscreteTopology (ZMod 3) := ⟨rfl⟩
  let φ := PowerSeries.map (Int.castRingHom (ZMod 3))
  have cont : Continuous (φ : ℤ⟦X⟧ → (ZMod 3)⟦X⟧) := by
    rw [continuous_iff_continuousAt]
    intro F
    rw [ContinuousAt, WithPiTopology.tendsto_iff_coeff_tendsto]
    intro k
    exact (continuous_of_discreteTopology (f := Int.castRingHom (ZMod 3))).continuousAt.comp
      ((WithPiTopology.continuous_coeff ℤ k).continuousAt)
  have h := ((hasProd_eulerProduct 1 one_ne_zero).pow 8).map φ cont
  simp only [φ, Function.comp_def, map_pow, map_sub, map_one, map_X, one_mul] at h
  have : CharP (ZMod 3)⟦X⟧ 3 := CharP.of_ringHom_of_ne_zero C 3 (by decide)
  have geom (i : ℕ) : ∑ j ∈ Finset.range 9, (X ^ (i + 1) : (ZMod 3)⟦X⟧) ^ j =
      (1 - X ^ (i + 1)) ^ 8 := by
    have hne : (1 : (ZMod 3)⟦X⟧) ≠ X ^ (i + 1) := fun e ↦ by
      simpa using congrArg constantCoeff e
    apply mul_right_cancel₀ (sub_ne_zero.mpr hne)
    rw [geom_sum_mul_neg, ← pow_succ]
    simpa using (sub_pow_expChar_pow (p := 3) (1 : (ZMod 3)⟦X⟧) (X ^ (i + 1)) 2).symm
  have hc := Nat.Partition.hasProd_powerSeriesMk_card_countRestricted (ZMod 3) (m := 9) (by decide)
  simp_rw [pow_mul, geom] at hc
  have eqn := congrArg (coeff n) (hc.unique h)
  unfold count
  rw [Nat.Partition.card_restricted_eq_card_countRestricted n (by decide : 0 < 9)]
  simpa [φ, ← map_pow] using eqn

private theorem step (n : ℕ) : (count (4 * n + 1) : ℤ) ≡ (count n : ℤ) [ZMOD 3] := by
  apply (ZMod.intCast_eq_intCast_iff _ _ 3).mp
  simp only [Int.cast_natCast, count_eq_coeff, coeff_four_mul_add_one, Int.cast_mul, Int.cast_neg,
    Int.cast_ofNat]
  rw [show -(8 : ZMod 3) = 1 by decide, one_mul]

private theorem iterate (r s : ℕ) :
    (count (r * 4 ^ s + (4 ^ (s + 1) - 1) / 3) : ℤ) ≡ (count (r + 1) : ℤ) [ZMOD 3] := by
  induction s with
  | zero => simp
  | succ s ih =>
    have hmod : 4 ^ (s + 1) % 3 = 1 := by
      rw [Nat.pow_mod]
      simp
    have hpos : 0 < 4 ^ (s + 1) := by positivity
    have hidx : r * 4 ^ (s + 1) + (4 ^ (s + 1 + 1) - 1) / 3 =
        4 * (r * 4 ^ s + (4 ^ (s + 1) - 1) / 3) + 1 := by
      rw [pow_succ 4 (s + 1)]
      have hm : r * 4 ^ (s + 1) = 4 * (r * 4 ^ s) := by rw [pow_succ]; ring
      omega
    rw [hidx]
    exact (step _).trans ih

private theorem small_counts : count 1 = 1 ∧ count 2 = 2 ∧ count 3 = 3 := by
  have all_parts {n : ℕ} (hn : n < 9) : count n = Fintype.card (Nat.Partition n) := by
    unfold count Nat.Partition.restricted
    rw [Finset.filter_true_of_mem, Finset.card_univ]
    intro p _ x hx hd
    exact (not_le_of_gt hn) ((Nat.le_of_dvd (p.parts_pos hx) hd).trans (p.le_of_mem_parts hx))
  have h₂ := Nat.Partition.mul_card_eq_sum 2
  simp [show Finset.Icc 1 2 = {1, 2} by decide] at h₂
  have c₂ : Fintype.card (Nat.Partition 2) = 2 := by omega
  have h₃ := Nat.Partition.mul_card_eq_sum 3
  simp [show Finset.Icc 1 3 = {1, 2, 3} by decide, c₂] at h₃
  rw [all_parts (by decide : 1 < 9), all_parts (by decide : 2 < 9), all_parts (by decide : 3 < 9)]
  exact ⟨Fintype.card_unique, c₂, by omega⟩

end card_nine_regular_iterate_modEq

open card_nine_regular_iterate_modEq in
/-- **Iterated congruences for 9-regular partitions modulo 3.** Let $R_9(m)$ denote the number of
partitions of $m$ in which no part is divisible by $9$, and let $N_s = (4^s - 1)/3$. For all
positive integers $r$ and $s$, $R_9((r - 1) 4^{s-1} + N_s) \equiv R_9(r) \pmod 3$,
$R_9(N_s) \equiv 1 \pmod 3$, $R_9(4^{s-1} + N_s) \equiv 2 \pmod 3$ and
$R_9(2 \cdot 4^{s-1} + N_s) \equiv 0 \pmod 3$.

Source: S. Sriram and A. David Christopher, *Congruences Relating Regular Partition Functions, a
Generalized Tau Function, and Partition Function Weighted Composition Sums*, INTEGERS 24 (2024),
Article A39, Corollary 5 (`integers-2024-A39-cor-5`). -/
public theorem card_nine_regular_iterate_modEq (r s : ℕ) (hr : 0 < r) (hs : 0 < s) :
    ((Nat.Partition.restricted ((r - 1) * 4 ^ (s - 1) + (4 ^ s - 1) / 3) (¬ 9 ∣ ·)).card : ℤ)
        ≡ ((Nat.Partition.restricted (r) (¬ 9 ∣ ·)).card : ℤ) [ZMOD 3] ∧
      ((Nat.Partition.restricted ((4 ^ s - 1) / 3) (¬ 9 ∣ ·)).card : ℤ) ≡ 1 [ZMOD 3] ∧
      ((Nat.Partition.restricted (4 ^ (s - 1) + (4 ^ s - 1) / 3) (¬ 9 ∣ ·)).card : ℤ)
          ≡ 2 [ZMOD 3] ∧
      ((Nat.Partition.restricted (2 * 4 ^ (s - 1) + (4 ^ s - 1) / 3) (¬ 9 ∣ ·)).card : ℤ)
          ≡ 0 [ZMOD 3] := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hr.ne'
  obtain ⟨s, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hs.ne'
  obtain ⟨h₁, h₂, h₃⟩ := small_counts
  refine ⟨by simpa using iterate r s, ?_, ?_, ?_⟩
  · simpa [h₁] using iterate 0 s
  · simpa [h₂] using iterate 1 s
  · simpa [h₃, Int.ModEq] using iterate 2 s

end MetaMathlibExt

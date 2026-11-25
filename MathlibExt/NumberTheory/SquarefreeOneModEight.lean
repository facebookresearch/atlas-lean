/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Squarefree
public import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.PSeries
import Mathlib.Data.Int.CardIntervalMod
import Mathlib.Data.Nat.Factorization.Root
import Mathlib.NumberTheory.ArithmeticFunction.Moebius

/-!
# Square-free integers congruent to one modulo eight

The relative density of this residue class among square-free integers is one sixth.
We apply Möbius inversion to square divisors and use that every odd square is one modulo eight.
-/

open Finset Filter Topology ArithmeticFunction

namespace MetaMathlibExt
namespace squarefree_one_mod_eight_relativeDensity

private def count (P : ℕ → Prop) [DecidablePred P] (X : ℕ) : ℕ :=
  ((Icc 1 X).filter P).card

private lemma count_le (P : ℕ → Prop) [DecidablePred P] (X : ℕ) : count P X ≤ X := by
  simpa [count, Nat.card_Icc] using (card_filter_le (Icc 1 X) P)

-- The square divisors of n are indexed by the divisors of its flooring square root.
private lemma squarefree_indicator {n X : ℕ} (hn : n ∈ Icc 1 X) :
    (if Squarefree n then (1 : ℝ) else 0) =
      ∑ d ∈ Icc 1 X, if d ^ 2 ∣ n then (moebius d : ℝ) else 0 := by
  obtain ⟨hn₀, hnX⟩ := mem_Icc.mp hn
  let r := Nat.floorRoot 2 n
  have hr : r ≠ 0 := Nat.floorRoot_ne_zero.mpr ⟨by decide, by omega⟩
  have hiff : Squarefree n ↔ r = 1 := by
    constructor
    · intro h
      exact Nat.isUnit_iff.mp (h r (by simpa [r, sq] using (Nat.floorRoot_pow_dvd (n := 2)
        (a := n))))
    · intro h d hd
      apply Nat.isUnit_iff.mpr
      have hd' : d ^ 2 ∣ n := by simpa [sq] using hd
      have hdr : d ∣ r := Nat.pow_dvd_iff_dvd_floorRoot.mp hd'
      exact Nat.dvd_one.mp (h ▸ hdr)
  have hs : (Icc 1 X).filter (fun d => d ^ 2 ∣ n) = r.divisors := by
    ext d
    simp only [mem_filter, mem_Icc, Nat.mem_divisors]
    constructor
    · exact fun h => ⟨Nat.pow_dvd_iff_dvd_floorRoot.mp h.2, hr⟩
    · rintro ⟨h, -⟩
      have hsq : d ^ 2 ∣ n := Nat.pow_dvd_iff_dvd_floorRoot.mpr h
      have hd : d ∣ n := (dvd_pow_self d two_ne_zero).trans hsq
      exact ⟨⟨Nat.pos_of_dvd_of_pos hd hn₀, (Nat.le_of_dvd hn₀ hd).trans hnX⟩, hsq⟩
  rw [← sum_filter, hs]
  simp only [hiff]
  rw [← ArithmeticFunction.one_apply]
  change (1 : ArithmeticFunction ℝ) r = ∑ i ∈ r.divisors, (moebius i : ℝ)
  rw [← coe_zeta_mul_coe_moebius, coe_zeta_mul_apply]
  rfl

-- Reindex multiples of q by their positive quotients.
private lemma count_multiples (P : ℕ → Prop) [DecidablePred P] (X q : ℕ) (hq : 0 < q) :
    count (fun n => P n ∧ q ∣ n) X = count (fun k => P (q * k)) (X / q) := by
  symm
  apply card_bij (fun k _ => q * k)
  · intro k hk
    obtain ⟨⟨hk₁, hk₂⟩, hkP⟩ := (mem_filter.mp hk).imp_left mem_Icc.mp
    exact mem_filter.mpr ⟨mem_Icc.mpr ⟨Nat.mul_pos hq hk₁,
      by simpa [mul_comm] using (Nat.le_div_iff_mul_le hq).mp hk₂⟩, hkP, dvd_mul_right _ _⟩
  · exact fun _ _ _ _ h => Nat.eq_of_mul_eq_mul_left hq h
  · intro n hn
    obtain ⟨⟨hn₁, hn₂⟩, hP, k, rfl⟩ := (mem_filter.mp hn).imp_left mem_Icc.mp
    refine ⟨k, mem_filter.mpr ⟨mem_Icc.mpr ⟨?_, ?_⟩, hP⟩, rfl⟩
    · by_contra! hk
      simp [show k = 0 by omega] at hn₁
    · exact (Nat.le_div_iff_mul_le hq).mpr (by simpa [mul_comm] using hn₂)

private noncomputable def oddWeight (d : ℕ) : ℝ :=
  if Odd d then (moebius d : ℝ) else 0

-- Both residue conditions vanish on multiples of four and are invariant under odd squares.
private lemma squarefree_count (P : ℕ → Prop) [DecidablePred P]
    (hP : ∀ d k, P (d ^ 2 * k) ↔ Odd d ∧ P k) (X : ℕ) :
    (count (fun n => Squarefree n ∧ P n) X : ℝ) =
      ∑ d ∈ Icc 1 X, oddWeight d * count P (X / d ^ 2) := by
  have hs : (Icc 1 X).filter (fun n => Squarefree n ∧ P n) =
      ((Icc 1 X).filter P).filter Squarefree := by
    ext n
    simp [and_assoc, and_left_comm, and_comm]
  unfold count at ⊢
  rw [hs, card_filter, Nat.cast_sum]
  simp only [Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  rw [sum_congr rfl (fun n hn => squarefree_indicator (mem_filter.mp hn).1), sum_comm]
  apply sum_congr rfl
  intro d hd
  have hd₀ := (mem_Icc.mp hd).1
  rw [← sum_filter, sum_const, nsmul_eq_mul, filter_filter]
  change (count (fun n => P n ∧ d ^ 2 ∣ n) X : ℝ) * _ = _
  rw [count_multiples P X (d ^ 2) (by positivity)]
  by_cases ho : Odd d
  · simp only [count, hP, ho, true_and, oddWeight, ite_true]
    exact mul_comm _ _
  · have hempty : count (fun k => P (d ^ 2 * k)) (X / d ^ 2) = 0 := by simp [count, hP, ho]
    simp [hempty, oddWeight, ho]

private lemma tendsto_div_count (q : ℕ) :
    Tendsto (fun X : ℕ => ((X / q : ℕ) : ℝ) / X) atTop (𝓝 (1 / (q : ℝ))) := by
  have h := (tendsto_nat_floor_mul_div_atTop (a := 1 / (q : ℝ)) (by positivity)).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))
  simpa only [Function.comp_def, one_div_mul_eq_div, Nat.floor_div_eq_div] using h

private lemma norm_oddWeight (d : ℕ) : ‖oddWeight d‖ ≤ 1 := by
  rw [Real.norm_eq_abs, oddWeight]
  split
  · exact_mod_cast (abs_moebius_le_one (n := d))
  · norm_num

private noncomputable def factor : ℝ := ∑' d : ℕ, oddWeight d / (d : ℝ) ^ 2

-- The first term is one. Beyond two, the reciprocal-square tail is at most two thirds.
private lemma factor_pos : 0 < factor := by
  have hb (d : ℕ) : ‖oddWeight d / (d : ℝ) ^ 2‖ ≤ 1 / (d : ℝ) ^ 2 := by
    rw [norm_div, Real.norm_of_nonneg (sq_nonneg _)]
    gcongr
    exact norm_oddWeight d
  have h := (Real.summable_one_div_nat_pow.mpr (by decide : 1 < 2)).of_norm_bounded hb
  suffices (1 / 3 : ℝ) ≤ factor by linarith
  apply ge_of_tendsto h.tendsto_sum_tsum_nat
  filter_upwards [eventually_ge_atTop 3] with N hN
  rw [← sum_range_add_sum_Ico _ hN]
  have hinit : ∑ d ∈ range 3, oddWeight d / (d : ℝ) ^ 2 = 1 := by
    norm_num [sum_range_succ, oddWeight, Nat.odd_iff, moebius_apply_one]
  rw [hinit]
  have htail := sum_Ioo_inv_sq_le (α := ℝ) 2 N
  have heq : Ioo 2 N = Ico 3 N := by ext d; simp; omega
  rw [heq] at htail
  have hle : (∑ d ∈ Ico 3 N, - (oddWeight d / (d : ℝ) ^ 2)) ≤
      ∑ d ∈ Ico 3 N, ((d : ℝ) ^ 2)⁻¹ := by
    apply sum_le_sum
    intro d _
    simpa only [one_div, Real.norm_eq_abs] using (neg_le_abs _).trans (hb d)
  rw [sum_neg_distrib] at hle
  linarith

-- Tannery's theorem passes the density limit through the sum over square divisors.
private lemma sifted_density (P : ℕ → Prop) [DecidablePred P] {a : ℝ}
    (hP : ∀ d k, P (d ^ 2 * k) ↔ Odd d ∧ P k)
    (ha : Tendsto (fun X : ℕ => (count P X : ℝ) / X) atTop (𝓝 a)) :
    Tendsto (fun X : ℕ => (count (fun n => Squarefree n ∧ P n) X : ℝ) / X)
      atTop (𝓝 (factor * a)) := by
  let f (X d : ℕ) : ℝ := oddWeight d * ((count P (X / d ^ 2) : ℝ) / X)
  have hlim (d : ℕ) : Tendsto (fun X => f X d) atTop (𝓝 (oddWeight d / (d : ℝ) ^ 2 * a)) := by
    rcases eq_or_ne d 0 with rfl | hd
    · simp [f, oddWeight, Nat.odd_iff]
    have hq := pow_ne_zero 2 hd
    have h := (ha.comp (Nat.tendsto_div_const_atTop hq)).mul (tendsto_div_count (d ^ 2))
    convert (h.const_mul (oddWeight d)).congr' ?_ using 1
    · congr 1
      push_cast
      ring
    filter_upwards [(Nat.tendsto_div_const_atTop hq).eventually (eventually_gt_atTop 0)]
      with X hX
    dsimp [f, Function.comp_def]
    have hn : ((X / d ^ 2 : ℕ) : ℝ) ≠ 0 := by exact_mod_cast hX.ne'
    field_simp
  have hbound (X d : ℕ) : ‖f X d‖ ≤ 1 / (d : ℝ) ^ 2 := by
    have hc : (count P (X / d ^ 2) : ℝ) ≤ (X : ℝ) / (d : ℝ) ^ 2 := calc
      _ ≤ ((X / d ^ 2 : ℕ) : ℝ) := by exact_mod_cast count_le P _
      _ ≤ (X : ℝ) / ((d ^ 2 : ℕ) : ℝ) := Nat.cast_div_le
      _ = _ := by rw [Nat.cast_pow]
    rcases eq_or_ne X 0 with rfl | hX
    · simp [f]
    have hX' : 0 < (X : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hX
    dsimp only [f]
    rw [norm_mul, Real.norm_of_nonneg (by positivity : 0 ≤ (count P (X / d ^ 2) : ℝ) / X)]
    calc
      _ ≤ 1 * ((count P (X / d ^ 2) : ℝ) / X) := by gcongr; exact norm_oddWeight d
      _ ≤ _ := by rw [one_mul, div_le_iff₀ hX', div_mul_eq_mul_div, one_mul]; exact hc
  have ht := tendsto_tsum_of_dominated_convergence
    (Real.summable_one_div_nat_pow.mpr (by decide : 1 < 2)) hlim (.of_forall hbound)
  rw [tsum_mul_right] at ht
  apply ht.congr
  intro X
  rw [tsum_eq_sum (s := Icc 1 X), squarefree_count P hP]
  · simp only [f, div_eq_mul_inv, sum_mul, mul_assoc]
  · intro d hd
    by_cases hd₀ : d = 0
    · simp [hd₀, f, oddWeight, Nat.odd_iff]
    have hlarge : X < d := by simpa [mem_Icc, Nat.one_le_iff_ne_zero, hd₀] using hd
    have hs : X < d ^ 2 := hlarge.trans_le (Nat.le_self_pow (by decide) _)
    simp [f, Nat.div_eq_of_lt hs, count]

private lemma one_mod_eight_density :
    Tendsto (fun X : ℕ => (count (fun n => n % 8 = 1) X : ℝ) / X) atTop (𝓝 (1 / 8)) := by
  have hc (X : ℕ) : count (fun n => n % 8 = 1) X =
      (X + 1) / 8 + if 1 < (X + 1) % 8 then 1 else 0 := by
    have hset : (Icc 1 X).filter (fun n => n % 8 = 1) =
        (range (X + 1)).filter (fun n => n ≡ 1 [MOD 8]) := by
      ext n
      rw [mem_filter, mem_filter, mem_Icc, mem_range]
      change (1 ≤ n ∧ n ≤ X) ∧ n % 8 = 1 ↔ n < X + 1 ∧ n % 8 = 1 % 8
      omega
    rw [count, hset, ← Nat.count_eq_card_filter_range, Nat.count_modEq_card]
    decide
  have hfloor := tendsto_div_count 8
  have hupper := hfloor.add tendsto_one_div_atTop_nhds_zero_nat
  norm_num at hfloor hupper
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le hfloor hupper
  · intro X
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg X)
    exact_mod_cast (show X / 8 ≤ count (fun n => n % 8 = 1) X by rw [hc]; split <;> omega)
  · intro X
    change _ ≤ ((X / 8 : ℕ) : ℝ) / X + _
    rw [← one_div (X : ℝ), ← add_div]
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg X)
    exact_mod_cast (show count (fun n => n % 8 = 1) X ≤ X / 8 + 1 by rw [hc]; split <;> omega)

private lemma four_not_dvd_density :
    Tendsto (fun X : ℕ => (count (fun n => ¬4 ∣ n) X : ℝ) / X) atTop (𝓝 (3 / 4)) := by
  have h := (tendsto_const_nhds (x := (1 : ℝ))).sub (tendsto_div_count 4)
  convert h.congr' ?_ using 1
  · norm_num
  filter_upwards [eventually_gt_atTop 0] with X hX
  have hc := card_filter_add_card_filter_not (s := Icc 1 X) (fun n => 4 ∣ n)
  have hI : Icc 1 X = Ioc 0 X := by ext; simp; omega
  rw [Nat.card_Icc, hI, Nat.Ioc_filter_dvd_card_eq_div] at hc
  simp only [Nat.add_one_sub_one, ← hI] at hc
  change X / 4 + count (fun n => ¬4 ∣ n) X = X at hc
  have hc' : ((X / 4 : ℕ) : ℝ) + count (fun n => ¬4 ∣ n) X = X := by exact_mod_cast hc
  field_simp
  linarith

private lemma odd_square_mod {d : ℕ} (hd : Odd d) : d ^ 2 ≡ 1 [MOD 8] := by
  have hd₀ : d ≠ 0 := by rintro rfl; simp at hd
  exact (Nat.modEq_of_dvd' (Nat.pow_pos (Nat.pos_of_ne_zero hd₀))
    (Nat.eight_dvd_sq_sub_one_of_odd hd)).symm

private lemma one_mod_eight_mul (d k : ℕ) : (d ^ 2 * k) % 8 = 1 ↔ Odd d ∧ k % 8 = 1 := by
  by_cases hd : Odd d
  · have heq := (odd_square_mod hd).mul_right k
    simp only [Nat.ModEq, one_mul] at heq
    simp [hd, heq]
  · have heven := Nat.not_odd_iff_even.mp hd
    have h4 : 4 ∣ d ^ 2 * k := dvd_mul_of_dvd_left
      (show 2 ^ 2 ∣ d ^ 2 from pow_dvd_pow_of_dvd heven.two_dvd 2) k
    simp only [hd, false_and, iff_false]
    omega

private lemma four_not_dvd_mul (d k : ℕ) : (¬4 ∣ d ^ 2 * k) ↔ Odd d ∧ ¬4 ∣ k := by
  by_cases hd : Odd d
  · have heq := ((odd_square_mod hd).of_dvd (by decide : 4 ∣ 8)).mul_right k
    simp only [one_mul, Nat.ModEq] at heq
    simp [Nat.dvd_iff_mod_eq_zero, heq, hd]
  · have heven := Nat.not_odd_iff_even.mp hd
    have h4 : 4 ∣ d ^ 2 * k := dvd_mul_of_dvd_left
      (show 2 ^ 2 ∣ d ^ 2 from pow_dvd_pow_of_dvd heven.two_dvd 2) k
    simp [hd, h4]

end squarefree_one_mod_eight_relativeDensity

open squarefree_one_mod_eight_relativeDensity

/-- **Relative density of square-free integers congruent to $1$ modulo $8$.** As $X \to \infty$
through the natural numbers, the number of square-free integers $t$ with $1 \le t \le X$ and
$t \equiv 1 \pmod 8$, divided by the number of square-free integers $t$ with $1 \le t \le X$,
tends to $1/6$.

Source: Satyabrat Sahoo and Shanta Laishram, *Generalized Fruit Diophantine Equation over
Number Fields*, INTEGERS 26 (2026), Article A21, Theorem 2 (`integers-2026-A21-thm-2`). -/
public theorem squarefree_one_mod_eight_relativeDensity :
    Tendsto (fun X : ℕ =>
        ((Finset.Icc 1 X).filter (fun t => Squarefree t ∧ t % 8 = 1)).card /
          (((Finset.Icc 1 X).filter Squarefree).card : ℝ))
      atTop (𝓝 (1 / 6)) := by
  have hnum := sifted_density _ one_mod_eight_mul one_mod_eight_density
  have hden := sifted_density _ four_not_dvd_mul four_not_dvd_density
  have heq (X : ℕ) : count (fun n => Squarefree n ∧ ¬4 ∣ n) X = count Squarefree X := by
    unfold count
    congr 1
    apply filter_congr
    intro n _
    exact and_iff_left_of_imp fun hn h4 => Nat.prime_two.not_isUnit (hn 2 h4)
  simp only [heq] at hden
  have h := hnum.div hden (mul_ne_zero factor_pos.ne' (by norm_num))
  convert h.congr' ?_ using 1
  · congr 1
    field_simp [factor_pos.ne']
    ring
  filter_upwards [eventually_gt_atTop 0] with X hX
  dsimp [count]
  field_simp

end MetaMathlibExt

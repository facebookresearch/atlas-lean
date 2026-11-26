/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.LurothConvergent
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Measure of Lüroth cylinders

The theorem `MetaMathlibExt.volume_lurothCylinder` gives the Lebesgue measure of the set of
points in `(0, 1]` with prescribed first `n` Lüroth digits as the product of the digit
weights.

Source: Dmitry Kleinbock and Yuqing Zhang, *Metrical Properties of Functions of
Consecutive Digits in Lüroth Series*, INTEGERS 24 (2024), Article A67.
-/

open MeasureTheory

namespace MetaMathlibExt

private abbrev unitInterval : Set ℝ := Set.Ioc (0 : ℝ) 1
private noncomputable abbrev μ : Measure ℝ := volume.restrict unitInterval

private theorem prob_univ : μ Set.univ = 1 := by
  simp [μ, unitInterval]

private def slope (n : ℕ) : ℝ := (n + 2) * (n + 1)

private def affine (n : ℕ) (x : ℝ) : ℝ := slope n * x - (n + 1)

private theorem digit_gt_one {y : ℝ} (hy : y ∈ Set.Ioc (0 : ℝ) 1) :
    1 < lurothDigit y := by
  unfold lurothDigit
  have h : 1 ≤ ⌊1 / y⌋₊ := by
    apply (Nat.one_le_floor_iff _).2
    rw [le_div_iff₀ hy.1]
    simpa using hy.2
  omega

private theorem branch_iff (n : ℕ) (x : ℝ) :
    affine n x ∈ unitInterval ↔ x ∈ unitInterval ∧ lurothDigit x = n + 2 := by
  let q : ℝ := n + 1
  have hq : 1 ≤ q := by simp [q]
  have hpos : 0 < q := by linarith
  have hsucc : 0 < q + 1 := by positivity
  have hlo : 0 < affine n x ↔ 1 < (q + 1) * x := by
    have : affine n x = q * ((q + 1) * x - 1) := by unfold affine slope q; ring
    rw [this, mul_pos_iff_of_pos_left hpos, sub_pos]
  have hhi : affine n x ≤ 1 ↔ q * x ≤ 1 := by
    have : affine n x - 1 = (q + 1) * (q * x - 1) := by unfold affine slope q; ring
    rw [← sub_nonpos, this, ← mul_zero (q + 1), mul_le_mul_iff_right₀ hsucc, sub_nonpos]
  rw [Set.mem_Ioc, hlo, hhi]
  have hd (hx : 0 < x) : lurothDigit x = n + 2 ↔ q * x ≤ 1 ∧ 1 < (q + 1) * x := by
    simp only [lurothDigit, Nat.succ.injEq, Nat.floor_eq_iff (by positivity : 0 ≤ 1 / x),
      Nat.cast_add, Nat.cast_one, le_div_iff₀ hx, div_lt_iff₀ hx, q]
  constructor
  · rintro ⟨hl, hu⟩
    have hx : 0 < x := pos_of_mul_pos_right (by linarith : 0 < (q + 1) * x) hsucc.le
    exact ⟨⟨hx, le_trans (le_mul_of_one_le_left hx.le hq) hu⟩, (hd hx).2 ⟨hu, hl⟩⟩
  · rintro ⟨hx, h⟩
    exact ((hd hx.1).1 h).symm

private theorem affine_eq_map {n : ℕ} {x : ℝ} (h : lurothDigit x = n + 2) :
    affine n x = lurothMap x := by
  simp [affine, slope, lurothMap, h]
  ring

private theorem volume_affine (n : ℕ) (t : Set ℝ) :
    volume (affine n ⁻¹' t) = ENNReal.ofReal (slope n)⁻¹ * volume t := by
  have hp : 0 < slope n := by unfold slope; positivity
  change volume ((slope n * ·) ⁻¹' ((· + -((n : ℝ) + 1)) ⁻¹' t)) = _
  rw [Real.volume_preimage_mul_left hp.ne', abs_of_pos (inv_pos.mpr hp),
    MeasureTheory.measure_preimage_add_right]

private noncomputable def weight (c : ℕ) : ENNReal :=
  ENNReal.ofReal (1 / ((c : ℝ) * ((c : ℝ) - 1)))

private theorem weight_eq_inv_slope (n : ℕ) :
    weight (n + 2) = ENNReal.ofReal (slope n)⁻¹ := by
  have hslope : slope n = ((n + 2 : ℕ) : ℝ) * (((n + 2 : ℕ) : ℝ) - 1) := by
    unfold slope
    push_cast
    ring
  unfold weight
  rw [hslope, inv_eq_one_div]

private theorem weight_small {c : ℕ} (hc : c < 2) : weight c = 0 := by
  have hc01 : c = 0 ∨ c = 1 := by omega
  rcases hc01 with rfl | rfl <;> simp [weight]

private theorem single_branch (c : ℕ) (t : Set ℝ) :
    μ ({x | lurothDigit x = c} ∩ lurothMap ⁻¹' t) = weight c * μ t := by
  by_cases hc : c < 2
  · rw [weight_small hc, zero_mul]
    have hempty : ({x | lurothDigit x = c} ∩ lurothMap ⁻¹' t) ∩ unitInterval = ∅ := by
      ext x
      simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_ofPred,
        Set.mem_empty_iff_false, iff_false]
      rintro ⟨⟨hdc, _⟩, hx⟩
      have hgt := digit_gt_one hx
      omega
    rw [Measure.restrict_apply' measurableSet_Ioc, hempty, measure_empty]
  · obtain ⟨n, rfl⟩ : ∃ n, c = n + 2 := ⟨c - 2, by omega⟩
    rw [weight_eq_inv_slope]
    have heq : ({x | lurothDigit x = n + 2} ∩ lurothMap ⁻¹' t) ∩ unitInterval =
        affine n ⁻¹' (t ∩ unitInterval) := by
      ext x
      simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_ofPred]
      constructor
      · rintro ⟨⟨hdc, htx⟩, hx⟩
        have haI : affine n x ∈ unitInterval := (branch_iff n x).mpr ⟨hx, hdc⟩
        have hat : affine n x ∈ t := by
          rw [affine_eq_map hdc]
          exact htx
        exact ⟨hat, haI⟩
      · rintro ⟨hat, haI⟩
        obtain ⟨hx, hdc⟩ := (branch_iff n x).mp haI
        have htx : lurothMap x ∈ t := by
          rw [← affine_eq_map hdc]
          exact hat
        exact ⟨⟨hdc, htx⟩, hx⟩
    rw [Measure.restrict_apply' measurableSet_Ioc, heq, volume_affine,
      Measure.restrict_apply' measurableSet_Ioc]

private theorem seq_zero (x : ℝ) : lurothDigitSeq x 0 = lurothDigit x := by
  simp [lurothDigitSeq]

private theorem seq_succ (x : ℝ) (i : ℕ) :
    lurothDigitSeq x (i + 1) = lurothDigitSeq (lurothMap x) i := by
  simp [lurothDigitSeq, Function.iterate_succ_apply]

private noncomputable def cyl (d : ℕ → ℕ) (n : ℕ) : Set ℝ :=
  ⋂ i ∈ Finset.range n, (fun x => lurothDigitSeq x i) ⁻¹' {d i}

private theorem cyl_measure (d : ℕ → ℕ) (n : ℕ) :
    μ (cyl d n) = ∏ i ∈ Finset.range n, weight (d i) := by
  induction n generalizing d with
  | zero =>
    have h : cyl d 0 = Set.univ := by
      simp [cyl]
    rw [h, prob_univ]
    simp
  | succ n ih =>
    let tail := cyl (fun i => d (i + 1)) n
    have heq : cyl d (n + 1) = {x | lurothDigit x = d 0} ∩ lurothMap ⁻¹' tail := by
      ext x
      simp only [cyl, tail, Set.mem_iInter, Set.mem_preimage, Set.mem_singleton_iff,
        Set.mem_inter_iff, Set.mem_ofPred, Finset.mem_range]
      constructor
      · intro h
        refine ⟨?_, fun i hi => ?_⟩
        · have h0 := h 0 (by omega)
          rwa [seq_zero] at h0
        · have hsucc := h (i + 1) (by omega)
          rwa [seq_succ] at hsucc
      · rintro ⟨h0, ht⟩ (_ | i) hi
        · simpa [seq_zero] using h0
        · have := ht i (by omega)
          simpa [seq_succ] using this
    rw [heq, single_branch, ih]
    rw [Finset.prod_range_succ', mul_comm]

/-- **Measure of Lüroth cylinders.** Write $d_k(x)$ for the $k$-th Lüroth digit of $x$. For every
$n \in \mathbb{N}$ and all natural numbers $c_1, \dots, c_n$, the set
$\{x \in (0, 1] : d_j(x) = c_j \text{ for } 1 \le j \le n\}$ has Lebesgue measure
$\prod_{j=1}^{n} \frac{1}{c_j (c_j - 1)}$, with the convention $1/0 = 0$; in particular both
sides vanish when some $c_j < 2$.

Source: Dmitry Kleinbock and Yuqing Zhang, *Metrical Properties of Functions of
Consecutive Digits in Lüroth Series*, INTEGERS 24 (2024), Article A67, Proposition 1,
(10) (`integers-2024-A67-prop-1`). -/
public theorem volume_lurothCylinder {n : ℕ} (c : Fin n → ℕ) :
    volume {x ∈ Set.Ioc (0 : ℝ) 1 | ∀ j : Fin n, lurothDigitSeq x j = c j} =
      ∏ j, ENNReal.ofReal (1 / ((c j : ℝ) * ((c j : ℝ) - 1))) := by
  let d : ℕ → ℕ := fun i => if h : i < n then c ⟨i, h⟩ else 0
  have hd : ∀ (i : ℕ) (h : i < n), d i = c ⟨i, h⟩ := fun i h => by simp [d, h]
  have hset : {x ∈ Set.Ioc (0 : ℝ) 1 | ∀ j : Fin n, lurothDigitSeq x j = c j} =
      cyl d n ∩ unitInterval := by
    ext x
    simp only [Set.mem_ofPred, Set.mem_inter_iff, cyl, unitInterval, Set.mem_iInter,
      Set.mem_preimage, Set.mem_singleton_iff, Finset.mem_range]
    constructor
    · rintro ⟨hxIoc, hx⟩
      refine ⟨fun i hi => ?_, hxIoc⟩
      have hji := hx ⟨i, hi⟩
      simpa [hd i hi] using hji
    · rintro ⟨hxCyl, hxIoc⟩
      refine ⟨hxIoc, fun j => ?_⟩
      have hval := hxCyl j.val j.isLt
      simpa [hd _ j.isLt] using hval
  have hprod : (∏ i ∈ Finset.range n, weight (d i)) = ∏ j, weight (c j) := by
    rw [← Fin.prod_univ_eq_prod_range (fun i => weight (d i)) n]
    apply Finset.prod_congr rfl
    intro j _
    congr 1
    exact hd _ j.isLt
  rw [hset, ← Measure.restrict_apply' measurableSet_Ioc, cyl_measure, hprod]
  rfl

end MetaMathlibExt

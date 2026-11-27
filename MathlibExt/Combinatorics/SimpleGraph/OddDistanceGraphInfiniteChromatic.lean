/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex

import Mathlib.Analysis.Fourier.FiniteAbelian.PontryaginDuality
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Odd distance graph has infinite chromatic number

This module proves Davies' odd distance theorem for arbitrary finite colorings of the plane.
-/

@[expose] public section

open scoped BigOperators

namespace MathlibExt.GraphTheory.OddDistanceGraphInfiniteChromaticWanted

/-! Source record `OPG-616`. Validated from hill-photon submission. -/

namespace ODGIC

/-!
# Clause inventory for [OPG-616]

- Object: `O`, graph on `ℝ²` (as `EuclideanSpace ℝ (Fin 2)`).
- Hypothesis: adjacency iff distance is an odd integer (odd `ℕ`
  suffices since distances are nonnegative).
- Question: `χ(O) = ∞` as `chromaticNumber = ⊤`.
-/

/-- **Odd distance graph.** The odd distance graph is the simple graph on the Euclidean plane
$\mathbb{R}^2$ in which two points $x$ and $y$ are adjacent when their Euclidean distance is an
odd integer. -/
noncomputable def OddDistanceGraph : SimpleGraph (EuclideanSpace ℝ (Fin 2)) where
  Adj x y := ∃ k : ℕ, Odd k ∧ dist x y = (k : ℝ)
  symm := ⟨by
    intro x y h
    obtain ⟨k, hk, hkk⟩ := h
    exact ⟨k, hk, by rw [dist_comm]; exact hkk⟩⟩
  loopless := ⟨by
    intro x h
    obtain ⟨k, hk, hkk⟩ := h
    rw [dist_self] at hkk
    have hk0 : k = 0 := by exact_mod_cast hkk.symm
    rw [hk0] at hk
    exact Nat.not_odd_zero hk⟩

/-- **Infinite chromatic number of the odd distance graph.** The proposition that the odd distance
graph on $\mathbb{R}^2$ has infinite chromatic number, that is, has no proper colouring with
finitely many colours. -/
def OddDistanceChromaticInfinite : Prop := OddDistanceGraph.chromaticNumber = ⊤

end ODGIC

-- Davies' directions are written with their powers of two factored out.
private def xOdd {m : ℕ} (i : Fin m) : ℤ :=
  2 ^ (2 * (i.val + 1)) - 1

private def yOdd {m : ℕ} (i : Fin m) : ℤ :=
  -1 - 2 ^ (m - i.val + 1)

private def direction {m : ℕ} (i : Fin m) : ℤ × ℤ :=
  (2 ^ (m - i.val) * xOdd i, 2 ^ (i.val + 1) * yOdd i)

private lemma xOdd_odd {m : ℕ} (i : Fin m) : Odd (xOdd i) := by
  unfold xOdd
  rw [show 2 * (i.val + 1) = (2 * i.val + 1) + 1 by omega, pow_succ]
  exact (even_two.mul_left _).sub_odd odd_one

private lemma yOdd_odd {m : ℕ} (i : Fin m) : Odd (yOdd i) := by
  unfold yOdd
  rw [pow_succ]
  exact odd_neg_one.sub_even (even_two.mul_left _)

private def det (u v : ℤ × ℤ) : ℤ :=
  u.1 * v.2 - v.1 * u.2

private def detOdd {m : ℕ} (i j : Fin m) : ℤ :=
  2 ^ (2 * (j.val - i.val)) * xOdd i * yOdd j - xOdd j * yOdd i

private lemma detOdd_odd {m : ℕ} {i j : Fin m} (h : i < j) : Odd (detOdd i j) := by
  have hij : i.val < j.val := h
  unfold detOdd
  rw [show 2 * (j.val - i.val) = (2 * (j.val - i.val) - 1) + 1 by omega, pow_succ]
  exact (((even_two.mul_left _).mul_right _).mul_right _).sub_odd
    ((xOdd_odd j).mul (yOdd_odd i))

private lemma det_direction {m : ℕ} {i j : Fin m} (h : i < j) :
    det (direction i) (direction j) = 2 ^ (m - j.val + i.val + 1) * detOdd i j := by
  have hij : i.val < j.val := h
  have hj := j.isLt
  unfold det detOdd direction
  dsimp only
  have h₁ : m - i.val + (j.val + 1) =
      (m - j.val + i.val + 1) + 2 * (j.val - i.val) := by omega
  have h₂ : m - j.val + (i.val + 1) = m - j.val + i.val + 1 := by omega
  calc
    _ = (2 : ℤ) ^ (m - i.val + (j.val + 1)) * xOdd i * yOdd j -
        2 ^ (m - j.val + (i.val + 1)) * xOdd j * yOdd i := by
      rw [pow_add, pow_add]
      ring
    _ = _ := by rw [h₁, h₂, pow_add]; ring

private lemma det_relation (u v w : ℤ × ℤ) :
    det v w • u + (-det u w) • v + det u v • w = 0 := by
  ext <;> simp [det] <;> ring

-- In the determinant relation, the middle coefficient is odd after division by the
-- common power of two. The two outer coefficients are even.
private lemma direction_relation {m : ℕ} {i j k : Fin m} (hij : i < j) (hjk : j < k) :
    ∃ a b c : ℤ, Even a ∧ Odd b ∧ Even c ∧
      a • direction i + b • direction j + c • direction k = 0 := by
  have hij' : i.val < j.val := hij
  have hjk' : j.val < k.val := hjk
  have hk := k.isLt
  let a : ℤ := 2 ^ (j.val - i.val) * detOdd j k
  let b : ℤ := -detOdd i k
  let c : ℤ := 2 ^ (k.val - j.val) * detOdd i j
  have ha : Even a := by
    dsimp [a]
    rw [show j.val - i.val = (j.val - i.val - 1) + 1 by omega, pow_succ]
    exact (even_two.mul_left _).mul_right _
  have hc : Even c := by
    dsimp [c]
    rw [show k.val - j.val = (k.val - j.val - 1) + 1 by omega, pow_succ]
    exact (even_two.mul_left _).mul_right _
  refine ⟨a, b, c, ha, (detOdd_odd (hij.trans hjk)).neg, hc, ?_⟩
  let p : ℤ := 2 ^ (m - k.val + i.val + 1)
  have hp : p ≠ 0 := by dsimp [p]; positivity
  have h := det_relation (direction i) (direction j) (direction k)
  rw [det_direction hij, det_direction hjk, det_direction (hij.trans hjk)] at h
  have he₁ : m - k.val + j.val + 1 = (m - k.val + i.val + 1) + (j.val - i.val) := by
    omega
  have he₂ : m - j.val + i.val + 1 = (m - k.val + i.val + 1) + (k.val - j.val) := by
    omega
  rw [he₁, he₂, pow_add (2 : ℤ) (m - k.val + i.val + 1) (j.val - i.val),
    pow_add (2 : ℤ) (m - k.val + i.val + 1) (k.val - j.val)] at h
  have h' : p • (a • direction i + b • direction j + c • direction k) = 0 := by
    simp only [smul_add, smul_smul, a, b, c, p, ← mul_assoc, mul_neg]
    exact h
  exact (smul_eq_zero.mp h').resolve_left hp

private lemma direction_not_three {m : ℕ} (χ : AddChar (ℤ × ℤ) ℂ)
    {i j k : Fin m} (hij : i < j) (hjk : j < k)
    (hi : χ (direction i) = -1) (hj : χ (direction j) = -1)
    (hk : χ (direction k) = -1) : False := by
  obtain ⟨a, b, c, ha, hb, hc, h⟩ := direction_relation hij hjk
  have hh := congrArg χ h
  simp only [AddChar.map_add_eq_mul, AddChar.map_zsmul_eq_zpow, AddChar.map_zero_eq_one,
    hi, hj, hk, ha.neg_one_zpow, hb.neg_one_zpow, hc.neg_one_zpow, one_mul, mul_one] at hh
  exact (by norm_num : (-1 : ℂ) ≠ 1) hh

private noncomputable def skew (m : ℕ) : ℝ := (2 ^ (m + 2) : ℝ)⁻¹

private noncomputable def latticePoint (m : ℕ) (u : ℤ × ℤ) : EuclideanSpace ℝ (Fin 2) :=
  !₂[(u.1 : ℝ) + skew m * (u.2 : ℝ), Real.sqrt (1 - skew m ^ 2) * (u.2 : ℝ)]

private lemma latticePoint_sub (m : ℕ) (u v : ℤ × ℤ) :
    latticePoint m (u - v) = latticePoint m u - latticePoint m v := by
  ext i
  fin_cases i <;> simp [latticePoint] <;> ring

private lemma latticePoint_zsmul (m : ℕ) (j : ℤ) (u : ℤ × ℤ) :
    latticePoint m (j • u) = (j : ℝ) • latticePoint m u := by
  ext i
  fin_cases i <;> simp [latticePoint, zsmul_eq_mul] <;> ring

private lemma norm_latticePoint_sq (m : ℕ) (u : ℤ × ℤ) :
    ‖latticePoint m u‖ ^ 2 = (u.1 : ℝ)^2 + (u.2 : ℝ)^2 +
      2 * skew m * (u.1 : ℝ) * (u.2 : ℝ) := by
  have h : skew m ≤ 1 := by
    unfold skew
    exact inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))
  have h' : 0 ≤ skew m := by unfold skew; positivity
  have hsq : 0 ≤ 1 - skew m ^ 2 := by nlinarith
  rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]
  simp only [latticePoint, Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [mul_pow, Real.sq_sqrt hsq]
  ring

private def oddLength {m : ℕ} (i : Fin m) : ℕ :=
  2 ^ (m + i.val + 2) + 2 ^ (m - i.val) + 1

private lemma oddLength_odd {m : ℕ} (i : Fin m) : Odd (oddLength i) := by
  have hi := i.isLt
  unfold oddLength
  rw [show m + i.val + 2 = (m + i.val + 1) + 1 by omega,
    show m - i.val = (m - i.val - 1) + 1 by omega, pow_succ, pow_succ]
  exact ((even_two.mul_left _).add (even_two.mul_left _)).add_one

private lemma norm_latticePoint_direction {m : ℕ} (i : Fin m) :
    ‖latticePoint m (direction i)‖ = (oddLength i : ℝ) := by
  have hi := i.isLt
  apply (sq_eq_sq₀ (norm_nonneg _) (by positivity)).mp
  rw [norm_latticePoint_sq]
  simp only [direction, xOdd, yOdd, oddLength, Int.cast_mul, Int.cast_sub, Int.cast_pow,
    Int.cast_ofNat, Int.cast_one, Int.cast_neg, Nat.cast_add, Nat.cast_pow, Nat.cast_ofNat,
    Nat.cast_one]
  let A : ℝ := 2 ^ (m - i.val)
  let B : ℝ := 2 ^ (i.val + 1)
  have hA : A ≠ 0 := by dsimp [A]; positivity
  have hB : B ≠ 0 := by dsimp [B]; positivity
  have h₁ : (2 : ℝ) ^ (2 * (i.val + 1)) = B ^ 2 := by
    rw [Nat.mul_comm, pow_mul]
  have h₂ : (2 : ℝ) ^ (m - i.val + 1) = 2 * A := by
    rw [pow_succ, mul_comm]
  have h₃ : (2 : ℝ) ^ (m + i.val + 2) = A * B ^ 2 := by
    rw [show m + i.val + 2 = (m - i.val) + 2 * (i.val + 1) by omega, pow_add, h₁]
  have h₄ : skew m = (2 * A * B)⁻¹ := by
    unfold skew
    congr 1
    rw [show m + 2 = (m - i.val) + (i.val + 1) + 1 by omega, pow_succ, pow_add]
    change A * B * 2 = 2 * A * B
    ring
  rw [h₁, h₂, h₃, h₄]
  change (A * (B ^ 2 - 1)) ^ 2 + (B * (-1 - 2 * A)) ^ 2 +
    2 * (2 * A * B)⁻¹ * (A * (B ^ 2 - 1)) * (B * (-1 - 2 * A)) =
      (A * B ^ 2 + A + 1) ^ 2
  field_simp
  ring

open Finset Filter
open scoped Topology

-- Averaging over pairs of even shifts gives a squared geometric sum multiplied by
-- the real part of the character at one odd shift.
private noncomputable def kernel (N : ℕ) (z : ℂ) : ℝ :=
  z.re * Complex.normSq (∑ j ∈ range N, (z ^ 2) ^ j)

private lemma kernel_ge_neg_sq {z : ℂ} (hz : ‖z‖ = 1) (N : ℕ) :
    -(N : ℝ)^2 ≤ kernel N z := by
  have hre : -1 ≤ z.re := by
    have hh := Complex.abs_re_le_norm z
    rw [hz, abs_le] at hh
    exact hh.1
  have hnorm : ‖∑ j ∈ range N, (z ^ 2) ^ j‖ ≤ N := by
    refine (norm_sum_le _ _).trans ?_
    simp [norm_pow, hz]
  rw [kernel, Complex.normSq_eq_norm_sq]
  have hsq := pow_le_pow_left₀ (norm_nonneg _) hnorm 2
  nlinarith [mul_nonneg (sub_nonneg.mpr hre) (sq_nonneg ‖∑ j ∈ range N, (z ^ 2) ^ j‖)]

private lemma kernel_ge_of_tendsto {z : ℕ → ℂ} {w : ℂ} {N : ℕ → ℕ}
    (hz : ∀ n, ‖z n‖ = 1) (hw : w ≠ -1) (hc : Tendsto z atTop (𝓝 w))
    (hN : Tendsto N atTop atTop) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, -ε * (N n : ℝ)^2 ≤ kernel (N n) (z n) := by
  by_cases h : w = 1
  · have hre : ∀ᶠ n in atTop, 0 < (z n).re := by
      have hh := Complex.continuous_re.continuousAt.tendsto.comp hc
      exact hh.eventually (lt_mem_nhds (by simp [h] : 0 < w.re))
    filter_upwards [hre] with n hn
    exact (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hε.le) (sq_nonneg _)).trans
      (mul_nonneg hn.le (Complex.normSq_nonneg _))
  have hsq : w ^ 2 ≠ 1 := sq_ne_one_iff.mpr ⟨h, hw⟩
  let δ := ‖w ^ 2 - 1‖ / 2
  have hδ : 0 < δ := half_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hsq))
  have hδlt : δ < ‖w ^ 2 - 1‖ := half_lt_self (norm_pos_iff.mpr (sub_ne_zero.mpr hsq))
  have hnorm : ∀ᶠ n in atTop, δ < ‖z n ^ 2 - 1‖ := by
    have hh : Continuous (fun v : ℂ ↦ ‖v ^ 2 - 1‖) := by fun_prop
    exact (hh.continuousAt.tendsto.comp hc).eventually (lt_mem_nhds hδlt)
  obtain ⟨B, hB⟩ := exists_nat_gt ((2 / δ)^2 / ε)
  filter_upwards [hnorm, hN.eventually_ge_atTop (B + 1)] with n hn hBn
  let S : ℂ := ∑ j ∈ range (N n), ((z n) ^ 2) ^ j
  have hgeom : ‖S‖ * ‖z n ^ 2 - 1‖ ≤ 2 := calc
    _ = ‖((z n) ^ 2) ^ (N n) - 1‖ := by
      rw [← norm_mul, geom_sum_mul]
    _ ≤ 2 := by
      calc
        _ ≤ ‖((z n) ^ 2) ^ (N n)‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
        _ = 2 := by simp [norm_pow, hz]; norm_num
  have hS : ‖S‖ ≤ 2 / δ :=
    (le_div_iff₀ hδ).mpr ((mul_le_mul_of_nonneg_left hn.le (norm_nonneg _)).trans hgeom)
  have hss := pow_le_pow_left₀ (norm_nonneg _) hS 2
  have hB' : (2 / δ)^2 < ε * (N n : ℝ) := by
    have hh := (div_lt_iff₀ hε).mp (hB.trans_le (Nat.cast_le.mpr (show B ≤ N n by omega)))
    linarith
  have hlarge : 1 ≤ (N n : ℝ) := by
    exact_mod_cast (show 1 ≤ N n by omega)
  have hBound : ‖S‖^2 ≤ ε * (N n : ℝ)^2 := by
    apply hss.trans
    apply hB'.le.trans
    gcongr
    exact le_self_pow₀ hlarge (by decide)
  have hre : -1 ≤ (z n).re := by
    have hh := Complex.abs_re_le_norm (z n)
    rw [hz, abs_le] at hh
    exact hh.1
  rw [kernel, Complex.normSq_eq_norm_sq]
  change -ε * (N n : ℝ)^2 ≤ (z n).re * ‖S‖^2
  nlinarith [mul_nonneg (sub_nonneg.mpr hre) (sq_nonneg ‖S‖)]

private noncomputable def phase (z : Circle × Circle) : AddChar (ℤ × ℤ) ℂ where
  toFun x := (z.1 : ℂ)^x.1 * (z.2 : ℂ)^x.2
  map_zero_eq_one' := by simp
  map_add_eq_mul' x y := by
    simp only [Prod.fst_add, Prod.snd_add, zpow_add₀ (Circle.coe_ne_zero _)]
    ring

private lemma phase_norm (z : Circle × Circle) (x : ℤ × ℤ) :
    ‖phase z x‖ = 1 := by
  change ‖(z.1 : ℂ)^x.1 * (z.2 : ℂ)^x.2‖ = 1
  simp [norm_zpow]

private lemma continuous_phase (x : ℤ × ℤ) : Continuous fun z : Circle × Circle ↦ phase z x := by
  change Continuous fun z : Circle × Circle ↦ ↑(z.1 ^ x.1) * (↑(z.2 ^ x.2) : ℂ)
  fun_prop

private lemma card_bad_phases {m : ℕ} (z : Circle × Circle) :
    ((univ : Finset (Fin m)).filter (fun i ↦ phase z (direction i) = -1)).card ≤ 2 := by
  classical
  by_contra! h
  obtain ⟨i, j, k, hi, hj, hk, hij, hik, hjk⟩ := two_lt_card_iff.mp h
  simp only [mem_filter, mem_univ, true_and] at hi hj hk
  by_cases h₁ : i < j
  · by_cases h₂ : j < k
    · exact direction_not_three _ h₁ h₂ hi hj hk
    · by_cases h₃ : i < k
      · exact direction_not_three _ h₃ (by omega) hi hk hj
      · exact direction_not_three _ (by omega) h₁ hk hi hj
  · by_cases h₂ : i < k
    · exact direction_not_three _ (by omega) h₂ hj hi hk
    · by_cases h₃ : j < k
      · exact direction_not_three _ h₃ (by omega) hj hk hi
      · exact direction_not_three _ (by omega) (by omega) hk hj hi

-- The only possible negative contributions in the limit come from phases equal to `-1`.
private lemma exists_kernel_sum_bound (m : ℕ) :
    ∃ N : ℕ, 0 < N ∧ ∀ z : Circle × Circle,
      -3 * (N : ℝ)^2 ≤ ∑ i : Fin m, kernel N (phase z (direction i)) := by
  classical
  by_contra! h
  choose z hz using fun n : ℕ ↦ h (n + 1) (by omega)
  obtain ⟨w, φ, hφ, hc⟩ := SeqCompactSpace.tendsto_subseq z
  let N (n : ℕ) := φ n + 1
  have hN : Tendsto N atTop atTop := tendsto_atTop_mono (fun n ↦ by simp [N]) hφ.tendsto_atTop
  let ε : ℝ := 1 / (m + 1)
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hεm : (m : ℝ) * ε ≤ 1 := by
    dsimp [ε]
    have hm : 0 < (m : ℝ) + 1 := by positivity
    rw [mul_one_div, div_le_iff₀ hm]
    linarith
  let bad : Finset (Fin m) := univ.filter (fun i ↦ phase w (direction i) = -1)
  have hbad : (bad.card : ℝ) ≤ 2 := by
    have hcard : bad.card ≤ 2 := card_bad_phases w
    exact_mod_cast hcard
  have hevent : ∀ᶠ n in atTop, ∀ i : Fin m, i ∉ bad →
      -ε * (N n : ℝ)^2 ≤ kernel (N n) (phase (z (φ n)) (direction i)) := by
    rw [Filter.eventually_all]
    intro i
    by_cases hi : i ∈ bad
    · exact Eventually.of_forall (fun _ h ↦ False.elim (h hi))
    · have hwi : phase w (direction i) ≠ -1 := by simpa [bad] using hi
      have hh := (continuous_phase (direction i)).continuousAt.tendsto.comp hc
      exact (kernel_ge_of_tendsto (fun _ ↦ phase_norm _ _) hwi hh hN hε).mono
        (fun _ h _ ↦ h)
  obtain ⟨n, hn⟩ := hevent.exists
  have hmain :
      (∑ i : Fin m, ((if i ∈ bad then -1 else 0) - ε) * (N n : ℝ)^2) ≤
        ∑ i : Fin m, kernel (N n) (phase (z (φ n)) (direction i)) := by
    refine sum_le_sum fun i _ ↦ ?_
    by_cases hi : i ∈ bad
    · refine le_trans ?_ (kernel_ge_neg_sq (phase_norm _ _) _)
      simp only [hi, ite_true]
      nlinarith [mul_nonneg hε.le (sq_nonneg (N n : ℝ))]
    · simpa [hi] using hn i hi
  have hsum : (∑ i : Fin m, if i ∈ bad then (-1 : ℝ) else 0) = -(bad.card : ℝ) := by
    rw [← sum_filter]
    simp
  simp only [← sum_mul, sum_sub_distrib, hsum, sum_const, card_univ, Fintype.card_fin,
    nsmul_eq_mul] at hmain
  have hge : -3 * (N n : ℝ)^2 ≤
      (-(bad.card : ℝ) - (m : ℝ) * ε) * (N n : ℝ)^2 :=
    mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg _)
  exact (not_lt_of_ge (hge.trans hmain)) (hz (φ n))

private def multiplier (i j : ℕ) : ℤ := 1 + 2 * ((i : ℤ) - j)

private lemma multiplier_odd (i j : ℕ) : Odd (multiplier i j) :=
  ⟨(i : ℤ) - j, by unfold multiplier; ring⟩

private lemma sum_shift_re {G : Type*} [AddCommGroup G] [Finite G]
    (χ : AddChar G ℂ) (d : G) (N : ℕ) :
    ∑ ij : Fin N × Fin N, (χ (multiplier ij.1.val ij.2.val • d)).re =
      kernel N (χ d) := by
  let f (i : Fin N) := (χ d ^ 2) ^ i.val
  have hf (i : Fin N) : f i = χ (((2 * i.val : ℕ) : ℤ) • d) := by
    rw [Nat.cast_smul_eq_nsmul, AddChar.map_nsmul_eq_pow, pow_mul]
  have hmul (i j : Fin N) :
      χ (multiplier i.val j.val • d) =
        χ d * f i * (starRingEnd ℂ) (f j) := by
    have h : multiplier i.val j.val = 1 + ((2 * i.val : ℕ) : ℤ) -
        ((2 * j.val : ℕ) : ℤ) := by simp [multiplier]; ring
    rw [h, sub_eq_add_neg]
    simp [add_zsmul, hf, AddChar.map_add_eq_mul, AddChar.map_neg_eq_inv,
      AddChar.inv_apply_eq_conj]
  have hsum : ∑ ij : Fin N × Fin N, χ (multiplier ij.1.val ij.2.val • d) =
      χ d * (↑(Complex.normSq (∑ j ∈ range N, (χ d ^ 2) ^ j)) : ℂ) := by
    simp only [Fintype.sum_prod_type, hmul, ← mul_sum, ← sum_mul, ← map_sum]
    rw [← Complex.mul_conj, ← Fin.sum_univ_eq_sum_range]
    unfold f
    ring
  calc
    _ = (∑ ij : Fin N × Fin N, χ (multiplier ij.1.val ij.2.val • d)).re := by
      rw [Complex.re_sum]
    _ = _ := by rw [hsum]; simp [kernel, Complex.mul_re]

private def reduceLattice (M : ℕ) : ℤ × ℤ →+ ZMod M × ZMod M :=
  (Int.castAddHom (ZMod M)).prodMap (Int.castAddHom (ZMod M))

private noncomputable def frequency {M : ℕ} [NeZero M]
    (χ : AddChar (ZMod M × ZMod M) ℂ) : Circle × Circle :=
  (⟨χ (1, 0), mem_sphere_zero_iff_norm.mpr (χ.norm_apply _)⟩,
   ⟨χ (0, 1), mem_sphere_zero_iff_norm.mpr (χ.norm_apply _)⟩)

private lemma phase_frequency {M : ℕ} [NeZero M]
    (χ : AddChar (ZMod M × ZMod M) ℂ) (x : ℤ × ℤ) :
    phase (frequency χ) x = χ (reduceLattice M x) := by
  have h : reduceLattice M x =
      x.1 • ((1, 0) : ZMod M × ZMod M) + x.2 • ((0, 1) : ZMod M × ZMod M) := by
    ext <;> simp [reduceLattice, zsmul_eq_mul]
  rw [h, AddChar.map_add_eq_mul, AddChar.map_zsmul_eq_zpow, AddChar.map_zsmul_eq_zpow]
  rfl

private lemma sum_shift_bound {m N M : ℕ} [NeZero M]
    (h : ∀ z : Circle × Circle,
      -3 * (N : ℝ)^2 ≤ ∑ i : Fin m, kernel N (phase z (direction i)))
    (χ : AddChar (ZMod M × ZMod M) ℂ) :
    - (3 * (N : ℝ)^2) ≤ ∑ i : Fin m × (Fin N × Fin N),
      (χ (reduceLattice M (multiplier i.2.1.val i.2.2.val • direction i.1))).re := by
  rw [← neg_mul, Fintype.sum_prod_type]
  refine (h (frequency χ)).trans_eq (sum_congr rfl fun i _ ↦ ?_)
  rw [phase_frequency, ← sum_shift_re χ (reduceLattice M (direction i))]
  refine sum_congr rfl fun ij _ ↦ ?_
  change (χ (multiplier ij.1.val ij.2.val • reduceLattice M (direction i))).re =
    (χ (reduceLattice M (multiplier ij.1.val ij.2.val • direction i))).re
  rw [(reduceLattice M).map_zsmul]

private noncomputable def mass {G : Type*} [AddCommGroup G]
    (s : Finset G) (χ : AddChar G ℂ) : ℝ :=
  Complex.normSq (∑ x ∈ s, χ x)

private lemma mass_nonneg {G : Type*} [AddCommGroup G]
    (s : Finset G) (χ : AddChar G ℂ) : 0 ≤ mass s χ :=
  Complex.normSq_nonneg _

private lemma mass_one {G : Type*} [AddCommGroup G] (s : Finset G) :
    mass s 1 = (s.card : ℝ)^2 := by
  simp [mass, Complex.normSq_eq_norm_sq]

-- Character orthogonality counts the pairs in the set separated by a given shift.
private lemma weighted_mass {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    (s : Finset G) (d : G) :
    ∑ χ : AddChar G ℂ, (χ d).re * mass s χ =
      ∑ x ∈ s, ∑ y ∈ s, if d + x = y then (Fintype.card G : ℝ) else 0 := by
  have h (χ : AddChar G ℂ) :
      (mass s χ : ℂ) = ∑ x ∈ s, ∑ y ∈ s, χ (x - y) := by
    rw [mass, ← Complex.mul_conj]
    simp only [map_sum, sum_mul, mul_sum]
    rw [sum_comm]
    simp only [sub_eq_add_neg, AddChar.map_add_eq_mul, AddChar.map_neg_eq_inv,
      AddChar.inv_apply_eq_conj]
  have hh :
      ∑ χ : AddChar G ℂ, χ d * (mass s χ : ℂ) =
        ∑ x ∈ s, ∑ y ∈ s, if d + x = y then (Fintype.card G : ℂ) else 0 := by
    simp only [h, mul_sum, ← AddChar.map_add_eq_mul]
    rw [sum_comm]
    refine sum_congr rfl fun x _ ↦ ?_
    rw [sum_comm]
    refine sum_congr rfl fun y _ ↦ ?_
    rw [AddChar.sum_apply_eq_ite, ← add_sub_assoc]
    simp only [sub_eq_zero]
  apply_fun Complex.re at hh
  simpa only [Complex.re_sum, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    mul_zero, sub_zero, apply_ite Complex.re, Complex.natCast_re, Complex.zero_re] using hh

private lemma sum_mass {G : Type*} [AddCommGroup G] [Fintype G]
    (s : Finset G) :
    ∑ χ : AddChar G ℂ, mass s χ = (Fintype.card G : ℝ) * s.card := by
  classical
  simpa [sum_ite_eq, mul_comm] using weighted_mass s 0

-- All the shifts have zero correlation. Bound the nontrivial terms from below
-- and keep the contribution of the trivial character.
private lemma spectral_bound {G D : Type*} [AddCommGroup G] [Fintype G]
    [Fintype D] (s : Finset G) (d : D → G) (a : ℝ)
    (hS : ∀ i x, x ∈ s → x + d i ∉ s)
    (hSpec : ∀ χ : AddChar G ℂ, -a ≤ ∑ i, (χ (d i)).re) :
    ((Fintype.card D : ℝ) + a) * (s.card : ℝ)^2 ≤ a * Fintype.card G * s.card := by
  classical
  let eigen (χ : AddChar G ℂ) : ℝ := ∑ i, (χ (d i)).re
  have hzero (i : D) : ∑ χ : AddChar G ℂ, (χ (d i)).re * mass s χ = 0 := by
    rw [weighted_mass]
    refine sum_eq_zero fun x hx ↦ sum_eq_zero fun y hy ↦ ?_
    have hne : d i + x ≠ y := fun he ↦ hS i x hx ((add_comm x (d i) ▸ he) ▸ hy)
    simp [hne]
  have htotal : ∑ χ : AddChar G ℂ, eigen χ * mass s χ = 0 := by
    simp_rw [eigen, sum_mul]
    rw [sum_comm]
    exact sum_eq_zero fun i _ ↦ hzero i
  have hpos (χ : AddChar G ℂ) : 0 ≤ (eigen χ + a) * mass s χ :=
    mul_nonneg (by dsimp [eigen]; linarith [hSpec χ]) (mass_nonneg s χ)
  have hmain := single_le_sum (fun χ (_ : χ ∈ (univ : Finset (AddChar G ℂ))) ↦ hpos χ)
    (mem_univ (1 : AddChar G ℂ))
  simp only [add_mul, sum_add_distrib, ← mul_sum, htotal, zero_add] at hmain
  have hone : eigen 1 = (Fintype.card D : ℝ) := by simp [eigen]
  simpa only [← add_mul, hone, mass_one, sum_mass, mul_assoc] using hmain

private def liftLattice {M : ℕ} (u : ZMod M × ZMod M) : ℤ × ℤ :=
  (u.1.val, u.2.val)

-- For points inside the box, the two representatives of a difference differ by
-- less than the modulus, so a modular edge lifts to an integer edge.
private lemma lift_shift_coord {B : ℕ} {x y : ZMod (2 * B)} {d : ℤ}
    (hx : x.val < B) (hy : y.val < B) (hd : d.natAbs ≤ B)
    (h : x + (d : ZMod (2 * B)) = y) (hB : 0 < B) :
    (y.val : ℤ) - (x.val : ℤ) = d := by
  have : NeZero (2 * B) := ⟨by omega⟩
  have hh : (d : ZMod (2 * B)) = (((y.val : ℤ) - (x.val : ℤ) : ℤ) : ZMod (2 * B)) := by
    simp only [Int.cast_sub, Int.cast_natCast, ZMod.natCast_zmod_val]
    exact eq_sub_of_add_eq' h
  have hdvd := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mp hh
  apply Int.eq_of_sub_eq_zero
  apply Int.eq_zero_of_dvd_of_natAbs_lt_natAbs hdvd
  omega

private lemma adj_of_lattice_shift {m : ℕ} (i : Fin m) (j : ℤ) (hj : Odd j)
    (u v : ℤ × ℤ) (h : v - u = j • direction i) :
    ODGIC.OddDistanceGraph.Adj (latticePoint m u) (latticePoint m v) := by
  refine ⟨j.natAbs * oddLength i, hj.natAbs.mul (oddLength_odd i), ?_⟩
  rw [dist_comm, dist_eq_norm, ← latticePoint_sub, h, latticePoint_zsmul, norm_smul,
    norm_latticePoint_direction]
  simp [Nat.cast_natAbs, Real.norm_eq_abs]

private lemma no_finite_coloring (r : ℕ) (color : ODGIC.OddDistanceGraph.Coloring (Fin r)) :
    False := by
  classical
  have : Nonempty (Fin r) := ⟨color 0⟩
  -- The box occupies one quarter of the quotient, and some color occupies at least
  -- a fraction `1 / r` of the box. The Fourier bound excludes that density.
  let m := 12 * r
  obtain ⟨N, hN, hk⟩ := exists_kernel_sum_bound m
  let D := Fin m × (Fin N × Fin N)
  let shift (i : D) : ℤ × ℤ := multiplier i.2.1.val i.2.2.val • direction i.1
  let bound (i : D) := max (shift i).1.natAbs (shift i).2.natAbs
  let B := univ.sup bound + 1
  have hB : 0 < B := Nat.succ_pos _
  let M := 2 * B
  have : NeZero M := ⟨by dsimp [M]; omega⟩
  let G := ZMod M × ZMod M
  let boxMap (x : Fin B × Fin B) : G := (x.1.val, x.2.val)
  have hval (x : Fin B) : (x.val : ZMod M).val = x.val :=
    ZMod.val_natCast_of_lt (by dsimp [M]; have := x.isLt; omega)
  have hInj : Function.Injective boxMap := by
    intro x y hxy
    have h₁ := congrArg (fun v : G ↦ v.1.val) hxy
    have h₂ := congrArg (fun v : G ↦ v.2.val) hxy
    exact Prod.ext (Fin.ext (by simpa [boxMap, hval] using h₁))
      (Fin.ext (by simpa [boxMap, hval] using h₂))
  let box : Finset G := univ.image boxMap
  have hcard : box.card = B ^ 2 := by
    simp [box, card_image_of_injective _ hInj, pow_two]
  have hbox (x : G) (hx : x ∈ box) : x.1.val < B ∧ x.2.val < B := by
    obtain ⟨y, _, rfl⟩ := mem_image.mp hx
    simpa only [boxMap, hval] using And.intro y.1.isLt y.2.isLt
  let c (x : G) := color (latticePoint m (liftLattice x))
  obtain ⟨k, _, hkmax⟩ := exists_max_image (univ : Finset (Fin r))
    (fun k ↦ (box.filter (fun x ↦ c x = k)).card) univ_nonempty
  let S := box.filter (fun x ↦ c x = k)
  have hS_card : B ^ 2 ≤ r * S.card := by
    rw [← hcard, card_eq_sum_card_fiberwise (f := c) (s := box) (t := univ)
      (fun _ _ ↦ mem_univ _)]
    exact (sum_le_sum hkmax).trans_eq (by simp [S])
  have hS_pos : 0 < S.card := by
    by_contra! h
    have hzero : S.card = 0 := by omega
    rw [hzero, mul_zero] at hS_card
    have : 0 < B ^ 2 := by positivity
    omega
  have hIndependent (i : D) (x : G) (hx : x ∈ S) :
      x + reduceLattice M (shift i) ∉ S := by
    let y := x + reduceLattice M (shift i)
    intro hy
    obtain ⟨hxbox, hxk⟩ := mem_filter.mp hx
    obtain ⟨hybox, hyk⟩ := mem_filter.mp hy
    have hbound : bound i ≤ B := (le_sup (f := bound) (mem_univ i)).trans (Nat.le_succ _)
    have he : liftLattice y - liftLattice x = shift i := by
      apply Prod.ext
      · exact lift_shift_coord (hbox x hxbox).1 (hbox y hybox).1
          ((le_max_left _ _).trans hbound) rfl hB
      · exact lift_shift_coord (hbox x hxbox).2 (hbox y hybox).2
          ((le_max_right _ _).trans hbound) rfl hB
    have hadj := adj_of_lattice_shift i.1 _ (multiplier_odd i.2.1.val i.2.2.val)
      (liftLattice x) (liftLattice y) he
    exact color.valid hadj (hxk.trans hyk.symm)
  have hspectral := spectral_bound S (fun i : D ↦ reduceLattice M (shift i))
    (3 * (N : ℝ)^2) hIndependent (sum_shift_bound hk)
  have hineq : ((m : ℝ) + 3) * (S.card : ℝ) ≤ 12 * (B : ℝ)^2 := by
    simp only [D, G, Fintype.card_prod, Fintype.card_fin, ZMod.card, M,
      Nat.cast_mul, Nat.cast_ofNat] at hspectral
    have hN' : 0 < (N : ℝ)^2 := by positivity
    have hs' : 0 < (S.card : ℝ) := by positivity
    apply (mul_le_mul_iff_left₀ (mul_pos hN' hs')).mp
    convert hspectral using 1 <;> ring
  have hS_card' : (B : ℝ)^2 ≤ (r : ℝ) * S.card := by exact_mod_cast hS_card
  have hm : (m : ℝ) = 12 * r := by simp [m]
  have hS_pos' : 0 < (S.card : ℝ) := by positivity
  rw [hm] at hineq
  nlinarith

/--
**Davies' odd distance theorem.** The odd distance graph on the Euclidean plane $\mathbb{R}^2$,
in which two points are adjacent when their distance is an odd integer, has infinite chromatic
number: it has no proper colouring with finitely many colours.

Davies proves (Theorem 1) that every finite colouring of the plane has a monochromatic pair of
points at odd integer distance.

Source: James Davies, Odd distances in colourings of
the plane, Geometric and Functional Analysis 34 (2024) 19-31, arXiv:2209.15598,
https://arxiv.org/abs/2209.15598. Moved from
`OpenConjectures/GraphTheory/OddDistanceGraphInfiniteChromatic`.
-/
public theorem OddDistanceChromaticInfinite_holds : ODGIC.OddDistanceChromaticInfinite := by
  change ODGIC.OddDistanceGraph.chromaticNumber = ⊤
  by_contra h
  obtain ⟨r, ⟨color⟩⟩ := SimpleGraph.chromaticNumber_ne_top_iff_exists.mp h
  exact no_finite_coloring r color

end MathlibExt.GraphTheory.OddDistanceGraphInfiniteChromaticWanted

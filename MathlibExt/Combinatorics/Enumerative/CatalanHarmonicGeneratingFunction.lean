/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Combinatorics.Enumerative.Catalan.Basic
public import Mathlib.NumberTheory.Harmonic.Defs
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.Module.ModuleTopology

@[expose] public section

section
open scoped BigOperators

namespace MetaMathlibExt

/-! # Generating function of Catalan numbers times harmonic numbers
-/

private noncomputable def harm (n : ℕ) : ℝ := ∑ k ∈ Finset.range n, (((k + 1 : ℕ) : ℝ)⁻¹)
private noncomputable def cbR (n : ℕ) : ℝ := (Nat.centralBinom n : ℝ)
private noncomputable def catR (n : ℕ) : ℝ := (catalan n : ℝ)

private lemma harm_le (n : ℕ) : harm n ≤ n := by
  unfold harm
  calc ∑ k ∈ Finset.range n, (((k + 1 : ℕ) : ℝ)⁻¹)
      ≤ ∑ _k ∈ Finset.range n, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro k _
        have h1 : (1 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by
          have : (1 : ℕ) ≤ k + 1 := Nat.le_add_left 1 k
          exact_mod_cast this
        exact inv_le_one_of_one_le₀ h1
    _ = n := by simp

private lemma harm_nonneg (n : ℕ) : 0 ≤ harm n := by
  unfold harm
  apply Finset.sum_nonneg
  intro k _
  positivity

private lemma harm_zero : harm 0 = 0 := by simp [harm]

private lemma harm_succ (n : ℕ) : harm (n + 1) = harm n + (((n + 1 : ℕ) : ℝ)⁻¹) := by
  simp [harm, Finset.sum_range_succ]

private lemma cbR_nonneg (n : ℕ) : 0 ≤ cbR n := by
  unfold cbR; exact_mod_cast Nat.centralBinom_pos n |>.le

private lemma cbR_le_four_pow (n : ℕ) : cbR n ≤ (4 : ℝ) ^ n := by
  unfold cbR; exact_mod_cast Nat.centralBinom_le_four_pow n

private lemma catalan_le_centralBinom (n : ℕ) : catalan n ≤ n.centralBinom := by
  rw [catalan_eq_centralBinom_div]; exact Nat.div_le_self _ _

private lemma catR_nonneg (n : ℕ) : 0 ≤ catR n := by
  unfold catR; positivity

private lemma catR_le_cbR (n : ℕ) : catR n ≤ cbR n := by
  unfold catR cbR; exact_mod_cast catalan_le_centralBinom n

private lemma catR_le_four_pow (n : ℕ) : catR n ≤ (4 : ℝ) ^ n :=
  le_trans (catR_le_cbR n) (cbR_le_four_pow n)

private lemma summable_q_pow {r : ℝ} (hr0 : 0 ≤ r) (hr1 : 4 * r < 1) :
    Summable (fun n : ℕ => (4 * r) ^ n) := by
  apply summable_geometric_of_norm_lt_one
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity : (0:ℝ) ≤ 4 * r)]
  linarith

private lemma summable_n_mul_q_pow {r : ℝ} (hr1 : 4 * r < 1) (hr0 : 0 ≤ r) :
    Summable (fun n : ℕ => (n : ℝ) * (4 * r) ^ n) := by
  have hq : ‖4 * r‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity : (0:ℝ) ≤ 4 * r)]
    linarith
  have h := summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 1 hq
  simp only [pow_one] at h
  exact h

private lemma summable_n2_mul_q_pow {r : ℝ} (hr1 : 4 * r < 1) (hr0 : 0 ≤ r) :
    Summable (fun n : ℕ => (n : ℝ) ^ 2 * (4 * r) ^ n) := by
  have hq : ‖4 * r‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity : (0:ℝ) ≤ 4 * r)]
    linarith
  exact summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 2 hq

private lemma summable_cb_pow {r y : ℝ} (hr0 : 0 ≤ r) (hr1 : 4 * r < 1) (hy : |y| ≤ r) :
    Summable (fun n : ℕ => cbR n * y ^ n) := by
  apply Summable.of_norm_bounded (g := fun n : ℕ => (4 * r) ^ n) (summable_q_pow hr0 hr1)
  intro n
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (cbR_nonneg n), abs_pow, mul_pow]
  exact mul_le_mul (cbR_le_four_pow n) (pow_le_pow_left₀ (abs_nonneg _) hy n)
    (pow_nonneg (abs_nonneg _) _) (by positivity)

private lemma summable_cat_pow {r y : ℝ} (hr0 : 0 ≤ r) (hr1 : 4 * r < 1) (hy : |y| ≤ r) :
    Summable (fun n : ℕ => catR n * y ^ n) := by
  apply Summable.of_norm_bounded (g := fun n : ℕ => (4 * r) ^ n) (summable_q_pow hr0 hr1)
  intro n
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (catR_nonneg n), abs_pow, mul_pow]
  exact mul_le_mul (catR_le_four_pow n) (pow_le_pow_left₀ (abs_nonneg _) hy n)
    (pow_nonneg (abs_nonneg _) _) (by positivity)

private lemma summable_cb_harm_pow {r y : ℝ} (hr0 : 0 ≤ r) (hr1 : 4 * r < 1) (hy : |y| ≤ r) :
    Summable (fun n : ℕ => cbR n * harm n * y ^ n) := by
  apply Summable.of_norm_bounded (g := fun n : ℕ => (n : ℝ) * (4 * r) ^ n)
    (summable_n_mul_q_pow hr1 hr0)
  intro n
  have hn : |harm n| ≤ (n : ℝ) := by
    rw [abs_of_nonneg (harm_nonneg n)]; exact harm_le n
  have hA : cbR n * |harm n| ≤ 4 ^ n * (n : ℝ) :=
    mul_le_mul (cbR_le_four_pow n) hn (abs_nonneg _) (by positivity)
  have hB : |y| ^ n ≤ r ^ n := pow_le_pow_left₀ (abs_nonneg _) hy n
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (cbR_nonneg n), abs_pow,
    mul_pow]
  calc cbR n * |harm n| * |y| ^ n ≤ (4 ^ n * ↑n) * r ^ n :=
        mul_le_mul hA hB (pow_nonneg (abs_nonneg _) _) (by positivity)
    _ = ↑n * (4 ^ n * r ^ n) := by ring

private lemma summable_cat_harm_pow_succ {r y : ℝ} (hr0 : 0 ≤ r) (hr1 : 4 * r < 1) (hy : |y| ≤ r) :
    Summable (fun n : ℕ => catR n * harm n * y ^ (n + 1)) := by
  apply Summable.of_norm_bounded (g := fun n : ℕ => r * ((n : ℝ) * (4 * r) ^ n))
    ((summable_n_mul_q_pow hr1 hr0).mul_left r)
  intro n
  have hn : |harm n| ≤ (n : ℝ) := by
    rw [abs_of_nonneg (harm_nonneg n)]; exact harm_le n
  have hA : catR n * |harm n| ≤ 4 ^ n * (n : ℝ) :=
    mul_le_mul (catR_le_four_pow n) hn (abs_nonneg _) (by positivity)
  have hB : |y| ^ n ≤ r ^ n := pow_le_pow_left₀ (abs_nonneg _) hy n
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (catR_nonneg n), abs_pow,
    pow_succ, mul_pow]
  calc catR n * |harm n| * (|y| ^ n * |y|)
      ≤ (4 ^ n * ↑n) * (r ^ n * r) :=
        mul_le_mul hA (mul_le_mul hB hy (abs_nonneg _) (by positivity))
          (by positivity) (by positivity)
    _ = r * (↑n * (4 ^ n * r ^ n)) := by ring

-- Series values
private noncomputable def Aval (y : ℝ) : ℝ := ∑' n : ℕ, cbR n * y ^ n
private noncomputable def Cval (y : ℝ) : ℝ := ∑' n : ℕ, catR n * y ^ n
private noncomputable def Bval (y : ℝ) : ℝ := ∑' n : ℕ, cbR n * harm n * y ^ n
private noncomputable def Fval (y : ℝ) : ℝ := ∑' n : ℕ, catR n * harm n * y ^ (n + 1)

-- Derivative term functions
private noncomputable def dA (n : ℕ) (z : ℝ) : ℝ := cbR n * ((n : ℝ) * z ^ (n - 1))
private noncomputable def dC (n : ℕ) (z : ℝ) : ℝ := catR n * ((n : ℝ) * z ^ (n - 1))
private noncomputable def dB (n : ℕ) (z : ℝ) : ℝ := cbR n * harm n * ((n : ℝ) * z ^ (n - 1))
private noncomputable def dF (n : ℕ) (z : ℝ) : ℝ := catR n * harm n * (((n : ℝ) + 1) * z ^ n)

private lemma term_deriv_A (n : ℕ) (z : ℝ) :
    HasDerivAt (fun y => cbR n * y ^ n) (dA n z) z := by
  unfold dA
  exact (hasDerivAt_pow n z).const_mul (cbR n)

private lemma term_deriv_C (n : ℕ) (z : ℝ) :
    HasDerivAt (fun y => catR n * y ^ n) (dC n z) z := by
  unfold dC
  exact (hasDerivAt_pow n z).const_mul (catR n)

private lemma term_deriv_B (n : ℕ) (z : ℝ) :
    HasDerivAt (fun y => cbR n * harm n * y ^ n) (dB n z) z := by
  unfold dB
  exact (hasDerivAt_pow n z).const_mul (cbR n * harm n)

private lemma term_deriv_F (n : ℕ) (z : ℝ) :
    HasDerivAt (fun y => catR n * harm n * y ^ (n + 1)) (dF n z) z := by
  unfold dF
  have h := (hasDerivAt_pow (n + 1) z).const_mul (catR n * harm n)
  rw [Nat.add_sub_cancel] at h
  push_cast at h
  exact h

/-- Midpoint radius facts for termwise differentiation at `y`. -/
private lemma mid_facts {y : ℝ} (hy : |y| < 1 / 4) :
    0 < (|y| + 1 / 4) / 2 ∧ 4 * ((|y| + 1 / 4) / 2) < 1 ∧
    y ∈ Set.Ioo (-((|y| + 1 / 4) / 2)) ((|y| + 1 / 4) / 2) ∧
    (0 : ℝ) ∈ Set.Ioo (-((|y| + 1 / 4) / 2)) ((|y| + 1 / 4) / 2) := by
  refine ⟨by linarith [abs_nonneg y], by linarith, ?_, ?_⟩
  · rw [Set.mem_Ioo]
    exact ⟨by linarith [neg_abs_le y, hy], by linarith [le_abs_self y, hy]⟩
  · rw [Set.mem_Ioo]
    constructor <;> linarith [abs_nonneg y]

private lemma dA_bound {r z : ℝ} (hrpos : 0 < r) (_hr1 : 4 * r < 1) (hzr : |z| ≤ r)
    (n : ℕ) : ‖dA n z‖ ≤ (r⁻¹ * ((n:ℝ) * (4*r)^n)) := by
  have hr0 : (0:ℝ) ≤ r := le_of_lt hrpos
  have e1 : ‖dA n z‖ = cbR n * (n:ℝ) * |z| ^ (n - 1) := by
    unfold dA
    rw [norm_mul, norm_mul, norm_pow, Real.norm_eq_abs, Real.norm_eq_abs,
      Real.norm_eq_abs, abs_of_nonneg (cbR_nonneg n),
        abs_of_nonneg (Nat.cast_nonneg n)]
    ring
  have hq : (4*r)^n = 4^n * r^n := mul_pow _ _ _
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [e1]; simp
  · rw [e1]
    have hle : |z|^(n-1) ≤ r^(n-1) := pow_le_pow_left₀ (abs_nonneg _) hzr _
    have hA : cbR n * (n:ℝ) ≤ 4^n * (n:ℝ) :=
      mul_le_mul_of_nonneg_right (cbR_le_four_pow n) (Nat.cast_nonneg _)
    calc cbR n * ↑n * |z| ^ (n - 1) ≤ (4^n * ↑n) * r^(n-1) :=
          mul_le_mul hA hle (pow_nonneg (abs_nonneg _) _) (by positivity)
      _ = r⁻¹ * (↑n * (4*r)^n) := by
          have hrne : r ≠ 0 := ne_of_gt hrpos
          have key : r ^ (n - 1) * r = r ^ n := by
            have h1 : n - 1 + 1 = n := by omega
            calc r ^ (n - 1) * r = r ^ (n - 1) * r ^ 1 := by rw [pow_one]
              _ = r ^ ((n - 1) + 1) := by rw [pow_add]
              _ = r ^ n := by rw [h1]
          rw [hq, inv_mul_eq_div, eq_div_iff hrne, ← key]
          ring

private lemma hasDerivAt_Aval {y : ℝ} (hy : |y| < 1 / 4) :
    HasDerivAt Aval (∑' n : ℕ, dA n y) y := by
  have ⟨hrpos, hr1, hymem, h0mem⟩ := mid_facts hy
  have hr0 : (0:ℝ) ≤ (|y| + 1/4)/2 := le_of_lt hrpos
  set r := (|y| + 1 / 4) / 2 with hrdef
  have hopen : IsOpen (Set.Ioo (-r) r) := isOpen_Ioo
  have hconn : IsPreconnected (Set.Ioo (-r) r) := (convex_Ioo _ _).isPreconnected
  have hbase : Summable (fun n : ℕ => cbR n * (0:ℝ) ^ n) :=
    summable_cb_pow hr0 hr1 (by simp [hr0])
  have hbound : ∀ n : ℕ, ∀ z ∈ Set.Ioo (-r) r, ‖dA n z‖ ≤ (r⁻¹ * ((n:ℝ) * (4*r)^n)) :=
    fun n z hz => dA_bound hrpos hr1 (le_of_lt (abs_lt.mpr (Set.mem_Ioo.mp hz))) n
  have hderiv : ∀ n : ℕ, ∀ z ∈ Set.Ioo (-r) r,
      HasDerivAt (fun y => cbR n * y ^ n) (dA n z) z :=
    fun n z _ => term_deriv_A n z
  have hU : Summable (fun n : ℕ => r⁻¹ * ((n:ℝ) * (4*r)^n)) :=
    (summable_n_mul_q_pow hr1 hr0).mul_left r⁻¹
  have h := hasDerivAt_tsum_of_isPreconnected (u := fun n : ℕ => r⁻¹ * ((n:ℝ) * (4*r)^n))
    hU hopen hconn hderiv hbound h0mem hbase hymem
  unfold Aval
  exact h

private lemma summable_dA {y : ℝ} (hy : |y| < 1 / 4) : Summable (fun n : ℕ => dA n y) := by
  have ⟨hrpos, hr1, hymem, _⟩ := mid_facts hy
  have hr0 : (0:ℝ) ≤ (|y| + 1/4)/2 := le_of_lt hrpos
  set r := (|y| + 1 / 4) / 2 with hrdef
  have hyr : |y| ≤ r := le_of_lt (abs_lt.mpr (Set.mem_Ioo.mp hymem))
  apply Summable.of_norm_bounded
    (g := fun n : ℕ => r⁻¹ * ((n:ℝ) * (4*r)^n))
    ((summable_n_mul_q_pow hr1 hr0).mul_left r⁻¹)
  intro n
  exact dA_bound hrpos hr1 hyr n

private lemma dC_bound {r z : ℝ} (hrpos : 0 < r) (_hr1 : 4 * r < 1) (hzr : |z| ≤ r)
    (n : ℕ) : ‖dC n z‖ ≤ (r⁻¹ * ((n:ℝ) * (4*r)^n)) := by
  have hr0 : (0:ℝ) ≤ r := le_of_lt hrpos
  have e1 : ‖dC n z‖ = catR n * (n:ℝ) * |z| ^ (n - 1) := by
    unfold dC
    rw [norm_mul, norm_mul, norm_pow, Real.norm_eq_abs, Real.norm_eq_abs,
      Real.norm_eq_abs, abs_of_nonneg (catR_nonneg n),
      abs_of_nonneg (Nat.cast_nonneg n)]
    ring
  have hq : (4*r)^n = 4^n * r^n := mul_pow _ _ _
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [e1]; simp
  · rw [e1]
    have hle : |z|^(n-1) ≤ r^(n-1) := pow_le_pow_left₀ (abs_nonneg _) hzr _
    have hA : catR n * (n:ℝ) ≤ 4^n * (n:ℝ) :=
      mul_le_mul_of_nonneg_right (catR_le_four_pow n) (Nat.cast_nonneg _)
    calc catR n * ↑n * |z| ^ (n - 1) ≤ (4^n * ↑n) * r^(n-1) :=
          mul_le_mul hA hle (pow_nonneg (abs_nonneg _) _) (by positivity)
      _ = r⁻¹ * (↑n * (4*r)^n) := by
          have hrne : r ≠ 0 := ne_of_gt hrpos
          have key : r ^ (n - 1) * r = r ^ n := by
            have h1 : n - 1 + 1 = n := by omega
            calc r ^ (n - 1) * r = r ^ (n - 1) * r ^ 1 := by rw [pow_one]
              _ = r ^ ((n - 1) + 1) := by rw [pow_add]
              _ = r ^ n := by rw [h1]
          rw [hq, inv_mul_eq_div, eq_div_iff hrne, ← key]
          ring

private lemma hasDerivAt_Cval {y : ℝ} (hy : |y| < 1 / 4) :
    HasDerivAt Cval (∑' n : ℕ, dC n y) y := by
  have ⟨hrpos, hr1, hymem, h0mem⟩ := mid_facts hy
  have hr0 : (0:ℝ) ≤ (|y| + 1/4)/2 := le_of_lt hrpos
  set r := (|y| + 1 / 4) / 2 with hrdef
  have hopen : IsOpen (Set.Ioo (-r) r) := isOpen_Ioo
  have hconn : IsPreconnected (Set.Ioo (-r) r) := (convex_Ioo _ _).isPreconnected
  have hbase : Summable (fun n : ℕ => catR n * (0:ℝ) ^ n) :=
    summable_cat_pow hr0 hr1 (by simp [hr0])
  have hbound : ∀ n : ℕ, ∀ z ∈ Set.Ioo (-r) r, ‖dC n z‖ ≤ (r⁻¹ * ((n:ℝ) * (4*r)^n)) :=
    fun n z hz => dC_bound hrpos hr1 (le_of_lt (abs_lt.mpr (Set.mem_Ioo.mp hz))) n
  have hderiv : ∀ n : ℕ, ∀ z ∈ Set.Ioo (-r) r,
      HasDerivAt (fun y => catR n * y ^ n) (dC n z) z :=
    fun n z _ => term_deriv_C n z
  have hU : Summable (fun n : ℕ => r⁻¹ * ((n:ℝ) * (4*r)^n)) :=
    (summable_n_mul_q_pow hr1 hr0).mul_left r⁻¹
  have h := hasDerivAt_tsum_of_isPreconnected (u := fun n : ℕ => r⁻¹ * ((n:ℝ) * (4*r)^n))
    hU hopen hconn hderiv hbound h0mem hbase hymem
  unfold Cval
  exact h

private lemma summable_dC {y : ℝ} (hy : |y| < 1 / 4) : Summable (fun n : ℕ => dC n y) := by
  have ⟨hrpos, hr1, hymem, _⟩ := mid_facts hy
  have hr0 : (0:ℝ) ≤ (|y| + 1/4)/2 := le_of_lt hrpos
  set r := (|y| + 1 / 4) / 2 with hrdef
  have hyr : |y| ≤ r := le_of_lt (abs_lt.mpr (Set.mem_Ioo.mp hymem))
  apply Summable.of_norm_bounded
    (g := fun n : ℕ => r⁻¹ * ((n:ℝ) * (4*r)^n))
    ((summable_n_mul_q_pow hr1 hr0).mul_left r⁻¹)
  intro n
  exact dC_bound hrpos hr1 hyr n

private lemma dB_bound {r z : ℝ} (hrpos : 0 < r) (_hr1 : 4 * r < 1) (hzr : |z| ≤ r)
    (n : ℕ) : ‖dB n z‖ ≤ (r⁻¹ * ((n:ℝ)^2 * (4*r)^n)) := by
  have hr0 : (0:ℝ) ≤ r := le_of_lt hrpos
  have habs_n : |(n : ℝ)| = (n : ℝ) := abs_of_nonneg (Nat.cast_nonneg n)
  have e1 : ‖dB n z‖ = cbR n * |harm n| * (n:ℝ) * |z| ^ (n - 1) := by
    unfold dB
    rw [norm_mul, norm_mul, norm_mul, norm_pow, Real.norm_eq_abs, Real.norm_eq_abs,
      Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (cbR_nonneg n), habs_n]
    ring
  have hq : (4*r)^n = 4^n * r^n := mul_pow _ _ _
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [e1]; simp
  · rw [e1]
    have hnR : |harm n| ≤ (n:ℝ) := by
      rw [abs_of_nonneg (harm_nonneg n)]; exact harm_le n
    have hle : |z|^(n-1) ≤ r^(n-1) := pow_le_pow_left₀ (abs_nonneg _) hzr _
    have h1 : cbR n * |harm n| ≤ 4^n * (n:ℝ) :=
      mul_le_mul (cbR_le_four_pow n) hnR (abs_nonneg _) (by positivity)
    have hA : cbR n * |harm n| * (n:ℝ) ≤ (4^n * (n:ℝ)) * (n:ℝ) :=
      mul_le_mul_of_nonneg_right h1 (Nat.cast_nonneg _)
    calc cbR n * |harm n| * ↑n * |z| ^ (n - 1) ≤ ((4^n * ↑n) * ↑n) * r^(n-1) :=
          mul_le_mul hA hle (pow_nonneg (abs_nonneg _) _) (by positivity)
      _ = r⁻¹ * (↑n^2 * (4*r)^n) := by
          have hrne : r ≠ 0 := ne_of_gt hrpos
          have key : r ^ (n - 1) * r = r ^ n := by
            have h1 : n - 1 + 1 = n := by omega
            calc r ^ (n - 1) * r = r ^ (n - 1) * r ^ 1 := by rw [pow_one]
              _ = r ^ ((n - 1) + 1) := by rw [pow_add]
              _ = r ^ n := by rw [h1]
          rw [hq, inv_mul_eq_div, eq_div_iff hrne, ← key]
          ring

private lemma hasDerivAt_Bval {y : ℝ} (hy : |y| < 1 / 4) :
    HasDerivAt Bval (∑' n : ℕ, dB n y) y := by
  have ⟨hrpos, hr1, hymem, h0mem⟩ := mid_facts hy
  have hr0 : (0:ℝ) ≤ (|y| + 1/4)/2 := le_of_lt hrpos
  set r := (|y| + 1 / 4) / 2 with hrdef
  have hopen : IsOpen (Set.Ioo (-r) r) := isOpen_Ioo
  have hconn : IsPreconnected (Set.Ioo (-r) r) := (convex_Ioo _ _).isPreconnected
  have hbase : Summable (fun n : ℕ => cbR n * harm n * (0:ℝ) ^ n) :=
    summable_cb_harm_pow hr0 hr1 (by simp [hr0])
  have hbound : ∀ n : ℕ, ∀ z ∈ Set.Ioo (-r) r, ‖dB n z‖ ≤ (r⁻¹ * ((n:ℝ)^2 * (4*r)^n)) :=
    fun n z hz => dB_bound hrpos hr1 (le_of_lt (abs_lt.mpr (Set.mem_Ioo.mp hz))) n
  have hderiv : ∀ n : ℕ, ∀ z ∈ Set.Ioo (-r) r,
      HasDerivAt (fun y => cbR n * harm n * y ^ n) (dB n z) z :=
    fun n z _ => term_deriv_B n z
  have hU : Summable (fun n : ℕ => r⁻¹ * ((n:ℝ)^2 * (4*r)^n)) :=
    (summable_n2_mul_q_pow hr1 hr0).mul_left r⁻¹
  have h := hasDerivAt_tsum_of_isPreconnected (u := fun n : ℕ => r⁻¹ * ((n:ℝ)^2 * (4*r)^n))
    hU hopen hconn hderiv hbound h0mem hbase hymem
  unfold Bval
  exact h

private lemma summable_dB {y : ℝ} (hy : |y| < 1 / 4) : Summable (fun n : ℕ => dB n y) := by
  have ⟨hrpos, hr1, hymem, _⟩ := mid_facts hy
  have hr0 : (0:ℝ) ≤ (|y| + 1/4)/2 := le_of_lt hrpos
  set r := (|y| + 1 / 4) / 2 with hrdef
  have hyr : |y| ≤ r := le_of_lt (abs_lt.mpr (Set.mem_Ioo.mp hymem))
  apply Summable.of_norm_bounded
    (g := fun n : ℕ => r⁻¹ * ((n:ℝ)^2 * (4*r)^n))
    ((summable_n2_mul_q_pow hr1 hr0).mul_left r⁻¹)
  intro n
  exact dB_bound hrpos hr1 hyr n

private lemma dF_bound {r z : ℝ} (_hr0 : 0 ≤ r) (_hr1 : 4 * r < 1) (hzr : |z| ≤ r)
    (n : ℕ) : ‖dF n z‖ ≤ (((n:ℝ) * ((n:ℝ)+1)) * (4*r)^n) := by
  have habs_n1 : |(n : ℝ) + 1| = (n : ℝ) + 1 := abs_of_nonneg (by positivity)
  have e1 : ‖dF n z‖ = catR n * |harm n| * ((n:ℝ)+1) * |z| ^ n := by
    unfold dF
    rw [norm_mul, norm_mul, norm_mul, norm_pow, Real.norm_eq_abs, Real.norm_eq_abs,
      Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (catR_nonneg n), habs_n1]
    ring
  rw [e1]
  have hnR : |harm n| ≤ (n:ℝ) := by
    rw [abs_of_nonneg (harm_nonneg n)]; exact harm_le n
  have hle : |z|^n ≤ r^n := pow_le_pow_left₀ (abs_nonneg _) hzr _
  have hA : catR n * |harm n| * ((n:ℝ)+1) ≤ (4^n * (n:ℝ)) * ((n:ℝ)+1) :=
    mul_le_mul_of_nonneg_right
      (mul_le_mul (catR_le_four_pow n) hnR (abs_nonneg _) (by positivity))
      (by positivity)
  calc catR n * |harm n| * (↑n+1) * |z| ^ n ≤ ((4^n * ↑n) * (↑n+1)) * r^n :=
        mul_le_mul hA hle (pow_nonneg (abs_nonneg _) _) (by positivity)
    _ = (↑n * (↑n+1)) * (4*r)^n := by rw [mul_pow]; ring

private lemma summable_uF {r : ℝ} (hr0 : 0 ≤ r) (hr1 : 4 * r < 1) :
    Summable (fun n : ℕ => ((n:ℝ) * ((n:ℝ)+1)) * (4*r)^n) := by
  have heq : (fun n : ℕ => ((n:ℝ) * ((n:ℝ)+1)) * (4*r)^n)
      = (fun n : ℕ => (n:ℝ)^2 * (4*r)^n + (n:ℝ) * (4*r)^n) := by
    funext n; ring
  rw [heq]
  exact (summable_n2_mul_q_pow hr1 hr0).add (summable_n_mul_q_pow hr1 hr0)

private lemma hasDerivAt_Fval {y : ℝ} (hy : |y| < 1 / 4) :
    HasDerivAt Fval (∑' n : ℕ, dF n y) y := by
  have ⟨hrpos, hr1, hymem, h0mem⟩ := mid_facts hy
  have hr0 : (0:ℝ) ≤ (|y| + 1/4)/2 := le_of_lt hrpos
  set r := (|y| + 1 / 4) / 2 with hrdef
  have hopen : IsOpen (Set.Ioo (-r) r) := isOpen_Ioo
  have hconn : IsPreconnected (Set.Ioo (-r) r) := (convex_Ioo _ _).isPreconnected
  have hbase : Summable (fun n : ℕ => catR n * harm n * (0:ℝ) ^ (n+1)) :=
    summable_cat_harm_pow_succ hr0 hr1 (by simp [hr0])
  have hbound : ∀ n : ℕ, ∀ z ∈ Set.Ioo (-r) r,
      ‖dF n z‖ ≤ (((n:ℝ) * ((n:ℝ)+1)) * (4*r)^n) :=
    fun n z hz => dF_bound hr0 hr1 (le_of_lt (abs_lt.mpr (Set.mem_Ioo.mp hz))) n
  have hderiv : ∀ n : ℕ, ∀ z ∈ Set.Ioo (-r) r,
      HasDerivAt (fun y => catR n * harm n * y ^ (n+1)) (dF n z) z :=
    fun n z _ => term_deriv_F n z
  have hU : Summable (fun n : ℕ => ((n:ℝ) * ((n:ℝ)+1)) * (4*r)^n) :=
    summable_uF hr0 hr1
  have h := hasDerivAt_tsum_of_isPreconnected
    (u := fun n : ℕ => ((n:ℝ) * ((n:ℝ)+1)) * (4*r)^n)
    hU hopen hconn hderiv hbound h0mem hbase hymem
  unfold Fval
  exact h

private lemma summable_dF {y : ℝ} (hy : |y| < 1 / 4) : Summable (fun n : ℕ => dF n y) := by
  have ⟨hrpos, hr1, hymem, _⟩ := mid_facts hy
  have hr0 : (0:ℝ) ≤ (|y| + 1/4)/2 := le_of_lt hrpos
  set r := (|y| + 1 / 4) / 2 with hrdef
  have hyr : |y| ≤ r := le_of_lt (abs_lt.mpr (Set.mem_Ioo.mp hymem))
  apply Summable.of_norm_bounded
    (g := fun n : ℕ => ((n:ℝ) * ((n:ℝ)+1)) * (4*r)^n)
    (summable_uF hr0 hr1)
  intro n
  exact dF_bound hr0 hr1 hyr n

/-- `y * (n * y^(n-1)) = n * y^n` for all `n` (including `n = 0`). -/
private lemma ypow_lemma (y : ℝ) (n : ℕ) : y * ((n:ℝ) * y^(n-1)) = (n:ℝ) * y^n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · have h1 : n - 1 + 1 = n := by omega
    calc y * (↑n * y^(n-1)) = ↑n * (y * y^(n-1)) := by ring
      _ = ↑n * y^n := by rw [← pow_succ', h1]

/-- Real form of `Nat.succ_mul_centralBinom_succ`. -/
private lemma hcb_eq (n : ℕ) : ((n:ℝ)+1) * cbR (n+1) = 2*(2*(n:ℝ)+1) * cbR n := by
  have h := Nat.succ_mul_centralBinom_succ n
  have hcast : ((((n+1) * Nat.centralBinom (n+1) : ℕ)) : ℝ)
      = ((((2*(2*n+1) * Nat.centralBinom n : ℕ))) : ℝ) := by exact_mod_cast h
  push_cast at hcast
  unfold cbR
  linear_combination hcast

private lemma htermA (y : ℝ) (n : ℕ) : dA (n+1) y = 4*y*(dA n y) + 2*(cbR n * y^n) := by
  have e1 : dA (n+1) y = ((((n:ℝ)+1) * cbR (n+1))) * y^n := by
    unfold dA
    rw [Nat.add_sub_cancel]
    push_cast
    ring
  have ey : 4*y*(dA n y) = (4*(n:ℝ))*(cbR n*y^n) := by
    unfold dA
    have h := ypow_lemma y n
    calc 4*y*(cbR n*(↑n*y^(n-1))) = (4*cbR n)*(y*(↑n*y^(n-1))) := by ring
      _ = (4*cbR n)*(↑n*y^n) := by rw [h]
      _ = (4*↑n)*(cbR n*y^n) := by ring
  rw [e1, ey, hcb_eq n]
  ring

private lemma ODE_A {y : ℝ} (hy : |y| < 1 / 4) :
    (∑' n, dA n y) = 4*y*(∑' n, dA n y) + 2*(Aval y) := by
  obtain ⟨hrpos, hr1, hymem, _⟩ := mid_facts hy
  have hr0 : (0:ℝ) ≤ (|y|+1/4)/2 := le_of_lt hrpos
  have hyr : |y| ≤ (|y|+1/4)/2 := le_of_lt (abs_lt.mpr (Set.mem_Ioo.mp hymem))
  have hsA := summable_dA hy
  have hsT : Summable (fun n => cbR n * y^n) := summable_cb_pow hr0 hr1 hyr
  have hz : dA 0 y = 0 := by simp [dA]
  have hshift : (∑' n, dA (n+1) y) = (∑' n, dA n y) := by
    have h := hsA.tsum_eq_zero_add
    rw [hz, zero_add] at h
    exact h.symm
  have h2 : (∑' n, dA (n+1) y) = 4*y*(∑' n, dA n y) + 2*(∑' n, cbR n * y^n) := by
    have e : (fun n => dA (n+1) y) = (fun n => 4*y*(dA n y) + 2*(cbR n * y^n)) :=
      funext (htermA y)
    have s1 : Summable (fun n => 4*y*(dA n y)) := hsA.mul_left _
    have s2 : Summable (fun n => 2*(cbR n * y^n)) := hsT.mul_left _
    rw [e, Summable.tsum_add s1 s2]
    simp only [tsum_mul_left]
  rw [hshift] at h2
  exact h2

private lemma succ_mul_catR (n : ℕ) : ((n:ℝ)+1) * catR n = cbR n := by
  have h := succ_mul_catalan_eq_centralBinom n
  unfold catR cbR
  have h2 : ((n + 1 : ℕ) : ℝ) * ((catalan n : ℕ) : ℝ)
      = ((n.centralBinom : ℕ) : ℝ) := by
    exact_mod_cast h
  push_cast at h2 ⊢
  linarith

private lemma htermC (y : ℝ) (n : ℕ) : cbR n * y^n = catR n * y^n + y*(dC n y) := by
  have ey : y*(dC n y) = (n:ℝ)*(catR n*y^n) := by
    unfold dC
    have h := ypow_lemma y n
    calc y*(catR n*(↑n*y^(n-1))) = catR n*(y*(↑n*y^(n-1))) := by ring
      _ = catR n*(↑n*y^n) := by rw [h]
      _ = ↑n*(catR n*y^n) := by ring
  have hcat := succ_mul_catR n
  rw [ey]
  have e : cbR n * y^n = ((n:ℝ)+1) * (catR n * y^n) := by
    rw [← hcat]; ring
  rw [e]; ring

private lemma ODE_C {y : ℝ} (hy : |y| < 1 / 4) :
    Aval y = Cval y + y*(∑' n, dC n y) := by
  obtain ⟨hrpos, hr1, hymem, _⟩ := mid_facts hy
  have hr0 : (0:ℝ) ≤ (|y|+1/4)/2 := le_of_lt hrpos
  have hyr : |y| ≤ (|y|+1/4)/2 := le_of_lt (abs_lt.mpr (Set.mem_Ioo.mp hymem))
  have s1 : Summable (fun n => catR n * y^n) := summable_cat_pow hr0 hr1 hyr
  have s2 : Summable (fun n => y*(dC n y)) := (summable_dC hy).mul_left _
  have e : (fun n => cbR n * y^n) = (fun n => catR n * y^n + y*(dC n y)) :=
    funext (htermC y)
  have hmul : (∑' n, y*(dC n y)) = y*(∑' n, dC n y) := tsum_mul_left
  have h2 : (∑' n, cbR n * y^n) = (∑' n, catR n * y^n) + y*(∑' n, dC n y) := by
    rw [e, Summable.tsum_add s1 s2, hmul]
  exact h2

private lemma htermB (y : ℝ) (n : ℕ) : dB (n+1) y
    = 4*y*(dB n y) + (2*(cbR n*harm n*y^n) + (4*(cbR n*y^n) - 2*(catR n*y^n))) := by
  have e1 : dB (n+1) y
      = ((((n:ℝ)+1) * cbR (n+1)) * (harm n + ((n:ℝ)+1)⁻¹)) * y^n := by
    unfold dB
    rw [Nat.add_sub_cancel, harm_succ]
    push_cast
    ring
  have ey : 4*y*(dB n y) = (4*(n:ℝ))*(cbR n*harm n*y^n) := by
    unfold dB
    have h := ypow_lemma y n
    calc 4*y*(cbR n*harm n*(↑n*y^(n-1)))
        = (4*(cbR n*harm n))*(y*(↑n*y^(n-1))) := by ring
      _ = (4*(cbR n*harm n))*(↑n*y^n) := by rw [h]
      _ = (4*↑n)*(cbR n*harm n*y^n) := by ring
  have hcat := succ_mul_catR n
  have hne : ((n:ℝ)+1) ≠ 0 := by positivity
  have h2 : ((n:ℝ)+1)⁻¹ * ((n:ℝ)+1) = 1 := inv_mul_cancel₀ hne
  rw [e1, ey, hcb_eq n]
  linear_combination (2 * y^n * ((n:ℝ)+1)⁻¹) * hcat + (y^n * (4*cbR n - 2*catR n)) * h2

private lemma ODE_B {y : ℝ} (hy : |y| < 1 / 4) :
    (∑' n, dB n y) = 4*y*(∑' n, dB n y)
      + (2*(Bval y) + (4*(Aval y) - 2*(Cval y))) := by
  obtain ⟨hrpos, hr1, hymem, _⟩ := mid_facts hy
  have hr0 : (0:ℝ) ≤ (|y|+1/4)/2 := le_of_lt hrpos
  have hyr : |y| ≤ (|y|+1/4)/2 := le_of_lt (abs_lt.mpr (Set.mem_Ioo.mp hymem))
  have hsB := summable_dB hy
  have hsT : Summable (fun n => cbR n * harm n * y^n) := summable_cb_harm_pow hr0 hr1 hyr
  have hsA : Summable (fun n => cbR n * y^n) := summable_cb_pow hr0 hr1 hyr
  have hsC : Summable (fun n => catR n * y^n) := summable_cat_pow hr0 hr1 hyr
  have hz : dB 0 y = 0 := by simp [dB]
  have hshift : (∑' n, dB (n+1) y) = (∑' n, dB n y) := by
    have h := hsB.tsum_eq_zero_add
    rw [hz, zero_add] at h
    exact h.symm
  have h2 : (∑' n, dB (n+1) y) = 4*y*(∑' n, dB n y)
      + (2*(∑' n, cbR n*harm n*y^n)
        + (4*(∑' n, cbR n*y^n) - 2*(∑' n, catR n*y^n))) := by
    have e : (fun n => dB (n+1) y) = (fun n => 4*y*(dB n y)
        + (2*(cbR n*harm n*y^n) + (4*(cbR n*y^n) - 2*(catR n*y^n)))) :=
      funext (htermB y)
    have s1 : Summable (fun n => 4*y*(dB n y)) := hsB.mul_left _
    have s2 : Summable (fun n => 2*(cbR n*harm n*y^n)) := hsT.mul_left _
    have s3 : Summable (fun n => 4*(cbR n*y^n)) := hsA.mul_left _
    have s4 : Summable (fun n => 2*(catR n*y^n)) := hsC.mul_left _
    have s5 : Summable (fun n =>
        (2*(cbR n*harm n*y^n) + (4*(cbR n*y^n) - 2*(catR n*y^n)))) :=
      s2.add (s3.sub s4)
    have hmul1 : (∑' n, 4*y*(dB n y)) = 4*y*(∑' n, dB n y) := tsum_mul_left
    have hmul2 : (∑' n, 2*(cbR n*harm n*y^n)) = 2*(∑' n, cbR n*harm n*y^n) :=
      tsum_mul_left
    have hmul3 : (∑' n, 4*(cbR n*y^n)) = 4*(∑' n, cbR n*y^n) := tsum_mul_left
    have hmul4 : (∑' n, 2*(catR n*y^n)) = 2*(∑' n, catR n*y^n) := tsum_mul_left
    rw [e, Summable.tsum_add s1 s5, hmul1,
      Summable.tsum_add s2 (s3.sub s4), Summable.tsum_sub s3 s4,
      hmul2, hmul3, hmul4]
  rw [hshift] at h2
  exact h2

private lemma htermF (y : ℝ) (n : ℕ) : dF n y = cbR n * harm n * y^n := by
  have hcat := succ_mul_catR n
  unfold dF
  linear_combination (harm n * y^n) * hcat

private lemma ODE_F' {y : ℝ} (hy : |y| < 1 / 4) : HasDerivAt Fval (Bval y) y := by
  have hF := hasDerivAt_Fval hy
  have e : (∑' n, dF n y) = Bval y := tsum_congr (htermF y)
  rw [e] at hF
  exact hF

private lemma Aval_zero : Aval 0 = 1 := by
  have hc0 : Nat.centralBinom 0 = 1 := by decide
  unfold Aval
  rw [tsum_eq_single 0 (fun b hb => by rw [zero_pow hb, mul_zero])]
  simp [cbR, hc0]

private lemma Cval_zero : Cval 0 = 1 := by
  unfold Cval
  rw [tsum_eq_single 0 (fun b hb => by rw [zero_pow hb, mul_zero])]
  simp [catR, catalan_zero]

private lemma Bval_zero : Bval 0 = 0 := by
  have hc0 : Nat.centralBinom 0 = 1 := by decide
  unfold Bval
  rw [tsum_eq_single 0 (fun b hb => by simp [zero_pow hb])]
  simp [cbR, hc0, harm_zero]

private lemma Fval_zero : Fval 0 = 0 := by
  unfold Fval
  have hz : ∀ n : ℕ, catR n * harm n * (0:ℝ)^(n+1) = 0 :=
    fun n => by rw [zero_pow (Nat.succ_ne_zero n), mul_zero]
  rw [tsum_congr hz]
  exact tsum_zero

private noncomputable def S (y : ℝ) : ℝ := Real.sqrt (1 - 4*y)

private lemma memIoo_abs {y : ℝ} (hy : y ∈ Set.Ioo (-1 / 4 : ℝ) (1 / 4)) : |y| < 1/4 := by
  have h := Set.mem_Ioo.mp hy
  rw [abs_lt]
  exact ⟨by linarith [h.1], h.2⟩

private lemma one_sub_pos {y : ℝ} (hy : y ∈ Set.Ioo (-1 / 4 : ℝ) (1 / 4)) : (0:ℝ) < 1 - 4*y := by
  have h := (Set.mem_Ioo.mp hy).2
  linarith

private lemma S_sq {y : ℝ} (hy : y ∈ Set.Ioo (-1 / 4 : ℝ) (1 / 4)) : S y ^ 2 = 1 - 4*y := by
  unfold S
  exact Real.sq_sqrt (le_of_lt (one_sub_pos hy))

private lemma S_pos {y : ℝ} (hy : y ∈ Set.Ioo (-1 / 4 : ℝ) (1 / 4)) : 0 < S y :=
  Real.sqrt_pos.mpr (one_sub_pos hy)

private lemma S_ne {y : ℝ} (hy : y ∈ Set.Ioo (-1 / 4 : ℝ) (1 / 4)) : S y ≠ 0 :=
  ne_of_gt (S_pos hy)

private lemma S_zero : S 0 = 1 := by simp [S]

private lemma hlin (y : ℝ) : HasDerivAt (fun t : ℝ => 1 - 4*t) (-4) y := by
  have h2 : HasDerivAt (fun t : ℝ => 4*t) 4 y := by
    simpa using (hasDerivAt_id y).const_mul 4
  simpa using HasDerivAt.const_sub (1:ℝ) h2

private lemma hS (y : ℝ) (hy : y ∈ Set.Ioo (-1 / 4 : ℝ) (1 / 4)) : HasDerivAt S (-2 / S y) y := by
  have hpos := one_sub_pos hy
  have h := (hlin y).sqrt (ne_of_gt hpos)
  have hne2 : Real.sqrt (1-4*y) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hpos)
  have h2' : (-4:ℝ) / (2 * Real.sqrt (1-4*y)) = -2 / S y := by
    unfold S
    field_simp
    ring
  rw [h2'] at h
  exact h

private lemma Aval_eq : ∀ y ∈ Set.Ioo (-1/4:ℝ) (1/4), Aval y = (S y)⁻¹ := by
  have hP : ∀ t ∈ Set.Ioo (-1/4:ℝ) (1/4),
      HasDerivAt (fun t => Aval t * S t) 0 t := by
    intro t ht
    have ht' : |t| < 1/4 := memIoo_abs ht
    have hAt := hasDerivAt_Aval ht'
    have hSt := hS t ht
    have hmul := hAt.mul hSt
    have hne := S_ne ht
    have hode := ODE_A ht'
    have h1 : (∑' n, dA n t) * (1 - 4*t) = 2 * Aval t := by
      linear_combination hode
    have hval : (∑' n, dA n t) * S t + Aval t * (-2 / S t) = 0 := by
      have hSi : (S t)⁻¹ * S t = 1 := inv_mul_cancel₀ hne
      have key : ((∑' n, dA n t) * S t + Aval t * (-2 / S t)) * S t = 0 := by
        linear_combination (∑' n, dA n t) * (S_sq ht) + h1 - (2 * Aval t) * hSi
      rcases mul_eq_zero.mp key with h | h
      · exact h
      · exact absurd h hne
    rwa [hval] at hmul
  have hQ : ∀ t ∈ Set.Ioo (-1/4:ℝ) (1/4),
      HasDerivAt (fun t => (S t)⁻¹ * S t) 0 t := by
    intro t ht
    have h1 : HasDerivAt (fun _ : ℝ => (1:ℝ)) 0 t := hasDerivAt_const t 1
    have hev : (fun t => (S t)⁻¹ * S t) =ᶠ[nhds t] (fun _ => 1) := by
      have hnb : Set.Ioo (-1/4:ℝ) (1/4) ∈ nhds t := isOpen_Ioo.mem_nhds ht
      filter_upwards [hnb] with s hs using inv_mul_cancel₀ (S_ne hs)
    exact h1.congr_of_eventuallyEq hev
  have hPdiff : DifferentiableOn ℝ (fun t => Aval t * S t) (Set.Ioo (-1/4:ℝ) (1/4)) :=
    fun t ht => (hP t ht).differentiableAt.differentiableWithinAt
  have hQdiff : DifferentiableOn ℝ (fun t => (S t)⁻¹ * S t) (Set.Ioo (-1/4:ℝ) (1/4)) :=
    fun t ht => (hQ t ht).differentiableAt.differentiableWithinAt
  have hderivP : ∀ t ∈ Set.Ioo (-1/4:ℝ) (1/4),
      deriv (fun t => Aval t * S t) t = 0 :=
    fun t ht => (hP t ht).deriv
  have hderivQ : ∀ t ∈ Set.Ioo (-1/4:ℝ) (1/4),
      deriv (fun t => (S t)⁻¹ * S t) t = 0 :=
    fun t ht => (hQ t ht).deriv
  have heq : Set.EqOn (deriv (fun t => Aval t * S t))
      (deriv (fun t => (S t)⁻¹ * S t)) (Set.Ioo (-1/4:ℝ) (1/4)) :=
    fun t ht => (hderivP t ht).trans (hderivQ t ht).symm
  have h0mem : (0:ℝ) ∈ Set.Ioo (-1/4:ℝ) (1/4) :=
    Set.mem_Ioo.mpr ⟨by norm_num, by norm_num⟩
  have hP0 : (fun t => Aval t * S t) 0 = (fun t => (S t)⁻¹ * S t) 0 := by
    simp only []
    rw [Aval_zero, S_zero]
    norm_num
  have hPQ : Set.EqOn (fun t => Aval t * S t) (fun t => (S t)⁻¹ * S t)
      (Set.Ioo (-1/4:ℝ) (1/4)) :=
    isOpen_Ioo.eqOn_of_deriv_eq (convex_Ioo _ _).isPreconnected
      hPdiff hQdiff heq h0mem hP0
  intro y hy
  have h : Aval y * S y = (S y)⁻¹ * S y := hPQ hy
  exact mul_right_cancel₀ (S_ne hy) h

private lemma Cval_eq : ∀ y ∈ Set.Ioo (-1/4:ℝ) (1/4), Cval y = 2/(1 + S y) := by
  have hL : ∀ t ∈ Set.Ioo (-1/4:ℝ) (1/4),
      HasDerivAt (fun t => t * Cval t) (Aval t) t := by
    intro t ht
    have ht' := memIoo_abs ht
    have hCt := hasDerivAt_Cval ht'
    have hIt : HasDerivAt (fun t : ℝ => t) 1 t := hasDerivAt_id' t
    have hmul := hIt.mul hCt
    have hode := ODE_C ht'
    have hval : (1:ℝ) * Cval t + t * (∑' n, dC n t) = Aval t := by
      linear_combination -hode
    rwa [hval] at hmul
  have hM : ∀ t ∈ Set.Ioo (-1/4:ℝ) (1/4),
      HasDerivAt (fun t => (1 - S t)/2) (Aval t) t := by
    intro t ht
    have hSt := hS t ht
    have hne := S_ne ht
    have hsub := HasDerivAt.const_sub (1:ℝ) hSt
    have hdiv := hsub.div_const 2
    have hAval : Aval t = (S t)⁻¹ := Aval_eq t ht
    have hval : (-(-2/S t))/2 = Aval t := by
      rw [hAval]
      field_simp
    rwa [hval] at hdiv
  have hLdiff : DifferentiableOn ℝ (fun t => t * Cval t) (Set.Ioo (-1/4:ℝ) (1/4)) :=
    fun t ht => (hL t ht).differentiableAt.differentiableWithinAt
  have hMdiff : DifferentiableOn ℝ (fun t => (1 - S t)/2) (Set.Ioo (-1/4:ℝ) (1/4)) :=
    fun t ht => (hM t ht).differentiableAt.differentiableWithinAt
  have hderivL : ∀ t ∈ Set.Ioo (-1/4:ℝ) (1/4),
      deriv (fun t => t * Cval t) t = Aval t :=
    fun t ht => (hL t ht).deriv
  have hderivM : ∀ t ∈ Set.Ioo (-1/4:ℝ) (1/4),
      deriv (fun t => (1 - S t)/2) t = Aval t :=
    fun t ht => (hM t ht).deriv
  have heq : Set.EqOn (deriv (fun t => t * Cval t))
      (deriv (fun t => (1 - S t)/2)) (Set.Ioo (-1/4:ℝ) (1/4)) :=
    fun t ht => (hderivL t ht).trans (hderivM t ht).symm
  have h0mem : (0:ℝ) ∈ Set.Ioo (-1/4:ℝ) (1/4) :=
    Set.mem_Ioo.mpr ⟨by norm_num, by norm_num⟩
  have hLM0 : (fun t => t * Cval t) 0 = (fun t => (1 - S t)/2) 0 := by
    simp only []
    rw [S_zero]
    simp
  have hLM : Set.EqOn (fun t => t * Cval t) (fun t => (1 - S t)/2)
      (Set.Ioo (-1/4:ℝ) (1/4)) :=
    isOpen_Ioo.eqOn_of_deriv_eq (convex_Ioo _ _).isPreconnected
      hLdiff hMdiff heq h0mem hLM0
  intro y hy
  have hne := S_ne hy
  have h1S : (1:ℝ) + S y ≠ 0 := ne_of_gt (by linarith [S_pos hy])
  rcases eq_or_ne y 0 with rfl | hy0
  · rw [Cval_zero, S_zero]; norm_num
  · have h : y * Cval y = (1 - S y)/2 := hLM hy
    have h2y : (2:ℝ)*y ≠ 0 := mul_ne_zero two_ne_zero hy0
    have e2 : (1 - S y)*(1 + S y) = 4*y := by linear_combination -(S_sq hy)
    have e : (1 - S y)/(2*y) = 2/(1 + S y) := by
      rw [div_eq_div_iff h2y h1S, e2]; ring
    have hC : Cval y = ((1 - S y)/2)/y := by
      rw [eq_div_iff hy0, mul_comm]
      exact h
    rw [hC, div_div]
    exact e

private lemma Bval_eq : ∀ y ∈ Set.Ioo (-1/4:ℝ) (1/4),
    Bval y = 2*(Real.log (1 + S y) - Real.log 2 - Real.log (S y))/S y := by
  have hJ : ∀ t ∈ Set.Ioo (-1/4:ℝ) (1/4),
      HasDerivAt (fun t => Bval t * S t) ((4*Aval t - 2*Cval t)/S t) t := by
    intro t ht
    have ht' : |t| < 1/4 := memIoo_abs ht
    have hBt := hasDerivAt_Bval ht'
    have hSt := hS t ht
    have hne := S_ne ht
    have hmul := hBt.mul hSt
    have hode := ODE_B ht'
    have h1 : (∑' n, dB n t) * (1 - 4*t)
        = 2*Bval t + (4*Aval t - 2*Cval t) := by
      linear_combination hode
    have hval : (∑' n, dB n t) * S t + Bval t * (-2 / S t)
        = (4*Aval t - 2*Cval t)/S t := by
      have hSi : (S t)⁻¹ * S t = 1 := inv_mul_cancel₀ hne
      have key : ((∑' n, dB n t) * S t + Bval t * (-2 / S t)) * S t
          = (4*Aval t - 2*Cval t) := by
        linear_combination (∑' n, dB n t) * (S_sq ht) + h1 - (2 * Bval t) * hSi
      have e : ((4*Aval t - 2*Cval t)/S t) * S t = (4*Aval t - 2*Cval t) :=
        div_mul_cancel₀ _ hne
      have hcan : ((∑' n, dB n t) * S t + Bval t * (-2 / S t)) * S t
          = ((4*Aval t - 2*Cval t)/S t) * S t := by
        rw [key, e]
      exact mul_right_cancel₀ hne hcan
    rwa [hval] at hmul
  have hK : ∀ t ∈ Set.Ioo (-1/4:ℝ) (1/4),
      HasDerivAt (fun t => 2*(Real.log (1 + S t) - Real.log 2 - Real.log (S t)))
        ((4*Aval t - 2*Cval t)/S t) t := by
    intro t ht
    have hSt := hS t ht
    have hne := S_ne ht
    have h1S : (1:ℝ) + S t ≠ 0 := ne_of_gt (by linarith [S_pos ht])
    have hf1 : HasDerivAt (fun t => 1 + S t) (-2/S t) t :=
      HasDerivAt.const_add 1 hSt
    have hlog1 : HasDerivAt (fun t => Real.log (1 + S t)) ((-2/S t)/(1 + S t)) t :=
      hf1.log h1S
    have hlogS : HasDerivAt (fun t => Real.log (S t)) ((-2/S t)/(S t)) t :=
      hSt.log hne
    have hlog2 : HasDerivAt (fun _ : ℝ => Real.log 2) 0 t := hasDerivAt_const t _
    have hKraw := ((hlog1.sub hlog2).sub hlogS).const_mul 2
    have hKas : HasDerivAt (fun t => 2*(Real.log (1 + S t) - Real.log 2 - Real.log (S t)))
        (2*(((-2/S t)/(1 + S t) - 0) - (-2/S t)/(S t))) t := hKraw
    have hvalK : (2*(((-2/S t)/(1 + S t) - 0) - (-2/S t)/(S t)))
        = (4*Aval t - 2*Cval t)/S t := by
      rw [Aval_eq t ht, Cval_eq t ht]
      field_simp
      ring
    rwa [hvalK] at hKas
  have hJdiff : DifferentiableOn ℝ (fun t => Bval t * S t) (Set.Ioo (-1/4:ℝ) (1/4)) :=
    fun t ht => (hJ t ht).differentiableAt.differentiableWithinAt
  have hKdiff : DifferentiableOn ℝ
      (fun t => 2*(Real.log (1 + S t) - Real.log 2 - Real.log (S t)))
      (Set.Ioo (-1/4:ℝ) (1/4)) :=
    fun t ht => (hK t ht).differentiableAt.differentiableWithinAt
  have hderivJ : ∀ t ∈ Set.Ioo (-1/4:ℝ) (1/4),
      deriv (fun t => Bval t * S t) t = (4*Aval t - 2*Cval t)/S t :=
    fun t ht => (hJ t ht).deriv
  have hderivK : ∀ t ∈ Set.Ioo (-1/4:ℝ) (1/4),
      deriv (fun t => 2*(Real.log (1 + S t) - Real.log 2 - Real.log (S t))) t
        = (4*Aval t - 2*Cval t)/S t :=
    fun t ht => (hK t ht).deriv
  have heq : Set.EqOn (deriv (fun t => Bval t * S t))
      (deriv (fun t => 2*(Real.log (1 + S t) - Real.log 2 - Real.log (S t))))
      (Set.Ioo (-1/4:ℝ) (1/4)) :=
    fun t ht => (hderivJ t ht).trans (hderivK t ht).symm
  have h0mem : (0:ℝ) ∈ Set.Ioo (-1/4:ℝ) (1/4) :=
    Set.mem_Ioo.mpr ⟨by norm_num, by norm_num⟩
  have hJK0 : (fun t => Bval t * S t) 0
      = (fun t => 2*(Real.log (1 + S t) - Real.log 2 - Real.log (S t))) 0 := by
    simp only []
    rw [Bval_zero, S_zero]
    norm_num [Real.log_one]
  have hJK : Set.EqOn (fun t => Bval t * S t)
      (fun t => 2*(Real.log (1 + S t) - Real.log 2 - Real.log (S t)))
      (Set.Ioo (-1/4:ℝ) (1/4)) :=
    isOpen_Ioo.eqOn_of_deriv_eq (convex_Ioo _ _).isPreconnected
      hJdiff hKdiff heq h0mem hJK0
  intro y hy
  have h : Bval y * S y = 2*(Real.log (1 + S y) - Real.log 2 - Real.log (S y)) :=
    hJK hy
  have e : Bval y = 2*(Real.log (1 + S y) - Real.log 2 - Real.log (S y))/S y := by
    rw [eq_div_iff (S_ne hy)]
    exact h
  exact e

private lemma Fval_eq_G : ∀ y ∈ Set.Ioo (-1/4:ℝ) (1/4), Fval y
    = (Real.log 2 + S y * Real.log (2 * S y) - (1 + S y) * Real.log (1 + S y)) := by
  have hG : ∀ t ∈ Set.Ioo (-1/4:ℝ) (1/4),
      HasDerivAt (fun t => Real.log 2 + S t * Real.log (2 * S t)
        - (1 + S t) * Real.log (1 + S t)) (Bval t) t := by
    intro t ht
    have hSt := hS t ht
    have hne := S_ne ht
    have h1S : (1:ℝ) + S t ≠ 0 := ne_of_gt (by linarith [S_pos ht])
    have h2S : (2:ℝ) * S t ≠ 0 := mul_ne_zero two_ne_zero hne
    have hf2S : HasDerivAt (fun t => 2 * S t) (2 * (-2/S t)) t :=
      hSt.const_mul 2
    have hg2S : HasDerivAt (fun t => Real.log (2 * S t)) ((2*(-2/S t))/(2*S t)) t :=
      hf2S.log h2S
    have hf1S : HasDerivAt (fun t => 1 + S t) (-2/S t) t :=
      HasDerivAt.const_add 1 hSt
    have hg1S : HasDerivAt (fun t => Real.log (1 + S t)) ((-2/S t)/(1+S t)) t :=
      hf1S.log h1S
    have hterm2 := hSt.mul hg2S
    have hterm3 := hf1S.mul hg1S
    have hlog2 : HasDerivAt (fun _ : ℝ => Real.log 2) 0 t := hasDerivAt_const t _
    have hGraw := ((hlog2.add hterm2).sub hterm3)
    have hGas0 : HasDerivAt
        (fun t => Real.log 2 + S t*Real.log (2*S t) - (1+S t)*Real.log (1+S t))
        ((0 + ((-2/S t)*Real.log (2*S t) + S t*((2*(-2/S t))/(2*S t))))
        - ((-2/S t)*Real.log (1+S t) + (1+S t)*(((-2/S t))/(1+S t)))) t := hGraw
    have hlog : Real.log (2*S t) = Real.log 2 + Real.log (S t) :=
      Real.log_mul two_ne_zero hne
    have hvalG : ((0 + ((-2/S t)*Real.log (2*S t) + S t*((2*(-2/S t))/(2*S t))))
        - ((-2/S t)*Real.log (1+S t) + (1+S t)*(((-2/S t))/(1+S t)))) = Bval t := by
      rw [hlog, Bval_eq t ht]
      field_simp
      ring
    rwa [hvalG] at hGas0
  have hFdiff : DifferentiableOn ℝ Fval (Set.Ioo (-1/4:ℝ) (1/4)) := by
    intro t ht
    have hye : |t| < 1/4 := memIoo_abs ht
    exact (ODE_F' hye).differentiableAt.differentiableWithinAt
  have hGdiff : DifferentiableOn ℝ
      (fun t => Real.log 2 + S t * Real.log (2 * S t)
        - (1 + S t) * Real.log (1 + S t)) (Set.Ioo (-1/4:ℝ) (1/4)) :=
    fun t ht => (hG t ht).differentiableAt.differentiableWithinAt
  have hderivF : ∀ t ∈ Set.Ioo (-1/4:ℝ) (1/4), deriv Fval t = Bval t := by
    intro t ht
    have hye : |t| < 1/4 := memIoo_abs ht
    exact (ODE_F' hye).deriv
  have hderivG : ∀ t ∈ Set.Ioo (-1/4:ℝ) (1/4),
      deriv (fun t => Real.log 2 + S t * Real.log (2 * S t)
        - (1 + S t) * Real.log (1 + S t)) t = Bval t :=
    fun t ht => (hG t ht).deriv
  have heq : Set.EqOn (deriv Fval)
      (deriv (fun t => Real.log 2 + S t * Real.log (2 * S t)
        - (1 + S t) * Real.log (1 + S t))) (Set.Ioo (-1/4:ℝ) (1/4)) :=
    fun t ht => (hderivF t ht).trans (hderivG t ht).symm
  have h0mem : (0:ℝ) ∈ Set.Ioo (-1/4:ℝ) (1/4) :=
    Set.mem_Ioo.mpr ⟨by norm_num, by norm_num⟩
  have hFG0 : Fval 0
      = (Real.log 2 + S 0 * Real.log (2 * S 0) - (1 + S 0) * Real.log (1 + S 0)) := by
    rw [Fval_zero, S_zero]
    have e1 : (2:ℝ)*(1:ℝ) = 2 := by norm_num
    have e2 : (1:ℝ)+1 = 2 := by norm_num
    rw [e1, e2]
    ring
  have hFG : Set.EqOn Fval
      (fun t => Real.log 2 + S t * Real.log (2 * S t)
        - (1 + S t) * Real.log (1 + S t)) (Set.Ioo (-1/4:ℝ) (1/4)) :=
    isOpen_Ioo.eqOn_of_deriv_eq (convex_Ioo _ _).isPreconnected
      hFdiff hGdiff heq h0mem hFG0
  intro y hy
  exact hFG hy

private lemma hcatchoose (n : ℕ) : (((Nat.choose (2*n) n/(n+1) : ℕ)) : ℝ) = catR n := by
  unfold catR
  have h1 : Nat.choose (2*n) n = Nat.centralBinom n :=
    (Nat.centralBinom_eq_two_mul_choose n).symm
  rw [h1, catalan_eq_centralBinom_div]

private lemma harm_eq_harmonic_cast (n : ℕ) : harm n = ((harmonic n : ℚ) : ℝ) := by
  induction n with
  | zero => simp [harm_zero, harmonic_zero]
  | succ n ih =>
    rw [harm_succ, harmonic_succ, ih, Rat.cast_add, Rat.cast_inv, Rat.cast_natCast]

/--
**Generating function of Catalan–harmonic products.** Let $C_n$ be the $n$th Catalan number and
$H_n = \sum_{k=1}^{n} 1/k$ the $n$th harmonic number, so that $H_0 = 0$. For every real number
$x$ with $|x| < 1/4$,
$$
\sum_{n=0}^{\infty} C_n H_n x^{n+1} = \log 2 + \sqrt{1-4x}\,\log\bigl(2\sqrt{1-4x}\bigr) -
\bigl(1 + \sqrt{1-4x}\bigr)\log\bigl(1 + \sqrt{1-4x}\bigr).
$$
-/
theorem catalan_harmonic_generating_function_canonical
    (x : ℝ) (hx : |x| < 1 / 4) :
    (∑' n : ℕ, (catalan n : ℝ) * ((harmonic n : ℚ) : ℝ) * x ^ (n + 1)) =
      Real.log 2 +
        Real.sqrt (1 - 4 * x) * Real.log (2 * Real.sqrt (1 - 4 * x)) -
        (1 + Real.sqrt (1 - 4 * x)) * Real.log (1 + Real.sqrt (1 - 4 * x)) := by
  have hxI : x ∈ Set.Ioo (-1/4:ℝ) (1/4) := by
    have h := abs_lt.mp hx
    rw [Set.mem_Ioo]
    exact ⟨by linarith [h.1], by linarith [h.2]⟩
  have hFGx : Fval x
      = (Real.log 2 + S x * Real.log (2 * S x) - (1 + S x) * Real.log (1 + S x)) :=
    Fval_eq_G x hxI
  have htsum : (∑' n : ℕ, (catalan n : ℝ) * ((harmonic n : ℚ) : ℝ) * x ^ (n + 1))
      = Fval x := by
    apply tsum_congr
    intro n
    have hcat : catR n = (catalan n : ℝ) := rfl
    rw [hcat, harm_eq_harmonic_cast n]
  rw [htsum]
  exact hFGx

/--
**Catalan–harmonic generating function with explicit coefficients.** For every real number $x$
with $|x| < 1/4$,
$$
\sum_{n=1}^{\infty} \frac{\binom{2n}{n}}{n+1} \Bigl(\sum_{k=1}^{n} \frac{1}{k}\Bigr) x^{n+1} =
\log 2 + \sqrt{1-4x}\,\log\bigl(2\sqrt{1-4x}\bigr) -
\bigl(1 + \sqrt{1-4x}\bigr)\log\bigl(1 + \sqrt{1-4x}\bigr).
$$

Here $\binom{2n}{n}/(n+1)$ is the $n$th Catalan number (the division is exact) and
$\sum_{k=1}^{n} 1/k$ is the $n$th harmonic number.

Proves `Wanted` entry `catalan_harmonic_generating_function`.

Source: Hongwei Chen, "Interesting Series Associated with Central Binomial
Coefficients, Catalan Numbers and Harmonic Numbers," Journal of Integer Sequences
19 (2016), Article 16.1.5, Corollary (label eq:c_gf), lines 156–160,
https://cs.uwaterloo.ca/journals/JIS/VOL19/Chen/chen21.tex; obtained there by
integrating the central-binomial harmonic generating function.
-/
theorem catalan_harmonic_generating_function
    (x : ℝ) (hx : |x| < 1 / 4) :
    (∑' n : ℕ,
      if n = 0 then 0
      else
        (((Nat.choose (2 * n) n / (n + 1) : ℕ) : ℝ) *
          (∑ k ∈ Finset.range n, (((k + 1 : ℕ) : ℝ)⁻¹)) * x ^ (n + 1))) =
      Real.log 2 +
        Real.sqrt (1 - 4 * x) * Real.log (2 * Real.sqrt (1 - 4 * x)) -
        (1 + Real.sqrt (1 - 4 * x)) * Real.log (1 + Real.sqrt (1 - 4 * x)) := by
  have hnew := catalan_harmonic_generating_function_canonical x hx
  rw [← hnew]
  apply tsum_congr
  intro n
  have hcho : (((Nat.choose (2 * n) n / (n + 1) : ℕ)) : ℝ) = (catalan n : ℝ) :=
    hcatchoose n
  have hhar : (∑ k ∈ Finset.range n, (((k + 1 : ℕ) : ℝ)⁻¹))
      = ((harmonic n : ℚ) : ℝ) :=
    harm_eq_harmonic_cast n
  rcases eq_or_ne n 0 with rfl | hn
  · simp [harmonic_zero, catalan_zero]
  · simp only [hn, ite_false, hcho, hhar]

end MetaMathlibExt
end

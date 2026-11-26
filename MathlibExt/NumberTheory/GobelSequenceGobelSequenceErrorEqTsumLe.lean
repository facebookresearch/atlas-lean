/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.GobelSequence
public import MathlibExt.NumberTheory.GobelSequenceRoots
public import MathlibExt.NumberTheory.GobelSequenceSomosBound
public import MathlibExt.NumberTheory.SomosLikeRoots
public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.ZMod.Basic
public import Mathlib.NumberTheory.Padics.PadicVal.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Defs

import MathlibExt.NumberTheory.GobelSequenceError
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Series formula and bound for the Göbel error

This file proves the logarithmic series formula and upper bound for the Göbel error.

Source: Gima, Matsusaka, Miyazaki, and Yara, *On Integrality and Asymptotic
Behavior of the (k, l)-Göbel Sequences*, Journal of Integer Sequences 27 (2024),
Article 24.8.1, Lemma 12 (`jis-2024-24.8.1-lem-12`).
-/

namespace MetaMathlibExt

open Filter Topology Asymptotics

private theorem seq_one_le (k l j : ℕ) (hl : 2 ≤ l) (hj : 1 ≤ j) :
    (1 : ℝ) ≤ gobelSequence k l j := by
  induction j, hj using Nat.le_induction with
  | base =>
    rw [gobelSequence_one]
    exact_mod_cast (by omega : 1 ≤ l)
  | succ j hj ih =>
    have hr := congrArg (Rat.cast : ℚ → ℝ) (gobelSequence_succ k l j hj)
    push_cast at hr
    have hp : (1 : ℝ) ≤ (gobelSequence k l j : ℝ) ^ (k - 1) := one_le_pow₀ ih
    have hprod : (j : ℝ) + 1 ≤
        (gobelSequence k l j : ℝ) * ((j : ℝ) + (gobelSequence k l j : ℝ) ^ (k - 1)) := by
      calc
        _ = 1 * ((j : ℝ) + 1) := by ring
        _ ≤ _ := mul_le_mul ih
          (by linarith : (j : ℝ) + 1 ≤ (j : ℝ) + (gobelSequence k l j : ℝ) ^ (k - 1))
          (by positivity) (by positivity)
    nlinarith
private theorem root_bounds (k l : ℕ) (hk : 2 ≤ k) (hl : 2 ≤ l) (C : ℝ)
    (hC : Tendsto (fun j : ℕ => (gobelSequence k l j : ℝ) ^ (1 / (k : ℝ) ^ j))
      atTop (𝓝 C)) (j : ℕ) (hj : 1 ≤ j) :
    1 ≤ C ∧ C ≤ (gobelSequence k l j : ℝ) ^ (1 / (k : ℝ) ^ j) := by
  have hlow : 1 ≤ C := ge_of_tendsto hC (eventually_atTop.2 ⟨1, fun m hm =>
    Real.one_le_rpow (seq_one_le k l m hl hm) (by positivity)⟩)
  have hanti : Antitone (fun m : ℕ =>
      (gobelSequence k l (m + 1) : ℝ) ^ (1 / (k : ℝ) ^ (m + 1))) :=
    antitone_nat_of_succ_le fun m => (gobelSequence_root_strictAnti k l (m + 1) hk hl
      (by omega)).1.le
  have hupper := hanti.le_of_tendsto (hC.comp (tendsto_add_atTop_nat 1)) (j - 1)
  exact ⟨hlow, by simpa [Nat.sub_add_cancel hj] using hupper⟩
private theorem linear_hasSum (n : ℕ) :
    HasSum (fun m : ℕ => ((m : ℝ) + n) / (2 : ℝ) ^ (m + 1)) ((n : ℝ) + 1) := by
  have hr : ‖(1 / 2 : ℝ)‖ < 1 := by norm_num
  have h := ((hasSum_coe_mul_geometric_of_norm_lt_one hr).add
    ((hasSum_geometric_of_norm_lt_one hr).mul_left (n : ℝ))).div_const 2
  convert h using 1
  · ext m
    simp only [add_div, one_div_pow, pow_succ, div_mul_eq_div_div]
    ring
  · norm_num
    ring
private theorem seq_lower (k l : ℕ) (hk : 2 ≤ k) (hl : 2 ≤ l) (C : ℝ)
    (hC : Tendsto (fun j : ℕ => (gobelSequence k l j : ℝ) ^ (1 / (k : ℝ) ^ j))
      atTop (𝓝 C)) (j : ℕ) (hj : 1 ≤ j) :
    C ^ (k ^ j) ≤ (gobelSequence k l j : ℝ) := by
  obtain ⟨hC1, hupper⟩ := root_bounds k l hk hl C hC j hj
  have h := pow_le_pow_left₀ (zero_le_one.trans hC1) hupper (k ^ j)
  have hg := (seq_one_le k l j hl hj)
  have hk0 : (k : ℝ) ≠ 0 := by positivity
  convert h using 1
  rw [← Real.rpow_mul_natCast (zero_le_one.trans hg), Nat.cast_pow,
    one_div_mul_cancel (pow_ne_zero j hk0), Real.rpow_one]
private theorem correction_bound (k l : ℕ) (hk : 2 ≤ k) (hl : 2 ≤ l) (C : ℝ)
    (hC : Tendsto (fun j : ℕ => (gobelSequence k l j : ℝ) ^ (1 / (k : ℝ) ^ j))
      atTop (𝓝 C)) (n : ℕ) (hn : 1 ≤ n) (m : ℕ) :
    0 ≤ Real.log (1 + ((m + n : ℕ) : ℝ) /
      (gobelSequence k l (m + n) : ℝ) ^ (k - 1)) / (k : ℝ) ^ (m + 1) ∧
    Real.log (1 + ((m + n : ℕ) : ℝ) /
      (gobelSequence k l (m + n) : ℝ) ^ (k - 1)) / (k : ℝ) ^ (m + 1) ≤
      (((m : ℝ) + n) / (2 : ℝ) ^ (m + 1)) / C ^ ((k - 1) * k ^ n) := by
  have hC1 := (root_bounds k l hk hl C hC n hn).1
  have hC0 : 0 < C := zero_lt_one.trans_le hC1
  have hk2 : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hg : (0 : ℝ) < gobelSequence k l (m + n) :=
    zero_lt_one.trans_le (seq_one_le k l (m + n) hl (by omega))
  have hden : C ^ ((k - 1) * k ^ n) ≤ (gobelSequence k l (m + n) : ℝ) ^ (k - 1) := by
    calc
      _ ≤ C ^ ((k - 1) * k ^ (m + n)) := pow_le_pow_right₀ hC1
        (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) (by omega)))
      _ = (C ^ (k ^ (m + n))) ^ (k - 1) := by rw [← pow_mul, Nat.mul_comm]
      _ ≤ _ := pow_le_pow_left₀ (by positivity) (seq_lower k l hk hl C hC (m + n) (by omega)) _
  have hx : 0 ≤ ((m + n : ℕ) : ℝ) / (gobelSequence k l (m + n) : ℝ) ^ (k - 1) :=
    div_nonneg (Nat.cast_nonneg _) (pow_nonneg hg.le _)
  constructor
  · exact div_nonneg (Real.log_nonneg (by linarith)) (by positivity)
  · calc
      _ ≤ (((m + n : ℕ) : ℝ) / (gobelSequence k l (m + n) : ℝ) ^ (k - 1)) /
          (k : ℝ) ^ (m + 1) := div_le_div_of_nonneg_right
        (by simpa using Real.log_le_sub_one_of_pos (by linarith :
          0 < 1 + ((m + n : ℕ) : ℝ) / (gobelSequence k l (m + n) : ℝ) ^ (k - 1)))
        (by positivity)
      _ ≤ (((m + n : ℕ) : ℝ) / C ^ ((k - 1) * k ^ n)) / (k : ℝ) ^ (m + 1) :=
        div_le_div_of_nonneg_right (div_le_div_of_nonneg_left (Nat.cast_nonneg _)
          (by positivity) hden) (by positivity)
      _ ≤ (((m + n : ℕ) : ℝ) / C ^ ((k - 1) * k ^ n)) / (2 : ℝ) ^ (m + 1) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity)
          (pow_le_pow_left₀ (by norm_num) hk2 _)
      _ = _ := by push_cast; ring
private theorem log_summable (k n : ℕ) (hk : 2 ≤ k) :
    Summable (fun m : ℕ => Real.log ((m + 1 : ℝ) + n) / (k : ℝ) ^ (m + 1)) := by
  have hk2 : (2 : ℝ) ≤ k := by exact_mod_cast hk
  refine (linear_hasSum (n + 1)).summable.of_nonneg_of_le (fun m =>
    div_nonneg (Real.log_nonneg (by
      have hm := Nat.cast_nonneg (α := ℝ) m
      have hn := Nat.cast_nonneg (α := ℝ) n
      linarith)) (by positivity)) fun m => ?_
  calc
    _ ≤ ((m + 1 : ℝ) + n) / (k : ℝ) ^ (m + 1) :=
      div_le_div_of_nonneg_right (Real.log_le_self (by positivity)) (by positivity)
    _ ≤ ((m + 1 : ℝ) + n) / (2 : ℝ) ^ (m + 1) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity)
        (pow_le_pow_left₀ (by norm_num) hk2 _)
    _ = _ := by push_cast; ring
@[expose] public section

/-- **Series formula and bound for the Göbel error.** Let $k, l \ge 2$ be natural numbers, let
$g_{k,l}$ be the $(k, l)$-Göbel sequence, and let $C$ be a real number such that the real numbers
$C_{k,l}(n) = g_{k,l}(n)^{1/k^n}$ tend to $C$ as $n \to \infty$. Then for every natural number
$n \ge 1$ the error

$$\varepsilon_{k,l}(n) = \sum_{m=1}^{\infty} \frac{\log(m + n)}{k^m} -
k^n \bigl(\log C_{k,l}(n) - \log C\bigr)$$

satisfies

$$\varepsilon_{k,l}(n) = \sum_{m=1}^{\infty} \frac{1}{k^m}
\log\Bigl(1 + \frac{m + n - 1}{g_{k,l}(m + n - 1)^{k-1}}\Bigr) \le \frac{2n}{C^{(k-1) k^n}}.$$

Source: Gima, Matsusaka, Miyazaki, and Yara, *On Integrality and Asymptotic
Behavior of the (k, l)-Göbel Sequences*, Journal of Integer Sequences 27 (2024),
Article 24.8.1, Lemma 12 (`jis-2024-24.8.1-lem-12`). -/
public theorem gobelSequence_error_eq_tsum_le (k l : ℕ) (hk : 2 ≤ k) (hl : 2 ≤ l) (C : ℝ)
    (hC : Tendsto (fun n : ℕ => (gobelSequence k l n : ℝ) ^ ((1 : ℝ) / (k : ℝ) ^ n))
      atTop (𝓝 C))
    (n : ℕ) (hn : 1 ≤ n) :
    (∑' m : ℕ, Real.log ((m + 1 : ℝ) + n) / (k : ℝ) ^ (m + 1))
        - (k : ℝ) ^ n * (Real.log ((gobelSequence k l n : ℝ) ^ ((1 : ℝ) / (k : ℝ) ^ n))
          - Real.log C)
      = ∑' m : ℕ, Real.log (1 + ((m + n : ℕ) : ℝ) / (gobelSequence k l (m + n) : ℝ) ^ (k - 1))
          / (k : ℝ) ^ (m + 1) ∧
    ∑' m : ℕ, Real.log (1 + ((m + n : ℕ) : ℝ) / (gobelSequence k l (m + n) : ℝ) ^ (k - 1))
          / (k : ℝ) ^ (m + 1)
      ≤ 2 * n / C ^ ((k - 1) * k ^ n)
     := by
  let a (m : ℕ) : ℝ := Real.log ((m + 1 : ℝ) + n) / (k : ℝ) ^ (m + 1)
  let e (m : ℕ) : ℝ := Real.log (1 + ((m + n : ℕ) : ℝ) /
    (gobelSequence k l (m + n) : ℝ) ^ (k - 1)) / (k : ℝ) ^ (m + 1)
  let d : ℝ := C ^ ((k - 1) * k ^ n)
  let b (m : ℕ) : ℝ := (((m : ℝ) + n) / (2 : ℝ) ^ (m + 1)) / d
  let f (m : ℕ) : ℝ := (k : ℝ) ^ n *
    Real.log ((gobelSequence k l (m + n) : ℝ) ^ (1 / (k : ℝ) ^ (m + n)))
  have hC1 := (root_bounds k l hk hl C hC n hn).1
  have hC0 : 0 < C := zero_lt_one.trans_le hC1
  have hd : 0 < d := pow_pos hC0 _
  have hb : HasSum b (((n : ℝ) + 1) / d) := (linear_hasSum n).div_const d
  have he0 (m : ℕ) : 0 ≤ e m := (correction_bound k l hk hl C hC n hn m).1
  have heb (m : ℕ) : e m ≤ b m := (correction_bound k l hk hl C hC n hn m).2
  have he : Summable e := hb.summable.of_nonneg_of_le he0 heb
  have ha : Summable a := log_summable k n hk
  have hid : (∑' m, a m) - (∑' m, e m) = (k : ℝ) ^ n *
      (Real.log ((gobelSequence k l n : ℝ) ^ ((1 : ℝ) / (k : ℝ) ^ n)) - Real.log C) :=
    gobelSequence_log_series_sub_correction_series hk hl hC hC0 hn ha he
  constructor
  · change (∑' m, a m) - (k : ℝ) ^ n *
        (Real.log ((gobelSequence k l n : ℝ) ^ (1 / (k : ℝ) ^ n)) - Real.log C) = ∑' m, e m
    linarith
  · change (∑' m, e m) ≤ 2 * n / d
    calc
      _ ≤ ∑' m, b m := he.tsum_le_tsum heb hb.summable
      _ = ((n : ℝ) + 1) / d := hb.tsum_eq
      _ ≤ 2 * n / d := div_le_div_of_nonneg_right
        (by exact_mod_cast (by omega : n + 1 ≤ 2 * n)) hd.le

end

end MetaMathlibExt

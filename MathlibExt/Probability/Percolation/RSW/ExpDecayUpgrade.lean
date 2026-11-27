/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Submultiplicative sequences: stretched-exponential decay implies exponential decay

A sequence `a : ℕ → [0, 1]` that is antitone and submultiplicative (`a (m + n) ≤ a m * a n`)
decays exponentially as soon as `a n₀ < 1` for some `n₀ > 0`; in particular stretched-exponential
decay `a n ≤ exp (-n ^ α)` upgrades to exponential decay. In percolation this is the step from
"some box-crossing or one-arm probability is small" to exponential decay, used in the
Duminil-Copin–Tassion dichotomy.

## Main results

* `StatMech.RSW.ExpDecay.rxd_submultiplicative_forces_exp_decay`: `a n₀ < 1` forces
  `a n ≤ C exp (-c n)`.
* `StatMech.RSW.ExpDecay.rxd_exp_decay_of_stretched`: stretched-exponential decay implies
  exponential decay for submultiplicative `a`.
* `StatMech.RSW.ExpDecay.rxd_exp_decay_literal`: for `α ≥ 1`, `exp (-n ^ α) ≤ exp (-n)` directly.

The hypothesis `hsub : ∀ m n, a (m + n) ≤ a m * a n` is Mathlib's `Submultiplicative a`; see also
`Submultiplicative` and `Subadditive` (Fekete's lemma) in `Mathlib/Analysis/Subadditive.lean`.
-/

@[expose] public section

open Real

namespace StatMech

namespace RSW

namespace ExpDecay

/-- For a submultiplicative sequence with `0 ≤ a` and `a 0 ≤ 1`, `a (k n₀) ≤ (a n₀) ^ k`.

See also `Submultiplicative.apply_mul_add_le` (Mathlib), `a (k n + r) ≤ a n ^ k * a r`. -/
theorem rxd_submul_pow (a : ℕ → ℝ) (hnn : ∀ n, 0 ≤ a n) (hle1 : a 0 ≤ 1)
    (hsub : ∀ m n, a (m + n) ≤ a m * a n) (n₀ : ℕ) :
    ∀ k, a (k * n₀) ≤ (a n₀) ^ k := by
  intro k
  induction k with
  | zero => simpa using hle1
  | succ k ih =>
    have hrw : (k + 1) * n₀ = n₀ + k * n₀ := by ring
    rw [hrw]
    calc a (n₀ + k * n₀) ≤ a n₀ * a (k * n₀) := hsub _ _
      _ ≤ a n₀ * (a n₀) ^ k := mul_le_mul_of_nonneg_left ih (hnn n₀)
      _ = (a n₀) ^ (k + 1) := by ring

/-- An antitone submultiplicative sequence in `[0, 1]` with `a n₀ < 1` for some `n₀ > 0` decays
exponentially: `a n ≤ C exp (-c n)` for some `c, C > 0`. -/
theorem rxd_submultiplicative_forces_exp_decay (a : ℕ → ℝ)
    (hnn : ∀ n, 0 ≤ a n) (hle1 : ∀ n, a n ≤ 1) (hanti : Antitone a)
    (hsub : ∀ m n, a (m + n) ≤ a m * a n)
    (n₀ : ℕ) (hn₀ : 0 < n₀) (hlt : a n₀ < 1) :
    ∃ c > 0, ∃ C > 0, ∀ n, a n ≤ C * Real.exp (-c * n) := by
  have hpow : ∀ k, a (k * n₀) ≤ (a n₀) ^ k :=
    rxd_submul_pow a hnn (hle1 0) hsub n₀
  set r : ℝ := max (a n₀) (1 / 2) with hr_def
  have hr0 : 0 < r := by rw [hr_def]; positivity
  have hr1 : r < 1 := by rw [hr_def]; exact max_lt hlt (by norm_num)
  have hsub' : ∀ k, a (k * n₀) ≤ r ^ k := fun k =>
    (hpow k).trans (pow_le_pow_left₀ (hnn n₀) (le_max_left _ _) k)
  have hL : 1 ≤ n₀ := hn₀
  have hlogr_neg : Real.log r < 0 := Real.log_neg hr0 hr1
  have hLpos : (0 : ℝ) < n₀ := by exact_mod_cast hL
  set c : ℝ := -(Real.log r) / n₀ with hc_def
  have hc_pos : 0 < c := by rw [hc_def]; exact div_pos (by linarith) hLpos
  refine ⟨c, hc_pos, r⁻¹, by positivity, fun n => ?_⟩
  set k := n / n₀ with hk_def
  have hfn : a n ≤ r ^ k := le_trans (hanti (Nat.div_mul_le_self n n₀)) (hsub' k)
  have hkpos_real : ((n : ℝ) / n₀ - 1) < (k : ℝ) := by
    have hnlt := Nat.lt_div_mul_add (a := n) (b := n₀) hL
    have hkk : (n : ℝ) < (k : ℝ) * n₀ + n₀ := by rw [hk_def]; exact_mod_cast hnlt
    rw [div_sub_one hLpos.ne', div_lt_iff₀ hLpos]; linarith
  have hrk : (r : ℝ) ^ (k : ℝ) = Real.exp ((k : ℝ) * Real.log r) := by
    rw [Real.rpow_def_of_pos hr0]; ring_nf
  have step2 : (r : ℝ) ^ k ≤ Real.exp (((n : ℝ) / n₀ - 1) * Real.log r) := by
    rw [show (r : ℝ) ^ k = r ^ (k : ℝ) from (Real.rpow_natCast r k).symm, hrk]
    exact Real.exp_le_exp.2 (mul_le_mul_of_nonpos_right hkpos_real.le hlogr_neg.le)
  have step3 :
      Real.exp (((n : ℝ) / n₀ - 1) * Real.log r) = r⁻¹ * Real.exp (-c * n) := by
    rw [sub_mul, one_mul, Real.exp_sub, hc_def,
        show -(-Real.log r / n₀) * (n : ℝ) = (n / n₀) * Real.log r from by ring,
        show Real.exp (Real.log r) = r from Real.exp_log hr0]
    ring
  calc a n ≤ r ^ k := hfn
    _ ≤ Real.exp (((n : ℝ) / n₀ - 1) * Real.log r) := step2
    _ = r⁻¹ * Real.exp (-c * n) := step3

/-- Stretched-exponential decay gives `a 1 ≤ exp (-1) < 1`. -/
theorem rxd_value_lt_one_of_stretched (a : ℕ → ℝ) (α : ℝ)
    (hstr : ∀ n, a n ≤ Real.exp (-(((n : ℝ)) ^ α))) :
    a 1 < 1 := by
  have h1 := hstr 1
  have he : (((1 : ℕ) : ℝ)) ^ α = 1 := by norm_num
  rw [he] at h1
  have hlt : Real.exp (-(1 : ℝ)) < 1 := by rw [Real.exp_lt_one_iff]; norm_num
  linarith

/-- For an antitone submultiplicative sequence in `[0, 1]`, stretched-exponential decay
`a n ≤ exp (-n ^ α)` implies exponential decay. (Only `a 1 < 1` is used, so `hα` is not needed.) -/
theorem rxd_exp_decay_of_stretched (a : ℕ → ℝ)
    (hnn : ∀ n, 0 ≤ a n) (hle1 : ∀ n, a n ≤ 1) (hanti : Antitone a)
    (α : ℝ) (_hα : 0 < α) (hstr : ∀ n, a n ≤ Real.exp (-(((n : ℝ)) ^ α)))
    (hsub : ∀ m n, a (m + n) ≤ a m * a n) :
    ∃ c > 0, ∃ C > 0, ∀ n, a n ≤ C * Real.exp (-c * n) :=
  rxd_submultiplicative_forces_exp_decay a hnn hle1 hanti hsub 1 Nat.one_pos
    (rxd_value_lt_one_of_stretched a α hstr)

/-- For `α ≥ 1`, the bound `a n ≤ exp (-n ^ α)` implies `a n ≤ exp (-n)`, without
submultiplicativity. -/
theorem rxd_exp_decay_literal (a : ℕ → ℝ)
    (α : ℝ) (hα : 1 ≤ α) (hstr : ∀ n, a n ≤ Real.exp (-(((n : ℝ)) ^ α))) :
    ∃ c > 0, ∀ n, a n ≤ Real.exp (-c * n) := by
  refine ⟨1, one_pos, fun n => ?_⟩
  refine (hstr n).trans (Real.exp_le_exp.2 ?_)
  have hle : (n : ℝ) ≤ (n : ℝ) ^ α := by
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      simpa using Real.rpow_nonneg (le_refl (0 : ℝ)) α
    · have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      exact self_le_rpow_of_one_le hn1 hα
  have hrw : -(1 : ℝ) * (n : ℝ) = -(n : ℝ) := by ring
  rw [hrw]
  linarith

end ExpDecay

end RSW

end StatMech

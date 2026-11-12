/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






















































import Mathlib

namespace StatMech.Universality

open Filter Topology
open scoped Topology



















def Submultiplicative (c : ℕ → ℝ) : Prop :=
  ∀ m n, c (m + n) ≤ c m * c n











theorem Subadditive_log_of_submultiplicative {c : ℕ → ℝ} (hpos : ∀ n, 0 < c n)
    (hsub : Submultiplicative c) : Subadditive (fun n => Real.log (c n)) := by
  intro m n
  have hmn : c (m + n) ≤ c m * c n := hsub m n
  calc
    Real.log (c (m + n)) ≤ Real.log (c m * c n) :=
      Real.log_le_log (hpos (m + n)) hmn
    _ = Real.log (c m) + Real.log (c n) :=
      Real.log_mul (hpos m).ne' (hpos n).ne'











theorem fekete_tendsto {x : ℕ → ℝ} (h : Subadditive x)
    (hbdd : BddBelow (Set.range fun n => x n / n)) :
    Tendsto (fun n => x n / n) atTop (𝓝 h.lim) :=
  h.tendsto_lim hbdd




theorem fekete_lim_eq_iInf {x : ℕ → ℝ} (h : Subadditive x) :
    h.lim = sInf ((fun n : ℕ => x n / n) '' Set.Ici 1) := by
  rw [Subadditive.lim]




theorem fekete_lim_le {x : ℕ → ℝ} (h : Subadditive x)
    (hbdd : BddBelow (Set.range fun n => x n / n)) {n : ℕ} (hn : n ≠ 0) :
    h.lim ≤ x n / n :=
  h.lim_le_div hbdd hn











theorem bddBelow_log_div {c : ℕ → ℝ} (hge : ∀ n, 1 ≤ c n) :
    BddBelow (Set.range fun n => Real.log (c n) / n) := by
  refine ⟨0, ?_⟩
  rintro y ⟨n, rfl⟩
  exact div_nonneg (Real.log_nonneg (hge n)) (Nat.cast_nonneg n)






theorem connectiveConstant_log_tendsto {c : ℕ → ℝ} (hge : ∀ n, 1 ≤ c n)
    (hsub : Submultiplicative c) :
    ∃ L : ℝ, Tendsto (fun n => Real.log (c n) / n) atTop (𝓝 L) := by
  have hpos : ∀ n, 0 < c n := fun n => zero_lt_one.trans_le (hge n)
  have hadd : Subadditive (fun n => Real.log (c n)) :=
    Subadditive_log_of_submultiplicative hpos hsub
  exact ⟨hadd.lim, fekete_tendsto hadd (bddBelow_log_div hge)⟩




theorem connectiveConstant_log_eq_iInf {c : ℕ → ℝ} (hge : ∀ n, 1 ≤ c n)
    (hsub : Submultiplicative c) :
    (Subadditive_log_of_submultiplicative
        (fun n => zero_lt_one.trans_le (hge n)) hsub).lim
      = sInf ((fun n : ℕ => Real.log (c n) / n) '' Set.Ici 1) :=
  fekete_lim_eq_iInf _






theorem connectiveConstant_tendsto {c : ℕ → ℝ} (hge : ∀ n, 1 ≤ c n)
    (hsub : Submultiplicative c) :
    ∃ κ : ℝ, 0 < κ ∧
      Tendsto (fun n => (c n) ^ ((n : ℝ)⁻¹)) atTop (𝓝 κ) := by
  obtain ⟨L, hL⟩ := connectiveConstant_log_tendsto hge hsub
  refine ⟨Real.exp L, Real.exp_pos L, ?_⟩
  
  have hpos : ∀ n, 0 < c n := fun n => zero_lt_one.trans_le (hge n)
  have hcont : Tendsto (fun y : ℝ => Real.exp y) (𝓝 L) (𝓝 (Real.exp L)) :=
    (Real.continuous_exp.tendsto L)
  have hcomp : Tendsto (fun n => Real.exp (Real.log (c n) / n)) atTop
      (𝓝 (Real.exp L)) := hcont.comp hL
  refine hcomp.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  rw [Real.rpow_def_of_pos (hpos n), Real.exp_eq_exp, div_eq_inv_mul, mul_comm]

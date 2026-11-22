/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.ModularForms.JacobiTheta.Ramanujan

import Mathlib.Analysis.SpecificLimits.Basic

@[expose] public section

open scoped Topology

namespace MetaMathlibExt

/-- **Absolute convergence of Ramanujan's general theta series.** For all complex numbers $a$
and $b$ with $|ab| < 1$, the series $\sum_{n \in \mathbb{Z}} |a^{n(n+1)/2} b^{n(n-1)/2}|$ of
the absolute values of the terms of Ramanujan's general theta function converges.

Source: arXiv:2607.26471, `Oliver_identities.tex` ll. 127-130. -/
theorem ramanujanTheta_summable (a b : ℂ) (h : ‖a * b‖ < 1) :
    Summable (fun n : ℤ => ‖ramanujanThetaTerm a b n‖) := by
  have machine : ∀ (x y : ℂ), ‖x * y‖ < 1 →
      Summable (fun n : ℕ => ‖ramanujanThetaTerm x y ((n : ℕ) : ℤ)‖) := by
    intro x y hxy
    have hterm : ∀ n : ℕ, ‖ramanujanThetaTerm x y ((n : ℕ) : ℤ)‖ =
        ‖x‖ ^ (((n : ℤ) * ((n : ℤ) + 1) / 2).toNat) *
        ‖y‖ ^ (((n : ℤ) * ((n : ℤ) - 1) / 2).toNat) := by
      intro n
      unfold ramanujanThetaTerm
      rw [Complex.norm_mul, Complex.norm_pow, Complex.norm_pow]
    have hcast : ∀ n : ℕ, ((n + 1 : ℕ) : ℤ) = (n : ℤ) + 1 := by
      intro n
      omega
    have hE1 : ∀ n : ℕ, (((n : ℤ) + 1) * (((n : ℤ) + 1) + 1) / 2).toNat =
        (((n : ℤ) * ((n : ℤ) + 1) / 2).toNat) + (n + 1) := by
      intro n
      have hring : ((n : ℤ) + 1) * (((n : ℤ) + 1) + 1) =
          (n : ℤ) * ((n : ℤ) + 1) + 2 * ((n : ℤ) + 1) := by
        ring
      have hdiv : ((n : ℤ) + 1) * (((n : ℤ) + 1) + 1) / 2 =
          (n : ℤ) * ((n : ℤ) + 1) / 2 + ((n : ℤ) + 1) := by
        rw [hring]
        exact Int.add_mul_ediv_left _ _ (by norm_num)
      have hprod : 0 ≤ (n : ℤ) * ((n : ℤ) + 1) := by
        positivity
      have hqnn : 0 ≤ (n : ℤ) * ((n : ℤ) + 1) / 2 :=
        Int.ediv_nonneg hprod (by norm_num)
      have hn1 : 0 ≤ ((n : ℤ) + 1) := by
        omega
      have htn : (((n : ℤ) + 1)).toNat = n + 1 := by
        rw [← hcast n]
        simp
      rw [hdiv, Int.toNat_add hqnn hn1, htn]
    have hE2 : ∀ n : ℕ, (((n : ℤ) + 1) * (((n : ℤ) + 1) - 1) / 2).toNat =
        (((n : ℤ) * ((n : ℤ) - 1) / 2).toNat) + n := by
      intro n
      by_cases hn : n = 0
      · subst hn
        decide
      · obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
        have hc : (((k + 1 : ℕ)) : ℤ) = (k : ℤ) + 1 := by
          omega
        rw [hc]
        have hring : (((k : ℤ) + 1) + 1) * ((((k : ℤ) + 1) + 1) - 1) =
            ((k : ℤ) + 1) * (((k : ℤ) + 1) - 1) + 2 * ((k : ℤ) + 1) := by
          ring
        have hdiv : (((k : ℤ) + 1) + 1) * ((((k : ℤ) + 1) + 1) - 1) / 2 =
            ((k : ℤ) + 1) * (((k : ℤ) + 1) - 1) / 2 + ((k : ℤ) + 1) := by
          rw [hring]
          exact Int.add_mul_ediv_left _ _ (by norm_num)
        have hsub : (((k : ℤ) + 1) - 1) = (k : ℤ) := by
          omega
        have hprod : 0 ≤ ((k : ℤ) + 1) * (((k : ℤ) + 1) - 1) := by
          rw [hsub]
          positivity
        have hqnn : 0 ≤ ((k : ℤ) + 1) * (((k : ℤ) + 1) - 1) / 2 :=
          Int.ediv_nonneg hprod (by norm_num)
        have hA1 : 0 ≤ ((k : ℤ) + 1) := by
          omega
        have htn : (((k : ℤ) + 1)).toNat = k + 1 := by
          rw [← hc]
          simp
        rw [hdiv, Int.toNat_add hqnn hA1, htn]
    have hrec : ∀ n : ℕ, ‖ramanujanThetaTerm x y ((n : ℤ) + 1)‖ =
        ‖ramanujanThetaTerm x y (n : ℤ)‖ *
        (‖x‖ ^ (n + 1) * ‖y‖ ^ n) := by
      intro n
      rw [← hcast n, hterm (n + 1), hterm n, hcast n, hE1 n, hE2 n,
        pow_add, pow_add]
      ring
    have hq : ‖x‖ * ‖y‖ < 1 := by
      have h2 := hxy
      rw [Complex.norm_mul] at h2
      exact h2
    have hq0 : (0 : ℝ) ≤ ‖x‖ * ‖y‖ := by
      positivity
    have hfactor : ∀ n : ℕ, ‖x‖ ^ (n + 1) * ‖y‖ ^ n =
        ‖x‖ * (‖x‖ * ‖y‖) ^ n := by
      intro n
      ring
    have hqpow : Filter.Tendsto (fun n : ℕ => (‖x‖ * ‖y‖) ^ n)
        Filter.atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq
    have hconst : Filter.Tendsto (fun _ : ℕ => ‖x‖)
        Filter.atTop (𝓝 ‖x‖) :=
      tendsto_const_nhds
    have hgr0 : Filter.Tendsto (fun n : ℕ => ‖x‖ * (‖x‖ * ‖y‖) ^ n)
        Filter.atTop (𝓝 (‖x‖ * 0)) :=
      hconst.mul hqpow
    have hr0 : ‖x‖ * (0 : ℝ) = 0 := by
      ring
    have hgr : Filter.Tendsto (fun n : ℕ => ‖x‖ * (‖x‖ * ‖y‖) ^ n)
        Filter.atTop (𝓝 0) := by
      rw [hr0] at hgr0
      exact hgr0
    have hρ0 : (0 : ℝ) ≤ 1 / 2 := by
      norm_num
    have hρ1 : (1 : ℝ) / 2 < 1 := by
      norm_num
    have hρpos : (0 : ℝ) < 1 / 2 := by
      norm_num
    have hev : ∀ᶠ n : ℕ in Filter.atTop,
        ‖x‖ * (‖x‖ * ‖y‖) ^ n < 1 / 2 :=
      hgr.eventually (Iio_mem_nhds hρpos)
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hev
    have hle : ∀ m : ℕ, N ≤ m → ‖x‖ ^ (m + 1) * ‖y‖ ^ m ≤ 1 / 2 := by
      intro m hm
      rw [hfactor m]
      exact le_of_lt (hN m hm)
    have hbound : ∀ k : ℕ, ‖ramanujanThetaTerm x y ((N + k : ℕ) : ℤ)‖ ≤
        ‖ramanujanThetaTerm x y ((N : ℕ) : ℤ)‖ * (1 / 2 : ℝ) ^ k := by
      intro k
      induction k with
      | zero =>
        simp
      | succ k ih =>
        have hc2 : ((N + (k + 1) : ℕ) : ℤ) = ((N + k : ℕ) : ℤ) + 1 := by
          omega
        rw [hc2, hrec (N + k)]
        have gF : (0 : ℝ) ≤ ‖x‖ ^ (N + k + 1) * ‖y‖ ^ (N + k) := by
          positivity
        have gC : (0 : ℝ) ≤ ‖ramanujanThetaTerm x y ((N : ℕ) : ℤ)‖ *
            (1 / 2 : ℝ) ^ k := by
          positivity
        have g2 : ‖x‖ ^ (N + k + 1) * ‖y‖ ^ (N + k) ≤ 1 / 2 :=
          hle (N + k) (by omega)
        calc ‖ramanujanThetaTerm x y ((N + k : ℕ) : ℤ)‖ *
                (‖x‖ ^ (N + k + 1) * ‖y‖ ^ (N + k))
            ≤ (‖ramanujanThetaTerm x y ((N : ℕ) : ℤ)‖ * (1 / 2 : ℝ) ^ k) *
                (‖x‖ ^ (N + k + 1) * ‖y‖ ^ (N + k)) := by
              gcongr
          _ ≤ (‖ramanujanThetaTerm x y ((N : ℕ) : ℤ)‖ * (1 / 2 : ℝ) ^ k) *
              (1 / 2) := by
              gcongr
          _ = ‖ramanujanThetaTerm x y ((N : ℕ) : ℤ)‖ *
              (1 / 2 : ℝ) ^ (k + 1) := by
              ring
    have hshift : Summable (fun k : ℕ =>
        ‖ramanujanThetaTerm x y ((N : ℕ) : ℤ)‖ * (1 / 2 : ℝ) ^ k) :=
      (summable_geometric_of_lt_one hρ0 hρ1).mul_left _
    have hf0 : ∀ k : ℕ, (0 : ℝ) ≤
        ‖ramanujanThetaTerm x y ((N + k : ℕ) : ℤ)‖ := by
      intro k
      positivity
    have htail : Summable (fun k : ℕ =>
        ‖ramanujanThetaTerm x y ((N + k : ℕ) : ℤ)‖) :=
      Summable.of_nonneg_of_le hf0 hbound hshift
    have htailNat : Summable (fun n : ℕ =>
        ‖ramanujanThetaTerm x y ((n + N : ℕ) : ℤ)‖) := by
      have heq : (fun n : ℕ =>
          ‖ramanujanThetaTerm x y ((n + N : ℕ) : ℤ)‖) =
          (fun k : ℕ =>
            ‖ramanujanThetaTerm x y ((N + k : ℕ) : ℤ)‖) := by
        funext k
        show ‖ramanujanThetaTerm x y ((k + N : ℕ) : ℤ)‖ =
          ‖ramanujanThetaTerm x y ((N + k : ℕ) : ℤ)‖
        rw [Nat.add_comm k N]
      rw [heq]
      exact htail
    have hfull : Summable
        (fun n : ℕ => ‖ramanujanThetaTerm x y ((n : ℕ) : ℤ)‖) :=
      (summable_nat_add_iff N).mp htailNat
    exact hfull
  have hba : ‖b * a‖ < 1 := by
    rw [mul_comm b a]
    exact h
  have hneg : Summable
      (fun n : ℕ => ‖ramanujanThetaTerm a b (-((n : ℕ) : ℤ))‖) := by
    simpa only [ramanujanThetaTerm_neg] using machine b a hba
  exact Summable.of_nat_of_neg (machine a b h) hneg

end MetaMathlibExt

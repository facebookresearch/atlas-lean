/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.FinitePrefixStopping

import Mathlib.Tactic

open scoped ENNReal

open Filter Topology

/-!
# Uniform EOS: geometric tail and certain termination

If the EOS probability is bounded below by a uniform `ε` at every
ordinary prefix, the defective survival mass of `FinitePrefixStopping`
dies geometrically: `survivalMass q n ≤ (1 - ε) ^ n`
(`survivalMass_le_pow_of_uniformEOS`), so it tends to `0`
(`tendsto_survivalMass_of_uniformEOS`) and the total terminated mass is
exactly `1` when `0 < ε` (`totalTerminatedMass_eq_one_of_uniformEOS`,
packaged as `uniformEOS_termination`). Pointwise positivity of the EOS
probability does not suffice: the tests include kernels with EOS
probability `0` and with positive-but-nonuniform EOS probability where
the conclusion fails.
-/

@[expose] public section

namespace MathlibExt.Probability.FinitePrefix


/-- Under a uniform lower bound `ε` on the EOS probability at every ordinary
prefix, the mass of surviving `n` steps without EOS is at most `(1 - ε) ^ n`. -/
theorem survivalMass_le_pow_of_uniformEOS {Token : Type*} [Fintype Token]
    (q : List Token → PMF (Option Token)) (ε : ℝ≥0∞)
    (hEOS : ∀ w : List Token, ε ≤ eosProb q w) (n : ℕ) :
    survivalMass q n ≤ (1 - ε) ^ n := by
  have hnorm : ∀ (p : List Token → PMF (Option Token)),
      eosProb p []
        + Finset.sum Finset.univ (fun a => p [] (Option.some a)) = 1 := by
    intro p
    have h := PMF.tsum_coe (p [])
    rw [tsum_fintype] at h
    rw [Fintype.sum_option] at h
    exact h
  induction n generalizing q with
  | zero =>
      have h0 : survivalMass q 0 = 1 := rfl
      rw [h0, pow_zero]
  | succ n ih =>
      rw [survivalMass_succ]
      have hstep : ∀ (a : Token),
          q [] (Option.some a) * survivalMass (fun p => q (a :: p)) n
            ≤ q [] (Option.some a) * (1 - ε) ^ n := by
        intro a
        exact mul_le_mul_right
          (ih (fun p => q (a :: p)) (fun w => hEOS (a :: w))) _
      calc Finset.sum Finset.univ
              (fun a => q [] (Option.some a)
                * survivalMass (fun p => q (a :: p)) n)
          ≤ Finset.sum Finset.univ
              (fun a => q [] (Option.some a) * (1 - ε) ^ n) :=
            Finset.sum_le_sum (fun a _ => hstep a)
        _ = (Finset.sum Finset.univ (fun a => q [] (Option.some a)))
              * (1 - ε) ^ n := (Finset.sum_mul _ _ _).symm
        _ ≤ (1 - ε) * (1 - ε) ^ n := by
            apply mul_le_mul_left _ _
            have he1 : eosProb q [] ≤ 1 := by
              rw [← hnorm q]
              exact le_add_right le_rfl
            have hεtop : ε ≠ ∞ :=
              ne_top_of_le_ne_top ENNReal.one_ne_top (le_trans (hEOS []) he1)
            have hle : ε
                  + Finset.sum Finset.univ (fun a => q [] (Option.some a)) ≤ 1 := by
              rw [← hnorm q]
              exact add_le_add_left (hEOS []) _
            exact ENNReal.le_sub_of_add_le_left hεtop hle
        _ = (1 - ε) ^ (n + 1) := (pow_succ' _ _).symm

/-- Under a positive uniform lower bound on the EOS probability, the survival
mass tends to zero. -/
theorem tendsto_survivalMass_of_uniformEOS {Token : Type*} [Fintype Token]
    (q : List Token → PMF (Option Token)) (ε : ℝ≥0∞) (hε : 0 < ε)
    (hEOS : ∀ w : List Token, ε ≤ eosProb q w) :
    Tendsto (fun n => survivalMass q n) atTop (𝓝 0) := by
  have hlt : (1 : ℝ≥0∞) - ε < 1 :=
    ENNReal.sub_lt_self ENNReal.one_ne_top one_ne_zero (ne_of_gt hε)
  have hpow := ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one hlt
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hpow _ _
  · intro n
    exact zero_le
  · intro n
    exact survivalMass_le_pow_of_uniformEOS q ε hEOS n

/-- Under a positive uniform lower bound on the EOS probability, the terminated
finite strings carry total mass one. -/
theorem totalTerminatedMass_eq_one_of_uniformEOS {Token : Type*} [Fintype Token]
    (q : List Token → PMF (Option Token)) (ε : ℝ≥0∞) (hε : 0 < ε)
    (hEOS : ∀ w : List Token, ε ≤ eosProb q w) :
    totalTerminatedMass q = 1 := by
  have hTend0 := tendsto_survivalMass_of_uniformEOS q ε hε hEOS
  have hpart : ∀ (N : ℕ),
      Finset.sum (Finset.range N) (fun k => stopMass q k)
        = 1 - survivalMass q N := by
    intro N
    have hbal := partial_mass_balance q N
    have h1 : (1 : ℝ≥0∞) = survivalMass q N
        + Finset.sum (Finset.range N) (fun k => stopMass q k) := by
      rw [add_comm]
      exact hbal.symm
    exact (ENNReal.sub_eq_of_eq_add_rev' ENNReal.one_ne_top h1).symm
  have hOne : Tendsto
      (fun N => Finset.sum (Finset.range N) (fun k => stopMass q k))
      atTop (𝓝 1) := by
    simp only [hpart]
    have hsub := ENNReal.tendsto_sub (a := (1 : ℝ≥0∞)) (b := (0 : ℝ≥0∞))
      (Or.inl ENNReal.one_ne_top)
    have hpair : Tendsto (fun N => ((1 : ℝ≥0∞), survivalMass q N)) atTop
        (𝓝 (1, 0)) :=
      tendsto_const_nhds.prodMk_nhds hTend0
    have hcomp : Tendsto (fun N => (1 : ℝ≥0∞) - survivalMass q N) atTop
        (𝓝 (1 - 0)) :=
      hsub.comp hpair
    simpa using hcomp
  have hHas : HasSum (fun k => stopMass q k) 1 :=
    (ENNReal.hasSum_iff_tendsto_nat 1).mpr hOne
  exact hHas.tsum_eq

/-- Uniform EOS termination: if the EOS probability is at least `ε > 0` at every
ordinary prefix, then the survival mass satisfies `s n ≤ (1 - ε) ^ n` for every
`n`, and the total mass of terminated finite strings is one. -/
theorem uniformEOS_termination {Token : Type*} [Fintype Token]
    (q : List Token → PMF (Option Token)) (ε : ℝ≥0∞) (hε : 0 < ε)
    (hEOS : ∀ w : List Token, ε ≤ eosProb q w) :
    (∀ n : ℕ, survivalMass q n ≤ (1 - ε) ^ n)
      ∧ totalTerminatedMass q = 1 := by
  exact ⟨fun n => survivalMass_le_pow_of_uniformEOS q ε hEOS n,
    totalTerminatedMass_eq_one_of_uniformEOS q ε hε hEOS⟩
end MathlibExt.Probability.FinitePrefix

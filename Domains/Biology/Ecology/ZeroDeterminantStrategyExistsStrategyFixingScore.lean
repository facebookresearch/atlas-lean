/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Basic.Real.Basic
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Order.Interval.Set.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FinCases
public import Domains.Biology.Ecology.ZeroDeterminantStrategyDotProductEqDivPdDet

/-!
# In the Prisoner's Dilemma X can fix any score of Y

This module defines Y's payoffs `payoffY` and proves that for `T > R > P > S` and every
`σ ∈ [P, R]` there is a memory-one strategy fixing Y's long-run score at `σ`
(`exists_strategy_fixing_score`). Memory-one strategies `IsStrategy`, Y's view `yView`, the
Markov matrix `markovMatrix`, stationary distributions `IsStationary`, the columns `pTilde`
and `qTilde` and the Press–Dyson determinant `pdDet` come from
`Domains.Biology.Ecology.ZeroDeterminantStrategyDotProductEqDivPdDet`.

Sources: W. H. Press and F. J. Dyson, "Iterated Prisoner's Dilemma contains strategies that
dominate any evolutionary opponent", Proc. Natl. Acad. Sci. USA 109 (2012) 10409–10413,
"Zero-determinant strategies", eqs. (1)–(7), and "X unilaterally sets Y's score", eqs. (8)–(10).
-/

@[expose] public section

namespace WantedExt.Biology.Ecology.ZeroDeterminantStrategyWanted

open Matrix Set

/-- Y's stage payoffs `S_Y = (R, T, S, P)` over `cc, cd, dc, dd` (seen from X). -/
def payoffY (R S T P : ℝ) : Fin 4 → ℝ :=
  ![R, T, S, P]

private theorem markov_sum (p q : Fin 4 → ℝ) (s : Fin 4) :
    markovMatrix p q s 0 + markovMatrix p q s 1 = p s := by
  simp only [markovMatrix, Matrix.of_apply]
  simp
  ring

private theorem dot_pTilde_eq_zero (p q v : Fin 4 → ℝ)
    (hv : IsStationary (markovMatrix p q) v) : v ⬝ᵥ pTilde p = 0 := by
  have hvm := hv.1
  have h0 : (v ᵥ* markovMatrix p q) 0 = v 0 := by rw [hvm]
  have h1 : (v ᵥ* markovMatrix p q) 1 = v 1 := by rw [hvm]
  simp only [Matrix.vecMul, dotProduct, Fin.sum_univ_four] at h0 h1
  have r0 := markov_sum p q 0
  have r1 := markov_sum p q 1
  have r2 := markov_sum p q 2
  have r3 := markov_sum p q 3
  have e0 : v 0 * p 0 = v 0 * markovMatrix p q 0 0 + v 0 * markovMatrix p q 0 1 := by
    rw [← r0, mul_add]
  have e1 : v 1 * p 1 = v 1 * markovMatrix p q 1 0 + v 1 * markovMatrix p q 1 1 := by
    rw [← r1, mul_add]
  have e2 : v 2 * p 2 = v 2 * markovMatrix p q 2 0 + v 2 * markovMatrix p q 2 1 := by
    rw [← r2, mul_add]
  have e3 : v 3 * p 3 = v 3 * markovMatrix p q 3 0 + v 3 * markovMatrix p q 3 1 := by
    rw [← r3, mul_add]
  have hsum : v 0 * p 0 + v 1 * p 1 + v 2 * p 2 + v 3 * p 3 = v 0 + v 1 := by
    rw [e0, e1, e2, e3]
    linarith [h0, h1]
  have hpt0 : pTilde p 0 = -1 + p 0 := by simp [pTilde]
  have hpt1 : pTilde p 1 = -1 + p 1 := by simp [pTilde]
  have hpt2 : pTilde p 2 = p 2 := by simp [pTilde]
  have hpt3 : pTilde p 3 = p 3 := by simp [pTilde]
  have hdot : v ⬝ᵥ pTilde p =
      v 0 * pTilde p 0 + v 1 * pTilde p 1 + v 2 * pTilde p 2 + v 3 * pTilde p 3 := by
    simp [dotProduct, Fin.sum_univ_four, add_assoc]
  rw [hdot, hpt0, hpt1, hpt2, hpt3]
  linarith [hsum]

private theorem pdDet_zero_eq (p : Fin 4 → ℝ) : pdDet p 0 1 = p 1 - 1 - p 3 := by
  simp [pdDet, Matrix.det_succ_column_zero, Fin.sum_univ_succ, Fin.succAbove, pTilde, qTilde]
  ring

/-- **In the Prisoner's Dilemma X can fix any score `P ≤ σ ≤ R` of Y** (Press and Dyson 2012,
eqs. (8)–(9)). If `T > R > P > S`, then for every `σ` with `P ≤ σ ≤ R` there is a
memory-one strategy `p` that is an equalizer for `σ`:
`p₂ = (p₁ (T - P) - (1 + p₄)(T - R)) / (R - P)`, `p₃ = ((1 - p₁)(P - S) + p₄ (R - S)) / (R - P)`,
`(1 - p₁) + p₄ ≠ 0` and
`((1 - p₁) P + p₄ R) / ((1 - p₁) + p₄) = σ`; that is nondegenerate, in that some memory-one
strategy `q` has `D(p, q, 1) ≠ 0`; and such that for every memory-one strategy `q` and every
stationary distribution `v` of `M(p, q)`, `v · S_Y = σ`.

Source: Press and Dyson (2012), "X unilaterally sets Y's score", eqs. (8)–(9). -/
public theorem exists_strategy_fixing_score {R S T P : ℝ} (hTR : R < T) (hRP : P < R)
    (hPS : S < P) (σ : ℝ) (hσ : σ ∈ Icc P R) :
    ∃ p : Fin 4 → ℝ, IsStrategy p ∧
      p 1 = (p 0 * (T - P) - (1 + p 3) * (T - R)) / (R - P) ∧
      p 2 = ((1 - p 0) * (P - S) + p 3 * (R - S)) / (R - P) ∧
      (1 - p 0) + p 3 ≠ 0 ∧ ((1 - p 0) * P + p 3 * R) / ((1 - p 0) + p 3) = σ ∧
      (∃ q : Fin 4 → ℝ, IsStrategy q ∧ pdDet p q 1 ≠ 0) ∧
      ∀ q : Fin 4 → ℝ, IsStrategy q → ∀ v : Fin 4 → ℝ,
        IsStationary (markovMatrix p q) v → v ⬝ᵥ payoffY R S T P = σ := by
  have hPσ : P ≤ σ := hσ.1
  have hσR : σ ≤ R := hσ.2
  have hST : S < T := lt_trans hPS (lt_trans hRP hTR)
  have hTSpos : 0 < T - S := sub_pos.mpr hST
  have hTSne : T - S ≠ 0 := sub_ne_zero.mpr (ne_of_gt hST)
  have hRPne : R - P ≠ 0 := sub_ne_zero.mpr (ne_of_gt hRP)
  have hTPne : T - P ≠ 0 := sub_ne_zero.mpr (ne_of_gt (lt_trans hRP hTR))
  refine ⟨![1 - (R - σ) / (T - S), 1 - (T - σ) / (T - S), (σ - S) / (T - S),
    (σ - P) / (T - S)], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    fin_cases i
    · change 0 ≤ 1 - (R - σ) / (T - S) ∧ 1 - (R - σ) / (T - S) ≤ 1
      refine ⟨?_, ?_⟩
      · have h1 : (R - σ) / (T - S) ≤ 1 := by
          rw [div_le_one hTSpos]
          linarith
        linarith
      · have h2 : 0 ≤ (R - σ) / (T - S) := by
          apply div_nonneg _ hTSpos.le
          linarith
        linarith
    · change 0 ≤ 1 - (T - σ) / (T - S) ∧ 1 - (T - σ) / (T - S) ≤ 1
      refine ⟨?_, ?_⟩
      · have h1 : (T - σ) / (T - S) ≤ 1 := by
          rw [div_le_one hTSpos]
          linarith
        linarith
      · have h2 : 0 ≤ (T - σ) / (T - S) := by
          apply div_nonneg _ hTSpos.le
          linarith
        linarith
    · change 0 ≤ (σ - S) / (T - S) ∧ (σ - S) / (T - S) ≤ 1
      refine ⟨?_, ?_⟩
      · apply div_nonneg _ hTSpos.le
        linarith
      · rw [div_le_one hTSpos]
        linarith
    · change 0 ≤ (σ - P) / (T - S) ∧ (σ - P) / (T - S) ≤ 1
      refine ⟨?_, ?_⟩
      · apply div_nonneg _ hTSpos.le
        linarith
      · rw [div_le_one hTSpos]
        linarith
  · simp
    field_simp
    ring
  · simp
    field_simp
    ring
  · change 1 - (1 - (R - σ) / (T - S)) + (σ - P) / (T - S) ≠ 0
    rw [sub_sub_cancel]
    have hD : (R - σ) / (T - S) + (σ - P) / (T - S) = (R - P) / (T - S) := by
      field_simp
      ring
    rw [hD]
    exact div_ne_zero hRPne hTSne
  · change ((1 - (1 - (R - σ) / (T - S))) * P + (σ - P) / (T - S) * R) /
        ((1 - (1 - (R - σ) / (T - S))) + (σ - P) / (T - S)) = σ
    rw [sub_sub_cancel]
    have hD : (R - σ) / (T - S) + (σ - P) / (T - S) = (R - P) / (T - S) := by
      field_simp
      ring
    have hDne : (R - σ) / (T - S) + (σ - P) / (T - S) ≠ 0 := by
      rw [hD]
      exact div_ne_zero hRPne hTSne
    have hNum : (R - σ) / (T - S) * P + (σ - P) / (T - S) * R = σ * ((R - P) / (T - S)) := by
      field_simp
      ring
    rw [div_eq_iff hDne, hNum, hD]
  · refine ⟨0, ?_, ?_⟩
    · intro i
      simp only [Pi.zero_apply]
      exact ⟨le_rfl, zero_le_one⟩
    · rw [pdDet_zero_eq]
      change 1 - (T - σ) / (T - S) - 1 - (σ - P) / (T - S) ≠ 0
      rw [show 1 - (T - σ) / (T - S) - 1 = -((T - σ) / (T - S)) by ring]
      have heq : -((T - σ) / (T - S)) - (σ - P) / (T - S) = -((T - P) / (T - S)) := by
        field_simp
        ring
      rw [heq]
      exact neg_ne_zero.mpr (div_ne_zero hTPne hTSne)
  · intro q _hq v hv
    have hdot0 : v ⬝ᵥ pTilde ![1 - (R - σ) / (T - S), 1 - (T - σ) / (T - S), (σ - S) / (T - S),
        (σ - P) / (T - S)] = 0 :=
      dot_pTilde_eq_zero _ _ _ hv
    have hpt0 : pTilde ![1 - (R - σ) / (T - S), 1 - (T - σ) / (T - S), (σ - S) / (T - S),
        (σ - P) / (T - S)] 0 = -1 + (1 - (R - σ) / (T - S)) := by
      simp [pTilde]
    have hpt1 : pTilde ![1 - (R - σ) / (T - S), 1 - (T - σ) / (T - S), (σ - S) / (T - S),
        (σ - P) / (T - S)] 1 = -1 + (1 - (T - σ) / (T - S)) := by
      simp [pTilde]
    have hpt2 : pTilde ![1 - (R - σ) / (T - S), 1 - (T - σ) / (T - S), (σ - S) / (T - S),
        (σ - P) / (T - S)] 2 = (σ - S) / (T - S) := by
      simp [pTilde]
    have hpt3 : pTilde ![1 - (R - σ) / (T - S), 1 - (T - σ) / (T - S), (σ - S) / (T - S),
        (σ - P) / (T - S)] 3 = (σ - P) / (T - S) := by
      simp [pTilde]
    have hsy0 : payoffY R S T P 0 = R := by simp [payoffY]
    have hsy1 : payoffY R S T P 1 = T := by simp [payoffY]
    have hsy2 : payoffY R S T P 2 = S := by simp [payoffY]
    have hsy3 : payoffY R S T P 3 = P := by simp [payoffY]
    have hdot : v ⬝ᵥ pTilde ![1 - (R - σ) / (T - S), 1 - (T - σ) / (T - S), (σ - S) / (T - S),
          (σ - P) / (T - S)] =
        v 0 * pTilde ![1 - (R - σ) / (T - S), 1 - (T - σ) / (T - S), (σ - S) / (T - S),
          (σ - P) / (T - S)] 0 +
        v 1 * pTilde ![1 - (R - σ) / (T - S), 1 - (T - σ) / (T - S), (σ - S) / (T - S),
          (σ - P) / (T - S)] 1 +
        v 2 * pTilde ![1 - (R - σ) / (T - S), 1 - (T - σ) / (T - S), (σ - S) / (T - S),
          (σ - P) / (T - S)] 2 +
        v 3 * pTilde ![1 - (R - σ) / (T - S), 1 - (T - σ) / (T - S), (σ - S) / (T - S),
          (σ - P) / (T - S)] 3 := by
      simp [dotProduct, Fin.sum_univ_four, add_assoc]
    have hdotY : v ⬝ᵥ payoffY R S T P = v 0 * payoffY R S T P 0 + v 1 * payoffY R S T P 1 +
        v 2 * payoffY R S T P 2 + v 3 * payoffY R S T P 3 := by
      simp [dotProduct, Fin.sum_univ_four, add_assoc]
    have hsum4 : v 0 + v 1 + v 2 + v 3 = 1 := by
      have hsum := hv.2.2
      simp [Fin.sum_univ_four, add_assoc] at hsum
      linarith
    rw [hdot, hpt0, hpt1, hpt2, hpt3] at hdot0
    rw [hdotY, hsy0, hsy1, hsy2, hsy3]
    have hmul := congrArg (fun x => x * (T - S)) hdot0
    simp only [add_mul] at hmul
    have e0 : v 0 * (-1 + (1 - (R - σ) / (T - S))) * (T - S) = -(v 0 * (R - σ)) := by
      field_simp
      ring
    have e1 : v 1 * (-1 + (1 - (T - σ) / (T - S))) * (T - S) = -(v 1 * (T - σ)) := by
      field_simp
      ring
    have e2 : v 2 * ((σ - S) / (T - S)) * (T - S) = v 2 * (σ - S) := by
      field_simp
    have e3 : v 3 * ((σ - P) / (T - S)) * (T - S) = v 3 * (σ - P) := by
      field_simp
    rw [e0, e1, e2, e3] at hmul
    simp only [zero_mul] at hmul
    have hlin : -(v 0 * R + v 1 * T + v 2 * S + v 3 * P) + σ * (v 0 + v 1 + v 2 + v 3) = 0 := by
      linarith [hmul]
    rw [hsum4] at hlin
    linarith [hlin]

end WantedExt.Biology.Ecology.ZeroDeterminantStrategyWanted

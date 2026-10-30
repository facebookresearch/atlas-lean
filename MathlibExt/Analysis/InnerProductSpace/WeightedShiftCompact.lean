/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.InnerProductSpace.WeightedShiftOperator
public import Mathlib.Analysis.Normed.Operator.Compact.Basic

/-!
# Compactness of weighted unilateral shifts

A weighted unilateral shift on `ℓ²(ℕ, 𝕜)` is compact if and only if its
weights tend to `0`. The weighted shift is the canonical forward shift
composed with the canonical diagonal operator. Composing it with the plain
backward shift recovers that diagonal operator, so compactness transfers in
both directions. The diagonal compactness criterion then gives the result.

The public prefix truncation retains exactly the coefficients with `n < N`.
Its convergence follows from the weighted-shift norm bound. Compactness of
eventually zero weights is a consequence of the compactness criterion.

These are derived supporting results for the archived Hilbert-space and
spectral material in
`v1/Atlas/IntroductionToFunctionalAnalysis/code/HilbertSpace.lean` and
`v1/Atlas/IntroductionToFunctionalAnalysis/code/SpectralTheory.lean`.
They are not identified as imported v1 targets.

## Main declarations

* `isCompactOperator_weightedShiftCLM_iff` : `S` is compact iff `w → 0`.
* `weightedShiftCLM_sub` : subtraction of weights subtracts the shifts.
* `tendsto_weightedShiftCLM_trunc` : prefix truncations converge in operator norm.
-/

@[expose] public section

namespace MathlibExt.Analysis.InnerProductSpace.WeightedShiftCompact

open Filter Topology Set
open scoped _root_.lp ENNReal
open MathlibExt.Analysis.InnerProductSpace
open MathlibExt.Analysis.InnerProductSpace.WeightedShiftOperator

variable {𝕜 : Type*} [RCLike 𝕜]

/-- The weights truncated after `N` coordinates: `w n` for `n < N`, `0`
for `n ≥ N`. -/
def truncWeights (w : ℕ → 𝕜) (N : ℕ) : ℕ → 𝕜 := fun n => if n < N then w n else 0

/-- Prefix truncation retains each weight at an index strictly below the cutoff. -/
theorem truncWeights_apply_lt {w : ℕ → 𝕜} {N n : ℕ} (h : n < N) :
    truncWeights w N n = w n :=
  ite_eq_left h

/-- Prefix truncation vanishes at and beyond the cutoff. -/
theorem truncWeights_apply_ge {w : ℕ → 𝕜} {N n : ℕ} (h : ¬ n < N) :
    truncWeights w N n = 0 :=
  ite_eq_right h

/-- Truncation does not increase the bound on the weights. -/
theorem bddAbove_truncWeights {w : ℕ → 𝕜}
    (hw : BddAbove (Set.range fun n => ‖w n‖)) (N : ℕ) :
    BddAbove (Set.range fun n => ‖truncWeights w N n‖) := by
  obtain ⟨C, hC⟩ := hw
  refine ⟨C, ?_⟩
  rintro y ⟨n, rfl⟩
  show ‖truncWeights w N n‖ ≤ C
  by_cases h : n < N
  · rw [truncWeights_apply_lt h]
    exact hC ⟨n, rfl⟩
  · rw [truncWeights_apply_ge h, norm_zero]
    exact le_trans (norm_nonneg _) (hC ⟨0, rfl⟩)

/-- Differences of bounded weight sequences are bounded. -/
theorem bddAbove_sub {w v : ℕ → 𝕜}
    (hw : BddAbove (Set.range fun n => ‖w n‖))
    (hv : BddAbove (Set.range fun n => ‖v n‖)) :
    BddAbove (Set.range fun n => ‖w n - v n‖) := by
  obtain ⟨Cw, hCw⟩ := hw
  obtain ⟨Cv, hCv⟩ := hv
  refine ⟨Cw + Cv, ?_⟩
  rintro y ⟨n, rfl⟩
  calc ‖w n - v n‖ ≤ ‖w n‖ + ‖v n‖ := norm_sub_le _ _
    _ ≤ Cw + Cv := add_le_add (hCw ⟨n, rfl⟩) (hCv ⟨n, rfl⟩)

/-- The weighted shift is additive in the weights. -/
theorem weightedShiftCLM_sub {w v : ℕ → 𝕜}
    (hw : BddAbove (Set.range fun n => ‖w n‖))
    (hv : BddAbove (Set.range fun n => ‖v n‖))
    (hsub : BddAbove (Set.range fun n => ‖w n - v n‖)) :
    weightedShiftCLM (w - v) hsub =
      weightedShiftCLM w hw - weightedShiftCLM v hv := by
  unfold weightedShiftCLM
  rw [← ContinuousLinearMap.comp_sub, LpDiagonalOperator.diagonalCLM_sub]
  congr 2

/-- The truncations of the weights converge to the shift in operator norm
when the weights tend to `0`. -/
theorem tendsto_weightedShiftCLM_trunc {w : ℕ → 𝕜}
    (hw : BddAbove (Set.range fun n => ‖w n‖))
    (hw0 : Tendsto w atTop (𝓝 0)) :
    Tendsto (fun N => weightedShiftCLM (truncWeights w N) (bddAbove_truncWeights hw N))
      atTop (𝓝 (weightedShiftCLM w hw)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N₀, hN₀⟩ := Metric.tendsto_atTop.mp hw0 (ε / 2) (half_pos hε)
  refine ⟨N₀, fun N hN => ?_⟩
  have hdiff : weightedShiftCLM (truncWeights w N) (bddAbove_truncWeights hw N) -
        weightedShiftCLM w hw =
      weightedShiftCLM (truncWeights w N - w)
        (bddAbove_sub (bddAbove_truncWeights hw N) hw) :=
    (weightedShiftCLM_sub (bddAbove_truncWeights hw N) hw _).symm
  rw [dist_eq_norm, hdiff]
  have hbound : ‖weightedShiftCLM (truncWeights w N - w)
      (bddAbove_sub (bddAbove_truncWeights hw N) hw)‖ ≤ ε / 2 := by
    apply norm_weightedShiftCLM_le_of_forall_le _ (fun n => ?_)
    by_cases h : n < N
    · rw [Pi.sub_apply, truncWeights_apply_lt h, sub_self, norm_zero]
      exact (half_pos hε).le
    · have hge : N₀ ≤ n := le_trans hN (not_lt.mp h)
      have hdist := hN₀ n hge
      rw [Pi.sub_apply, truncWeights_apply_ge h, zero_sub, norm_neg]
      have hdist' : dist (w n) 0 = ‖w n‖ := by rw [dist_eq_norm, sub_zero]
      rw [hdist'] at hdist
      exact hdist.le
  calc ‖weightedShiftCLM (truncWeights w N - w)
        (bddAbove_sub (bddAbove_truncWeights hw N) hw)‖
      ≤ ε / 2 := hbound
    _ < ε := half_lt_self hε

/-- The original upper-bound hypothesis supplies the canonical diagonal bound. -/
private theorem diagonalBound {w : ℕ → 𝕜}
    (hw : BddAbove (Set.range fun n => ‖w n‖)) : ∃ C, ∀ n, ‖w n‖ ≤ C := by
  obtain ⟨C, hC⟩ := hw
  exact ⟨C, fun n => hC ⟨n, rfl⟩⟩

/-- The plain backward shift recovers diagonal multiplication from the weighted shift. -/
private theorem backward_comp_weightedShift (w : ℕ → 𝕜)
    (hw : BddAbove (Set.range fun n => ‖w n‖)) :
    LpShiftOperator.backwardCLM ∘L weightedShiftCLM w hw =
      LpDiagonalOperator.diagonalCLM w (diagonalBound hw) := by
  simpa only [weightedShiftCLM, ← ContinuousLinearMap.comp_assoc,
    LpShiftOperator.backward_comp_shift, ContinuousLinearMap.one_def] using
    (ContinuousLinearMap.id_comp (LpDiagonalOperator.diagonalCLM w (diagonalBound hw)))

/-- The weighted shift is compact if and only if its weights tend to `0`. -/
theorem isCompactOperator_weightedShiftCLM_iff {w : ℕ → 𝕜}
    (hw : BddAbove (Set.range fun n => ‖w n‖)) :
    IsCompactOperator (weightedShiftCLM w hw) ↔ Tendsto w atTop (𝓝 0) := by
  rw [← Nat.cofinite_eq_atTop,
    ← LpDiagonalOperator.isCompactOperator_diagonalCLM_iff (diagonalBound hw)]
  constructor
  · intro h
    have hc := h.clm_comp (LpShiftOperator.backwardCLM (𝕜 := 𝕜))
    simpa only [← ContinuousLinearMap.coe_comp, backward_comp_weightedShift w hw] using hc
  · intro h
    have hc := h.clm_comp (LpShiftOperator.shiftCLM (𝕜 := 𝕜))
    simpa only [← ContinuousLinearMap.coe_comp, weightedShiftCLM] using hc

/-- A weighted shift whose weights are eventually zero is compact. -/
theorem isCompactOperator_weightedShift_of_forall_eq_zero {w : ℕ → 𝕜}
    (hw : BddAbove (Set.range fun n => ‖w n‖)) {N : ℕ}
    (hN : ∀ n, N ≤ n → w n = 0) :
    IsCompactOperator (weightedShiftCLM w hw) := by
  rw [isCompactOperator_weightedShiftCLM_iff hw, Metric.tendsto_atTop]
  intro ε hε
  exact ⟨N, fun n hn => by rw [hN n hn, dist_self]; exact hε⟩

end MathlibExt.Analysis.InnerProductSpace.WeightedShiftCompact

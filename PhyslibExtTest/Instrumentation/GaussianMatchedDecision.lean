/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.Instrumentation.GaussianMatchedDecision
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Tactic.NormNum
import Mathlib.Data.Matrix.Mul
import Mathlib.Tactic.Linarith

@[expose] public section

open Matrix
open PhyslibExt.Instrumentation.GaussianMatchedDecision
open MathlibExt.LinearAlgebra.Matrix.MatchedSNRQuotient

namespace PhyslibExtTest.Instrumentation.GaussianMatchedDecision

/-- The `Fin 1` fixture from the module: the rule decides `true` at
`y = 0` and `false` at `y = -2`. -/
example (tie : Bool) :
    matchedFilterRule (WithLp.toLp 2 ![(1 : ℝ)]) (WithLp.toLp 2 ![0]) !![(1 : ℝ)]
        (1 / 4) (3 / 4) 0 4 2 1 tie (WithLp.toLp 2 ![0]) = true ∧
      matchedFilterRule (WithLp.toLp 2 ![(1 : ℝ)]) (WithLp.toLp 2 ![0]) !![(1 : ℝ)]
        (1 / 4) (3 / 4) 0 4 2 1 tie (WithLp.toLp 2 ![-2]) = false :=
  matchedFilterRule_fin_one_example tie

/-- Transposing the two off-diagonal costs in the `Fin 1` fixture
changes the threshold. -/
example :
    matchedThreshold (WithLp.toLp 2 ![(1 : ℝ)]) (WithLp.toLp 2 ![0]) !![(1 : ℝ)]
        (1 / 4) (3 / 4) 0 2 4 1 ≠
      matchedThreshold (WithLp.toLp 2 ![(1 : ℝ)]) (WithLp.toLp 2 ![0]) !![(1 : ℝ)]
        (1 / 4) (3 / 4) 0 4 2 1 :=
  matchedThreshold_fin_one_flipped_ne

/-- The transposed-cost `Fin 1` rule is rejected at `y = 0`. -/
example (tie : Bool) :
    matchedFilterRule (WithLp.toLp 2 ![(1 : ℝ)]) (WithLp.toLp 2 ![0]) !![(1 : ℝ)]
      (1 / 4) (3 / 4) 0 2 4 1 tie (WithLp.toLp 2 ![0]) = false :=
  matchedFilterRule_fin_one_flipped_example tie

/-- The `Fin 2` fixture with non-diagonal covariance: `true`, tie,
and `false` branches. -/
example (tie : Bool) :
    matchedFilterRule (WithLp.toLp 2 ![(1 : ℝ), 1]) (WithLp.toLp 2 ![0, 0])
        !![(2 : ℝ), 1; 1, 2] (1 / 2) (1 / 2) 0 1 1 0 tie (WithLp.toLp 2 ![1, 1]) = true ∧
      matchedFilterRule (WithLp.toLp 2 ![(1 : ℝ), 1]) (WithLp.toLp 2 ![0, 0])
          !![(2 : ℝ), 1; 1, 2] (1 / 2) (1 / 2) 0 1 1 0 tie (WithLp.toLp 2 ![1, 0]) = tie ∧
      matchedFilterRule (WithLp.toLp 2 ![(1 : ℝ), 1]) (WithLp.toLp 2 ![0, 0])
          !![(2 : ℝ), 1; 1, 2] (1 / 2) (1 / 2) 0 1 1 0 tie (WithLp.toLp 2 ![0, 0]) = false :=
  matchedFilterRule_fin_two_example tie

/-- Equal means in `Fin 2`: the rule decides `true` at every
observation for these priors and costs. -/
example (tie : Bool) (y : EuclideanSpace ℝ (Fin 2)) :
    matchedFilterRule (WithLp.toLp 2 ![(1 : ℝ), 1]) (WithLp.toLp 2 ![1, 1])
      !![(2 : ℝ), 1; 1, 2] (1 / 4) (3 / 4) 0 4 2 1 tie y = true :=
  matchedFilterRule_fin_two_equal_means_example tie y

/-- The matched statistic in the `Fin 2` fixture at `(1, 1)` is
`2 / 3`, evaluated through the matched weight. -/
example :
    matchedStatistic (WithLp.toLp 2 ![(1 : ℝ), 1]) (WithLp.toLp 2 ![0, 0])
        !![(2 : ℝ), 1; 1, 2] (WithLp.toLp 2 ![1, 1]) =
      (!![(2 : ℝ), 1; 1, 2]⁻¹ *ᵥ WithLp.ofLp (WithLp.toLp 2 ![(1 : ℝ), 1] -
          WithLp.toLp 2 ![0, 0])) ⬝ᵥ WithLp.ofLp (WithLp.toLp 2 ![1, 1]) := by
  have hR : (!![(2 : ℝ), 1; 1, 2] : Matrix (Fin 2) (Fin 2) ℝ).PosDef := by
    refine Matrix.PosDef.of_dotProduct_mulVec_pos (by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.IsHermitian, Matrix.conjTranspose]) ?_
    intro x hx
    have hne : x 0 ≠ 0 ∨ x 1 ≠ 0 := by
      by_contra h
      push_neg at h
      exact hx (funext fun i => by fin_cases i <;> simp [h.1, h.2])
    simp only [star_trivial, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.of_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_fin_one]
    rcases hne with h0 | h1
    · nlinarith [sq_nonneg (x 0 + x 1), sq_nonneg (x 0), sq_pos_of_ne_zero h0]
    · nlinarith [sq_nonneg (x 0 + x 1), sq_nonneg (x 1), sq_pos_of_ne_zero h1]
  exact matchedStatistic_eq_dotProduct_matchedWeight _ _ _ hR _

/-- SNR optimality at a concrete weight: in the `Fin 2` fixture the
weight `(1, 0)` has matched SNR at most that of the matched weight. -/
example :
    matchedSNR !![(2 : ℝ), 1; 1, 2]
        (WithLp.ofLp (WithLp.toLp 2 ![(1 : ℝ), 1] - WithLp.toLp 2 ![0, 0])) ![1, 0] ≤
      matchedSNR !![(2 : ℝ), 1; 1, 2]
        (WithLp.ofLp (WithLp.toLp 2 ![(1 : ℝ), 1] - WithLp.toLp 2 ![0, 0]))
        (!![(2 : ℝ), 1; 1, 2]⁻¹ *ᵥ
          WithLp.ofLp (WithLp.toLp 2 ![(1 : ℝ), 1] - WithLp.toLp 2 ![0, 0])) := by
  have hR : (!![(2 : ℝ), 1; 1, 2] : Matrix (Fin 2) (Fin 2) ℝ).PosDef := by
    refine Matrix.PosDef.of_dotProduct_mulVec_pos (by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.IsHermitian, Matrix.conjTranspose]) ?_
    intro x hx
    have hne : x 0 ≠ 0 ∨ x 1 ≠ 0 := by
      by_contra h
      push_neg at h
      exact hx (funext fun i => by fin_cases i <;> simp [h.1, h.2])
    simp only [star_trivial, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.of_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_fin_one]
    rcases hne with h0 | h1
    · nlinarith [sq_nonneg (x 0 + x 1), sq_nonneg (x 0), sq_pos_of_ne_zero h0]
    · nlinarith [sq_nonneg (x 0 + x 1), sq_nonneg (x 1), sq_pos_of_ne_zero h1]
  have hs : (WithLp.toLp 2 ![(1 : ℝ), 1] : EuclideanSpace ℝ (Fin 2)) ≠
      WithLp.toLp 2 ![0, 0] := by
    intro hcon
    have h := congrFun (congrArg WithLp.ofLp hcon) 0
    simp [WithLp.ofLp_toLp] at h
  have hw : (![1, 0] : Fin 2 → ℝ) ≠ 0 := by
    intro hcon
    have h := congrFun hcon 0
    simp at h
  exact matchedSNR_le_matchedSNR_matchedWeight _ _ _ hR hs ![1, 0] hw

end PhyslibExtTest.Instrumentation.GaussianMatchedDecision

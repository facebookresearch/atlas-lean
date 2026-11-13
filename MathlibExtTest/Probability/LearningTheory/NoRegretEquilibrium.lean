/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.LearningTheory.NoRegretEquilibrium
import Mathlib.Tactic

@[expose] public section

open Matrix Convexity MathlibExt.Probability.LearningTheory.NoRegretEquilibrium

namespace MathlibExtTest.Probability.LearningTheory.NoRegretEquilibrium

/-- One round: the average strategy is the strategy played. -/
example {k : ℕ} (p : Fin 1 → StdSimplex ℝ (Fin k)) : avgStrategy one_pos p = p 0 := by
  rw [← StdSimplex.weights_inj]
  ext i
  simp [avgStrategy_weights]

/-- Averaging two rounds of opposite pure strategies gives the uniform strategy. -/
example : (avgStrategy (T := 2) two_pos ![StdSimplex.single 0, StdSimplex.single 1]).weights =
    Finsupp.equivFunOnFinite.symm (fun _ : Fin 2 => (1 / 2 : ℝ)) := by
  ext i
  fin_cases i <;> simp [avgStrategy_weights, StdSimplex.single, Fin.sum_univ_two]

/-- The `1 × 1` game with payoff `1`: constant play has zero regret, so the theorem applies with
`εrow = εcol = 0`. -/
example {T : ℕ} (hT : 0 < T) (x y : StdSimplex ℝ (Fin 1)) :
    x.weights ⬝ᵥ (!![(1 : ℝ)] *ᵥ (avgStrategy hT fun _ => StdSimplex.single 0).weights) -
      (avgStrategy hT fun _ => StdSimplex.single 0).weights ⬝ᵥ (!![(1 : ℝ)] *ᵥ y.weights) ≤
        0 + 0 := by
  refine no_regret_approx_saddle hT _ _ _ 0 0 (fun x' => ?_) (fun y' => ?_) x y
  · obtain rfl : x' = StdSimplex.single 0 := Subsingleton.elim _ _
    simp
  · obtain rfl : y' = StdSimplex.single 0 := Subsingleton.elim _ _
    simp

/-- Orientation check, the `2 × 1` game with payoffs `0` (first row) and `1` (second row): the row
player, who maximizes, always plays the second row, so neither player has positive regret and the
averages form an exact saddle point. -/
example {T : ℕ} (hT : 0 < T) (x : StdSimplex ℝ (Fin 2)) (y : StdSimplex ℝ (Fin 1)) :
    x.weights ⬝ᵥ (!![(0 : ℝ); 1] *ᵥ (avgStrategy hT fun _ => StdSimplex.single 0).weights) -
      (avgStrategy hT fun _ => StdSimplex.single 1).weights ⬝ᵥ (!![(0 : ℝ); 1] *ᵥ y.weights) ≤
        0 + 0 := by
  refine no_regret_approx_saddle hT _ _ _ 0 0 (fun x' => ?_) (fun y' => ?_) x y
  · have hx : x'.weights 1 ≤ 1 := StdSimplex.weights_apply_le_one x' 1
    simp only [StdSimplex.single, dotProduct, mulVec, Fin.sum_univ_two, Fin.sum_univ_one,
      Finsupp.single_apply, of_apply, cons_val_zero, cons_val_one, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hT' : (0 : ℝ) < T := by exact_mod_cast hT
    rw [← sub_div]
    apply div_nonpos_of_nonpos_of_nonneg _ hT'.le
    norm_num
    nlinarith
  · obtain rfl : y' = StdSimplex.single 0 := Subsingleton.elim _ _
    simp

/-- The approximate-saddle-point inequalities: no deviation gains more than `εrow + εcol`. -/
example {m n T : ℕ} (hT : 0 < T) (A : Matrix (Fin m) (Fin n) ℝ)
    (p : Fin T → StdSimplex ℝ (Fin m)) (q : Fin T → StdSimplex ℝ (Fin n)) (εrow εcol : ℝ)
    (hrow : ∀ x : StdSimplex ℝ (Fin m),
      (∑ t, x.weights ⬝ᵥ (A *ᵥ (q t).weights)) / T -
        (∑ t, (p t).weights ⬝ᵥ (A *ᵥ (q t).weights)) / T ≤ εrow)
    (hcol : ∀ y : StdSimplex ℝ (Fin n),
      (∑ t, (p t).weights ⬝ᵥ (A *ᵥ (q t).weights)) / T -
        (∑ t, (p t).weights ⬝ᵥ (A *ᵥ y.weights)) / T ≤ εcol)
    (x : StdSimplex ℝ (Fin m)) (y : StdSimplex ℝ (Fin n)) :
    x.weights ⬝ᵥ (A *ᵥ (avgStrategy hT q).weights) ≤
        (avgStrategy hT p).weights ⬝ᵥ (A *ᵥ (avgStrategy hT q).weights) + (εrow + εcol) ∧
      (avgStrategy hT p).weights ⬝ᵥ (A *ᵥ (avgStrategy hT q).weights) ≤
        (avgStrategy hT p).weights ⬝ᵥ (A *ᵥ y.weights) + (εrow + εcol) := by
  constructor
  · linarith [no_regret_approx_saddle hT A p q εrow εcol hrow hcol x (avgStrategy hT q)]
  · linarith [no_regret_approx_saddle hT A p q εrow εcol hrow hcol (avgStrategy hT p) y]

end MathlibExtTest.Probability.LearningTheory.NoRegretEquilibrium

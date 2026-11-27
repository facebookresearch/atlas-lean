/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.GameTheory.Regret
public import MathlibExt.GameTheory.RegretInducedLoss
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Finset.BooleanAlgebra
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.NormNum

/-!
# Tests for external and swap regret

Worked example: `K = Fin 2`, `T = 3`, losses `![1, 0]`, `![1, 0]`, `![0, 1]`
by round and play `![1, 0]` every round. Expected loss `2`, cumulative losses
`(2, 1)`, external regret `1`, swap regret `1`, average regret `1 / 3`.
-/

@[expose] public section

namespace MathlibExtTest.GameTheory.Regret

open scoped BigOperators

open MathlibExt.GameTheory.Regret

/-- Loss vectors of the worked example. -/
def exLoss : Fin 3 → Fin 2 → ℝ :=
  ![![1, 0], ![1, 0], ![0, 1]]

/-- Played distributions of the worked example. -/
def exPlay : Fin 3 → Fin 2 → ℝ :=
  fun _ => ![1, 0]

/-- T1: expected loss of the worked example is `2`. -/
theorem ex_expectedLoss : expectedLoss exPlay exLoss = 2 := by
  norm_num [expectedLoss, exPlay, exLoss, Fin.sum_univ_three, Fin.sum_univ_two,
    Matrix.cons_val_two]

/-- T1: cumulative loss of action `0` is `2`. -/
theorem ex_cumulativeLoss_zero : cumulativeLoss exLoss 0 = 2 := by
  norm_num [cumulativeLoss, exLoss, Fin.sum_univ_three, Matrix.cons_val_two]

/-- T1: cumulative loss of action `1` is `1`. -/
theorem ex_cumulativeLoss_one : cumulativeLoss exLoss 1 = 1 := by
  norm_num [cumulativeLoss, exLoss, Fin.sum_univ_three, Matrix.cons_val_two]

/-- T2: external regret of the worked example is `1`. -/
theorem ex_externalRegret : externalRegret exPlay exLoss = 1 := by
  have hmin : Finset.univ.inf' Finset.univ_nonempty (cumulativeLoss exLoss) = 1 := by
    apply le_antisymm
    · calc Finset.univ.inf' Finset.univ_nonempty (cumulativeLoss exLoss)
          ≤ cumulativeLoss exLoss 1 :=
            Finset.inf'_le _ (Finset.mem_univ _)
        _ = 1 := ex_cumulativeLoss_one
    · apply Finset.le_inf' _ _ (fun b _ => ?_)
      fin_cases b
      · norm_num [ex_cumulativeLoss_zero]
      · norm_num [ex_cumulativeLoss_one]
  norm_num [externalRegret, ex_expectedLoss, hmin]

/-- T3: swap regret of the worked example is `1`. -/
theorem ex_swapRegret : swapRegret exPlay exLoss = 1 := by
  have hmin : Finset.univ.inf' Finset.univ_nonempty
      (fun δ : Fin 2 → Fin 2 => ∑ t, ∑ a, exPlay t a * exLoss t (δ a)) = 1 := by
    apply le_antisymm
    · calc Finset.univ.inf' Finset.univ_nonempty
            (fun δ : Fin 2 → Fin 2 => ∑ t, ∑ a, exPlay t a * exLoss t (δ a))
          ≤ (fun δ : Fin 2 → Fin 2 => ∑ t, ∑ a, exPlay t a * exLoss t (δ a))
              (fun _ => 1) :=
            Finset.inf'_le _ (Finset.mem_univ _)
        _ = 1 := by
            norm_num [exPlay, exLoss, Fin.sum_univ_three, Fin.sum_univ_two,
              Matrix.cons_val_two]
    · apply Finset.le_inf' _ _ (fun δ _ => ?_)
      have h01 : ∀ i : Fin 2, i = 0 ∨ i = 1 := by
        intro i
        fin_cases i
        · exact Or.inl rfl
        · exact Or.inr rfl
      simp only [exPlay, exLoss, Fin.sum_univ_three, Fin.sum_univ_two,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.head_cons, Matrix.tail_cons]
      rcases h01 (δ 0) with h | h <;> rw [h] <;> norm_num
  rw [swapRegret, ex_expectedLoss, hmin]
  norm_num

/-- T4: average regret of the worked example is `1 / 3`. -/
theorem ex_averageRegret : averageRegret exPlay exLoss = 1 / 3 := by
  norm_num [averageRegret, ex_externalRegret]

/-- T5: `![1 / 2, 1 / 2]` is in the simplex. -/
theorem ex_simplex_half : IsSimplex (![1 / 2, 1 / 2] : Fin 2 → ℝ) := by
  rw [isSimplex_iff]
  refine ⟨fun a => ?_, ?_⟩
  · fin_cases a <;> norm_num
  · norm_num [Fin.sum_univ_two]

/-- T5: `![1, 1]` is not in the simplex. -/
theorem ex_not_simplex_one : ¬ IsSimplex (![1, 1] : Fin 2 → ℝ) := by
  intro h
  norm_num [isSimplex_iff, Fin.sum_univ_two] at h

/-- Mismatch cost of the induced-loss example. -/
def exCost : Fin 2 → (Fin 2 → Fin 2) → ℝ :=
  fun _ s => if s 0 = s 1 then 0 else 1

/-- Uniform opponent mix of the induced-loss example. -/
noncomputable def exOpp : Fin 2 → Fin 2 → ℝ :=
  fun _ => ![1 / 2, 1 / 2]

/-- T6: pure cost under the uniform mix is `1 / 2` for both actions. -/
theorem test_pureCost_uniform :
    MathlibExt.GameTheory.CorrelatedEquilibrium.pureCost exCost exOpp 0 0
        = 1 / 2 ∧
      MathlibExt.GameTheory.CorrelatedEquilibrium.pureCost exCost exOpp 0 1
        = 1 / 2 := by
  have hsum : ∀ g : (Fin 2 → Fin 2) → ℝ,
      ∑ s, g s = (g ![0, 0] + g ![0, 1]) + (g ![1, 0] + g ![1, 1]) := by
    intro g
    rw [← Equiv.sum_comp (finTwoArrowEquiv (Fin 2)).symm g]
    simp only [Fintype.sum_prod_type, Fin.sum_univ_two,
      finTwoArrowEquiv_symm_apply]
  have h10 : (1 : Fin 2) ≠ 0 := by decide
  have herase : Finset.univ.erase (0 : Fin 2) = {1} := by decide
  constructor
  · simp only [pureCost_eq_sum_filter, exCost, exOpp, Finset.sum_filter, hsum, herase,
      Finset.prod_singleton, Matrix.cons_val_zero, Matrix.cons_val_one]
    simp
  · simp only [pureCost_eq_sum_filter, exCost, exOpp, Finset.sum_filter, hsum, herase,
      Finset.prod_singleton, Matrix.cons_val_zero, Matrix.cons_val_one]
    simp

/-- Mixed-play example losses: action `0` loses in round `0`, action `1`
loses in round `1`. -/
def mixLoss : Fin 2 → Fin 2 → ℝ :=
  ![![1, 0], ![0, 1]]

/-- Mixed-play example play: action `t` is played in round `t`. -/
def mixPlay : Fin 2 → Fin 2 → ℝ :=
  ![![1, 0], ![0, 1]]

/-- T7: with genuinely varying play, swap regret `2` strictly exceeds
external regret `1`. -/
theorem ex2_swap_gt_external :
    externalRegret mixPlay mixLoss = 1 ∧ swapRegret mixPlay mixLoss = 2 ∧
      externalRegret mixPlay mixLoss ≤ swapRegret mixPlay mixLoss := by
  have hplay : ∀ t, IsSimplex (mixPlay t) := by
    intro t
    fin_cases t <;> rw [isSimplex_iff] <;> refine ⟨?_, ?_⟩
    · intro a
      fin_cases a <;> norm_num [mixPlay]
    · norm_num [mixPlay, Fin.sum_univ_two]
    · intro a
      fin_cases a <;> norm_num [mixPlay]
    · norm_num [mixPlay, Fin.sum_univ_two]
  have hexp : expectedLoss mixPlay mixLoss = 2 := by
    norm_num [expectedLoss, mixPlay, mixLoss, Fin.sum_univ_two,
      Matrix.cons_val_two]
  have hcum : ∀ a : Fin 2, cumulativeLoss mixLoss a = 1 := by
    intro a
    fin_cases a <;>
      norm_num [cumulativeLoss, mixLoss, Fin.sum_univ_two, Matrix.cons_val_two]
  have hext : externalRegret mixPlay mixLoss = 1 := by
    have hmin : Finset.univ.inf' Finset.univ_nonempty
        (cumulativeLoss mixLoss) = 1 := by
      apply le_antisymm
      · calc Finset.univ.inf' Finset.univ_nonempty (cumulativeLoss mixLoss)
            ≤ cumulativeLoss mixLoss 0 :=
              Finset.inf'_le _ (Finset.mem_univ _)
          _ = 1 := hcum 0
      · exact Finset.le_inf' _ _ fun b _ => le_of_eq (hcum b).symm
    norm_num [externalRegret, hexp, hmin]
  have hswap : swapRegret mixPlay mixLoss = 2 := by
    have hmin : Finset.univ.inf' Finset.univ_nonempty
        (fun δ : Fin 2 → Fin 2 => ∑ t, ∑ a, mixPlay t a * mixLoss t (δ a))
        = 0 := by
      apply le_antisymm
      · calc Finset.univ.inf' Finset.univ_nonempty
              (fun δ : Fin 2 → Fin 2 => ∑ t, ∑ a, mixPlay t a * mixLoss t (δ a))
            ≤ (fun δ : Fin 2 → Fin 2 =>
                ∑ t, ∑ a, mixPlay t a * mixLoss t (δ a))
                (fun a => if a = 0 then 1 else 0) :=
              Finset.inf'_le _ (Finset.mem_univ _)
          _ = 0 := by
              norm_num [mixPlay, mixLoss, Fin.sum_univ_two, Matrix.cons_val_two]
      · apply Finset.le_inf' _ _ (fun δ _ => ?_)
        have h01 : ∀ i : Fin 2, i = 0 ∨ i = 1 := by
          intro i
          fin_cases i
          · exact Or.inl rfl
          · exact Or.inr rfl
        simp only [mixPlay, mixLoss, Fin.sum_univ_two, Matrix.cons_val_zero,
          Matrix.cons_val_one]
        rcases h01 (δ 0) with h | h <;> rcases h01 (δ 1) with h' | h' <;>
          rw [h, h'] <;> norm_num
    rw [swapRegret, hexp, hmin]
    norm_num
  exact ⟨hext, hswap, externalRegret_le_swapRegret mixPlay mixLoss hplay⟩

/-- T8: average regret and the base lemmas need no `NeZero` horizon and no
`DecidableEq` on actions: with neither instance in scope, a per-round loss
shift leaves average regret unchanged, and regret against a fixed
distribution is at most external regret. -/
theorem test_regret_no_instances {K : Type*} [Fintype K] [Nonempty K] {T : ℕ}
    (play loss : Fin T → K → ℝ) (hplay : ∀ t, IsSimplex (play t)) (c : Fin T → ℝ)
    (q : K → ℝ) (hq : IsSimplex q) :
    averageRegret play (fun t a => loss t a + c t) = averageRegret play loss ∧
      expectedLoss play loss - ∑ a, q a * cumulativeLoss loss a ≤
        externalRegret play loss := by
  refine ⟨?_, expectedLoss_sub_weightedCumulative_le_externalRegret play loss q hq⟩
  rw [averageRegret, averageRegret, externalRegret_add_roundConst play loss hplay c]

end MathlibExtTest.GameTheory.Regret

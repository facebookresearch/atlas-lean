/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.GameTheory.RegretBlumMansourBound

set_option autoImplicit false

@[expose] public section

namespace MathlibExtTest.GameTheory.RegretBlumMansourBound

open MathlibExt.GameTheory.Regret
open scoped BigOperators

/-- Identity recommendations for the two-action test: copy `j` plays `j`. -/
def qIdB : Fin 1 → Fin 2 → Fin 2 → ℝ :=
  fun _ j a => if a = j then 1 else 0

/-- Uniform master play for the two-action test. -/
noncomputable def pUB : Fin 1 → Fin 2 → ℝ :=
  fun _ _ => 1 / 2

/-- Example losses for the two-action test. -/
def l0B : Fin 1 → Fin 2 → ℝ :=
  fun _ a => if a = 0 then 2 else 6

theorem b0_stationary : IsStationaryPlay qIdB pUB := by
  refine ⟨?_, ?_, ?_⟩
  · intro t j
    rw [isSimplex_iff]
    refine ⟨?_, ?_⟩
    · intro a
      fin_cases j <;> fin_cases a <;> simp [qIdB]
    · fin_cases j <;> simp [qIdB]
  · intro t
    rw [isSimplex_iff]
    refine ⟨?_, ?_⟩
    · intro a
      show (0 : ℝ) ≤ 1 / 2
      norm_num
    · simp only [pUB, Fin.sum_univ_two]
      norm_num
  · intro t i
    simp only [pUB, qIdB, Fin.sum_univ_two]
    fin_cases i <;> simp

/-- B1: on the fixture, the two copies' external regrets against their
scaled losses are `0` and `2`, each at most the uniform bound `R = 2`. -/
theorem b1_copy_regrets :
    externalRegret (fun t => qIdB t 0) (scaledLoss pUB l0B 0) = 0 ∧
      externalRegret (fun t => qIdB t 1) (scaledLoss pUB l0B 1) = 2 ∧
      ∀ j, externalRegret (fun t => qIdB t j) (scaledLoss pUB l0B j) ≤ 2 := by
  have hcum : ∀ j a : Fin 2,
      cumulativeLoss (scaledLoss pUB l0B j) a = if a = 0 then 1 else 3 := by
    intro j a
    fin_cases a <;>
      norm_num [cumulativeLoss, scaledLoss, pUB, l0B, Fin.sum_univ_one]
  have hmin_scaled : ∀ j : Fin 2, Finset.univ.inf' Finset.univ_nonempty
      (cumulativeLoss (scaledLoss pUB l0B j)) = 1 := by
    intro j
    apply le_antisymm
    · calc Finset.univ.inf' Finset.univ_nonempty
            (cumulativeLoss (scaledLoss pUB l0B j))
          ≤ cumulativeLoss (scaledLoss pUB l0B j) 0 :=
            Finset.inf'_le _ (Finset.mem_univ _)
        _ = 1 := by simp [hcum]
    · apply Finset.le_inf' _ _ (fun a _ => ?_)
      fin_cases a <;> simp [hcum]
  have h0 : externalRegret (fun t => qIdB t 0) (scaledLoss pUB l0B 0) = 0 := by
    have hexp : expectedLoss (fun t => qIdB t 0) (scaledLoss pUB l0B 0) = 1 := by
      norm_num [expectedLoss, scaledLoss, qIdB, pUB, l0B, Fin.sum_univ_one,
        Fin.sum_univ_two]
    rw [externalRegret, hexp, hmin_scaled]
    norm_num
  have h1 : externalRegret (fun t => qIdB t 1) (scaledLoss pUB l0B 1) = 2 := by
    have hexp : expectedLoss (fun t => qIdB t 1) (scaledLoss pUB l0B 1) = 3 := by
      norm_num [expectedLoss, scaledLoss, qIdB, pUB, l0B, Fin.sum_univ_one,
        Fin.sum_univ_two]
    rw [externalRegret, hexp, hmin_scaled]
    norm_num
  refine ⟨h0, h1, ?_⟩
  intro j
  fin_cases j
  · show externalRegret (fun t => qIdB t 0) (scaledLoss pUB l0B 0) ≤ 2
    rw [h0]; norm_num
  · show externalRegret (fun t => qIdB t 1) (scaledLoss pUB l0B 1) ≤ 2
    rw [h1]

/-- B2: the uniform bound on the fixture. The swap regret is
independently computed to be `2`, and the theorem bounds it by
`|Fin 2| * 2 = 4`. -/
theorem b2_uniform_bound_example :
    swapRegret pUB l0B = 2 ∧ swapRegret pUB l0B ≤ 4 := by
  have h01 : ∀ i : Fin 2, i = 0 ∨ i = 1 := by
    intro i
    fin_cases i
    · exact Or.inl rfl
    · exact Or.inr rfl
  have hswap : swapRegret pUB l0B = 2 := by
    have hexp : expectedLoss pUB l0B = 4 := by
      simp only [expectedLoss, pUB, l0B, Fin.sum_univ_one, Fin.sum_univ_two]
      simp
      norm_num
    have hmin : Finset.univ.inf' Finset.univ_nonempty
        (fun δ : Fin 2 → Fin 2 => ∑ t, ∑ a, pUB t a * l0B t (δ a)) = 2 := by
      apply le_antisymm
      · calc Finset.univ.inf' Finset.univ_nonempty
              (fun δ : Fin 2 → Fin 2 => ∑ t, ∑ a, pUB t a * l0B t (δ a))
            ≤ (fun δ : Fin 2 → Fin 2 => ∑ t, ∑ a, pUB t a * l0B t (δ a))
                (fun _ => 0) :=
              Finset.inf'_le _ (Finset.mem_univ _)
          _ = 2 := by
              simp only [pUB, l0B, Fin.sum_univ_one, Fin.sum_univ_two]
              simp
              norm_num
      · apply Finset.le_inf' _ _ (fun δ _ => ?_)
        simp only [pUB, l0B, Fin.sum_univ_one, Fin.sum_univ_two]
        rcases h01 (δ 0) with h | h <;> rcases h01 (δ 1) with h' | h' <;>
          simp [h, h'] <;> norm_num
    rw [swapRegret, hexp, hmin]
    norm_num
  refine ⟨hswap, ?_⟩
  have h := swapRegret_le_card_mul_of_externalRegret_le qIdB pUB l0B
    b0_stationary 2 b1_copy_regrets.2.2
  calc swapRegret pUB l0B ≤ (Fintype.card (Fin 2) : ℝ) * 2 := h
    _ = 4 := by norm_num [Fintype.card_fin]

/-- B3: the averaged bound on the fixture (horizon `T = 1`, so the
average regrets equal the unnormalized ones). -/
theorem b3_average_bound_example :
    swapRegret pUB l0B / ((1 : ℕ) : ℝ) ≤ 4 := by
  have hR : ∀ j, averageRegret (fun t => qIdB t j) (scaledLoss pUB l0B j) ≤ 2 := by
    intro j
    have h := b1_copy_regrets.2.2 j
    simpa [averageRegret] using h
  have h := swapRegret_div_le_card_mul_of_averageRegret_le qIdB pUB l0B
    b0_stationary 2 hR
  calc swapRegret pUB l0B / ((1 : ℕ) : ℝ)
      ≤ (Fintype.card (Fin 2) : ℝ) * 2 := h
    _ = 4 := by norm_num [Fintype.card_fin]

/-- Swap recommendations for the existence test: copy `j` plays the other
action. -/
def qSwapB : Fin 1 → Fin 2 → Fin 2 → ℝ :=
  fun _ j a => if a = j then 0 else 1

/-- B4: the existence form on the swap recommendations. The stationary
play is forced to be uniform, the copies' regrets for that play are at
most `2`, and the conclusion bounds its swap regret by `4`. -/
theorem b4_exists_bound_example :
    ∃ p : Fin 1 → Fin 2 → ℝ, IsStationaryPlay qSwapB p ∧
      swapRegret p l0B ≤ 4 := by
  have hq : ∀ t j, IsSimplex (qSwapB t j) := by
    intro t j
    rw [isSimplex_iff]
    refine ⟨?_, ?_⟩
    · intro a
      fin_cases j <;> fin_cases a <;> simp [qSwapB]
    · fin_cases j <;> simp [qSwapB, Fin.sum_univ_two]
  obtain ⟨p, hp, hbound⟩ :=
    exists_stationaryPlay_swapRegret_le_card_mul qSwapB l0B 2 hq
  have hunif : ∀ t, p t 0 = 1 / 2 ∧ p t 1 = 1 / 2 := by
    intro t
    have hsum : p t 0 + p t 1 = 1 := by
      have h := ((isSimplex_iff _).mp (hp.2.1 t)).2
      rwa [Fin.sum_univ_two] at h
    have h0 : p t 0 = p t 1 := by
      have h := hp.2.2 t 0
      simpa [qSwapB, Fin.sum_univ_two] using h
    constructor <;> linarith
  have hR : ∀ j, externalRegret (fun t => qSwapB t j) (scaledLoss p l0B j) ≤ 2 := by
    have hpj : ∀ j : Fin 2, p 0 j = 1 / 2 := by
      intro j
      fin_cases j
      · exact (hunif 0).1
      · exact (hunif 0).2
    have hcum : ∀ j a : Fin 2,
        cumulativeLoss (scaledLoss p l0B j) a = if a = 0 then 1 else 3 := by
      intro j a
      fin_cases a <;>
        norm_num [cumulativeLoss, scaledLoss, l0B, Fin.sum_univ_one, hpj]
    have hmin_scaled : ∀ j : Fin 2, Finset.univ.inf' Finset.univ_nonempty
        (cumulativeLoss (scaledLoss p l0B j)) = 1 := by
      intro j
      apply le_antisymm
      · calc Finset.univ.inf' Finset.univ_nonempty
              (cumulativeLoss (scaledLoss p l0B j))
            ≤ cumulativeLoss (scaledLoss p l0B j) 0 :=
              Finset.inf'_le _ (Finset.mem_univ _)
          _ = 1 := by simp [hcum]
      · apply Finset.le_inf' _ _ (fun a _ => ?_)
        fin_cases a <;> simp [hcum]
    intro j
    fin_cases j
    · show externalRegret (fun t => qSwapB t 0) (scaledLoss p l0B 0) ≤ 2
      have hexp : expectedLoss (fun t => qSwapB t 0) (scaledLoss p l0B 0) = 3 := by
        norm_num [expectedLoss, scaledLoss, qSwapB, l0B, Fin.sum_univ_one,
          Fin.sum_univ_two, hpj]
      rw [externalRegret, hexp, hmin_scaled]
      norm_num
    · show externalRegret (fun t => qSwapB t 1) (scaledLoss p l0B 1) ≤ 2
      have hexp : expectedLoss (fun t => qSwapB t 1) (scaledLoss p l0B 1) = 1 := by
        norm_num [expectedLoss, scaledLoss, qSwapB, l0B, Fin.sum_univ_one,
          Fin.sum_univ_two, hpj]
      rw [externalRegret, hexp, hmin_scaled]
      norm_num
  refine ⟨p, hp, ?_⟩
  calc swapRegret p l0B ≤ (Fintype.card (Fin 2) : ℝ) * 2 := hbound hR
    _ = 4 := by norm_num [Fintype.card_fin]

/-- Identity recommendations over a two-round horizon. -/
def qId2 : Fin 2 → Fin 2 → Fin 2 → ℝ :=
  fun _ j a => if a = j then 1 else 0

/-- Uniform master play over a two-round horizon. -/
noncomputable def pU2 : Fin 2 → Fin 2 → ℝ :=
  fun _ _ => 1 / 2

/-- Two-round losses: action `0` costs `2` then `4`; action `1` costs `6`
in both rounds. -/
def l2 : Fin 2 → Fin 2 → ℝ :=
  fun t a => if a = 0 then (if t = 0 then 2 else 4) else 6

/-- B5: the averaged bound over a two-round horizon, where the division
by `T = 2` is exercised. The copies' average regrets are independently
computed to be `0` and `3 / 2`, the swap regret to be `3`, and the
theorem bounds the average swap regret by `2 * (3 / 2) = 3`. -/
theorem b5_average_bound_two_rounds :
    swapRegret pU2 l2 = 3
    ∧ averageRegret (fun t => qId2 t 0) (scaledLoss pU2 l2 0) = 0
    ∧ averageRegret (fun t => qId2 t 1) (scaledLoss pU2 l2 1) = 3 / 2
    ∧ swapRegret pU2 l2 / ((2 : ℕ) : ℝ) ≤ 3 := by
  have hstat : IsStationaryPlay qId2 pU2 := by
    refine ⟨?_, ?_, ?_⟩
    · intro t j
      rw [isSimplex_iff]
      refine ⟨?_, ?_⟩
      · intro a
        fin_cases j <;> fin_cases a <;> simp [qId2]
      · fin_cases j <;> simp [qId2]
    · intro t
      rw [isSimplex_iff]
      refine ⟨?_, ?_⟩
      · intro a
        show (0 : ℝ) ≤ 1 / 2
        norm_num
      · simp only [pU2, Fin.sum_univ_two]
        norm_num
    · intro t i
      simp only [pU2, qId2, Fin.sum_univ_two]
      fin_cases i <;> simp
  have hcum : ∀ j a : Fin 2,
      cumulativeLoss (scaledLoss pU2 l2 j) a = if a = 0 then 3 else 6 := by
    intro j a
    fin_cases a <;>
      norm_num [cumulativeLoss, scaledLoss, pU2, l2, Fin.sum_univ_two]
  have hmin_scaled : ∀ j : Fin 2, Finset.univ.inf' Finset.univ_nonempty
      (cumulativeLoss (scaledLoss pU2 l2 j)) = 3 := by
    intro j
    apply le_antisymm
    · calc Finset.univ.inf' Finset.univ_nonempty
            (cumulativeLoss (scaledLoss pU2 l2 j))
          ≤ cumulativeLoss (scaledLoss pU2 l2 j) 0 :=
            Finset.inf'_le _ (Finset.mem_univ _)
        _ = 3 := by simp [hcum]
    · apply Finset.le_inf' _ _ (fun a _ => ?_)
      fin_cases a <;> simp only [hcum] <;> norm_num
  have havg0 : averageRegret (fun t => qId2 t 0) (scaledLoss pU2 l2 0) = 0 := by
    have hexp : expectedLoss (fun t => qId2 t 0) (scaledLoss pU2 l2 0) = 3 := by
      norm_num [expectedLoss, scaledLoss, qId2, pU2, l2, Fin.sum_univ_two]
    rw [averageRegret, externalRegret, hexp, hmin_scaled]
    norm_num
  have havg1 : averageRegret (fun t => qId2 t 1) (scaledLoss pU2 l2 1)
      = 3 / 2 := by
    have hexp : expectedLoss (fun t => qId2 t 1) (scaledLoss pU2 l2 1) = 6 := by
      norm_num [expectedLoss, scaledLoss, qId2, pU2, l2, Fin.sum_univ_two]
    rw [averageRegret, externalRegret, hexp, hmin_scaled]
    norm_num
  have hswap : swapRegret pU2 l2 = 3 := by
    have h01 : ∀ i : Fin 2, i = 0 ∨ i = 1 := by
      intro i
      fin_cases i
      · exact Or.inl rfl
      · exact Or.inr rfl
    have hexp : expectedLoss pU2 l2 = 9 := by
      norm_num [expectedLoss, pU2, l2, Fin.sum_univ_two]
    have hmin : Finset.univ.inf' Finset.univ_nonempty
        (fun δ : Fin 2 → Fin 2 => ∑ t, ∑ a, pU2 t a * l2 t (δ a)) = 6 := by
      apply le_antisymm
      · calc Finset.univ.inf' Finset.univ_nonempty
              (fun δ : Fin 2 → Fin 2 => ∑ t, ∑ a, pU2 t a * l2 t (δ a))
            ≤ (fun δ : Fin 2 → Fin 2 => ∑ t, ∑ a, pU2 t a * l2 t (δ a))
                (fun _ => 0) :=
              Finset.inf'_le _ (Finset.mem_univ _)
          _ = 6 := by
              norm_num [pU2, l2, Fin.sum_univ_two]
      · apply Finset.le_inf' _ _ (fun δ _ => ?_)
        simp only [pU2, l2, Fin.sum_univ_two]
        rcases h01 (δ 0) with h | h <;> rcases h01 (δ 1) with h' | h' <;>
          simp [h, h'] <;> norm_num
    rw [swapRegret, hexp, hmin]
    norm_num
  have hR : ∀ j, averageRegret (fun t => qId2 t j) (scaledLoss pU2 l2 j)
      ≤ 3 / 2 := by
    intro j
    fin_cases j
    · show averageRegret (fun t => qId2 t 0) (scaledLoss pU2 l2 0) ≤ 3 / 2
      rw [havg0]; norm_num
    · show averageRegret (fun t => qId2 t 1) (scaledLoss pU2 l2 1) ≤ 3 / 2
      rw [havg1]
  have h := swapRegret_div_le_card_mul_of_averageRegret_le qId2 pU2 l2
    hstat (3 / 2) hR
  refine ⟨hswap, havg0, havg1, ?_⟩
  calc swapRegret pU2 l2 / ((2 : ℕ) : ℝ)
      ≤ (Fintype.card (Fin 2) : ℝ) * (3 / 2) := h
    _ = 3 := by norm_num [Fintype.card_fin]

end MathlibExtTest.GameTheory.RegretBlumMansourBound

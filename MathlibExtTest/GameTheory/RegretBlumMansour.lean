/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.GameTheory.RegretBlumMansour
public import MathlibExt.GameTheory.Regret

set_option autoImplicit false

@[expose] public section

namespace MathlibExtTest.GameTheory.RegretBlumMansour

open MathlibExt.GameTheory.Regret
open scoped BigOperators

/-- Identity recommendations for the two-action test: copy `j` plays `j`. -/
def qId : Fin 1 → Fin 2 → Fin 2 → ℝ :=
  fun _ j a => if a = j then 1 else 0

/-- Uniform master play for the two-action test. -/
noncomputable def pU : Fin 1 → Fin 2 → ℝ :=
  fun _ _ => 1 / 2

/-- Example losses for the two-action test. -/
def l0 : Fin 1 → Fin 2 → ℝ :=
  fun _ a => if a = 0 then 2 else 6

theorem t1_stationary : IsStationaryPlay qId pU := by
  refine ⟨?_, ?_, ?_⟩
  · intro t j
    rw [isSimplex_iff]
    refine ⟨?_, ?_⟩
    · intro a
      fin_cases j <;> fin_cases a <;> simp [qId]
    · fin_cases j <;> simp [qId, Fin.sum_univ_two]
  · intro t
    rw [isSimplex_iff]
    refine ⟨?_, ?_⟩
    · intro a
      show (0 : ℝ) ≤ 1 / 2
      norm_num
    · simp only [pU, Fin.sum_univ_two]
      norm_num
  · intro t i
    simp only [pU, qId, Fin.sum_univ_two]
    fin_cases i <;> simp

theorem t2_consensus_value :
    expectedLoss pU l0 = 4 ∧
      ∑ j, expectedLoss (fun t => qId t j) (scaledLoss pU l0 j) = 4 := by
  constructor
  · simp only [expectedLoss, pU, l0, Fin.sum_univ_one, Fin.sum_univ_two]
    simp
    norm_num
  · simp only [expectedLoss, scaledLoss, qId, pU, l0, Fin.sum_univ_two,
      Fin.sum_univ_one]
    simp
    norm_num

/-- T3: the Blum-Mansour decomposition on the test fixture, with the swap
regret and both copies' external regrets evaluated. -/
theorem t3_blum_mansour_decomposition_example :
    swapRegret pU l0 = 2 ∧
      externalRegret (fun t => qId t 0) (scaledLoss pU l0 0) = 0 ∧
      externalRegret (fun t => qId t 1) (scaledLoss pU l0 1) = 2 ∧
      swapRegret pU l0 ≤
        ∑ j, externalRegret (fun t => qId t j) (scaledLoss pU l0 j) := by
  have h01 : ∀ i : Fin 2, i = 0 ∨ i = 1 := by
    intro i
    fin_cases i
    · exact Or.inl rfl
    · exact Or.inr rfl
  have hswap : swapRegret pU l0 = 2 := by
    have hmin : Finset.univ.inf' Finset.univ_nonempty
        (fun δ : Fin 2 → Fin 2 => ∑ t, ∑ a, pU t a * l0 t (δ a)) = 2 := by
      apply le_antisymm
      · calc Finset.univ.inf' Finset.univ_nonempty
              (fun δ : Fin 2 → Fin 2 => ∑ t, ∑ a, pU t a * l0 t (δ a))
            ≤ (fun δ : Fin 2 → Fin 2 => ∑ t, ∑ a, pU t a * l0 t (δ a))
                (fun _ => 0) :=
              Finset.inf'_le _ (Finset.mem_univ _)
          _ = 2 := by
              simp only [pU, l0, Fin.sum_univ_one, Fin.sum_univ_two]
              simp
              norm_num
      · apply Finset.le_inf' _ _ (fun δ _ => ?_)
        simp only [pU, l0, Fin.sum_univ_one, Fin.sum_univ_two]
        rcases h01 (δ 0) with h | h <;> rcases h01 (δ 1) with h' | h' <;>
          simp [h, h'] <;> norm_num
    rw [swapRegret, t2_consensus_value.1, hmin]
    norm_num
  have hcum : ∀ j a : Fin 2,
      cumulativeLoss (scaledLoss pU l0 j) a = if a = 0 then 1 else 3 := by
    intro j a
    fin_cases a <;> norm_num [cumulativeLoss, scaledLoss, pU, l0, Fin.sum_univ_one]
  have hmin_scaled : ∀ j : Fin 2, Finset.univ.inf' Finset.univ_nonempty
      (cumulativeLoss (scaledLoss pU l0 j)) = 1 := by
    intro j
    apply le_antisymm
    · calc Finset.univ.inf' Finset.univ_nonempty
            (cumulativeLoss (scaledLoss pU l0 j))
          ≤ cumulativeLoss (scaledLoss pU l0 j) 0 :=
            Finset.inf'_le _ (Finset.mem_univ _)
        _ = 1 := by simp [hcum]
    · apply Finset.le_inf' _ _ (fun a _ => ?_)
      fin_cases a <;> simp [hcum]
  have h0 : externalRegret (fun t => qId t 0) (scaledLoss pU l0 0) = 0 := by
    have hexp : expectedLoss (fun t => qId t 0) (scaledLoss pU l0 0) = 1 := by
      norm_num [expectedLoss, scaledLoss, qId, pU, l0, Fin.sum_univ_one,
        Fin.sum_univ_two]
    rw [externalRegret, hexp, hmin_scaled]
    norm_num
  have h1 : externalRegret (fun t => qId t 1) (scaledLoss pU l0 1) = 2 := by
    have hexp : expectedLoss (fun t => qId t 1) (scaledLoss pU l0 1) = 3 := by
      norm_num [expectedLoss, scaledLoss, qId, pU, l0, Fin.sum_univ_one,
        Fin.sum_univ_two]
    rw [externalRegret, hexp, hmin_scaled]
    norm_num
  exact ⟨hswap, h0, h1,
    swapRegret_le_sum_externalRegret_scaled qId pU l0 t1_stationary⟩

/-- Swap recommendations for the existence test: copy `j` plays the other action. -/
def qSwap : Fin 1 → Fin 2 → Fin 2 → ℝ :=
  fun _ j a => if a = j then 0 else 1

/-- T4: stationary-play existence applied to the swap recommendations; the
stationary play is forced to be uniform. -/
theorem t4_exists_stationary_swap :
    ∃ p : Fin 1 → Fin 2 → ℝ, IsStationaryPlay qSwap p ∧
      ∀ t, p t 0 = 1 / 2 ∧ p t 1 = 1 / 2 := by
  have hq : ∀ t j, IsSimplex (qSwap t j) := by
    intro t j
    rw [isSimplex_iff]
    refine ⟨?_, ?_⟩
    · intro a
      fin_cases j <;> fin_cases a <;> simp [qSwap]
    · fin_cases j <;> simp [qSwap, Fin.sum_univ_two]
  obtain ⟨p, hp⟩ := exists_isStationaryPlay qSwap hq
  refine ⟨p, hp, ?_⟩
  intro t
  have hsum : p t 0 + p t 1 = 1 := by
    have h := ((isSimplex_iff _).mp (hp.2.1 t)).2
    rwa [Fin.sum_univ_two] at h
  have h0 : p t 0 = p t 1 := by
    have h := hp.2.2 t 0
    simpa [qSwap, Fin.sum_univ_two] using h
  constructor <;> linarith

/-- T5: the expected-loss decomposition needs no `DecidableEq` and no
`Nonempty` instance on the actions. -/
theorem t5_expectedLoss_eq_sum_scaled_no_instances {K : Type*} [Fintype K] {T : ℕ}
    (q : Fin T → K → K → ℝ) (p loss : Fin T → K → ℝ) (hp : IsStationaryPlay q p) :
    expectedLoss p loss = ∑ j, expectedLoss (fun t => q t j) (scaledLoss p loss j) :=
  expectedLoss_eq_sum_scaled q p loss hp

/-- T6: with no `DecidableEq` instance on the actions, a stationary play exists
and its expected loss decomposes over the copies. -/
theorem t6_exists_stationary_no_decidableEq {K : Type*} [Fintype K] [Nonempty K] {T : ℕ}
    (q : Fin T → K → K → ℝ) (hq : ∀ t j, IsSimplex (q t j)) (loss : Fin T → K → ℝ) :
    ∃ p : Fin T → K → ℝ, IsStationaryPlay q p ∧
      expectedLoss p loss = ∑ j, expectedLoss (fun t => q t j) (scaledLoss p loss j) := by
  obtain ⟨p, hp⟩ := exists_isStationaryPlay q hq
  exact ⟨p, hp, expectedLoss_eq_sum_scaled q p loss hp⟩

end MathlibExtTest.GameTheory.RegretBlumMansour

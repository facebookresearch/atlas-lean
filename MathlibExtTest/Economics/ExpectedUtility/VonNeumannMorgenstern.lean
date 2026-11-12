/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Economics.ExpectedUtility.VonNeumannMorgenstern
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

@[expose] public section

open Convexity MathlibExt.Economics.ExpectedUtility

namespace MathlibExtTest.Economics.ExpectedUtility.VonNeumannMorgenstern

/-- The expected-utility preference of the Bernoulli utility `![0, 1]` on two outcomes. -/
def euPref : StdSimplex ℝ (Fin 2) → StdSimplex ℝ (Fin 2) → Prop :=
  fun p q => expectedUtility ![0, 1] q ≤ expectedUtility ![0, 1] p

theorem euPref_isPreferenceRelation : IsPreferenceRelation euPref := by
  constructor
  · intro p q
    exact le_total _ _
  · intro p q r hpq hqr
    exact le_trans hqr hpq

theorem euPref_independence : SatisfiesIndependence euPref := by
  intro p q r α h0 h1
  unfold euPref
  rw [expectedUtility_mix, expectedUtility_mix]
  rw [add_le_add_iff_right]
  exact (mul_le_mul_iff_of_pos_left h0).symm

theorem euPref_archimedean : SatisfiesArchimedean euPref := by
  intro p q r hpq hqr
  have hba : expectedUtility ![0, 1] q < expectedUtility ![0, 1] p := not_le.mp hpq.2
  have hcb : expectedUtility ![0, 1] r < expectedUtility ![0, 1] q := not_le.mp hqr.2
  set a : ℝ := expectedUtility ![0, 1] p with ha
  set b : ℝ := expectedUtility ![0, 1] q with hb
  set c : ℝ := expectedUtility ![0, 1] r with hc
  have hac : (0 : ℝ) < a - c := by linarith
  have hbc : (0 : ℝ) < b - c := by linarith
  set t : ℝ := (b - c) / (a - c) with ht
  have ht0 : (0 : ℝ) < t := div_pos hbc hac
  have ht1 : t < 1 := by
    rw [div_lt_one hac]
    linarith
  have ht_eq : t * (a - c) = b - c := div_mul_cancel₀ _ (ne_of_gt hac)
  refine ⟨(1 + t) / 2, t / 2, by linarith, by linarith, by linarith, by linarith, ?_, ?_⟩
  · have hαt : t < (1 + t) / 2 := by linarith
    have hmul : t * (a - c) < ((1 + t) / 2) * (a - c) :=
      mul_lt_mul_of_pos_right hαt hac
    have key : b < ((1 + t) / 2) * a + (1 - (1 + t) / 2) * c := by
      have e1 : b = t * (a - c) + c := by rw [ht_eq]; ring
      have e2 : ((1 + t) / 2) * a + (1 - (1 + t) / 2) * c
          = ((1 + t) / 2) * (a - c) + c := by ring
      rw [e1, e2]
      linarith
    unfold StrictPref euPref
    rw [expectedUtility_mix]
    exact ⟨le_of_lt key, not_le_of_gt key⟩
  · have hβt : t / 2 < t := by linarith
    have hmul : (t / 2) * (a - c) < t * (a - c) :=
      mul_lt_mul_of_pos_right hβt hac
    have key : (t / 2) * a + (1 - t / 2) * c < b := by
      have e1 : b = t * (a - c) + c := by rw [ht_eq]; ring
      have e2 : (t / 2) * a + (1 - t / 2) * c = (t / 2) * (a - c) + c := by ring
      rw [e1, e2]
      linarith
    unfold StrictPref euPref
    rw [expectedUtility_mix]
    exact ⟨le_of_lt key, not_le_of_gt key⟩

theorem euPref_representation :
    ∃ u : Fin 2 → ℝ, IsExpectedUtilityRepresentation euPref u := by
  exact exists_isExpectedUtilityRepresentation euPref_isPreferenceRelation
    euPref_independence euPref_archimedean

/-- Every lottery indifferent to every other (all outcomes indifferent). -/
def allIndifferent : StdSimplex ℝ (Fin 3) → StdSimplex ℝ (Fin 3) → Prop :=
  fun _ _ => True

theorem allIndifferent_axioms :
    IsPreferenceRelation allIndifferent ∧ SatisfiesIndependence allIndifferent ∧
      SatisfiesArchimedean allIndifferent := by
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · intro p q
    exact Or.inl trivial
  · intro p q r _ _
    exact trivial
  · intro p q r α h0 h1
    exact Iff.rfl
  · intro p q r hpq hqr
    exact absurd hpq.1 hpq.2

theorem allIndifferent_zero_representation :
    IsExpectedUtilityRepresentation allIndifferent 0 := by
  intro p q
  constructor
  · intro _
    simp [expectedUtility]
  · intro _
    trivial

/-- Mixing with weight one returns the first lottery; with weight zero, the second. -/
theorem mix_one_zero (p q : StdSimplex ℝ (Fin 2)) :
    mix 1 zero_le_one le_rfl p q = p ∧ mix 0 le_rfl zero_le_one p q = q := by
  exact ⟨mix_one zero_le_one le_rfl p q, mix_zero le_rfl zero_le_one p q⟩

/-- Expected utility of a point mass is the utility of its outcome. -/
theorem expectedUtility_single (u : Fin 3 → ℝ) (x : Fin 3) :
    expectedUtility u (StdSimplex.single x) = u x := by
  unfold expectedUtility
  rw [StdSimplex.weights_single]
  rw [Finset.sum_eq_single x]
  · simp
  · intro y _ hy
    rw [Finsupp.single_eq_of_ne hy]
    exact zero_mul _
  · intro h
    exact absurd (Finset.mem_univ x) h

end MathlibExtTest.Economics.ExpectedUtility.VonNeumannMorgenstern

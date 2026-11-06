/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisFifthRootEightFinalPairQ
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisFifthRootEightFinalOctadNumerator
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisFifthRootEightShortCache

/-! Actual nonzero original short witnesses for root-eight phase constraints. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

/-- Twenty-two physical pair or octad short coordinates of the actual source. -/
def generatedFifthRootEightQSupportIndex : Fin 22 → GriessShortIndex :=
  ![Sum.inl (0, 0),
    Sum.inl (1, 0),
    Sum.inl (0, 1),
    Sum.inl (0, 2),
    Sum.inl (0, 7),
    Sum.inl (0, 10),
    Sum.inl (0, 17),
    Sum.inl (0, 18),
    Sum.inl (0, 19),
    Sum.inl (0, 25),
    Sum.inl (0, 26),
    Sum.inl (0, 27),
    Sum.inr (Sum.inl (228, 0)),
    Sum.inr (Sum.inl (229, 0)),
    Sum.inr (Sum.inl (507, 0)),
    Sum.inr (Sum.inl (246, 0)),
    Sum.inr (Sum.inl (235, 1)),
    Sum.inr (Sum.inl (249, 0)),
    Sum.inr (Sum.inl (227, 0)),
    Sum.inr (Sum.inl (731, 1)),
    Sum.inr (Sum.inl (486, 0)),
    Sum.inr (Sum.inl (109, 0))]

/-- The complete rational original-source formula at each selected physical coordinate. -/
def generatedFifthRootEightQSupportValue (j : Fin 22) : ℚ :=
  match generatedFifthRootEightQSupportIndex j with
  | Sum.inl (s, p) => generatedFifthRootEightFinalPairQ s p
  | Sum.inr (Sum.inl (o, e)) => (generatedFifthRootEightFinalOctadNumerator o e : ℚ) / 128
  | Sum.inr (Sum.inr _) => 0

/-- The selected source numerators; all actual signs are retained. -/
def generatedFifthRootEightQSupportNumerator : Fin 22 → ℤ :=
  ![4, -4, 4, 8, -4, 4, 4, -4, -4, 4, 4, -4, -8, 4, -4, 4, 4, 4, -8, -4, 4, 4]

/-- Every original pair numerator equals its exact complete signed source cache. -/
theorem generatedFifthRootEight_incoming_pair_cached_integer (s : Fin 2) (p : Fin 276) :
    generatedFifthRootEightIncomingPairNumerator s p =
      generatedFifthRootEightShortCachedCoefficient (Sum.inl (s, p)) := by
  have h := generatedFifthRootEight_incoming_pair_numerator s p
  have hc : (griessConwayEncode
      (rhoLocal generatedFifthRootEightLocal generatedFifthAxis)).2.1 (Sum.inl (s, p)) =
        (generatedFifthRootEightShortCachedCoefficient (Sum.inl (s, p)) : ℝ) / 16 := by
    change (griessConwayEncode
      (rhoLocal (generatedAxisGlobalFifthShortLocalWord 8) generatedFifthAxis)).2.1 _ = _
    rw [generatedAxisGlobalFifthRoot08Packet_actual,
      generatedFifthRootEight_incoming_short_actual,
      generatedFifthRootEight_short_cached_coefficient_actual]
  rw [hc] at h
  have hi : (generatedFifthRootEightIncomingPairNumerator s p : ℝ) =
      (generatedFifthRootEightShortCachedCoefficient (Sum.inl (s, p)) : ℝ) := by linarith
  exact_mod_cast hi

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
-- Evaluate all twenty-two complete rational source formulas using the verified original caches.
/-- Every selected rational formula has precisely its stated signed nonzero numerator. -/
theorem generatedFifthRootEight_Q_support_value_checked : ∀ j : Fin 22,
    generatedFifthRootEightQSupportValue j =
      (generatedFifthRootEightQSupportNumerator j : ℚ) / 128 := by
  unfold generatedFifthRootEightQSupportValue
  simp only [generatedFifthRootEightFinalPairQ, generatedFifthRootEightFinalOctadNumerator]
  simp_rw [← generatedAxisGlobalPairCoordinates_actual,
    generatedFifthRootEight_incoming_pair_cached_integer,
    ← generatedFifthRootEight_short_cached_coefficient_actual]
  decide +kernel

/-- Every selected original source numerator is nonzero. -/
theorem generatedFifthRootEight_Q_support_numerator_ne_zero (j : Fin 22) :
    generatedFifthRootEightQSupportNumerator j ≠ 0 := by
  revert j
  decide +kernel

/-- Whether the original physical label is a pair or octad rather than an odd label. -/
private def evenShortLabel : GriessShortIndex → Bool
  | Sum.inr (Sum.inr _) => false
  | _ => true

/-- Every selected original short coordinate equals its complete rational source value. -/
theorem generatedFifthRootEight_Q_support_coordinate (j : Fin 22) :
    (griessConwayEncode generatedFifthRootEightAxis).2.1
      (generatedFifthRootEightQSupportIndex j) =
        (generatedFifthRootEightQSupportValue j : ℝ) := by
  have hn : ∀ j : Fin 22,
      evenShortLabel (generatedFifthRootEightQSupportIndex j) = true := by decide +kernel
  rcases h : generatedFifthRootEightQSupportIndex j with ⟨a, b⟩ | (⟨a, b⟩ | ⟨a, b⟩)
  · simp only [generatedFifthRootEightQSupportValue, h]
    exact generatedFifthRootEight_final_pair_q a b
  · simp only [generatedFifthRootEightQSupportValue, h]
    push_cast
    exact generatedFifthRootEight_final_octad_numerator a b
  · have hf := hn j
    simp only [h, evenShortLabel, Bool.false_eq_true] at hf

/-- Every selected physical coefficient of the original complete axis is genuinely nonzero. -/
theorem generatedFifthRootEight_Q_support_nonzero (j : Fin 22) :
    (griessConwayEncode generatedFifthRootEightAxis).2.1
      (generatedFifthRootEightQSupportIndex j) ≠ 0 := by
  rw [generatedFifthRootEight_Q_support_coordinate,
    generatedFifthRootEight_Q_support_value_checked]
  push_cast
  exact div_ne_zero
    (by exact_mod_cast generatedFifthRootEight_Q_support_numerator_ne_zero j) (by norm_num)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

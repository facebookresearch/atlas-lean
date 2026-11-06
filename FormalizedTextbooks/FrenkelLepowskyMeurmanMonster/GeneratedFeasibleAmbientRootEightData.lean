/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleAmbientIntegerZero
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightPositiveFinalShortSourceActual
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightPositiveFinalShortInteger
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsRawFormula
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsPairCoordinates

/-! Integer data for the actual Root8 prototype in its positive final normalization.

The matrix numerator over 256 is fixed by the incoming diagonal and the incoming pair
coefficients; a nonnegative rank-one decomposition shows that it dominates `48 I`. The
short numerators over 256 are the complete packed cache of the existing Root8 work. The
per-label orthogonality check used by the address packets is defined here. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The matrix numerator, over 256, of the actual positive final Root8 axis. -/
def generatedFeasibleAmbientRootEightN : Fin 24 → Fin 24 → ℤ :=
  ![![80, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 96, 16, 0, 0, 0, 0, 0, -16, 0, 0, 16, 0, 0, 0, 0, -16, 16, -16, -16, 16, 0, 16, 0],
    ![0, 16, 96, 0, 0, 0, 0, 0, -16, 0, 0, 16, 0, 0, 0, 0, -16, 16, -16, -16, 16, 0, 16, 0],
    ![0, 0, 0, 80, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 80, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 80, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 80, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 80, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, -16, -16, 0, 0, 0, 0, 0, 96, 0, 0, -16, 0, 0, 0, 0, 16, -16, 16, 16, -16, 0, -16, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 80, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 80, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 16, 16, 0, 0, 0, 0, 0, -16, 0, 0, 96, 0, 0, 0, 0, -16, 16, -16, -16, 16, 0, 16, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 80, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 80, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 80, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 80, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, -16, -16, 0, 0, 0, 0, 0, 16, 0, 0, -16, 0, 0, 0, 0, 80, -32, 16, 16, -16, 0, -16, 0],
    ![0, 16, 16, 0, 0, 0, 0, 0, -16, 0, 0, 16, 0, 0, 0, 0, -32, 80, -16, -16, 16, 0, 16, 0],
    ![0, -16, -16, 0, 0, 0, 0, 0, 16, 0, 0, -16, 0, 0, 0, 0, 16, -16, 96, 16, -16, 0, -16, 0],
    ![0, -16, -16, 0, 0, 0, 0, 0, 16, 0, 0, -16, 0, 0, 0, 0, 16, -16, 16, 96, -16, 0, -16, 0],
    ![0, 16, 16, 0, 0, 0, 0, 0, -16, 0, 0, 16, 0, 0, 0, 0, -16, 16, -16, -16, 96, 0, 16, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 80, 0, 0],
    ![0, 16, 16, 0, 0, 0, 0, 0, -16, 0, 0, 16, 0, 0, 0, 0, -16, 16, -16, -16, 16, 0, 96, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 80]]

/-- Rank-one directions of the positive semidefinite certificate. -/
def generatedFeasibleAmbientRootEightW : Fin 24 → Fin 24 → ℤ :=
  ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 3, 1, 0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0, -1, 1, -1, -1, 1, 0, 1, 0],
    ![0, 0, 4, 0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0, -1, 1, -1, -1, 1, 0, 1, 0],
    ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 5, 0, 0, -1, 0, 0, 0, 0, 1, -1, 1, 1, -1, 0, -1, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6, 0, 0, 0, 0, -1, 1, -1, -1, 1, 0, 1, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, -4, 1, 1, -1, 0, -1, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 1, -1, 0, -1, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 10, -1, 0, -1, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 11, 0, 1, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]]

/-- Nonnegative weights of the positive semidefinite certificate. -/
def generatedFeasibleAmbientRootEightC : Fin 24 → ℤ :=
  ![15840, 2640, 1320, 15840, 15840, 15840, 15840, 15840, 792, 15840, 15840, 528, 15840, 15840,
    15840, 15840, 660, 0, 220, 176, 144, 15840, 17280, 15840]

set_option maxRecDepth 100000 in
-- The 576 matrix entries are checked against 24 rank-one terms.
private theorem decomp : ∀ i j : Fin 24, 495 * generatedFeasibleAmbientRootEightN i j =
    495 * 48 * (if i = j then 1 else 0) + ∑ k, generatedFeasibleAmbientRootEightC k *
      (generatedFeasibleAmbientRootEightW k i * generatedFeasibleAmbientRootEightW k j) := by
  decide +kernel

/-- The Root8 matrix numerator dominates `48 I` on every integral vector. -/
theorem generatedFeasibleAmbient_rootEight_quad_ge (u : Fin 24 → ℤ) :
    48 * ∑ i, u i ^ 2 ≤ generatedFeasibleAmbientQuad generatedFeasibleAmbientRootEightN u :=
  generatedFeasibleAmbient_quad_ge_of_decomp _ 48 495 generatedFeasibleAmbientRootEightC
    generatedFeasibleAmbientRootEightW (by norm_num) (by decide) decomp u

private theorem diag_check : ∀ i : Fin 24,
    generatedFeasibleAmbientRootEightN i i = generatedRootEightIncomingMatrixNumerator i i := by
  decide +kernel

set_option maxRecDepth 100000 in
-- All 276 incoming pair coefficients are looked up in the existing exact cache.
private theorem pair_check : ∀ p : Fin 276,
    generatedFeasibleAmbientRootEightN (generatedAxisGlobalPairCoordinates p).1
      (generatedAxisGlobalPairCoordinates p).2 =
      8 * (generatedFifthRootEightShortCachedCoefficient (Sum.inl (0, p)) +
        generatedFifthRootEightShortCachedCoefficient (Sum.inl (1, p))) := by
  decide +kernel

private theorem symm_check : ∀ i j : Fin 24,
    generatedFeasibleAmbientRootEightN i j = generatedFeasibleAmbientRootEightN j i := by
  decide +kernel

private theorem pairIndex_coordinates (i j : Fin 24) (h : i ≠ j) :
    griessCoordinatePair (griessPairIndex i j h) = if i < j then (i, j) else (j, i) := by
  simp only [griessCoordinatePair, griessPairIndex, Equiv.apply_symm_apply]

/-- Every actual matrix coordinate of the positive final Root8 axis. -/
theorem generatedFeasibleAmbient_rootEight_matrix (i j : Fin 24) :
    (griessConwayEncode generatedRootEightIncomingPositiveTrialityDestination).1 i j =
      (generatedFeasibleAmbientRootEightN i j : ℝ) / 256 := by
  rw [generatedRootEightIncomingPositiveTrialityDestination,
    generatedAxisGlobalRawTrialityFormula_actual]
  change generatedAxisGlobalRawTrialityMatrix
    (griessConwayEncode generatedRootEightIncomingPositiveDestination) i j = _
  unfold generatedAxisGlobalRawTrialityMatrix
  by_cases h : i = j
  · subst h
    rw [dite_eq_left rfl, generatedRootEight_incoming_positive_matrix_integer, diag_check]
  · rw [dite_eq_right h, generatedRootEight_incoming_positive_short_integer,
      generatedRootEight_incoming_positive_short_integer]
    set p := griessPairIndex i j h with hp
    have hc := pairIndex_coordinates i j h
    rw [← hp, ← generatedAxisGlobalPairCoordinates_actual] at hc
    have hpair := pair_check p
    rw [hc] at hpair
    have hN : generatedFeasibleAmbientRootEightN i j =
        8 * (generatedFifthRootEightShortCachedCoefficient (Sum.inl (0, p)) +
          generatedFifthRootEightShortCachedCoefficient (Sum.inl (1, p))) := by
      split_ifs at hpair with hij
      · exact hpair
      · rw [symm_check]
        exact hpair
    rw [hN]
    push_cast
    ring

/-- Every actual short coordinate of the positive final Root8 axis, from the packed cache. -/
theorem generatedFeasibleAmbient_rootEight_short (r : GriessShortIndex) :
    (griessConwayEncode generatedRootEightIncomingPositiveTrialityDestination).2.1 r =
      (generatedRootEightPositiveFinalShortCachedNumerator r : ℝ) / 256 := by
  rw [generatedRootEight_positive_final_short_integer,
    generatedRootEight_positive_final_short_source_actual]

/-- The orthogonality catalogue of the positive final Root8 axis: one signed pair axis. -/
def generatedFeasibleAmbientRootEightZeroSet : Finset (GriessShortIndex × ZMod 2) :=
  {(Sum.inl (1, 248), 0)}

/-- The integer orthogonality test for one signed axis against the positive final Root8 axis. -/
def generatedFeasibleAmbientRootEightTest (r : GriessShortIndex) (c : ZMod 2) : Prop :=
  ((256 : ℕ) : ℤ) * generatedFeasibleAmbientQuad generatedFeasibleAmbientRootEightN
      (generatedAxisGlobalShortIntegral r) =
    32 * ((256 : ℕ) : ℤ) * generatedFeasibleAmbientSign c *
      generatedRootEightPositiveFinalShortCachedNumerator r →
    (r, c) ∈ generatedFeasibleAmbientRootEightZeroSet

instance (r : GriessShortIndex) (c : ZMod 2) :
    Decidable (generatedFeasibleAmbientRootEightTest r c) := by
  unfold generatedFeasibleAmbientRootEightTest
  infer_instance

/-- The finite check at one short label: a small numerator, or both signs tested exactly. -/
def generatedFeasibleAmbientRootEightCheck (r : GriessShortIndex) : Prop :=
  |generatedRootEightPositiveFinalShortCachedNumerator r| < 48 ∨
    (generatedFeasibleAmbientRootEightTest r 0 ∧ generatedFeasibleAmbientRootEightTest r 1)

instance (r : GriessShortIndex) : Decidable (generatedFeasibleAmbientRootEightCheck r) := by
  unfold generatedFeasibleAmbientRootEightCheck
  infer_instance

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

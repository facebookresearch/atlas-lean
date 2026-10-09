/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Quantum.Grover.Symmetry
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Tactic

/-!
# Exact analysis of Grover search

For a nonempty proper marked subset, define
`θ = arcsin (sqrt (marked.card / Fintype.card α))`. In normalized coordinates,
one Grover step is rotation by `2θ`. Consequently, after `k` iterations the
marked probability is `sin² ((2k + 1)θ)`.
-/

@[expose] public section

namespace Cslib.Grover

private theorem sin_arcsin_sqrt_div (m u n : ℝ) (hm : 0 ≤ m) (hu : 0 ≤ u)
    (hn : n = m + u) (hn0 : n ≠ 0) :
    Real.sin (Real.arcsin (Real.sqrt (m / n))) =
      Real.sqrt m / Real.sqrt n := by
  have hnnonneg : 0 ≤ n := by nlinarith
  have hnpos : 0 < n := lt_of_le_of_ne hnnonneg (Ne.symm hn0)
  have hp1 : m / n ≤ 1 := (div_le_one hnpos).2 (by nlinarith)
  rw [Real.sin_arcsin (by linarith [Real.sqrt_nonneg (m / n)])
    (Real.sqrt_le_one.mpr hp1), Real.sqrt_div hm]

private theorem cos_arcsin_sqrt_div (m u n : ℝ) (hm : 0 ≤ m) (hu : 0 ≤ u)
    (hn : n = m + u) (hn0 : n ≠ 0) :
    Real.cos (Real.arcsin (Real.sqrt (m / n))) =
      Real.sqrt u / Real.sqrt n := by
  have hnnonneg : 0 ≤ n := by nlinarith
  have hnpos : 0 < n := lt_of_le_of_ne hnnonneg (Ne.symm hn0)
  have hp0 : 0 ≤ m / n := div_nonneg hm hnpos.le
  rw [Real.cos_arcsin, Real.sq_sqrt hp0]
  have hone : 1 - m / n = u / n := by
    field_simp
    nlinarith
  rw [hone, Real.sqrt_div hu]

private theorem cos_two_arcsin_sqrt_div (m u n : ℝ) (hm : 0 ≤ m)
    (hu : 0 ≤ u) (hn : n = m + u) (hn0 : n ≠ 0) :
    Real.cos (2 * Real.arcsin (Real.sqrt (m / n))) = (u - m) / n := by
  rw [Real.cos_two_mul', sin_arcsin_sqrt_div m u n hm hu hn hn0,
    cos_arcsin_sqrt_div m u n hm hu hn hn0]
  have hnnonneg : 0 ≤ n := by nlinarith
  have hnpos : 0 < n := lt_of_le_of_ne hnnonneg (Ne.symm hn0)
  have hsqrtn0 : Real.sqrt n ≠ 0 := (Real.sqrt_pos.2 hnpos).ne'
  rw [div_pow, div_pow, Real.sq_sqrt hm, Real.sq_sqrt hu,
    Real.sq_sqrt hnnonneg]
  field_simp

private theorem sin_two_arcsin_sqrt_div (m u n : ℝ) (hm : 0 ≤ m)
    (hu : 0 ≤ u) (hn : n = m + u) (hn0 : n ≠ 0) :
    Real.sin (2 * Real.arcsin (Real.sqrt (m / n))) =
      2 * Real.sqrt m * Real.sqrt u / n := by
  rw [Real.sin_two_mul, sin_arcsin_sqrt_div m u n hm hu hn hn0,
    cos_arcsin_sqrt_div m u n hm hu hn hn0]
  have hnnonneg : 0 ≤ n := by nlinarith
  have hnpos : 0 < n := lt_of_le_of_ne hnnonneg (Ne.symm hn0)
  have hsqrtn0 : Real.sqrt n ≠ 0 := (Real.sqrt_pos.2 hnpos).ne'
  field_simp
  rw [Real.sq_sqrt hnnonneg]
  ring

/-- Grover's angle for a marked subset of a finite search space. -/
noncomputable def groverAngle {α : Type*} [Fintype α] (marked : Finset α) : ℝ :=
  Real.arcsin (Real.sqrt ((marked.card : ℝ) / Fintype.card α))

private theorem card_cast_eq_marked_add_unmarked {α : Type*} [Fintype α]
    [DecidableEq α] (marked : Finset α) :
    (Fintype.card α : ℝ) = (marked.card : ℝ) + (markedᶜ.card : ℝ) := by
  exact_mod_cast (Finset.card_add_card_compl marked).symm

theorem sin_groverAngle {α : Type*} [Fintype α]
    (marked : Finset α) (hMarked : marked.Nonempty) :
    Real.sin (groverAngle marked) =
      Real.sqrt marked.card / Real.sqrt (Fintype.card α) := by
  classical
  have hm : 0 ≤ (marked.card : ℝ) := by positivity
  have hu : 0 ≤ (markedᶜ.card : ℝ) := by positivity
  have hn := card_cast_eq_marked_add_unmarked marked
  have hmpos : 0 < (marked.card : ℝ) := by
    exact_mod_cast (Finset.card_pos.mpr hMarked)
  have hn0 : (Fintype.card α : ℝ) ≠ 0 := by nlinarith
  exact sin_arcsin_sqrt_div _ _ _ hm hu hn hn0

theorem cos_groverAngle {α : Type*} [Fintype α] [DecidableEq α]
    (marked : Finset α) (hMarked : marked.Nonempty) :
    Real.cos (groverAngle marked) =
      Real.sqrt markedᶜ.card / Real.sqrt (Fintype.card α) := by
  have hm : 0 ≤ (marked.card : ℝ) := by positivity
  have hu : 0 ≤ (markedᶜ.card : ℝ) := by positivity
  have hn := card_cast_eq_marked_add_unmarked marked
  have hmpos : 0 < (marked.card : ℝ) := by
    exact_mod_cast (Finset.card_pos.mpr hMarked)
  have hn0 : (Fintype.card α : ℝ) ≠ 0 := by nlinarith
  exact cos_arcsin_sqrt_div _ _ _ hm hu hn hn0

theorem cos_two_groverAngle {α : Type*} [Fintype α] [DecidableEq α]
    (marked : Finset α) (hMarked : marked.Nonempty) :
    Real.cos (2 * groverAngle marked) =
      ((markedᶜ.card : ℝ) - marked.card) / Fintype.card α := by
  have hm : 0 ≤ (marked.card : ℝ) := by positivity
  have hu : 0 ≤ (markedᶜ.card : ℝ) := by positivity
  have hn := card_cast_eq_marked_add_unmarked marked
  have hmpos : 0 < (marked.card : ℝ) := by
    exact_mod_cast (Finset.card_pos.mpr hMarked)
  have hn0 : (Fintype.card α : ℝ) ≠ 0 := by nlinarith
  exact cos_two_arcsin_sqrt_div _ _ _ hm hu hn hn0

theorem sin_two_groverAngle {α : Type*} [Fintype α] [DecidableEq α]
    (marked : Finset α) (hMarked : marked.Nonempty) :
    Real.sin (2 * groverAngle marked) =
      2 * Real.sqrt marked.card * Real.sqrt markedᶜ.card /
        Fintype.card α := by
  have hm : 0 ≤ (marked.card : ℝ) := by positivity
  have hu : 0 ≤ (markedᶜ.card : ℝ) := by positivity
  have hn := card_cast_eq_marked_add_unmarked marked
  have hmpos : 0 < (marked.card : ℝ) := by
    exact_mod_cast (Finset.card_pos.mpr hMarked)
  have hn0 : (Fintype.card α : ℝ) ≠ 0 := by nlinarith
  exact sin_two_arcsin_sqrt_div _ _ _ hm hu hn hn0

/-- Symmetric state whose total marked and unmarked coordinates are
`sin φ` and `cos φ`, respectively. -/
noncomputable def angleAmplitude {α : Type*} [Fintype α] [DecidableEq α]
    (marked : Finset α) (φ : ℝ) : Amplitude α :=
  symmetricAmplitude marked (Real.sin φ / Real.sqrt marked.card)
    (Real.cos φ / Real.sqrt markedᶜ.card)

private theorem marked_update_algebra (m u n sm su θ φ : ℝ)
    (hn : n = m + u) (hn0 : n ≠ 0) (hsm0 : sm ≠ 0) (hsu0 : su ≠ 0)
    (hsm : sm ^ 2 = m) (hsu : su ^ 2 = u)
    (hcos : Real.cos (2 * θ) = (u - m) / n)
    (hsin : Real.sin (2 * θ) = 2 * sm * su / n) :
    2 * ((u * (Real.cos φ / su) - m * (Real.sin φ / sm)) / n) +
        Real.sin φ / sm =
      Real.sin (φ + 2 * θ) / sm := by
  rw [Real.sin_add, hcos, hsin]
  field_simp
  rw [hn, ← hsm, ← hsu]
  ring

private theorem unmarked_update_algebra (m u n sm su θ φ : ℝ)
    (hn : n = m + u) (hn0 : n ≠ 0) (hsm0 : sm ≠ 0) (hsu0 : su ≠ 0)
    (hsm : sm ^ 2 = m) (hsu : su ^ 2 = u)
    (hcos : Real.cos (2 * θ) = (u - m) / n)
    (hsin : Real.sin (2 * θ) = 2 * sm * su / n) :
    2 * ((u * (Real.cos φ / su) - m * (Real.sin φ / sm)) / n) -
        Real.cos φ / su =
      Real.cos (φ + 2 * θ) / su := by
  rw [Real.cos_add, hcos, hsin]
  field_simp
  rw [hn, ← hsm, ← hsu]
  ring

private theorem markedAmplitudeNext_angleAmplitude {α : Type*} [Fintype α]
    [DecidableEq α] (marked : Finset α) (hMarked : marked.Nonempty)
    (hUnmarked : markedᶜ.Nonempty) (φ : ℝ) :
    markedAmplitudeNext marked
        (Real.sin φ / Real.sqrt marked.card)
        (Real.cos φ / Real.sqrt markedᶜ.card) =
      Real.sin (φ + 2 * groverAngle marked) / Real.sqrt marked.card := by
  have hmpos : 0 < (marked.card : ℝ) := by
    exact_mod_cast (Finset.card_pos.mpr hMarked)
  have hupos : 0 < (markedᶜ.card : ℝ) := by
    exact_mod_cast (Finset.card_pos.mpr hUnmarked)
  have hn := card_cast_eq_marked_add_unmarked marked
  have hn0 : (Fintype.card α : ℝ) ≠ 0 := by nlinarith
  have hsm0 : Real.sqrt (marked.card : ℝ) ≠ 0 :=
    (Real.sqrt_pos.2 hmpos).ne'
  have hsu0 : Real.sqrt (markedᶜ.card : ℝ) ≠ 0 :=
    (Real.sqrt_pos.2 hupos).ne'
  unfold markedAmplitudeNext oracleMean
  exact marked_update_algebra _ _ _ _ _ _ _ hn hn0 hsm0 hsu0
    (Real.sq_sqrt hmpos.le) (Real.sq_sqrt hupos.le)
    (cos_two_groverAngle marked hMarked)
    (sin_two_groverAngle marked hMarked)

private theorem unmarkedAmplitudeNext_angleAmplitude {α : Type*} [Fintype α]
    [DecidableEq α] (marked : Finset α) (hMarked : marked.Nonempty)
    (hUnmarked : markedᶜ.Nonempty) (φ : ℝ) :
    unmarkedAmplitudeNext marked
        (Real.sin φ / Real.sqrt marked.card)
        (Real.cos φ / Real.sqrt markedᶜ.card) =
      Real.cos (φ + 2 * groverAngle marked) / Real.sqrt markedᶜ.card := by
  have hmpos : 0 < (marked.card : ℝ) := by
    exact_mod_cast (Finset.card_pos.mpr hMarked)
  have hupos : 0 < (markedᶜ.card : ℝ) := by
    exact_mod_cast (Finset.card_pos.mpr hUnmarked)
  have hn := card_cast_eq_marked_add_unmarked marked
  have hn0 : (Fintype.card α : ℝ) ≠ 0 := by nlinarith
  have hsm0 : Real.sqrt (marked.card : ℝ) ≠ 0 :=
    (Real.sqrt_pos.2 hmpos).ne'
  have hsu0 : Real.sqrt (markedᶜ.card : ℝ) ≠ 0 :=
    (Real.sqrt_pos.2 hupos).ne'
  unfold unmarkedAmplitudeNext oracleMean
  exact unmarked_update_algebra _ _ _ _ _ _ _ hn hn0 hsm0 hsu0
    (Real.sq_sqrt hmpos.le) (Real.sq_sqrt hupos.le)
    (cos_two_groverAngle marked hMarked)
    (sin_two_groverAngle marked hMarked)

theorem groverStep_angleAmplitude {α : Type*} [Fintype α] [DecidableEq α]
    (marked : Finset α) (hMarked : marked.Nonempty)
    (hUnmarked : markedᶜ.Nonempty) (φ : ℝ) :
    groverStep marked (angleAmplitude marked φ) =
      angleAmplitude marked (φ + 2 * groverAngle marked) := by
  unfold angleAmplitude
  rw [groverStep_symmetricAmplitude,
    markedAmplitudeNext_angleAmplitude marked hMarked hUnmarked,
    unmarkedAmplitudeNext_angleAmplitude marked hMarked hUnmarked]

theorem angleAmplitude_groverAngle_eq_uniform {α : Type*} [Fintype α]
    [DecidableEq α] (marked : Finset α) (hMarked : marked.Nonempty)
    (hUnmarked : markedᶜ.Nonempty) :
    angleAmplitude marked (groverAngle marked) = uniformAmplitude α := by
  have hmpos : 0 < (marked.card : ℝ) := by
    exact_mod_cast (Finset.card_pos.mpr hMarked)
  have hupos : 0 < (markedᶜ.card : ℝ) := by
    exact_mod_cast (Finset.card_pos.mpr hUnmarked)
  have hsm0 : Real.sqrt (marked.card : ℝ) ≠ 0 :=
    (Real.sqrt_pos.2 hmpos).ne'
  have hsu0 : Real.sqrt (markedᶜ.card : ℝ) ≠ 0 :=
    (Real.sqrt_pos.2 hupos).ne'
  rw [angleAmplitude, sin_groverAngle marked hMarked,
    cos_groverAngle marked hMarked]
  have hmCancel :
      (Real.sqrt (marked.card : ℝ) / Real.sqrt (Fintype.card α)) /
          Real.sqrt marked.card =
        1 / Real.sqrt (Fintype.card α) := by
    field_simp
  have huCancel :
      (Real.sqrt (markedᶜ.card : ℝ) / Real.sqrt (Fintype.card α)) /
          Real.sqrt markedᶜ.card =
        1 / Real.sqrt (Fintype.card α) := by
    field_simp
  rw [hmCancel, huCancel]
  exact (uniformAmplitude_eq_symmetricAmplitude marked).symm

/-- Apply the Grover step `k` times. -/
noncomputable def groverIterate {α : Type*} [Fintype α] [DecidableEq α]
    (marked : Finset α) (k : ℕ) (ψ : Amplitude α) : Amplitude α :=
  (groverStep marked)^[k] ψ

/-- Every finite sequence of Grover steps preserves squared norm. -/
@[simp]
theorem amplitudeNormSq_groverIterate {α : Type*} [Fintype α]
    [DecidableEq α] [Nonempty α] (marked : Finset α) (k : ℕ)
    (ψ : Amplitude α) :
    amplitudeNormSq (groverIterate marked k ψ) = amplitudeNormSq ψ := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [groverIterate, Function.iterate_succ_apply', amplitudeNormSq_groverStep]
      simpa [groverIterate] using ih

/-- Grover iteration preserves normalization of the uniform initial state. -/
@[simp]
theorem amplitudeNormSq_groverIterate_uniform {α : Type*} [Fintype α]
    [DecidableEq α] [Nonempty α] (marked : Finset α) (k : ℕ) :
    amplitudeNormSq (groverIterate marked k (uniformAmplitude α)) = 1 := by
  rw [amplitudeNormSq_groverIterate, amplitudeNormSq_uniformAmplitude]

/-- Phase reached from the uniform initial state after `k` iterations. -/
noncomputable def groverPhase {α : Type*} [Fintype α]
    (marked : Finset α) (k : ℕ) : ℝ :=
  (2 * (k : ℝ) + 1) * groverAngle marked

theorem groverIterate_uniform_eq_angleAmplitude {α : Type*} [Fintype α]
    [DecidableEq α] (marked : Finset α) (hMarked : marked.Nonempty)
    (hUnmarked : markedᶜ.Nonempty) (k : ℕ) :
    groverIterate marked k (uniformAmplitude α) =
      angleAmplitude marked (groverPhase marked k) := by
  induction k with
  | zero =>
      simpa [groverIterate, groverPhase] using
        (angleAmplitude_groverAngle_eq_uniform marked hMarked hUnmarked).symm
  | succ k ih =>
      rw [groverIterate, Function.iterate_succ_apply']
      change groverStep marked (groverIterate marked k (uniformAmplitude α)) = _
      rw [ih, groverStep_angleAmplitude marked hMarked hUnmarked]
      congr 1
      simp [groverPhase, Nat.cast_succ]
      ring

theorem markedProbability_angleAmplitude {α : Type*} [Fintype α]
    [DecidableEq α] (marked : Finset α) (hMarked : marked.Nonempty)
    (φ : ℝ) :
    markedProbability marked (angleAmplitude marked φ) = (Real.sin φ) ^ 2 := by
  have hmpos : 0 < (marked.card : ℝ) := by
    exact_mod_cast (Finset.card_pos.mpr hMarked)
  have hsm0 : Real.sqrt (marked.card : ℝ) ≠ 0 :=
    (Real.sqrt_pos.2 hmpos).ne'
  rw [angleAmplitude, markedProbability_symmetricAmplitude, div_pow,
    Real.sq_sqrt hmpos.le]
  field_simp

/-- Exact success probability of standard Grover search after `k` iterations. -/
theorem markedProbability_groverIterate_uniform {α : Type*} [Fintype α]
    [DecidableEq α] (marked : Finset α) (hMarked : marked.Nonempty)
    (hUnmarked : markedᶜ.Nonempty) (k : ℕ) :
    markedProbability marked (groverIterate marked k (uniformAmplitude α)) =
      (Real.sin (groverPhase marked k)) ^ 2 := by
  rw [groverIterate_uniform_eq_angleAmplitude marked hMarked hUnmarked,
    markedProbability_angleAmplitude marked hMarked]

end Cslib.Grover

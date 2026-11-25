/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.MeasureTheory.Measure.UnitIntervalMomentRepresentation

/-! # Tests for Pitman's representation of consistent rates -/

open MeasureTheory unitInterval
open MathlibExt.Biology.PopulationGenetics.Coalescent.LambdaCoalescentWanted

/-- A zero rate array gives a representing measure of total mass zero. -/
example : ∃ (μ : Measure I) (_ : IsFiniteMeasure μ), μ.real Set.univ = 0 := by
  obtain ⟨μ, hμ, h⟩ := exists_measure_of_consistent (fun _ _ => 0)
    (by intros; rfl) (by intros; simp)
  exact ⟨μ, hμ, by simpa [unitIntervalMoment] using (h 2 2 le_rfl le_rfl).symm⟩

/-- At two blocks both endpoint atoms contribute. Higher moments distinguish the two atoms. -/
example : ∃ (μ : Measure I) (_ : IsFiniteMeasure μ), μ.real Set.univ = 5 ∧
    unitIntervalMoment μ 0 3 = 2 ∧ unitIntervalMoment μ 3 0 = 3 ∧
    unitIntervalMoment μ 1 1 = 0 := by
  let r (b k : ℕ) : ℝ := (if k = 2 then 2 else 0) + (if k = b then 3 else 0)
  have hn (b k : ℕ) : 0 ≤ r b k := by dsimp [r]; positivity
  have hc (b k : ℕ) (hk : 2 ≤ k) (hkb : k ≤ b) : r b k = r (b + 1) k + r (b + 1) (k + 1) := by
    simp [r, show k ≠ b + 1 by omega, show k + 1 ≠ 2 by omega]
  obtain ⟨μ, hμ, h⟩ := exists_measure_of_consistent r (fun b k _ _ => hn b k) hc
  have hmass := (h 2 2 le_rfl le_rfl).symm
  norm_num [r, unitIntervalMoment] at hmass
  exact ⟨μ, hμ, hmass,
    by simpa [r] using (h 5 2 (by decide) (by decide)).symm,
    by simpa [r] using (h 5 5 (by decide) le_rfl).symm,
    by simpa [r] using (h 4 3 (by decide) (by decide)).symm⟩

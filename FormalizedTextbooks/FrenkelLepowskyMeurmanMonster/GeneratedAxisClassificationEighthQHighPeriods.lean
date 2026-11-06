/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationEighthTensorHighData

/-! The literal twenty-four original spin addresses have only zero and omega translation periods.
Their equality with the actual high tensor support is a separate obligation. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Both original spin addresses belonging to each of the twelve literal odd codes. -/
def generatedEighthHighSpinMask (j : Fin 24) : Fin 4096 :=
  if h : j.val < 12 then
    Fin.castAdd 2048 (generatedEighthHighOddCode ⟨j.val, h⟩)
  else Fin.natAdd 2048 (generatedEighthHighOddCode ⟨j.val - 12, by omega⟩)

/-- The same addresses in the genuine original spin module. -/
def generatedEighthHighSpinIndex (j : Fin 24) : SpinIndex :=
  golayLabelCoefficients (generatedEighthHighSpinMask j)

/-- The exact finite set of those original spin addresses. -/
def generatedEighthHighSpinSet : Set SpinIndex := Set.range generatedEighthHighSpinIndex

/-- A literal counterexample address for each forbidden candidate translation. -/
def generatedEighthHighPeriodWitness : Fin 24 → Fin 24 :=
  ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

/-- The zero original spin coordinate belongs to the literal address set. -/
theorem generatedEighth_high_spin_zero_mem : (0 : SpinIndex) ∈ generatedEighthHighSpinSet := by
  refine ⟨8, ?_⟩
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Check all candidate periods against twenty-four original decoded vectors and literal witnesses.
/-- Every candidate is zero, omega, or has an explicitly checked escaping translation. -/
theorem generatedEighth_high_period_certificate : ∀ j : Fin 24,
    generatedEighthHighSpinIndex j = 0 ∨
    generatedEighthHighSpinIndex j = Pi.single (11 : Fin 12) 1 ∨
    ∀ l : Fin 24,
      generatedEighthHighSpinIndex (generatedEighthHighPeriodWitness j) +
        generatedEighthHighSpinIndex j ≠ generatedEighthHighSpinIndex l := by
  decide +kernel

/-- Every actual translation preserving this literal set is zero or the original omega direction. -/
theorem generatedEighth_high_spin_period (a : SpinIndex)
    (h : ∀ t ∈ generatedEighthHighSpinSet, t + a ∈ generatedEighthHighSpinSet) :
    a = 0 ∨ a = Pi.single (11 : Fin 12) 1 := by
  have ha : a ∈ generatedEighthHighSpinSet := by
    simpa only [zero_add] using h 0 generatedEighth_high_spin_zero_mem
  obtain ⟨j, hj⟩ := ha
  rcases generatedEighth_high_period_certificate j with hz | ho | he
  · exact Or.inl (hj.symm.trans hz)
  · exact Or.inr (hj.symm.trans ho)
  · obtain ⟨l, hl⟩ := h (generatedEighthHighSpinIndex (generatedEighthHighPeriodWitness j))
      ⟨generatedEighthHighPeriodWitness j, rfl⟩
    exfalso
    apply he l
    rw [hj]
    exact hl.symm

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

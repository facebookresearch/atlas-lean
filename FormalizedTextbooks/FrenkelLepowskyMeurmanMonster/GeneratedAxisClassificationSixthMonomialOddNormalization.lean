/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthMonomialOddData

/-! Normalization by the all-one code is an exact binary-coordinate identity. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix
set_option backward.isDefEq.respectTransparency false

/-- The low eleven-bit code representative as a full twelve-bit label. -/
def generatedSixthMonomialLowCode (n : Fin 4096) : Fin 4096 := ⟨n.val % 2048, by omega⟩

/-- The discarded all-one coordinate is retained exactly in binary code coordinates. -/
theorem generatedSixth_monomial_low_code (n : Fin 4096) :
    golayLabelCoefficients (generatedSixthMonomialLowCode n) +
      (if n.val.testBit 11 then Pi.single 11 1 else 0) = golayLabelCoefficients n := by
  ext a
  have hm : (n.val % 2048).testBit a.val =
      (decide (a.val < 11) && n.val.testBit a.val) := by
    simpa only [show (2 ^ 11 : ℕ) = 2048 by decide] using
      Nat.testBit_mod_two_pow n.val 11 a.val
  by_cases ha : a = 11
  · subst a
    have hz : (n.val % 2048).testBit 11 = false := by
      simpa using Nat.testBit_mod_two_pow n.val 11 11
    cases h : n.val.testBit 11 <;>
      simp [golayLabelCoefficients, generatedSixthMonomialLowCode, hz, h]
  · have hav : a.val < 11 := by
      have hne : a.val ≠ 11 := fun h => ha (Fin.ext h)
      omega
    have hs : (if n.val.testBit 11 then (Pi.single 11 1 : SpinIndex) else 0) a = 0 := by
      split <;> simp_all
    simp only [golayLabelCoefficients, generatedSixthMonomialLowCode, Pi.add_apply,
      hm, hav, decide_true, Bool.true_and, hs, add_zero]

/-- The computational source label is exactly the complete original matrix-vector transform. -/
theorem generatedSixth_monomial_odd_full_source (k : Fin 4) (f : Fin 512) :
    golayLabelCoefficients (generatedSixthMonomialOddFullSourceCode k f) =
      (representativeMatrix (generatedSixthMonomialMaskCoordinateRows k)) *ᵥ
        golayLabelCoefficients ⟨(generatedSixthMonomialOddCode f).val, by omega⟩ := by
  rw [generatedSixthMonomialOddFullSourceCode, generatedSixth_monomial_mask_label]
  rfl

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

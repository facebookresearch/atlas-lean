/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinShortActions
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinQMaskGeneric
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinShortPackedMetadata
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsMaskCertificate

/-! Exact full extraspecial action by finite bit masks. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000

/-- Genuine compact fibers preserve the original extraspecial square form. -/
theorem generatedNinth_lower_spin_short_packed_square (i : Fin 11) (v : Fin 24 → ZMod 2) :
    squareQuad (qBinaryAction (spinConjugation (generatedNinthLowerSpinCompact i)) v) =
      squareQuad v := by
  change squareQuad (spinBinaryAction (generatedNinthLowerSpinCompact i) v) = _
  rw [generatedNinth_lower_spin_compact_compatibility]
  exact leechBinaryAction_squareQuad _ v

/-- Certified polynomial masks are the complete genuine compact source Q action. -/
theorem generatedNinth_lower_spin_short_packed_actual (i : Fin 11) (v : ℕ) :
    spinConjugation (generatedNinthLowerSpinCompact i) (generatedAxisGlobalQMask v) =
      generatedAxisGlobalQMaskImage (generatedNinthLowerSpinShortPackedColumns i)
        (generatedNinthLowerSpinShortPackedRows i)
        (generatedNinthLowerSpinShortPackedCoefficients i) v := by
  have hm := generatedNinth_lower_spin_short_packed_metadata i
  exact generatedNinth_lower_spin_q_mask_from_units _
    (generatedNinth_lower_spin_short_packed_square i)
    (generatedNinthLowerSpinShortPackedImages i) _ _ _
    (generatedNinth_lower_spin_compact_generator i) hm.1 hm.2.1 hm.2.2 v

/-- Packed vector and full central identities certify the unchanged original preferred-Q
transport and signed coefficient condition. -/
theorem generatedNinth_lower_spin_short_condition_of_packed (i : Fin 11) (a : Fin 98280)
    (h : generatedNinthLowerSpinShortPackedCondition i a) :
    generatedNinthLowerSpinShortCondition i a := by
  dsimp only [generatedNinthLowerSpinShortPackedCondition] at h
  refine ⟨?_, h.2.2⟩
  rw [← generatedNinth_lower_spin_short_q_fast_actual,
    generatedNinth_lower_spin_short_packed_actual]
  exact generatedAxisGlobalQMaskImage_certificate _ _ _ _ _ _ h.1 h.2.1

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

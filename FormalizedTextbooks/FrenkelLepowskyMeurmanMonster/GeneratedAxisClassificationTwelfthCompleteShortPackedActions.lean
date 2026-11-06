/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthCompleteShortActions
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthCompleteShortPackedMetadata
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinQMaskGeneric
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsMaskCertificate

/-! Complete actual preferred short action from finite mask and central phase identities. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

/-- Every genuine candidate preserves the complete original extraspecial square form. -/
theorem generatedTwelfth_complete_short_packed_square (g : Fin 12) (v : Fin 24 → ZMod 2) :
    squareQuad (qBinaryAction (spinConjugation (generatedTwelfthSpinCompact g)) v) =
      squareQuad v := by
  change squareQuad (spinBinaryAction (generatedTwelfthSpinCompact g) v) = _
  rw [generatedTwelfth_certified_spatial_compatibility]
  exact leechBinaryAction_squareQuad _ v

/-- Exact decoded vector and central metadata evaluate the entire actual candidate Q action. -/
theorem generatedTwelfth_complete_short_packed_actual (g : Fin 12) (v : ℕ) :
    spinConjugation (generatedTwelfthSpinCompact g) (generatedAxisGlobalQMask v) =
      generatedAxisGlobalQMaskImage (generatedTwelfthSpinCompactBinaryColumns g)
        (generatedTwelfthCompleteShortPackedRows g)
        (generatedTwelfthCompleteShortPackedCoefficients g) v := by
  have hm := generatedTwelfth_complete_short_packed_metadata g
  exact generatedNinth_lower_spin_q_mask_from_units _
    (generatedTwelfth_complete_short_packed_square g)
    (generatedTwelfthSpinCompactFullQCache g) _ _ _
    (generatedTwelfth_spin_compact_full_Q_generator g) hm.1 hm.2.1 hm.2.2 v

/-- Complete finite mask and central phase identities prove actual unchanged preferred-Q
transport and the entire signed coefficient condition. -/
theorem generatedTwelfth_complete_short_condition_of_packed (g : Fin 12) (a : Fin 98280)
    (h : generatedTwelfthCompleteShortPackedCondition g a) :
    generatedTwelfthCompleteShortCondition g a := by
  dsimp only [generatedTwelfthCompleteShortPackedCondition] at h
  refine ⟨?_, h.2.2⟩
  rw [← generatedTwelfth_spin_compact_full_Q_fast,
    generatedTwelfth_complete_short_packed_actual]
  exact generatedAxisGlobalQMaskImage_certificate _ _ _ _ _ _ h.1 h.2.1

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

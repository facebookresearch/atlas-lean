/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationEighthQSpinOrbit

/-! The genuine odd-parity modulation cuts out exactly the original rank-eleven support. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix BigOperators
set_option backward.isDefEq.respectTransparency false

/-- The actual fixing modulation, retaining its full twelve-bit label. -/
def generatedEighthSpinSupportModulation (_ : Fin 1) : Fin 4096 := 3079

/-- The original single Pauli equation on twelve genuine spin coordinates. -/
def generatedEighthSpinSupportMatrix : Matrix (Fin 1) (Fin 12) (ZMod 2) :=
  fun j i => golayLabelCoefficients (generatedEighthSpinSupportModulation j) i

/-- The original omega direction complements the eleven translation columns. -/
def generatedEighthSpinSupportComplement : Matrix (Fin 12) (Fin 1) (ZMod 2) :=
  fun i _ => if i = 11 then 1 else 0

/-- The one literal modulation is a genuine fixing Pauli operator. -/
theorem generatedEighth_spin_support_modulation_fixed (j : Fin 1) :
    spinRepresentation (cocodeQ (golayLabelCoefficients
      (generatedEighthSpinSupportModulation j))) generatedEighthSpinState =
        generatedEighthSpinState :=
  generatedEighth_spin_state_odd_modulation_fixed

set_option maxHeartbeats 2000000 in
-- Check all 144 entries of the original rank-eleven projection plus its omega complement.
/-- The literal original translation projection and support complement sum to the identity. -/
theorem generatedEighth_spin_support_projection_certificate :
    generatedEighthSpinPauliTranslationMatrix * generatedEighthSpinPauliLeftInverse +
      generatedEighthSpinSupportComplement * generatedEighthSpinSupportMatrix = 1 := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

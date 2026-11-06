/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinDirectCompactBinaryData00
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinDirectCompactBinaryData01
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinDirectCompactBinaryData02
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinDirectCompactBinaryData03
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinDirectCompactBinaryData04
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinDirectCompactBinaryData05
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinDirectCompactBinaryData06
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinDirectCompactBinaryData07
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinDirectCompactBinaryData08
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinDirectCompactBinaryData09
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinDirectCompactBinaryData10
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinDirectIntegralBinaryData

/-! Genuine compact spin products agree with all complete integral lattice binary actions. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
open scoped Matrix
set_option backward.isDefEq.respectTransparency false

/-- Every compact corrected generator has the complete certified original lattice binary column. -/
theorem generatedNinth_lower_spin_direct_compact_binary_certificate (i : Fin 11) :
    ∀ j : Fin 24,
      toAdd (qQuotHom (generatedNinthLowerSpinCorrection i *
        generatedNinthLowerSpinQImage i j * (generatedNinthLowerSpinCorrection i)⁻¹)) =
      (leechHyperbolicInverse *
        (generatedNinthLowerSpinDirectIntegralMatrix i).map (Int.castRingHom (ZMod 2)) *
          leechHyperbolicMatrix) *ᵥ Pi.single j 1 := by
  fin_cases i
  · exact generatedNinth_lower_spin_direct_compact_binary_certificate_00
  · exact generatedNinth_lower_spin_direct_compact_binary_certificate_01
  · exact generatedNinth_lower_spin_direct_compact_binary_certificate_02
  · exact generatedNinth_lower_spin_direct_compact_binary_certificate_03
  · exact generatedNinth_lower_spin_direct_compact_binary_certificate_04
  · exact generatedNinth_lower_spin_direct_compact_binary_certificate_05
  · exact generatedNinth_lower_spin_direct_compact_binary_certificate_06
  · exact generatedNinth_lower_spin_direct_compact_binary_certificate_07
  · exact generatedNinth_lower_spin_direct_compact_binary_certificate_08
  · exact generatedNinth_lower_spin_direct_compact_binary_certificate_09
  · exact generatedNinth_lower_spin_direct_compact_binary_certificate_10

/-- The actual compact spin binary action retains every original coordinate
of the certified matrix. -/
theorem generatedNinth_lower_spin_direct_compact_binary_generator (i : Fin 11) (j : Fin 24) :
    spinBinaryAction (generatedNinthLowerSpinCompact i) (Pi.single j 1) =
      (leechHyperbolicInverse *
        (generatedNinthLowerSpinDirectIntegralMatrix i).map (Int.castRingHom (ZMod 2)) *
          leechHyperbolicMatrix) *ᵥ Pi.single j 1 := by
  change qBinaryAction (spinConjugation (generatedNinthLowerSpinCompact i))
    (toAdd (qQuotHom (qCoordinateGenerator j))) = _
  rw [qBinaryAction_apply, generatedNinth_lower_spin_compact_generator,
    generatedNinth_lower_spin_direct_compact_binary_certificate]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTenthLink
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthCCLocalOrbit

/-! The two genuine Tenth whole-axis fixers are proved, so the Tenth coverage reduction and the
root-word binding keep only their triality-image inputs. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Both genuine Tenth fibers fix the whole canonical compact source axis. -/
theorem generatedAxisGlobalTwelveTenthFixers_closed : GeneratedAxisGlobalTwelveTenthFixers :=
  generatedTenth_actual_two_fixers

/-- Tenth family coverage from the triality images at the 64 non-identity root words alone. -/
theorem generatedAxisGlobalTwelve_tenth_covered_closed
    (hpositive : ∀ k : Fin 65, k ≠ 0 →
      sExtra (rhoLocal (generatedAxisGlobalTwelveTenthRootWord k)
        (generatedAxisGlobalTwelveRepresentative 11)) ∈
        generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative)
    (hnegative : ∀ k : Fin 65, k ≠ 0 →
      sExtra⁻¹ (rhoLocal (generatedAxisGlobalTwelveTenthRootWord k)
        (generatedAxisGlobalTwelveRepresentative 11)) ∈
        generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative) :
    GeneratedAxisGlobalTwelveFamilyCovered 11 :=
  generatedAxisGlobalTwelve_tenth_covered_of generatedAxisGlobalTwelveTenthFixers_closed
    hpositive hnegative

/-- Known triality images at a Tenth coset bind the root word whose binary root a gated letter
word carries to the binary root of that coset, with no fixer premise. -/
theorem generatedAxisGlobalTwelveTenth_root_pair_of_word_closed (k : Fin 65) (h : H)
    (w : List (Fin 6))
    (hw : monsterCo1GeometryBinaryMaskDecode (n := 24)
      (generatedTenthAxisLowerRecoveryThreeProjectionMaskWord w
        (generatedAxisGlobalTwelveTenthRootMask k)) = (generatedAxisGlobalBinaryRoot h).val)
    (hpos : sExtra (rhoLocal h (generatedAxisGlobalTwelveRepresentative 11)) ∈
      generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative)
    (hneg : sExtra⁻¹ (rhoLocal h (generatedAxisGlobalTwelveRepresentative 11)) ∈
      generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative) :
    sExtra (rhoLocal (generatedAxisGlobalTwelveTenthRootWord k)
        (generatedAxisGlobalTwelveRepresentative 11)) ∈
        generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative ∧
      sExtra⁻¹ (rhoLocal (generatedAxisGlobalTwelveTenthRootWord k)
        (generatedAxisGlobalTwelveRepresentative 11)) ∈
        generatedLocalOrbitUnion generatedAxisGlobalTwelveRepresentative :=
  generatedAxisGlobalTwelveTenth_root_pair_of_word generatedAxisGlobalTwelveTenthFixers_closed
    k h w hw hpos hneg

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

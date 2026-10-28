/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveEighthBindRoots

/-! Alternative Eighth bindings through partner cosets.

Eighth root 22 has both triality images in the Ninth class. The Ninth transports N5+ and N5- of
gninth (`/tmp/flm-cc-gninth-transporters.json`) at one Ninth coset `x` bind it at their Eighth
coset, so no Eighth-side identification is needed for this root. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-- The odd source word of the Eighth coset of the Ninth transport N5+. -/
def generatedAxisGlobalTwelveEighthBindNinthWord22 : List (Fin 10) := [0, 0, 7, 0, 0, 9, 6, 0]

/-- The extraspecial, sign and permutation prefix of the Eighth coset of N5+. -/
def generatedAxisGlobalTwelveEighthBindNinthPre22 : List IdentLetter :=
  [IdentLetter.qel (qCentral 1 * generatedAxisGlobalQMask 3200698), IdentLetter.sign 317 0,
    IdentLetter.mono (0, true), IdentLetter.mono (0, true), IdentLetter.mono (0, true),
    IdentLetter.mono (1, false), IdentLetter.mono (0, true), IdentLetter.mono (0, true),
    IdentLetter.mono (0, true), IdentLetter.mono (1, false), IdentLetter.mono (0, true),
    IdentLetter.mono (0, true), IdentLetter.mono (1, false), IdentLetter.mono (0, false),
    IdentLetter.mono (0, false), IdentLetter.mono (0, false), IdentLetter.mono (1, false),
    IdentLetter.mono (0, true), IdentLetter.mono (1, false), IdentLetter.mono (0, true),
    IdentLetter.mono (1, false), IdentLetter.mono (0, false), IdentLetter.mono (1, false),
    IdentLetter.mono (0, true), IdentLetter.mono (0, true), IdentLetter.mono (1, false),
    IdentLetter.mono (0, false), IdentLetter.mono (1, false), IdentLetter.mono (0, true),
    IdentLetter.mono (1, false), IdentLetter.mono (0, true), IdentLetter.mono (0, true)]

/-- The Eighth coset of the Ninth transport N5+. -/
def generatedAxisGlobalTwelveEighthBindNinthCoset22 : H :=
  eighthBindRep generatedAxisGlobalTwelveEighthBindNinthPre22
    generatedAxisGlobalTwelveEighthBindNinthWord22

/-- Eighth root 22 from the two Ninth transports N5+ and N5- (gninth) at one Ninth coset `x`. -/
theorem generatedAxisGlobalTwelveEighthBind_root22_ninth (x : H)
    (htr : sExtra (rhoLocal x (generatedAxisGlobalTwelveRepresentative 8)) =
      rhoLocal generatedAxisGlobalTwelveEighthBindNinthCoset22 generatedEighthAxis)
    (hother : ∃ i : Fin 12, ∃ g : H,
      sExtra⁻¹ (rhoLocal x (generatedAxisGlobalTwelveRepresentative 8)) =
        rhoLocal g (generatedAxisGlobalTwelveRepresentative i)) :
    GeneratedAxisGlobalTwelveEighthRootBound 22 := by
  obtain ⟨i, g, hg⟩ := hother
  exact eighthBind_rootBound_of_forward 22 generatedAxisGlobalTwelveEighthBindNinthPre22 (by decide)
    generatedAxisGlobalTwelveEighthBindNinthWord22 (by decide) [13, 13, 14, 12, 5, 12]
    (by decide +kernel) 8 x htr (generatedAxisGlobalTwelve_mem_of_transport i g hg)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

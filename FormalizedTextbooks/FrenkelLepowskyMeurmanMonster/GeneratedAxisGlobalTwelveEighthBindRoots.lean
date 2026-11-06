/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveEighthBindFrame

/-! Binding wrappers for the thirty-six non-Ω Eighth forest roots.

Every root has an explicit representative coset in the shared identification alphabet. Each
wrapper turns the whole-vector identifications at that coset (or the partner transports into it)
into `GeneratedAxisGlobalTwelveEighthRootBound`; the binary root matching is fully checked here.
The identifications themselves are hypotheses: numeric transports for all of them are listed in
`/tmp/flm-cc-goctad-transporters.json` and in the Tenth records of gtenth. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-- The odd source word of the representative coset of Eighth root 1. -/
def generatedAxisGlobalTwelveEighthBindWord1 : List (Fin 10) := [0, 7, 0, 8]

/-- The representative coset of Eighth root 1. -/
def generatedAxisGlobalTwelveEighthBindCoset1 : H :=
  eighthBindRep []
    generatedAxisGlobalTwelveEighthBindWord1

/-- The odd source word of the representative coset of Eighth root 2. -/
def generatedAxisGlobalTwelveEighthBindWord2 : List (Fin 10) := [0, 6, 0]

/-- The representative coset of Eighth root 2. -/
def generatedAxisGlobalTwelveEighthBindCoset2 : H :=
  eighthBindRep []
    generatedAxisGlobalTwelveEighthBindWord2

/-- The odd source word of the representative coset of Eighth root 3. -/
def generatedAxisGlobalTwelveEighthBindWord3 : List (Fin 10) := [0, 8, 0, 7, 7]

/-- The representative coset of Eighth root 3. -/
def generatedAxisGlobalTwelveEighthBindCoset3 : H :=
  eighthBindRep []
    generatedAxisGlobalTwelveEighthBindWord3

/-- The odd source word of the representative coset of Eighth root 4. -/
def generatedAxisGlobalTwelveEighthBindWord4 : List (Fin 10) := [0, 0, 7, 9, 0, 0, 7, 9, 0]

/-- The extraspecial, sign and permutation prefix of the coset of Eighth root 4. -/
def generatedAxisGlobalTwelveEighthBindPre4 : List IdentLetter :=
  [IdentLetter.qel (qCentral 0 * generatedAxisGlobalQMask 9152780), IdentLetter.sign 1286 0,
    IdentLetter.mono (0, true), IdentLetter.mono (0, true), IdentLetter.mono (1, false),
    IdentLetter.mono (0, true), IdentLetter.mono (1, false), IdentLetter.mono (0, true),
    IdentLetter.mono (1, false), IdentLetter.mono (0, false), IdentLetter.mono (1, false),
    IdentLetter.mono (0, true), IdentLetter.mono (1, false), IdentLetter.mono (0, true),
    IdentLetter.mono (0, true), IdentLetter.mono (0, true), IdentLetter.mono (1, false),
    IdentLetter.mono (0, false), IdentLetter.mono (0, false), IdentLetter.mono (0, false),
    IdentLetter.mono (1, false), IdentLetter.mono (0, true), IdentLetter.mono (0, true),
    IdentLetter.mono (0, true), IdentLetter.mono (1, true), IdentLetter.mono (0, false),
    IdentLetter.mono (0, false), IdentLetter.mono (1, true), IdentLetter.mono (0, false),
    IdentLetter.mono (0, false), IdentLetter.mono (0, false), IdentLetter.mono (1, true),
    IdentLetter.mono (0, true), IdentLetter.mono (1, true), IdentLetter.mono (0, false),
    IdentLetter.mono (0, false), IdentLetter.mono (1, true), IdentLetter.mono (0, true),
    IdentLetter.mono (1, true), IdentLetter.mono (0, false), IdentLetter.mono (1, true),
    IdentLetter.mono (0, false), IdentLetter.mono (0, false), IdentLetter.mono (1, true),
    IdentLetter.mono (0, true), IdentLetter.mono (0, true), IdentLetter.mono (0, true),
    IdentLetter.mono (1, false), IdentLetter.mono (0, false), IdentLetter.mono (1, false),
    IdentLetter.mono (0, false), IdentLetter.mono (0, false), IdentLetter.mono (0, false),
    IdentLetter.mono (1, false), IdentLetter.mono (0, false), IdentLetter.mono (0, false),
    IdentLetter.mono (1, false), IdentLetter.mono (0, false), IdentLetter.mono (0, false),
    IdentLetter.mono (1, false), IdentLetter.mono (0, false), IdentLetter.mono (0, false),
    IdentLetter.mono (1, false), IdentLetter.mono (0, false), IdentLetter.mono (1, false),
    IdentLetter.mono (0, true), IdentLetter.mono (0, true), IdentLetter.mono (1, false),
    IdentLetter.mono (0, true), IdentLetter.mono (1, false)]

/-- The representative coset of Eighth root 4. -/
def generatedAxisGlobalTwelveEighthBindCoset4 : H :=
  eighthBindRep generatedAxisGlobalTwelveEighthBindPre4
    generatedAxisGlobalTwelveEighthBindWord4

/-- The odd source word of the representative coset of Eighth root 5. -/
def generatedAxisGlobalTwelveEighthBindWord5 : List (Fin 10) := [0, 8, 6, 0, 6]

/-- The representative coset of Eighth root 5. -/
def generatedAxisGlobalTwelveEighthBindCoset5 : H :=
  eighthBindRep []
    generatedAxisGlobalTwelveEighthBindWord5

/-- The odd source word of the representative coset of Eighth root 6. -/
def generatedAxisGlobalTwelveEighthBindWord6 : List (Fin 10) := [0, 8, 6, 0]

/-- The representative coset of Eighth root 6. -/
def generatedAxisGlobalTwelveEighthBindCoset6 : H :=
  eighthBindRep []
    generatedAxisGlobalTwelveEighthBindWord6

/-- The odd source word of the representative coset of Eighth root 7. -/
def generatedAxisGlobalTwelveEighthBindWord7 : List (Fin 10) := [0, 0, 9, 6, 0, 0, 6, 9, 0, 0]

/-- The extraspecial, sign and permutation prefix of the coset of Eighth root 7. -/
def generatedAxisGlobalTwelveEighthBindPre7 : List IdentLetter :=
  [IdentLetter.qel (qCentral 1 * generatedAxisGlobalQMask 6837538), IdentLetter.sign 1573 0,
    IdentLetter.mono (1, false), IdentLetter.mono (0, false), IdentLetter.mono (1, false),
    IdentLetter.mono (0, false), IdentLetter.mono (0, false), IdentLetter.mono (0, false),
    IdentLetter.mono (1, false), IdentLetter.mono (0, false), IdentLetter.mono (1, false),
    IdentLetter.mono (0, true), IdentLetter.mono (1, false), IdentLetter.mono (0, true),
    IdentLetter.mono (1, false), IdentLetter.mono (0, false), IdentLetter.mono (0, false),
    IdentLetter.mono (1, false), IdentLetter.mono (0, false), IdentLetter.mono (0, false),
    IdentLetter.mono (0, false), IdentLetter.mono (1, false), IdentLetter.mono (0, true),
    IdentLetter.mono (0, true), IdentLetter.mono (0, true), IdentLetter.mono (1, true),
    IdentLetter.mono (0, true), IdentLetter.mono (1, true), IdentLetter.mono (0, true),
    IdentLetter.mono (1, true), IdentLetter.mono (0, false), IdentLetter.mono (1, true),
    IdentLetter.mono (0, true), IdentLetter.mono (0, true), IdentLetter.mono (1, true),
    IdentLetter.mono (0, true), IdentLetter.mono (1, true), IdentLetter.mono (0, false),
    IdentLetter.mono (0, false), IdentLetter.mono (1, true), IdentLetter.mono (0, false),
    IdentLetter.mono (1, true), IdentLetter.mono (0, true), IdentLetter.mono (0, true),
    IdentLetter.mono (0, true), IdentLetter.mono (1, true), IdentLetter.mono (0, true),
    IdentLetter.mono (1, true), IdentLetter.mono (0, true), IdentLetter.mono (1, false),
    IdentLetter.mono (0, true), IdentLetter.mono (0, true), IdentLetter.mono (1, false),
    IdentLetter.mono (0, false), IdentLetter.mono (0, false), IdentLetter.mono (1, false),
    IdentLetter.mono (0, true), IdentLetter.mono (1, false), IdentLetter.mono (0, false),
    IdentLetter.mono (0, false), IdentLetter.mono (1, false), IdentLetter.mono (0, false),
    IdentLetter.mono (0, false), IdentLetter.mono (0, false), IdentLetter.mono (1, false),
    IdentLetter.mono (0, true), IdentLetter.mono (0, true), IdentLetter.mono (1, false)]

/-- The representative coset of Eighth root 7. -/
def generatedAxisGlobalTwelveEighthBindCoset7 : H :=
  eighthBindRep generatedAxisGlobalTwelveEighthBindPre7
    generatedAxisGlobalTwelveEighthBindWord7

/-- The odd source word of the representative coset of Eighth root 8. -/
def generatedAxisGlobalTwelveEighthBindWord8 : List (Fin 10) := [0, 0, 7, 9, 0, 7, 0, 0]

/-- The extraspecial, sign and permutation prefix of the coset of Eighth root 8. -/
def generatedAxisGlobalTwelveEighthBindPre8 : List IdentLetter :=
  [IdentLetter.qel (qCentral 1 * generatedAxisGlobalQMask 2601256), IdentLetter.sign 1579 0,
    IdentLetter.mono (0, false), IdentLetter.mono (0, false), IdentLetter.mono (1, false),
    IdentLetter.mono (0, true), IdentLetter.mono (1, false), IdentLetter.mono (0, true),
    IdentLetter.mono (0, true), IdentLetter.mono (0, true), IdentLetter.mono (1, false),
    IdentLetter.mono (0, false), IdentLetter.mono (0, false), IdentLetter.mono (1, false),
    IdentLetter.mono (0, false), IdentLetter.mono (1, false), IdentLetter.mono (0, false),
    IdentLetter.mono (0, false), IdentLetter.mono (1, false), IdentLetter.mono (0, false),
    IdentLetter.mono (1, false), IdentLetter.mono (0, false), IdentLetter.mono (0, false),
    IdentLetter.mono (1, false), IdentLetter.mono (0, true), IdentLetter.mono (0, true),
    IdentLetter.mono (0, true), IdentLetter.mono (1, false), IdentLetter.mono (0, false),
    IdentLetter.mono (0, false), IdentLetter.mono (0, false), IdentLetter.mono (1, true),
    IdentLetter.mono (0, false), IdentLetter.mono (1, true), IdentLetter.mono (0, false),
    IdentLetter.mono (0, false), IdentLetter.mono (1, true), IdentLetter.mono (0, true),
    IdentLetter.mono (0, true), IdentLetter.mono (1, true), IdentLetter.mono (0, true),
    IdentLetter.mono (0, true), IdentLetter.mono (1, true), IdentLetter.mono (0, false),
    IdentLetter.mono (1, true), IdentLetter.mono (0, true), IdentLetter.mono (0, true),
    IdentLetter.mono (1, true), IdentLetter.mono (0, false), IdentLetter.mono (0, false),
    IdentLetter.mono (1, true), IdentLetter.mono (0, true), IdentLetter.mono (1, false),
    IdentLetter.mono (0, false), IdentLetter.mono (1, false), IdentLetter.mono (0, true),
    IdentLetter.mono (1, false), IdentLetter.mono (0, true), IdentLetter.mono (0, true),
    IdentLetter.mono (1, false), IdentLetter.mono (0, true), IdentLetter.mono (0, true),
    IdentLetter.mono (1, false), IdentLetter.mono (0, false), IdentLetter.mono (1, false),
    IdentLetter.mono (0, true), IdentLetter.mono (1, false), IdentLetter.mono (0, false),
    IdentLetter.mono (0, false), IdentLetter.mono (0, false), IdentLetter.mono (1, false),
    IdentLetter.mono (0, false), IdentLetter.mono (0, false), IdentLetter.mono (1, false),
    IdentLetter.mono (0, true), IdentLetter.mono (1, false)]

/-- The representative coset of Eighth root 8. -/
def generatedAxisGlobalTwelveEighthBindCoset8 : H :=
  eighthBindRep generatedAxisGlobalTwelveEighthBindPre8
    generatedAxisGlobalTwelveEighthBindWord8

/-- The odd source word of the representative coset of Eighth root 9. -/
def generatedAxisGlobalTwelveEighthBindWord9 : List (Fin 10) := [0, 6, 8, 0, 6, 8]

/-- The representative coset of Eighth root 9. -/
def generatedAxisGlobalTwelveEighthBindCoset9 : H :=
  eighthBindRep []
    generatedAxisGlobalTwelveEighthBindWord9

/-- The odd source word of the representative coset of Eighth root 10. -/
def generatedAxisGlobalTwelveEighthBindWord10 : List (Fin 10) := [0, 0, 7, 9, 0, 0, 9]

/-- The extraspecial, sign and permutation prefix of the coset of Eighth root 10. -/
def generatedAxisGlobalTwelveEighthBindPre10 : List IdentLetter :=
  [IdentLetter.qel (qCentral 0 * generatedAxisGlobalQMask 16413671), IdentLetter.sign 11 0,
    IdentLetter.mono (0, true), IdentLetter.mono (1, false), IdentLetter.mono (0, true),
    IdentLetter.mono (0, true), IdentLetter.mono (1, false), IdentLetter.mono (0, true),
    IdentLetter.mono (1, false), IdentLetter.mono (0, false), IdentLetter.mono (0, false),
    IdentLetter.mono (1, false), IdentLetter.mono (0, true), IdentLetter.mono (1, false),
    IdentLetter.mono (0, false), IdentLetter.mono (1, false), IdentLetter.mono (0, true),
    IdentLetter.mono (0, true), IdentLetter.mono (0, true), IdentLetter.mono (1, false),
    IdentLetter.mono (0, false), IdentLetter.mono (0, false), IdentLetter.mono (0, false),
    IdentLetter.mono (1, false), IdentLetter.mono (0, false), IdentLetter.mono (1, false),
    IdentLetter.mono (0, false), IdentLetter.mono (0, false), IdentLetter.mono (0, false),
    IdentLetter.mono (1, true), IdentLetter.mono (0, true), IdentLetter.mono (0, true),
    IdentLetter.mono (1, true), IdentLetter.mono (0, true), IdentLetter.mono (1, true),
    IdentLetter.mono (0, true), IdentLetter.mono (0, true), IdentLetter.mono (1, true),
    IdentLetter.mono (0, true), IdentLetter.mono (0, true), IdentLetter.mono (1, true),
    IdentLetter.mono (0, false), IdentLetter.mono (0, false), IdentLetter.mono (1, true),
    IdentLetter.mono (0, false), IdentLetter.mono (0, false), IdentLetter.mono (0, false),
    IdentLetter.mono (1, true), IdentLetter.mono (0, false), IdentLetter.mono (0, false),
    IdentLetter.mono (1, false), IdentLetter.mono (0, true), IdentLetter.mono (1, false),
    IdentLetter.mono (0, false), IdentLetter.mono (0, false), IdentLetter.mono (1, false),
    IdentLetter.mono (0, false), IdentLetter.mono (1, false), IdentLetter.mono (0, false),
    IdentLetter.mono (0, false), IdentLetter.mono (0, false), IdentLetter.mono (1, false),
    IdentLetter.mono (0, true), IdentLetter.mono (1, false), IdentLetter.mono (0, false),
    IdentLetter.mono (1, false), IdentLetter.mono (0, false), IdentLetter.mono (1, false),
    IdentLetter.mono (0, true), IdentLetter.mono (1, false), IdentLetter.mono (0, true),
    IdentLetter.mono (0, true), IdentLetter.mono (0, true)]

/-- The representative coset of Eighth root 10. -/
def generatedAxisGlobalTwelveEighthBindCoset10 : H :=
  eighthBindRep generatedAxisGlobalTwelveEighthBindPre10
    generatedAxisGlobalTwelveEighthBindWord10

/-- The odd source word of the representative coset of Eighth root 11. -/
def generatedAxisGlobalTwelveEighthBindWord11 : List (Fin 10) := [0, 8, 7, 0, 7, 8, 0]

/-- The representative coset of Eighth root 11. -/
def generatedAxisGlobalTwelveEighthBindCoset11 : H :=
  eighthBindRep []
    generatedAxisGlobalTwelveEighthBindWord11

/-- The odd source word of the representative coset of Eighth root 12. -/
def generatedAxisGlobalTwelveEighthBindWord12 : List (Fin 10) := [0, 6, 6, 8, 7, 0]

/-- The representative coset of Eighth root 12. -/
def generatedAxisGlobalTwelveEighthBindCoset12 : H :=
  eighthBindRep []
    generatedAxisGlobalTwelveEighthBindWord12

/-- The odd source word of the representative coset of Eighth root 13. -/
def generatedAxisGlobalTwelveEighthBindWord13 : List (Fin 10) := [0, 8, 7, 0]

/-- The representative coset of Eighth root 13. -/
def generatedAxisGlobalTwelveEighthBindCoset13 : H :=
  eighthBindRep []
    generatedAxisGlobalTwelveEighthBindWord13

/-- The odd source word of the representative coset of Eighth root 14. -/
def generatedAxisGlobalTwelveEighthBindWord14 : List (Fin 10) := [0, 0, 7, 0, 9, 0, 0]

/-- The extraspecial, sign and permutation prefix of the coset of Eighth root 14. -/
def generatedAxisGlobalTwelveEighthBindPre14 : List IdentLetter :=
  [IdentLetter.qel (qCentral 1 * generatedAxisGlobalQMask 2546990), IdentLetter.sign 464 0,
    IdentLetter.mono (1, false), IdentLetter.mono (0, false), IdentLetter.mono (1, false),
    IdentLetter.mono (0, true), IdentLetter.mono (1, false), IdentLetter.mono (0, true),
    IdentLetter.mono (0, true), IdentLetter.mono (1, false), IdentLetter.mono (0, true),
    IdentLetter.mono (0, true), IdentLetter.mono (0, true), IdentLetter.mono (1, false),
    IdentLetter.mono (0, true), IdentLetter.mono (1, false), IdentLetter.mono (0, true),
    IdentLetter.mono (0, true), IdentLetter.mono (1, false), IdentLetter.mono (0, true),
    IdentLetter.mono (0, true), IdentLetter.mono (1, false), IdentLetter.mono (0, false),
    IdentLetter.mono (0, false), IdentLetter.mono (0, false), IdentLetter.mono (0, false),
    IdentLetter.mono (0, false), IdentLetter.mono (1, true), IdentLetter.mono (0, true),
    IdentLetter.mono (1, true), IdentLetter.mono (0, false), IdentLetter.mono (1, true),
    IdentLetter.mono (0, false), IdentLetter.mono (0, false), IdentLetter.mono (1, true),
    IdentLetter.mono (0, true), IdentLetter.mono (0, true), IdentLetter.mono (0, true),
    IdentLetter.mono (1, true), IdentLetter.mono (0, true), IdentLetter.mono (1, true),
    IdentLetter.mono (0, false), IdentLetter.mono (0, false), IdentLetter.mono (1, true),
    IdentLetter.mono (0, false), IdentLetter.mono (0, false), IdentLetter.mono (0, false),
    IdentLetter.mono (1, true), IdentLetter.mono (0, false), IdentLetter.mono (1, false),
    IdentLetter.mono (0, false), IdentLetter.mono (1, false), IdentLetter.mono (0, false),
    IdentLetter.mono (0, false), IdentLetter.mono (0, false), IdentLetter.mono (1, false),
    IdentLetter.mono (0, false), IdentLetter.mono (1, false), IdentLetter.mono (0, false),
    IdentLetter.mono (0, false), IdentLetter.mono (1, false), IdentLetter.mono (0, false),
    IdentLetter.mono (1, false), IdentLetter.mono (0, true), IdentLetter.mono (0, true)]

/-- The representative coset of Eighth root 14. -/
def generatedAxisGlobalTwelveEighthBindCoset14 : H :=
  eighthBindRep generatedAxisGlobalTwelveEighthBindPre14
    generatedAxisGlobalTwelveEighthBindWord14

/-- The odd source word of the representative coset of Eighth root 15. -/
def generatedAxisGlobalTwelveEighthBindWord15 : List (Fin 10) := [0, 7, 8, 0, 7, 8, 0]

/-- The representative coset of Eighth root 15. -/
def generatedAxisGlobalTwelveEighthBindCoset15 : H :=
  eighthBindRep []
    generatedAxisGlobalTwelveEighthBindWord15

/-- The odd source word of the representative coset of Eighth root 16. -/
def generatedAxisGlobalTwelveEighthBindWord16 : List (Fin 10) := [0, 8, 0]

/-- The representative coset of Eighth root 16. -/
def generatedAxisGlobalTwelveEighthBindCoset16 : H :=
  eighthBindRep []
    generatedAxisGlobalTwelveEighthBindWord16

/-- The odd source word of the representative coset of Eighth root 17. -/
def generatedAxisGlobalTwelveEighthBindWord17 : List (Fin 10) := [0, 6, 8, 0]

/-- The representative coset of Eighth root 17. -/
def generatedAxisGlobalTwelveEighthBindCoset17 : H :=
  eighthBindRep []
    generatedAxisGlobalTwelveEighthBindWord17

/-- The odd source word of the representative coset of Eighth root 18. -/
def generatedAxisGlobalTwelveEighthBindWord18 : List (Fin 10) := [0, 7, 8, 0, 7, 7]

/-- The extraspecial, sign and permutation prefix of the coset of Eighth root 18. -/
def generatedAxisGlobalTwelveEighthBindPre18 : List IdentLetter :=
  [IdentLetter.qel (qCentral 0 * generatedAxisGlobalQMask 14936448), IdentLetter.sign 297 0,
    IdentLetter.mono (1, false), IdentLetter.mono (0, false), IdentLetter.mono (0, false),
    IdentLetter.mono (0, false), IdentLetter.mono (1, false), IdentLetter.mono (0, true),
    IdentLetter.mono (0, true), IdentLetter.mono (1, false), IdentLetter.mono (0, false),
    IdentLetter.mono (0, false), IdentLetter.mono (1, false), IdentLetter.mono (0, false),
    IdentLetter.mono (1, false), IdentLetter.mono (0, false), IdentLetter.mono (1, false),
    IdentLetter.mono (0, true), IdentLetter.mono (0, true), IdentLetter.mono (1, false),
    IdentLetter.mono (0, false), IdentLetter.mono (1, false), IdentLetter.mono (0, true),
    IdentLetter.mono (1, false), IdentLetter.mono (0, false), IdentLetter.mono (0, false),
    IdentLetter.mono (0, false), IdentLetter.mono (1, true), IdentLetter.mono (0, true),
    IdentLetter.mono (1, true), IdentLetter.mono (0, true), IdentLetter.mono (0, true),
    IdentLetter.mono (0, true), IdentLetter.mono (1, true), IdentLetter.mono (0, true),
    IdentLetter.mono (1, true), IdentLetter.mono (0, false), IdentLetter.mono (0, false),
    IdentLetter.mono (1, true), IdentLetter.mono (0, false), IdentLetter.mono (1, true),
    IdentLetter.mono (0, false), IdentLetter.mono (0, false), IdentLetter.mono (0, false),
    IdentLetter.mono (1, true), IdentLetter.mono (0, false), IdentLetter.mono (1, true),
    IdentLetter.mono (0, true), IdentLetter.mono (0, true), IdentLetter.mono (0, true),
    IdentLetter.mono (1, false), IdentLetter.mono (0, false), IdentLetter.mono (1, false),
    IdentLetter.mono (0, false), IdentLetter.mono (0, false), IdentLetter.mono (1, false),
    IdentLetter.mono (0, false), IdentLetter.mono (1, false), IdentLetter.mono (0, true),
    IdentLetter.mono (0, true), IdentLetter.mono (0, true), IdentLetter.mono (1, false),
    IdentLetter.mono (0, false), IdentLetter.mono (0, false), IdentLetter.mono (1, false),
    IdentLetter.mono (0, true), IdentLetter.mono (1, false), IdentLetter.mono (0, true),
    IdentLetter.mono (0, true), IdentLetter.mono (1, false), IdentLetter.mono (0, true),
    IdentLetter.mono (1, false)]

/-- The representative coset of Eighth root 18. -/
def generatedAxisGlobalTwelveEighthBindCoset18 : H :=
  eighthBindRep generatedAxisGlobalTwelveEighthBindPre18
    generatedAxisGlobalTwelveEighthBindWord18

/-- The odd source word of the representative coset of Eighth root 19. -/
def generatedAxisGlobalTwelveEighthBindWord19 : List (Fin 10) := [0, 0, 7, 9, 0, 0, 7]

/-- The extraspecial, sign and permutation prefix of the coset of Eighth root 19. -/
def generatedAxisGlobalTwelveEighthBindPre19 : List IdentLetter :=
  [IdentLetter.qel (qCentral 1 * generatedAxisGlobalQMask 8443954), IdentLetter.sign 1516 0,
    IdentLetter.mono (0, true), IdentLetter.mono (0, true), IdentLetter.mono (1, false),
    IdentLetter.mono (0, true), IdentLetter.mono (1, false), IdentLetter.mono (0, true),
    IdentLetter.mono (1, false), IdentLetter.mono (0, false), IdentLetter.mono (1, false),
    IdentLetter.mono (0, true), IdentLetter.mono (1, false), IdentLetter.mono (0, true),
    IdentLetter.mono (0, true), IdentLetter.mono (0, true), IdentLetter.mono (1, false),
    IdentLetter.mono (0, false), IdentLetter.mono (0, false), IdentLetter.mono (0, false),
    IdentLetter.mono (1, false), IdentLetter.mono (0, true), IdentLetter.mono (0, true),
    IdentLetter.mono (0, true), IdentLetter.mono (1, true), IdentLetter.mono (0, false),
    IdentLetter.mono (0, false), IdentLetter.mono (1, true), IdentLetter.mono (0, false),
    IdentLetter.mono (0, false), IdentLetter.mono (0, false), IdentLetter.mono (1, true),
    IdentLetter.mono (0, true), IdentLetter.mono (1, true), IdentLetter.mono (0, false),
    IdentLetter.mono (0, false), IdentLetter.mono (1, true), IdentLetter.mono (0, true),
    IdentLetter.mono (1, true), IdentLetter.mono (0, false), IdentLetter.mono (1, true),
    IdentLetter.mono (0, false), IdentLetter.mono (0, false), IdentLetter.mono (1, true),
    IdentLetter.mono (0, true), IdentLetter.mono (1, false), IdentLetter.mono (0, false),
    IdentLetter.mono (0, false), IdentLetter.mono (1, false), IdentLetter.mono (0, true),
    IdentLetter.mono (1, false), IdentLetter.mono (0, true), IdentLetter.mono (0, true),
    IdentLetter.mono (1, false), IdentLetter.mono (0, true), IdentLetter.mono (1, false),
    IdentLetter.mono (0, false), IdentLetter.mono (0, false), IdentLetter.mono (0, false),
    IdentLetter.mono (1, false), IdentLetter.mono (0, true), IdentLetter.mono (1, false),
    IdentLetter.mono (0, false), IdentLetter.mono (0, false), IdentLetter.mono (0, false),
    IdentLetter.mono (1, false), IdentLetter.mono (0, false), IdentLetter.mono (1, false)]

/-- The representative coset of Eighth root 19. -/
def generatedAxisGlobalTwelveEighthBindCoset19 : H :=
  eighthBindRep generatedAxisGlobalTwelveEighthBindPre19
    generatedAxisGlobalTwelveEighthBindWord19

/-- The odd source word of the representative coset of Eighth root 20. -/
def generatedAxisGlobalTwelveEighthBindWord20 : List (Fin 10) := [0, 0, 9, 6, 0, 0, 9]

/-- The extraspecial, sign and permutation prefix of the coset of Eighth root 20. -/
def generatedAxisGlobalTwelveEighthBindPre20 : List IdentLetter :=
  [IdentLetter.qel (qCentral 1 * generatedAxisGlobalQMask 11665289), IdentLetter.sign 1687 0,
    IdentLetter.mono (1, false), IdentLetter.mono (0, true), IdentLetter.mono (1, false),
    IdentLetter.mono (0, true), IdentLetter.mono (0, true), IdentLetter.mono (0, true),
    IdentLetter.mono (1, false), IdentLetter.mono (0, true), IdentLetter.mono (1, false),
    IdentLetter.mono (0, false), IdentLetter.mono (0, false), IdentLetter.mono (0, false),
    IdentLetter.mono (1, false), IdentLetter.mono (0, false), IdentLetter.mono (0, false),
    IdentLetter.mono (0, false), IdentLetter.mono (1, false), IdentLetter.mono (0, true),
    IdentLetter.mono (0, true), IdentLetter.mono (1, false), IdentLetter.mono (0, false),
    IdentLetter.mono (1, false), IdentLetter.mono (0, false), IdentLetter.mono (0, false),
    IdentLetter.mono (1, true), IdentLetter.mono (0, false), IdentLetter.mono (1, true),
    IdentLetter.mono (0, true), IdentLetter.mono (0, true), IdentLetter.mono (1, true),
    IdentLetter.mono (0, false), IdentLetter.mono (1, true), IdentLetter.mono (0, true),
    IdentLetter.mono (1, true), IdentLetter.mono (0, true), IdentLetter.mono (1, true),
    IdentLetter.mono (0, false), IdentLetter.mono (0, false), IdentLetter.mono (0, false),
    IdentLetter.mono (1, true), IdentLetter.mono (0, true), IdentLetter.mono (0, true),
    IdentLetter.mono (1, true), IdentLetter.mono (0, false), IdentLetter.mono (0, false),
    IdentLetter.mono (1, false), IdentLetter.mono (0, false), IdentLetter.mono (1, false),
    IdentLetter.mono (0, true), IdentLetter.mono (0, true), IdentLetter.mono (0, true),
    IdentLetter.mono (1, false), IdentLetter.mono (0, false), IdentLetter.mono (1, false),
    IdentLetter.mono (0, true), IdentLetter.mono (0, true), IdentLetter.mono (0, true),
    IdentLetter.mono (1, false), IdentLetter.mono (0, true), IdentLetter.mono (1, false),
    IdentLetter.mono (0, true), IdentLetter.mono (1, false), IdentLetter.mono (0, false),
    IdentLetter.mono (0, false), IdentLetter.mono (1, false), IdentLetter.mono (0, true),
    IdentLetter.mono (0, true), IdentLetter.mono (0, true), IdentLetter.mono (1, false),
    IdentLetter.mono (0, true)]

/-- The representative coset of Eighth root 20. -/
def generatedAxisGlobalTwelveEighthBindCoset20 : H :=
  eighthBindRep generatedAxisGlobalTwelveEighthBindPre20
    generatedAxisGlobalTwelveEighthBindWord20

/-- The odd source word of the representative coset of Eighth root 21. -/
def generatedAxisGlobalTwelveEighthBindWord21 : List (Fin 10) := [0, 6, 8, 7, 0]

/-- The representative coset of Eighth root 21. -/
def generatedAxisGlobalTwelveEighthBindCoset21 : H :=
  eighthBindRep []
    generatedAxisGlobalTwelveEighthBindWord21

/-- The odd source word of the representative coset of Eighth root 22. -/
def generatedAxisGlobalTwelveEighthBindWord22 : List (Fin 10) := [0, 8, 6, 6, 0, 7]

/-- The representative coset of Eighth root 22. -/
def generatedAxisGlobalTwelveEighthBindCoset22 : H :=
  eighthBindRep []
    generatedAxisGlobalTwelveEighthBindWord22

/-- The odd source word of the representative coset of Eighth root 23. -/
def generatedAxisGlobalTwelveEighthBindWord23 : List (Fin 10) := [0, 8, 0, 6, 6, 8]

/-- The representative coset of Eighth root 23. -/
def generatedAxisGlobalTwelveEighthBindCoset23 : H :=
  eighthBindRep []
    generatedAxisGlobalTwelveEighthBindWord23

/-- The odd source word of the representative coset of Eighth root 24. -/
def generatedAxisGlobalTwelveEighthBindWord24 : List (Fin 10) := [0, 6, 8]

/-- The representative coset of Eighth root 24. -/
def generatedAxisGlobalTwelveEighthBindCoset24 : H :=
  eighthBindRep []
    generatedAxisGlobalTwelveEighthBindWord24

/-- The odd source word of the representative coset of Eighth root 25. -/
def generatedAxisGlobalTwelveEighthBindWord25 : List (Fin 10) := [0, 8, 7, 7, 8]

/-- The representative coset of Eighth root 25. -/
def generatedAxisGlobalTwelveEighthBindCoset25 : H :=
  eighthBindRep []
    generatedAxisGlobalTwelveEighthBindWord25

/-- The odd source word of the representative coset of Eighth root 26. -/
def generatedAxisGlobalTwelveEighthBindWord26 : List (Fin 10) := [0, 8]

/-- The representative coset of Eighth root 26. -/
def generatedAxisGlobalTwelveEighthBindCoset26 : H :=
  eighthBindRep []
    generatedAxisGlobalTwelveEighthBindWord26

/-- The odd source word of the representative coset of Eighth root 27. -/
def generatedAxisGlobalTwelveEighthBindWord27 : List (Fin 10) := [0]

/-- The representative coset of Eighth root 27. -/
def generatedAxisGlobalTwelveEighthBindCoset27 : H :=
  eighthBindRep []
    generatedAxisGlobalTwelveEighthBindWord27

/-- The odd source word of the representative coset of Eighth root 28. -/
def generatedAxisGlobalTwelveEighthBindWord28 : List (Fin 10) := [0, 6]

/-- The representative coset of Eighth root 28. -/
def generatedAxisGlobalTwelveEighthBindCoset28 : H :=
  eighthBindRep []
    generatedAxisGlobalTwelveEighthBindWord28

/-- The odd source word of the representative coset of Eighth root 29. -/
def generatedAxisGlobalTwelveEighthBindWord29 : List (Fin 10) := [0, 8, 6, 6, 0, 8, 0]

/-- The representative coset of Eighth root 29. -/
def generatedAxisGlobalTwelveEighthBindCoset29 : H :=
  eighthBindRep []
    generatedAxisGlobalTwelveEighthBindWord29

/-- The odd source word of the representative coset of Eighth root 30. -/
def generatedAxisGlobalTwelveEighthBindWord30 : List (Fin 10) := [0, 8, 0, 6, 8, 6, 0]

/-- The extraspecial, sign and permutation prefix of the coset of Eighth root 30. -/
def generatedAxisGlobalTwelveEighthBindPre30 : List IdentLetter :=
  [IdentLetter.qel (qCentral 1 * generatedAxisGlobalQMask 13882608), IdentLetter.sign 1928 0,
    IdentLetter.mono (1, false), IdentLetter.mono (0, false), IdentLetter.mono (1, false),
    IdentLetter.mono (0, false), IdentLetter.mono (0, false), IdentLetter.mono (1, false),
    IdentLetter.mono (0, true), IdentLetter.mono (1, false), IdentLetter.mono (0, true),
    IdentLetter.mono (0, true), IdentLetter.mono (1, false), IdentLetter.mono (0, false),
    IdentLetter.mono (0, false), IdentLetter.mono (1, false), IdentLetter.mono (0, true),
    IdentLetter.mono (1, false), IdentLetter.mono (0, true), IdentLetter.mono (1, false),
    IdentLetter.mono (0, false), IdentLetter.mono (1, false), IdentLetter.mono (0, false),
    IdentLetter.mono (0, false), IdentLetter.mono (1, false), IdentLetter.mono (0, false),
    IdentLetter.mono (1, true), IdentLetter.mono (0, false), IdentLetter.mono (0, false),
    IdentLetter.mono (0, false), IdentLetter.mono (1, true), IdentLetter.mono (0, false),
    IdentLetter.mono (1, true), IdentLetter.mono (0, true), IdentLetter.mono (0, true),
    IdentLetter.mono (1, true), IdentLetter.mono (0, false), IdentLetter.mono (0, false),
    IdentLetter.mono (0, false), IdentLetter.mono (1, true), IdentLetter.mono (0, true),
    IdentLetter.mono (0, true), IdentLetter.mono (0, true), IdentLetter.mono (1, true),
    IdentLetter.mono (0, true), IdentLetter.mono (0, true), IdentLetter.mono (0, true),
    IdentLetter.mono (1, true), IdentLetter.mono (0, false), IdentLetter.mono (1, false),
    IdentLetter.mono (0, false), IdentLetter.mono (0, false), IdentLetter.mono (1, false),
    IdentLetter.mono (0, true), IdentLetter.mono (1, false), IdentLetter.mono (0, true),
    IdentLetter.mono (1, false), IdentLetter.mono (0, false), IdentLetter.mono (0, false),
    IdentLetter.mono (1, false), IdentLetter.mono (0, false), IdentLetter.mono (0, false),
    IdentLetter.mono (0, false), IdentLetter.mono (1, false), IdentLetter.mono (0, true),
    IdentLetter.mono (1, false), IdentLetter.mono (0, false), IdentLetter.mono (0, false),
    IdentLetter.mono (0, false), IdentLetter.mono (1, false), IdentLetter.mono (0, false),
    IdentLetter.mono (0, false)]

/-- The representative coset of Eighth root 30. -/
def generatedAxisGlobalTwelveEighthBindCoset30 : H :=
  eighthBindRep generatedAxisGlobalTwelveEighthBindPre30
    generatedAxisGlobalTwelveEighthBindWord30

/-- The odd source word of the representative coset of Eighth root 31. -/
def generatedAxisGlobalTwelveEighthBindWord31 : List (Fin 10) := [0, 0, 9, 0, 0, 6, 6, 9, 0, 0]

/-- The extraspecial, sign and permutation prefix of the coset of Eighth root 31. -/
def generatedAxisGlobalTwelveEighthBindPre31 : List IdentLetter :=
  [IdentLetter.qel (qCentral 0 * generatedAxisGlobalQMask 2170979), IdentLetter.sign 78 0,
    IdentLetter.mono (1, false), IdentLetter.mono (0, true), IdentLetter.mono (1, false),
    IdentLetter.mono (0, false), IdentLetter.mono (0, false), IdentLetter.mono (0, false),
    IdentLetter.mono (1, false), IdentLetter.mono (0, true), IdentLetter.mono (0, true),
    IdentLetter.mono (1, false), IdentLetter.mono (0, true), IdentLetter.mono (1, false),
    IdentLetter.mono (0, true), IdentLetter.mono (1, false), IdentLetter.mono (0, false),
    IdentLetter.mono (0, false), IdentLetter.mono (1, false), IdentLetter.mono (0, false),
    IdentLetter.mono (1, false), IdentLetter.mono (0, true), IdentLetter.mono (0, true),
    IdentLetter.mono (1, true), IdentLetter.mono (0, true), IdentLetter.mono (1, true),
    IdentLetter.mono (0, false), IdentLetter.mono (0, false), IdentLetter.mono (1, true),
    IdentLetter.mono (0, false), IdentLetter.mono (0, false), IdentLetter.mono (1, true),
    IdentLetter.mono (0, false), IdentLetter.mono (0, false), IdentLetter.mono (0, false),
    IdentLetter.mono (1, true), IdentLetter.mono (0, false), IdentLetter.mono (1, true),
    IdentLetter.mono (0, false), IdentLetter.mono (0, false), IdentLetter.mono (1, true),
    IdentLetter.mono (0, false), IdentLetter.mono (1, true), IdentLetter.mono (0, true),
    IdentLetter.mono (1, true), IdentLetter.mono (0, false), IdentLetter.mono (1, false),
    IdentLetter.mono (0, true), IdentLetter.mono (1, false), IdentLetter.mono (0, true),
    IdentLetter.mono (0, true), IdentLetter.mono (1, false), IdentLetter.mono (0, true),
    IdentLetter.mono (0, true), IdentLetter.mono (0, true), IdentLetter.mono (1, false),
    IdentLetter.mono (0, false), IdentLetter.mono (1, false), IdentLetter.mono (0, true),
    IdentLetter.mono (0, true), IdentLetter.mono (0, true), IdentLetter.mono (1, false),
    IdentLetter.mono (0, true), IdentLetter.mono (1, false), IdentLetter.mono (0, true),
    IdentLetter.mono (1, false), IdentLetter.mono (0, false)]

/-- The representative coset of Eighth root 31. -/
def generatedAxisGlobalTwelveEighthBindCoset31 : H :=
  eighthBindRep generatedAxisGlobalTwelveEighthBindPre31
    generatedAxisGlobalTwelveEighthBindWord31

/-- The odd source word of the representative coset of Eighth root 32. -/
def generatedAxisGlobalTwelveEighthBindWord32 : List (Fin 10) := [0, 0, 7, 9, 7, 0, 0, 9, 0, 0]

/-- The extraspecial, sign and permutation prefix of the coset of Eighth root 32. -/
def generatedAxisGlobalTwelveEighthBindPre32 : List IdentLetter :=
  [IdentLetter.qel (qCentral 0 * generatedAxisGlobalQMask 2724567), IdentLetter.sign 637 0,
    IdentLetter.mono (0, true), IdentLetter.mono (0, true), IdentLetter.mono (1, false),
    IdentLetter.mono (0, false), IdentLetter.mono (1, false), IdentLetter.mono (0, false),
    IdentLetter.mono (0, false), IdentLetter.mono (1, false), IdentLetter.mono (0, true),
    IdentLetter.mono (0, true), IdentLetter.mono (1, false), IdentLetter.mono (0, false),
    IdentLetter.mono (1, false), IdentLetter.mono (0, false), IdentLetter.mono (1, false),
    IdentLetter.mono (0, true), IdentLetter.mono (0, true), IdentLetter.mono (1, false),
    IdentLetter.mono (0, true), IdentLetter.mono (1, false), IdentLetter.mono (0, false),
    IdentLetter.mono (1, true), IdentLetter.mono (0, false), IdentLetter.mono (1, true),
    IdentLetter.mono (0, true), IdentLetter.mono (0, true), IdentLetter.mono (0, true),
    IdentLetter.mono (1, true), IdentLetter.mono (0, false), IdentLetter.mono (0, false),
    IdentLetter.mono (0, false), IdentLetter.mono (1, true), IdentLetter.mono (0, false),
    IdentLetter.mono (1, true), IdentLetter.mono (0, true), IdentLetter.mono (1, true),
    IdentLetter.mono (0, true), IdentLetter.mono (0, true), IdentLetter.mono (1, true),
    IdentLetter.mono (0, true), IdentLetter.mono (1, true), IdentLetter.mono (0, false),
    IdentLetter.mono (0, false), IdentLetter.mono (0, false), IdentLetter.mono (0, false),
    IdentLetter.mono (1, false), IdentLetter.mono (0, true), IdentLetter.mono (1, false),
    IdentLetter.mono (0, false), IdentLetter.mono (0, false), IdentLetter.mono (1, false),
    IdentLetter.mono (0, true), IdentLetter.mono (1, false), IdentLetter.mono (0, true),
    IdentLetter.mono (0, true), IdentLetter.mono (0, true), IdentLetter.mono (1, false),
    IdentLetter.mono (0, false), IdentLetter.mono (0, false), IdentLetter.mono (1, false),
    IdentLetter.mono (0, false), IdentLetter.mono (1, false), IdentLetter.mono (0, true),
    IdentLetter.mono (1, false), IdentLetter.mono (0, true), IdentLetter.mono (0, true),
    IdentLetter.mono (0, true), IdentLetter.mono (1, false), IdentLetter.mono (0, true)]

/-- The representative coset of Eighth root 32. -/
def generatedAxisGlobalTwelveEighthBindCoset32 : H :=
  eighthBindRep generatedAxisGlobalTwelveEighthBindPre32
    generatedAxisGlobalTwelveEighthBindWord32

/-- The odd source word of the representative coset of Eighth root 33. -/
def generatedAxisGlobalTwelveEighthBindWord33 : List (Fin 10) := [0, 0, 7, 9, 0, 0, 7, 0, 9, 0, 0]

/-- The extraspecial, sign and permutation prefix of the coset of Eighth root 33. -/
def generatedAxisGlobalTwelveEighthBindPre33 : List IdentLetter :=
  [IdentLetter.qel (qCentral 0 * generatedAxisGlobalQMask 6014393), IdentLetter.sign 1190 0,
    IdentLetter.mono (1, false), IdentLetter.mono (0, true), IdentLetter.mono (1, false),
    IdentLetter.mono (0, false), IdentLetter.mono (0, false), IdentLetter.mono (0, false),
    IdentLetter.mono (1, false), IdentLetter.mono (0, true), IdentLetter.mono (0, true),
    IdentLetter.mono (1, false), IdentLetter.mono (0, true), IdentLetter.mono (1, false),
    IdentLetter.mono (0, true), IdentLetter.mono (1, false), IdentLetter.mono (0, false),
    IdentLetter.mono (0, false), IdentLetter.mono (1, false), IdentLetter.mono (0, false),
    IdentLetter.mono (1, false), IdentLetter.mono (0, true), IdentLetter.mono (0, true),
    IdentLetter.mono (1, true), IdentLetter.mono (0, true), IdentLetter.mono (1, true),
    IdentLetter.mono (0, false), IdentLetter.mono (0, false), IdentLetter.mono (1, true),
    IdentLetter.mono (0, false), IdentLetter.mono (0, false), IdentLetter.mono (1, true),
    IdentLetter.mono (0, false), IdentLetter.mono (0, false), IdentLetter.mono (0, false),
    IdentLetter.mono (1, true), IdentLetter.mono (0, false), IdentLetter.mono (1, true),
    IdentLetter.mono (0, false), IdentLetter.mono (0, false), IdentLetter.mono (1, true),
    IdentLetter.mono (0, false), IdentLetter.mono (1, true), IdentLetter.mono (0, true),
    IdentLetter.mono (1, true), IdentLetter.mono (0, true), IdentLetter.mono (1, false),
    IdentLetter.mono (0, true), IdentLetter.mono (1, false), IdentLetter.mono (0, false),
    IdentLetter.mono (0, false), IdentLetter.mono (1, false), IdentLetter.mono (0, true),
    IdentLetter.mono (1, false), IdentLetter.mono (0, true), IdentLetter.mono (0, true),
    IdentLetter.mono (1, false), IdentLetter.mono (0, false), IdentLetter.mono (1, false),
    IdentLetter.mono (0, true), IdentLetter.mono (0, true), IdentLetter.mono (0, true),
    IdentLetter.mono (1, false), IdentLetter.mono (0, true), IdentLetter.mono (1, false),
    IdentLetter.mono (0, false), IdentLetter.mono (0, false), IdentLetter.mono (1, false)]

/-- The representative coset of Eighth root 33. -/
def generatedAxisGlobalTwelveEighthBindCoset33 : H :=
  eighthBindRep generatedAxisGlobalTwelveEighthBindPre33
    generatedAxisGlobalTwelveEighthBindWord33

/-- The odd source word of the representative coset of Eighth root 34. -/
def generatedAxisGlobalTwelveEighthBindWord34 : List (Fin 10) := [0, 0, 9, 0, 0, 7, 7, 9, 0, 0]

/-- The extraspecial, sign and permutation prefix of the coset of Eighth root 34. -/
def generatedAxisGlobalTwelveEighthBindPre34 : List IdentLetter :=
  [IdentLetter.qel (qCentral 0 * generatedAxisGlobalQMask 14427251), IdentLetter.sign 1566 0,
    IdentLetter.mono (1, false), IdentLetter.mono (0, true), IdentLetter.mono (0, true),
    IdentLetter.mono (1, false), IdentLetter.mono (0, true), IdentLetter.mono (0, true),
    IdentLetter.mono (1, false), IdentLetter.mono (0, false), IdentLetter.mono (1, false),
    IdentLetter.mono (0, true), IdentLetter.mono (1, false), IdentLetter.mono (0, false),
    IdentLetter.mono (1, false), IdentLetter.mono (0, false), IdentLetter.mono (1, false),
    IdentLetter.mono (0, true), IdentLetter.mono (0, true), IdentLetter.mono (1, false),
    IdentLetter.mono (0, true), IdentLetter.mono (0, true), IdentLetter.mono (0, true),
    IdentLetter.mono (0, true), IdentLetter.mono (1, true), IdentLetter.mono (0, false),
    IdentLetter.mono (0, false), IdentLetter.mono (1, true), IdentLetter.mono (0, false),
    IdentLetter.mono (1, true), IdentLetter.mono (0, false), IdentLetter.mono (0, false),
    IdentLetter.mono (1, true), IdentLetter.mono (0, false), IdentLetter.mono (0, false),
    IdentLetter.mono (0, false), IdentLetter.mono (1, true), IdentLetter.mono (0, false),
    IdentLetter.mono (0, false), IdentLetter.mono (0, false), IdentLetter.mono (1, true),
    IdentLetter.mono (0, false), IdentLetter.mono (1, true), IdentLetter.mono (0, true),
    IdentLetter.mono (0, true), IdentLetter.mono (1, false), IdentLetter.mono (0, true),
    IdentLetter.mono (1, false), IdentLetter.mono (0, false), IdentLetter.mono (0, false),
    IdentLetter.mono (1, false), IdentLetter.mono (0, true), IdentLetter.mono (1, false),
    IdentLetter.mono (0, false), IdentLetter.mono (0, false), IdentLetter.mono (0, false),
    IdentLetter.mono (1, false), IdentLetter.mono (0, true), IdentLetter.mono (0, true),
    IdentLetter.mono (1, false), IdentLetter.mono (0, false), IdentLetter.mono (0, false),
    IdentLetter.mono (0, false), IdentLetter.mono (1, false), IdentLetter.mono (0, false),
    IdentLetter.mono (0, false), IdentLetter.mono (1, false), IdentLetter.mono (0, true),
    IdentLetter.mono (1, false), IdentLetter.mono (0, true)]

/-- The representative coset of Eighth root 34. -/
def generatedAxisGlobalTwelveEighthBindCoset34 : H :=
  eighthBindRep generatedAxisGlobalTwelveEighthBindPre34
    generatedAxisGlobalTwelveEighthBindWord34

/-- The odd source word of the representative coset of Eighth root 35. -/
def generatedAxisGlobalTwelveEighthBindWord35 : List (Fin 10) := [0, 8, 0, 7, 7, 8, 0]

/-- The representative coset of Eighth root 35. -/
def generatedAxisGlobalTwelveEighthBindCoset35 : H :=
  eighthBindRep []
    generatedAxisGlobalTwelveEighthBindWord35

/-- The odd source word of the representative coset of Eighth root 36. -/
def generatedAxisGlobalTwelveEighthBindWord36 : List (Fin 10) := [0, 0, 7, 0, 0, 9, 7, 9, 0, 0]

/-- The extraspecial, sign and permutation prefix of the coset of Eighth root 36. -/
def generatedAxisGlobalTwelveEighthBindPre36 : List IdentLetter :=
  [IdentLetter.qel (qCentral 0 * generatedAxisGlobalQMask 9308953), IdentLetter.sign 1387 0,
    IdentLetter.mono (0, false), IdentLetter.mono (1, false), IdentLetter.mono (0, false),
    IdentLetter.mono (1, false), IdentLetter.mono (0, true), IdentLetter.mono (0, true),
    IdentLetter.mono (1, false), IdentLetter.mono (0, false), IdentLetter.mono (1, false),
    IdentLetter.mono (0, true), IdentLetter.mono (0, true), IdentLetter.mono (1, false),
    IdentLetter.mono (0, false), IdentLetter.mono (0, false), IdentLetter.mono (0, false),
    IdentLetter.mono (1, false), IdentLetter.mono (0, false), IdentLetter.mono (0, false),
    IdentLetter.mono (1, false), IdentLetter.mono (0, false), IdentLetter.mono (0, false),
    IdentLetter.mono (0, false), IdentLetter.mono (1, false), IdentLetter.mono (0, true),
    IdentLetter.mono (1, true), IdentLetter.mono (0, false), IdentLetter.mono (0, false),
    IdentLetter.mono (0, false), IdentLetter.mono (1, true), IdentLetter.mono (0, false),
    IdentLetter.mono (0, false), IdentLetter.mono (0, false), IdentLetter.mono (1, true),
    IdentLetter.mono (0, false), IdentLetter.mono (0, false), IdentLetter.mono (1, true),
    IdentLetter.mono (0, true), IdentLetter.mono (1, true), IdentLetter.mono (0, true),
    IdentLetter.mono (0, true), IdentLetter.mono (1, true), IdentLetter.mono (0, false),
    IdentLetter.mono (0, false), IdentLetter.mono (1, true), IdentLetter.mono (0, false),
    IdentLetter.mono (0, false), IdentLetter.mono (1, false), IdentLetter.mono (0, true),
    IdentLetter.mono (0, true), IdentLetter.mono (1, false), IdentLetter.mono (0, false),
    IdentLetter.mono (1, false), IdentLetter.mono (0, false), IdentLetter.mono (0, false),
    IdentLetter.mono (0, false), IdentLetter.mono (1, false), IdentLetter.mono (0, true),
    IdentLetter.mono (1, false), IdentLetter.mono (0, false), IdentLetter.mono (1, false),
    IdentLetter.mono (0, false), IdentLetter.mono (1, false), IdentLetter.mono (0, true),
    IdentLetter.mono (1, false), IdentLetter.mono (0, false)]

/-- The representative coset of Eighth root 36. -/
def generatedAxisGlobalTwelveEighthBindCoset36 : H :=
  eighthBindRep generatedAxisGlobalTwelveEighthBindPre36
    generatedAxisGlobalTwelveEighthBindWord36

/-- Eighth root 1 from the identifications of both triality images at its coset. -/
theorem generatedAxisGlobalTwelveEighthBind_root1
    (hpos : ∃ i : Fin 12, ∃ g : H,
      sExtra (rhoLocal generatedAxisGlobalTwelveEighthBindCoset1 generatedEighthAxis) =
        rhoLocal g (generatedAxisGlobalTwelveRepresentative i))
    (hneg : ∃ i : Fin 12, ∃ g : H,
      sExtra⁻¹ (rhoLocal generatedAxisGlobalTwelveEighthBindCoset1 generatedEighthAxis) =
        rhoLocal g (generatedAxisGlobalTwelveRepresentative i)) :
    GeneratedAxisGlobalTwelveEighthRootBound 1 :=
  eighthBind_rootBound_of_ids 1 [] (by decide)
    generatedAxisGlobalTwelveEighthBindWord1 (by decide) [12, 14, 9, 14, 1]
    (by decide +kernel) hpos hneg

/-- Eighth root 2 from the identifications of both triality images at its coset. -/
theorem generatedAxisGlobalTwelveEighthBind_root2
    (hpos : ∃ i : Fin 12, ∃ g : H,
      sExtra (rhoLocal generatedAxisGlobalTwelveEighthBindCoset2 generatedEighthAxis) =
        rhoLocal g (generatedAxisGlobalTwelveRepresentative i))
    (hneg : ∃ i : Fin 12, ∃ g : H,
      sExtra⁻¹ (rhoLocal generatedAxisGlobalTwelveEighthBindCoset2 generatedEighthAxis) =
        rhoLocal g (generatedAxisGlobalTwelveRepresentative i)) :
    GeneratedAxisGlobalTwelveEighthRootBound 2 :=
  eighthBind_rootBound_of_ids 2 [] (by decide)
    generatedAxisGlobalTwelveEighthBindWord2 (by decide) [13, 15, 12, 2, 15, 12, 12]
    (by decide +kernel) hpos hneg

/-- Eighth root 3 from the identifications of both triality images at its coset. -/
theorem generatedAxisGlobalTwelveEighthBind_root3
    (hpos : ∃ i : Fin 12, ∃ g : H,
      sExtra (rhoLocal generatedAxisGlobalTwelveEighthBindCoset3 generatedEighthAxis) =
        rhoLocal g (generatedAxisGlobalTwelveRepresentative i))
    (hneg : ∃ i : Fin 12, ∃ g : H,
      sExtra⁻¹ (rhoLocal generatedAxisGlobalTwelveEighthBindCoset3 generatedEighthAxis) =
        rhoLocal g (generatedAxisGlobalTwelveRepresentative i)) :
    GeneratedAxisGlobalTwelveEighthRootBound 3 :=
  eighthBind_rootBound_of_ids 3 [] (by decide)
    generatedAxisGlobalTwelveEighthBindWord3 (by decide) [4]
    (by decide +kernel) hpos hneg

/-- Eighth root 4 from the Tenth transport T26- (gtenth) and the identification of the
other image at its coset (record `E4@T26-` of goctad). -/
theorem generatedAxisGlobalTwelveEighthBind_root4 (x : H)
    (htr : sExtra⁻¹ (rhoLocal x (generatedAxisGlobalTwelveRepresentative 11)) =
      rhoLocal generatedAxisGlobalTwelveEighthBindCoset4 generatedEighthAxis)
    (hnew : ∃ i : Fin 12, ∃ g : H,
      sExtra⁻¹ (rhoLocal generatedAxisGlobalTwelveEighthBindCoset4 generatedEighthAxis) =
        rhoLocal g (generatedAxisGlobalTwelveRepresentative i)) :
    GeneratedAxisGlobalTwelveEighthRootBound 4 := by
  have hknown : ∃ i : Fin 12, ∃ g : H,
      sExtra (rhoLocal generatedAxisGlobalTwelveEighthBindCoset4 generatedEighthAxis) =
        rhoLocal g (generatedAxisGlobalTwelveRepresentative i) := by
    refine ⟨11, x, ?_⟩
    rw [← htr, LinearEquiv.coe_inv, LinearEquiv.apply_symm_apply]
  exact eighthBind_rootBound_of_ids 4 generatedAxisGlobalTwelveEighthBindPre4 (by decide)
    generatedAxisGlobalTwelveEighthBindWord4 (by decide) [4, 15, 13, 14, 13, 5, 15, 13]
    (by decide +kernel) hknown hnew

/-- Eighth root 5 from the identifications of both triality images at its coset. -/
theorem generatedAxisGlobalTwelveEighthBind_root5
    (hpos : ∃ i : Fin 12, ∃ g : H,
      sExtra (rhoLocal generatedAxisGlobalTwelveEighthBindCoset5 generatedEighthAxis) =
        rhoLocal g (generatedAxisGlobalTwelveRepresentative i))
    (hneg : ∃ i : Fin 12, ∃ g : H,
      sExtra⁻¹ (rhoLocal generatedAxisGlobalTwelveEighthBindCoset5 generatedEighthAxis) =
        rhoLocal g (generatedAxisGlobalTwelveRepresentative i)) :
    GeneratedAxisGlobalTwelveEighthRootBound 5 :=
  eighthBind_rootBound_of_ids 5 [] (by decide)
    generatedAxisGlobalTwelveEighthBindWord5 (by decide) [14, 10, 13, 14, 13, 14, 9]
    (by decide +kernel) hpos hneg

/-- Eighth root 6 from the identifications of both triality images at its coset. -/
theorem generatedAxisGlobalTwelveEighthBind_root6
    (hpos : ∃ i : Fin 12, ∃ g : H,
      sExtra (rhoLocal generatedAxisGlobalTwelveEighthBindCoset6 generatedEighthAxis) =
        rhoLocal g (generatedAxisGlobalTwelveRepresentative i))
    (hneg : ∃ i : Fin 12, ∃ g : H,
      sExtra⁻¹ (rhoLocal generatedAxisGlobalTwelveEighthBindCoset6 generatedEighthAxis) =
        rhoLocal g (generatedAxisGlobalTwelveRepresentative i)) :
    GeneratedAxisGlobalTwelveEighthRootBound 6 :=
  eighthBind_rootBound_of_ids 6 [] (by decide)
    generatedAxisGlobalTwelveEighthBindWord6 (by decide) [12, 12, 14, 14, 5, 14, 6]
    (by decide +kernel) hpos hneg

/-- Eighth root 7 from the two Tenth transports T12+ and T12- (gtenth) at one
Tenth coset `x`. -/
theorem generatedAxisGlobalTwelveEighthBind_root7 (x : H)
    (htr : sExtra (rhoLocal x (generatedAxisGlobalTwelveRepresentative 11)) =
      rhoLocal generatedAxisGlobalTwelveEighthBindCoset7 generatedEighthAxis)
    (hother : ∃ i : Fin 12, ∃ g : H,
      sExtra⁻¹ (rhoLocal x (generatedAxisGlobalTwelveRepresentative 11)) =
        rhoLocal g (generatedAxisGlobalTwelveRepresentative i)) :
    GeneratedAxisGlobalTwelveEighthRootBound 7 := by
  obtain ⟨i, g, hg⟩ := hother
  exact eighthBind_rootBound_of_forward 7 generatedAxisGlobalTwelveEighthBindPre7 (by decide)
    generatedAxisGlobalTwelveEighthBindWord7 (by decide) [12, 14, 12, 12, 15, 15, 3, 12]
    (by decide +kernel) 11 x htr
    (generatedAxisGlobalTwelve_mem_of_transport i g hg)

/-- Eighth root 8 from the two Tenth transports T36- and T36+ (gtenth) at one
Tenth coset `x`. -/
theorem generatedAxisGlobalTwelveEighthBind_root8 (x : H)
    (htr : sExtra⁻¹ (rhoLocal x (generatedAxisGlobalTwelveRepresentative 11)) =
      rhoLocal generatedAxisGlobalTwelveEighthBindCoset8 generatedEighthAxis)
    (hother : ∃ i : Fin 12, ∃ g : H,
      sExtra (rhoLocal x (generatedAxisGlobalTwelveRepresentative 11)) =
        rhoLocal g (generatedAxisGlobalTwelveRepresentative i)) :
    GeneratedAxisGlobalTwelveEighthRootBound 8 := by
  obtain ⟨i, g, hg⟩ := hother
  exact eighthBind_rootBound_of_inverse 8 generatedAxisGlobalTwelveEighthBindPre8 (by decide)
    generatedAxisGlobalTwelveEighthBindWord8 (by decide) [14, 12, 14, 12, 1, 15, 0]
    (by decide +kernel) 11 x htr
    (generatedAxisGlobalTwelve_mem_of_transport i g hg)

/-- Eighth root 9 from the identifications of both triality images at its coset. -/
theorem generatedAxisGlobalTwelveEighthBind_root9
    (hpos : ∃ i : Fin 12, ∃ g : H,
      sExtra (rhoLocal generatedAxisGlobalTwelveEighthBindCoset9 generatedEighthAxis) =
        rhoLocal g (generatedAxisGlobalTwelveRepresentative i))
    (hneg : ∃ i : Fin 12, ∃ g : H,
      sExtra⁻¹ (rhoLocal generatedAxisGlobalTwelveEighthBindCoset9 generatedEighthAxis) =
        rhoLocal g (generatedAxisGlobalTwelveRepresentative i)) :
    GeneratedAxisGlobalTwelveEighthRootBound 9 :=
  eighthBind_rootBound_of_ids 9 [] (by decide)
    generatedAxisGlobalTwelveEighthBindWord9 (by decide) [15, 12, 9, 12, 12, 15]
    (by decide +kernel) hpos hneg

/-- Eighth root 10 from the Tenth transport T27- (gtenth) and the identification of the
other image at its coset (record `E10@T27-` of goctad). -/
theorem generatedAxisGlobalTwelveEighthBind_root10 (x : H)
    (htr : sExtra⁻¹ (rhoLocal x (generatedAxisGlobalTwelveRepresentative 11)) =
      rhoLocal generatedAxisGlobalTwelveEighthBindCoset10 generatedEighthAxis)
    (hnew : ∃ i : Fin 12, ∃ g : H,
      sExtra⁻¹ (rhoLocal generatedAxisGlobalTwelveEighthBindCoset10 generatedEighthAxis) =
        rhoLocal g (generatedAxisGlobalTwelveRepresentative i)) :
    GeneratedAxisGlobalTwelveEighthRootBound 10 := by
  have hknown : ∃ i : Fin 12, ∃ g : H,
      sExtra (rhoLocal generatedAxisGlobalTwelveEighthBindCoset10 generatedEighthAxis) =
        rhoLocal g (generatedAxisGlobalTwelveRepresentative i) := by
    refine ⟨11, x, ?_⟩
    rw [← htr, LinearEquiv.coe_inv, LinearEquiv.apply_symm_apply]
  exact eighthBind_rootBound_of_ids 10 generatedAxisGlobalTwelveEighthBindPre10 (by decide)
    generatedAxisGlobalTwelveEighthBindWord10 (by decide) [15, 12, 15, 13, 13, 3, 15, 3]
    (by decide +kernel) hknown hnew

/-- Eighth root 11 from the identifications of both triality images at its coset. -/
theorem generatedAxisGlobalTwelveEighthBind_root11
    (hpos : ∃ i : Fin 12, ∃ g : H,
      sExtra (rhoLocal generatedAxisGlobalTwelveEighthBindCoset11 generatedEighthAxis) =
        rhoLocal g (generatedAxisGlobalTwelveRepresentative i))
    (hneg : ∃ i : Fin 12, ∃ g : H,
      sExtra⁻¹ (rhoLocal generatedAxisGlobalTwelveEighthBindCoset11 generatedEighthAxis) =
        rhoLocal g (generatedAxisGlobalTwelveRepresentative i)) :
    GeneratedAxisGlobalTwelveEighthRootBound 11 :=
  eighthBind_rootBound_of_ids 11 [] (by decide)
    generatedAxisGlobalTwelveEighthBindWord11 (by decide) [14, 12, 15, 0, 12, 12, 9]
    (by decide +kernel) hpos hneg

/-- Eighth root 12 from the identifications of both triality images at its coset. -/
theorem generatedAxisGlobalTwelveEighthBind_root12
    (hpos : ∃ i : Fin 12, ∃ g : H,
      sExtra (rhoLocal generatedAxisGlobalTwelveEighthBindCoset12 generatedEighthAxis) =
        rhoLocal g (generatedAxisGlobalTwelveRepresentative i))
    (hneg : ∃ i : Fin 12, ∃ g : H,
      sExtra⁻¹ (rhoLocal generatedAxisGlobalTwelveEighthBindCoset12 generatedEighthAxis) =
        rhoLocal g (generatedAxisGlobalTwelveRepresentative i)) :
    GeneratedAxisGlobalTwelveEighthRootBound 12 :=
  eighthBind_rootBound_of_ids 12 [] (by decide)
    generatedAxisGlobalTwelveEighthBindWord12 (by decide) [15, 15, 7, 15, 1]
    (by decide +kernel) hpos hneg

/-- Eighth root 13 from the identifications of both triality images at its coset. -/
theorem generatedAxisGlobalTwelveEighthBind_root13
    (hpos : ∃ i : Fin 12, ∃ g : H,
      sExtra (rhoLocal generatedAxisGlobalTwelveEighthBindCoset13 generatedEighthAxis) =
        rhoLocal g (generatedAxisGlobalTwelveRepresentative i))
    (hneg : ∃ i : Fin 12, ∃ g : H,
      sExtra⁻¹ (rhoLocal generatedAxisGlobalTwelveEighthBindCoset13 generatedEighthAxis) =
        rhoLocal g (generatedAxisGlobalTwelveRepresentative i)) :
    GeneratedAxisGlobalTwelveEighthRootBound 13 :=
  eighthBind_rootBound_of_ids 13 [] (by decide)
    generatedAxisGlobalTwelveEighthBindWord13 (by decide) [12, 15, 12, 4]
    (by decide +kernel) hpos hneg

/-- Eighth root 14 from the Tenth transport T43- (gtenth) and the identification of the
other image at its coset (record `E14@T43-` of goctad). -/
theorem generatedAxisGlobalTwelveEighthBind_root14 (x : H)
    (htr : sExtra⁻¹ (rhoLocal x (generatedAxisGlobalTwelveRepresentative 11)) =
      rhoLocal generatedAxisGlobalTwelveEighthBindCoset14 generatedEighthAxis)
    (hnew : ∃ i : Fin 12, ∃ g : H,
      sExtra⁻¹ (rhoLocal generatedAxisGlobalTwelveEighthBindCoset14 generatedEighthAxis) =
        rhoLocal g (generatedAxisGlobalTwelveRepresentative i)) :
    GeneratedAxisGlobalTwelveEighthRootBound 14 := by
  have hknown : ∃ i : Fin 12, ∃ g : H,
      sExtra (rhoLocal generatedAxisGlobalTwelveEighthBindCoset14 generatedEighthAxis) =
        rhoLocal g (generatedAxisGlobalTwelveRepresentative i) := by
    refine ⟨11, x, ?_⟩
    rw [← htr, LinearEquiv.coe_inv, LinearEquiv.apply_symm_apply]
  exact eighthBind_rootBound_of_ids 14 generatedAxisGlobalTwelveEighthBindPre14 (by decide)
    generatedAxisGlobalTwelveEighthBindWord14 (by decide) [13, 15, 15, 15, 12, 8, 15, 0]
    (by decide +kernel) hknown hnew

/-- Eighth root 15 from the identifications of both triality images at its coset. -/
theorem generatedAxisGlobalTwelveEighthBind_root15
    (hpos : ∃ i : Fin 12, ∃ g : H,
      sExtra (rhoLocal generatedAxisGlobalTwelveEighthBindCoset15 generatedEighthAxis) =
        rhoLocal g (generatedAxisGlobalTwelveRepresentative i))
    (hneg : ∃ i : Fin 12, ∃ g : H,
      sExtra⁻¹ (rhoLocal generatedAxisGlobalTwelveEighthBindCoset15 generatedEighthAxis) =
        rhoLocal g (generatedAxisGlobalTwelveRepresentative i)) :
    GeneratedAxisGlobalTwelveEighthRootBound 15 :=
  eighthBind_rootBound_of_ids 15 [] (by decide)
    generatedAxisGlobalTwelveEighthBindWord15 (by decide) [14, 13, 5, 12]
    (by decide +kernel) hpos hneg

/-- Eighth root 16 from the identifications of both triality images at its coset. -/
theorem generatedAxisGlobalTwelveEighthBind_root16
    (hpos : ∃ i : Fin 12, ∃ g : H,
      sExtra (rhoLocal generatedAxisGlobalTwelveEighthBindCoset16 generatedEighthAxis) =
        rhoLocal g (generatedAxisGlobalTwelveRepresentative i))
    (hneg : ∃ i : Fin 12, ∃ g : H,
      sExtra⁻¹ (rhoLocal generatedAxisGlobalTwelveEighthBindCoset16 generatedEighthAxis) =
        rhoLocal g (generatedAxisGlobalTwelveRepresentative i)) :
    GeneratedAxisGlobalTwelveEighthRootBound 16 :=
  eighthBind_rootBound_of_ids 16 [] (by decide)
    generatedAxisGlobalTwelveEighthBindWord16 (by decide) [12, 12, 3, 12, 14, 12]
    (by decide +kernel) hpos hneg

/-- Eighth root 17 from the identifications of both triality images at its coset. -/
theorem generatedAxisGlobalTwelveEighthBind_root17
    (hpos : ∃ i : Fin 12, ∃ g : H,
      sExtra (rhoLocal generatedAxisGlobalTwelveEighthBindCoset17 generatedEighthAxis) =
        rhoLocal g (generatedAxisGlobalTwelveRepresentative i))
    (hneg : ∃ i : Fin 12, ∃ g : H,
      sExtra⁻¹ (rhoLocal generatedAxisGlobalTwelveEighthBindCoset17 generatedEighthAxis) =
        rhoLocal g (generatedAxisGlobalTwelveRepresentative i)) :
    GeneratedAxisGlobalTwelveEighthRootBound 17 :=
  eighthBind_rootBound_of_ids 17 [] (by decide)
    generatedAxisGlobalTwelveEighthBindWord17 (by decide) [13, 15, 0, 15, 15]
    (by decide +kernel) hpos hneg

/-- Eighth root 18 through the Eighth-diagonal transport of root 12: the identifications of root
12 bind root 18 at the target coset. -/
theorem generatedAxisGlobalTwelveEighthBind_root18
    (htr : sExtra (rhoLocal generatedAxisGlobalTwelveEighthBindCoset12 generatedEighthAxis) =
      rhoLocal generatedAxisGlobalTwelveEighthBindCoset18 generatedEighthAxis)
    (hother : ∃ i : Fin 12, ∃ g : H,
      sExtra⁻¹ (rhoLocal generatedAxisGlobalTwelveEighthBindCoset12 generatedEighthAxis) =
        rhoLocal g (generatedAxisGlobalTwelveRepresentative i)) :
    GeneratedAxisGlobalTwelveEighthRootBound 18 := by
  obtain ⟨i, g, hg⟩ := hother
  exact eighthBind_rootBound_of_forward 18 generatedAxisGlobalTwelveEighthBindPre18 (by decide)
    generatedAxisGlobalTwelveEighthBindWord18 (by decide) [14, 13, 15, 0, 15, 12]
    (by decide +kernel) 7 generatedAxisGlobalTwelveEighthBindCoset12 htr
    (generatedAxisGlobalTwelve_mem_of_transport i g hg)

/-- Eighth root 19 from the Tenth transport T33+ (gtenth) and the identification of the
other image at its coset (record `E19@T33+` of goctad). -/
theorem generatedAxisGlobalTwelveEighthBind_root19 (x : H)
    (htr : sExtra (rhoLocal x (generatedAxisGlobalTwelveRepresentative 11)) =
      rhoLocal generatedAxisGlobalTwelveEighthBindCoset19 generatedEighthAxis)
    (hnew : ∃ i : Fin 12, ∃ g : H,
      sExtra (rhoLocal generatedAxisGlobalTwelveEighthBindCoset19 generatedEighthAxis) =
        rhoLocal g (generatedAxisGlobalTwelveRepresentative i)) :
    GeneratedAxisGlobalTwelveEighthRootBound 19 := by
  have hknown : ∃ i : Fin 12, ∃ g : H,
      sExtra⁻¹ (rhoLocal generatedAxisGlobalTwelveEighthBindCoset19 generatedEighthAxis) =
        rhoLocal g (generatedAxisGlobalTwelveRepresentative i) := by
    refine ⟨11, x, ?_⟩
    rw [← htr, LinearEquiv.coe_inv, LinearEquiv.symm_apply_apply]
  exact eighthBind_rootBound_of_ids 19 generatedAxisGlobalTwelveEighthBindPre19 (by decide)
    generatedAxisGlobalTwelveEighthBindWord19 (by decide) [15, 1, 15, 13, 14, 13, 14, 13]
    (by decide +kernel) hnew hknown

/-- Eighth root 20 from the two Tenth transports T39- and T39+ (gtenth) at one
Tenth coset `x`. -/
theorem generatedAxisGlobalTwelveEighthBind_root20 (x : H)
    (htr : sExtra⁻¹ (rhoLocal x (generatedAxisGlobalTwelveRepresentative 11)) =
      rhoLocal generatedAxisGlobalTwelveEighthBindCoset20 generatedEighthAxis)
    (hother : ∃ i : Fin 12, ∃ g : H,
      sExtra (rhoLocal x (generatedAxisGlobalTwelveRepresentative 11)) =
        rhoLocal g (generatedAxisGlobalTwelveRepresentative i)) :
    GeneratedAxisGlobalTwelveEighthRootBound 20 := by
  obtain ⟨i, g, hg⟩ := hother
  exact eighthBind_rootBound_of_inverse 20 generatedAxisGlobalTwelveEighthBindPre20 (by decide)
    generatedAxisGlobalTwelveEighthBindWord20 (by decide) [15, 15, 13, 14, 13, 14, 5, 12, 0]
    (by decide +kernel) 11 x htr
    (generatedAxisGlobalTwelve_mem_of_transport i g hg)

/-- Eighth root 21 from the identifications of both triality images at its coset. -/
theorem generatedAxisGlobalTwelveEighthBind_root21
    (hpos : ∃ i : Fin 12, ∃ g : H,
      sExtra (rhoLocal generatedAxisGlobalTwelveEighthBindCoset21 generatedEighthAxis) =
        rhoLocal g (generatedAxisGlobalTwelveRepresentative i))
    (hneg : ∃ i : Fin 12, ∃ g : H,
      sExtra⁻¹ (rhoLocal generatedAxisGlobalTwelveEighthBindCoset21 generatedEighthAxis) =
        rhoLocal g (generatedAxisGlobalTwelveRepresentative i)) :
    GeneratedAxisGlobalTwelveEighthRootBound 21 :=
  eighthBind_rootBound_of_ids 21 [] (by decide)
    generatedAxisGlobalTwelveEighthBindWord21 (by decide) [7, 15, 15, 15, 13, 2]
    (by decide +kernel) hpos hneg

/-- Eighth root 22 from the identifications of both triality images at its coset. -/
theorem generatedAxisGlobalTwelveEighthBind_root22
    (hpos : ∃ i : Fin 12, ∃ g : H,
      sExtra (rhoLocal generatedAxisGlobalTwelveEighthBindCoset22 generatedEighthAxis) =
        rhoLocal g (generatedAxisGlobalTwelveRepresentative i))
    (hneg : ∃ i : Fin 12, ∃ g : H,
      sExtra⁻¹ (rhoLocal generatedAxisGlobalTwelveEighthBindCoset22 generatedEighthAxis) =
        rhoLocal g (generatedAxisGlobalTwelveRepresentative i)) :
    GeneratedAxisGlobalTwelveEighthRootBound 22 :=
  eighthBind_rootBound_of_ids 22 [] (by decide)
    generatedAxisGlobalTwelveEighthBindWord22 (by decide) [14, 14, 4, 12, 14]
    (by decide +kernel) hpos hneg

/-- Eighth root 23 from the identifications of both triality images at its coset. -/
theorem generatedAxisGlobalTwelveEighthBind_root23
    (hpos : ∃ i : Fin 12, ∃ g : H,
      sExtra (rhoLocal generatedAxisGlobalTwelveEighthBindCoset23 generatedEighthAxis) =
        rhoLocal g (generatedAxisGlobalTwelveRepresentative i))
    (hneg : ∃ i : Fin 12, ∃ g : H,
      sExtra⁻¹ (rhoLocal generatedAxisGlobalTwelveEighthBindCoset23 generatedEighthAxis) =
        rhoLocal g (generatedAxisGlobalTwelveRepresentative i)) :
    GeneratedAxisGlobalTwelveEighthRootBound 23 :=
  eighthBind_rootBound_of_ids 23 [] (by decide)
    generatedAxisGlobalTwelveEighthBindWord23 (by decide) [15, 13, 6, 15, 0]
    (by decide +kernel) hpos hneg

/-- Eighth root 24 from the identifications of both triality images at its coset. -/
theorem generatedAxisGlobalTwelveEighthBind_root24
    (hpos : ∃ i : Fin 12, ∃ g : H,
      sExtra (rhoLocal generatedAxisGlobalTwelveEighthBindCoset24 generatedEighthAxis) =
        rhoLocal g (generatedAxisGlobalTwelveRepresentative i))
    (hneg : ∃ i : Fin 12, ∃ g : H,
      sExtra⁻¹ (rhoLocal generatedAxisGlobalTwelveEighthBindCoset24 generatedEighthAxis) =
        rhoLocal g (generatedAxisGlobalTwelveRepresentative i)) :
    GeneratedAxisGlobalTwelveEighthRootBound 24 :=
  eighthBind_rootBound_of_ids 24 [] (by decide)
    generatedAxisGlobalTwelveEighthBindWord24 (by decide) [12, 15, 12, 0]
    (by decide +kernel) hpos hneg

/-- Eighth root 25 from the identifications of both triality images at its coset. -/
theorem generatedAxisGlobalTwelveEighthBind_root25
    (hpos : ∃ i : Fin 12, ∃ g : H,
      sExtra (rhoLocal generatedAxisGlobalTwelveEighthBindCoset25 generatedEighthAxis) =
        rhoLocal g (generatedAxisGlobalTwelveRepresentative i))
    (hneg : ∃ i : Fin 12, ∃ g : H,
      sExtra⁻¹ (rhoLocal generatedAxisGlobalTwelveEighthBindCoset25 generatedEighthAxis) =
        rhoLocal g (generatedAxisGlobalTwelveRepresentative i)) :
    GeneratedAxisGlobalTwelveEighthRootBound 25 :=
  eighthBind_rootBound_of_ids 25 [] (by decide)
    generatedAxisGlobalTwelveEighthBindWord25 (by decide) [14, 14, 14, 12, 0]
    (by decide +kernel) hpos hneg

/-- Eighth root 26 from the identifications of both triality images at its coset. -/
theorem generatedAxisGlobalTwelveEighthBind_root26
    (hpos : ∃ i : Fin 12, ∃ g : H,
      sExtra (rhoLocal generatedAxisGlobalTwelveEighthBindCoset26 generatedEighthAxis) =
        rhoLocal g (generatedAxisGlobalTwelveRepresentative i))
    (hneg : ∃ i : Fin 12, ∃ g : H,
      sExtra⁻¹ (rhoLocal generatedAxisGlobalTwelveEighthBindCoset26 generatedEighthAxis) =
        rhoLocal g (generatedAxisGlobalTwelveRepresentative i)) :
    GeneratedAxisGlobalTwelveEighthRootBound 26 :=
  eighthBind_rootBound_of_ids 26 [] (by decide)
    generatedAxisGlobalTwelveEighthBindWord26 (by decide) [12, 15, 15, 15, 0]
    (by decide +kernel) hpos hneg

/-- Eighth root 27 from the identifications of both triality images at its coset. -/
theorem generatedAxisGlobalTwelveEighthBind_root27
    (hpos : ∃ i : Fin 12, ∃ g : H,
      sExtra (rhoLocal generatedAxisGlobalTwelveEighthBindCoset27 generatedEighthAxis) =
        rhoLocal g (generatedAxisGlobalTwelveRepresentative i))
    (hneg : ∃ i : Fin 12, ∃ g : H,
      sExtra⁻¹ (rhoLocal generatedAxisGlobalTwelveEighthBindCoset27 generatedEighthAxis) =
        rhoLocal g (generatedAxisGlobalTwelveRepresentative i)) :
    GeneratedAxisGlobalTwelveEighthRootBound 27 :=
  eighthBind_rootBound_of_ids 27 [] (by decide)
    generatedAxisGlobalTwelveEighthBindWord27 (by decide) [13, 15, 13, 14, 13, 2]
    (by decide +kernel) hpos hneg

/-- Eighth root 28 from the identifications of both triality images at its coset. -/
theorem generatedAxisGlobalTwelveEighthBind_root28
    (hpos : ∃ i : Fin 12, ∃ g : H,
      sExtra (rhoLocal generatedAxisGlobalTwelveEighthBindCoset28 generatedEighthAxis) =
        rhoLocal g (generatedAxisGlobalTwelveRepresentative i))
    (hneg : ∃ i : Fin 12, ∃ g : H,
      sExtra⁻¹ (rhoLocal generatedAxisGlobalTwelveEighthBindCoset28 generatedEighthAxis) =
        rhoLocal g (generatedAxisGlobalTwelveRepresentative i)) :
    GeneratedAxisGlobalTwelveEighthRootBound 28 :=
  eighthBind_rootBound_of_ids 28 [] (by decide)
    generatedAxisGlobalTwelveEighthBindWord28 (by decide) [12, 14, 14, 12, 0]
    (by decide +kernel) hpos hneg

/-- Eighth root 29 from the identifications of both triality images at its coset. -/
theorem generatedAxisGlobalTwelveEighthBind_root29
    (hpos : ∃ i : Fin 12, ∃ g : H,
      sExtra (rhoLocal generatedAxisGlobalTwelveEighthBindCoset29 generatedEighthAxis) =
        rhoLocal g (generatedAxisGlobalTwelveRepresentative i))
    (hneg : ∃ i : Fin 12, ∃ g : H,
      sExtra⁻¹ (rhoLocal generatedAxisGlobalTwelveEighthBindCoset29 generatedEighthAxis) =
        rhoLocal g (generatedAxisGlobalTwelveRepresentative i)) :
    GeneratedAxisGlobalTwelveEighthRootBound 29 :=
  eighthBind_rootBound_of_ids 29 [] (by decide)
    generatedAxisGlobalTwelveEighthBindWord29 (by decide) [12, 7, 14, 14, 14, 4, 14]
    (by decide +kernel) hpos hneg

/-- Eighth root 30 through the Eighth-diagonal transport of root 11: the identifications of root
11 bind root 30 at the target coset. -/
theorem generatedAxisGlobalTwelveEighthBind_root30
    (htr : sExtra (rhoLocal generatedAxisGlobalTwelveEighthBindCoset11 generatedEighthAxis) =
      rhoLocal generatedAxisGlobalTwelveEighthBindCoset30 generatedEighthAxis)
    (hother : ∃ i : Fin 12, ∃ g : H,
      sExtra⁻¹ (rhoLocal generatedAxisGlobalTwelveEighthBindCoset11 generatedEighthAxis) =
        rhoLocal g (generatedAxisGlobalTwelveRepresentative i)) :
    GeneratedAxisGlobalTwelveEighthRootBound 30 := by
  obtain ⟨i, g, hg⟩ := hother
  exact eighthBind_rootBound_of_forward 30 generatedAxisGlobalTwelveEighthBindPre30 (by decide)
    generatedAxisGlobalTwelveEighthBindWord30 (by decide) [0, 15, 12, 12, 15, 3, 0]
    (by decide +kernel) 7 generatedAxisGlobalTwelveEighthBindCoset11 htr
    (generatedAxisGlobalTwelve_mem_of_transport i g hg)

/-- Eighth root 31 from the two Tenth transports T35+ and T35- (gtenth) at one
Tenth coset `x`. -/
theorem generatedAxisGlobalTwelveEighthBind_root31 (x : H)
    (htr : sExtra (rhoLocal x (generatedAxisGlobalTwelveRepresentative 11)) =
      rhoLocal generatedAxisGlobalTwelveEighthBindCoset31 generatedEighthAxis)
    (hother : ∃ i : Fin 12, ∃ g : H,
      sExtra⁻¹ (rhoLocal x (generatedAxisGlobalTwelveRepresentative 11)) =
        rhoLocal g (generatedAxisGlobalTwelveRepresentative i)) :
    GeneratedAxisGlobalTwelveEighthRootBound 31 := by
  obtain ⟨i, g, hg⟩ := hother
  exact eighthBind_rootBound_of_forward 31 generatedAxisGlobalTwelveEighthBindPre31 (by decide)
    generatedAxisGlobalTwelveEighthBindWord31 (by decide) [13, 14, 10, 12, 15, 13, 13]
    (by decide +kernel) 11 x htr
    (generatedAxisGlobalTwelve_mem_of_transport i g hg)

/-- Eighth root 32 from the two Tenth transports T16- and T16+ (gtenth) at one
Tenth coset `x`. -/
theorem generatedAxisGlobalTwelveEighthBind_root32 (x : H)
    (htr : sExtra⁻¹ (rhoLocal x (generatedAxisGlobalTwelveRepresentative 11)) =
      rhoLocal generatedAxisGlobalTwelveEighthBindCoset32 generatedEighthAxis)
    (hother : ∃ i : Fin 12, ∃ g : H,
      sExtra (rhoLocal x (generatedAxisGlobalTwelveRepresentative 11)) =
        rhoLocal g (generatedAxisGlobalTwelveRepresentative i)) :
    GeneratedAxisGlobalTwelveEighthRootBound 32 := by
  obtain ⟨i, g, hg⟩ := hother
  exact eighthBind_rootBound_of_inverse 32 generatedAxisGlobalTwelveEighthBindPre32 (by decide)
    generatedAxisGlobalTwelveEighthBindWord32 (by decide) [13, 14, 4, 1, 13]
    (by decide +kernel) 11 x htr
    (generatedAxisGlobalTwelve_mem_of_transport i g hg)

/-- Eighth root 33 from the Tenth transport T32+ (gtenth) and the identification of the
other image at its coset (record `E33@T32+` of goctad). -/
theorem generatedAxisGlobalTwelveEighthBind_root33 (x : H)
    (htr : sExtra (rhoLocal x (generatedAxisGlobalTwelveRepresentative 11)) =
      rhoLocal generatedAxisGlobalTwelveEighthBindCoset33 generatedEighthAxis)
    (hnew : ∃ i : Fin 12, ∃ g : H,
      sExtra (rhoLocal generatedAxisGlobalTwelveEighthBindCoset33 generatedEighthAxis) =
        rhoLocal g (generatedAxisGlobalTwelveRepresentative i)) :
    GeneratedAxisGlobalTwelveEighthRootBound 33 := by
  have hknown : ∃ i : Fin 12, ∃ g : H,
      sExtra⁻¹ (rhoLocal generatedAxisGlobalTwelveEighthBindCoset33 generatedEighthAxis) =
        rhoLocal g (generatedAxisGlobalTwelveRepresentative i) := by
    refine ⟨11, x, ?_⟩
    rw [← htr, LinearEquiv.coe_inv, LinearEquiv.symm_apply_apply]
  exact eighthBind_rootBound_of_ids 33 generatedAxisGlobalTwelveEighthBindPre33 (by decide)
    generatedAxisGlobalTwelveEighthBindWord33 (by decide) [6, 0, 15, 13, 1]
    (by decide +kernel) hnew hknown

/-- Eighth root 34 from the Tenth transport T21- (gtenth) and the identification of the
other image at its coset (record `E34@T21-` of goctad). -/
theorem generatedAxisGlobalTwelveEighthBind_root34 (x : H)
    (htr : sExtra⁻¹ (rhoLocal x (generatedAxisGlobalTwelveRepresentative 11)) =
      rhoLocal generatedAxisGlobalTwelveEighthBindCoset34 generatedEighthAxis)
    (hnew : ∃ i : Fin 12, ∃ g : H,
      sExtra⁻¹ (rhoLocal generatedAxisGlobalTwelveEighthBindCoset34 generatedEighthAxis) =
        rhoLocal g (generatedAxisGlobalTwelveRepresentative i)) :
    GeneratedAxisGlobalTwelveEighthRootBound 34 := by
  have hknown : ∃ i : Fin 12, ∃ g : H,
      sExtra (rhoLocal generatedAxisGlobalTwelveEighthBindCoset34 generatedEighthAxis) =
        rhoLocal g (generatedAxisGlobalTwelveRepresentative i) := by
    refine ⟨11, x, ?_⟩
    rw [← htr, LinearEquiv.coe_inv, LinearEquiv.apply_symm_apply]
  exact eighthBind_rootBound_of_ids 34 generatedAxisGlobalTwelveEighthBindPre34 (by decide)
    generatedAxisGlobalTwelveEighthBindWord34 (by decide) [3]
    (by decide +kernel) hknown hnew

/-- Eighth root 35 from the identifications of both triality images at its coset. -/
theorem generatedAxisGlobalTwelveEighthBind_root35
    (hpos : ∃ i : Fin 12, ∃ g : H,
      sExtra (rhoLocal generatedAxisGlobalTwelveEighthBindCoset35 generatedEighthAxis) =
        rhoLocal g (generatedAxisGlobalTwelveRepresentative i))
    (hneg : ∃ i : Fin 12, ∃ g : H,
      sExtra⁻¹ (rhoLocal generatedAxisGlobalTwelveEighthBindCoset35 generatedEighthAxis) =
        rhoLocal g (generatedAxisGlobalTwelveRepresentative i)) :
    GeneratedAxisGlobalTwelveEighthRootBound 35 :=
  eighthBind_rootBound_of_ids 35 [] (by decide)
    generatedAxisGlobalTwelveEighthBindWord35 (by decide) [10, 4, 2, 1, 0]
    (by decide +kernel) hpos hneg

/-- Eighth root 36 from the two Tenth transports T31+ and T31- (gtenth) at one
Tenth coset `x`. -/
theorem generatedAxisGlobalTwelveEighthBind_root36 (x : H)
    (htr : sExtra (rhoLocal x (generatedAxisGlobalTwelveRepresentative 11)) =
      rhoLocal generatedAxisGlobalTwelveEighthBindCoset36 generatedEighthAxis)
    (hother : ∃ i : Fin 12, ∃ g : H,
      sExtra⁻¹ (rhoLocal x (generatedAxisGlobalTwelveRepresentative 11)) =
        rhoLocal g (generatedAxisGlobalTwelveRepresentative i)) :
    GeneratedAxisGlobalTwelveEighthRootBound 36 := by
  obtain ⟨i, g, hg⟩ := hother
  exact eighthBind_rootBound_of_forward 36 generatedAxisGlobalTwelveEighthBindPre36 (by decide)
    generatedAxisGlobalTwelveEighthBindWord36 (by decide) [1, 15, 12, 14, 13, 6]
    (by decide +kernel) 11 x htr
    (generatedAxisGlobalTwelve_mem_of_transport i g hg)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

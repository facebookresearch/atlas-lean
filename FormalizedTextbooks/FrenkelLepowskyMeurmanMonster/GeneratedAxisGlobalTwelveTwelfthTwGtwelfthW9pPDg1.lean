/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTwelfthTwGtwelfthW9pChecks
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWBase
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWSelfOct
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamTwelfthS
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWOddDistinct

/-! # Factory odd part (group 1) of the identification Twelfth[9]+ <-> Twelfth[21]- (record
gtwelfth:W9+, e = 1)

Dense target: the odd part of the pairing is evaluated in groups of target terms and the odd self
part as a sum of squares (distinct odd labels). -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
open GeneratedAxisGlobalTwelveTwelfthIdent
set_option autoImplicit false
set_option Elab.async false

/-- Group 1 of the chunks of the target list. -/
def twGtwelfthW9pGTg1 : List (ℕ × ℤ) :=
  decodeTerms twGtwelfthW9pGT8Labs twGtwelfthW9pGT8Nums 2048 ++
    (decodeTerms twGtwelfthW9pGT9Labs twGtwelfthW9pGT9Nums 2048 ++
    (decodeTerms twGtwelfthW9pGT10Labs twGtwelfthW9pGT10Nums 2048 ++
    (decodeTerms twGtwelfthW9pGT11Labs twGtwelfthW9pGT11Nums 2048 ++
    (decodeTerms twGtwelfthW9pGT12Labs twGtwelfthW9pGT12Nums 2048 ++
    (decodeTerms twGtwelfthW9pGT13Labs twGtwelfthW9pGT13Nums 2048 ++
    (decodeTerms twGtwelfthW9pGT14Labs twGtwelfthW9pGT14Nums 2048 ++
    (decodeTerms twGtwelfthW9pGT15Labs twGtwelfthW9pGT15Nums 2048)))))))

set_option maxRecDepth 100000 in
/-- The odd part of the pairing over group 1 of the target terms. -/
theorem twGtwelfthW9p_og1 : oddSumF 80 true twGtwelfthW9pHX twGtwelfthW9pGTg1 = 383778816 := by
  decide +kernel

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

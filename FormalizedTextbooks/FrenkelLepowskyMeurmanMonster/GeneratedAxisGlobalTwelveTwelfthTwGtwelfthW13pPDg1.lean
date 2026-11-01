/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTwelfthTwGtwelfthW13pChecks
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWBase
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWSelfOct
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamTwelfthS
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWOddDistinct

/-! # Factory odd part (group 1) of the identification Twelfth[13]- <-> Twelfth[13]+ (record
gtwelfth:W13+, e = 1)

Dense target: the odd part of the pairing is evaluated in groups of target terms and the odd self
part as a sum of squares (distinct odd labels). -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
open GeneratedAxisGlobalTwelveTwelfthIdent
set_option autoImplicit false
set_option Elab.async false

/-- Group 1 of the chunks of the target list. -/
def twGtwelfthW13pGTg1 : List (ℕ × ℤ) :=
  decodeTerms twGtwelfthW13pGT8Labs twGtwelfthW13pGT8Nums 2048 ++
    (decodeTerms twGtwelfthW13pGT9Labs twGtwelfthW13pGT9Nums 2048 ++
    (decodeTerms twGtwelfthW13pGT10Labs twGtwelfthW13pGT10Nums 2048 ++
    (decodeTerms twGtwelfthW13pGT11Labs twGtwelfthW13pGT11Nums 2048 ++
    (decodeTerms twGtwelfthW13pGT12Labs twGtwelfthW13pGT12Nums 2048 ++
    (decodeTerms twGtwelfthW13pGT13Labs twGtwelfthW13pGT13Nums 2048 ++
    (decodeTerms twGtwelfthW13pGT14Labs twGtwelfthW13pGT14Nums 2048 ++
    (decodeTerms twGtwelfthW13pGT15Labs twGtwelfthW13pGT15Nums 2048)))))))

set_option maxRecDepth 100000 in
/-- The odd part of the pairing over group 1 of the target terms. -/
theorem twGtwelfthW13p_og1 : oddSumF 80 true twGtwelfthW13pHX twGtwelfthW13pGTg1 = 379584512 := by
  decide +kernel

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTwelfthTwGtwelfthW21pChecks
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWBase
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWSelfOct
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamTwelfthS
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWOddDistinct

/-! # Factory odd part (group 1) of the identification Twelfth[9]+ <-> Twelfth[21]+ (record
gtwelfth:W21+, e = 1)

Dense target: the odd part of the pairing is evaluated in groups of target terms and the odd self
part as a sum of squares (distinct odd labels). -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
open GeneratedAxisGlobalTwelveTwelfthIdent
set_option autoImplicit false
set_option Elab.async false

/-- Group 1 of the chunks of the target list. -/
def twGtwelfthW21pGTg1 : List (ℕ × ℤ) :=
  decodeTerms twGtwelfthW21pGT8Labs twGtwelfthW21pGT8Nums 2048 ++
    (decodeTerms twGtwelfthW21pGT9Labs twGtwelfthW21pGT9Nums 2048 ++
    (decodeTerms twGtwelfthW21pGT10Labs twGtwelfthW21pGT10Nums 2048 ++
    (decodeTerms twGtwelfthW21pGT11Labs twGtwelfthW21pGT11Nums 2048 ++
    (decodeTerms twGtwelfthW21pGT12Labs twGtwelfthW21pGT12Nums 2048 ++
    (decodeTerms twGtwelfthW21pGT13Labs twGtwelfthW21pGT13Nums 2048 ++
    (decodeTerms twGtwelfthW21pGT14Labs twGtwelfthW21pGT14Nums 2048 ++
    (decodeTerms twGtwelfthW21pGT15Labs twGtwelfthW21pGT15Nums 2048)))))))

set_option maxRecDepth 100000 in
/-- The odd part of the pairing over group 1 of the target terms. -/
theorem twGtwelfthW21p_og1 : oddSumF 80 true twGtwelfthW21pHX twGtwelfthW21pGTg1 = 380108800 := by
  decide +kernel

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

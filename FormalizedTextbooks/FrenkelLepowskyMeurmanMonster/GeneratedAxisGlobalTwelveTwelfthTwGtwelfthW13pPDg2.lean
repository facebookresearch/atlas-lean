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

/-! # Factory odd part (group 2) of the identification Twelfth[13]- <-> Twelfth[13]+ (record
gtwelfth:W13+, e = 1)

Dense target: the odd part of the pairing is evaluated in groups of target terms and the odd self
part as a sum of squares (distinct odd labels). -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
open GeneratedAxisGlobalTwelveTwelfthIdent
set_option autoImplicit false
set_option Elab.async false

/-- Group 2 of the chunks of the target list. -/
def twGtwelfthW13pGTg2 : List (ℕ × ℤ) :=
  decodeTerms twGtwelfthW13pGT16Labs twGtwelfthW13pGT16Nums 2048 ++
    (decodeTerms twGtwelfthW13pGT17Labs twGtwelfthW13pGT17Nums 2048 ++
    (decodeTerms twGtwelfthW13pGT18Labs twGtwelfthW13pGT18Nums 2048 ++
    (decodeTerms twGtwelfthW13pGT19Labs twGtwelfthW13pGT19Nums 2048 ++
    (decodeTerms twGtwelfthW13pGT20Labs twGtwelfthW13pGT20Nums 2048 ++
    (decodeTerms twGtwelfthW13pGT21Labs twGtwelfthW13pGT21Nums 2048 ++
    (decodeTerms twGtwelfthW13pGT22Labs twGtwelfthW13pGT22Nums 1704))))))

set_option maxRecDepth 100000 in
/-- The odd part of the pairing over group 2 of the target terms. -/
theorem twGtwelfthW13p_og2 : oddSumF 80 true twGtwelfthW13pHX twGtwelfthW13pGTg2 = 296353792 := by
  decide +kernel

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

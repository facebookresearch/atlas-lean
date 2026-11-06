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

/-! # Factory odd part (group 2) of the identification Twelfth[9]+ <-> Twelfth[21]+ (record
gtwelfth:W21+, e = 1)

Dense target: the odd part of the pairing is evaluated in groups of target terms and the odd self
part as a sum of squares (distinct odd labels). -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
open GeneratedAxisGlobalTwelveTwelfthIdent
set_option autoImplicit false
set_option Elab.async false

/-- Group 2 of the chunks of the target list. -/
def twGtwelfthW21pGTg2 : List (ℕ × ℤ) :=
  decodeTerms twGtwelfthW21pGT16Labs twGtwelfthW21pGT16Nums 2048 ++
    (decodeTerms twGtwelfthW21pGT17Labs twGtwelfthW21pGT17Nums 2048 ++
    (decodeTerms twGtwelfthW21pGT18Labs twGtwelfthW21pGT18Nums 2048 ++
    (decodeTerms twGtwelfthW21pGT19Labs twGtwelfthW21pGT19Nums 2048 ++
    (decodeTerms twGtwelfthW21pGT20Labs twGtwelfthW21pGT20Nums 2048 ++
    (decodeTerms twGtwelfthW21pGT21Labs twGtwelfthW21pGT21Nums 2048 ++
    (decodeTerms twGtwelfthW21pGT22Labs twGtwelfthW21pGT22Nums 1704))))))

set_option maxRecDepth 100000 in
/-- The odd part of the pairing over group 2 of the target terms. -/
theorem twGtwelfthW21p_og2 : oddSumF 80 true twGtwelfthW21pHX twGtwelfthW21pGTg2 = 296353792 := by
  decide +kernel

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

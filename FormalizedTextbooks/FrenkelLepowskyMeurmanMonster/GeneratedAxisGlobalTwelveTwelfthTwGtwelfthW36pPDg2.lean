/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTwelfthTwGtwelfthW36pChecks
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWBase
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWSelfOct
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamTwelfthS
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWOddDistinct

/-! # Factory odd part (group 2) of the identification Twelfth[36]+ <-> Twelfth[36]+ (record
gtwelfth:W36+, e = 1)

Dense target: the odd part of the pairing is evaluated in groups of target terms and the odd self
part as a sum of squares (distinct odd labels). -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
open GeneratedAxisGlobalTwelveTwelfthIdent
set_option autoImplicit false
set_option Elab.async false

/-- Group 2 of the chunks of the target list. -/
def twGtwelfthW36pGTg2 : List (ℕ × ℤ) :=
  decodeTerms twGtwelfthW36pGT16Labs twGtwelfthW36pGT16Nums 2048 ++
    (decodeTerms twGtwelfthW36pGT17Labs twGtwelfthW36pGT17Nums 2048 ++
    (decodeTerms twGtwelfthW36pGT18Labs twGtwelfthW36pGT18Nums 2048 ++
    (decodeTerms twGtwelfthW36pGT19Labs twGtwelfthW36pGT19Nums 2048 ++
    (decodeTerms twGtwelfthW36pGT20Labs twGtwelfthW36pGT20Nums 2048 ++
    (decodeTerms twGtwelfthW36pGT21Labs twGtwelfthW36pGT21Nums 2048 ++
    (decodeTerms twGtwelfthW36pGT22Labs twGtwelfthW36pGT22Nums 1704))))))

set_option maxRecDepth 100000 in
/-- The odd part of the pairing over group 2 of the target terms. -/
theorem twGtwelfthW36p_og2 : oddSumF 64 true twGtwelfthW36pHX twGtwelfthW36pGTg2 = 18522112 := by
  decide +kernel

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

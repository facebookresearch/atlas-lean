/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWR8fR81pChecks
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWBase
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWSelfOct
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamRootEightM
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamTwelfthS
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWOddDistinct

/-! # Factory odd part (group 2) of the identification Root8[16]+ <-> Twelfth[24]+ (record
r8f:R81+, e = 1)

Dense target: the odd part of the pairing is evaluated in groups of target terms and the odd self
part as a sum of squares (distinct odd labels). -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
open GeneratedAxisGlobalTwelveTwelfthIdent
set_option autoImplicit false
set_option Elab.async false

/-- Group 2 of the chunks of the target list. -/
def wR8fR81pGTg2 : List (ℕ × ℤ) :=
  decodeTerms wR8fR81pGT16Labs wR8fR81pGT16Nums 2048 ++
    (decodeTerms wR8fR81pGT17Labs wR8fR81pGT17Nums 2048 ++
    (decodeTerms wR8fR81pGT18Labs wR8fR81pGT18Nums 2048 ++
    (decodeTerms wR8fR81pGT19Labs wR8fR81pGT19Nums 2048 ++
    (decodeTerms wR8fR81pGT20Labs wR8fR81pGT20Nums 2048 ++
    (decodeTerms wR8fR81pGT21Labs wR8fR81pGT21Nums 2048 ++
    (decodeTerms wR8fR81pGT22Labs wR8fR81pGT22Nums 1704))))))

set_option maxRecDepth 100000 in
/-- The odd part of the pairing over group 2 of the target terms. -/
theorem wR8fR81p_og2 : oddSumF 112 true wR8fR81pHX wR8fR81pGTg2 = 296353792 := by
  decide +kernel

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

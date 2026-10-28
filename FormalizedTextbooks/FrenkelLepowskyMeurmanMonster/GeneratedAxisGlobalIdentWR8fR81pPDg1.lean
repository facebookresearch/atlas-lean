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

/-! # Factory odd part (group 1) of the identification Root8[16]+ <-> Twelfth[24]+ (record
r8f:R81+, e = 1)

Dense target: the odd part of the pairing is evaluated in groups of target terms and the odd self
part as a sum of squares (distinct odd labels). -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
open GeneratedAxisGlobalTwelveTwelfthIdent
set_option autoImplicit false
set_option Elab.async false

/-- Group 1 of the chunks of the target list. -/
def wR8fR81pGTg1 : List (ℕ × ℤ) :=
  decodeTerms wR8fR81pGT8Labs wR8fR81pGT8Nums 2048 ++
    (decodeTerms wR8fR81pGT9Labs wR8fR81pGT9Nums 2048 ++
    (decodeTerms wR8fR81pGT10Labs wR8fR81pGT10Nums 2048 ++
    (decodeTerms wR8fR81pGT11Labs wR8fR81pGT11Nums 2048 ++
    (decodeTerms wR8fR81pGT12Labs wR8fR81pGT12Nums 2048 ++
    (decodeTerms wR8fR81pGT13Labs wR8fR81pGT13Nums 2048 ++
    (decodeTerms wR8fR81pGT14Labs wR8fR81pGT14Nums 2048 ++
    (decodeTerms wR8fR81pGT15Labs wR8fR81pGT15Nums 2048)))))))

set_option maxRecDepth 100000 in
/-- The odd part of the pairing over group 1 of the target terms. -/
theorem wR8fR81p_og1 : oddSumF 112 true wR8fR81pHX wR8fR81pGTg1 = 377880576 := by
  decide +kernel

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

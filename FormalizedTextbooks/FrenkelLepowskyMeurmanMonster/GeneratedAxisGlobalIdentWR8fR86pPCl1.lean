/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWR8fR86pChecks
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWBase
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWSelfOct
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamRootEightM
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamTwelfthS
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWOddSplitL

/-! # Factory tensor part (odd source terms, group 1) of the identification Root8[12]+ <->
Twelfth[34]- (record r8f:R86+, e = 1)

Dense source or long words: the tensor part of the pairing is evaluated in parts. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
open GeneratedAxisGlobalTwelveTwelfthIdent
set_option autoImplicit false
set_option Elab.async false

/-- Group 1 of the chunks of the source list. -/
def wR8fR86pHTg1 : List (ℕ × ℤ) :=
  decodeTerms wR8fR86pHT8Labs wR8fR86pHT8Nums 2048 ++
    (decodeTerms wR8fR86pHT9Labs wR8fR86pHT9Nums 2048 ++
    (decodeTerms wR8fR86pHT10Labs wR8fR86pHT10Nums 2048 ++
    (decodeTerms wR8fR86pHT11Labs wR8fR86pHT11Nums 2048 ++
    (decodeTerms wR8fR86pHT12Labs wR8fR86pHT12Nums 2048 ++
    (decodeTerms wR8fR86pHT13Labs wR8fR86pHT13Nums 2048 ++
    (decodeTerms wR8fR86pHT14Labs wR8fR86pHT14Nums 2048 ++
    (decodeTerms wR8fR86pHT15Labs wR8fR86pHT15Nums 2048)))))))

set_option maxRecDepth 100000 in
/-- The odd part of the tensor pairing over group 1 of the source terms. -/
theorem wR8fR86p_ol1 : oddSumL 96 true wR8fR86pGX wR8fR86pHTg1 = 1122369536 := by
  decide +kernel

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

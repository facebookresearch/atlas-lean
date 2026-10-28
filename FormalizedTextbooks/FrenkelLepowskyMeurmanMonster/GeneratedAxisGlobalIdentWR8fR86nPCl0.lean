/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWR8fR86nChecks
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWBase
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWSelfOct
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamRootEightM
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamTwelfthS
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWOddSplitL

/-! # Factory tensor part (odd source terms, group 0) of the identification Root8[12]- <->
Twelfth[34]- (record r8f:R86-, e = -1)

Dense source or long words: the tensor part of the pairing is evaluated in parts. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
open GeneratedAxisGlobalTwelveTwelfthIdent
set_option autoImplicit false
set_option Elab.async false

/-- Group 0 of the chunks of the source list. -/
def wR8fR86nHTg0 : List (ℕ × ℤ) :=
  decodeTerms wR8fR86nHT0Labs wR8fR86nHT0Nums 2048 ++
    (decodeTerms wR8fR86nHT1Labs wR8fR86nHT1Nums 2048 ++
    (decodeTerms wR8fR86nHT2Labs wR8fR86nHT2Nums 2048 ++
    (decodeTerms wR8fR86nHT3Labs wR8fR86nHT3Nums 2048 ++
    (decodeTerms wR8fR86nHT4Labs wR8fR86nHT4Nums 2048 ++
    (decodeTerms wR8fR86nHT5Labs wR8fR86nHT5Nums 2048 ++
    (decodeTerms wR8fR86nHT6Labs wR8fR86nHT6Nums 2048 ++
    (decodeTerms wR8fR86nHT7Labs wR8fR86nHT7Nums 2048)))))))

set_option maxRecDepth 100000 in
/-- The odd part of the tensor pairing over group 0 of the source terms. -/
theorem wR8fR86n_ol0 : oddSumL 96 false wR8fR86nGX wR8fR86nHTg0 = 918552576 := by
  decide +kernel

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

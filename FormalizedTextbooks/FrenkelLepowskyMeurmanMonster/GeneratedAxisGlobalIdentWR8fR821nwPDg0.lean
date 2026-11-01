/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWR8fR821nwChecks
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWBase
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWSelfOct
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamRootEightM
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWOddDistinct

/-! # Factory odd part (group 0) of the identification Root8[33]- <-> Root8[33]- (record
r8f:R821-, e = -1)

Dense target: the odd part of the pairing is evaluated in groups of target terms and the odd self
part as a sum of squares (distinct odd labels). -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

/-- Group 0 of the chunks of the target list. -/
def wR8fR821nwGTg0 : List (ℕ × ℤ) :=
  decodeTerms wR8fR821nwGT0Labs wR8fR821nwGT0Nums 2048 ++
    (decodeTerms wR8fR821nwGT1Labs wR8fR821nwGT1Nums 2048 ++
    (decodeTerms wR8fR821nwGT2Labs wR8fR821nwGT2Nums 2048 ++
    (decodeTerms wR8fR821nwGT3Labs wR8fR821nwGT3Nums 2048 ++
    (decodeTerms wR8fR821nwGT4Labs wR8fR821nwGT4Nums 2048 ++
    (decodeTerms wR8fR821nwGT5Labs wR8fR821nwGT5Nums 2048 ++
    (decodeTerms wR8fR821nwGT6Labs wR8fR821nwGT6Nums 2048 ++
    (decodeTerms wR8fR821nwGT7Labs wR8fR821nwGT7Nums 2048)))))))

set_option maxRecDepth 100000 in
/-- The odd part of the pairing over group 0 of the target terms. -/
theorem wR8fR821nw_og0 : oddSumF 96 false wR8fR821nwHX wR8fR821nwGTg0 = 914358272 := by
  decide +kernel

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

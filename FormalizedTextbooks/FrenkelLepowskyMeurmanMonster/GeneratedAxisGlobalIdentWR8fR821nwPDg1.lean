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

/-! # Factory odd part (group 1) of the identification Root8[33]- <-> Root8[33]- (record
r8f:R821-, e = -1)

Dense target: the odd part of the pairing is evaluated in groups of target terms and the odd self
part as a sum of squares (distinct odd labels). -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

/-- Group 1 of the chunks of the target list. -/
def wR8fR821nwGTg1 : List (ℕ × ℤ) :=
  decodeTerms wR8fR821nwGT8Labs wR8fR821nwGT8Nums 2048 ++
    (decodeTerms wR8fR821nwGT9Labs wR8fR821nwGT9Nums 2048 ++
    (decodeTerms wR8fR821nwGT10Labs wR8fR821nwGT10Nums 2048 ++
    (decodeTerms wR8fR821nwGT11Labs wR8fR821nwGT11Nums 2048 ++
    (decodeTerms wR8fR821nwGT12Labs wR8fR821nwGT12Nums 2048 ++
    (decodeTerms wR8fR821nwGT13Labs wR8fR821nwGT13Nums 2048 ++
    (decodeTerms wR8fR821nwGT14Labs wR8fR821nwGT14Nums 2048 ++
    (decodeTerms wR8fR821nwGT15Labs wR8fR821nwGT15Nums 2048)))))))

set_option maxRecDepth 100000 in
/-- The odd part of the pairing over group 1 of the target terms. -/
theorem wR8fR821nw_og1 : oddSumF 96 false wR8fR821nwHX wR8fR821nwGTg1 = 1061814272 := by
  decide +kernel

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

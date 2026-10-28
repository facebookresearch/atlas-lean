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
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWOddDistinct

/-! # Factory odd part (group 2) of the identification Root8[12]- <-> Twelfth[34]- (record
r8f:R86-, e = -1)

Dense target: the odd part of the pairing is evaluated in groups of target terms and the odd self
part as a sum of squares (distinct odd labels). -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
open GeneratedAxisGlobalTwelveTwelfthIdent
set_option autoImplicit false
set_option Elab.async false

/-- Group 2 of the chunks of the target list. -/
def wR8fR86nGTg2 : List (ℕ × ℤ) :=
  decodeTerms wR8fR86nGT16Labs wR8fR86nGT16Nums 2048 ++
    (decodeTerms wR8fR86nGT17Labs wR8fR86nGT17Nums 2048 ++
    (decodeTerms wR8fR86nGT18Labs wR8fR86nGT18Nums 2048 ++
    (decodeTerms wR8fR86nGT19Labs wR8fR86nGT19Nums 2048 ++
    (decodeTerms wR8fR86nGT20Labs wR8fR86nGT20Nums 2048 ++
    (decodeTerms wR8fR86nGT21Labs wR8fR86nGT21Nums 2048 ++
    (decodeTerms wR8fR86nGT22Labs wR8fR86nGT22Nums 1704))))))

set_option maxRecDepth 100000 in
/-- The odd part of the pairing over group 2 of the target terms. -/
theorem wR8fR86n_og2 : oddSumF 96 false wR8fR86nHX wR8fR86nGTg2 = 4741660672 := by
  decide +kernel

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

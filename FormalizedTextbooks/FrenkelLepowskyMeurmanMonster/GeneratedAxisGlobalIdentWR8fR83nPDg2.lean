/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWR8fR83nChecks
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWBase
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWSelfOct
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamRootEightM
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamTwelfthS
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWOddDistinct

/-! # Factory odd part (group 2) of the identification Root8[11]- <-> Twelfth[29]- (record
r8f:R83-, e = -1)

Dense target: the odd part of the pairing is evaluated in groups of target terms and the odd self
part as a sum of squares (distinct odd labels). -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
open GeneratedAxisGlobalTwelveTwelfthIdent
set_option autoImplicit false
set_option Elab.async false

/-- Group 2 of the chunks of the target list. -/
def wR8fR83nGTg2 : List (ℕ × ℤ) :=
  decodeTerms wR8fR83nGT16Labs wR8fR83nGT16Nums 2048 ++
    (decodeTerms wR8fR83nGT17Labs wR8fR83nGT17Nums 2048 ++
    (decodeTerms wR8fR83nGT18Labs wR8fR83nGT18Nums 2048 ++
    (decodeTerms wR8fR83nGT19Labs wR8fR83nGT19Nums 2048 ++
    (decodeTerms wR8fR83nGT20Labs wR8fR83nGT20Nums 2048 ++
    (decodeTerms wR8fR83nGT21Labs wR8fR83nGT21Nums 2048 ++
    (decodeTerms wR8fR83nGT22Labs wR8fR83nGT22Nums 1704))))))

set_option maxRecDepth 100000 in
/-- The odd part of the pairing over group 2 of the target terms. -/
theorem wR8fR83n_og2 : oddSumF 72 false wR8fR83nHX wR8fR83nGTg2 = 20176896 := by
  decide +kernel

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

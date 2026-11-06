/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGninthN1nChecks
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWBase
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWSelfOct
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamNinthM
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamTenthM
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWOddDistinct

/-! # Factory odd part (group 2) of the identification Ninth[1]- <-> Tenth[33]+ (record
gninth:N1-, e = -1)

Dense target: the odd part of the pairing is evaluated in groups of target terms and the odd self
part as a sum of squares (distinct odd labels). -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

/-- Group 2 of the chunks of the target list. -/
def wGninthN1nGTg2 : List (ℕ × ℤ) :=
  decodeTerms wGninthN1nGT16Labs wGninthN1nGT16Nums 2048 ++
    (decodeTerms wGninthN1nGT17Labs wGninthN1nGT17Nums 2048 ++
    (decodeTerms wGninthN1nGT18Labs wGninthN1nGT18Nums 2048 ++
    (decodeTerms wGninthN1nGT19Labs wGninthN1nGT19Nums 2048 ++
    (decodeTerms wGninthN1nGT20Labs wGninthN1nGT20Nums 2048 ++
    (decodeTerms wGninthN1nGT21Labs wGninthN1nGT21Nums 2048 ++
    (decodeTerms wGninthN1nGT22Labs wGninthN1nGT22Nums 1026))))))

set_option maxRecDepth 100000 in
/-- The odd part of the pairing over group 2 of the target terms. -/
theorem wGninthN1n_og2 : oddSumF 64 false wGninthN1nHX wGninthN1nGTg2 = 1234560 := by
  decide +kernel

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

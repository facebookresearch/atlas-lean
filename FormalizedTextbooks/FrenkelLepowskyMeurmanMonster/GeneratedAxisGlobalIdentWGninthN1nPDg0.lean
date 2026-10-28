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

/-! # Factory odd part (group 0) of the identification Ninth[1]- <-> Tenth[33]+ (record
gninth:N1-, e = -1)

Dense target: the odd part of the pairing is evaluated in groups of target terms and the odd self
part as a sum of squares (distinct odd labels). -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

/-- Group 0 of the chunks of the target list. -/
def wGninthN1nGTg0 : List (ℕ × ℤ) :=
  decodeTerms wGninthN1nGT0Labs wGninthN1nGT0Nums 2048 ++
    (decodeTerms wGninthN1nGT1Labs wGninthN1nGT1Nums 2048 ++
    (decodeTerms wGninthN1nGT2Labs wGninthN1nGT2Nums 2048 ++
    (decodeTerms wGninthN1nGT3Labs wGninthN1nGT3Nums 2048 ++
    (decodeTerms wGninthN1nGT4Labs wGninthN1nGT4Nums 2048 ++
    (decodeTerms wGninthN1nGT5Labs wGninthN1nGT5Nums 2048 ++
    (decodeTerms wGninthN1nGT6Labs wGninthN1nGT6Nums 2048 ++
    (decodeTerms wGninthN1nGT7Labs wGninthN1nGT7Nums 2048)))))))

set_option maxRecDepth 100000 in
/-- The odd part of the pairing over group 0 of the target terms. -/
theorem wGninthN1n_og0 : oddSumF 64 false wGninthN1nHX wGninthN1nGTg0 = 1425408 := by
  decide +kernel

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

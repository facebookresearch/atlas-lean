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
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWOddSplitL

/-! # Factory tensor part (odd source terms, group 0) of the identification Ninth[1]- <->
Tenth[33]+ (record gninth:N1-, e = -1)

Dense source or long words: the tensor part of the pairing is evaluated in parts. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

/-- Group 0 of the chunks of the source list. -/
def wGninthN1nHTg0 : List (ℕ × ℤ) :=
  decodeTerms wGninthN1nHT0Labs wGninthN1nHT0Nums 2048 ++
    (decodeTerms wGninthN1nHT1Labs wGninthN1nHT1Nums 2048 ++
    (decodeTerms wGninthN1nHT2Labs wGninthN1nHT2Nums 2048 ++
    (decodeTerms wGninthN1nHT3Labs wGninthN1nHT3Nums 2048 ++
    (decodeTerms wGninthN1nHT4Labs wGninthN1nHT4Nums 2048 ++
    (decodeTerms wGninthN1nHT5Labs wGninthN1nHT5Nums 2048 ++
    (decodeTerms wGninthN1nHT6Labs wGninthN1nHT6Nums 2048 ++
    (decodeTerms wGninthN1nHT7Labs wGninthN1nHT7Nums 2048)))))))

set_option maxRecDepth 100000 in
/-- The odd part of the tensor pairing over group 0 of the source terms. -/
theorem wGninthN1n_ol0 : oddSumL 64 false wGninthN1nGX wGninthN1nHTg0 = 23166976 := by
  decide +kernel

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

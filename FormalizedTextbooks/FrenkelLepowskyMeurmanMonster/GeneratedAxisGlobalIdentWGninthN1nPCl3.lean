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

/-! # Factory tensor part (odd source terms, group 3) of the identification Ninth[1]- <->
Tenth[33]+ (record gninth:N1-, e = -1)

Dense source or long words: the tensor part of the pairing is evaluated in parts. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

/-- Group 3 of the chunks of the source list. -/
def wGninthN1nHTg3 : List (ℕ × ℤ) :=
  decodeTerms wGninthN1nHT24Labs wGninthN1nHT24Nums 2048 ++
    (decodeTerms wGninthN1nHT25Labs wGninthN1nHT25Nums 2048 ++
    (decodeTerms wGninthN1nHT26Labs wGninthN1nHT26Nums 2048 ++
    (decodeTerms wGninthN1nHT27Labs wGninthN1nHT27Nums 2048 ++
    (decodeTerms wGninthN1nHT28Labs wGninthN1nHT28Nums 2048 ++
    (decodeTerms wGninthN1nHT29Labs wGninthN1nHT29Nums 2048 ++
    (decodeTerms wGninthN1nHT30Labs wGninthN1nHT30Nums 144))))))

set_option maxRecDepth 100000 in
/-- The odd part of the tensor pairing over group 3 of the source terms. -/
theorem wGninthN1n_ol3 : oddSumL 64 false wGninthN1nGX wGninthN1nHTg3 = 25624576 := by
  decide +kernel

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

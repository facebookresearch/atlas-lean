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

/-! # Factory tensor part (odd source terms, group 2) of the identification Ninth[1]- <->
Tenth[33]+ (record gninth:N1-, e = -1)

Dense source or long words: the tensor part of the pairing is evaluated in parts. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

/-- Group 2 of the chunks of the source list. -/
def wGninthN1nHTg2 : List (ℕ × ℤ) :=
  decodeTerms wGninthN1nHT16Labs wGninthN1nHT16Nums 2048 ++
    (decodeTerms wGninthN1nHT17Labs wGninthN1nHT17Nums 2048 ++
    (decodeTerms wGninthN1nHT18Labs wGninthN1nHT18Nums 2048 ++
    (decodeTerms wGninthN1nHT19Labs wGninthN1nHT19Nums 2048 ++
    (decodeTerms wGninthN1nHT20Labs wGninthN1nHT20Nums 2048 ++
    (decodeTerms wGninthN1nHT21Labs wGninthN1nHT21Nums 2048 ++
    (decodeTerms wGninthN1nHT22Labs wGninthN1nHT22Nums 2048 ++
    (decodeTerms wGninthN1nHT23Labs wGninthN1nHT23Nums 2048)))))))

set_option maxRecDepth 100000 in
/-- The odd part of the tensor pairing over group 2 of the source terms. -/
theorem wGninthN1n_ol2 : oddSumL 64 false wGninthN1nGX wGninthN1nHTg2 = 37289984 := by
  decide +kernel

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

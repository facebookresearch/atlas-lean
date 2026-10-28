/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentPilot1Checks
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentTensorPairO

/-! # Pilot identification: the grouped representation and the side conditions

The representation `pilot1Lg` of `h₁ v₅` with its octad terms grouped by octad, the numeric
side conditions of the packed pairing, and the applicability of the packed octad transform. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

/-- The representation of `h₁ v₅` with its octad terms grouped by octad. -/
def pilot1Lg : IdentVec :=
  ⟨fifthSrcMat.act identSpatialAlphabet pilot1H, ShortData.ofListI pilot1Th, 1 / 16,
    tensorRat 64 pilot1LX ((tensorWordDenAll pilot1H : ℚ) * 1)⟩

/-- The grouped representation has the same coordinates. -/
theorem pilot1Lg_real : pilot1Lg.real = pilot1L.real :=
  IdentVec.real_short_congr _ _ _ _ _
    ((shortVec_ofListI pilot1Th).trans (shortVec_ofList pilot1Th).symm)

set_option maxRecDepth 100000 in
/-- The coefficient sums of the odd terms. -/
theorem pilot1_absSum : absSumO pilot1Lg.sh.odd = 4096 ∧ absSumO pilot1W.sh.odd = 4096 := by
  decide +kernel

/-- The numeric side conditions of the pilot pairing. -/
theorem pilot1_bounds : PairXBounds 64 4194304 33554432 pilot1Lg pilot1W := by
  obtain ⟨h1, h2⟩ := pilot1_absSum
  exact ⟨by norm_num, by norm_num, by norm_num, by rw [h2]; norm_num, by rw [h2]; norm_num,
    by rw [h1]; norm_num, by rw [h1]; norm_num⟩

set_option maxRecDepth 100000 in
/-- The packed octad transform applies to `h₁ v₅` at octad field width `32`. -/
theorem pilot1_octOk : octPackOk 32 pilot1Lg = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- The grouped short block of `h₁ v₅` satisfies the range conditions. -/
theorem pilot1Lg_ok : pilot1Lg.sh.ok = true := ofListI_ok pilot1Th pilot1T_labels.1

/-- The short block of `g v₅` satisfies the range conditions. -/
theorem pilot1W_ok : pilot1W.sh.ok = true := ofList_ok pilot1Tg pilot1T_labels.2

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

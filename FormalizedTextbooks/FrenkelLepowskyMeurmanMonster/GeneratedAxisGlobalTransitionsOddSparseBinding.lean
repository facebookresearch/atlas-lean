/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddSparseCheck00
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddSparseCheck01
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddSparseCheck02
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddSparseCheck03
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddSparseCheck04
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddComparisonRationalData

/-! Every executable sparse coefficient equals the entire original preferred-basis sum. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option autoImplicit false
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

/-- All five original source trees have their complete coordinate key certificates. -/
theorem generatedAxisGlobalOddSparse_valid (k : Fin 5) :
    GeneratedAxisGlobalSparseLookupValid
      (fun p => generatedAxisGlobalShortNumber (generatedAxisGlobalOddSparseLabel k p))
      (generatedAxisGlobalOddSparseTree k) := by
  fin_cases k
  · exact generatedAxisGlobalOddSparseCheck00_valid
  · exact generatedAxisGlobalOddSparseCheck01_valid
  · exact generatedAxisGlobalOddSparseCheck02_valid
  · exact generatedAxisGlobalOddSparseCheck03_valid
  · exact generatedAxisGlobalOddSparseCheck04_valid

/-- Every source coefficient is found under its exact actual original coordinate. -/
theorem generatedAxisGlobalOddSparse_roundtrip (k : Fin 5)
    (p : GeneratedAxisGlobalOddShortPacketIndex) :
    generatedAxisGlobalOddSparseSource k (generatedAxisGlobalOddSparseLabel k p) = some p := by
  fin_cases k
  · exact generatedAxisGlobalOddSparseCheck00_roundtrip p
  · exact generatedAxisGlobalOddSparseCheck01_roundtrip p
  · exact generatedAxisGlobalOddSparseCheck02_roundtrip p
  · exact generatedAxisGlobalOddSparseCheck03_roundtrip p
  · exact generatedAxisGlobalOddSparseCheck04_roundtrip p

/-- A successful lookup identifies the actual original preferred coordinate of that source unit. -/
theorem generatedAxisGlobalOddSparse_sound (k : Fin 5) (r : GriessShortIndex)
    (p : GeneratedAxisGlobalOddShortPacketIndex)
    (hp : generatedAxisGlobalOddSparseSource k r = some p) :
    generatedAxisGlobalOddSparseLabel k p = r := by
  apply generatedAxisGlobalShortNumber_injective
  exact generatedAxisGlobalSparseLookup_sound _ _ (generatedAxisGlobalOddSparse_valid k) _ _ hp

/-- The entire original rational source sum equals the exact executable sparse coefficient. -/
theorem generatedAxisGlobalOddSparseShortQ_sum (k : Fin 5) (r : GriessShortIndex) :
    (∑ p : GeneratedAxisGlobalOddShortPacketIndex,
      generatedAxisGlobalOddSparseCoefficient k p *
        (if generatedAxisGlobalOddSparseLabel k p = r then 1 else 0)) =
      generatedAxisGlobalOddSparseShortQ k r := by
  have h := generatedAxisGlobalSparseLookup_sum _ _
    (generatedAxisGlobalOddSparse_roundtrip k) (generatedAxisGlobalOddSparse_sound k)
    (generatedAxisGlobalOddSparseCoefficient k) r
  cases hg : generatedAxisGlobalOddSparseSource k r <;>
    simpa only [generatedAxisGlobalOddSparseShortQ, hg] using h

/-- The original root-zero rational constituent agrees at every physical coordinate. -/
theorem generatedAxisGlobalOddSparseShortQ_root00 (r : GriessShortIndex) :
    generatedAxisGlobalOddRootShortQ 0 r = generatedAxisGlobalOddSparseShortQ 0 r := by
  exact generatedAxisGlobalOddSparseShortQ_sum 0 r

/-- The original root-six rational constituent agrees at every physical coordinate. -/
theorem generatedAxisGlobalOddSparseShortQ_root06 (r : GriessShortIndex) :
    generatedAxisGlobalOddRootShortQ 6 r = generatedAxisGlobalOddSparseShortQ 1 r := by
  exact generatedAxisGlobalOddSparseShortQ_sum 1 r

/-- Every comparison rational short constituent has its complete exact sparse source binding. -/
theorem generatedAxisGlobalOddSparseShortQ_comparison (k : Fin 3) (r : GriessShortIndex) :
    generatedAxisGlobalOddComparisonShortQ k r =
      generatedAxisGlobalOddSparseShortQ ⟨k.val + 2, by omega⟩ r := by
  fin_cases k
  · exact generatedAxisGlobalOddSparseShortQ_sum 2 r
  · exact generatedAxisGlobalOddSparseShortQ_sum 3 r
  · exact generatedAxisGlobalOddSparseShortQ_sum 4 r

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

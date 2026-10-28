/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddOtherSparseCheck02
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddOtherSparseCheck03
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddOtherSparseCheck04

/-! The complete original preferred-coordinate sums equal the exact sparse coefficients at every source coordinate. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-- All original source keys in all three complete source trees are valid. -/
theorem generatedAxisGlobalOddOtherSparse_valid (k : Fin 3) :
    GeneratedAxisGlobalSparseLookupValid
      (fun p => generatedAxisGlobalShortNumber (generatedAxisGlobalOddOtherSparseLabel k p))
      (generatedAxisGlobalOddOtherSparseTree k) := by
  fin_cases k
  · exact generatedAxisGlobalOddOtherSparseCheck02_valid
  · exact generatedAxisGlobalOddOtherSparseCheck03_valid
  · exact generatedAxisGlobalOddOtherSparseCheck04_valid

/-- Every original preferred source index has its exact complete coordinate round trip. -/
theorem generatedAxisGlobalOddOtherSparse_roundtrip (k : Fin 3)
    (p : GeneratedAxisGlobalOddShortPacketIndex) :
    generatedAxisGlobalOddOtherSparseSource k (generatedAxisGlobalOddOtherSparseLabel k p) = some p := by
  fin_cases k
  · exact generatedAxisGlobalOddOtherSparseCheck02_roundtrip p
  · exact generatedAxisGlobalOddOtherSparseCheck03_roundtrip p
  · exact generatedAxisGlobalOddOtherSparseCheck04_roundtrip p

/-- Successful lookups return the actual original preferred coordinate. -/
theorem generatedAxisGlobalOddOtherSparse_sound (k : Fin 3) (r : GriessShortIndex)
    (p : GeneratedAxisGlobalOddShortPacketIndex)
    (hp : generatedAxisGlobalOddOtherSparseSource k r = some p) :
    generatedAxisGlobalOddOtherSparseLabel k p = r := by
  apply generatedAxisGlobalShortNumber_injective
  exact generatedAxisGlobalSparseLookup_sound _ _
    (generatedAxisGlobalOddOtherSparse_valid k) _ _ hp

/-- Every original rational source sum is exactly the executable sparse source coefficient. -/
theorem generatedAxisGlobalOddOtherSparseShortQ_root (k : Fin 3) (r : GriessShortIndex) :
    generatedAxisGlobalOddRootShortQ (generatedAxisGlobalOddOtherSparseRoot k) r =
      generatedAxisGlobalOddOtherSparseShortQ k r := by
  have h := generatedAxisGlobalSparseLookup_sum _ _
    (generatedAxisGlobalOddOtherSparse_roundtrip k) (generatedAxisGlobalOddOtherSparse_sound k)
    (generatedAxisGlobalOddOtherSparseCoefficient k) r
  cases hg : generatedAxisGlobalOddOtherSparseSource k r <;>
    simpa only [generatedAxisGlobalOddOtherSparseShortQ, generatedAxisGlobalOddRootShortQ,
      generatedAxisGlobalOddOtherSparseCoefficient, generatedAxisGlobalOddOtherSparseLabel, hg] using h

/-- The original root-two source coefficient has its complete exact sparse binding. -/
theorem generatedAxisGlobalOddOtherSparseShortQ_root02 (r : GriessShortIndex) :
    generatedAxisGlobalOddRootShortQ 2 r = generatedAxisGlobalOddOtherSparseShortQ 0 r :=
  generatedAxisGlobalOddOtherSparseShortQ_root 0 r

/-- The original root-three source coefficient has its complete exact sparse binding. -/
theorem generatedAxisGlobalOddOtherSparseShortQ_root03 (r : GriessShortIndex) :
    generatedAxisGlobalOddRootShortQ 3 r = generatedAxisGlobalOddOtherSparseShortQ 1 r :=
  generatedAxisGlobalOddOtherSparseShortQ_root 1 r

/-- The original root-four source coefficient has its complete exact sparse binding. -/
theorem generatedAxisGlobalOddOtherSparseShortQ_root04 (r : GriessShortIndex) :
    generatedAxisGlobalOddRootShortQ 4 r = generatedAxisGlobalOddOtherSparseShortQ 2 r :=
  generatedAxisGlobalOddOtherSparseShortQ_root 2 r

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

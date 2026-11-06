/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthRepresentative
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthFinalShortNumerator
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsPairCoordinates

/-! A compressed original-source inverse for every pair row of the complete root-9 packet. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option maxRecDepth 10000

/-- Every genuine incoming short label in its original finite packet order. -/
def generatedTwelfthIncomingShortLabel (n : Fin 4136) : GriessShortIndex :=
  generatedAxisGlobalFifthRoot09ShortLabels
    ⟨n.val / 256, by omega⟩ ⟨n.val % 256, Nat.mod_lt _ (by decide)⟩

/-- Every original central phase in the identical packet order. -/
def generatedTwelfthIncomingShortPhase (n : Fin 4136) : ZMod 2 :=
  generatedAxisGlobalFifthRoot09ShortPhases
    ⟨n.val / 256, by omega⟩ ⟨n.val % 256, Nat.mod_lt _ (by decide)⟩

/-- The unique original packet entry for a pair row, or 4136 when no entry maps to that row. -/
def generatedTwelfthPairSource : Fin 552 → ℕ :=
  ![
    4136, 4136, 21, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 549,
    4136, 4136, 535, 4136, 4136, 4136, 4136, 305, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136,
    4136, 4136, 4136, 4136, 4136, 4136, 156, 442, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136,
    4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 306, 40, 4136, 4136, 4136,
    4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 296, 4136,
    4136, 292, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136,
    4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136,
    4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136,
    4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136,
    4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136,
    4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136,
    4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136,
    4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136,
    4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136,
    4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136,
    4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 258, 4136, 4136, 4136, 4136, 456,
    4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136,
    4136, 4136, 4136, 4136, 445, 43, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136,
    4136, 4136, 4136, 4136, 459, 268, 4136, 4136, 4136, 4136, 4136, 4136, 283, 4136, 4136, 4136,
    4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 168, 4136, 4136, 164, 4136, 4136, 4136,
    4136, 0, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 318, 4136,
    4136, 314, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136,
    4136, 4136, 4136, 284, 18, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136,
    4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136,
    4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136,
    4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136,
    4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136,
    4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136,
    4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136,
    4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136,
    4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136,
    4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136,
    4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 182, 543, 4136, 4136,
    4136, 4136, 4136, 4136, 178, 4136, 4136, 4136, 4136, 532, 4136, 4136, 4136, 4136, 4136, 4136,
    4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136
  ]

/-- All source identifiers are valid packet numbers or the unique outside sentinel. -/
theorem generatedTwelfth_pair_source_bound (p : Fin 552) :
    generatedTwelfthPairSource p ≤ 4136 := by
  revert p
  decide +kernel

/-- The actual outgoing pair number, or 552 for either nonpair family. -/
def generatedTwelfthIncomingPairNumber (n : Fin 4136) : ℕ :=
  match generatedTwelfthIncomingShortLabel n with
  | Sum.inl (s, p) => 276 * s.val + p.val
  | Sum.inr _ => 552

set_option maxHeartbeats 64000000 in
-- Check every original finite dictionary label against the compressed source inverse.
/-- The complete outgoing pair-number graph has exactly the recorded original source. -/
theorem generatedTwelfth_pair_source_graph : ∀ n : Fin 4136,
    if h : generatedTwelfthIncomingPairNumber n < 552 then
      generatedTwelfthPairSource ⟨generatedTwelfthIncomingPairNumber n, h⟩ = n.val
    else True := by
  decide +kernel

/-- Every actual packet entry reaching a pair row has its unique recorded original source. -/
theorem generatedTwelfth_pair_source_forward (n : Fin 4136) :
    match generatedTwelfthIncomingShortLabel n with
    | Sum.inl (s, p) => generatedTwelfthPairSource ⟨276 * s.val + p.val, by omega⟩ = n.val
    | Sum.inr _ => True := by
  have h := generatedTwelfth_pair_source_graph n
  cases he : generatedTwelfthIncomingShortLabel n with
  | inl p =>
    rcases p with ⟨s, p⟩
    have hb : 276 * s.val + p.val < 552 := by omega
    simpa only [generatedTwelfthIncomingPairNumber, he, hb, dite_eq_left] using h
  | inr _ => trivial

set_option maxHeartbeats 64000000 in
-- Check all 552 original inverse rows, including each outside sentinel.
/-- Every finite nonsentinel inverse reconstructs exactly its actual outgoing pair row. -/
theorem generatedTwelfth_pair_source_reverse_checked : ∀ (s : Fin 2) (p : Fin 276),
    if h : generatedTwelfthPairSource ⟨276 * s.val + p.val, by omega⟩ < 4136 then
      generatedTwelfthIncomingShortLabel
        ⟨generatedTwelfthPairSource ⟨276 * s.val + p.val, by omega⟩, h⟩ = Sum.inl (s, p)
    else True := by
  decide +kernel

/-- Every nonsentinel inverse identifies exactly the actual original pair row. -/
theorem generatedTwelfth_pair_source_reverse (s : Fin 2) (p : Fin 276)
    (h : generatedTwelfthPairSource ⟨276 * s.val + p.val, by omega⟩ < 4136) :
    generatedTwelfthIncomingShortLabel
      ⟨generatedTwelfthPairSource ⟨276 * s.val + p.val, by omega⟩, h⟩ = Sum.inl (s, p) := by
  simpa only [h, dite_eq_left] using generatedTwelfth_pair_source_reverse_checked s p

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

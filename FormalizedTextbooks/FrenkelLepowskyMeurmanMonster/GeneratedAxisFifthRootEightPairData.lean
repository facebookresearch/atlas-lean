/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisFifthRootEightRepresentative
public import
FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthFinalShortNumerator
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsPairCoordinates

/-! A compressed original-source inverse for every pair row of the complete root-8 packet. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option maxRecDepth 10000

/-- Every genuine incoming short label in its original finite packet order. -/
def generatedFifthRootEightIncomingShortLabel (n : Fin 4136) : GriessShortIndex :=
  generatedAxisGlobalFifthRoot08ShortLabels
    ⟨n.val / 256, by omega⟩ ⟨n.val % 256, Nat.mod_lt _ (by decide)⟩

/-- Every original central phase in the identical packet order. -/
def generatedFifthRootEightIncomingShortPhase (n : Fin 4136) : ZMod 2 :=
  generatedAxisGlobalFifthRoot08ShortPhases
    ⟨n.val / 256, by omega⟩ ⟨n.val % 256, Nat.mod_lt _ (by decide)⟩

/-- The unique original packet entry for a pair row, or 4136 when no entry maps to that row. -/
def generatedFifthRootEightPairSource : Fin 552 → ℕ :=
  ![4136, 4136, 111, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136,
  4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 7, 4136, 4136, 4136, 4136, 4136, 2139, 4136,
  4136, 4136, 4136, 4136, 4136, 4136, 4136, 3147, 4091, 4136, 1271, 4136, 1301, 4136, 4136,
  4136, 4136, 4136, 4136, 2142, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 3150, 4094,
  4136, 1286, 4136, 1316, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136,
  4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136,
  4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136,
  4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136,
  4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136,
  4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136,
  4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 1758, 2012,
  4136, 2532, 4136, 2529, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136,
  4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136,
  4136, 4136, 4136, 4136, 4136, 4136, 1746, 4136, 4136, 1990, 4136, 4136, 4136, 4136, 4136,
  4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136,
  4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136,
  4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 1885, 4136, 4136, 4136, 4136, 1870,
  4136, 3540, 4136, 3537, 4136, 4136, 3716, 4136, 3713, 4136, 4136, 4136, 4136, 4136, 4136, 30,
  4136, 4136, 94, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136,
  4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136,
  4136, 4136, 4136, 4136, 4136, 2123, 4136, 4136, 4136, 4136, 3131, 4136, 4136, 4132, 4136,
  4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 2126, 4136, 4136, 4136,
  4136, 3134, 4136, 4136, 4129, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136,
  4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136,
  4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136,
  4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136,
  4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136,
  4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136,
  4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 251, 4136, 4136, 4136, 4136,
  1762, 4136, 4136, 1975, 4136, 4136, 4136, 4136, 123, 4136, 4136, 4136, 4136, 4136, 4136, 4136,
  4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136,
  4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 1742, 1997, 4136, 2516, 4136, 2513,
  4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136,
  4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136,
  4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 4136, 231, 1874, 4136, 3524, 4136, 3521, 4136,
  4136, 1889, 4136, 4136, 4136, 4136, 265, 4136, 4136, 4136, 4136, 3739, 4136, 3742, 4136, 4136,
  4136, 4136, 4136, 4136, 4136]

/-- All source identifiers are valid packet numbers or the unique outside sentinel. -/
theorem generatedFifthRootEight_pair_source_bound (p : Fin 552) :
    generatedFifthRootEightPairSource p ≤ 4136 := by
  revert p
  decide +kernel

/-- The actual outgoing pair number, or 552 for either nonpair family. -/
def generatedFifthRootEightIncomingPairNumber (n : Fin 4136) : ℕ :=
  match generatedFifthRootEightIncomingShortLabel n with
  | Sum.inl (s, p) => 276 * s.val + p.val
  | Sum.inr _ => 552

set_option maxHeartbeats 64000000 in
-- Check every original finite dictionary label against the compressed source inverse.
/-- The complete outgoing pair-number graph has exactly the recorded original source. -/
theorem generatedFifthRootEight_pair_source_graph : ∀ n : Fin 4136,
    if h : generatedFifthRootEightIncomingPairNumber n < 552 then
      generatedFifthRootEightPairSource ⟨generatedFifthRootEightIncomingPairNumber n, h⟩ = n.val
    else True := by
  decide +kernel

/-- Every actual packet entry reaching a pair row has its unique recorded original source. -/
theorem generatedFifthRootEight_pair_source_forward (n : Fin 4136) :
    match generatedFifthRootEightIncomingShortLabel n with
    | Sum.inl (s, p) => generatedFifthRootEightPairSource ⟨276 * s.val + p.val, by omega⟩ = n.val
    | Sum.inr _ => True := by
  have h := generatedFifthRootEight_pair_source_graph n
  cases he : generatedFifthRootEightIncomingShortLabel n with
  | inl p =>
    rcases p with ⟨s, p⟩
    have hb : 276 * s.val + p.val < 552 := by omega
    simpa only [generatedFifthRootEightIncomingPairNumber, he, hb, dite_eq_left] using h
  | inr _ => trivial

set_option maxHeartbeats 64000000 in
-- Check all 552 original inverse rows, including each outside sentinel.
/-- Every finite nonsentinel inverse reconstructs exactly its actual outgoing pair row. -/
theorem generatedFifthRootEight_pair_source_reverse_checked : ∀ (s : Fin 2) (p : Fin 276),
    if h : generatedFifthRootEightPairSource ⟨276 * s.val + p.val, by omega⟩ < 4136 then
      generatedFifthRootEightIncomingShortLabel
        ⟨generatedFifthRootEightPairSource ⟨276 * s.val + p.val, by omega⟩, h⟩ = Sum.inl (s, p)
    else True := by
  decide +kernel

/-- Every nonsentinel inverse identifies exactly the actual original pair row. -/
theorem generatedFifthRootEight_pair_source_reverse (s : Fin 2) (p : Fin 276)
    (h : generatedFifthRootEightPairSource ⟨276 * s.val + p.val, by omega⟩ < 4136) :
    generatedFifthRootEightIncomingShortLabel
      ⟨generatedFifthRootEightPairSource ⟨276 * s.val + p.val, by omega⟩, h⟩ = Sum.inl (s, p) := by
  simpa only [h, dite_eq_left] using generatedFifthRootEight_pair_source_reverse_checked s p

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

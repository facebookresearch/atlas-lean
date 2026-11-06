/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Exact literal transition-target statement, with no source or subgroup assumptions. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationC422CosetProgram
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationC422CosetOrbitData

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- The literal chronological claim has exactly the required two transition words. -/
def y422CosetTransitionWords (i : Fin 1080) (a : Fin 9) : Prop :=
  (y422CosetProgram (y422CosetTransitionTarget i a)).1.left =
    y422CosetPathWord (y422CosetRoot i) ++ [(y422CosetGeneratorLetter a, true)] ∧
  (y422CosetProgram (y422CosetTransitionTarget i a)).1.right =
    y422CosetPathWord (y422CosetRoot (y422CosetNext i a))

/-- Flat finite indexing lists all 1080 states and their nine actual source transitions. -/
def y422CosetTargetWords (k : Fin 9720) : Prop :=
  y422CosetTransitionWords ⟨k.val / 9, by omega⟩ ⟨k.val % 9, by omega⟩

/-- Literal transition boundaries are decidable by equality of finite source words. -/
instance y422CosetTargetWordsDecidable (k : Fin 9720) : Decidable (y422CosetTargetWords k) := by
  unfold y422CosetTargetWords y422CosetTransitionWords
  infer_instance

/-- A state/source pair returns its literal original flat transition index. -/
theorem y422CosetTargetWords_pair (i : Fin 1080) (a : Fin 9) :
    y422CosetTargetWords ⟨9 * i.val + a.val, by omega⟩ ↔ y422CosetTransitionWords i a := by
  have hi : (⟨(9 * i.val + a.val) / 9, by omega⟩ : Fin 1080) = i := by
    apply Fin.ext
    dsimp only
    omega
  have ha : (⟨(9 * i.val + a.val) % 9, by omega⟩ : Fin 9) = a := by
    apply Fin.ext
    dsimp only
    omega
  unfold y422CosetTargetWords
  dsimp only
  rw [hi, ha]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

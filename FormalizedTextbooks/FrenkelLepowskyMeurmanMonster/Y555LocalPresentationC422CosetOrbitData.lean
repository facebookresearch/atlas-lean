/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Actual bounded orbit data assembled without out-of-range reduction or padding. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationC422CosetOrbitData00
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationC422CosetOrbitData01
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationC422CosetOrbitData02
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationC422CosetOrbitData03
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationC422CosetOrbitData04
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationC422CosetOrbitData05
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationC422CosetOrbitData06
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationC422CosetOrbitData07
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationC422CosetOrbitData08

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- A checked exact interval of roots, transitions, and literal target indices. -/
structure Y422CosetOrbitChunk where
  /-- The exact first state index. -/
  offset : ℕ
  /-- The exact number of states in this interval. -/
  size : ℕ
  /-- Literal natural-number data, before finite decoding. -/
  data : Fin size → ℕ × (Fin 9 → ℕ) × (Fin 9 → ℕ)
  /-- Every literal index has its actual finite bound. -/
  allowed : ∀ i, (data i).1 < 9033 ∧
    ∀ a, ((data i).2.1 a < 1080 ∧ (data i).2.2 a < 41827)

/-- Exact intervals, retaining the final fifty-six states without padding. -/
def y422CosetOrbitChunks : Fin 9 → Y422CosetOrbitChunk :=
  ![⟨0, 128, y422CosetOrbitRaw00, y422CosetOrbitRaw00_allowed⟩,
    ⟨128, 128, y422CosetOrbitRaw01, y422CosetOrbitRaw01_allowed⟩,
    ⟨256, 128, y422CosetOrbitRaw02, y422CosetOrbitRaw02_allowed⟩,
    ⟨384, 128, y422CosetOrbitRaw03, y422CosetOrbitRaw03_allowed⟩,
    ⟨512, 128, y422CosetOrbitRaw04, y422CosetOrbitRaw04_allowed⟩,
    ⟨640, 128, y422CosetOrbitRaw05, y422CosetOrbitRaw05_allowed⟩,
    ⟨768, 128, y422CosetOrbitRaw06, y422CosetOrbitRaw06_allowed⟩,
    ⟨896, 128, y422CosetOrbitRaw07, y422CosetOrbitRaw07_allowed⟩,
    ⟨1024, 56, y422CosetOrbitRaw08, y422CosetOrbitRaw08_allowed⟩]

/-- Exact quotient offsets for the state intervals. -/
theorem y422CosetOrbitChunks_offset (b : Fin 9) :
    (y422CosetOrbitChunks b).offset = 128 * b.val := by
  revert b
  decide +kernel

/-- The last interval retains its actual fifty-six states. -/
theorem y422CosetOrbitChunks_size (b : Fin 9) :
    (y422CosetOrbitChunks b).size = if b.val < 8 then 128 else 56 := by
  revert b
  decide +kernel

/-- The exact state interval containing a supplied state. -/
def y422CosetOrbitBlock (i : Fin 1080) : Fin 9 := ⟨i.val / 128, by omega⟩

/-- The exact local state index, with the shorter final tail checked. -/
def y422CosetOrbitLocal (i : Fin 1080) : Fin (y422CosetOrbitChunks (y422CosetOrbitBlock i)).size :=
  ⟨i.val % 128, by
    rw [y422CosetOrbitChunks_size]
    unfold y422CosetOrbitBlock
    dsimp only
    split_ifs <;> omega⟩

/-- The literal state data, selected inside their exact checked interval. -/
def y422CosetOrbitRaw (i : Fin 1080) : ℕ × (Fin 9 → ℕ) × (Fin 9 → ℕ) :=
  (y422CosetOrbitChunks (y422CosetOrbitBlock i)).data (y422CosetOrbitLocal i)

/-- All assembled raw state indices retain their actual finite bounds. -/
theorem y422CosetOrbitRaw_allowed (i : Fin 1080) :
    (y422CosetOrbitRaw i).1 < 9033 ∧
      ∀ a, ((y422CosetOrbitRaw i).2.1 a < 1080 ∧ (y422CosetOrbitRaw i).2.2 a < 41827) :=
  (y422CosetOrbitChunks (y422CosetOrbitBlock i)).allowed (y422CosetOrbitLocal i)

/-- The actual acyclic source-path representative index of a state. -/
def y422CosetRoot (i : Fin 1080) : Fin 9033 :=
  ⟨(y422CosetOrbitRaw i).1, (y422CosetOrbitRaw_allowed i).1⟩

/-- The exact destination state after one actual source generator. -/
def y422CosetNext (i : Fin 1080) (a : Fin 9) : Fin 1080 :=
  ⟨(y422CosetOrbitRaw i).2.1 a, ((y422CosetOrbitRaw_allowed i).2 a).1⟩

/-- The exact chronological claim proving a supplied state transition. -/
def y422CosetTransitionTarget (i : Fin 1080) (a : Fin 9) : Fin 41827 :=
  ⟨(y422CosetOrbitRaw i).2.2 a, ((y422CosetOrbitRaw_allowed i).2 a).2⟩

/-- The initial state uses the exact original empty path. -/
theorem y422CosetRoot_zero : y422CosetRoot 0 = 0 := by
  apply Fin.ext
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

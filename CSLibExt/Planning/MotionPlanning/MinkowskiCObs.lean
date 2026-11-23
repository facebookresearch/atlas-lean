/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Planning.MotionPlanning.ConfigurationSpace

@[expose] public section

namespace Cslib.Planning.MotionPlanning

/-- Translating placement of a rigid body `A₀` (given at placement `0`):
configuration `q` shifts every body point by `q`. -/
def translatePlacement (V : Type*) [NormedAddCommGroup V] (A₀ : Set V) :
    V → Set V :=
  fun q => (· + q) '' A₀

/-- Minkowski sum of two sets, as an explicit set-builder. -/
def minkSum (V : Type*) [NormedAddCommGroup V] (O A : Set V) : Set V :=
  {x | ∃ o ∈ O, ∃ a ∈ A, x = o + a}

/-- Pointwise negation of a set, as an explicit set-builder. -/
def negSet (V : Type*) [NormedAddCommGroup V] (A : Set V) : Set V :=
  {x | ∃ a ∈ A, x = -a}

/-- A translating placement collides iff some body point shifted by `q` lands in
the obstacle set. -/
theorem mem_cObs_translatePlacement (V : Type*) [NormedAddCommGroup V]
    (A₀ : Set V) (O : Set V) (q : V) :
    q ∈ cObs V V (translatePlacement V A₀) O ↔ ∃ a ∈ A₀, a + q ∈ O := by
  rw [mem_cObs]
  constructor
  · rintro ⟨y, ⟨a, ha, rfl⟩, hy⟩
    exact ⟨a, ha, hy⟩
  · rintro ⟨a, ha, hy⟩
    exact ⟨_, ⟨a, ha, rfl⟩, hy⟩

/-- Membership in `O ⊕ (-A₀)` unfolds to a sum representation. -/
theorem mem_minkSum_neg (V : Type*) [NormedAddCommGroup V]
    (A₀ : Set V) (O : Set V) (q : V) :
    q ∈ minkSum V O (negSet V A₀) ↔ ∃ o ∈ O, ∃ a ∈ A₀, q = o + -a := by
  constructor
  · rintro ⟨o, ho, a', ⟨a, ha, rfl⟩, hq⟩
    exact ⟨o, ho, a, ha, hq⟩
  · rintro ⟨o, ho, a, ha, hq⟩
    exact ⟨o, ho, -a, ⟨a, ha, rfl⟩, hq⟩

/-- The C-obstacle of a translating robot is the Minkowski sum `O ⊕ (-A₀)`,
with the reference point at the origin. -/
theorem cObs_translate (V : Type*) [NormedAddCommGroup V] (A₀ : Set V)
    (O : Set V) :
    cObs V V (translatePlacement V A₀) O = minkSum V O (negSet V A₀) := by
  ext q
  rw [mem_cObs_translatePlacement, mem_minkSum_neg]
  constructor
  · rintro ⟨a, ha, hy⟩
    exact ⟨a + q, hy, a, ha, by abel⟩
  · rintro ⟨o, ho, a, ha, hq⟩
    have h : a + q = o := by rw [hq]; abel
    refine ⟨a, ha, ?_⟩
    rwa [h]

/-- Point robot: with `A₀ = {0}` the C-obstacle is exactly `O`. -/
theorem cObs_translate_singleton_zero (V : Type*) [NormedAddCommGroup V]
    (O : Set V) :
    cObs V V (translatePlacement V {0}) O = O := by
  rw [cObs_translate]
  ext q
  rw [mem_minkSum_neg]
  constructor
  · rintro ⟨o, ho, a, ha, hq⟩
    simp only [Set.mem_singleton_iff] at ha
    subst ha
    simp only [neg_zero, add_zero] at hq
    rwa [hq]
  · intro hq
    exact ⟨q, hq, 0, Set.mem_singleton 0, by simp⟩

/-- Free space of a translating robot, as the complement of `O ⊕ (-A₀)`. -/
theorem cFree_translate (V : Type*) [NormedAddCommGroup V] (A₀ : Set V)
    (O : Set V) :
    cFree V V (translatePlacement V A₀) O = (minkSum V O (negSet V A₀))ᶜ := by
  show (cObs V V (translatePlacement V A₀) O)ᶜ = _
  rw [cObs_translate]

end Cslib.Planning.MotionPlanning

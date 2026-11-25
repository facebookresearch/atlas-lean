/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Planning.MotionPlanning.ConfigurationSpace
public import Mathlib.Algebra.Group.Pointwise.Set.Basic

import Mathlib.Tactic.Abel

/-!
# C-obstacle of a translating robot as a Minkowski sum

For a robot translating in a vector space, with body `A₀` at the reference
placement `0`, the C-obstacle of `translatePlacement` is the Minkowski
(pointwise) sum `O + (-A₀)`, and free space is its complement.

## References

* T. Lozano-Pérez, _Spatial Planning: A Configuration Space Approach_,
  IEEE Transactions on Computers 32(2), 1983, pp. 108-120.
* S. M. LaValle, _Planning Algorithms_, Cambridge University Press, 2006, Ch. 4.
-/

@[expose] public section

namespace Cslib.Planning.MotionPlanning

open Pointwise

/-- Translating placement of a rigid body `A₀` (given at placement `0`):
configuration `q` shifts every body point by `q`. -/
def translatePlacement (V : Type*) [AddCommGroup V] (A₀ : Set V) :
    V → Set V :=
  fun q => (· + q) '' A₀

/-- A translating placement collides iff some body point shifted by `q` lands in
the obstacle set. -/
theorem mem_cObs_translatePlacement (V : Type*) [AddCommGroup V]
    (A₀ : Set V) (O : Set V) (q : V) :
    q ∈ cObs V V (translatePlacement V A₀) O ↔ ∃ a ∈ A₀, a + q ∈ O := by
  rw [mem_cObs]
  constructor
  · rintro ⟨y, ⟨a, ha, rfl⟩, hy⟩
    exact ⟨a, ha, hy⟩
  · rintro ⟨a, ha, hy⟩
    exact ⟨a + q, ⟨a, ha, rfl⟩, hy⟩

/-- The C-obstacle of a translating robot is the Minkowski sum `O ⊕ (-A₀)`,
with the reference point at the origin. -/
theorem cObs_translate (V : Type*) [AddCommGroup V] (A₀ : Set V)
    (O : Set V) :
    cObs V V (translatePlacement V A₀) O = O + (-A₀) := by
  ext q
  rw [mem_cObs_translatePlacement, Set.mem_add]
  constructor
  · rintro ⟨a, ha, hy⟩
    exact ⟨a + q, hy, -a, Set.mem_neg.mpr (by simpa using ha), by abel⟩
  · rintro ⟨o, ho, b, hb, hq⟩
    rw [Set.mem_neg] at hb
    refine ⟨-b, hb, ?_⟩
    have h : -b + q = o := by rw [← hq]; abel
    rwa [h]

/-- Point robot: with `A₀ = {0}` the C-obstacle is exactly `O`. -/
theorem cObs_translate_singleton_zero (V : Type*) [AddCommGroup V]
    (O : Set V) :
    cObs V V (translatePlacement V {0}) O = O := by
  rw [cObs_translate]
  ext q
  rw [Set.mem_add]
  constructor
  · rintro ⟨o, ho, b, hb, hq⟩
    rw [Set.mem_neg, Set.mem_singleton_iff] at hb
    have hb0 : b = 0 := neg_eq_zero.mp hb
    subst hb0
    rw [add_zero] at hq
    rwa [← hq]
  · intro hq
    exact ⟨q, hq, 0, by simp, by simp⟩

/-- Free space of a translating robot, as the complement of `O ⊕ (-A₀)`. -/
theorem cFree_translate (V : Type*) [AddCommGroup V] (A₀ : Set V)
    (O : Set V) :
    cFree V V (translatePlacement V A₀) O = (O + (-A₀))ᶜ := by
  show (cObs V V (translatePlacement V A₀) O)ᶜ = _
  rw [cObs_translate]

end Cslib.Planning.MotionPlanning

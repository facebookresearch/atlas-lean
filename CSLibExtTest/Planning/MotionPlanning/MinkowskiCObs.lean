/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib

namespace Cslib.Planning.MotionPlanning

open Pointwise

/-- A configuration collides iff some placed body point lands in the obstacle set. -/
def cObs (C V : Type*) (placement : C → Set V) (O : Set V) : Set C :=
  {q | ∃ y, y ∈ placement q ∧ y ∈ O}

/-- Membership in the C-obstacle unfolds to the collision witness. -/
theorem mem_cObs (C V : Type*) (placement : C → Set V) (O : Set V) (q : C) :
    q ∈ cObs C V placement O ↔ ∃ y, y ∈ placement q ∧ y ∈ O :=
  Iff.rfl

/-- Free space is the complement of the C-obstacle. -/
def cFree (C V : Type*) (placement : C → Set V) (O : Set V) : Set C :=
  (cObs C V placement O)ᶜ

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
    exact ⟨_, ⟨a, ha, rfl⟩, hy⟩

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

/-- The plane, as a two-dimensional Euclidean space. -/
abbrev plane := EuclideanSpace ℝ (Fin 2)

/-- Test point: the first basis vector of the plane. -/
noncomputable def testVec : plane := EuclideanSpace.single 0 1

/-- C-obstacle membership with explicit witness: `0` collides since `0 + 0 ∈ O`. -/
theorem test_cObs_mem_zero :
    (0 : plane) ∈ cObs plane plane
      (translatePlacement plane {0, testVec}) {0} := by
  rw [mem_cObs_translatePlacement]
  exact ⟨0, by simp, by simp⟩

/-- Pointwise-side membership with explicit witnesses: `0 = 0 + -0`. -/
theorem test_pointwise_mem_zero :
    (0 : plane) ∈ ({0} : Set plane) + (-({0, testVec} : Set plane)) := by
  exact ⟨0, Set.mem_singleton 0, 0, by simp, by simp⟩

/-- C-obstacle membership with a two-point obstacle set. -/
theorem test_cObs_mem_two_point :
    testVec ∈ cObs plane plane
      (translatePlacement plane {0, testVec}) {0, testVec} := by
  rw [mem_cObs_translatePlacement]
  exact ⟨0, by simp, by simp⟩

/-- Pointwise-side membership with a two-point obstacle set:
`testVec = testVec + -0`. -/
theorem test_pointwise_mem_two_point :
    testVec ∈ ({0, testVec} : Set plane) + (-({0, testVec} : Set plane)) := by
  exact ⟨testVec, by simp, 0, by simp, by simp⟩

/-- Point-robot instance on the plane. -/
theorem test_point_robot :
    cObs plane plane (translatePlacement plane {0}) {0} = ({0} : Set plane) :=
  cObs_translate_singleton_zero plane {0}

/-- Point-robot membership instance on the plane. -/
theorem test_point_robot_mem :
    (0 : plane) ∈ cObs plane plane (translatePlacement plane {0}) {0} := by
  rw [test_point_robot]
  exact Set.mem_singleton 0

/-- Sign-sensitive membership over `ℝ`: `-1 = 0 + (-1)`, so `-1` collides. -/
theorem test_sign_mem_neg_one :
    (-1 : ℝ) ∈ cObs ℝ ℝ (translatePlacement ℝ {1}) {0} := by
  rw [mem_cObs_translatePlacement]
  exact ⟨1, by simp, by simp⟩

/-- Sign-sensitive non-membership over `ℝ`: `1 + 1 ≠ 0`, so `1` is free. -/
theorem test_sign_notmem_one :
    (1 : ℝ) ∉ cObs ℝ ℝ (translatePlacement ℝ {1}) {0} := by
  rw [mem_cObs_translatePlacement]
  rintro ⟨a, ha, hy⟩
  simp only [Set.mem_singleton_iff] at ha hy
  rw [ha] at hy
  norm_num at hy

-- Axiom probes (scratch acceptance evidence).
#print axioms mem_cObs_translatePlacement
#print axioms cObs_translate
#print axioms cObs_translate_singleton_zero
#print axioms cFree_translate
#print axioms test_cObs_mem_zero
#print axioms test_pointwise_mem_zero
#print axioms test_cObs_mem_two_point
#print axioms test_pointwise_mem_two_point
#print axioms test_point_robot
#print axioms test_point_robot_mem
#print axioms test_sign_mem_neg_one
#print axioms test_sign_notmem_one

end Cslib.Planning.MotionPlanning

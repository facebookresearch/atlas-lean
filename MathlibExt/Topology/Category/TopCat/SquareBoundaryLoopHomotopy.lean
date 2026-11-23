/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.Category.TopCat.HomotopyPullback
public import Mathlib.Topology.Homotopy.HomotopyGroup

/-!
# Based-loop homotopies from a filled square

A continuous square whose left and top edges are constant, whose bottom edge is a reversed based
loop, and whose right edge is a supplied based-loop family determines a compact-open continuous
homotopy from the original loop to that right edge.

This file makes no lifting, contraction, homotopy-equivalence, weak-equivalence, bar, `EG`, or `BG`
claim.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open Topology Set
open scoped Topology.Homotopy

universe u

namespace TopCat

/-- Package the supplied right boundary of a square as a continuous family of based loops. -/
def squareRightEdgeLoop
    {B : TopCat.{u}} (b : B)
    (A : C((LoopSpace B b × unitInterval) × unitInterval, B))
    (R : C(LoopSpace B b × unitInterval, B))
    (hRight : ∀ (γ : LoopSpace B b) (t : unitInterval),
      A ((γ, 1), t) = R (γ, t))
    (hBottom : ∀ (γ : LoopSpace B b) (s : unitInterval),
      A ((γ, s), 0) = γ (unitInterval.symm s))
    (hTop : ∀ (γ : LoopSpace B b) (s : unitInterval),
      A ((γ, s), 1) = b) :
    C(LoopSpace B b, LoopSpace B b) where
  toFun γ :=
    { toFun := fun t => R (γ, t)
      continuous_toFun := R.continuous.comp (continuous_const.prodMk continuous_id)
      source' := by
        rw [← hRight]
        simpa using hBottom γ 1
      target' := by
        rw [← hRight]
        exact hTop γ 1 }
  continuous_toFun := by
    rw [← Path.continuous_uncurry_iff]
    exact R.continuous

/-- A filled square gives a compact-open homotopy from each original based loop to the supplied
right-edge loop, in the literal bottom-to-right orientation. -/
noncomputable def squareBoundaryLoopHomotopy
    {B : TopCat.{u}} (b : B)
    (A : C((LoopSpace B b × unitInterval) × unitInterval, B))
    (R : C(LoopSpace B b × unitInterval, B))
    (hLeft : ∀ (γ : LoopSpace B b) (t : unitInterval),
      A ((γ, 0), t) = b)
    (hRight : ∀ (γ : LoopSpace B b) (t : unitInterval),
      A ((γ, 1), t) = R (γ, t))
    (hBottom : ∀ (γ : LoopSpace B b) (s : unitInterval),
      A ((γ, s), 0) = γ (unitInterval.symm s))
    (hTop : ∀ (γ : LoopSpace B b) (s : unitInterval),
      A ((γ, s), 1) = b) :
    ContinuousMap.Homotopy (ContinuousMap.id (LoopSpace B b))
      (squareRightEdgeLoop b A R hRight hBottom hTop) := by
  let leftEdge :
      Path ((0, 0) : unitInterval × unitInterval) (0, 1) :=
    { toFun := fun t => (0, t)
      continuous_toFun := by fun_prop
      source' := rfl
      target' := rfl }
  let topEdge :
      Path ((0, 1) : unitInterval × unitInterval) (1, 1) :=
    { toFun := fun t => (t, 1)
      continuous_toFun := by fun_prop
      source' := rfl
      target' := rfl }
  let boundary : Path ((0, 0) : unitInterval × unitInterval) (1, 1) :=
    leftEdge.trans topEdge
  have boundary_zero : boundary 0 = (0, 0) := Path.source _
  have boundary_one : boundary 1 = (1, 1) := Path.target _
  have boundary_eq_base (γ : LoopSpace B b) (r : unitInterval) :
      A ((γ, (boundary r).1), (boundary r).2) = b := by
    dsimp only [boundary]
    rw [Path.trans_apply]
    split_ifs with h
    · exact hLeft γ _
    · exact hTop γ _
  let sweep : C(unitInterval × unitInterval, unitInterval × unitInterval) :=
    { toFun := fun z =>
        (Set.Icc.convexComb 1 (boundary z.1).1 z.2,
          Set.Icc.convexComb 0 (boundary z.1).2 z.2)
      continuous_toFun := by fun_prop }
  have sweep_loop_zero (r : unitInterval) : sweep (r, 0) = (1, 0) := by
    simp [sweep]
  have sweep_loop_one (r : unitInterval) : sweep (r, 1) = boundary r := by
    simp [sweep]
  have sweep_homotopy_zero (z : unitInterval) :
      sweep (0, z) = (unitInterval.symm z, 0) := by
    apply Prod.ext
    · apply Subtype.ext
      simp [sweep, boundary_zero, Set.Icc.convexComb, unitInterval.symm]
    · apply Subtype.ext
      simp [sweep, boundary_zero, Set.Icc.convexComb]
  have sweep_homotopy_one (z : unitInterval) : sweep (1, z) = (1, z) := by
    simp [sweep, boundary_one]
  let swept : C(unitInterval × LoopSpace B b, LoopSpace B b) :=
    { toFun := fun z =>
        { toFun := fun t => A ((z.2, (sweep (z.1, t)).1), (sweep (z.1, t)).2)
          continuous_toFun := by fun_prop
          source' := by
            rw [sweep_loop_zero]
            simpa using hBottom z.2 1
          target' := by
            rw [sweep_loop_one]
            exact boundary_eq_base z.2 z.1 }
      continuous_toFun := by
        rw [← Path.continuous_uncurry_iff]
        change Continuous fun z :
            (unitInterval × LoopSpace B b) × unitInterval =>
          A ((z.1.2, (sweep (z.1.1, z.2)).1), (sweep (z.1.1, z.2)).2)
        fun_prop }
  exact
    { toContinuousMap := swept
      map_zero_left := fun γ => by
        apply Path.ext
        funext z
        change A ((γ, (sweep (0, z)).1), (sweep (0, z)).2) = γ z
        rw [sweep_homotopy_zero, hBottom]
        simp
      map_one_left := fun γ => by
        apply Path.ext
        funext z
        change A ((γ, (sweep (1, z)).1), (sweep (1, z)).2) = R (γ, z)
        rw [sweep_homotopy_one, hRight] }

end TopCat

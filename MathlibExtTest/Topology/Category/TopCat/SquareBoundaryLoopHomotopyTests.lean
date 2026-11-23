/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.Category.TopCat.SquareBoundaryLoopHomotopy

@[expose] public section

set_option autoImplicit false

noncomputable section

open Topology
open scoped Topology.Homotopy

universe u

namespace TopCat

section Generic

variable {B : TopCat.{u}} (b : B)
variable (A : C((LoopSpace B b × unitInterval) × unitInterval, B))
variable (R : C(LoopSpace B b × unitInterval, B))
variable (hLeft : ∀ (γ : LoopSpace B b) (t : unitInterval),
  A ((γ, 0), t) = b)
variable (hRight : ∀ (γ : LoopSpace B b) (t : unitInterval),
  A ((γ, 1), t) = R (γ, t))
variable (hBottom : ∀ (γ : LoopSpace B b) (s : unitInterval),
  A ((γ, s), 0) = γ (unitInterval.symm s))
variable (hTop : ∀ (γ : LoopSpace B b) (s : unitInterval),
  A ((γ, s), 1) = b)

example : C(LoopSpace B b, LoopSpace B b) :=
  squareRightEdgeLoop b A R hRight hBottom hTop

example :
    ContinuousMap.Homotopy (ContinuousMap.id (LoopSpace B b))
      (squareRightEdgeLoop b A R hRight hBottom hTop) :=
  squareBoundaryLoopHomotopy b A R hLeft hRight hBottom hTop

example (γ : LoopSpace B b) :
    squareBoundaryLoopHomotopy b A R hLeft hRight hBottom hTop (0, γ) = γ := by
  apply ContinuousMap.Homotopy.apply_zero

example (γ : LoopSpace B b) :
    squareBoundaryLoopHomotopy b A R hLeft hRight hBottom hTop (1, γ) =
      squareRightEdgeLoop b A R hRight hBottom hTop γ := by
  apply ContinuousMap.Homotopy.apply_one

example : True := by
  fail_if_success
    have _ : ContinuousMap.Homotopy (ContinuousMap.id (LoopSpace B b))
        (squareRightEdgeLoop b A R hRight hBottom hTop) :=
      squareBoundaryLoopHomotopy b A R hRight hBottom hTop
  fail_if_success
    have _ : ContinuousMap.Homotopy (ContinuousMap.id (LoopSpace B b))
        (squareRightEdgeLoop b A R hRight hBottom hTop) :=
      squareBoundaryLoopHomotopy b A R hLeft hBottom hTop
  fail_if_success
    have _ : ContinuousMap.Homotopy (ContinuousMap.id (LoopSpace B b))
        (squareRightEdgeLoop b A R hRight hBottom hTop) :=
      squareBoundaryLoopHomotopy b A R hLeft hRight hTop
  fail_if_success
    have _ : ContinuousMap.Homotopy (ContinuousMap.id (LoopSpace B b))
        (squareRightEdgeLoop b A R hRight hBottom hTop) :=
      squareBoundaryLoopHomotopy b A R hLeft hRight hBottom
  trivial

example (Rraw : LoopSpace B b × unitInterval → B)
    (_hRightRaw : ∀ (γ : LoopSpace B b) (t : unitInterval),
      A ((γ, 1), t) = Rraw (γ, t)) : True := by
  fail_if_success
    let _ := squareBoundaryLoopHomotopy b A Rraw hLeft _hRightRaw hBottom hTop
  trivial

example (_hBottomWrong : ∀ (γ : LoopSpace B b) (s : unitInterval),
    A ((γ, s), 0) = γ s) : True := by
  fail_if_success
    let _ := squareBoundaryLoopHomotopy b A R hLeft hRight _hBottomWrong hTop
  trivial

example : True := by
  fail_if_success
    let _ := squareBoundaryLoopHomotopyEquiv b A R hLeft hRight hBottom hTop
  fail_if_success
    let _ := squareBoundaryLoopWeakEquivalence b A R hLeft hRight hBottom hTop
  fail_if_success
    let _ := squareBoundaryLoopLift b A R hLeft hRight hBottom hTop
  trivial

end Generic

section Constant

example {B : TopCat.{u}} (b : B) [Subsingleton B] :
    let A : C((LoopSpace B b × unitInterval) × unitInterval, B) :=
      ContinuousMap.const _ b
    let R : C(LoopSpace B b × unitInterval, B) := ContinuousMap.const _ b
    ContinuousMap.Homotopy (ContinuousMap.id (LoopSpace B b))
      (squareRightEdgeLoop b A R (by intros; rfl)
        (by intros; exact Subsingleton.elim _ _) (by intros; rfl)) := by
  dsimp only
  exact squareBoundaryLoopHomotopy b (ContinuousMap.const _ b)
    (ContinuousMap.const _ b) (by intros; rfl) (by intros; rfl)
    (by intros; exact Subsingleton.elim _ _) (by intros; rfl)

end Constant

section UniverseOne

example {B : TopCat.{1}} (b : B)
    (A : C((LoopSpace B b × unitInterval) × unitInterval, B))
    (R : C(LoopSpace B b × unitInterval, B))
    (hLeft : ∀ (γ : LoopSpace B b) (t : unitInterval), A ((γ, 0), t) = b)
    (hRight : ∀ (γ : LoopSpace B b) (t : unitInterval),
      A ((γ, 1), t) = R (γ, t))
    (hBottom : ∀ (γ : LoopSpace B b) (s : unitInterval),
      A ((γ, s), 0) = γ (unitInterval.symm s))
    (hTop : ∀ (γ : LoopSpace B b) (s : unitInterval), A ((γ, s), 1) = b) :
    ContinuousMap.Homotopy (ContinuousMap.id (LoopSpace B b))
      (squareRightEdgeLoop b A R hRight hBottom hTop) :=
  squareBoundaryLoopHomotopy b A R hLeft hRight hBottom hTop

end UniverseOne

section UniverseZero

example {B : TopCat.{0}} (b : B)
    (A : C((LoopSpace B b × unitInterval) × unitInterval, B))
    (R : C(LoopSpace B b × unitInterval, B))
    (hLeft : ∀ (γ : LoopSpace B b) (t : unitInterval), A ((γ, 0), t) = b)
    (hRight : ∀ (γ : LoopSpace B b) (t : unitInterval),
      A ((γ, 1), t) = R (γ, t))
    (hBottom : ∀ (γ : LoopSpace B b) (s : unitInterval),
      A ((γ, s), 0) = γ (unitInterval.symm s))
    (hTop : ∀ (γ : LoopSpace B b) (s : unitInterval), A ((γ, s), 1) = b) :
    ContinuousMap.Homotopy (ContinuousMap.id (LoopSpace B b))
      (squareRightEdgeLoop b A R hRight hBottom hTop) :=
  squareBoundaryLoopHomotopy b A R hLeft hRight hBottom hTop

end UniverseZero

#check squareRightEdgeLoop
#check squareBoundaryLoopHomotopy

#print axioms squareRightEdgeLoop
#print axioms squareBoundaryLoopHomotopy

end TopCat

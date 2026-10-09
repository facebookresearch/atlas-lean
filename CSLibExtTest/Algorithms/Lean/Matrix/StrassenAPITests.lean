/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.Matrix.Strassen

/-!
# Ordinary-import Strassen API tests

The executor and exact time theorem need only the four scalar operations; the
pointwise and canonical Matrix results need a nonunital, nonassociative ring.
-/

set_option autoImplicit false

universe u

open Cslib.Algorithms.Lean.TimeM
open Cslib.Algorithms.Lean.Matrix

example {R : Type u} [Zero R] [Add R] [Sub R] [Mul R] :
    (k : Nat) → Vector (Vector R (2 ^ k)) (2 ^ k) →
      Vector (Vector R (2 ^ k)) (2 ^ k) → Vector (Vector R (2 ^ k)) (2 ^ k) →
        Cslib.Algorithms.Lean.TimeM (Nat × Nat) (Vector (Vector R (2 ^ k)) (2 ^ k)) :=
  strassenMatrixAccumulate

example {R : Type u} [Zero R] [Add R] [Sub R] [Mul R] (k : Nat)
    (A B C : Vector (Vector R (2 ^ k)) (2 ^ k)) :
    (strassenMatrixAccumulate k A B C).time =
      (7 ^ k, (25 * 7 ^ k - 22 * 4 ^ k) / 3) :=
  strassenMatrixAccumulate_time k A B C

example {R : Type u} [NonUnitalNonAssocRing R] (k : Nat)
    (A B C : Vector (Vector R (2 ^ k)) (2 ^ k)) (i j : Fin (2 ^ k)) :
    ((strassenMatrixAccumulate k A B C).ret.get i).get j =
      (C.get i).get j + ∑ t : Fin (2 ^ k), (A.get i).get t * (B.get t).get j :=
  strassenMatrixAccumulate_apply k A B C i j

example {R : Type u} [NonUnitalNonAssocRing R] (k : Nat)
    (A B C : Vector (Vector R (2 ^ k)) (2 ^ k)) :
    (Matrix.of fun i j => ((strassenMatrixAccumulate k A B C).ret.get i).get j) =
      (Matrix.of fun i j => (C.get i).get j) +
        (Matrix.of fun i j => (A.get i).get j) * (Matrix.of fun i j => (B.get i).get j) :=
  strassenMatrixAccumulate_ret k A B C

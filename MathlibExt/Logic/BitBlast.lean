/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Bool.Basic

/-!
# Bit-blasting core laws

Fixed-width bit-vectors are modeled as bit functions
`Fin n → Bool`, with bitwise operations pointwise. This module
proves the basic pointwise laws (commutativity, idempotence,
De Morgan) that a bit-blasting translation to SAT must
preserve. The `BitVec` and SAT encodings are not formalized
here.
-/

@[expose] public section

/-- Fixed-width bit-vectors as bit functions (core of VER-11
bit-blasting). Width is implicit in the index type `Fin n`. -/
def BV (n : ℕ) := Fin n → Bool

/-- Bitwise AND, pointwise. -/
def bvAnd {n : ℕ} (a b : BV n) : BV n := fun i => a i && b i

/-- Bitwise OR, pointwise. -/
def bvOr {n : ℕ} (a b : BV n) : BV n := fun i => a i || b i

/-- Bitwise NOT, pointwise. -/
def bvNot {n : ℕ} (a : BV n) : BV n := fun i => !(a i)

/-- AND is commutative. -/
theorem bvAnd_comm {n : ℕ} (a b : BV n) : bvAnd a b = bvAnd b a := by
  funext i
  simp only [bvAnd, Bool.and_comm]

/-- AND is idempotent. -/
theorem bvAnd_self {n : ℕ} (a : BV n) : bvAnd a a = a := by
  funext i
  simp only [bvAnd, Bool.and_self]

/-- De Morgan: NOT (a AND b) = (NOT a) OR (NOT b). -/
theorem bvNot_and {n : ℕ} (a b : BV n) :
    bvNot (bvAnd a b) = bvOr (bvNot a) (bvNot b) := by
  funext i
  simp only [bvNot, bvAnd, bvOr, Bool.not_and]

/-- Bit-level characterization of AND. -/
theorem bvAnd_apply {n : ℕ} (a b : BV n) (i : Fin n) :
    bvAnd a b i = (a i && b i) := by
  rfl

end

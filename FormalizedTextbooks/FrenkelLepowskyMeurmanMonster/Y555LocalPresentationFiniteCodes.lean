/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Exact finite integer encodings and sorted injectivity certificates for source matrix images. -/
module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Order.Fin.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- An exact base-three integer encoding of the 49 entries of a finite source image matrix. -/
def y322Orthogonal3MatrixCode (matrix : Matrix (Fin 7) (Fin 7) (ZMod 3)) : ℕ :=
  ∑ r : Fin 7, ∑ c : Fin 7, (matrix r c).val * 3 ^ (r.val * 7 + c.val)

/-- A sorted finite encoding and an explicitly checked inverse position give injective labels. -/
theorem y322SortedFiniteCode_injective {n : ℕ} (sorted : Fin (n + 1) → ℕ)
    (position inverse : Fin (n + 1) → Fin (n + 1)) (mono : StrictMono sorted)
    (hinverse : ∀ i, inverse (position i) = i) :
    Function.Injective (fun i => sorted (position i)) := by
  intro i j h
  have hp := congrArg inverse (mono.injective h)
  simpa only [hinverse] using hp

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

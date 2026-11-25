/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import MathlibExt.LinearAlgebra.Matrix.Stable

/-! Public clients for the actual stable algebra and its finite-support coordinates. -/

@[expose] public section

noncomputable section

open scoped BigOperators

universe u v

variable (k : Type u) [CommRing k] (A : Type v) [NonUnitalRing A] [Module k A]

/-- Products retain their values when the two finite generators are enlarged. -/
example {n m : ℕ} (h : n ≤ m) (B C : Matrix (Fin n) (Fin n) A) :
    Matrix.Stable.ofFinite k A n B * Matrix.Stable.ofFinite k A n C =
      Matrix.Stable.ofFinite k A m (Matrix.zeroExtend h B * Matrix.zeroExtend h C) := by
  rw [← Matrix.Stable.ofFinite_zeroExtend k A h B,
    ← Matrix.Stable.ofFinite_zeroExtend k A h C, Matrix.Stable.mul_ofFinite]

/-- Product coordinates through the promoted equivalence preserve noncommutative order. -/
example (n : ℕ) (B C : Matrix (Fin n) (Fin n) A) (i j : Fin n) :
    Matrix.Stable.finsuppEquiv k A
        (Matrix.Stable.ofFinite k A n B * Matrix.Stable.ofFinite k A n C) (i.val, j.val) =
      ∑ p : Fin n, B i p * C p j :=
  (Matrix.Stable.finsuppEquiv_apply k A _ (i.val, j.val)).trans
    (Matrix.Stable.mul_entries_ofFinite k A n B C i j)

/-- The coordinate equivalence and the entry map describe the same finite support. -/
example (x : Matrix.Stable k A) :
    (Function.support (fun p : ℕ × ℕ => Matrix.Stable.finsuppEquiv k A x p)).Finite := by
  simpa only [Matrix.Stable.finsuppEquiv_apply] using
    Matrix.Stable.entries_finiteSupport k A x

/-- Included matrices have zero coordinates outside their actual finite square. -/
example (n : ℕ) (B : Matrix (Fin n) (Fin n) A) (i j : ℕ) (h : n ≤ i ∨ n ≤ j) :
    Matrix.Stable.finsuppEquiv k A (Matrix.Stable.ofFinite k A n B) (i, j) = 0 := by
  rw [Matrix.Stable.finsuppEquiv_apply, Matrix.Stable.entries_ofFinite]
  rcases h with hi | hj
  · rw [dite_eq_right (Nat.not_lt.mpr hi)]
  · by_cases hi : i < n
    · rw [dite_eq_left hi, dite_eq_right (Nat.not_lt.mpr hj)]
    · rw [dite_eq_right hi]

/-- The size-zero boundary is the genuine empty matrix stage. -/
example (B : Matrix (Fin 0) (Fin 0) A) : Matrix.Stable.ofFinite k A 0 B = 0 := by
  have hB : B = 0 := by
    funext i j
    exact Fin.elim0 i
  rw [hB, map_zero]

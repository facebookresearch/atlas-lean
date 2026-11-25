/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import Domains.Chemistry.Diffraction.CubicPlaneSpacing
import Mathlib.Algebra.Ring.Parity
import Mathlib.Data.Int.GCD
import Mathlib.Tactic.NormNum

/-! # Tests for simple cubic plane spacing and occupancy -/

open Chemistry.Diffraction
open scoped BigOperators

private abbrev cubicPlane (a : ℝ) (h : Fin 3 → ℤ) (m : ℤ) : Set (EuclideanSpace ℝ (Fin 3)) :=
  {x | ∑ i, (h i : ℝ) * x i = (m : ℝ) * a}

private abbrev cubicLattice (a : ℝ) : Set (EuclideanSpace ℝ (Fin 3)) :=
  Set.range fun z : Fin 3 → ℤ => WithLp.toLp 2 (fun i => a * (z i : ℝ))

-- A mixed-sign normal of length 3 at negative levels; test attainment and the lower bound.
example {a : ℝ} (ha : 0 < a) :
    (∃ x ∈ cubicPlane a ![-1, 2, 2] (-2), ∃ y ∈ cubicPlane a ![-1, 2, 2] (-1), dist x y = a / 3) ∧
      (∀ x ∈ cubicPlane a ![-1, 2, 2] (-2), ∀ y ∈ cubicPlane a ![-1, 2, 2] (-1), a / 3 ≤ dist x y) := by
  have hs : Real.sqrt ((-1 : ℝ) ^ 2 + 2 ^ 2 + 2 ^ 2) = 3 := by
    rw [show (-1 : ℝ) ^ 2 + 2 ^ 2 + 2 ^ 2 = 3 ^ 2 by norm_num,
      Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 3)]
  have hd : IsLeast (Set.image2 dist (cubicPlane a ![-1, 2, 2] (-2))
      (cubicPlane a ![-1, 2, 2] (-1))) (a / 3) := by
    simpa only [cubicPlane, show (-2 : ℤ) + 1 = -1 by decide, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons, Int.cast_neg,
      Int.cast_one, Int.cast_ofNat, hs] using
      (cubic_plane_spacing_and_occupancy ha).1 ![-1, 2, 2] (by decide) (-2)
  exact ⟨Set.mem_image2.mp hd.1, fun _ hx _ hy => hd.2 (Set.mem_image2_of_mem hx hy)⟩

-- No pair is coprime, but the gcd of all three indices is 1.
example {a : ℝ} (ha : 0 < a) (m : ℤ) :
    (cubicPlane a ![-6, 10, 15] m ∩ cubicLattice a).Nonempty :=
  ((cubic_plane_spacing_and_occupancy ha).2.2.1 ![-6, 10, 15]).2 (by decide) m

-- A different nonprimitive triple, including a negative index.
example {a : ℝ} (ha : 0 < a) (m : ℤ) :
    (cubicPlane a ![-6, 10, 0] m ∩ cubicLattice a).Nonempty ↔ (2 : ℤ) ∣ m := by
  have hd := (cubic_plane_spacing_and_occupancy ha).2.1 ![-6, 10, 0] m
  change _ ↔ (Int.gcd (Int.gcd (-6) 10 : ℤ) 0 : ℤ) ∣ m at hd
  rw [show Int.gcd (Int.gcd (-6) 10 : ℤ) 0 = 2 by decide] at hd
  exact hd

-- For (2,0,0) the geometric spacing is a/2, even next to an empty level.
example {a : ℝ} (ha : 0 < a) (m : ℤ) :
    IsLeast (Set.image2 dist (cubicPlane a ![2, 0, 0] m) (cubicPlane a ![2, 0, 0] (m + 1)))
      (a / 2) := by
  have hs : Real.sqrt ((2 : ℝ) ^ 2 + 0 ^ 2 + 0 ^ 2) = 2 := by
    simpa only [zero_pow (by decide : 2 ≠ 0), add_zero] using
      Real.sqrt_sq (zero_le_two : (0 : ℝ) ≤ 2)
  simpa only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.tail_cons,
    Matrix.head_cons, Int.cast_ofNat, Int.cast_zero, hs] using
    (cubic_plane_spacing_and_occupancy ha).1 ![2, 0, 0] (by decide) m

-- Consecutive even levels are occupied, there is no occupied level between them, and their
-- spacing is a.
example {a : ℝ} (ha : 0 < a) (m : ℤ) :
    (cubicPlane a ![2, 0, 0] (2 * m) ∩ cubicLattice a).Nonempty ∧
      (cubicPlane a ![2, 0, 0] (2 * (m + 1)) ∩ cubicLattice a).Nonempty ∧
      (∀ k : ℤ, 2 * m < k → k < 2 * (m + 1) →
        ¬ (cubicPlane a ![2, 0, 0] k ∩ cubicLattice a).Nonempty) ∧
      IsLeast (Set.image2 dist (cubicPlane a ![2, 0, 0] (2 * m))
        (cubicPlane a ![2, 0, 0] (2 * (m + 1)))) a := by
  obtain ⟨heven, hspacing⟩ := (cubic_plane_spacing_and_occupancy ha).2.2.2
  refine ⟨(heven _).2 ⟨m, by omega⟩, (heven _).2 ⟨m + 1, by omega⟩, ?_, hspacing m⟩
  intro k hlo hhi hk
  exact (Int.not_even_iff_odd.mpr ⟨m, by omega⟩) ((heven k).1 hk)

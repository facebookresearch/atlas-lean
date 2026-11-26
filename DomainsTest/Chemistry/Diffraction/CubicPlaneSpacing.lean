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

open Chemistry.Diffraction Crystallography.BravaisLattice

variable {a : ℝ} (ha : 0 < a)

local notation "Λ" => simpleCubic a ha

-- A mixed-sign normal of length 3 at negative levels; test attainment and the lower bound.
example :
    (∃ x ∈ latticePlane Λ ![-1, 2, 2] (-2), ∃ y ∈ latticePlane Λ ![-1, 2, 2] (-1),
      dist x y = a / 3) ∧
    (∀ x ∈ latticePlane Λ ![-1, 2, 2] (-2), ∀ y ∈ latticePlane Λ ![-1, 2, 2] (-1),
      a / 3 ≤ dist x y) := by
  have hs : Real.sqrt ((-1 : ℝ) ^ 2 + 2 ^ 2 + 2 ^ 2) = 3 := by
    rw [show (-1 : ℝ) ^ 2 + 2 ^ 2 + 2 ^ 2 = 3 ^ 2 by norm_num,
      Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 3)]
  have hd : IsLeast (Set.image2 dist (latticePlane Λ ![-1, 2, 2] (-2))
      (latticePlane Λ ![-1, 2, 2] (-1))) (a / 3) := by
    simpa only [show (-2 : ℤ) + 1 = -1 by decide, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons, Int.cast_neg, Int.cast_one,
      Int.cast_ofNat, hs] using
      (cubic_plane_spacing_and_occupancy ha).1 ![-1, 2, 2] (by decide) (-2)
  exact ⟨Set.mem_image2.mp hd.1, fun _ hx _ hy => hd.2 (Set.mem_image2_of_mem hx hy)⟩

-- No pair is coprime, but the gcd of all three indices is 1.
example (m : ℤ) : (latticePlane Λ ![-6, 10, 15] m ∩ (lattice Λ : Set _)).Nonempty :=
  ((cubic_plane_spacing_and_occupancy ha).2.2.1 ![-6, 10, 15]).2 (by decide) m

-- A different nonprimitive triple, including a negative index.
example (m : ℤ) :
    (latticePlane Λ ![-6, 10, 0] m ∩ (lattice Λ : Set _)).Nonempty ↔ (2 : ℤ) ∣ m := by
  have hd := (cubic_plane_spacing_and_occupancy ha).2.1 ![-6, 10, 0] m
  change _ ↔ (Int.gcd (Int.gcd (-6) 10 : ℤ) 0 : ℤ) ∣ m at hd
  rw [show Int.gcd (Int.gcd (-6) 10 : ℤ) 0 = 2 by decide] at hd
  exact hd

-- For (2,0,0) the geometric spacing is a/2, even next to an empty level.
example (m : ℤ) :
    IsLeast (Set.image2 dist (latticePlane Λ ![2, 0, 0] m) (latticePlane Λ ![2, 0, 0] (m + 1)))
      (a / 2) := by
  have hs : Real.sqrt ((2 : ℝ) ^ 2 + 0 ^ 2 + 0 ^ 2) = 2 := by
    simpa only [zero_pow (by decide : 2 ≠ 0), add_zero] using
      Real.sqrt_sq (zero_le_two : (0 : ℝ) ≤ 2)
  simpa only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.tail_cons,
    Matrix.head_cons, Int.cast_ofNat, Int.cast_zero, hs] using
    (cubic_plane_spacing_and_occupancy ha).1 ![2, 0, 0] (by decide) m

-- Consecutive even levels are occupied, there is no occupied level between them, and their
-- spacing is a.
example (m : ℤ) :
    (latticePlane Λ ![2, 0, 0] (2 * m) ∩ (lattice Λ : Set _)).Nonempty ∧
      (latticePlane Λ ![2, 0, 0] (2 * (m + 1)) ∩ (lattice Λ : Set _)).Nonempty ∧
      (∀ k : ℤ, 2 * m < k → k < 2 * (m + 1) →
        ¬ (latticePlane Λ ![2, 0, 0] k ∩ (lattice Λ : Set _)).Nonempty) ∧
      IsLeast (Set.image2 dist (latticePlane Λ ![2, 0, 0] (2 * m))
        (latticePlane Λ ![2, 0, 0] (2 * (m + 1)))) a := by
  obtain ⟨heven, hspacing⟩ := (cubic_plane_spacing_and_occupancy ha).2.2.2
  refine ⟨(heven _).2 ⟨m, by omega⟩, (heven _).2 ⟨m + 1, by omega⟩, ?_, hspacing m⟩
  intro k hlo hhi hk
  exact (Int.not_even_iff_odd.mpr ⟨m, by omega⟩) ((heven k).1 hk)

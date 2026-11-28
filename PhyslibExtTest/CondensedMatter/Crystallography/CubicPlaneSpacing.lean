/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import PhyslibExt.CondensedMatter.Crystallography.CubicPlaneSpacing
import Mathlib.Algebra.Ring.Parity
import Mathlib.Tactic.NormNum

/-! # Tests for plane spacing and occupancy -/

open Crystallography.BravaisLattice

/-! ## A. Bravais lattice levels -/

variable (Λ : Crystallography.BravaisLattice)

-- The geometric minimum is attained at negative levels independently of the lattice metric.
example : ∃ x ∈ Λ.latticePlane ![-1, 2, 2] (-2), ∃ y ∈ Λ.latticePlane ![-1, 2, 2] (-1),
    dist x y = Λ.interplanarSpacing ![-1, 2, 2] := by
  have hd := Λ.latticePlane_isLeast_dist ![-1, 2, 2] (by decide) (-2)
  exact Set.mem_image2.mp hd.1

-- No pair is coprime, but the gcd of all three indices is 1.
example (m : ℤ) : (Λ.latticePlane ![-6, 10, 15] m ∩ (Λ.lattice : Set _)).Nonempty :=
  (Λ.latticePlane_all_occupied_iff_primitive ![-6, 10, 15]).mpr (by decide) m

-- A different nonprimitive triple, including a negative index.
example (m : ℤ) :
    (Λ.latticePlane ![-6, 10, 0] m ∩ (Λ.lattice : Set _)).Nonempty ↔ (2 : ℤ) ∣ m := by
  rw [Λ.latticePlane_occupied_iff_dvd, show millerIndexGCD ![-6, 10, 0] = 2 by decide]
  rfl

-- With the zero normal, only the zero level is occupied.
example (m : ℤ) : (Λ.latticePlane 0 m ∩ (Λ.lattice : Set _)).Nonempty ↔ m = 0 := by
  rw [Λ.latticePlane_occupied_iff_dvd, show millerIndexGCD 0 = 0 by decide, Nat.cast_zero,
    zero_dvd_iff]

/-! ## B. Simple cubic spacing -/

variable {a : ℝ} (ha : 0 < a)

local notation "L" => simpleCubic a ha

-- A mixed-sign normal of length 3 at negative levels; test attainment and the lower bound.
example :
    (∃ x ∈ (L).latticePlane ![-1, 2, 2] (-2), ∃ y ∈ (L).latticePlane ![-1, 2, 2] (-1),
      dist x y = a / 3) ∧
    (∀ x ∈ (L).latticePlane ![-1, 2, 2] (-2), ∀ y ∈ (L).latticePlane ![-1, 2, 2] (-1),
      a / 3 ≤ dist x y) := by
  have hs : Real.sqrt ((-1 : ℝ) ^ 2 + 2 ^ 2 + 2 ^ 2) = 3 := by
    rw [show (-1 : ℝ) ^ 2 + 2 ^ 2 + 2 ^ 2 = 3 ^ 2 by norm_num,
      Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 3)]
  have hd : IsLeast (Set.image2 dist ((L).latticePlane ![-1, 2, 2] (-2))
      ((L).latticePlane ![-1, 2, 2] (-1))) (a / 3) := by
    simpa only [show (-2 : ℤ) + 1 = -1 by decide, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons, Int.cast_neg, Int.cast_one,
      Int.cast_ofNat, hs] using
      latticePlane_isLeast_dist_simpleCubic ha ![-1, 2, 2] (by decide) (-2)
  exact ⟨Set.mem_image2.mp hd.1, fun _ hx _ hy => hd.2 (Set.mem_image2_of_mem hx hy)⟩

-- For (2,0,0) the geometric spacing is a/2, even next to an empty level.
example (m : ℤ) :
    IsLeast (Set.image2 dist ((L).latticePlane ![2, 0, 0] m) ((L).latticePlane ![2, 0, 0] (m + 1)))
      (a / 2) := by
  have hs : Real.sqrt ((2 : ℝ) ^ 2 + 0 ^ 2 + 0 ^ 2) = 2 := by
    simpa only [zero_pow (by decide : 2 ≠ 0), add_zero] using
      Real.sqrt_sq (zero_le_two : (0 : ℝ) ≤ 2)
  simpa only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.tail_cons,
    Matrix.head_cons, Int.cast_ofNat, Int.cast_zero, hs] using
    latticePlane_isLeast_dist_simpleCubic ha ![2, 0, 0] (by decide) m

-- Consecutive even levels are occupied, there is no occupied level between them, and their
-- spacing is a.
example (m : ℤ) :
    ((L).latticePlane ![2, 0, 0] (2 * m) ∩ ((L).lattice : Set _)).Nonempty ∧
      ((L).latticePlane ![2, 0, 0] (2 * (m + 1)) ∩ ((L).lattice : Set _)).Nonempty ∧
      (∀ k : ℤ, 2 * m < k → k < 2 * (m + 1) →
        ¬ ((L).latticePlane ![2, 0, 0] k ∩ ((L).lattice : Set _)).Nonempty) ∧
      IsLeast (Set.image2 dist ((L).latticePlane ![2, 0, 0] (2 * m))
        ((L).latticePlane ![2, 0, 0] (2 * (m + 1)))) a := by
  refine ⟨((L).latticePlane_200_occupied_iff_even _).mpr ⟨m, by omega⟩,
    ((L).latticePlane_200_occupied_iff_even _).mpr ⟨m + 1, by omega⟩, ?_,
    interplanarSpacing_cubic_200_occupied ha m⟩
  intro k hlo hhi hk
  exact (Int.not_even_iff_odd.mpr ⟨m, by omega⟩) (((L).latticePlane_200_occupied_iff_even k).mp hk)

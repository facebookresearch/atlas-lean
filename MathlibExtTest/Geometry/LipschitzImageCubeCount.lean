/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


/-
Ported from fairinternal/formal-math `MathlibExtTest/Geometry/LipschitzImageCubeCount.lean`
at commit 5971cd008f11196e18b863495ddad4501d3e5585.
The test statements and proofs are retained; only the Atlas adapter
import prefix is removed for the native ATLAS module identities.
-/

module

import Mathlib.Data.Set.Card
import MathlibExt.Geometry.LipschitzImageCubeCount

/-!
# Tests for Lipschitz image cube counts

Concrete checks for `LipschitzImageCubeCount`:

- The constant zero map on the 0-dimensional cube meets exactly one integer
  cube (exact one-element count).
- The 1D identity parametrization at `t = 1` meets exactly the integer cubes
  indexed by `0` and `1` under the half-open convention (genuine membership,
  nonmembership, exact set, and exact count).
- Direct uses of the finiteness, cardinality, and `O(t ^ d)` API.
-/

open LipschitzImageCubeCount

open scoped NNReal

/-- Constant zero map out of the 0-dimensional cube. -/
def constZeroCube : ↥(unitCube 0) → (Fin 1 → ℝ) := fun _ _ => 0

/-- The 1D identity parametrization. -/
def identCube : ↥(unitCube 1) → (Fin 1 → ℝ) := fun y _ => y.val 0

/-- The identity parametrization is 1-Lipschitz. -/
theorem lip_identCube : LipschitzWith 1 identCube := by
  apply LipschitzWith.mk_one
  intro y y'
  change dist (identCube y) (identCube y') ≤ dist y.val y'.val
  rw [dist_pi_le_iff dist_nonneg]
  intro i
  have hi : i = 0 := Subsingleton.elim _ _
  subst hi
  change dist (y.val 0) (y'.val 0) ≤ dist y.val y'.val
  exact dist_le_pi_dist _ _ 0

/-- The constant vector `1` lies in the 1-dimensional unit cube. -/
theorem one_mem_unitCube1 : (1 : Fin 1 → ℝ) ∈ unitCube 1 := by
  change (1 : Fin 1 → ℝ) ∈ Set.Icc 0 1
  refine Set.mem_Icc.mpr ⟨?_, ?_⟩
  · intro i
    change (0 : ℝ) ≤ 1
    exact zero_le_one
  · exact le_rfl

/-- Exact set: the constant zero map on the 0-cube meets only cube `0`. -/
theorem constZeroCube_set :
    integerCubeSet constZeroCube 1 = {fun _ => (0 : ℤ)} := by
  ext v
  simp only [mem_integerCubeSet_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨y, hy⟩
    have h1 := hy 0
    have e : (1 : ℝ) * (constZeroCube y) 0 = 0 := by simp [constZeroCube]
    rw [e] at h1
    have hlo : v 0 ≤ 0 := by exact_mod_cast h1.1
    have hhi : (-1 : ℤ) < v 0 := by
      have h : (-1 : ℝ) < (v 0 : ℝ) := by linarith [h1.2]
      exact_mod_cast h
    have hv0 : v 0 = 0 := by omega
    funext i
    have hi : i = 0 := Subsingleton.elim _ _
    subst hi
    simpa using hv0
  · intro h
    rw [h]
    refine ⟨⟨0, unitCube_zero_mem 0⟩, fun i => ?_⟩
    have hi : i = 0 := Subsingleton.elim _ _
    subst hi
    norm_num [constZeroCube]

/-- Exact one-element count for the constant zero map on the 0-cube. -/
example : Nat.card (integerCubeSet constZeroCube 1) = 1 := by
  rw [constZeroCube_set, Nat.card_coe_set_eq, Set.ncard_singleton]

/-- Membership: cube `0` meets the 1D identity image at `t = 1`. -/
example : (fun _ => (0 : ℤ)) ∈ integerCubeSet identCube 1 := by
  refine ⟨⟨0, unitCube_zero_mem 1⟩, fun i => ?_⟩
  have hi : i = 0 := Subsingleton.elim _ _
  subst hi
  norm_num [identCube]

/-- Membership: cube `1` meets the 1D identity image at `t = 1`. -/
example : (fun _ => (1 : ℤ)) ∈ integerCubeSet identCube 1 := by
  refine ⟨⟨1, one_mem_unitCube1⟩, fun i => ?_⟩
  have hi : i = 0 := Subsingleton.elim _ _
  subst hi
  norm_num [identCube]

/-- Nonmembership: cube `2` does not meet the 1D identity image at `t = 1`. -/
example : (fun _ => (2 : ℤ)) ∉ integerCubeSet identCube 1 := by
  rw [mem_integerCubeSet_iff]
  rintro ⟨y, hy⟩
  have hmem : (0 : Fin 1 → ℝ) ≤ y.val ∧ y.val ≤ 1 :=
    Set.mem_Icc.mp y.property
  have hle : y.val 0 ≤ 1 := hmem.2 0
  have h1 := hy 0
  have e2 : (((fun _ => (2 : ℤ)) 0 : ℤ) : ℝ) = 2 := by norm_num
  have eid : (identCube y) 0 = y.val 0 := rfl
  rw [e2, eid, one_mul] at h1
  linarith

/-- Nonmembership: cube `-1` does not meet the 1D identity image at `t = 1`. -/
example : (fun _ => (-1 : ℤ)) ∉ integerCubeSet identCube 1 := by
  rw [mem_integerCubeSet_iff]
  rintro ⟨y, hy⟩
  have hmem : (0 : Fin 1 → ℝ) ≤ y.val ∧ y.val ≤ 1 :=
    Set.mem_Icc.mp y.property
  have hlo : 0 ≤ y.val 0 := hmem.1 0
  have h1 := hy 0
  have em1 : (((fun _ => (-1 : ℤ)) 0 : ℤ) : ℝ) = -1 := by norm_num
  have eid : (identCube y) 0 = y.val 0 := rfl
  rw [em1, eid, one_mul] at h1
  linarith

/-- Exact set: at `t = 1` the 1D identity meets precisely cubes `0` and `1`. -/
theorem identCube_set :
    integerCubeSet identCube 1 = {fun _ => (0 : ℤ), fun _ => (1 : ℤ)} := by
  ext v
  simp only [mem_integerCubeSet_iff, Set.mem_insert_iff,
    Set.mem_singleton_iff]
  constructor
  · rintro ⟨y, hy⟩
    have hmem : (0 : Fin 1 → ℝ) ≤ y.val ∧ y.val ≤ 1 :=
      Set.mem_Icc.mp y.property
    have hlo : 0 ≤ y.val 0 := hmem.1 0
    have hhi : y.val 0 ≤ 1 := hmem.2 0
    have h1 := hy 0
    have eid : (identCube y) 0 = y.val 0 := rfl
    rw [eid, one_mul] at h1
    have hlo' : (0 : ℤ) ≤ v 0 := by
      have h : (-1 : ℝ) < (v 0 : ℝ) := by linarith [h1.2, hlo]
      have h' : (-1 : ℤ) < v 0 := by exact_mod_cast h
      omega
    have hhi' : v 0 ≤ 1 := by
      have h : (v 0 : ℝ) ≤ 1 := by linarith [h1.2, hhi]
      exact_mod_cast h
    have hv0 : v 0 = 0 ∨ v 0 = 1 := by omega
    have hfun : ∀ i : Fin 1, v i = v 0 := fun i => by
      have hi : i = 0 := Subsingleton.elim _ _
      rw [hi]
    rcases hv0 with h0 | h1'
    · left
      funext i
      rw [hfun i, h0]
    · right
      funext i
      rw [hfun i, h1']
  · rintro (rfl | rfl)
    · refine ⟨⟨0, unitCube_zero_mem 1⟩, fun i => ?_⟩
      have hi : i = 0 := Subsingleton.elim _ _
      subst hi
      norm_num [identCube]
    · refine ⟨⟨1, one_mem_unitCube1⟩, fun i => ?_⟩
      have hi : i = 0 := Subsingleton.elim _ _
      subst hi
      norm_num [identCube]

/-- Exact two-element count for the 1D identity at `t = 1`. -/
example : Nat.card (integerCubeSet identCube 1) = 2 := by
  rw [identCube_set, Nat.card_coe_set_eq]
  apply Set.ncard_pair
  decide

/-- Direct use of the finiteness API. -/
example : Set.Finite (integerCubeSet identCube 2) :=
  finite_integerCubeSet identCube 1 lip_identCube 2 (by norm_num)

/-- Direct use of the cardinality API at a concrete parameter. -/
example : Nat.card (integerCubeSet identCube 2) ≤
    ⌈(2 : ℝ)⌉₊ ^ 1 *
      (2 * ⌈((1 : ℝ≥0) : ℝ) * Real.sqrt ((1 : ℕ) : ℝ)⌉₊ + 3) ^ 1 :=
  card_integerCubeSet_le identCube 1 lip_identCube 2 (by norm_num)

/-- Direct use of the `O(t ^ d)` API at a concrete parameter. -/
example : ∃ C : ℝ, 0 < C ∧
    (Nat.card (integerCubeSet identCube 2) : ℝ) ≤ C * 2 ^ 1 := by
  obtain ⟨C, hCpos, hC⟩ :=
    exists_cubeCount_le_const_mul_pow identCube 1 lip_identCube
  exact ⟨C, hCpos, hC 2 (by norm_num)⟩

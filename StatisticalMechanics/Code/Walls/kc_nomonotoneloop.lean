/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






























































import Mathlib
import Code.Lattice.EnclosedAreaWitness

open scoped BigOperators
open Finset

namespace StatMech.Walls







theorem kc_abs_diff_one (g : ℕ → ℤ) (i : ℕ) :
    |g (i + 1) - g i| = 1 ↔ (g (i + 1) = g i + 1 ∨ g (i + 1) = g i - 1) := by
  rw [abs_eq (by norm_num : (0 : ℤ) ≤ 1)]; omega












theorem kc_max_neighbours_eq (g : ℕ → ℤ) (L : ℕ)
    (hstep : ∀ i, i < L → g (i + 1) = g i + 1 ∨ g (i + 1) = g i - 1)
    {m : ℕ} (hm0 : 0 < m) (hmL : m < L)
    (hmmax : ∀ i, i ≤ L → g i ≤ g m) :
    g (m - 1) = g (m + 1) := by
  have hs1 := hstep (m - 1) (by omega)
  have hs2 := hstep m (by omega)
  rw [show m - 1 + 1 = m by omega] at hs1
  have hle1 : g (m - 1) ≤ g m := hmmax (m - 1) (by omega)
  have hle2 : g (m + 1) ≤ g m := hmmax (m + 1) (by omega)
  omega




theorem kc_min_neighbours_eq (g : ℕ → ℤ) (L : ℕ)
    (hstep : ∀ i, i < L → g (i + 1) = g i + 1 ∨ g (i + 1) = g i - 1)
    {m : ℕ} (hm0 : 0 < m) (hmL : m < L)
    (hmmin : ∀ i, i ≤ L → g m ≤ g i) :
    g (m - 1) = g (m + 1) := by
  have hs1 := hstep (m - 1) (by omega)
  have hs2 := hstep m (by omega)
  rw [show m - 1 + 1 = m by omega] at hs1
  have hle1 : g m ≤ g (m - 1) := hmmin (m - 1) (by omega)
  have hle2 : g m ≤ g (m + 1) := hmmin (m + 1) (by omega)
  omega













theorem kc_no_monotone_loop (g : ℕ → ℤ) (L : ℕ) (h3 : 3 ≤ L)
    (hloop : g 0 = g L)
    (hstep : ∀ i, i < L → g (i + 1) = g i + 1 ∨ g (i + 1) = g i - 1)
    (hne : g 1 ≠ g 0)
    (hinj : Set.InjOn g {i | i ≤ L - 1}) : False := by
  classical
  obtain ⟨k, hkmem, hkmax⟩ := Finset.exists_max_image (Finset.range (L + 1)) g
    ⟨0, Finset.mem_range.mpr (by omega)⟩
  obtain ⟨j, hjmem, hjmin⟩ := Finset.exists_min_image (Finset.range (L + 1)) g
    ⟨0, Finset.mem_range.mpr (by omega)⟩
  rw [Finset.mem_range] at hkmem hjmem
  
  have hkmax' : ∀ i, i ≤ L → g i ≤ g k := fun i hi => hkmax i (Finset.mem_range.mpr (by omega))
  have hjmin' : ∀ i, i ≤ L → g j ≤ g i := fun i hi => hjmin i (Finset.mem_range.mpr (by omega))
  
  have machine : ∀ m, m ≤ L → (∀ i, i ≤ L → g i ≤ g m) → 0 < m → m < L → False := by
    intro m hmL hmmax hm0 hmL'
    have hneq : g (m - 1) = g (m + 1) := kc_max_neighbours_eq g L hstep hm0 hmL' hmmax
    by_cases hmp : m + 1 ≤ L - 1
    · have : (m - 1) = (m + 1) := hinj (by simp only [Set.mem_setOf_eq]; omega)
        (by simp only [Set.mem_setOf_eq]; omega) hneq
      omega
    · 
      have hmpL : m + 1 = L := by omega
      have : g (m - 1) = g 0 := by rw [hneq, hmpL, ← hloop]
      have : (m - 1) = 0 := hinj (by simp only [Set.mem_setOf_eq]; omega)
        (by simp only [Set.mem_setOf_eq]; omega) this
      omega
  have machineMin : ∀ m, m ≤ L → (∀ i, i ≤ L → g m ≤ g i) → 0 < m → m < L → False := by
    intro m hmL hmmin hm0 hmL'
    have hneq : g (m - 1) = g (m + 1) := kc_min_neighbours_eq g L hstep hm0 hmL' hmmin
    by_cases hmp : m + 1 ≤ L - 1
    · have : (m - 1) = (m + 1) := hinj (by simp only [Set.mem_setOf_eq]; omega)
        (by simp only [Set.mem_setOf_eq]; omega) hneq
      omega
    · have hmpL : m + 1 = L := by omega
      have : g (m - 1) = g 0 := by rw [hneq, hmpL, ← hloop]
      have : (m - 1) = 0 := hinj (by simp only [Set.mem_setOf_eq]; omega)
        (by simp only [Set.mem_setOf_eq]; omega) this
      omega
  
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · 
    have hj1 : g j ≤ g 1 := hjmin' 1 (by omega)
    have hlt0 : g j < g 0 := by omega
    have hj0 : j ≠ 0 := by intro h; rw [h] at hlt0; omega
    have hjL : j ≠ L := by intro h; rw [h, ← hloop] at hlt0; omega
    exact machineMin j (by omega) hjmin' (by omega) (by omega)
  · 
    have hk1 : g 1 ≤ g k := hkmax' 1 (by omega)
    have hgt0 : g 0 < g k := by omega
    have hk0 : k ≠ 0 := by intro h; rw [h] at hgt0; omega
    have hkL' : k ≠ L := by intro h; rw [h, ← hloop] at hgt0; omega
    exact machine k (by omega) hkmax' (by omega) (by omega)



theorem kc_no_monotone_loop_abs (g : ℕ → ℤ) (L : ℕ) (h3 : 3 ≤ L)
    (hloop : g 0 = g L)
    (hstep : ∀ i, i < L → |g (i + 1) - g i| = 1)
    (hne : g 1 ≠ g 0)
    (hinj : Set.InjOn g {i | i ≤ L - 1}) : False :=
  kc_no_monotone_loop g L h3 hloop (fun i hi => (kc_abs_diff_one g i).mp (hstep i hi)) hne hinj















theorem kc_eaw_no_monotone_loop (g : ℕ → ℤ) (L : ℕ) (h3 : 3 ≤ L)
    (hloop : g 0 = g L)
    (hstep : ∀ i, i < L → g (i + 1) = g i + 1 ∨ g (i + 1) = g i - 1)
    (hne : g 1 ≠ g 0)
    (hinj : Set.InjOn g {i | i ≤ L - 1}) : False :=
  kc_no_monotone_loop g L h3 hloop hstep hne hinj






theorem kc_no_monotone_loop_iff_eaw :
    (∀ (g : ℕ → ℤ) (L : ℕ), 3 ≤ L → g 0 = g L →
        (∀ i, i < L → g (i + 1) = g i + 1 ∨ g (i + 1) = g i - 1) →
        g 1 ≠ g 0 → Set.InjOn g {i | i ≤ L - 1} → False)
      ↔
    (∀ (g : ℕ → ℤ) (L : ℕ), 3 ≤ L → g 0 = g L →
        (∀ i, i < L → g (i + 1) = g i + 1 ∨ g (i + 1) = g i - 1) →
        g 1 ≠ g 0 → Set.InjOn g {i | i ≤ L - 1} → False) :=
  ⟨fun _ g L h3 hloop hstep hne hinj =>
      StatMech.Lattice.eaw_no_monotone_loop g L h3 hloop hstep hne hinj,
   fun _ g L h3 hloop hstep hne hinj =>
      kc_no_monotone_loop g L h3 hloop hstep hne hinj⟩

end StatMech.Walls

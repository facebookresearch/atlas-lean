/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierA.GrahamFourColorBalancedCore









open Finset
open Classical

namespace StatMech.GrahamGHS.FourColor

open StatMech.Sharpness.RandomCurrent

variable {ι W : Type*} [Fintype ι] [DecidableEq ι]
  [Fintype W] [DecidableEq W]

def middleMask (m : Finset ι) (c : ↑m -> Fin 4) : Finset ι :=
  colorClass m c 1 ∪ colorClass m c 2

def outerMask (m : Finset ι) (c : ↑m -> Fin 4) : Finset ι :=
  colorClass m c 0 ∪ colorClass m c 3

theorem mem_colorClass_iff (m : Finset ι) (c : ↑m -> Fin 4)
    (a : Fin 4) (i : ι) :
    i ∈ colorClass m c a ↔ ∃ hi : i ∈ m, c ⟨i, hi⟩ = a := by
  simp [colorClass]


theorem middleMask_balancedSwap (m X Y : Finset ι) (c : ↑m -> Fin 4) :
    middleMask m (balancedSwap m X Y c) = middleMask m c := by
  ext i
  by_cases hi : i ∈ m
  · have hv : c ⟨i, hi⟩ = 0 ∨ c ⟨i, hi⟩ = 1 ∨
        c ⟨i, hi⟩ = 2 ∨ c ⟨i, hi⟩ = 3 := by omega
    rcases hv with hv | hv | hv | hv <;>
      by_cases hX : i ∈ X <;> by_cases hY : i ∈ Y <;>
        simp [middleMask, mem_colorClass_iff, balancedSwap, middleSwapOn,
          outerSwapOn, Equiv.swap_apply_def, hi, hX, hY, hv]
  · simp [middleMask, mem_colorClass_iff, hi]


theorem outerMask_balancedSwap (m X Y : Finset ι) (c : ↑m -> Fin 4) :
    outerMask m (balancedSwap m X Y c) = outerMask m c := by
  ext i
  by_cases hi : i ∈ m
  · have hv : c ⟨i, hi⟩ = 0 ∨ c ⟨i, hi⟩ = 1 ∨
        c ⟨i, hi⟩ = 2 ∨ c ⟨i, hi⟩ = 3 := by omega
    rcases hv with hv | hv | hv | hv <;>
      by_cases hX : i ∈ X <;> by_cases hY : i ∈ Y <;>
        simp [outerMask, mem_colorClass_iff, balancedSwap, middleSwapOn,
          outerSwapOn, Equiv.swap_apply_def, hi, hX, hY, hv]
  · simp [outerMask, mem_colorClass_iff, hi]

theorem leftPattern_middleMask_sources
    {ends : ι -> Sym2 W} {m : Finset ι} {j k l zero : W}
    {c : ↑m -> Fin 4}
    (h : LeftPattern ends m {j, k} {k, l} k zero c) :
    sources ends (middleMask m c) = {k, l} := by
  rw [middleMask, sources_union_of_disjoint
    (colorClass_disjoint m c (by decide)), h.2.1, h.2.2.1]
  simp

theorem leftPattern_outerMask_sources
    {ends : ι -> Sym2 W} {m : Finset ι} {j k l zero : W}
    {c : ↑m -> Fin 4}
    (h : LeftPattern ends m {j, k} {k, l} k zero c) :
    sources ends (outerMask m c) = {j, k} := by
  rw [outerMask, sources_union_of_disjoint
    (colorClass_disjoint m c (by decide)), h.1, h.2.2.2.1]
  simp



theorem leftPattern_middleComponent_sources
    {ends : ι -> Sym2 W} {m : Finset ι} {j k l zero : W}
    {c : ↑m -> Fin 4}
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l)
    (h : LeftPattern ends m {j, k} {k, l} k zero c) :
    sources ends (edgeComponent ends (middleMask m c) k) = {k, l} := by
  rw [sources_edgeComponent, leftPattern_middleMask_sources h]
  apply Finset.inter_eq_left.mpr
  intro x hx
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx
  rw [StatMech.Sharpness.RandomCurrent.mem_compOf]
  rcases hx with rfl | rfl
  · exact Relation.ReflTransGen.refl
  · have hconn := (leftPattern_sharedSource_connections hloop hjk hkl h).2
    exact connK_mono (by
      intro i hi
      exact Finset.mem_union_right _ hi) hconn



theorem middleComponent_balancedSwap
    (ends : ι -> Sym2 W) (m X Y : Finset ι) (c : ↑m -> Fin 4) (k : W) :
    edgeComponent ends (middleMask m (balancedSwap m X Y c)) k =
      edgeComponent ends (middleMask m c) k := by
  rw [middleMask_balancedSwap]

end StatMech.GrahamGHS.FourColor

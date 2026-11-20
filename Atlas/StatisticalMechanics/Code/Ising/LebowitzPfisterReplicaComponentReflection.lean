/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.Ising.LebowitzPfisterReplicaGhostComponent











open Finset
open scoped symmDiff

namespace StatMech.Ising

open StatMech.Sharpness
open StatMech.Sharpness.FluxEdgeCopy
open StatMech.Sharpness.RandomCurrent

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]



def lpReplicaPartialReflectSource
    (A C : Finset (LPReplicaCurrentVertex V)) :
    Finset (LPReplicaCurrentVertex V) :=
  (A \ C) ∆ (A ∩ C).map lpReplicaCurrentReflect.toEmbedding

omit [Fintype V] in
theorem mem_lpReplicaPartialReflectSource
    (A C : Finset (LPReplicaCurrentVertex V))
    (x : LPReplicaCurrentVertex V) :
    x ∈ lpReplicaPartialReflectSource A C ↔
      ((x ∈ A ∧ x ∉ C) ∧
          ¬ (lpReplicaCurrentReflect x ∈ A ∧
            lpReplicaCurrentReflect x ∈ C)) ∨
        ((lpReplicaCurrentReflect x ∈ A ∧
            lpReplicaCurrentReflect x ∈ C) ∧
          ¬ (x ∈ A ∧ x ∉ C)) := by
  have hinv : Function.Involutive
      (lpReplicaCurrentReflect : LPReplicaCurrentVertex V ->
        LPReplicaCurrentVertex V) := by
    intro z
    rcases z with (z | b)
    · rcases z with z | z <;> rfl
    · cases b <;> rfl
  unfold lpReplicaPartialReflectSource
  simp only [Finset.mem_symmDiff, Finset.mem_sdiff, Finset.mem_inter,
    Finset.mem_map]
  constructor
  · rintro (⟨hx, hnot⟩ | ⟨hmap, hx⟩)
    · left
      refine ⟨hx, ?_⟩
      rintro ⟨hra, hrc⟩
      apply hnot
      refine ⟨lpReplicaCurrentReflect x, ⟨hra, hrc⟩, ?_⟩
      exact hinv x
    · right
      rcases hmap with ⟨y, hy, rfl⟩
      refine ⟨?_, hx⟩
      change lpReplicaCurrentReflect (lpReplicaCurrentReflect y) ∈ A ∧
        lpReplicaCurrentReflect (lpReplicaCurrentReflect y) ∈ C
      simpa only [hinv y] using hy
  · rintro (⟨hx, hnot⟩ | ⟨hr, hx⟩)
    · left
      refine ⟨hx, ?_⟩
      rintro ⟨y, hy, hxy⟩
      apply hnot
      subst x
      change lpReplicaCurrentReflect (lpReplicaCurrentReflect y) ∈ A ∧
        lpReplicaCurrentReflect (lpReplicaCurrentReflect y) ∈ C
      simpa only [hinv y] using hy
    · right
      refine ⟨?_, hx⟩
      refine ⟨lpReplicaCurrentReflect x, ?_, ?_⟩
      · simpa only [hinv x] using hr
      · exact hinv x

omit [Fintype V] [Fintype I] [DecidableEq I] in
private theorem lpReplicaPartial_six_eq_seam_j
    (sites : I -> V) (hsite : Function.Injective sites)
    {i j : I} (hij : i ≠ j)
    (C : Finset (LPReplicaCurrentVertex V))
    (hg0 : (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V) ∈ C)
    (hg1 : (lpReplicaCurrentGhost1 : LPReplicaCurrentVertex V) ∉ C)
    (hsplitI :
      (lpReplicaCurrentLeft sites i ∈ C ∧
          lpReplicaCurrentRight sites i ∉ C) ∨
        (lpReplicaCurrentLeft sites i ∉ C ∧
          lpReplicaCurrentRight sites i ∈ C))
    (hnotSplitJ : ¬ (
      (lpReplicaCurrentLeft sites j ∈ C ∧
          lpReplicaCurrentRight sites j ∉ C) ∨
        (lpReplicaCurrentLeft sites j ∉ C ∧
          lpReplicaCurrentRight sites j ∈ C))) :
    lpReplicaPartialReflectSource
        {lpReplicaCurrentGhost0, lpReplicaCurrentGhost1,
          lpReplicaCurrentLeft sites i, lpReplicaCurrentRight sites i,
          lpReplicaCurrentLeft sites j, lpReplicaCurrentRight sites j} C =
      lpMatchingSeamSource
        (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j := by
  have hs : sites i ≠ sites j := hsite.ne hij
  ext z
  rw [mem_lpReplicaPartialReflectSource]
  by_cases hli : lpReplicaCurrentLeft sites i ∈ C <;>
    by_cases hri : lpReplicaCurrentRight sites i ∈ C <;>
    by_cases hlj : lpReplicaCurrentLeft sites j ∈ C <;>
    by_cases hrj : lpReplicaCurrentRight sites j ∈ C
  all_goals
    rcases z with (z | b)
    · rcases z with x | x <;>
        simp only [lpReplicaCurrentReflect_left,
          lpReplicaCurrentReflect_right] <;>
        by_cases hi : x = sites i <;> by_cases hj : x = sites j <;>
          simp_all [lpMatchingSeamSource, lpReplicaCurrentLeft,
            lpReplicaCurrentRight, lpReplicaCurrentGhost0,
            lpReplicaCurrentGhost1, Finset.mem_symmDiff]
    · cases b <;>
        simp_all [lpMatchingSeamSource, lpReplicaCurrentLeft,
          lpReplicaCurrentRight, lpReplicaCurrentGhost0,
          lpReplicaCurrentGhost1, Finset.mem_symmDiff]

omit [Fintype V] [Fintype I] [DecidableEq I] in
private theorem lpReplicaPartial_six_eq_seam_i
    (sites : I -> V) (hsite : Function.Injective sites)
    {i j : I} (hij : i ≠ j)
    (C : Finset (LPReplicaCurrentVertex V))
    (hg0 : (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V) ∈ C)
    (hg1 : (lpReplicaCurrentGhost1 : LPReplicaCurrentVertex V) ∉ C)
    (hnotSplitI : ¬ (
      (lpReplicaCurrentLeft sites i ∈ C ∧
          lpReplicaCurrentRight sites i ∉ C) ∨
        (lpReplicaCurrentLeft sites i ∉ C ∧
          lpReplicaCurrentRight sites i ∈ C)))
    (hsplitJ :
      (lpReplicaCurrentLeft sites j ∈ C ∧
          lpReplicaCurrentRight sites j ∉ C) ∨
        (lpReplicaCurrentLeft sites j ∉ C ∧
          lpReplicaCurrentRight sites j ∈ C)) :
    lpReplicaPartialReflectSource
        {lpReplicaCurrentGhost0, lpReplicaCurrentGhost1,
          lpReplicaCurrentLeft sites i, lpReplicaCurrentRight sites i,
          lpReplicaCurrentLeft sites j, lpReplicaCurrentRight sites j} C =
      lpMatchingSeamSource
        (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i := by
  have hs : sites i ≠ sites j := hsite.ne hij
  ext z
  rw [mem_lpReplicaPartialReflectSource]
  by_cases hli : lpReplicaCurrentLeft sites i ∈ C <;>
    by_cases hri : lpReplicaCurrentRight sites i ∈ C <;>
    by_cases hlj : lpReplicaCurrentLeft sites j ∈ C <;>
    by_cases hrj : lpReplicaCurrentRight sites j ∈ C
  all_goals
    rcases z with (z | b)
    · rcases z with x | x <;>
        simp only [lpReplicaCurrentReflect_left,
          lpReplicaCurrentReflect_right] <;>
        by_cases hi : x = sites i <;> by_cases hj : x = sites j <;>
          simp_all [lpMatchingSeamSource, lpReplicaCurrentLeft,
            lpReplicaCurrentRight, lpReplicaCurrentGhost0,
            lpReplicaCurrentGhost1, Finset.mem_symmDiff]
    · cases b <;>
        simp_all [lpMatchingSeamSource, lpReplicaCurrentLeft,
          lpReplicaCurrentRight, lpReplicaCurrentGhost0,
          lpReplicaCurrentGhost1, Finset.mem_symmDiff]

local instance (G : SimpleGraph V) (sites : I -> V) :
    DecidableRel (lpReplicaCurrentGraph G sites).Adj :=
  Classical.decRel _

omit [Fintype I] [DecidableEq I] in




theorem lpReplicaOffdiagComponent_partialReflectSource
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites) {i j : I} (hij : i ≠ j)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hsrc : RandomCurrent.sources
      (endsM (lpReplicaCurrentGraph G sites) m)
      (Finset.univ : Finset (Copy (lpReplicaCurrentGraph G sites) m)) =
        lpMatchingSeamSource
            (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i ∆
          lpMatchingSeamSource
            (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j ∆
          lpMatchingGhostSource
            (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
            lpReplicaCurrentGhost1)
    (hdisc : ¬ RandomCurrent.connK
      (endsM (lpReplicaCurrentGraph G sites) m)
      (Finset.univ : Finset (Copy (lpReplicaCurrentGraph G sites) m))
      lpReplicaCurrentGhost0 lpReplicaCurrentGhost1) :
    let H := lpReplicaCurrentGraph G sites
    let K : Finset (Copy H m) := Finset.univ
    let e := endsM H m
    let C := RandomCurrent.compOf e K
      (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
    let A := lpMatchingSeamSource
          (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i ∆
        lpMatchingSeamSource
          (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j ∆
        lpMatchingGhostSource
          (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
          lpReplicaCurrentGhost1
    lpReplicaPartialReflectSource A C = lpMatchingSeamSource
        (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i ∨
      lpReplicaPartialReflectSource A C = lpMatchingSeamSource
        (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j := by
  dsimp only
  let H := lpReplicaCurrentGraph G sites
  let K : Finset (Copy H m) := Finset.univ
  let e := endsM H m
  let C := RandomCurrent.compOf e K
    (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
  have hg0 : (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V) ∈ C := by
    rw [RandomCurrent.mem_compOf]
    exact Relation.ReflTransGen.refl
  have hg1 : (lpReplicaCurrentGhost1 : LPReplicaCurrentVertex V) ∉ C := by
    rw [RandomCurrent.mem_compOf]
    simpa [e, K, H] using hdisc
  have hsplit := lpReplicaGhostComponent_splits_exactly_one_markedSeam
    G sites hsite hij m hsrc hdisc
  have hsplitC :
      (((lpReplicaCurrentLeft sites i ∈ C ∧
            lpReplicaCurrentRight sites i ∉ C) ∨
          (lpReplicaCurrentLeft sites i ∉ C ∧
            lpReplicaCurrentRight sites i ∈ C)) ∧
        ¬ ((lpReplicaCurrentLeft sites j ∈ C ∧
            lpReplicaCurrentRight sites j ∉ C) ∨
          (lpReplicaCurrentLeft sites j ∉ C ∧
            lpReplicaCurrentRight sites j ∈ C))) ∨
      (¬ ((lpReplicaCurrentLeft sites i ∈ C ∧
            lpReplicaCurrentRight sites i ∉ C) ∨
          (lpReplicaCurrentLeft sites i ∉ C ∧
            lpReplicaCurrentRight sites i ∈ C)) ∧
        ((lpReplicaCurrentLeft sites j ∈ C ∧
            lpReplicaCurrentRight sites j ∉ C) ∨
          (lpReplicaCurrentLeft sites j ∉ C ∧
            lpReplicaCurrentRight sites j ∈ C))) := by
    simpa only [C, RandomCurrent.mem_compOf] using hsplit
  have hA := lpReplicaOffdiagSource_eq_six sites hsite hij
  rw [hA]
  rcases hsplitC with h | h
  · exact Or.inr (lpReplicaPartial_six_eq_seam_j sites hsite hij C
      hg0 hg1 h.1 h.2)
  · exact Or.inl (lpReplicaPartial_six_eq_seam_i sites hsite hij C
      hg0 hg1 h.1 h.2)

omit [Fintype V] in




theorem lpOffdiagPartialSource_complement
    (Si Sj T P : Finset (LPReplicaCurrentVertex V))
    (hP : P = Si ∨ P = Sj) :
    (P = Si ∧ (Si ∆ Sj ∆ T) ∆ P = Sj ∆ T) ∨
      (P = Sj ∧ (Si ∆ Sj ∆ T) ∆ P = Si ∆ T) := by
  rcases hP with rfl | rfl
  · left
    refine ⟨rfl, ?_⟩
    ext x
    simp only [Finset.mem_symmDiff]
    tauto
  · right
    refine ⟨rfl, ?_⟩
    ext x
    simp only [Finset.mem_symmDiff]
    tauto

omit [Fintype I] [DecidableEq I] in



theorem lpReplicaOffdiagComponent_partialReflectAllocation
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites) {i j : I} (hij : i ≠ j)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hsrc : RandomCurrent.sources
      (endsM (lpReplicaCurrentGraph G sites) m)
      (Finset.univ : Finset (Copy (lpReplicaCurrentGraph G sites) m)) =
        lpMatchingSeamSource
            (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i ∆
          lpMatchingSeamSource
            (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j ∆
          lpMatchingGhostSource
            (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
            lpReplicaCurrentGhost1)
    (hdisc : ¬ RandomCurrent.connK
      (endsM (lpReplicaCurrentGraph G sites) m)
      (Finset.univ : Finset (Copy (lpReplicaCurrentGraph G sites) m))
      lpReplicaCurrentGhost0 lpReplicaCurrentGhost1) :
    let H := lpReplicaCurrentGraph G sites
    let C := RandomCurrent.compOf (endsM H m)
      (Finset.univ : Finset (Copy H m))
      (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
    let Si := lpMatchingSeamSource
      (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i
    let Sj := lpMatchingSeamSource
      (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j
    let T := lpMatchingGhostSource
      (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
      lpReplicaCurrentGhost1
    let P := lpReplicaPartialReflectSource (Si ∆ Sj ∆ T) C
    (P = Si ∧ (Si ∆ Sj ∆ T) ∆ P = Sj ∆ T) ∨
      (P = Sj ∧ (Si ∆ Sj ∆ T) ∆ P = Si ∆ T) := by
  dsimp only
  apply lpOffdiagPartialSource_complement
  exact lpReplicaOffdiagComponent_partialReflectSource
    G sites hsite hij m hsrc hdisc

end

end StatMech.Ising

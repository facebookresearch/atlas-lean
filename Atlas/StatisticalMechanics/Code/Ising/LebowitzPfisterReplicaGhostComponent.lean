/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.Ising.LebowitzPfisterReplicaAggregateSwitching
import Code.Sharpness.SwitchingDichotomy










open Finset
open scoped symmDiff

namespace StatMech.Ising

open StatMech.Sharpness
open StatMech.Sharpness.FluxEdgeCopy
open StatMech.Sharpness.RandomCurrent

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

omit [Fintype V] [Fintype I] [DecidableEq I] in


theorem lpReplicaOffdiagSource_eq_six
    (sites : I -> V) (hsite : Function.Injective sites)
    {i j : I} (hij : i ≠ j) :
    lpMatchingSeamSource
          (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i ∆
        lpMatchingSeamSource
          (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j ∆
        lpMatchingGhostSource
          (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
          lpReplicaCurrentGhost1 =
      {lpReplicaCurrentGhost0, lpReplicaCurrentGhost1,
        lpReplicaCurrentLeft sites i, lpReplicaCurrentRight sites i,
        lpReplicaCurrentLeft sites j, lpReplicaCurrentRight sites j} := by
  have hs : sites i ≠ sites j := hsite.ne hij
  ext z
  rcases z with (z | b)
  · rcases z with x | x <;>
      simp [lpMatchingSeamSource, lpMatchingGhostSource,
        lpReplicaCurrentLeft, lpReplicaCurrentRight,
        lpReplicaCurrentGhost0, lpReplicaCurrentGhost1,
        Finset.mem_symmDiff] <;>
      by_cases hi : x = sites i <;> by_cases hj : x = sites j <;>
        simp_all
  · cases b <;>
      simp [lpMatchingSeamSource, lpMatchingGhostSource,
        lpReplicaCurrentLeft, lpReplicaCurrentRight,
        lpReplicaCurrentGhost0, lpReplicaCurrentGhost1,
        Finset.mem_symmDiff]

local instance (G : SimpleGraph V) (sites : I -> V) :
    DecidableRel (lpReplicaCurrentGraph G sites).Adj :=
  Classical.decRel _

set_option maxHeartbeats 1600000 in

omit [Fintype I] [DecidableEq I] in



theorem lpReplicaGhostComponent_splits_exactly_one_markedSeam
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
    let ciL := RandomCurrent.connK
      (endsM (lpReplicaCurrentGraph G sites) m) Finset.univ
      lpReplicaCurrentGhost0 (lpReplicaCurrentLeft sites i)
    let ciR := RandomCurrent.connK
      (endsM (lpReplicaCurrentGraph G sites) m) Finset.univ
      lpReplicaCurrentGhost0 (lpReplicaCurrentRight sites i)
    let cjL := RandomCurrent.connK
      (endsM (lpReplicaCurrentGraph G sites) m) Finset.univ
      lpReplicaCurrentGhost0 (lpReplicaCurrentLeft sites j)
    let cjR := RandomCurrent.connK
      (endsM (lpReplicaCurrentGraph G sites) m) Finset.univ
      lpReplicaCurrentGhost0 (lpReplicaCurrentRight sites j)
    let splitI := (ciL ∧ ¬ ciR) ∨ (¬ ciL ∧ ciR)
    let splitJ := (cjL ∧ ¬ cjR) ∨ (¬ cjL ∧ cjR)
    (splitI ∧ ¬ splitJ) ∨ (¬ splitI ∧ splitJ) := by
  let H := lpReplicaCurrentGraph G sites
  let K : Finset (Copy H m) := Finset.univ
  let e := endsM H m
  let g0 : LPReplicaCurrentVertex V := lpReplicaCurrentGhost0
  let g1 : LPReplicaCurrentVertex V := lpReplicaCurrentGhost1
  let li := lpReplicaCurrentLeft sites i
  let ri := lpReplicaCurrentRight sites i
  let lj := lpReplicaCurrentLeft sites j
  let rj := lpReplicaCurrentRight sites j
  have hA :
      lpMatchingSeamSource
            (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i ∆
          lpMatchingSeamSource
            (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j ∆
          lpMatchingGhostSource
            (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
            lpReplicaCurrentGhost1 =
        {g0, g1, li, ri, lj, rj} := by
    simpa [g0, g1, li, ri, lj, rj] using
      lpReplicaOffdiagSource_eq_six sites hsite hij
  have heven : Even (RandomCurrent.compOddVertices e K g0).card :=
    RandomCurrent.even_compOddVertices e K
      (fun q _ => endsM_not_isDiag H m q) g0
  have hself : RandomCurrent.connK e K g0 g0 :=
    Relation.ReflTransGen.refl
  have hdisc' : ¬ RandomCurrent.connK e K g0 g1 := by
    simpa [e, K, H, g0, g1] using hdisc
  rw [RandomCurrent.compOddVertices_eq_filter_sources, hsrc, hA] at heven
  rw [Finset.card_filter] at heven
  have hs : sites i ≠ sites j := hsite.ne hij
  have hg0 : g0 ∉ ({g1, li, ri, lj, rj} :
      Finset (LPReplicaCurrentVertex V)) := by
    simp [g0, g1, li, ri, lj, rj, lpReplicaCurrentLeft,
      lpReplicaCurrentRight, lpReplicaCurrentGhost0,
      lpReplicaCurrentGhost1]
  have hg1 : g1 ∉ ({li, ri, lj, rj} :
      Finset (LPReplicaCurrentVertex V)) := by
    simp [g1, li, ri, lj, rj, lpReplicaCurrentLeft,
      lpReplicaCurrentRight, lpReplicaCurrentGhost1]
  have hli_ne : li ∉ ({ri, lj, rj} :
      Finset (LPReplicaCurrentVertex V)) := by
    simp [li, ri, lj, rj, lpReplicaCurrentLeft,
      lpReplicaCurrentRight, hs]
  have hri_ne : ri ∉ ({lj, rj} :
      Finset (LPReplicaCurrentVertex V)) := by
    simp [ri, lj, rj, lpReplicaCurrentLeft,
      lpReplicaCurrentRight, hs]
  have hlj_ne : lj ∉ ({rj} : Finset (LPReplicaCurrentVertex V)) := by
    simp [lj, rj, lpReplicaCurrentLeft, lpReplicaCurrentRight]
  rw [Finset.sum_insert hg0, Finset.sum_insert hg1,
    Finset.sum_insert hli_ne, Finset.sum_insert hri_ne,
    Finset.sum_insert hlj_ne, Finset.sum_singleton] at heven
  dsimp only
  change (((RandomCurrent.connK e K g0 li ∧
        ¬ RandomCurrent.connK e K g0 ri) ∨
      (¬ RandomCurrent.connK e K g0 li ∧
        RandomCurrent.connK e K g0 ri)) ∧
      ¬ ((RandomCurrent.connK e K g0 lj ∧
        ¬ RandomCurrent.connK e K g0 rj) ∨
      (¬ RandomCurrent.connK e K g0 lj ∧
        RandomCurrent.connK e K g0 rj))) ∨
    (¬ ((RandomCurrent.connK e K g0 li ∧
        ¬ RandomCurrent.connK e K g0 ri) ∨
      (¬ RandomCurrent.connK e K g0 li ∧
        RandomCurrent.connK e K g0 ri)) ∧
      ((RandomCurrent.connK e K g0 lj ∧
        ¬ RandomCurrent.connK e K g0 rj) ∨
      (¬ RandomCurrent.connK e K g0 lj ∧
        RandomCurrent.connK e K g0 rj)))
  by_cases hli : RandomCurrent.connK e K g0 li <;>
    by_cases hri : RandomCurrent.connK e K g0 ri <;>
    by_cases hlj : RandomCurrent.connK e K g0 lj <;>
    by_cases hrj : RandomCurrent.connK e K g0 rj <;>
    simp only [hli, hri, hlj, hrj, not_true_eq_false,
      not_false_eq_true, and_self, and_true, and_false, or_true,
      or_false, not_false_eq_true, not_true_eq_false] at ⊢ <;>
    simp [hself, hdisc', hli, hri, hlj, hrj] at heven <;>
    norm_num at heven

end

end StatMech.Ising

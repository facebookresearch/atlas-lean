/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.FrontierA.TriangularIsingTorusPeriodicLift





namespace StatMech.FrontierA

theorem triangularTorusSurfaceSpin_zero_zero_quadratic
    (x y : Fin 2) :
    surfaceQuadraticParity (triangularTorusSurfaceSpin 0 0)
      (fun _ : Fin 1 => x, fun _ : Fin 1 => y) =
        if x = 0 ∧ y = 0 then 0 else 1 := by
  fin_cases x <;> fin_cases y <;>
    norm_num [surfaceQuadraticParity, triangularTorusSurfaceSpin,
      Fin.sum_univ_one, Fin.val_add]

theorem triangularTorusSurfaceSpin_zero_zero_sign
    (x y : Fin 2) :
    (surfaceParitySign
      (surfaceQuadraticParity (triangularTorusSurfaceSpin 0 0)
        (fun _ : Fin 1 => x, fun _ : Fin 1 => y)) : Complex) =
      if x = 0 ∧ y = 0 then 1 else -1 := by
  rw [triangularTorusSurfaceSpin_zero_zero_quadratic]
  split_ifs <;> norm_num [surfaceParitySign]

theorem triangularTorusCycle_baseSpinSign_eq_windingParity
    (L : Nat) [Fact (2 < L)] {root : ZMod L × ZMod L}
    (p : (triangularTorusGraph L).Walk root root) (hp : p.IsCycle)
    (mx my : Int)
    (hdisplacement : ∑ k, triangularIntStep
      (triangularTorusCycleNativeDart L p k).2 =
        ((L : Int) * mx, (L : Int) * my)) :
    (surfaceParitySign
      (surfaceQuadraticParity (triangularTorusSurfaceSpin 0 0)
        (surfaceSubgraphHomology (triangularTorusSurfaceEdgeClass L)
          p.edges.toFinset)) : Complex) =
      if StatMech.Onsager.ons_intParity mx = 0 ∧
          StatMech.Onsager.ons_intParity my = 0 then 1 else -1 := by
  rw [triangularTorusCycle_surfaceHomology_eq_windingParity
    L p hp mx my hdisplacement]
  exact triangularTorusSurfaceSpin_zero_zero_sign _ _

theorem triangularTorusCycle_surfaceHomology_eq_zero_iff_windingParity
    (L : Nat) [Fact (2 < L)] {root : ZMod L × ZMod L}
    (p : (triangularTorusGraph L).Walk root root) (hp : p.IsCycle)
    (mx my : Int)
    (hdisplacement : ∑ k, triangularIntStep
      (triangularTorusCycleNativeDart L p k).2 =
        ((L : Int) * mx, (L : Int) * my)) :
    surfaceSubgraphHomology (triangularTorusSurfaceEdgeClass L)
        p.edges.toFinset = 0 ↔
      StatMech.Onsager.ons_intParity mx = 0 ∧
        StatMech.Onsager.ons_intParity my = 0 := by
  rw [triangularTorusCycle_surfaceHomology_eq_windingParity
    L p hp mx my hdisplacement]
  constructor
  · intro h
    constructor
    · simpa using congrFun (congrArg Prod.fst h) 0
    · simpa using congrFun (congrArg Prod.snd h) 0
  · rintro ⟨hx, hy⟩
    apply Prod.ext <;> funext i
    · simpa [hx]
    · simpa [hy]



theorem exists_triangularTorusCycle_nonzeroHomology_periodicLift
    (L : Nat) [Fact (2 < L)] {root : ZMod L × ZMod L}
    (p : (triangularTorusGraph L).Walk root root) (hp : p.IsCycle)
    (hhom : surfaceSubgraphHomology (triangularTorusSurfaceEdgeClass L)
      p.edges.toFinset ≠ 0) :
    letI : NeZero p.darts.length :=
      ⟨Nat.ne_of_gt (List.length_pos_of_ne_nil
        (SimpleGraph.Walk.darts_eq_nil.not.mpr hp.not_nil))⟩
    exists mx my : Int,
      (∑ k, triangularIntStep
        (triangularTorusCycleNativeDart L p k).2) =
          ((L : Int) * mx, (L : Int) * my) ∧
      (mx ≠ 0 ∨ my ≠ 0) ∧
      Function.Injective (triangularIntPeriodicPos
        (fun k => (triangularTorusCycleNativeDart L p k).2)) := by
  letI : NeZero p.darts.length :=
    ⟨Nat.ne_of_gt (List.length_pos_of_ne_nil
      (SimpleGraph.Walk.darts_eq_nil.not.mpr hp.not_nil))⟩
  obtain ⟨mx, my, hdisplacement⟩ :=
    exists_triangularTorusCycle_winding L p hp
  have hne : mx ≠ 0 ∨ my ≠ 0 := by
    by_contra h
    push_neg at h
    rcases h with ⟨rfl, rfl⟩
    apply hhom
    rw [triangularTorusCycle_surfaceHomology_eq_windingParity
      L p hp 0 0 hdisplacement]
    apply Prod.ext <;> funext i <;>
      simp [StatMech.Onsager.ons_intParity]
  exact ⟨mx, my, hdisplacement, hne,
    triangularTorusCyclePeriodicPos_injective
      L p hp mx my hdisplacement hne⟩

end StatMech.FrontierA

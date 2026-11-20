/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.FKRectBlackOrbitWindingGeometry
import Code.FrontierD.FKMedialLoopVerticalWinding
import Code.FrontierD.FKRectZeroTurnDevelopedAnchor



open Equiv Finset SimpleGraph
open StatMech.Onsager StatMech.Onsager.BaseCase

namespace StatMech.FrontierD

noncomputable section

@[simp] theorem finitePeriodicSucc_svFinLast {N : Nat} (hN : 0 < N) :
    finitePeriodicSucc hN (svFinLast hN) = (⟨0, hN⟩ : Fin N) := by
  apply Fin.ext
  simp [finitePeriodicSucc, svFinLast, Nat.sub_add_cancel hN]

theorem not_even_svFinLast_of_even {N : Nat} (hN : 0 < N)
    (heven : Even N) : ¬ Even (svFinLast hN).val := by
  simp only [svFinLast, Fin.val_mk]
  rw [Nat.even_sub hN]
  simp [heven]

theorem finZero_ne_svFinLast {N : Nat} (hN : 1 < N) :
    (⟨0, Nat.zero_lt_of_lt hN⟩ : Fin N) ≠
      svFinLast (Nat.zero_lt_of_lt hN) := by
  intro h
  have hv := congrArg Fin.val h
  simp only [svFinLast, Fin.val_mk] at hv
  omega


def fkMedialVerticalSeamBlackDart
    (pairing : FKMedialLoopPairing T) (i : Fin T.width) :
    FKMedialBlackDart T := by
  let s := fkMedialVerticalSeamDart T i
  by_cases hs : fkMedialCheckerColor s = false
  · exact ⟨fkMedialLocalMate pairing (fkMedialBondMate T s), by
      have hbond := fkMedialCheckerColor_bondMate_ne T s
      have hlocal := fkMedialCheckerColor_localMate_ne pairing
        (fkMedialBondMate T s)
      rw [hs] at hbond
      generalize hb : fkMedialCheckerColor (fkMedialBondMate T s) = b
        at hbond hlocal
      generalize hl : fkMedialCheckerColor
        (fkMedialLocalMate pairing (fkMedialBondMate T s)) = c at hlocal
      cases b <;> cases c <;> simp_all⟩
  · exact ⟨fkMedialLocalMate pairing s, by
      rw [fkMedialCheckerColor_localMate_eq_not]
      simp [Bool.eq_true_of_not_eq_false hs]⟩



def fkMedialBlackVerticalSeamContribution
    (pairing : FKMedialLoopPairing T) (d : FKMedialBlackDart T) : Int :=
  ∑ i : Fin T.width,
    if fkMedialVerticalSeamBlackDart pairing i = d then
      fkMedialCanonicalVerticalSeamSign T i
    else 0

@[simp] theorem fkMedialVerticalSeamBlackDart_fst
    (pairing : FKMedialLoopPairing T) (i : Fin T.width) :
    (fkMedialVerticalSeamBlackDart pairing i).1.1.1 = i := by
  unfold fkMedialVerticalSeamBlackDart
  dsimp only
  split
  · cases h : pairing (i, (⟨0, T.height_pos⟩ : Fin T.height)) <;>
      simp [fkMedialVerticalSeamDart, fkMedialBondMate,
        fkMedialLocalMate, finitePeriodicSucc_svFinLast, h]
  · cases h : pairing (i, svFinLast T.height_pos) <;>
      simp [fkMedialVerticalSeamDart, fkMedialLocalMate, h]

theorem fkMedialVerticalSeamBlackDart_injective
    (pairing : FKMedialLoopPairing T) :
    Function.Injective (fkMedialVerticalSeamBlackDart pairing) := by
  intro i j hij
  have hv := congrArg (fun d : FKMedialBlackDart T => d.1.1.1) hij
  simpa using hv

theorem fkMedialVerticalSeamBlackDart_component
    (pairing : FKMedialLoopPairing T) (i : Fin T.width) :
    (fkMedialLoopGraph T pairing).connectedComponentMk
        (fkMedialVerticalSeamBlackDart pairing i).1 =
      (fkMedialLoopGraph T pairing).connectedComponentMk
        (fkMedialVerticalSeamDart T i) := by
  unfold fkMedialVerticalSeamBlackDart
  dsimp only
  by_cases hs : fkMedialCheckerColor (fkMedialVerticalSeamDart T i) = false
  · rw [dif_pos hs]
    apply ConnectedComponent.sound
    have hreach := fkMedialBoundaryStep_reachable pairing
      (fkMedialLocalMate pairing
        (fkMedialBondMate T (fkMedialVerticalSeamDart T i)))
    simpa [fkMedialBoundaryStep_apply, fkMedialLocalMate_involutive,
      fkMedialBondMate_involutive] using hreach
  · rw [dif_neg hs]
    apply ConnectedComponent.sound
    exact (fkMedial_reachable_localMate pairing
      (fkMedialVerticalSeamDart T i)).symm



theorem fkMedialLoopCanonicalVerticalFlux_eq_blackCycleContribution
    (pairing : FKMedialLoopPairing T) (d : FKMedialBlackDart T) :
    fkMedialLoopCanonicalVerticalFlux pairing
        ((fkMedialLoopGraph T pairing).connectedComponentMk d.1) =
      ∑ e : FKMedialBlackDart T,
        if (fkMedialBlackBoundaryPerm pairing).SameCycle d e then
          fkMedialBlackVerticalSeamContribution pairing e
        else 0 := by
  classical
  unfold fkMedialLoopCanonicalVerticalFlux
    fkMedialBlackVerticalSeamContribution
  calc
    (∑ i : Fin T.width,
        if (fkMedialLoopGraph T pairing).connectedComponentMk
              (fkMedialVerticalSeamDart T i) =
            (fkMedialLoopGraph T pairing).connectedComponentMk d.1 then
          fkMedialCanonicalVerticalSeamSign T i else 0) =
      ∑ i : Fin T.width, ∑ e : FKMedialBlackDart T,
        if (fkMedialBlackBoundaryPerm pairing).SameCycle d e then
          (if fkMedialVerticalSeamBlackDart pairing i = e then
            fkMedialCanonicalVerticalSeamSign T i else 0)
        else 0 := by
      apply Finset.sum_congr rfl
      intro i hi
      by_cases hcomponent :
          (fkMedialLoopGraph T pairing).connectedComponentMk
              (fkMedialVerticalSeamDart T i) =
            (fkMedialLoopGraph T pairing).connectedComponentMk d.1
      · rw [if_pos hcomponent]
        have hreach : (fkMedialLoopGraph T pairing).Reachable d.1
            (fkMedialVerticalSeamBlackDart pairing i).1 := by
          apply ConnectedComponent.exact
          rw [fkMedialVerticalSeamBlackDart_component]
          exact hcomponent.symm
        have hcycle : (fkMedialBlackBoundaryPerm pairing).SameCycle d
            (fkMedialVerticalSeamBlackDart pairing i) :=
          (fkMedial_blackBoundary_sameCycle_iff_reachable pairing _ _).2 hreach
        rw [Finset.sum_eq_single
          (fkMedialVerticalSeamBlackDart pairing i)]
        · simp [hcycle]
        · intro e he hne
          simp [hne.symm]
        · simp
      · rw [if_neg hcomponent]
        symm
        apply Finset.sum_eq_zero
        intro e he
        by_cases hie : fkMedialVerticalSeamBlackDart pairing i = e
        · subst e
          have hcycle : ¬ (fkMedialBlackBoundaryPerm pairing).SameCycle d
              (fkMedialVerticalSeamBlackDart pairing i) := by
            intro h
            apply hcomponent
            have hreach :=
              (fkMedial_blackBoundary_sameCycle_iff_reachable pairing _ _).1 h
            have hc := ConnectedComponent.sound hreach
            rw [fkMedialVerticalSeamBlackDart_component] at hc
            exact hc.symm
          simp [hcycle]
        · simp [hie]
    _ = ∑ e : FKMedialBlackDart T,
        if (fkMedialBlackBoundaryPerm pairing).SameCycle d e then
          ∑ i : Fin T.width,
            if fkMedialVerticalSeamBlackDart pairing i = e then
              fkMedialCanonicalVerticalSeamSign T i else 0
        else 0 := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro e he
      by_cases hcycle : (fkMedialBlackBoundaryPerm pairing).SameCycle d e
      · simp [hcycle]
      · simp [hcycle]



def fkMedialBlackVerticalWrapContribution
    (pairing : FKMedialLoopPairing T) (d : FKMedialBlackDart T) : Int :=
  let m := fkMedialLocalMate pairing d.1
  if m.2 = .north ∧ m.1.2 = svFinLast T.height_pos then -1
  else if m.2 = .south ∧
      m.1.2 = (⟨0, T.height_pos⟩ : Fin T.height) then 1
  else 0

private theorem verticalSucc_step_telescope {N : Nat} (hN : 0 < N)
    (j : Fin N) :
    (1 : Int) = ((finitePeriodicSucc hN j).val : Int) - (j.val : Int) -
      (N : Int) * (if j = svFinLast hN then -1 else 0) := by
  by_cases hj : j = svFinLast hN
  · subst j
    rw [finitePeriodicSucc_svFinLast]
    simp [svFinLast]
    omega
  · have hne : j.val + 1 ≠ N := by
      intro h
      apply hj
      apply Fin.ext
      simp [svFinLast]
      omega
    rw [finitePeriodicSucc_val]
    simp [hj, hne]

private theorem verticalPred_step_telescope {N : Nat} (hN : 0 < N)
    (j : Fin N) :
    (-1 : Int) =
      ((SixVertexArrows.cyclicPred hN j).val : Int) - (j.val : Int) -
        (N : Int) *
          (if j = (⟨0, hN⟩ : Fin N) then 1 else 0) := by
  by_cases hj : j = (⟨0, hN⟩ : Fin N)
  · subst j
    rw [if_pos rfl]
    simp only [SixVertexArrows.cyclicPred, Fin.val_mk, Nat.zero_add]
    rw [Nat.mod_eq_of_lt (Nat.sub_lt hN Nat.zero_lt_one)]
    rw [Nat.cast_sub hN]
    omega
  · have hjval : j.val ≠ 0 := by
      intro h
      apply hj
      apply Fin.ext
      simpa using h
    rw [if_neg hj]
    simp only [SixVertexArrows.cyclicPred, Fin.val_mk]
    have hjpos : 0 < j.val := Nat.pos_of_ne_zero hjval
    have hmod : (j.val + N - 1) % N = j.val - 1 := by
      have heq : j.val + N - 1 = (j.val - 1) + N := by omega
      rw [heq, Nat.add_mod_right, Nat.mod_eq_of_lt]
      omega
    simp only [mul_zero, sub_zero]
    change (-1 : Int) = (((j.val + N - 1) % N : Nat) : Int) - j.val
    rw [hmod]
    omega



theorem fkRectBlackBoundaryMedialStep_snd_eq_coordinate_sub_wrap
    (pairing : FKMedialLoopPairing T) (d : FKMedialBlackDart T) :
    (stepOf (fkRectBlackBoundaryMedialDirection pairing d)).2 =
      (((fkMedialBlackBoundaryPerm pairing d).1.1.2.val : Nat) : Int) -
        ((d.1.1.2.val : Nat) : Int) -
        (T.height : Int) *
          fkMedialBlackVerticalWrapContribution pairing d := by
  rcases d with ⟨⟨⟨i, j⟩, side⟩, hd⟩
  cases hp : pairing (i, j) <;> cases side
  all_goals
    simp only [fkRectBlackBoundaryMedialDirection,
      fkRectMedialSideDirection, fkMedialBlackBoundaryPerm_val,
      fkMedialBlackVerticalWrapContribution, fkMedialLocalMate,
      fkMedialBondMate, hp, stepOf]
  all_goals try simpa [mul_ite] using
    (verticalSucc_step_telescope T.height_pos j)
  all_goals try simpa [mul_ite] using
    (verticalPred_step_telescope T.height_pos j)


theorem fkMedialBlackVerticalWrapContribution_seamBlackDart
    (pairing : FKMedialLoopPairing T) (i : Fin T.width) :
    fkMedialBlackVerticalWrapContribution pairing
        (fkMedialVerticalSeamBlackDart pairing i) =
      fkMedialCanonicalVerticalSeamSign T i := by
  let s := fkMedialVerticalSeamDart T i
  by_cases hs : fkMedialCheckerColor s = false
  · have hs' : fkMedialCheckerColor
        (fkMedialVerticalSeamDart T i) = false := by
      simpa [s] using hs
    unfold fkMedialVerticalSeamBlackDart
    dsimp only
    rw [dif_pos hs']
    simp [fkMedialBlackVerticalWrapContribution,
      fkMedialLocalMate_involutive, fkMedialBondMate,
      fkMedialVerticalSeamDart, finitePeriodicSucc_svFinLast,
      fkMedialCanonicalVerticalSeamSign]
    simpa [fkMedialVerticalSeamDart] using hs'
  · have hs' : fkMedialCheckerColor
        (fkMedialVerticalSeamDart T i) = true := by
      exact Bool.eq_true_of_not_eq_false (by simpa [s] using hs)
    unfold fkMedialVerticalSeamBlackDart
    dsimp only
    rw [dif_neg (by simp [hs'])]
    simp [fkMedialBlackVerticalWrapContribution,
      fkMedialLocalMate_involutive, fkMedialVerticalSeamDart,
      fkMedialCanonicalVerticalSeamSign]
    simpa [fkMedialVerticalSeamDart] using hs'



theorem exists_verticalSeamBlackDart_of_wrapContribution_ne_zero
    (pairing : FKMedialLoopPairing T) (d : FKMedialBlackDart T)
    (hwrap : fkMedialBlackVerticalWrapContribution pairing d ≠ 0) :
    ∃ i : Fin T.width, fkMedialVerticalSeamBlackDart pairing i = d := by
  let m := fkMedialLocalMate pairing d.1
  unfold fkMedialBlackVerticalWrapContribution at hwrap
  dsimp only at hwrap
  split at hwrap
  next hnorth =>
    rcases hnorth with ⟨hside, hy⟩
    let i : Fin T.width := m.1.1
    have hm : m = fkMedialVerticalSeamDart T i := by
      change m.2 = .north at hside
      change m.1.2 = svFinLast T.height_pos at hy
      rcases m with ⟨⟨mi, mj⟩, mside⟩
      simp_all [i, fkMedialVerticalSeamDart]
    have hcolor : fkMedialCheckerColor (fkMedialVerticalSeamDart T i) = true := by
      rw [← hm, fkMedialCheckerColor_localMate_eq_not, d.2]
      rfl
    refine ⟨i, ?_⟩
    unfold fkMedialVerticalSeamBlackDart
    dsimp only
    rw [dif_neg (by simp [hcolor])]
    apply Subtype.ext
    change fkMedialLocalMate pairing (fkMedialVerticalSeamDart T i) = d.1
    rw [← hm, fkMedialLocalMate_involutive]
  next hnotNorth =>
    split at hwrap
    next hsouth =>
      rcases hsouth with ⟨hside, hy⟩
      let i : Fin T.width := m.1.1
      have hm : fkMedialBondMate T (fkMedialVerticalSeamDart T i) = m := by
        change m.2 = .south at hside
        change m.1.2 = (⟨0, T.height_pos⟩ : Fin T.height) at hy
        rcases m with ⟨⟨mi, mj⟩, mside⟩
        simp_all [i, fkMedialVerticalSeamDart, fkMedialBondMate,
          finitePeriodicSucc_svFinLast]
      have hmcolor : fkMedialCheckerColor m = true := by
        change fkMedialCheckerColor (fkMedialLocalMate pairing d.1) = true
        rw [fkMedialCheckerColor_localMate_eq_not, d.2]
        rfl
      have hcolor : fkMedialCheckerColor
          (fkMedialVerticalSeamDart T i) = false := by
        have hne := fkMedialCheckerColor_bondMate_ne T
          (fkMedialVerticalSeamDart T i)
        rw [hm, hmcolor] at hne
        cases h : fkMedialCheckerColor (fkMedialVerticalSeamDart T i) <;>
          simp_all
      refine ⟨i, ?_⟩
      unfold fkMedialVerticalSeamBlackDart
      dsimp only
      rw [dif_pos hcolor]
      apply Subtype.ext
      change fkMedialLocalMate pairing
          (fkMedialBondMate T (fkMedialVerticalSeamDart T i)) = d.1
      rw [hm]
      exact fkMedialLocalMate_involutive pairing d.1
    next hneither => simp at hwrap



theorem fkMedialBlackVerticalSeamContribution_eq_wrapContribution
    (pairing : FKMedialLoopPairing T) (d : FKMedialBlackDart T) :
    fkMedialBlackVerticalSeamContribution pairing d =
      fkMedialBlackVerticalWrapContribution pairing d := by
  classical
  by_cases himage : ∃ i : Fin T.width,
      fkMedialVerticalSeamBlackDart pairing i = d
  · obtain ⟨i, hi⟩ := himage
    subst d
    unfold fkMedialBlackVerticalSeamContribution
    rw [Finset.sum_eq_single i]
    · simp [fkMedialBlackVerticalWrapContribution_seamBlackDart]
    · intro j hj hji
      rw [if_neg]
      intro hrep
      exact hji (fkMedialVerticalSeamBlackDart_injective pairing hrep)
    · simp
  · have hwrap : fkMedialBlackVerticalWrapContribution pairing d = 0 := by
      by_contra hne
      exact himage
        (exists_verticalSeamBlackDart_of_wrapContribution_ne_zero
          pairing d hne)
    rw [hwrap]
    unfold fkMedialBlackVerticalSeamContribution
    apply Finset.sum_eq_zero
    intro i hi
    simp only [ite_eq_right_iff]
    exact fun hrep => (himage ⟨i, hrep⟩).elim



theorem fkRectBlackOrbitVerticalWrapSum_eq_neg_winding
    (R : FKRectTorus) (omega : R.Configuration)
    (d : FKMedialBlackDart R.medialTorus) :
    let pairing := fkRectConfigurationToMedialPairing R omega
    let l := fkRectBlackOrbitList pairing d
    (∑ i : Fin l.length,
      fkMedialBlackVerticalWrapContribution pairing (l.get i)) =
        -(fkRectWalkWinding R
          (fkRectBlackBoundaryPrimalCycleWalk R omega d)).2 := by
  dsimp only
  let pairing := fkRectConfigurationToMedialPairing R omega
  let l := fkRectBlackOrbitList pairing d
  have hn : 0 < l.length := fkRectBlackOrbitList_length_pos pairing d
  letI : NeZero l.length := ⟨hn.ne'⟩
  let e : Fin l.length → FKMedialBlackDart R.medialTorus := l.get
  let y : Fin l.length → Int := fun i => ((e i).1.1.2.val : Nat)
  let c : Fin l.length → Int := fun i =>
    fkMedialBlackVerticalWrapContribution pairing (e i)
  have hnext (i : Fin l.length) :
      e (i + 1) = fkMedialBlackBoundaryPerm pairing (e i) := by
    exact fkRectBlackOrbitList_get_add_one pairing d i
  have hlocal (i : Fin l.length) :
      (stepOf (fkRectBlackBoundaryMedialDirection pairing (e i))).2 =
        y (i + 1) - y i - (R.height : Int) * c i := by
    have h := fkRectBlackBoundaryMedialStep_snd_eq_coordinate_sub_wrap
      pairing (e i)
    rw [← hnext i] at h
    exact h
  have hy : (∑ i, y (i + 1)) = ∑ i, y i := by
    change (∑ i, y ((Equiv.addRight (1 : Fin l.length)) i)) = _
    exact Equiv.sum_comp (Equiv.addRight (1 : Fin l.length)) y
  have hsum :
      (∑ i, (stepOf
        (fkRectBlackBoundaryMedialDirection pairing (e i))).2) =
        -(R.height : Int) * ∑ i, c i := by
    calc
      (∑ i, (stepOf
          (fkRectBlackBoundaryMedialDirection pairing (e i))).2) =
          ∑ i, (y (i + 1) - y i - (R.height : Int) * c i) := by
            apply Finset.sum_congr rfl
            intro i hi
            exact hlocal i
      _ = -(R.height : Int) * ∑ i, c i := by
        rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib,
          Finset.mul_sum, hy]
        rw [sub_self, zero_sub]
        simp
  have hdisp := fkRectBlackOrbitMedialDisplacement_eq_winding R omega d
  change ons_pathDisplacement (List.ofFn fun i =>
      fkRectBlackBoundaryMedialDirection pairing (e i)) = _ at hdisp
  rw [ons_pathDisplacement_ofFn] at hdisp
  have hsnd := congrArg Prod.snd hdisp
  have hsnd' :
      (∑ i, (stepOf
        (fkRectBlackBoundaryMedialDirection pairing (e i))).2) =
        (R.height : Int) *
          (fkRectWalkWinding R
            (fkRectBlackBoundaryPrimalCycleWalk R omega d)).2 := by
    simpa only [Prod.snd_sum, Prod.snd] using hsnd
  have hheight : (0 : Int) < R.height := by exact_mod_cast R.height_pos
  change (∑ i, c i) = _
  nlinarith



theorem fkMedialBlackCycleWrapContribution_eq_orbitSum
    (pairing : FKMedialLoopPairing T) (d : FKMedialBlackDart T) :
    (∑ e : FKMedialBlackDart T,
      if (fkMedialBlackBoundaryPerm pairing).SameCycle d e then
        fkMedialBlackVerticalWrapContribution pairing e else 0) =
      ∑ i : Fin (fkRectBlackOrbitList pairing d).length,
        fkMedialBlackVerticalWrapContribution pairing
          ((fkRectBlackOrbitList pairing d).get i) := by
  classical
  let p := fkMedialBlackBoundaryPerm pairing
  let l := fkRectBlackOrbitList pairing d
  let f : FKMedialBlackDart T → Int :=
    fkMedialBlackVerticalWrapContribution pairing
  have hsupport : d ∈ p.support := by
    rw [Equiv.Perm.mem_support]
    exact fkMedialBlackBoundaryPerm_apply_ne pairing d
  calc
    (∑ e : FKMedialBlackDart T, if p.SameCycle d e then f e else 0) =
        ∑ e ∈ l.toFinset, f e := by
      rw [← Finset.sum_filter]
      congr 1
      ext e
      simp only [Finset.mem_filter, Finset.mem_univ, true_and,
        List.mem_toFinset]
      change p.SameCycle d e ↔ e ∈ p.toList d
      rw [Equiv.Perm.mem_toList_iff]
      simp [hsupport]
    _ = (l.map f).sum := by
      exact List.sum_toFinset f (by
        simpa [l, p] using Equiv.Perm.nodup_toList p d)
    _ = ∑ i : Fin l.length, f (l.get i) := by
      rw [← List.sum_ofFn]
      exact congrArg List.sum (by
        simpa [List.get_eq_getElem] using
          (List.ofFn_getElem_eq_map l f).symm)



theorem fkMedialLoopCanonicalVerticalFlux_eq_neg_blackBoundaryWinding
    (R : FKRectTorus) (omega : R.Configuration)
    (d : FKMedialBlackDart R.medialTorus) :
    let pairing := fkRectConfigurationToMedialPairing R omega
    fkMedialLoopCanonicalVerticalFlux pairing
        ((fkMedialLoopGraph R.medialTorus pairing).connectedComponentMk d.1) =
      -(fkRectWalkWinding R
        (fkRectBlackBoundaryPrimalCycleWalk R omega d)).2 := by
  dsimp only
  let pairing := fkRectConfigurationToMedialPairing R omega
  rw [fkMedialLoopCanonicalVerticalFlux_eq_blackCycleContribution]
  simp_rw [fkMedialBlackVerticalSeamContribution_eq_wrapContribution]
  rw [fkMedialBlackCycleWrapContribution_eq_orbitSum]
  exact fkRectBlackOrbitVerticalWrapSum_eq_neg_winding R omega d



theorem one_le_fkMedialUnorientedVerticalWindingTotal_of_blackBoundary
    (R : FKRectTorus) (omega : R.Configuration)
    (d : FKMedialBlackDart R.medialTorus)
    (hvertical : (fkRectWalkWinding R
      (fkRectBlackBoundaryPrimalCycleWalk R omega d)).2 ≠ 0) :
    1 ≤ fkMedialUnorientedVerticalWindingTotal
      (fkRectConfigurationToMedialPairing R omega) := by
  let pairing := fkRectConfigurationToMedialPairing R omega
  let C := (fkMedialLoopGraph R.medialTorus pairing).connectedComponentMk d.1
  have hflux : fkMedialLoopCanonicalVerticalFlux pairing C ≠ 0 := by
    rw [show C = (fkMedialLoopGraph R.medialTorus pairing).connectedComponentMk
      d.1 from rfl,
      fkMedialLoopCanonicalVerticalFlux_eq_neg_blackBoundaryWinding]
    exact neg_ne_zero.mpr hvertical
  have hmem : C ∈ fkMedialVerticallyWindingComponents pairing := by
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ C, hflux⟩
  have hcard : 1 ≤ (fkMedialVerticallyWindingComponents pairing).card := by
    exact Finset.one_le_card.mpr ⟨C, hmem⟩
  exact hcard.trans
    (card_fkMedialVerticallyWindingComponents_le_total pairing)




theorem one_le_fkMedialUnorientedVerticalWindingTotal_of_boundaryOrbit
    (R : FKRectTorus) (omega : R.Configuration)
    (d : FKMedialDart R.medialTorus)
    (hvertical : (fkRectWalkWinding R
      (fkRectMedialBoundaryPrimalOrbitWalk R omega d)).2 ≠ 0) :
    1 ≤ fkMedialUnorientedVerticalWindingTotal
      (fkRectConfigurationToMedialPairing R omega) := by
  let pairing := fkRectConfigurationToMedialPairing R omega
  have blackCase (bd : FKMedialBlackDart R.medialTorus)
      (horbit : (fkRectWalkWinding R
        (fkRectMedialBoundaryPrimalOrbitWalk R omega bd.1)).2 ≠ 0) :
      1 ≤ fkMedialUnorientedVerticalWindingTotal pairing := by
    have hscale := congrArg Prod.snd
      (fkRectMedialBoundaryPrimalOrbitWalk_winding_eq_nsmul_blackCycle
        R omega bd)
    have hcycle : (fkRectWalkWinding R
        (fkRectBlackBoundaryPrimalCycleWalk R omega bd)).2 ≠ 0 := by
      intro hzero
      simp only [Prod.smul_snd] at hscale
      rw [hzero, smul_zero] at hscale
      exact horbit hscale
    exact one_le_fkMedialUnorientedVerticalWindingTotal_of_blackBoundary
      R omega bd hcycle
  cases hd : fkMedialCheckerColor d
  · exact blackCase ⟨d, hd⟩ hvertical
  · let d' := fkMedialLocalMate pairing d
    have hd' : fkMedialCheckerColor d' = false := by
      simp [d', fkMedialCheckerColor_localMate_eq_not, hd]
    have hvertical' : (fkRectWalkWinding R
        (fkRectMedialBoundaryPrimalOrbitWalk R omega d')).2 ≠ 0 := by
      have hneg := congrArg Prod.snd
        (fkRectMedialBoundaryPrimalOrbitWalk_winding_localMate R omega d)
      change (fkRectWalkWinding R
          (fkRectMedialBoundaryPrimalOrbitWalk R omega d')).2 =
        _ at hneg
      simp only [Prod.snd_neg] at hneg
      intro hzero
      apply hvertical
      rw [hzero] at hneg
      exact neg_eq_zero.mp hneg.symm
    exact blackCase ⟨d', hd'⟩ hvertical'

end

end StatMech.FrontierD

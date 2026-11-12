/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.FrontierA.TriangularIsingTorusBaseSpin
import Code.Onsager.PeriodicTurnClosure










open scoped BigOperators

namespace StatMech.FrontierA

open StatMech.Onsager
open StatMech.Onsager.BaseCase

def triangularPathDisplacement : List (Fin 6) -> Int × Int
  | [] => 0
  | d :: ds => triangularIntStep d + triangularPathDisplacement ds

def triangularPathVertices : List (Fin 6) -> List (Int × Int)
  | [] => [0]
  | d :: ds =>
      0 :: (triangularPathVertices ds).map (triangularIntStep d + ·)

@[simp] theorem triangularPathDisplacement_nil :
    triangularPathDisplacement [] = 0 := rfl

@[simp] theorem triangularPathDisplacement_cons
    (d : Fin 6) (ds : List (Fin 6)) :
    triangularPathDisplacement (d :: ds) =
      triangularIntStep d + triangularPathDisplacement ds := rfl

@[simp] theorem triangularPathVertices_nil :
    triangularPathVertices [] = [0] := rfl

@[simp] theorem triangularPathVertices_cons
    (d : Fin 6) (ds : List (Fin 6)) :
    triangularPathVertices (d :: ds) =
      0 :: (triangularPathVertices ds).map (triangularIntStep d + ·) := rfl

theorem triangularPathDisplacement_append (l r : List (Fin 6)) :
    triangularPathDisplacement (l ++ r) =
      triangularPathDisplacement l + triangularPathDisplacement r := by
  induction l with
  | nil => simp
  | cons d ds ih => simp only [List.cons_append,
      triangularPathDisplacement_cons, ih]; abel

@[simp] theorem triangularPathVertices_length (l : List (Fin 6)) :
    (triangularPathVertices l).length = l.length + 1 := by
  induction l with
  | nil => rfl
  | cons d ds ih => simp [ih]

@[simp] theorem triangularPathVertices_head (l : List (Fin 6)) :
    (triangularPathVertices l).head? = some 0 := by
  cases l <;> rfl

theorem triangularPathVertices_getLast (l : List (Fin 6)) :
    (triangularPathVertices l).getLast? =
      some (triangularPathDisplacement l) := by
  induction l with
  | nil => rfl
  | cons d ds ih =>
      simp only [triangularPathVertices_cons, List.getLast?_cons,
        List.getLast?_map, ih, Option.map_some,
        triangularPathDisplacement_cons]
      simp

theorem triangularPathVertices_append (l r : List (Fin 6)) :
    triangularPathVertices (l ++ r) =
      (triangularPathVertices l).dropLast ++
        (triangularPathVertices r).map
          (triangularPathDisplacement l + ·) := by
  induction l with
  | nil => simp
  | cons d ds ih =>
      have hmap :
          (triangularPathVertices ds).map (triangularIntStep d + ·) ≠ [] := by
        intro h
        have hlen := congrArg List.length h
        rw [List.length_map, triangularPathVertices_length] at hlen
        simp at hlen
      simp only [List.cons_append, triangularPathVertices_cons, ih,
        List.map_append, List.map_map,
        List.dropLast_cons_of_ne_nil hmap,
        <- List.map_dropLast, triangularPathDisplacement_cons]
      congr 2
      apply List.map_congr_left
      intro z hz
      simp only [Function.comp_apply]
      abel

theorem triangularPathVertices_append_dropLast (l r : List (Fin 6)) :
    (triangularPathVertices (l ++ r)).dropLast =
      (triangularPathVertices l).dropLast ++
        (triangularPathVertices r).dropLast.map
          (triangularPathDisplacement l + ·) := by
  rw [triangularPathVertices_append]
  have hne :
      (triangularPathVertices r).map
          (triangularPathDisplacement l + ·) ≠ [] := by
    intro h
    have hlen := congrArg List.length h
    rw [List.length_map, triangularPathVertices_length] at hlen
    simp at hlen
  rw [List.dropLast_append_of_ne_nil hne, <- List.map_dropLast]

def triangularAxisDirection : Fin 4 -> Fin 6 := ![1, 3, 0, 2]

@[simp] theorem triangularIntStep_axisDirection (d : Fin 4) :
    triangularIntStep (triangularAxisDirection d) = stepOf d := by
  fin_cases d <;> rfl

theorem triangularPathDisplacement_map_axis (l : List (Fin 4)) :
    triangularPathDisplacement (l.map triangularAxisDirection) =
      ons_pathDisplacement l := by
  induction l with
  | nil => rfl
  | cons d ds ih =>
      simp only [List.map_cons, triangularPathDisplacement_cons,
        ons_pathDisplacement_cons, triangularIntStep_axisDirection, ih]

theorem triangularPathVertices_map_axis (l : List (Fin 4)) :
    triangularPathVertices (l.map triangularAxisDirection) =
      ons_pathVertices l := by
  induction l with
  | nil => rfl
  | cons d ds ih =>
      simp only [List.map_cons, triangularPathVertices_cons,
        ons_pathVertices_cons, triangularIntStep_axisDirection, ih]

def triangularOutsideConnector (dx dy top : Int) : List (Fin 6) :=
  (ons_outsideConnector dx dy top).map triangularAxisDirection

theorem triangularOutsideConnector_displacement
    (dx dy top : Int) (hdx : 0 < dx) (hdy : dy < top)
    (htop : 0 < top) :
    triangularPathDisplacement (triangularOutsideConnector dx dy top) =
      (-dx, -dy) := by
  rw [triangularOutsideConnector, triangularPathDisplacement_map_axis]
  exact ons_outsideConnector_displacement dx dy top hdx hdy htop

theorem triangularOutsideConnector_vertices_dropLast_nodup
    (dx dy top : Int) (hdx : 0 < dx) (hdy : dy < top)
    (htop : 0 < top) :
    (triangularPathVertices
      (triangularOutsideConnector dx dy top)).dropLast.Nodup := by
  rw [triangularOutsideConnector, triangularPathVertices_map_axis]
  exact ons_outsideConnector_vertices_dropLast_nodup
    dx dy top hdx hdy htop

theorem triangularPathDisplacement_not_mem_dropLast_of_vertices_nodup
    (l : List (Fin 6)) (hnodup : (triangularPathVertices l).Nodup) :
    triangularPathDisplacement l ∉ (triangularPathVertices l).dropLast := by
  have hne : triangularPathVertices l ≠ [] := by
    intro h
    have := congrArg List.length h
    simp at this
  have hlast : (triangularPathVertices l).getLast hne =
      triangularPathDisplacement l := by
    have h := triangularPathVertices_getLast l
    rw [List.getLast?_eq_getLast hne] at h
    exact Option.some.inj h
  rw [<- List.dropLast_append_getLast hne] at hnodup
  have hdisj := (List.nodup_append.mp hnodup).2.2
  intro hmem
  exact hdisj (triangularPathDisplacement l) hmem
    ((triangularPathVertices l).getLast hne) (by simp) hlast.symm

theorem triangularOutsideConnector_shift_disjoint
    (l : List (Fin 6)) (dx dy top : Int)
    (hdx : 0 < dx) (hdy : dy < top) (htop : 0 < top)
    (hdisp : triangularPathDisplacement l = (dx, dy))
    (hnodup : (triangularPathVertices l).Nodup)
    (hxmin : ∀ z ∈ (triangularPathVertices l).dropLast, 0 ≤ z.1)
    (hxmax : ∀ z ∈ (triangularPathVertices l).dropLast, z.1 ≤ dx)
    (hymax : ∀ z ∈ (triangularPathVertices l).dropLast, z.2 < top) :
    ∀ z ∈ (triangularPathVertices l).dropLast,
      ∀ w ∈ (triangularPathVertices
        (triangularOutsideConnector dx dy top)).dropLast,
        z ≠ triangularPathDisplacement l + w := by
  intro z hz w hw heq
  have hend : (dx, dy) ∉ (triangularPathVertices l).dropLast := by
    simpa [hdisp] using
      triangularPathDisplacement_not_mem_dropLast_of_vertices_nodup l hnodup
  rw [triangularOutsideConnector, triangularPathVertices_map_axis] at hw
  rcases ons_mem_outsideConnector_vertices_dropLast
      dx dy top hdx hdy htop w hw with
    rfl | ⟨k, hk, rfl⟩ | ⟨k, hk, rfl⟩ |
      ⟨k, hk, rfl⟩ | rfl
  · have hzeq : z = (dx, dy) := by simpa [hdisp] using heq
    exact hend (hzeq ▸ hz)
  · have hx := congrArg Prod.fst heq
    have := hxmax z hz
    simp [hdisp] at hx
    omega
  · have hy := congrArg Prod.snd heq
    have := hymax z hz
    have hk' : (k : Int) < dx + 2 := by
      simpa [Int.toNat_of_nonneg (show 0 ≤ dx + 2 by omega)] using hk
    simp [hdisp] at hy
    omega
  · have hx := congrArg Prod.fst heq
    have := hxmin z hz
    simp [hdisp] at hx
    omega
  · have hx := congrArg Prod.fst heq
    have := hxmin z hz
    simp [hdisp] at hx
    omega

theorem triangularBoundingClosure_vertices_dropLast_nodup
    (l : List (Fin 6)) (dx dy top : Int)
    (hdx : 0 < dx) (hdy : dy < top) (htop : 0 < top)
    (hdisp : triangularPathDisplacement l = (dx, dy))
    (hnodup : (triangularPathVertices l).Nodup)
    (hxmin : ∀ z ∈ (triangularPathVertices l).dropLast, 0 ≤ z.1)
    (hxmax : ∀ z ∈ (triangularPathVertices l).dropLast, z.1 ≤ dx)
    (hymax : ∀ z ∈ (triangularPathVertices l).dropLast, z.2 < top) :
    (triangularPathVertices
      (l ++ triangularOutsideConnector dx dy top)).dropLast.Nodup := by
  rw [triangularPathVertices_append_dropLast]
  have hleft : (triangularPathVertices l).dropLast.Nodup :=
    List.Nodup.sublist (List.dropLast_sublist _) hnodup
  have hright :
      ((triangularPathVertices
        (triangularOutsideConnector dx dy top)).dropLast.map
          (triangularPathDisplacement l + ·)).Nodup :=
    (triangularOutsideConnector_vertices_dropLast_nodup
      dx dy top hdx hdy htop).map (add_right_injective _)
  apply List.Nodup.append hleft hright
  rw [List.disjoint_iff_ne]
  intro z hz b hb
  rw [List.mem_map] at hb
  obtain ⟨w, hw, rfl⟩ := hb
  exact triangularOutsideConnector_shift_disjoint l dx dy top
    hdx hdy htop hdisp hnodup hxmin hxmax hymax z hz w hw

theorem triangularPeriodicIntPos_succ_cast
    {m : Nat} (direction : Fin (m + 1) -> Fin 6) (i : Fin m) :
    triangularIntPos direction i.succ =
      triangularIntPos direction i.castSucc +
        triangularIntStep (direction i.castSucc) := by
  have hfilter :
      (Finset.univ.filter (fun j : Fin (m + 1) => j < i.succ)) =
        insert i.castSucc
          (Finset.univ.filter
            (fun j : Fin (m + 1) => j < i.castSucc)) := by
    apply Finset.ext
    intro j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_insert]
    constructor
    · intro hj
      rw [Fin.lt_def] at hj
      simp only [Fin.val_succ] at hj
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hlt | heq
      · exact Or.inr (Fin.lt_def.mpr hlt)
      · exact Or.inl (Fin.ext heq)
    · rintro (rfl | hj)
      · exact Fin.castSucc_lt_succ
      · exact hj.trans Fin.castSucc_lt_succ
  have hnotmem : i.castSucc ∉
      (Finset.univ.filter
        (fun j : Fin (m + 1) => j < i.castSucc)) := by simp
  rw [triangularIntPos, triangularIntPos, hfilter,
    Finset.sum_insert hnotmem, add_comm]

theorem triangularPos_succ_eq_head_add_pos_tail
    {n : Nat} [NeZero n] (d : Fin (n + 1) -> Fin 6) (i : Fin n) :
    triangularIntPos d i.succ =
      triangularIntStep (d 0) +
        triangularIntPos (fun j : Fin n => d j.succ) i := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne n)
  induction i using Fin.induction with
  | zero =>
      rw [triangularPeriodicIntPos_succ_cast d 0]
      simp [triangularIntPos]
  | succ i ih =>
      rw [triangularPeriodicIntPos_succ_cast d i.succ]
      have hi : i.succ.castSucc = i.castSucc.succ := Fin.ext rfl
      rw [hi, ih,
        triangularPeriodicIntPos_succ_cast (fun j => d j.succ) i]
      abel

theorem triangularPathVertices_dropLast_eq_ofFn_pos
    (l : List (Fin 6)) [NeZero l.length] :
    (triangularPathVertices l).dropLast =
      List.ofFn (triangularIntPos (fun i : Fin l.length => l.get i)) := by
  have hl : l ≠ [] := by
    intro h
    subst l
    exact NeZero.ne 0 rfl
  obtain ⟨d, ds, rfl⟩ := List.exists_cons_of_ne_nil hl
  cases ds with
  | nil => simp [triangularPathVertices, List.ofFn_succ, triangularIntPos]
  | cons e es =>
      letI : NeZero (e :: es).length := ⟨by simp⟩
      have ih := triangularPathVertices_dropLast_eq_ofFn_pos (e :: es)
      have hmap :
          (triangularPathVertices (e :: es)).map
            (triangularIntStep d + ·) ≠ [] := by simp
      rw [triangularPathVertices_cons,
        List.dropLast_cons_of_ne_nil hmap, <- List.map_dropLast, ih]
      conv_rhs => rw [List.ofFn_succ]
      change 0 :: _ = triangularIntPos
        (fun i : Fin (d :: e :: es).length => (d :: e :: es).get i) 0 :: _
      rw [show triangularIntPos
        (fun i : Fin (d :: e :: es).length => (d :: e :: es).get i) 0 = 0 by
          simp [triangularIntPos]]
      congr 1
      rw [List.map_ofFn]
      congr 1
      funext i
      exact (triangularPos_succ_eq_head_add_pos_tail
        (fun j : Fin ((e :: es).length + 1) => (d :: e :: es).get j) i).symm

theorem triangularPos_get_injective_of_vertices_dropLast_nodup
    (l : List (Fin 6)) [NeZero l.length]
    (hnodup : (triangularPathVertices l).dropLast.Nodup) :
    Function.Injective
      (triangularIntPos (fun i : Fin l.length => l.get i)) := by
  rw [triangularPathVertices_dropLast_eq_ofFn_pos] at hnodup
  exact List.nodup_ofFn.mp hnodup

theorem triangularPathDisplacement_eq_sum_map (l : List (Fin 6)) :
    triangularPathDisplacement l = (l.map triangularIntStep).sum := by
  induction l with
  | nil => rfl
  | cons d ds ih => simp [ih]

theorem triangularPathDisplacement_ofFn
    {n : Nat} (d : Fin n -> Fin 6) :
    triangularPathDisplacement (List.ofFn d) =
      ∑ i, triangularIntStep (d i) := by
  rw [triangularPathDisplacement_eq_sum_map, List.map_ofFn, List.sum_ofFn]
  simp [Function.comp_def]

theorem triangularSimpleList_phaseCycle_eq_neg_one
    (l : List (Fin 6)) [NeZero l.length]
    (hclosed : triangularPathDisplacement l = 0)
    (hsimple : (triangularPathVertices l).dropLast.Nodup)
    (hlen : 3 ≤ l.length) :
    kwVectorPhaseCycle (l.map triangularIntVector) = -1 := by
  let d : Fin l.length -> Fin 6 := fun i => l.get i
  have hsum : ∑ i, triangularIntStep (d i) = 0 := by
    rw [<- triangularPathDisplacement_ofFn, List.ofFn_get]
    exact hclosed
  have hinj : Function.Injective (triangularIntPos d) :=
    triangularPos_get_injective_of_vertices_dropLast_nodup l hsimple
  let polygon := triangularIntSimplePolygon d hsum hlen hinj
  have hpolygon := kwFiniteSimplePolygonPhaseSign_adaptive polygon
  have hedges : polygon.edgeList =
      List.ofFn (fun i => triangularIntVector (d i)) := by
    unfold KWFiniteSimplePolygon.edgeList
    congr 1
    funext i
    dsimp only [polygon]
    exact triangularIntSimplePolygon_edgeVector d hsum hlen hinj i
  rw [hedges] at hpolygon
  simpa [d, <- List.map_ofFn] using hpolygon

def triangularPeriodStateCoord {n : Nat} [NeZero n]
    (d : Fin n -> Fin 6) (z : Nat × Fin n) : Int × Int :=
  triangularIntPos d z.2 +
    z.1 • triangularPathDisplacement (List.ofFn d)

def triangularPeriodicArcDirections {n : Nat}
    (d : Fin n -> Fin 6) (N : Nat) (imin imax : Fin n) : List (Fin 6) :=
  (ons_periodicArcStates N imin imax).dropLast.map (fun z => d z.2)

theorem triangularPeriodStateList_isChain {n : Nat} [NeZero n]
    (d : Fin n -> Fin 6) (r : Nat) :
    List.IsChain
      (fun a b => triangularPeriodStateCoord d b =
        triangularPeriodStateCoord d a + triangularIntStep (d a.2))
      (ons_periodStateList n r) := by
  rw [ons_periodStateList, List.isChain_ofFn]
  intro i hi
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne n)
  let j : Fin m := ⟨i, by omega⟩
  have hjc : (j.castSucc : Fin (m + 1)) = ⟨i, by omega⟩ := Fin.ext rfl
  have hjs : (j.succ : Fin (m + 1)) = ⟨i + 1, hi⟩ := Fin.ext rfl
  simp only [triangularPeriodStateCoord]
  rw [<- hjc, <- hjs, triangularPeriodicIntPos_succ_cast]
  abel

theorem triangularPeriodState_boundary {m : Nat}
    (d : Fin (m + 1) -> Fin 6) (r : Nat) :
    triangularPeriodStateCoord d (r + 1, 0) =
      triangularPeriodStateCoord d (r, Fin.last m) +
        triangularIntStep (d (Fin.last m)) := by
  simp only [triangularPeriodStateCoord]
  rw [triangularIntPos_zero, zero_add]
  have hdisp : triangularPathDisplacement (List.ofFn d) =
      triangularIntPos d (Fin.last m) +
        triangularIntStep (d (Fin.last m)) := by
    rw [triangularPathDisplacement_ofFn, Fin.sum_univ_castSucc]
    congr 1
    unfold triangularIntPos
    apply Finset.sum_bij (fun i _ => i.castSucc)
    · intro i hi
      simp
    · intro i hi j hj heq
      apply Fin.ext
      exact congrArg (fun x : Fin (m + 1) => x.val) heq
    · intro j hj
      have hjlt : j < Fin.last m := (Finset.mem_filter.mp hj).2
      have hjlast : j ≠ Fin.last m := ne_of_lt hjlt
      obtain ⟨i, rfl⟩ := Fin.exists_castSucc_eq.mpr hjlast
      exact ⟨i, Finset.mem_univ _, rfl⟩
    · intro i hi
      rfl
  rw [succ_nsmul, hdisp]
  abel

theorem triangularAllPeriodStates_isChain {n : Nat} [NeZero n]
    (d : Fin n -> Fin 6) (N : Nat) :
    List.IsChain
      (fun a b => triangularPeriodStateCoord d b =
        triangularPeriodStateCoord d a + triangularIntStep (d a.2))
      (ons_allPeriodStates n N) := by
  induction N with
  | zero =>
      simpa [ons_allPeriodStates] using triangularPeriodStateList_isChain d 0
  | succ N ih =>
      rw [ons_allPeriodStates, List.range_succ, List.flatMap_append]
      simp only [List.flatMap_singleton]
      apply List.IsChain.append
        (by simpa [ons_allPeriodStates] using ih)
        (triangularPeriodStateList_isChain d (N + 1))
      intro a ha b hb
      have ha' : a = (N, ons_lastFin n) := by
        change a ∈ (ons_allPeriodStates n N).getLast? at ha
        rw [ons_allPeriodStates_getLast?] at ha
        symm
        simpa using ha
      have hb' : b = (N + 1, (0 : Fin n)) := by
        change b ∈ (ons_periodStateList n (N + 1)).head? at hb
        rw [ons_periodStateList_head?] at hb
        symm
        simpa using hb
      rw [ha', hb']
      obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne n)
      exact triangularPeriodState_boundary d N

theorem triangularPeriodicArcStates_isChain {n : Nat} [NeZero n]
    (d : Fin n -> Fin 6) (N : Nat) (imin imax : Fin n) :
    List.IsChain
      (fun a b => triangularPeriodStateCoord d b =
        triangularPeriodStateCoord d a + triangularIntStep (d a.2))
      (ons_periodicArcStates N imin imax) := by
  exact (triangularAllPeriodStates_isChain d N).drop imin.val |>.take _

theorem triangularPathVertices_map_dropLast_of_chain
    {X : Type*} [Inhabited X]
    (coord : X -> Int × Int) (dir : X -> Fin 6)
    (s : List X) (hs : s ≠ [])
    (hchain : List.IsChain
      (fun a b => coord b = coord a + triangularIntStep (dir a)) s) :
    triangularPathVertices (s.dropLast.map dir) =
      s.map (fun x => coord x - coord s.head!) := by
  induction s with
  | nil => exact (hs rfl).elim
  | cons a as ih =>
      cases as with
      | nil => simp [triangularPathVertices, List.head!]
      | cons b bs =>
          have hc := List.isChain_cons_cons.mp hchain
          have ih' := ih (by simp) hc.2
          rw [List.dropLast_cons_of_ne_nil (by simp), List.map_cons,
            triangularPathVertices_cons, ih']
          simp only [List.map_cons, List.cons.injEq, List.head!,
            sub_self, true_and]
          constructor
          · rw [hc.1]
            abel
          · rw [List.map_map]
            apply List.map_congr_left
            intro x hx
            simp only [Function.comp_apply]
            rw [hc.1]
            abel

theorem triangularPeriodicArc_pathVertices {n : Nat} [NeZero n]
    (d : Fin n -> Fin 6) (N : Nat) (hN : 1 ≤ N)
    (imin imax : Fin n) :
    triangularPathVertices (triangularPeriodicArcDirections d N imin imax) =
      (ons_periodicArcStates N imin imax).map
        (fun z => triangularPeriodStateCoord d z -
          triangularPeriodStateCoord d (0, imin)) := by
  rw [triangularPeriodicArcDirections]
  have hs : ons_periodicArcStates N imin imax ≠ [] := by
    intro h
    have hh := ons_periodicArcStates_head? N hN imin imax
    rw [h] at hh
    simp at hh
  have h := triangularPathVertices_map_dropLast_of_chain
    (triangularPeriodStateCoord d) (fun z => d z.2)
    (ons_periodicArcStates N imin imax) hs
    (triangularPeriodicArcStates_isChain d N imin imax)
  rw [show (ons_periodicArcStates N imin imax).head! = (0, imin) by
    have hh := ons_periodicArcStates_head? N hN imin imax
    cases hs' : ons_periodicArcStates N imin imax with
    | nil => simp [hs'] at hh
    | cons a as => simpa [hs'] using hh] at h
  exact h

theorem triangularPeriodicArc_pathVertices_nodup {n : Nat} [NeZero n]
    (d : Fin n -> Fin 6) (N : Nat) (hN : 1 ≤ N)
    (imin imax : Fin n)
    (hinj : Function.Injective (triangularPeriodStateCoord d)) :
    (triangularPathVertices
      (triangularPeriodicArcDirections d N imin imax)).Nodup := by
  rw [triangularPeriodicArc_pathVertices d N hN imin imax]
  apply List.Nodup.map (by
    intro a b hab
    apply hinj
    apply sub_left_injective
    exact hab)
  exact ons_periodicArcStates_nodup N imin imax

theorem triangularPeriodicArc_displacement {n : Nat} [NeZero n]
    (d : Fin n -> Fin 6) (N : Nat) (hN : 1 ≤ N)
    (imin imax : Fin n) :
    triangularPathDisplacement
        (triangularPeriodicArcDirections d N imin imax) =
      triangularPeriodStateCoord d (N, imax) -
        triangularPeriodStateCoord d (0, imin) := by
  have hlast := triangularPathVertices_getLast
    (triangularPeriodicArcDirections d N imin imax)
  rw [triangularPeriodicArc_pathVertices d N hN imin imax,
    List.getLast?_map, ons_periodicArcStates_getLast? N hN] at hlast
  exact Option.some.inj hlast.symm

theorem triangularPeriodicArc_xmin {n : Nat} [NeZero n]
    (d : Fin n -> Fin 6) (N : Nat) (hN : 1 ≤ N)
    (imin imax : Fin n)
    (hmin : ∀ i, (triangularIntPos d imin).1 ≤ (triangularIntPos d i).1)
    (hD : 0 < (triangularPathDisplacement (List.ofFn d)).1) :
    ∀ z ∈ (triangularPathVertices
      (triangularPeriodicArcDirections d N imin imax)).dropLast,
      0 ≤ z.1 := by
  intro z hz
  have hz' : z ∈ triangularPathVertices
      (triangularPeriodicArcDirections d N imin imax) :=
    List.mem_of_mem_dropLast hz
  rw [triangularPeriodicArc_pathVertices d N hN imin imax,
    List.mem_map] at hz'
  obtain ⟨s, hs, rfl⟩ := hz'
  have hp := hmin s.2
  simp [triangularPeriodStateCoord, Prod.smul_mk]
  nlinarith [Nat.zero_le s.1]

theorem triangularPeriodicArc_xmax {n : Nat} [NeZero n]
    (d : Fin n -> Fin 6) (N : Nat) (hN : 1 ≤ N)
    (imin imax : Fin n)
    (hmax : ∀ i, (triangularIntPos d i).1 ≤ (triangularIntPos d imax).1)
    (hD : 0 < (triangularPathDisplacement (List.ofFn d)).1) :
    ∀ z ∈ (triangularPathVertices
      (triangularPeriodicArcDirections d N imin imax)).dropLast,
      z.1 ≤
        (triangularPeriodStateCoord d (N, imax) -
          triangularPeriodStateCoord d (0, imin)).1 := by
  intro z hz
  have hz' : z ∈ triangularPathVertices
      (triangularPeriodicArcDirections d N imin imax) :=
    List.mem_of_mem_dropLast hz
  rw [triangularPeriodicArc_pathVertices d N hN imin imax,
    List.mem_map] at hz'
  obtain ⟨s, hs, rfl⟩ := hz'
  have hp := hmax s.2
  have hr := ons_mem_periodicArcStates_fst_le N imin imax s hs
  simp [triangularPeriodStateCoord, Prod.smul_mk]
  nlinarith

theorem triangularExists_path_top (l : List (Fin 6)) (dy : Int) :
    ∃ top : Int, 0 < top ∧ dy < top ∧
      ∀ z ∈ (triangularPathVertices l).dropLast, z.2 < top := by
  let ys := ((triangularPathVertices l).dropLast.map
    (fun z => z.2.natAbs)).sum
  let top : Int := (dy.natAbs + ys + 1 : Nat)
  refine ⟨top, ?_, ?_, ?_⟩
  · simp [top]
    positivity
  · have hdy : dy ≤ (dy.natAbs : Int) := Int.le_natAbs
    simp only [top, Nat.cast_add, Nat.cast_one]
    have hys : (0 : Int) ≤ ys := by positivity
    omega
  · intro z hz
    have hmem : z.2.natAbs ∈
        (triangularPathVertices l).dropLast.map (fun w => w.2.natAbs) :=
      List.mem_map.mpr ⟨z, hz, rfl⟩
    have hleNat : z.2.natAbs ≤ ys := List.le_sum_of_mem hmem
    have hle : z.2 ≤ (z.2.natAbs : Int) := Int.le_natAbs
    have hcast : (z.2.natAbs : Int) ≤ ys := by exact_mod_cast hleNat
    simp only [top, Nat.cast_add, Nat.cast_one]
    have hdy0 : (0 : Int) ≤ dy.natAbs := by positivity
    omega

theorem triangularPeriodicArc_closure_phase_eq_neg_one
    {n : Nat} [NeZero n]
    (d : Fin n -> Fin 6) (N : Nat) (hN : 1 ≤ N)
    (imin imax : Fin n)
    (hinj : Function.Injective (triangularPeriodStateCoord d))
    (hmin : ∀ i, (triangularIntPos d imin).1 ≤ (triangularIntPos d i).1)
    (hmax : ∀ i, (triangularIntPos d i).1 ≤ (triangularIntPos d imax).1)
    (hD : 0 < (triangularPathDisplacement (List.ofFn d)).1) :
    let l := triangularPeriodicArcDirections d N imin imax
    let delta := triangularPeriodStateCoord d (N, imax) -
      triangularPeriodStateCoord d (0, imin)
    let top := Classical.choose (triangularExists_path_top l delta.2)
    kwVectorPhaseCycle
      ((l ++ triangularOutsideConnector delta.1 delta.2 top).map
        triangularIntVector) = -1 := by
  dsimp only
  let l := triangularPeriodicArcDirections d N imin imax
  let delta := triangularPeriodStateCoord d (N, imax) -
    triangularPeriodStateCoord d (0, imin)
  let top := Classical.choose (triangularExists_path_top l delta.2)
  have hspec := Classical.choose_spec (triangularExists_path_top l delta.2)
  have htop : 0 < top := hspec.1
  have hdy : delta.2 < top := hspec.2.1
  have hymax : ∀ z ∈ (triangularPathVertices l).dropLast, z.2 < top :=
    hspec.2.2
  have hdx : 0 < delta.1 := by
    have hp := hmin imax
    have hmul : 0 < (N : Int) *
        (triangularPathDisplacement (List.ofFn d)).1 := by positivity
    simp [delta, triangularPeriodStateCoord, Prod.smul_mk]
    nlinarith
  have hdisp : triangularPathDisplacement l = delta :=
    triangularPeriodicArc_displacement d N hN imin imax
  have hnodup : (triangularPathVertices l).Nodup :=
    triangularPeriodicArc_pathVertices_nodup d N hN imin imax hinj
  have hxmin := triangularPeriodicArc_xmin d N hN imin imax hmin hD
  have hxmax := triangularPeriodicArc_xmax d N hN imin imax hmax hD
  let c := triangularOutsideConnector delta.1 delta.2 top
  letI : NeZero (l ++ c).length := by
    refine ⟨?_⟩
    simp [c, triangularOutsideConnector, ons_outsideConnector]
  have hclosed : triangularPathDisplacement (l ++ c) = 0 := by
    rw [triangularPathDisplacement_append,
      triangularOutsideConnector_displacement delta.1 delta.2 top
        hdx hdy htop, hdisp]
    ext <;> simp
  have hsimple :
      (triangularPathVertices (l ++ c)).dropLast.Nodup :=
    triangularBoundingClosure_vertices_dropLast_nodup l delta.1 delta.2 top
      hdx hdy htop hdisp hnodup hxmin hxmax hymax
  have hlen : 3 ≤ (l ++ c).length := by
    have hv0 : top.toNat ≠ 0 := by
      intro h
      have := Int.toNat_eq_zero.mp h
      omega
    have hv : 1 ≤ top.toNat := Nat.one_le_iff_ne_zero.mpr hv0
    simp [c, triangularOutsideConnector, ons_outsideConnector]
    omega
  exact triangularSimpleList_phaseCycle_eq_neg_one
    (l ++ c) hclosed hsimple hlen

theorem kwVectorPhasePath_append
    (l r : List Complex) (hl : l ≠ []) (hr : r ≠ []) :
    kwVectorPhasePath (l ++ r) =
      kwVectorPhasePath l * kwVectorTurnPhase l.getLast! r.head! *
        kwVectorPhasePath r := by
  obtain ⟨x, xs, rfl⟩ := List.exists_cons_of_ne_nil hl
  obtain ⟨y, ys, rfl⟩ := List.exists_cons_of_ne_nil hr
  simpa [List.getLast!, List.head!] using
    kwVectorPhasePath_append_cons x xs y ys

theorem kwVectorPhaseCycle_eq_path_mul_turn
    (l : List Complex) (hl : l ≠ []) :
    kwVectorPhaseCycle l =
      kwVectorPhasePath l * kwVectorTurnPhase l.getLast! l.head! := by
  obtain ⟨x, xs, rfl⟩ := List.exists_cons_of_ne_nil hl
  rfl

theorem kwVectorPhaseCycle_append
    (l r : List Complex) (hl : l ≠ []) (hr : r ≠ []) :
    kwVectorPhaseCycle (l ++ r) =
      kwVectorPhasePath l * kwVectorTurnPhase l.getLast! r.head! *
        kwVectorPhasePath r * kwVectorTurnPhase r.getLast! l.head! := by
  obtain ⟨x, xs, rfl⟩ := List.exists_cons_of_ne_nil hl
  obtain ⟨y, ys, rfl⟩ := List.exists_cons_of_ne_nil hr
  simpa [List.getLast!, List.head!] using
    kwVectorPhaseCycle_append_cons x xs y ys

theorem map_head!_of_ne_nil
    {X Y : Type*} [Inhabited X] [Inhabited Y]
    (f : X -> Y) (l : List X) (hl : l ≠ []) :
    (l.map f).head! = f l.head! := by
  obtain ⟨x, xs, rfl⟩ := List.exists_cons_of_ne_nil hl
  rfl

theorem map_getLast!_of_ne_nil
    {X Y : Type*} [Inhabited X] [Inhabited Y]
    (f : X -> Y) (l : List X) (hl : l ≠ []) :
    (l.map f).getLast! = f l.getLast! := by
  have hmap : l.map f ≠ [] := by simpa using hl
  rw [ons_getLast!_eq_getLast (l.map f) hmap,
    ons_getLast!_eq_getLast l hl]
  exact List.getLast_map hmap

theorem kwVectorPhasePath_replicate_succ (n : Nat) (x : Complex) :
    kwVectorPhasePath (List.replicate (n + 1) x) = 1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [show List.replicate (n + 1 + 1) x =
          x :: x :: List.replicate n x by
        rw [List.replicate_succ, List.replicate_succ]]
      rw [kwVectorPhasePath_cons_cons]
      rw [show x :: List.replicate n x =
          List.replicate (n + 1) x by rw [List.replicate_succ], ih]
      simp [kwVectorTurnPhase, kwAngleTurnPhase]

theorem getLast!_replicate_succ
    {X : Type*} [Inhabited X] (n : Nat) (x : X) :
    (List.replicate (n + 1) x).getLast! = x := by
  have h : List.replicate (n + 1) x ≠ [] := by simp
  rw [ons_getLast!_eq_getLast _ h]
  exact List.getLast_replicate h

theorem kwVectorPhasePath_five_blocks
    (a b c d e : Complex) (na nb nc nd ne : Nat) :
    kwVectorPhasePath
        (List.replicate (na + 1) a ++
          List.replicate (nb + 1) b ++
          List.replicate (nc + 1) c ++
          List.replicate (nd + 1) d ++
          List.replicate (ne + 1) e) =
      kwVectorTurnPhase a b * kwVectorTurnPhase b c *
        kwVectorTurnPhase c d * kwVectorTurnPhase d e := by
  let A := List.replicate (na + 1) a
  let B := List.replicate (nb + 1) b
  let C := List.replicate (nc + 1) c
  let D := List.replicate (nd + 1) d
  let E := List.replicate (ne + 1) e
  have hA : A ≠ [] := by simp [A]
  have hB : B ≠ [] := by simp [B]
  have hC : C ≠ [] := by simp [C]
  have hD : D ≠ [] := by simp [D]
  have hE : E ≠ [] := by simp [E]
  change kwVectorPhasePath (A ++ B ++ C ++ D ++ E) = _
  simp only [List.append_assoc]
  rw [kwVectorPhasePath_append A (B ++ (C ++ (D ++ E))) hA
      (by simp [hB]),
    kwVectorPhasePath_append B (C ++ (D ++ E)) hB (by simp [hC]),
    kwVectorPhasePath_append C (D ++ E) hC (by simp [hD]),
    kwVectorPhasePath_append D E hD hE]
  have hAlast : A.getLast! = a := by
    exact getLast!_replicate_succ na a
  have hBlast : B.getLast! = b := by
    exact getLast!_replicate_succ nb b
  have hClast : C.getLast! = c := by
    exact getLast!_replicate_succ nc c
  have hDlast : D.getLast! = d := by
    exact getLast!_replicate_succ nd d
  have hBhead : (B ++ (C ++ (D ++ E))).head! = b := by
    simp [B, List.replicate_succ]
  have hChead : (C ++ (D ++ E)).head! = c := by
    simp [C, List.replicate_succ]
  have hDhead : (D ++ E).head! = d := by
    simp [D, List.replicate_succ]
  have hEhead : E.head! = e := by
    simp [E, List.replicate_succ]
  rw [hAlast, hBlast, hClast, hDlast,
    hBhead, hChead, hDhead, hEhead]
  simp [A, B, C, D, E, kwVectorPhasePath_replicate_succ]
  ring

theorem triangularOutsideConnector_phasePath
    (dx dy top : Int) (hdx : 0 < dx) (hdy : dy < top)
    (htop : 0 < top) :
    kwVectorPhasePath
        ((triangularOutsideConnector dx dy top).map triangularIntVector) =
      kwVectorTurnPhase (triangularIntVector 1) (triangularIntVector 3) *
        kwVectorTurnPhase (triangularIntVector 3) (triangularIntVector 0) *
        kwVectorTurnPhase (triangularIntVector 0) (triangularIntVector 2) *
        kwVectorTurnPhase (triangularIntVector 2) (triangularIntVector 1) := by
  have hu : 0 < (top - dy).toNat := by
    apply Nat.pos_of_ne_zero
    intro hzero
    have := Int.toNat_eq_zero.mp hzero
    omega
  have hw : 0 < (dx + 2).toNat := by
    apply Nat.pos_of_ne_zero
    intro hzero
    have := Int.toNat_eq_zero.mp hzero
    omega
  have hv : 0 < top.toNat := by
    apply Nat.pos_of_ne_zero
    intro hzero
    have := Int.toNat_eq_zero.mp hzero
    omega
  obtain ⟨u, hu'⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hu)
  obtain ⟨w, hw'⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hw)
  obtain ⟨v, hv'⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hv)
  rw [show (triangularOutsideConnector dx dy top).map triangularIntVector =
      List.replicate (0 + 1) (triangularIntVector 1) ++
        List.replicate (u + 1) (triangularIntVector 3) ++
        List.replicate (w + 1) (triangularIntVector 0) ++
        List.replicate (v + 1) (triangularIntVector 2) ++
        List.replicate (0 + 1) (triangularIntVector 1) by
      simp [triangularOutsideConnector, ons_outsideConnector,
        triangularAxisDirection, hu', hw', hv', List.map_replicate]]
  exact kwVectorPhasePath_five_blocks _ _ _ _ _ 0 u w v 0

@[simp] theorem triangularOutsideConnector_head
    (dx dy top : Int) :
    (triangularOutsideConnector dx dy top).head! = 1 := by
  simp [triangularOutsideConnector, ons_outsideConnector,
    triangularAxisDirection]

@[simp] theorem triangularOutsideConnector_getLast
    (dx dy top : Int) :
    (triangularOutsideConnector dx dy top).getLast! = 1 := by
  simp [triangularOutsideConnector, ons_outsideConnector,
    triangularAxisDirection, List.getLast!]

theorem triangularOfFn_ne_nil {n : Nat} [NeZero n]
    (d : Fin n -> Fin 6) : List.ofFn d ≠ [] := by
  intro h
  have := congrArg List.length h
  simp at this
  exact NeZero.ne n this

theorem triangularDrop_ofFn_ne_nil {n : Nat} [NeZero n]
    (d : Fin n -> Fin 6) (i : Fin n) :
    (List.ofFn d).drop i.val ≠ [] := by
  intro h
  have := congrArg List.length h
  rw [List.length_drop, List.length_ofFn] at this
  simp at this
  omega

def triangularDirectionPeriods {n : Nat}
    (d : Fin n -> Fin 6) (N : Nat) : List (Fin 6) :=
  (List.range N).flatMap (fun _ => List.ofFn d)

@[simp] theorem triangularDirectionPeriods_length {n : Nat}
    (d : Fin n -> Fin 6) (N : Nat) :
    (triangularDirectionPeriods d N).length = N * n := by
  simp [triangularDirectionPeriods, List.length_flatMap]

theorem triangularAllPeriodStates_map_direction {n : Nat}
    (d : Fin n -> Fin 6) (N : Nat) :
    (ons_allPeriodStates n N).map (fun z => d z.2) =
      triangularDirectionPeriods d (N + 1) := by
  simp [ons_allPeriodStates, ons_periodStateList,
    triangularDirectionPeriods, List.map_flatMap, List.map_ofFn]
  apply List.flatMap_congr
  intro r hr
  congr 1

theorem triangularPeriodicArcDirections_eq_slice
    {n : Nat} [NeZero n]
    (d : Fin n -> Fin 6) (N : Nat) (hN : 1 ≤ N)
    (imin imax : Fin n) :
    triangularPeriodicArcDirections d N imin imax =
      ((triangularDirectionPeriods d (N + 1)).drop imin.val).take
        (N * n + imax.val - imin.val) := by
  let count := N * n + imax.val + 1 - imin.val
  have hn : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  have hmul : n ≤ N * n := Nat.le_mul_of_pos_left n (by omega)
  have hcount : 0 < count := by dsimp [count]; omega
  have hle : count ≤
      ((triangularDirectionPeriods d (N + 1)).drop imin.val).length := by
    rw [List.length_drop]
    simp [triangularDirectionPeriods, List.length_flatMap]
    rw [Nat.add_mul]
    dsimp [count]
    omega
  rw [triangularPeriodicArcDirections, ons_periodicArcStates,
    List.map_dropLast, List.map_take, List.map_drop,
    triangularAllPeriodStates_map_direction,
    ons_dropLast_take_of_pos_le _ count hcount hle]
  congr 1
  dsimp [count]
  omega

theorem triangularDirectionPeriods_succ {n : Nat}
    (d : Fin n -> Fin 6) (N : Nat) :
    triangularDirectionPeriods d (N + 1) =
      triangularDirectionPeriods d N ++ List.ofFn d := by
  simp [triangularDirectionPeriods, List.range_succ, List.flatMap_append]

theorem triangularDirectionPeriods_append_comm {n : Nat}
    (d : Fin n -> Fin 6) (N : Nat) :
    triangularDirectionPeriods d N ++ List.ofFn d =
      List.ofFn d ++ triangularDirectionPeriods d N := by
  induction N with
  | zero => simp [triangularDirectionPeriods]
  | succ N ih =>
      rw [show N + 1 = N + 1 by rfl, triangularDirectionPeriods_succ]
      rw [<- List.append_assoc, ih, List.append_assoc]

theorem triangularDirectionPeriods_succ_left {n : Nat}
    (d : Fin n -> Fin 6) (N : Nat) :
    triangularDirectionPeriods d (N + 1) =
      List.ofFn d ++ triangularDirectionPeriods d N := by
  rw [triangularDirectionPeriods_succ,
    triangularDirectionPeriods_append_comm]

theorem triangularPeriodicArcDirections_eq_blocks
    {n : Nat} [NeZero n]
    (d : Fin n -> Fin 6) (N : Nat) (hN : 1 ≤ N)
    (imin imax : Fin n) :
    triangularPeriodicArcDirections d N imin imax =
      (List.ofFn d).drop imin.val ++
        triangularDirectionPeriods d (N - 1) ++
        (List.ofFn d).take imax.val := by
  rw [triangularPeriodicArcDirections_eq_slice d N hN,
    triangularDirectionPeriods_succ_left]
  rw [List.drop_append, List.take_append]
  simp only [List.length_ofFn]
  have hdrop : imin.val - n = 0 := by omega
  rw [hdrop, List.drop_zero]
  have hfirst :
      ((List.ofFn d).drop imin.val).take
          (N * n + imax.val - imin.val) =
        (List.ofFn d).drop imin.val := by
    apply (List.take_eq_self_iff _).mpr
    rw [List.length_drop, List.length_ofFn]
    have hmul : n ≤ N * n := Nat.le_mul_of_pos_left n (by omega)
    omega
  rw [hfirst, List.length_drop, List.length_ofFn]
  have hNsplit : N = (N - 1) + 1 := by omega
  have hmulEq : N * n = (N - 1) * n + n := by
    rw [hNsplit, Nat.add_mul]
    simp
  have hrem : N * n + imax.val - imin.val - (n - imin.val) =
      (N - 1) * n + imax.val := by rw [hmulEq]; omega
  rw [hrem]
  conv_lhs =>
    rhs
    rw [hNsplit, triangularDirectionPeriods_succ]
  rw [List.take_append]
  simp only [triangularDirectionPeriods_length]
  have htakePeriods :
      (triangularDirectionPeriods d (N - 1)).take
          ((N - 1) * n + imax.val) =
        triangularDirectionPeriods d (N - 1) := by
    apply (List.take_eq_self_iff _).mpr
    simp
  have hnorm : N - 1 + 1 - 1 = N - 1 := by omega
  rw [hnorm, htakePeriods, Nat.add_sub_cancel_left]
  exact (List.append_assoc _ _ _).symm

theorem triangularDrop_ofFn_getLast! {n : Nat} [NeZero n]
    (d : Fin n -> Fin 6) (i : Fin n) :
    ((List.ofFn d).drop i.val).getLast! = (List.ofFn d).getLast! := by
  have hdrop := triangularDrop_ofFn_ne_nil d i
  have hsplit := List.take_append_drop i.val (List.ofFn d)
  calc
    ((List.ofFn d).drop i.val).getLast! =
        ((List.ofFn d).take i.val ++
          (List.ofFn d).drop i.val).getLast! :=
      (ons_getLast!_append_of_right_ne_nil
        ((List.ofFn d).take i.val) ((List.ofFn d).drop i.val) hdrop).symm
    _ = (List.ofFn d).getLast! := congrArg List.getLast! hsplit

theorem triangularDirectionPeriods_getLast! {n : Nat} [NeZero n]
    (d : Fin n -> Fin 6) (N : Nat) (hN : 1 ≤ N) :
    (triangularDirectionPeriods d N).getLast! =
      (List.ofFn d).getLast! := by
  have hsplit : N = (N - 1) + 1 := by omega
  rw [hsplit, triangularDirectionPeriods_succ]
  exact ons_getLast!_append_of_right_ne_nil
    (triangularDirectionPeriods d (N - 1)) (List.ofFn d)
    (triangularOfFn_ne_nil d)

theorem triangularArcInitialBlock_getLast! {n : Nat} [NeZero n]
    (d : Fin n -> Fin 6) (N : Nat) (hN : 1 ≤ N) (imin : Fin n) :
    ((List.ofFn d).drop imin.val ++
      triangularDirectionPeriods d (N - 1)).getLast! =
        (List.ofFn d).getLast! := by
  by_cases hzero : N - 1 = 0
  · rw [hzero]
    change (((List.ofFn d).drop imin.val) ++ []).getLast! = _
    rw [List.append_nil]
    exact triangularDrop_ofFn_getLast! d imin
  · have hpos : 1 ≤ N - 1 := Nat.one_le_iff_ne_zero.mpr hzero
    have hperiods : triangularDirectionPeriods d (N - 1) ≠ [] := by
      intro h
      have hlen := congrArg List.length h
      rw [triangularDirectionPeriods_length] at hlen
      simp at hlen
      rcases hlen with hleft | hright
      · exact hzero hleft
      · exact NeZero.ne n hright
    rw [ons_getLast!_append_of_right_ne_nil
      ((List.ofFn d).drop imin.val)
      (triangularDirectionPeriods d (N - 1)) hperiods]
    exact triangularDirectionPeriods_getLast! d (N - 1) hpos

theorem triangularTake_ofFn_head! {n : Nat} [NeZero n]
    (d : Fin n -> Fin 6) (i : Fin n)
    (h : (List.ofFn d).take i.val ≠ []) :
    ((List.ofFn d).take i.val).head! = (List.ofFn d).head! := by
  have hfull := triangularOfFn_ne_nil d
  rw [ons_head!_eq_head ((List.ofFn d).take i.val) h,
    ons_head!_eq_head (List.ofFn d) hfull]
  exact List.head_take h

theorem kwVectorPhasePath_insert_cycle
    (A D P : List Complex) (hA : A ≠ []) (hD : D ≠ [])
    (hlast : A.getLast! = D.getLast!)
    (hhead : P ≠ [] -> P.head! = D.head!) :
    kwVectorPhasePath (A ++ D ++ P) =
      kwVectorPhasePath (A ++ P) * kwVectorPhaseCycle D := by
  have hAD : A ++ D ≠ [] := List.append_ne_nil_of_right_ne_nil A hD
  have hcycle := kwVectorPhaseCycle_eq_path_mul_turn D hD
  by_cases hP : P = []
  · subst P
    simp only [List.append_nil]
    rw [kwVectorPhasePath_append A D hA hD, hcycle, hlast]
    ring
  · rw [kwVectorPhasePath_append (A ++ D) P hAD hP,
      kwVectorPhasePath_append A D hA hD,
      kwVectorPhasePath_append A P hA hP,
      ons_getLast!_append_of_right_ne_nil A D hD,
      hhead hP, hcycle, hlast]
    ring

theorem triangularPeriodicArc_phasePath_succ
    {n : Nat} [NeZero n]
    (d : Fin n -> Fin 6) (N : Nat) (hN : 1 ≤ N)
    (imin imax : Fin n) :
    let old := triangularPeriodicArcDirections d N imin imax
    let new := triangularPeriodicArcDirections d (N + 1) imin imax
    kwVectorPhasePath (new.map triangularIntVector) =
      kwVectorPhasePath (old.map triangularIntVector) *
        kwVectorPhaseCycle ((List.ofFn d).map triangularIntVector) := by
  let S := (List.ofFn d).drop imin.val
  let M := triangularDirectionPeriods d (N - 1)
  let D := List.ofFn d
  let P := (List.ofFn d).take imax.val
  let A := S ++ M
  have hA : A ≠ [] := List.append_ne_nil_of_left_ne_nil
    (triangularDrop_ofFn_ne_nil d imin) M
  have hD : D ≠ [] := triangularOfFn_ne_nil d
  have hlast : A.getLast! = D.getLast! :=
    triangularArcInitialBlock_getLast! d N hN imin
  have hhead : P ≠ [] -> P.head! = D.head! := by
    intro hP
    exact triangularTake_ofFn_head! d imax hP
  have hinsert := kwVectorPhasePath_insert_cycle
    (A.map triangularIntVector) (D.map triangularIntVector)
      (P.map triangularIntVector) (by simpa using hA) (by simpa using hD)
      (by
        rw [map_getLast!_of_ne_nil triangularIntVector A hA,
          map_getLast!_of_ne_nil triangularIntVector D hD]
        exact congrArg triangularIntVector hlast) (by
        intro hPmap
        have hP : P ≠ [] := by simpa using hPmap
        rw [map_head!_of_ne_nil triangularIntVector P hP,
          map_head!_of_ne_nil triangularIntVector D hD]
        exact congrArg triangularIntVector (hhead hP))
  dsimp only
  rw [triangularPeriodicArcDirections_eq_blocks d N hN,
    triangularPeriodicArcDirections_eq_blocks d (N + 1) (by omega)]
  have hsplit : N = (N - 1) + 1 := by omega
  have hper : triangularDirectionPeriods d N =
      triangularDirectionPeriods d (N - 1) ++ List.ofFn d := by
    conv_lhs => rw [hsplit]
    exact triangularDirectionPeriods_succ d (N - 1)
  have hsuccsub : N + 1 - 1 = N := by omega
  rw [hsuccsub, hper, List.map_append, List.map_append, List.map_append]
  simpa only [S, M, D, P, A, List.map_append,
    List.append_assoc] using hinsert

theorem triangularPeriodicArc_head_succ
    {n : Nat} [NeZero n]
    (d : Fin n -> Fin 6) (N : Nat) (hN : 1 ≤ N)
    (imin imax : Fin n) :
    (triangularPeriodicArcDirections d (N + 1) imin imax).head! =
      (triangularPeriodicArcDirections d N imin imax).head! := by
  rw [triangularPeriodicArcDirections_eq_blocks d N hN,
    triangularPeriodicArcDirections_eq_blocks d (N + 1) (by omega)]
  simp [triangularDrop_ofFn_ne_nil d imin]

theorem triangularPeriodicArc_getLast_succ
    {n : Nat} [NeZero n]
    (d : Fin n -> Fin 6) (N : Nat) (hN : 1 ≤ N)
    (imin imax : Fin n) :
    (triangularPeriodicArcDirections d (N + 1) imin imax).getLast! =
      (triangularPeriodicArcDirections d N imin imax).getLast! := by
  rw [triangularPeriodicArcDirections_eq_blocks d N hN,
    triangularPeriodicArcDirections_eq_blocks d (N + 1) (by omega)]
  by_cases hP : (List.ofFn d).take imax.val = []
  · rw [hP, List.append_nil, List.append_nil]
    rw [triangularArcInitialBlock_getLast! d N hN imin,
      triangularArcInitialBlock_getLast! d (N + 1) (by omega) imin]
  · rw [ons_getLast!_append_of_right_ne_nil _ _ hP,
      ons_getLast!_append_of_right_ne_nil _ _ hP]

theorem triangularPeriodicArc_ne_nil
    {n : Nat} [NeZero n]
    (d : Fin n -> Fin 6) (N : Nat) (hN : 1 ≤ N)
    (imin imax : Fin n) :
    triangularPeriodicArcDirections d N imin imax ≠ [] := by
  rw [triangularPeriodicArcDirections_eq_blocks d N hN]
  exact List.append_ne_nil_of_left_ne_nil
    (List.append_ne_nil_of_left_ne_nil
      (triangularDrop_ofFn_ne_nil d imin) _) _

theorem triangularPeriodicClosure_phase_succ
    {n : Nat} [NeZero n]
    (d : Fin n -> Fin 6) (N : Nat) (hN : 1 ≤ N)
    (imin imax : Fin n)
    (dx dy top dx' dy' top' : Int)
    (hdx : 0 < dx) (hdy : dy < top) (htop : 0 < top)
    (hdx' : 0 < dx') (hdy' : dy' < top') (htop' : 0 < top') :
    let old := triangularPeriodicArcDirections d N imin imax
    let new := triangularPeriodicArcDirections d (N + 1) imin imax
    kwVectorPhaseCycle
        ((new ++ triangularOutsideConnector dx' dy' top').map
          triangularIntVector) =
      kwVectorPhaseCycle
          ((old ++ triangularOutsideConnector dx dy top).map
            triangularIntVector) *
        kwVectorPhaseCycle ((List.ofFn d).map triangularIntVector) := by
  dsimp only
  let old := triangularPeriodicArcDirections d N imin imax
  let new := triangularPeriodicArcDirections d (N + 1) imin imax
  let c := triangularOutsideConnector dx dy top
  let c' := triangularOutsideConnector dx' dy' top'
  have hold : old ≠ [] := triangularPeriodicArc_ne_nil d N hN imin imax
  have hnew : new ≠ [] := triangularPeriodicArc_ne_nil d (N + 1) (by omega)
    imin imax
  have hc : c ≠ [] := by simp [c, triangularOutsideConnector,
    ons_outsideConnector]
  have hc' : c' ≠ [] := by simp [c', triangularOutsideConnector,
    ons_outsideConnector]
  rw [List.map_append, List.map_append,
    kwVectorPhaseCycle_append _ _ (by simpa using hnew) (by simpa using hc'),
    kwVectorPhaseCycle_append _ _ (by simpa using hold) (by simpa using hc)]
  have hpath := triangularPeriodicArc_phasePath_succ d N hN imin imax
  have hhead := triangularPeriodicArc_head_succ d N hN imin imax
  have hlast := triangularPeriodicArc_getLast_succ d N hN imin imax
  have hcpath := triangularOutsideConnector_phasePath dx dy top hdx hdy htop
  have hcpath' := triangularOutsideConnector_phasePath
    dx' dy' top' hdx' hdy' htop'
  have hheadmap : (new.map triangularIntVector).head! =
      (old.map triangularIntVector).head! := by
    rw [map_head!_of_ne_nil triangularIntVector new hnew,
      map_head!_of_ne_nil triangularIntVector old hold, hhead]
  have hlastmap : (new.map triangularIntVector).getLast! =
      (old.map triangularIntVector).getLast! := by
    rw [map_getLast!_of_ne_nil triangularIntVector new hnew,
      map_getLast!_of_ne_nil triangularIntVector old hold, hlast]
  have hchead : (c.map triangularIntVector).head! = triangularIntVector 1 := by
    rw [map_head!_of_ne_nil triangularIntVector c hc,
      triangularOutsideConnector_head]
  have hchead' : (c'.map triangularIntVector).head! = triangularIntVector 1 := by
    rw [map_head!_of_ne_nil triangularIntVector c' hc',
      triangularOutsideConnector_head]
  have hclast : (c.map triangularIntVector).getLast! = triangularIntVector 1 := by
    rw [map_getLast!_of_ne_nil triangularIntVector c hc,
      triangularOutsideConnector_getLast]
  have hclast' : (c'.map triangularIntVector).getLast! = triangularIntVector 1 := by
    rw [map_getLast!_of_ne_nil triangularIntVector c' hc',
      triangularOutsideConnector_getLast]
  rw [hpath, hcpath, hcpath', hheadmap, hlastmap,
    hchead, hchead', hclast, hclast']
  ring



theorem triangularPeriodicSimple_phaseCycle_eq_one_of_pos_x
    {n : Nat} [NeZero n] (d : Fin n -> Fin 6)
    (hinj : Function.Injective (triangularPeriodStateCoord d))
    (hD : 0 < (triangularPathDisplacement (List.ofFn d)).1) :
    kwVectorPhaseCycle ((List.ofFn d).map triangularIntVector) = 1 := by
  obtain ⟨imin, -, hmin⟩ := Finset.exists_min_image Finset.univ
    (fun i : Fin n => (triangularIntPos d i).1) Finset.univ_nonempty
  obtain ⟨imax, -, hmax⟩ := Finset.exists_max_image Finset.univ
    (fun i : Fin n => (triangularIntPos d i).1) Finset.univ_nonempty
  have hmin' : ∀ i, (triangularIntPos d imin).1 ≤
      (triangularIntPos d i).1 := fun i => hmin i (Finset.mem_univ i)
  have hmax' : ∀ i, (triangularIntPos d i).1 ≤
      (triangularIntPos d imax).1 := fun i => hmax i (Finset.mem_univ i)
  let l1 := triangularPeriodicArcDirections d 1 imin imax
  let l2 := triangularPeriodicArcDirections d 2 imin imax
  let delta1 := triangularPeriodStateCoord d (1, imax) -
    triangularPeriodStateCoord d (0, imin)
  let delta2 := triangularPeriodStateCoord d (2, imax) -
    triangularPeriodStateCoord d (0, imin)
  let top1 := Classical.choose (triangularExists_path_top l1 delta1.2)
  let top2 := Classical.choose (triangularExists_path_top l2 delta2.2)
  have hs1 := Classical.choose_spec (triangularExists_path_top l1 delta1.2)
  have hs2 := Classical.choose_spec (triangularExists_path_top l2 delta2.2)
  have hdx1 : 0 < delta1.1 := by
    have hp := hmin' imax
    simp [delta1, triangularPeriodStateCoord, Prod.smul_mk]
    nlinarith
  have hdx2 : 0 < delta2.1 := by
    have hp := hmin' imax
    simp [delta2, triangularPeriodStateCoord, Prod.smul_mk]
    nlinarith
  have hphase1 := triangularPeriodicArc_closure_phase_eq_neg_one
    d 1 (by omega) imin imax hinj hmin' hmax' hD
  have hphase2 := triangularPeriodicArc_closure_phase_eq_neg_one
    d 2 (by omega) imin imax hinj hmin' hmax' hD
  have hsucc := triangularPeriodicClosure_phase_succ
    d 1 (by omega) imin imax
    delta1.1 delta1.2 top1 delta2.1 delta2.2 top2
    hdx1 hs1.2.1 hs1.1 hdx2 hs2.2.1 hs2.1
  dsimp only [l1, l2, delta1, delta2, top1, top2] at hphase1 hphase2 hsucc
  rw [hphase1, hphase2] at hsucc
  norm_num at hsucc ⊢
  exact hsucc.symm

def triangularSwapDirection : Fin 6 -> Fin 6 := ![2, 3, 0, 1, 4, 5]

def triangularSwapPoint (p : Int × Int) : Int × Int := (p.2, p.1)

@[simp] theorem triangularIntStep_opposite (a : Fin 6) :
    triangularIntStep (triangularTorusDirectionReverse a) =
      -triangularIntStep a := by
  fin_cases a <;> rfl

@[simp] theorem triangularIntStep_swap (a : Fin 6) :
    triangularIntStep (triangularSwapDirection a) =
      triangularSwapPoint (triangularIntStep a) := by
  fin_cases a <;> rfl

theorem triangularIntPos_opposite
    {n : Nat} [NeZero n] (d : Fin n -> Fin 6) (i : Fin n) :
    triangularIntPos (fun k => triangularTorusDirectionReverse (d k)) i =
      -triangularIntPos d i := by
  unfold triangularIntPos
  simp only [triangularIntStep_opposite]
  exact Finset.sum_neg_distrib
    (s := Finset.univ.filter (fun k : Fin n => k < i))
    (fun k => triangularIntStep (d k))

theorem triangularIntPos_swap
    {n : Nat} [NeZero n] (d : Fin n -> Fin 6) (i : Fin n) :
    triangularIntPos (fun k => triangularSwapDirection (d k)) i =
      triangularSwapPoint (triangularIntPos d i) := by
  unfold triangularIntPos
  simp_rw [triangularIntStep_swap]
  apply Prod.ext
  · simp only [triangularSwapPoint, Prod.fst_sum, Prod.snd_sum]
  · simp only [triangularSwapPoint, Prod.fst_sum, Prod.snd_sum]

theorem triangularPathDisplacement_ofFn_opposite
    {n : Nat} (d : Fin n -> Fin 6) :
    triangularPathDisplacement
        (List.ofFn (fun k => triangularTorusDirectionReverse (d k))) =
      -triangularPathDisplacement (List.ofFn d) := by
  rw [triangularPathDisplacement_ofFn,
    triangularPathDisplacement_ofFn]
  simp only [triangularIntStep_opposite]
  exact Finset.sum_neg_distrib (s := Finset.univ)
    (fun k => triangularIntStep (d k))

theorem triangularPathDisplacement_ofFn_swap
    {n : Nat} (d : Fin n -> Fin 6) :
    triangularPathDisplacement
        (List.ofFn (fun k => triangularSwapDirection (d k))) =
      triangularSwapPoint
        (triangularPathDisplacement (List.ofFn d)) := by
  rw [triangularPathDisplacement_ofFn,
    triangularPathDisplacement_ofFn]
  simp_rw [triangularIntStep_swap]
  apply Prod.ext
  · simp only [triangularSwapPoint, Prod.fst_sum, Prod.snd_sum]
  · simp only [triangularSwapPoint, Prod.fst_sum, Prod.snd_sum]

theorem triangularPeriodStateCoord_opposite
    {n : Nat} [NeZero n] (d : Fin n -> Fin 6) (z : Nat × Fin n) :
    triangularPeriodStateCoord
        (fun k => triangularTorusDirectionReverse (d k)) z =
      -triangularPeriodStateCoord d z := by
  rw [triangularPeriodStateCoord, triangularPeriodStateCoord,
    triangularIntPos_opposite,
    triangularPathDisplacement_ofFn_opposite]
  apply Prod.ext <;> simp [Prod.smul_mk] <;> ring

theorem triangularPeriodStateCoord_swap
    {n : Nat} [NeZero n] (d : Fin n -> Fin 6) (z : Nat × Fin n) :
    triangularPeriodStateCoord
        (fun k => triangularSwapDirection (d k)) z =
      triangularSwapPoint (triangularPeriodStateCoord d z) := by
  rw [triangularPeriodStateCoord, triangularPeriodStateCoord,
    triangularIntPos_swap, triangularPathDisplacement_ofFn_swap]
  apply Prod.ext <;> simp [triangularSwapPoint, Prod.smul_mk]

theorem triangularPeriodStateCoord_opposite_injective
    {n : Nat} [NeZero n] (d : Fin n -> Fin 6)
    (hinj : Function.Injective (triangularPeriodStateCoord d)) :
    Function.Injective (triangularPeriodStateCoord
      (fun k => triangularTorusDirectionReverse (d k))) := by
  intro x y hxy
  apply hinj
  have h := congrArg Neg.neg hxy
  simpa [triangularPeriodStateCoord_opposite] using h

theorem triangularPeriodStateCoord_swap_injective
    {n : Nat} [NeZero n] (d : Fin n -> Fin 6)
    (hinj : Function.Injective (triangularPeriodStateCoord d)) :
    Function.Injective (triangularPeriodStateCoord
      (fun k => triangularSwapDirection (d k))) := by
  intro x y hxy
  apply hinj
  have h := congrArg triangularSwapPoint hxy
  simpa [triangularPeriodStateCoord_swap, triangularSwapPoint] using h

theorem kwVectorTurnPhase_triangular_eq_exp_turnExponent
    (a b : Fin 6) (hne : b ≠ triangularTorusDirectionReverse a) :
    kwVectorTurnPhase (triangularIntVector a) (triangularIntVector b) =
      Complex.exp
        ((((triangularTorusTurnExponent a b : Int) : Real) *
          (Real.pi / 4) : Complex) * Complex.I / 2) := by
  unfold kwVectorTurnPhase kwAngleTurnPhase
  rw [triangularIntVector_arg, triangularIntVector_arg,
    triangularTorusDirectionAngle_turn a b hne]
  congr 1
  push_cast
  ring

theorem triangularTurnExponent_opposite
    (a b : Fin 6) (hne : b ≠ triangularTorusDirectionReverse a) :
    triangularTorusTurnExponent
        (triangularTorusDirectionReverse a)
        (triangularTorusDirectionReverse b) =
      triangularTorusTurnExponent a b := by
  fin_cases a <;> fin_cases b <;>
    simp [triangularTorusDirectionReverse,
      triangularTorusTurnExponent] at hne ⊢

theorem triangularTurnExponent_swap
    (a b : Fin 6) (hne : b ≠ triangularTorusDirectionReverse a) :
    triangularTorusTurnExponent
        (triangularSwapDirection a) (triangularSwapDirection b) =
      -triangularTorusTurnExponent a b := by
  fin_cases a <;> fin_cases b <;>
    simp [triangularSwapDirection, triangularTorusDirectionReverse,
      triangularTorusTurnExponent] at hne ⊢

theorem triangularSwapDirection_reverse (a : Fin 6) :
    triangularSwapDirection (triangularTorusDirectionReverse a) =
      triangularTorusDirectionReverse (triangularSwapDirection a) := by
  fin_cases a <;> rfl

theorem triangularSwapDirection_injective :
    Function.Injective triangularSwapDirection := by
  intro a b h
  fin_cases a <;> fin_cases b <;>
    simp [triangularSwapDirection] at h ⊢

theorem triangularOppositeDirection_reverse (a : Fin 6) :
    triangularTorusDirectionReverse
        (triangularTorusDirectionReverse a) = a := by
  fin_cases a <;> rfl

theorem triangularDirection_nonbacktracking_opposite
    {n : Nat} [NeZero n] (d : Fin n -> Fin 6)
    (hnb : ∀ k, d (k + 1) ≠ triangularTorusDirectionReverse (d k)) :
    ∀ k,
      triangularTorusDirectionReverse (d (k + 1)) ≠
        triangularTorusDirectionReverse
          (triangularTorusDirectionReverse (d k)) := by
  intro k h
  rw [triangularOppositeDirection_reverse] at h
  exact hnb k (triangularOppositeDirection_reverse (d (k + 1)) ▸
    congrArg triangularTorusDirectionReverse h)

theorem triangularDirection_nonbacktracking_swap
    {n : Nat} [NeZero n] (d : Fin n -> Fin 6)
    (hnb : ∀ k, d (k + 1) ≠ triangularTorusDirectionReverse (d k)) :
    ∀ k,
      triangularSwapDirection (d (k + 1)) ≠
        triangularTorusDirectionReverse
          (triangularSwapDirection (d k)) := by
  intro k h
  rw [<- triangularSwapDirection_reverse] at h
  exact hnb k (triangularSwapDirection_injective h)

theorem triangularPhaseCycle_opposite
    {n : Nat} [NeZero n] (d : Fin n -> Fin 6)
    (hnb : ∀ k, d (k + 1) ≠ triangularTorusDirectionReverse (d k)) :
    kwVectorPhaseCycle
        ((List.ofFn (fun k => triangularTorusDirectionReverse (d k))).map
          triangularIntVector) =
      kwVectorPhaseCycle ((List.ofFn d).map triangularIntVector) := by
  rw [show (List.ofFn
      (fun k => triangularTorusDirectionReverse (d k))).map
        triangularIntVector =
      List.ofFn (fun k => triangularIntVector
        (triangularTorusDirectionReverse (d k))) by
          rw [List.map_ofFn]
          congr 1,
    show (List.ofFn d).map triangularIntVector =
      List.ofFn (fun k => triangularIntVector (d k)) by
        rw [List.map_ofFn]
        congr 1,
    kwVectorPhaseCycle_ofFn, kwVectorPhaseCycle_ofFn]
  unfold kwLoopPhaseProduct
  apply Finset.prod_congr rfl
  intro k hk
  have hnb' := triangularDirection_nonbacktracking_opposite d hnb k
  rw [kwVectorTurnPhase_triangular_eq_exp_turnExponent _ _ hnb',
    kwVectorTurnPhase_triangular_eq_exp_turnExponent _ _ (hnb k),
    triangularTurnExponent_opposite _ _ (hnb k)]

theorem triangularPhaseCycle_swap
    {n : Nat} [NeZero n] (d : Fin n -> Fin 6)
    (hnb : ∀ k, d (k + 1) ≠ triangularTorusDirectionReverse (d k)) :
    kwVectorPhaseCycle
        ((List.ofFn (fun k => triangularSwapDirection (d k))).map
          triangularIntVector) =
      (kwVectorPhaseCycle ((List.ofFn d).map triangularIntVector))⁻¹ := by
  rw [show (List.ofFn (fun k => triangularSwapDirection (d k))).map
        triangularIntVector =
      List.ofFn (fun k => triangularIntVector
        (triangularSwapDirection (d k))) by
          rw [List.map_ofFn]
          congr 1,
    show (List.ofFn d).map triangularIntVector =
      List.ofFn (fun k => triangularIntVector (d k)) by
        rw [List.map_ofFn]
        congr 1,
    kwVectorPhaseCycle_ofFn, kwVectorPhaseCycle_ofFn]
  unfold kwLoopPhaseProduct
  rw [<- Finset.prod_inv_distrib]
  apply Finset.prod_congr rfl
  intro k hk
  have hnb' := triangularDirection_nonbacktracking_swap d hnb k
  rw [kwVectorTurnPhase_triangular_eq_exp_turnExponent _ _ hnb',
    kwVectorTurnPhase_triangular_eq_exp_turnExponent _ _ (hnb k),
    triangularTurnExponent_swap _ _ (hnb k)]
  rw [<- Complex.exp_neg]
  congr 1
  push_cast
  ring



theorem triangularPeriodicSimple_phaseCycle_eq_one_of_nonzero
    {n : Nat} [NeZero n] (d : Fin n -> Fin 6)
    (hinj : Function.Injective (triangularPeriodStateCoord d))
    (hnb : ∀ k, d (k + 1) ≠ triangularTorusDirectionReverse (d k))
    (hne : (triangularPathDisplacement (List.ofFn d)).1 ≠ 0 ∨
      (triangularPathDisplacement (List.ofFn d)).2 ≠ 0) :
    kwVectorPhaseCycle ((List.ofFn d).map triangularIntVector) = 1 := by
  let D := triangularPathDisplacement (List.ofFn d)
  change D.1 ≠ 0 ∨ D.2 ≠ 0 at hne
  by_cases hxpos : 0 < D.1
  · exact triangularPeriodicSimple_phaseCycle_eq_one_of_pos_x d hinj hxpos
  by_cases hxneg : D.1 < 0
  · let dr : Fin n -> Fin 6 := fun k => triangularTorusDirectionReverse (d k)
    have hDr : 0 < (triangularPathDisplacement (List.ofFn dr)).1 := by
      rw [triangularPathDisplacement_ofFn_opposite]
      simpa [D] using neg_pos.mpr hxneg
    have hr := triangularPeriodicSimple_phaseCycle_eq_one_of_pos_x dr
      (triangularPeriodStateCoord_opposite_injective d hinj) hDr
    rw [triangularPhaseCycle_opposite d hnb] at hr
    exact hr
  have hxzero : D.1 = 0 := by omega
  have hyne : D.2 ≠ 0 := hne.resolve_left (not_ne_iff.mpr hxzero)
  let ds : Fin n -> Fin 6 := fun k => triangularSwapDirection (d k)
  have hinjs := triangularPeriodStateCoord_swap_injective d hinj
  by_cases hypos : 0 < D.2
  · have hDs : 0 < (triangularPathDisplacement (List.ofFn ds)).1 := by
      rw [triangularPathDisplacement_ofFn_swap]
      exact hypos
    have hs := triangularPeriodicSimple_phaseCycle_eq_one_of_pos_x ds hinjs hDs
    rw [triangularPhaseCycle_swap d hnb] at hs
    simpa using congrArg Inv.inv hs
  · have hyneg : D.2 < 0 := lt_of_le_of_ne (le_of_not_gt hypos) hyne
    let drs : Fin n -> Fin 6 :=
      fun k => triangularTorusDirectionReverse (ds k)
    have hDrs : 0 < (triangularPathDisplacement (List.ofFn drs)).1 := by
      rw [triangularPathDisplacement_ofFn_opposite,
        triangularPathDisplacement_ofFn_swap]
      simpa using neg_pos.mpr hyneg
    have hrs := triangularPeriodicSimple_phaseCycle_eq_one_of_pos_x drs
      (triangularPeriodStateCoord_opposite_injective ds hinjs) hDrs
    rw [triangularPhaseCycle_opposite ds
      (triangularDirection_nonbacktracking_swap d hnb),
      triangularPhaseCycle_swap d hnb] at hrs
    simpa using congrArg Inv.inv hrs

theorem exists_triangularTurnExponent_sum_eq_eight_mul_even_of_phase_one
    {n : Nat} [NeZero n] (direction : Fin n -> Fin 6)
    (hnonbacktracking : ∀ k,
      direction (k + 1) ≠ triangularTorusDirectionReverse (direction k))
    (hphase : kwVectorPhaseCycle
      ((List.ofFn direction).map triangularIntVector) = 1) :
    ∃ m : Int,
      (∑ k, triangularTorusTurnExponent
        (direction k) (direction (k + 1))) = 8 * (2 * m) := by
  have hphaseLoop : kwLoopPhaseProduct
      (fun a b => kwAngleTurnPhase
        (triangularTorusDirectionAngle a)
        (triangularTorusDirectionAngle b)) direction = 1 := by
    have hvec : kwLoopPhaseProduct kwVectorTurnPhase
        (fun k => triangularIntVector (direction k)) = 1 := by
      rw [<- kwVectorPhaseCycle_ofFn]
      have hlist : List.ofFn (fun k => triangularIntVector (direction k)) =
          (List.ofFn direction).map triangularIntVector := by
        rw [List.map_ofFn]
        congr 1
      rw [hlist]
      exact hphase
    unfold kwLoopPhaseProduct at hvec ⊢
    simpa only [kwVectorTurnPhase_triangularIntVector] using hvec
  obtain ⟨winding, hturn⟩ :=
    kw_totalPrincipalTurn_eq_int_mul_two_pi
      triangularTorusDirectionAngle direction
  have hexpEq := kwLoopPhaseProduct_angleTurnPhase_eq_exp_sum
    triangularTorusDirectionAngle direction
  rw [hphaseLoop, hturn] at hexpEq
  have hexp : Complex.exp
      (((winding : Real) * Real.pi : Complex) * Complex.I) = 1 := by
    convert hexpEq.symm using 1 <;> push_cast <;> ring
  have hexp' : Complex.exp
      (((((winding : Real) * Real.pi) : Real) : Complex) * Complex.I) = 1 := by
    convert hexp using 1 <;> push_cast <;> ring
  rw [Complex.exp_ofReal_mul_I] at hexp'
  have hre := congrArg Complex.re hexp'
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero,
    zero_mul, sub_zero] at hre
  norm_num at hre
  rw [Real.cos_int_mul_pi] at hre
  obtain ⟨m, hm | hm⟩ := Int.even_or_odd' winding
  · have hsum :
        (∑ k, (triangularTorusDirectionAngle (direction (k + 1)) -
          triangularTorusDirectionAngle (direction k)).toReal : Real) =
        ((∑ k, triangularTorusTurnExponent
          (direction k) (direction (k + 1)) : Int) : Real) *
            (Real.pi / 4) := by
      rw [show (∑ k,
          (triangularTorusDirectionAngle (direction (k + 1)) -
            triangularTorusDirectionAngle (direction k)).toReal : Real) =
          ∑ k, (triangularTorusTurnExponent
            (direction k) (direction (k + 1)) : Real) *
              (Real.pi / 4) by
        apply Finset.sum_congr rfl
        intro k _
        exact triangularTorusDirectionAngle_turn _ _
          (hnonbacktracking k)]
      rw [<- Finset.sum_mul]
      norm_cast
    have hreal :
        (((∑ k, triangularTorusTurnExponent
          (direction k) (direction (k + 1)) : Int) : Real) *
            (Real.pi / 4)) =
          (winding : Real) * (2 * Real.pi) := hsum.symm.trans hturn
    have hcast :
        (((∑ k, triangularTorusTurnExponent
          (direction k) (direction (k + 1)) : Int) : Real)) =
          8 * (winding : Real) := by
      have hpi : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
      field_simp at hreal ⊢
      nlinarith
    have hint :
        (∑ k, triangularTorusTurnExponent
          (direction k) (direction (k + 1))) = 8 * winding := by
      exact_mod_cast hcast
    refine ⟨m, ?_⟩
    rw [hint, hm]
  · have hodd : Odd winding := ⟨m, by omega⟩
    have hneg : (-1 : Real) ^ winding = -1 := hodd.neg_one_zpow
    rw [hneg] at hre
    norm_num at hre

theorem triangularPeriodStateCoord_eq_intPeriodicPos
    {n : Nat} [NeZero n] (d : Fin n -> Fin 6)
    (z : Nat × Fin n) :
    triangularPeriodStateCoord d z =
      triangularIntPeriodicPos d ((z.1 : Int), z.2) := by
  rw [triangularPeriodStateCoord, triangularIntPeriodicPos,
    triangularPathDisplacement_ofFn]
  apply Prod.ext <;> simp [Prod.smul_mk] <;> ring

theorem triangularPeriodStateCoord_injective_of_intPeriodicPos
    {n : Nat} [NeZero n] (d : Fin n -> Fin 6)
    (hinj : Function.Injective (triangularIntPeriodicPos d)) :
    Function.Injective (triangularPeriodStateCoord d) := by
  intro z w hzw
  have hcoords :
      triangularIntPeriodicPos d ((z.1 : Int), z.2) =
        triangularIntPeriodicPos d ((w.1 : Int), w.2) :=
    (triangularPeriodStateCoord_eq_intPeriodicPos d z).symm.trans
      (hzw.trans (triangularPeriodStateCoord_eq_intPeriodicPos d w))
  have h := hinj hcoords
  have hfst : (z.1 : Int) = (w.1 : Int) := by
    simpa using congrArg Prod.fst h
  have hsnd : z.2 = w.2 := by
    simpa using congrArg Prod.snd h
  apply Prod.ext
  · exact_mod_cast hfst
  · exact hsnd



theorem triangularTorus_cyclePhaseProduct_eq_one_of_nonzeroHomology
    (L : Nat) [Fact (2 < L)]
    (rho : Complex) (hrho : rho ^ 4 = Complex.I)
    {root : ZMod L × ZMod L}
    (p : (triangularTorusGraph L).Walk root root) (hp : p.IsCycle)
    (hhom : surfaceSubgraphHomology (triangularTorusSurfaceEdgeClass L)
      p.edges.toFinset ≠ 0) :
    letI : NeZero p.darts.length :=
      ⟨Nat.ne_of_gt (List.length_pos_of_ne_nil
        (SimpleGraph.Walk.darts_eq_nil.not.mpr hp.not_nil))⟩
    kwLoopPhaseProduct (triangularTorusGraphPhase L rho 1 1)
      (kwGraphCycleDartLoop p) = 1 := by
  letI : NeZero p.darts.length :=
    ⟨Nat.ne_of_gt (List.length_pos_of_ne_nil
      (SimpleGraph.Walk.darts_eq_nil.not.mpr hp.not_nil))⟩
  obtain ⟨mx, my, hdisplacement, hwind, hinjInt⟩ :=
    exists_triangularTorusCycle_nonzeroHomology_periodicLift L p hp hhom
  let direction : Fin p.darts.length -> Fin 6 :=
    fun k => (triangularTorusCycleNativeDart L p k).2
  have hinj : Function.Injective (triangularPeriodStateCoord direction) :=
    triangularPeriodStateCoord_injective_of_intPeriodicPos direction hinjInt
  have hnonzero :
      (triangularPathDisplacement (List.ofFn direction)).1 ≠ 0 ∨
        (triangularPathDisplacement (List.ofFn direction)).2 ≠ 0 := by
    rw [triangularPathDisplacement_ofFn, hdisplacement]
    have hL : (L : Int) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt (lt_trans (by decide : 0 < 2)
        (Fact.out : 2 < L)))
    rcases hwind with hx | hy
    · exact Or.inl (mul_ne_zero hL hx)
    · exact Or.inr (mul_ne_zero hL hy)
  have hnb : ∀ k,
      direction (k + 1) ≠ triangularTorusDirectionReverse (direction k) := by
    simpa only [direction, triangularTorusCycleNativeDart_snd] using
      triangularTorus_cycleDirection_nonbacktracking L p hp
  have hprincipal := triangularPeriodicSimple_phaseCycle_eq_one_of_nonzero
    direction hinj hnb hnonzero
  obtain ⟨m, hm⟩ :=
    exists_triangularTurnExponent_sum_eq_eight_mul_even_of_phase_one
      direction hnb hprincipal
  apply triangularTorus_cyclePhaseProduct_eq_one_of_even_revolutions
    L rho hrho p hp m
  simpa only [direction, triangularTorusCycleNativeDart_snd] using hm

theorem triangularTorus_baseSpinSign_eq_if_homology_zero
    (h : SurfaceHomology 1) :
    (surfaceParitySign
      (surfaceQuadraticParity (triangularTorusSurfaceSpin 0 0) h) : Complex) =
      if h = 0 then 1 else -1 := by
  rcases h with ⟨hx, hy⟩
  let x : Fin 2 := hx 0
  let y : Fin 2 := hy 0
  have hx' : hx = fun _ : Fin 1 => x := by
    funext i
    fin_cases i
    rfl
  have hy' : hy = fun _ : Fin 1 => y := by
    funext i
    fin_cases i
    rfl
  rw [hx', hy']
  rw [triangularTorusSurfaceSpin_zero_zero_sign]
  have hpair :
      ((fun _ : Fin 1 => x), (fun _ : Fin 1 => y)) = 0 ↔
        x = 0 ∧ y = 0 := by
    constructor
    · intro h
      constructor
      · simpa using congrArg (fun z => z.1 0) h
      · simpa using congrArg (fun z => z.2 0) h
    · rintro ⟨hx0, hy0⟩
      apply Prod.ext <;> funext i
      · simpa [hx0]
      · simpa [hy0]
  by_cases hxy : x = 0 ∧ y = 0
  · rw [if_pos hxy, if_pos (hpair.mpr hxy)]
  · rw [if_neg hxy, if_neg (fun h => hxy (hpair.mp h))]

end StatMech.FrontierA

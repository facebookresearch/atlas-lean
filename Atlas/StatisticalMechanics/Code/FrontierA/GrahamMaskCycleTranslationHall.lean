/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierA.GrahamCanonicalTransferComponentCut











open Finset
open scoped symmDiff

namespace StatMech.GrahamGHS.FourColor

variable {I W : Type*} [Fintype I] [DecidableEq I]
  [Fintype W] [DecidableEq W]

open StatMech.Sharpness.RandomCurrent



def rightMaskCycleDifference
    (m : Finset I) (a c : ↑m -> Fin 4) : Finset I :=
  balancedMiddleDifference m a c ∪ balancedOuterDifference m a c



def CrossesRootComponentCut
    (ends : I -> Sym2 W) (K : Finset I) (k : W) (e : I) : Prop :=
  ∃ u v, u ∈ ends e ∧ v ∈ ends e ∧
    u ∉ StatMech.FrontierA.grahamComponentComplement ends K k ∧
    v ∈ StatMech.FrontierA.grahamComponentComplement ends K k


theorem rightMaskCycleTranslate_trans
    (m : Finset I) (a b c q : ↑m -> Fin 4) :
    rightMaskCycleTranslate m b c
        (rightMaskCycleTranslate m a b q) =
      rightMaskCycleTranslate m a c q := by
  rw [rightMaskCycleTranslate, rightMaskCycleTranslate,
    rightMaskCycleTranslate, balancedSwap_comp_eq_symmDiff]
  simp only [balancedMiddleDifference, balancedOuterDifference]
  have hmiddle :
      (colorClass m a 1 ∆ colorClass m b 1) ∆
          (colorClass m b 1 ∆ colorClass m c 1) =
        colorClass m a 1 ∆ colorClass m c 1 := by
    calc
      _ = colorClass m a 1 ∆
          (colorClass m b 1 ∆ colorClass m b 1) ∆
            colorClass m c 1 := by ac_rfl
      _ = _ := by simp
  have houter :
      (colorClass m a 0 ∆ colorClass m b 0) ∆
          (colorClass m b 0 ∆ colorClass m c 0) =
        colorClass m a 0 ∆ colorClass m c 0 := by
    calc
      _ = colorClass m a 0 ∆
          (colorClass m b 0 ∆ colorClass m b 0) ∆
            colorClass m c 0 := by ac_rfl
      _ = _ := by simp
  rw [hmiddle, houter]


@[simp] theorem rightMaskCycleTranslate_self
    (m : Finset I) (a q : ↑m -> Fin 4) :
    rightMaskCycleTranslate m a a q = q := by
  rw [rightMaskCycleTranslate, balancedMiddleDifference,
    balancedOuterDifference, symmDiff_self, symmDiff_self]
  funext i
  simp [balancedSwap, middleSwapOn, outerSwapOn]



theorem rightMaskCycleTranslate_left_injective
    (m : Finset I) (a q : ↑m -> Fin 4)
    (ha : fourColorMaskProfile m a = fourColorMaskProfile m q) :
    Function.Injective (fun c :
      {c : ↑m -> Fin 4 // fourColorMaskProfile m c =
        fourColorMaskProfile m a} =>
      rightMaskCycleTranslate m a c.1 q) := by
  intro c d hcd
  apply Subtype.ext
  by_contra hcne
  have hprofileAC : fourColorMaskProfile m a =
      fourColorMaskProfile m c.1 := c.2.symm
  have hprofileCD : fourColorMaskProfile m c.1 =
      fourColorMaskProfile m d.1 := c.2.trans d.2.symm
  have hprofileCQ : fourColorMaskProfile m c.1 =
      fourColorMaskProfile m q := hprofileAC.symm.trans ha
  have hfixed : rightMaskCycleTranslate m c.1 d.1 q = q := by
    have hcongr := congrArg
      (rightMaskCycleTranslate m a c.1) hcd
    have hleft : rightMaskCycleTranslate m a c.1
        (rightMaskCycleTranslate m a c.1 q) = q := by
      rw [rightMaskCycleTranslate_comm m a c.1 q,
        rightMaskCycleTranslate_trans, rightMaskCycleTranslate_self]
    have hright : rightMaskCycleTranslate m a c.1
        (rightMaskCycleTranslate m a d.1 q) =
          rightMaskCycleTranslate m c.1 d.1 q := by
      rw [rightMaskCycleTranslate_comm m a d.1 q,
        rightMaskCycleTranslate_trans,
        rightMaskCycleTranslate_comm m d.1 c.1 q]
    rw [hleft, hright] at hcongr
    exact hcongr.symm
  exact (rightMaskCycleTranslate_ne m c.1 d.1 q
    (congrArg Prod.fst hprofileCD)
    (congrArg Prod.snd hprofileCD)
    (congrArg Prod.fst hprofileCQ)
    (congrArg Prod.snd hprofileCQ) hcne) hfixed



theorem rightMaskCycleTranslate_rows
    (m : Finset I) (a c q : ↑m -> Fin 4)
    (hac : fourColorMaskProfile m a = fourColorMaskProfile m c)
    (haq : fourColorMaskProfile m a = fourColorMaskProfile m q) :
    rowClass m (rightMaskCycleTranslate m a c q) 0 =
        rowClass m q 0 ∆ rightMaskCycleDifference m a c ∧
      rowClass m (rightMaskCycleTranslate m a c q) 1 =
        rowClass m q 1 ∆ rightMaskCycleDifference m a c := by
  have hX : balancedMiddleDifference m a c ⊆
      colorClass m q 1 ∪ colorClass m q 2 := by
    have hsub := balancedMiddleDifference_subset m a c
      (congrArg Prod.fst hac)
    have hmid : middleMask m a = middleMask m q :=
      congrArg Prod.fst haq
    rw [← middleMask, ← hmid]
    exact hsub
  have hY : balancedOuterDifference m a c ⊆
      colorClass m q 0 ∪ colorClass m q 3 := by
    have hsub := balancedOuterDifference_subset m a c
      (congrArg Prod.snd hac)
    have hout : outerMask m a = outerMask m q :=
      congrArg Prod.snd haq
    rw [← outerMask, ← hout]
    exact hsub
  constructor
  · exact rowClass_balancedSwap_zero hX hY
  · exact rowClass_balancedSwap_one hX hY



theorem not_conn_symmDiff_of_noCrossing_componentComplement
    (ends : I -> Sym2 W) (K D : Finset I) (k zero : W)
    (hdisc : ¬ connK ends K k zero)
    (hcross : NoCrossingK ends (K ∆ D)
      (StatMech.FrontierA.grahamComponentComplement ends K k)) :
    ¬ connK ends (K ∆ D) k zero := by
  intro hconn
  have hk : k ∉ StatMech.FrontierA.grahamComponentComplement ends K k :=
    StatMech.FrontierA.grahamComponentComplement_not_mem ends K k
  have hzero : zero ∈
      StatMech.FrontierA.grahamComponentComplement ends K k := by
    rw [StatMech.FrontierA.grahamComponentComplement, mem_notConnCompK]
    exact hdisc
  exact (connK_not_mem_of_noCrossing hcross hk hconn) hzero



theorem exists_mem_difference_crossing_of_toggle_connected
    (ends : I -> Sym2 W) (K D : Finset I) (k zero : W)
    (hdisc : ¬ connK ends K k zero)
    (hconn : connK ends (K ∆ D) k zero) :
    ∃ e ∈ D, CrossesRootComponentCut ends K k e := by
  let S := StatMech.FrontierA.grahamComponentComplement ends K k
  have hk : k ∉ S :=
    StatMech.FrontierA.grahamComponentComplement_not_mem ends K k
  have hzero : zero ∈ S := by
    dsimp only [S]
    rw [StatMech.FrontierA.grahamComponentComplement, mem_notConnCompK]
    exact hdisc
  obtain ⟨e, he, hcross⟩ := exists_crossing_edge_mem_sdiff_of_connK
    (StatMech.FrontierA.grahamComponentComplement_noCrossing ends K k)
      hk hzero hconn
  have he' := Finset.mem_sdiff.mp he
  have heD : e ∈ D := by
    rcases Finset.mem_symmDiff.mp he'.1 with heK | heD
    · exact False.elim (he'.2 heK.1)
    · exact heD.1
  exact ⟨e, heD, hcross⟩




theorem exists_cycleDifference_crossing_of_translate_not_disconnects
    (ends : I -> Sym2 W) (m : Finset I) (k zero : W)
    (a c q : ↑m -> Fin 4)
    (hac : fourColorMaskProfile m a = fourColorMaskProfile m c)
    (haq : fourColorMaskProfile m a = fourColorMaskProfile m q)
    (hq : RowsDisconnect ends m q k zero)
    (hfail : ¬ RowsDisconnect ends m
      (rightMaskCycleTranslate m a c q) k zero) :
    (∃ e ∈ rightMaskCycleDifference m a c,
        CrossesRootComponentCut ends (rowClass m q 0) k e) ∨
      ∃ e ∈ rightMaskCycleDifference m a c,
        CrossesRootComponentCut ends (rowClass m q 1) k e := by
  have hrows := rightMaskCycleTranslate_rows m a c q hac haq
  rw [RowsDisconnect] at hq hfail
  have hconn :
      connK ends (rowClass m q 0 ∆ rightMaskCycleDifference m a c)
          k zero ∨
        connK ends (rowClass m q 1 ∆ rightMaskCycleDifference m a c)
          k zero := by
    rw [hrows.1, hrows.2] at hfail
    tauto
  rcases hconn with hconn | hconn
  · exact Or.inl (exists_mem_difference_crossing_of_toggle_connected
      ends (rowClass m q 0) (rightMaskCycleDifference m a c)
        k zero hq.1 hconn)
  · exact Or.inr (exists_mem_difference_crossing_of_toggle_connected
      ends (rowClass m q 1) (rightMaskCycleDifference m a c)
        k zero hq.2 hconn)



theorem rightMaskCycleTranslate_disconnects_of_no_crossing_edges
    (ends : I -> Sym2 W) (m : Finset I) (k zero : W)
    (a c q : ↑m -> Fin 4)
    (hac : fourColorMaskProfile m a = fourColorMaskProfile m c)
    (haq : fourColorMaskProfile m a = fourColorMaskProfile m q)
    (hq : RowsDisconnect ends m q k zero)
    (hno0 : ∀ e ∈ rightMaskCycleDifference m a c,
      ¬ CrossesRootComponentCut ends (rowClass m q 0) k e)
    (hno1 : ∀ e ∈ rightMaskCycleDifference m a c,
      ¬ CrossesRootComponentCut ends (rowClass m q 1) k e) :
    RowsDisconnect ends m
      (rightMaskCycleTranslate m a c q) k zero := by
  by_contra hfail
  rcases exists_cycleDifference_crossing_of_translate_not_disconnects
      ends m k zero a c q hac haq hq hfail with hcross | hcross
  · obtain ⟨e, he, hcut⟩ := hcross
    exact hno0 e he hcut
  · obtain ⟨e, he, hcut⟩ := hcross
    exact hno1 e he hcut



def RightMaskCycleDifferenceRespectsCuts
    (ends : I -> Sym2 W) (m K D : Finset I) (k : W) : Prop :=
  NoCrossingK ends (K ∆ D)
      (StatMech.FrontierA.grahamComponentComplement ends K k) ∧
    NoCrossingK ends ((m \ K) ∆ D)
      (StatMech.FrontierA.grahamComponentComplement ends (m \ K) k)



theorem rightMaskCycleTranslate_disconnects_of_respectsCuts
    (ends : I -> Sym2 W) (m : Finset I) (k zero : W)
    (a c q : ↑m -> Fin 4)
    (hac : fourColorMaskProfile m a = fourColorMaskProfile m c)
    (haq : fourColorMaskProfile m a = fourColorMaskProfile m q)
    (hq : RowsDisconnect ends m q k zero)
    (hcuts : RightMaskCycleDifferenceRespectsCuts ends m
      (rowClass m q 0) (rightMaskCycleDifference m a c) k) :
    RowsDisconnect ends m
      (rightMaskCycleTranslate m a c q) k zero := by
  have hrows := rightMaskCycleTranslate_rows m a c q hac haq
  rw [RowsDisconnect] at hq ⊢
  rw [hrows.1, hrows.2]
  constructor
  · exact not_conn_symmDiff_of_noCrossing_componentComplement
      ends (rowClass m q 0) (rightMaskCycleDifference m a c)
        k zero hq.1 hcuts.1
  · rw [rowClass_one_eq_sdiff] at hq ⊢
    exact not_conn_symmDiff_of_noCrossing_componentComplement
      ends (m \ rowClass m q 0) (rightMaskCycleDifference m a c)
        k zero hq.2 hcuts.2




noncomputable def maskFiberCycleTranslateEmbedding
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    (a : leftMaskFiber ends m j k l zero p)
    (q : rightMaskFiber ends m j k l zero p)
    (hgate : ∀ c : leftMaskFiber ends m j k l zero p,
      RowsDisconnect ends m
        (rightMaskCycleTranslate m a.1.1 c.1.1 q.1.1) k zero) :
    leftMaskFiber ends m j k l zero p ↪
      rightMaskFiber ends m j k l zero p where
  toFun c := rightMaskCycleTranslateMemOfDisconnects
    ends m j k l zero p a c q (hgate c)
  inj' := by
    intro c d hcd
    apply Subtype.ext
    apply Subtype.ext
    have hval := congrArg
      (fun z : rightMaskFiber ends m j k l zero p => z.1.1) hcd
    let A : {
        x : ↑m -> Fin 4 // fourColorMaskProfile m x =
          fourColorMaskProfile m a.1.1} := ⟨c.1.1, c.2.trans a.2.symm⟩
    let B : {
        x : ↑m -> Fin 4 // fourColorMaskProfile m x =
          fourColorMaskProfile m a.1.1} := ⟨d.1.1, d.2.trans a.2.symm⟩
    have hprofileAQ : fourColorMaskProfile m a.1.1 =
        fourColorMaskProfile m q.1.1 := a.2.trans q.2.symm
    have hAB : A = B := rightMaskCycleTranslate_left_injective
      m a.1.1 q.1.1 hprofileAQ (by
        change rightMaskCycleTranslate m a.1.1 c.1.1 q.1.1 =
          rightMaskCycleTranslate m a.1.1 d.1.1 q.1.1
        exact hval)
    exact congrArg (fun z : {
      x : ↑m -> Fin 4 // fourColorMaskProfile m x =
        fourColorMaskProfile m a.1.1} => z.1) hAB



theorem card_leftMaskFiber_le_rightMaskFiber_of_cycleTranslate
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    (a : leftMaskFiber ends m j k l zero p)
    (q : rightMaskFiber ends m j k l zero p)
    (hgate : ∀ c : leftMaskFiber ends m j k l zero p,
      RowsDisconnect ends m
        (rightMaskCycleTranslate m a.1.1 c.1.1 q.1.1) k zero) :
    Fintype.card (leftMaskFiber ends m j k l zero p) ≤
      Fintype.card (rightMaskFiber ends m j k l zero p) :=
  Fintype.card_le_of_embedding
    (maskFiberCycleTranslateEmbedding
      ends m j k l zero p a q hgate)



noncomputable def cycleTranslateBadCount
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    (base : leftMaskFiber ends m j k l zero p ×
      rightMaskFiber ends m j k l zero p) : Nat := by
  classical
  exact #((Finset.univ : Finset
    (leftMaskFiber ends m j k l zero p)).filter fun c =>
    ¬ RowsDisconnect ends m
      (rightMaskCycleTranslate m base.1.1.1 c.1.1 base.2.1.1) k zero)



theorem cycleTranslateBadCount_eq_zero_iff
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    (base : leftMaskFiber ends m j k l zero p ×
      rightMaskFiber ends m j k l zero p) :
    cycleTranslateBadCount ends m j k l zero p base = 0 ↔
      ∀ c : leftMaskFiber ends m j k l zero p,
        RowsDisconnect ends m
          (rightMaskCycleTranslate
            m base.1.1.1 c.1.1 base.2.1.1) k zero := by
  classical
  simp [cycleTranslateBadCount]



noncomputable def cycleTranslateMinBadPair
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (c : leftMaskFiber ends m j k l zero p) :
    leftMaskFiber ends m j k l zero p ×
      rightMaskFiber ends m j k l zero p := by
  let q := Classical.choice
    (rightMaskFiber_nonempty_of_left hloop hjk hkl hk0 p c)
  exact Classical.choose
    ((Finset.univ : Finset
      (leftMaskFiber ends m j k l zero p ×
        rightMaskFiber ends m j k l zero p)).exists_min_image
      (cycleTranslateBadCount ends m j k l zero p)
      ⟨(c, q), Finset.mem_univ _⟩)



theorem cycleTranslateMinBadPair_spec
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (c : leftMaskFiber ends m j k l zero p) :
    ∀ base : leftMaskFiber ends m j k l zero p ×
        rightMaskFiber ends m j k l zero p,
      cycleTranslateBadCount ends m j k l zero p
          (cycleTranslateMinBadPair
            ends m j k l zero hloop hjk hkl hk0 p c) ≤
        cycleTranslateBadCount ends m j k l zero p base := by
  let q := Classical.choice
    (rightMaskFiber_nonempty_of_left hloop hjk hkl hk0 p c)
  intro base
  exact (Classical.choose_spec
    ((Finset.univ : Finset
      (leftMaskFiber ends m j k l zero p ×
        rightMaskFiber ends m j k l zero p)).exists_min_image
      (cycleTranslateBadCount ends m j k l zero p)
      ⟨(c, q), Finset.mem_univ _⟩)).2 base (Finset.mem_univ _)



theorem card_leftMaskFiber_le_rightMaskFiber_of_minBadCount_zero
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (c : leftMaskFiber ends m j k l zero p)
    (hzero : cycleTranslateBadCount ends m j k l zero p
      (cycleTranslateMinBadPair
        ends m j k l zero hloop hjk hkl hk0 p c) = 0) :
    Fintype.card (leftMaskFiber ends m j k l zero p) ≤
      Fintype.card (rightMaskFiber ends m j k l zero p) := by
  let base := cycleTranslateMinBadPair
    ends m j k l zero hloop hjk hkl hk0 p c
  apply card_leftMaskFiber_le_rightMaskFiber_of_cycleTranslate
    ends m j k l zero p base.1 base.2
  exact (cycleTranslateBadCount_eq_zero_iff
    ends m j k l zero p base).mp hzero





theorem rowDataRepairHall_of_cycleTranslate_orbits
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (horbit : ∀ p : Finset I × Finset I,
      Nonempty (leftMaskFiber ends m j k l zero p) ->
        ∃ a : leftMaskFiber ends m j k l zero p,
          ∃ q : rightMaskFiber ends m j k l zero p,
            ∀ c : leftMaskFiber ends m j k l zero p,
              RowsDisconnect ends m
                (rightMaskCycleTranslate m a.1.1 c.1.1 q.1.1) k zero) :
    RowDataRepairHall ends m j k l zero := by
  apply rowDataRepairHall_of_maskwise
  intro p
  by_cases hleft : Nonempty (leftMaskFiber ends m j k l zero p)
  · obtain ⟨a, q, hgate⟩ := horbit p hleft
    exact card_leftMaskFiber_le_rightMaskFiber_of_cycleTranslate
      ends m j k l zero p a q hgate
  · have hempty : IsEmpty (leftMaskFiber ends m j k l zero p) :=
      not_nonempty_iff.mp hleft
    simp



theorem rowDataRepairHall_of_minCycleTranslateBadCount_zero
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (hzero : ∀ (p : Finset I × Finset I)
      (c : leftMaskFiber ends m j k l zero p),
      cycleTranslateBadCount ends m j k l zero p
        (cycleTranslateMinBadPair
          ends m j k l zero hloop hjk hkl hk0 p c) = 0) :
    RowDataRepairHall ends m j k l zero := by
  apply rowDataRepairHall_of_cycleTranslate_orbits
  intro p hleft
  let c := Classical.choice hleft
  let base := cycleTranslateMinBadPair
    ends m j k l zero hloop hjk hkl hk0 p c
  refine ⟨base.1, base.2, ?_⟩
  exact (cycleTranslateBadCount_eq_zero_iff
    ends m j k l zero p base).mp (hzero p c)




theorem rowDataRepairHall_of_cycleTranslate_respectsCuts
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hcuts : ∀ p : Finset I × Finset I,
      Nonempty (leftMaskFiber ends m j k l zero p) ->
        ∃ a : leftMaskFiber ends m j k l zero p,
          ∃ q : rightMaskFiber ends m j k l zero p,
            ∀ c : leftMaskFiber ends m j k l zero p,
              RightMaskCycleDifferenceRespectsCuts ends m
                (rowClass m q.1.1 0)
                (rightMaskCycleDifference m a.1.1 c.1.1) k) :
    RowDataRepairHall ends m j k l zero := by
  apply rowDataRepairHall_of_cycleTranslate_orbits
  intro p hleft
  obtain ⟨a, q, hq⟩ := hcuts p hleft
  refine ⟨a, q, fun c => ?_⟩
  exact rightMaskCycleTranslate_disconnects_of_respectsCuts
    ends m k zero a.1.1 c.1.1 q.1.1
      (a.2.trans c.2.symm) (a.2.trans q.2.symm) q.1.2.2.2.2.2
      (hq c)




theorem rowDataRepairHall_of_cycleTranslate_no_crossing_edges
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hno : ∀ p : Finset I × Finset I,
      Nonempty (leftMaskFiber ends m j k l zero p) ->
        ∃ a : leftMaskFiber ends m j k l zero p,
          ∃ q : rightMaskFiber ends m j k l zero p,
            ∀ c : leftMaskFiber ends m j k l zero p,
              (∀ e ∈ rightMaskCycleDifference m a.1.1 c.1.1,
                ¬ CrossesRootComponentCut
                  ends (rowClass m q.1.1 0) k e) ∧
              ∀ e ∈ rightMaskCycleDifference m a.1.1 c.1.1,
                ¬ CrossesRootComponentCut
                  ends (rowClass m q.1.1 1) k e) :
    RowDataRepairHall ends m j k l zero := by
  apply rowDataRepairHall_of_cycleTranslate_orbits
  intro p hleft
  obtain ⟨a, q, hq⟩ := hno p hleft
  refine ⟨a, q, fun c => ?_⟩
  exact rightMaskCycleTranslate_disconnects_of_no_crossing_edges
    ends m k zero a.1.1 c.1.1 q.1.1
      (a.2.trans c.2.symm) (a.2.trans q.2.symm) q.1.2.2.2.2.2
      (hq c).1 (hq c).2

end StatMech.GrahamGHS.FourColor

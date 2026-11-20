/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierA.GrahamMaskAffineCycle








open Finset
open Classical
open scoped symmDiff

namespace StatMech.GrahamGHS.FourColor

open StatMech.Sharpness.RandomCurrent

variable {I W : Type*} [Fintype I] [DecidableEq I]
  [Fintype W] [DecidableEq W]


def RootSpanning (ends : I → Sym2 W) (S : Finset I) (root : W) : Prop :=
  ∀ i ∈ S, ∀ x ∈ ends i, connK ends S root x


theorem eq_or_eq_of_card_le_two
    {A : Type*} [Fintype A] [DecidableEq A]
    (a b x : A) (hab : a ≠ b) (hcard : Fintype.card A ≤ 2) :
    x = a ∨ x = b := by
  letI : Nontrivial A := ⟨⟨a, b, hab⟩⟩
  have hone : 1 < Fintype.card A := Fintype.one_lt_card
  have hcard2 : Fintype.card A = 2 := by omega
  have hpCard : ({a, b} : Finset A).card = 2 := by simp [hab]
  have hp : ({a, b} : Finset A) = Finset.univ :=
    Finset.eq_univ_of_card _ (hpCard.trans hcard2.symm)
  have hx : x ∈ ({a, b} : Finset A) := by rw [hp]; simp
  simpa using hx



theorem rootSpanning_of_subsingleton_cycleSector
    (ends : I → Sym2 W) (S : Finset I) (a b : W)
    (hloop : ∀ i ∈ S, ¬ (ends i).IsDiag)
    (hab : a ≠ b) (hsrc : sources ends S = {a, b})
    (hsub : Subsingleton (boundarySector ends S ∅)) :
    RootSpanning ends S a := by
  have habConn : connK ends S a b :=
    StatMech.Walls.gc6_pairingPath_abstract ends S S hloop
      Finset.Subset.rfl hsrc hab
  let E := edgeComponent ends S a
  have hES : E ⊆ S := by
    intro i hi
    dsimp only [E] at hi
    rw [edgeComponent, Finset.mem_filter] at hi
    exact hi.1
  have hEsrc : sources ends E = {a, b} := by
    dsimp only [E]
    rw [sources_edgeComponent, hsrc]
    apply Finset.inter_eq_left.mpr
    intro x hx
    rw [mem_compOf]
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact Relation.ReflTransGen.refl
    · exact habConn
  have hcomplSrc : sources ends (S \ E) = ∅ := by
    rw [sources_sdiff_of_subset hES, hsrc, hEsrc, symmDiff_self]
    rfl
  let T : boundarySector ends S ∅ :=
    ⟨S \ E, Finset.sdiff_subset, hcomplSrc⟩
  have hT := congrArg Subtype.val
    (hsub.allEq T (emptyBoundarySector ends S))
  have hcompl : S \ E = ∅ := by
    simpa [T, emptyBoundarySector] using hT
  intro i hi x hx
  have hiE : i ∈ E := by
    by_contra hnot
    have : i ∈ S \ E := Finset.mem_sdiff.mpr ⟨hi, hnot⟩
    rw [hcompl] at this
    simp at this
  dsimp only [E] at hiE
  rw [edgeComponent, Finset.mem_filter] at hiE
  exact hiE.2 x hx



theorem subsingleton_cycleSector_sdiff_of_card_le_two
    (ends : I → Sym2 W) (S Z : Finset I)
    (hZS : Z ⊆ S) (hZsrc : sources ends Z = ∅) (hZne : Z ≠ ∅)
    (hcard : Fintype.card (boundarySector ends S ∅) ≤ 2) :
    Subsingleton (boundarySector ends (S \ Z) ∅) := by
  let z : boundarySector ends S ∅ := ⟨Z, hZS, hZsrc⟩
  have hz0 : z ≠ emptyBoundarySector ends S := by
    intro h
    apply hZne
    have := congrArg Subtype.val h
    simpa [z, emptyBoundarySector] using this
  have hempty (T : boundarySector ends (S \ Z) ∅) : T.1 = ∅ := by
    let t : boundarySector ends S ∅ :=
      ⟨T.1, T.2.1.trans Finset.sdiff_subset, T.2.2⟩
    rcases eq_or_eq_of_card_le_two
      (emptyBoundarySector ends S) z t hz0.symm hcard with ht | ht
    · have := congrArg Subtype.val ht
      simpa [t, emptyBoundarySector] using this
    · exfalso
      obtain ⟨i, hiZ⟩ := Finset.nonempty_iff_ne_empty.mpr hZne
      have hit : i ∈ T.1 := by
        have hval := congrArg Subtype.val ht
        change T.1 = Z at hval
        rw [hval]
        exact hiZ
      exact (Finset.mem_sdiff.mp (T.2.1 hit)).2 hiZ
  constructor
  intro T U
  apply Subtype.ext
  rw [hempty T, hempty U]



theorem rootSpanning_sdiff_of_cycleSector_card_le_two
    (ends : I → Sym2 W) (S Z : Finset I) (a b : W)
    (hloop : ∀ i ∈ S, ¬ (ends i).IsDiag)
    (hab : a ≠ b) (hsrc : sources ends S = {a, b})
    (hZS : Z ⊆ S) (hZsrc : sources ends Z = ∅) (hZne : Z ≠ ∅)
    (hcard : Fintype.card (boundarySector ends S ∅) ≤ 2) :
    RootSpanning ends (S \ Z) a := by
  apply rootSpanning_of_subsingleton_cycleSector ends (S \ Z) a b
  · intro i hi
    exact hloop i (Finset.sdiff_subset hi)
  · exact hab
  · rw [sources_sdiff_of_subset hZS, hsrc, hZsrc]
    simp
  · exact subsingleton_cycleSector_sdiff_of_card_le_two
      ends S Z hZS hZsrc hZne hcard




theorem conn_union_union_cycle_side
    (ends : I → Sym2 W) (K L Z : Finset I) (k x : W)
    (hK : RootSpanning ends K k) (hL : RootSpanning ends L k)
    (hconn : connK ends ((K ∪ L) ∪ Z) k x) :
    connK ends (K ∪ Z) k x ∨ connK ends (L ∪ Z) k x := by
  induction hconn with
  | refl => exact Or.inl Relation.ReflTransGen.refl
  | @tail a b _ hstep ih =>
      obtain ⟨i, hi, ha, hb, hab⟩ := hstep
      rcases Finset.mem_union.mp hi with hiKL | hiZ
      · rcases Finset.mem_union.mp hiKL with hiK | hiL
        · exact Or.inl (connK_mono Finset.subset_union_left
            (hK i hiK b hb))
        · exact Or.inr (connK_mono Finset.subset_union_left
            (hL i hiL b hb))
      · rcases ih with hKa | hLa
        · exact Or.inl (hKa.tail ⟨i, Finset.mem_union_right _ hiZ,
            ha, hb, hab⟩)
        · exact Or.inr (hLa.tail ⟨i, Finset.mem_union_right _ hiZ,
            ha, hb, hab⟩)


theorem not_conn_union_union_cycle
    (ends : I → Sym2 W) (K L Z : Finset I) (k zero : W)
    (hK : RootSpanning ends K k) (hL : RootSpanning ends L k)
    (hKZ : ¬ connK ends (K ∪ Z) k zero)
    (hLZ : ¬ connK ends (L ∪ Z) k zero) :
    ¬ connK ends ((K ∪ L) ∪ Z) k zero := by
  intro hconn
  exact (conn_union_union_cycle_side ends K L Z k zero hK hL hconn).elim
    hKZ hLZ


theorem middleCycle_fourthCorner_gates
    (ends : I → Sym2 W) (M O X : Finset I) (j k l zero : W)
    (hloopM : ∀ i ∈ M, ¬ (ends i).IsDiag)
    (hloopO : ∀ i ∈ O, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l)
    (hMsrc : sources ends M = {k, l})
    (hOsrc : sources ends O = {j, k})
    (hOsub : Subsingleton (boundarySector ends O ∅))
    (hMcard : Fintype.card (boundarySector ends M ∅) ≤ 2)
    (hXM : X ⊆ M) (hXsrc : sources ends X = ∅) (hXne : X ≠ ∅)
    (hOdisc : ¬ connK ends O k zero)
    (hMdisc : ¬ connK ends M k zero)
    (hOXdisc : ¬ connK ends (O ∪ X) k zero)
    (hMXdisc : ¬ connK ends (M \ X) k zero) :
    ¬ connK ends (M ∪ O) k zero ∧
      ¬ connK ends ((M \ X) ∪ O) k zero ∧
      ¬ connK ends X k zero := by
  have hOroot : RootSpanning ends O k := by
    apply rootSpanning_of_subsingleton_cycleSector ends O k j
    · exact hloopO
    · exact hjk.symm
    · simpa only [Finset.pair_comm] using hOsrc
    · exact hOsub
  have hMXroot : RootSpanning ends (M \ X) k :=
    rootSpanning_sdiff_of_cycleSector_card_le_two ends M X k l
      hloopM hkl hMsrc hXM hXsrc hXne hMcard
  have hminus : ¬ connK ends ((M \ X) ∪ O) k zero := by
    have h := not_conn_union_union_cycle ends O (M \ X) ∅ k zero
      hOroot hMXroot (by simpa using hOdisc) (by simpa using hMXdisc)
    simpa [Finset.union_comm, Finset.union_left_comm,
      Finset.union_assoc] using h
  have htotal : ¬ connK ends (M ∪ O) k zero := by
    have hMXunion : (M \ X) ∪ X = M :=
      Finset.sdiff_union_of_subset hXM
    have h := not_conn_union_union_cycle ends O (M \ X) X k zero
      hOroot hMXroot hOXdisc (by simpa [hMXunion] using hMdisc)
    rw [Finset.union_assoc O (M \ X) X, hMXunion,
      Finset.union_comm O M] at h
    exact h
  have hXdisc : ¬ connK ends X k zero := by
    intro hconn
    exact hOXdisc (connK_mono Finset.subset_union_right hconn)
  exact ⟨htotal, hminus, hXdisc⟩



theorem outerCycle_fourthCorner_gates
    (ends : I → Sym2 W) (M O Y : Finset I) (j k l zero : W)
    (hloopM : ∀ i ∈ M, ¬ (ends i).IsDiag)
    (hloopO : ∀ i ∈ O, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l)
    (hMsrc : sources ends M = {k, l})
    (hOsrc : sources ends O = {j, k})
    (hMsub : Subsingleton (boundarySector ends M ∅))
    (hOcard : Fintype.card (boundarySector ends O ∅) ≤ 2)
    (hYO : Y ⊆ O) (hYsrc : sources ends Y = ∅) (hYne : Y ≠ ∅)
    (hMdisc : ¬ connK ends M k zero)
    (hOdisc : ¬ connK ends O k zero)
    (hMYdisc : ¬ connK ends (M ∪ Y) k zero)
    (hOYdisc : ¬ connK ends (O \ Y) k zero) :
    ¬ connK ends (M ∪ O) k zero ∧
      ¬ connK ends (M ∪ (O \ Y)) k zero ∧
      ¬ connK ends Y k zero := by
  have hMroot : RootSpanning ends M k :=
    rootSpanning_of_subsingleton_cycleSector ends M k l
      hloopM hkl hMsrc hMsub
  have hOYroot : RootSpanning ends (O \ Y) k := by
    apply rootSpanning_sdiff_of_cycleSector_card_le_two ends O Y k j
    · exact hloopO
    · exact hjk.symm
    · simpa only [Finset.pair_comm] using hOsrc
    · exact hYO
    · exact hYsrc
    · exact hYne
    · exact hOcard
  have hminus : ¬ connK ends (M ∪ (O \ Y)) k zero := by
    have h := not_conn_union_union_cycle ends M (O \ Y) ∅ k zero
      hMroot hOYroot (by simpa using hMdisc) (by simpa using hOYdisc)
    simpa [Finset.union_assoc] using h
  have htotal : ¬ connK ends (M ∪ O) k zero := by
    have hOYunion : (O \ Y) ∪ Y = O :=
      Finset.sdiff_union_of_subset hYO
    have h := not_conn_union_union_cycle ends M (O \ Y) Y k zero
      hMroot hOYroot hMYdisc (by simpa [hOYunion] using hOdisc)
    rw [Finset.union_assoc M (O \ Y) Y, hOYunion] at h
    exact h
  have hYdisc : ¬ connK ends Y k zero := by
    intro hconn
    exact hMYdisc (connK_mono Finset.subset_union_right hconn)
  exact ⟨htotal, hminus, hYdisc⟩



theorem colorClass_one_eq_middleMask_sdiff_two
    (m : Finset I) (c : ↑m → Fin 4) :
    colorClass m c 1 = middleMask m c \ colorClass m c 2 := by
  rw [middleMask]
  ext i
  have hd := Finset.disjoint_left.mp
    (colorClass_disjoint m c (show (1 : Fin 4) ≠ 2 by decide))
  simp only [Finset.mem_sdiff, Finset.mem_union]
  aesop


theorem rightRows_eq_cycleCoordinates
    (m : Finset I) (q : ↑m → Fin 4) :
    rowClass m q 0 =
        (middleMask m q \ colorClass m q 2) ∪
          (outerMask m q \ colorClass m q 3) ∧
      rowClass m q 1 = colorClass m q 2 ∪ colorClass m q 3 := by
  constructor
  · rw [rowClass_zero, colorClass_one_eq_middleMask_sdiff_two,
      colorClass_zero_eq_outerMask_sdiff_three]
    exact Finset.union_comm _ _
  · exact rowClass_one m q



theorem rightRows_eq_of_cycleCoordinates_empty
    (m M O : Finset I) (q : ↑m → Fin 4)
    (hM : middleMask m q = M) (hO : outerMask m q = O)
    (h2 : colorClass m q 2 = ∅) (h3 : colorClass m q 3 = ∅) :
    rowClass m q 0 = M ∪ O ∧ rowClass m q 1 = ∅ := by
  have hrows := rightRows_eq_cycleCoordinates m q
  constructor
  · simpa [hM, hO, h2, h3] using hrows.1
  · simpa [h2, h3] using hrows.2



theorem rightRows_eq_of_middleCycleCoordinate
    (m M O X : Finset I) (q : ↑m → Fin 4)
    (hM : middleMask m q = M) (hO : outerMask m q = O)
    (h2 : colorClass m q 2 = X) (h3 : colorClass m q 3 = ∅) :
    rowClass m q 0 = (M \ X) ∪ O ∧ rowClass m q 1 = X := by
  have hrows := rightRows_eq_cycleCoordinates m q
  constructor
  · simpa [hM, hO, h2, h3] using hrows.1
  · simpa [h2, h3] using hrows.2



theorem rightRows_eq_of_outerCycleCoordinate
    (m M O Y : Finset I) (q : ↑m → Fin 4)
    (hM : middleMask m q = M) (hO : outerMask m q = O)
    (h2 : colorClass m q 2 = ∅) (h3 : colorClass m q 3 = Y) :
    rowClass m q 0 = M ∪ (O \ Y) ∧ rowClass m q 1 = Y := by
  have hrows := rightRows_eq_cycleCoordinates m q
  constructor
  · simpa [hM, hO, h2, h3] using hrows.1
  · simpa [h2, h3] using hrows.2

theorem not_conn_empty (ends : I → Sym2 W) {k zero : W} (hk0 : k ≠ zero) :
    ¬ connK ends ∅ k zero := by
  intro h
  rcases h.cases_tail with hEq | ⟨x, -, i, hi, -⟩
  · exact hk0 hEq.symm
  · simp at hi



theorem rightMaskCycleTranslate_disconnects_of_first_empty
    (ends : I → Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (c d : leftMaskFiber ends m j k l zero p) (hcd : c ≠ d)
    (hcEmpty : leftMaskCyclePair ends m j k l zero p c =
      emptyMaskCyclePair ends p)
    (hcycle : Fintype.card (boundarySector ends p.1 ∅) *
      Fintype.card (boundarySector ends p.2 ∅) ≤ 2)
    (q : rightMaskFiber ends m j k l zero p) :
    RowsDisconnect ends m
      (rightMaskCycleTranslate m c.1.1 d.1.1 q.1.1) k zero := by
  let M := p.1
  let O := p.2
  let X := balancedMiddleDifference m c.1.1 d.1.1
  let Y := balancedOuterDifference m c.1.1 d.1.1
  let qt := rightMaskCycleTranslate m c.1.1 d.1.1 q.1.1
  have hmidc : middleMask m c.1.1 = M := congrArg Prod.fst c.2
  have houtc : outerMask m c.1.1 = O := congrArg Prod.snd c.2
  have hmidd : middleMask m d.1.1 = M := congrArg Prod.fst d.2
  have houtd : outerMask m d.1.1 = O := congrArg Prod.snd d.2
  have hmidq : middleMask m q.1.1 = M := congrArg Prod.fst q.2
  have houtq : outerMask m q.1.1 = O := congrArg Prod.snd q.2
  have hMsrc : sources ends M = {k, l} := by
    rw [← hmidc]
    exact leftPattern_middleMask_sources c.1.2
  have hOsrc : sources ends O = {j, k} := by
    rw [← houtc]
    exact leftPattern_outerMask_sources c.1.2
  have hMm : M ⊆ m := by
    rw [← hmidc, middleMask]
    exact Finset.union_subset (colorClass_subset m c.1.1 1)
      (colorClass_subset m c.1.1 2)
  have hOm : O ⊆ m := by
    rw [← houtc, outerMask]
    exact Finset.union_subset (colorClass_subset m c.1.1 0)
      (colorClass_subset m c.1.1 3)
  have hloopM : ∀ i ∈ M, ¬ (ends i).IsDiag :=
    fun i hi => hloop i (hMm hi)
  have hloopO : ∀ i ∈ O, ¬ (ends i).IsDiag :=
    fun i hi => hloop i (hOm hi)
  have hXc : X ⊆ middleMask m c.1.1 :=
    balancedMiddleDifference_subset m c.1.1 d.1.1
      (hmidc.trans hmidd.symm)
  have hYc : Y ⊆ outerMask m c.1.1 :=
    balancedOuterDifference_subset m c.1.1 d.1.1
      (houtc.trans houtd.symm)
  have hXM : X ⊆ M := by simpa only [hmidc] using hXc
  have hYO : Y ⊆ O := by simpa only [houtc] using hYc
  have hXsrc : sources ends X = ∅ := by
    dsimp only [X]
    rw [balancedMiddleDifference, sources_symmDiff,
      c.1.2.2.1, d.1.2.2.1]
    simp
  have hYsrc : sources ends Y = ∅ := by
    dsimp only [Y]
    rw [balancedOuterDifference, sources_symmDiff,
      c.1.2.1, d.1.2.1]
    simp
  have hcRows := rows_eq_masks_of_leftMaskCyclePair_eq_empty
    ends m j k l zero p c hcEmpty
  have hOdisc : ¬ connK ends O k zero := by
    simpa [RowsDisconnect, O, hcRows.1] using c.1.2.2.2.2.2.1
  have hMdisc : ¬ connK ends M k zero := by
    simpa [RowsDisconnect, M, hcRows.2] using c.1.2.2.2.2.2.2
  have hXcolors : X ⊆ colorClass m c.1.1 1 ∪ colorClass m c.1.1 2 := by
    simpa only [middleMask] using hXc
  have hYcolors : Y ⊆ colorClass m c.1.1 0 ∪ colorClass m c.1.1 3 := by
    simpa only [outerMask] using hYc
  have hswap : balancedSwap m X Y c.1.1 = d.1.1 := by
    dsimp only [X, Y]
    exact balancedSwap_difference m c.1.1 d.1.1
      (hmidc.trans hmidd.symm) (houtc.trans houtd.symm)
  have hdRow0 : rowClass m d.1.1 0 = O ∆ (X ∪ Y) := by
    calc
      rowClass m d.1.1 0 = rowClass m (balancedSwap m X Y c.1.1) 0 :=
        congrArg (fun z => rowClass m z 0) hswap.symm
      _ = rowClass m c.1.1 0 ∆ (X ∪ Y) :=
        rowClass_balancedSwap_zero hXcolors hYcolors
      _ = O ∆ (X ∪ Y) := by rw [hcRows.1]
  have hdRow1 : rowClass m d.1.1 1 = M ∆ (X ∪ Y) := by
    calc
      rowClass m d.1.1 1 = rowClass m (balancedSwap m X Y c.1.1) 1 :=
        congrArg (fun z => rowClass m z 1) hswap.symm
      _ = rowClass m c.1.1 1 ∆ (X ∪ Y) :=
        rowClass_balancedSwap_one hXcolors hYcolors
      _ = M ∆ (X ∪ Y) := by rw [hcRows.2]
  have hdDisc0 : ¬ connK ends (O ∆ (X ∪ Y)) k zero := by
    rw [← hdRow0]
    exact d.1.2.2.2.2.2.1
  have hdDisc1 : ¬ connK ends (M ∆ (X ∪ Y)) k zero := by
    rw [← hdRow1]
    exact d.1.2.2.2.2.2.2
  have hXq : X ⊆ colorClass m q.1.1 1 ∪ colorClass m q.1.1 2 := by
    rw [← middleMask, hmidq]
    exact hXM
  have hYq : Y ⊆ colorClass m q.1.1 0 ∪ colorClass m q.1.1 3 := by
    rw [← outerMask, houtq]
    exact hYO
  have hYq' : Y ⊆ colorClass m (middleSwapOn m X q.1.1) 0 ∪
      colorClass m (middleSwapOn m X q.1.1) 3 := by
    rwa [colorClass_middleSwapOn_zero, colorClass_middleSwapOn_three]
  have hqt2 : colorClass m qt 2 = colorClass m q.1.1 2 ∆ X := by
    dsimp only [qt, rightMaskCycleTranslate]
    unfold balancedSwap
    rw [colorClass_outerSwapOn_two,
      colorClass_middleSwapOn_two m X q.1.1 hXq]
  have hqt3 : colorClass m qt 3 = colorClass m q.1.1 3 ∆ Y := by
    dsimp only [qt, rightMaskCycleTranslate]
    unfold balancedSwap
    rw [colorClass_outerSwapOn_three m Y _ hYq',
      colorClass_middleSwapOn_three]
  have hc1 : colorClass m c.1.1 1 = ∅ := by
    have h := congrArg (fun z => z.1.1) hcEmpty
    simpa [leftMaskCyclePair, emptyMaskCyclePair,
      emptyBoundarySector] using h
  have hc3 : colorClass m c.1.1 3 = ∅ := by
    have h := congrArg (fun z => z.2.1) hcEmpty
    simpa [leftMaskCyclePair, emptyMaskCyclePair,
      emptyBoundarySector] using h
  have hd1 : colorClass m d.1.1 1 = X := by
    rw [← hswap]
    unfold balancedSwap
    rw [colorClass_outerSwapOn_one,
      colorClass_middleSwapOn_one m X c.1.1 hXcolors, hc1]
    simp
  have hYc' : Y ⊆ colorClass m (middleSwapOn m X c.1.1) 0 ∪
      colorClass m (middleSwapOn m X c.1.1) 3 := by
    rwa [colorClass_middleSwapOn_zero, colorClass_middleSwapOn_three]
  have hd3 : colorClass m d.1.1 3 = Y := by
    rw [← hswap]
    unfold balancedSwap
    rw [colorClass_outerSwapOn_three m Y _ hYc',
      colorClass_middleSwapOn_three, hc3]
    simp
  let emptyPair := emptyMaskCyclePair ends p
  let dPair := leftMaskCyclePair ends m j k l zero p d
  have hdPairNe : emptyPair ≠ dPair := by
    intro heq
    apply hcd
    apply (leftMaskCycleEmbedding ends m j k l zero p).injective
    exact hcEmpty.trans heq
  have hambient : Fintype.card
      (boundarySector ends p.1 ∅ × boundarySector ends p.2 ∅) ≤ 2 := by
    simpa only [Fintype.card_prod] using hcycle
  have hqPair := eq_or_eq_of_card_le_two emptyPair dPair
    (rightMaskCyclePair ends m j k l zero p q) hdPairNe hambient
  have hcoord :
      (colorClass m qt 2 = ∅ ∧ colorClass m qt 3 = ∅) ∨
      (colorClass m qt 2 = X ∧ colorClass m qt 3 = Y) := by
    rcases hqPair with hqEmpty | hqd
    · right
      have hq2 : colorClass m q.1.1 2 = ∅ := by
        have h := congrArg (fun z => z.1.1) hqEmpty
        simpa [rightMaskCyclePair, emptyPair, emptyMaskCyclePair,
          emptyBoundarySector] using h
      have hq3 : colorClass m q.1.1 3 = ∅ := by
        have h := congrArg (fun z => z.2.1) hqEmpty
        simpa [rightMaskCyclePair, emptyPair, emptyMaskCyclePair,
          emptyBoundarySector] using h
      constructor
      · rw [hqt2, hq2]
        ext i
        simp [Finset.mem_symmDiff]
      · rw [hqt3, hq3]
        ext i
        simp [Finset.mem_symmDiff]
    · left
      have hq2 : colorClass m q.1.1 2 = X := by
        have h := congrArg (fun z => z.1.1) hqd
        simpa [rightMaskCyclePair, dPair, leftMaskCyclePair, hd1] using h
      have hq3 : colorClass m q.1.1 3 = Y := by
        have h := congrArg (fun z => z.2.1) hqd
        simpa [rightMaskCyclePair, dPair, leftMaskCyclePair, hd3] using h
      constructor
      · rw [hqt2, hq2, symmDiff_self]
        rfl
      · rw [hqt3, hq3, symmDiff_self]
        rfl
  have hmidqt : middleMask m qt = M := by
    dsimp only [qt, rightMaskCycleTranslate]
    rw [middleMask_balancedSwap, hmidq]
  have houtqt : outerMask m qt = O := by
    dsimp only [qt, rightMaskCycleTranslate]
    rw [outerMask_balancedSwap, houtq]
  rcases leftMaskCycleDifference_empty_side_of_cycleProduct_le_two
    ends m j k l zero p c d hcycle with hXempty | hYempty
  · have hXe : X = ∅ := by simpa only [X] using hXempty
    have hYne : Y ≠ ∅ := by
      intro hYe
      apply hcd
      apply Subtype.ext
      apply Subtype.ext
      calc
        c.1.1 = balancedSwap m X Y c.1.1 := by
          rw [hXe, hYe]
          funext i
          simp [balancedSwap, middleSwapOn, outerSwapOn]
        _ = d.1.1 := hswap
    have hMsub : Subsingleton (boundarySector ends M ∅) := by
      rcases cycleProduct_le_two_factor_card_eq_one ends p hcycle with h | h
      · exact Fintype.card_le_one_iff_subsingleton.mp (by simpa [M] using h.le)
      · exfalso
        have hsub := Fintype.card_le_one_iff_subsingleton.mp (by simpa [O] using h.le)
        let y : boundarySector ends O ∅ := ⟨Y, hYO, hYsrc⟩
        have hy := congrArg Subtype.val
          (hsub.allEq y (emptyBoundarySector ends O))
        apply hYne
        simpa [y, emptyBoundarySector] using hy
    have hOcard : Fintype.card (boundarySector ends O ∅) ≤ 2 := by
      have hpos : 0 < Fintype.card (boundarySector ends M ∅) :=
        Fintype.card_pos_iff.mpr ⟨emptyBoundarySector ends M⟩
      dsimp only [M, O] at hpos ⊢
      nlinarith [hcycle]
    have hMYdisc : ¬ connK ends (M ∪ Y) k zero := by
      have hdisj : Disjoint M Y :=
        (middleMask_disjoint_outerMask m c.1.1).mono
          (by rw [hmidc]) hYc
      have hsymm : M ∆ (X ∪ Y) = M ∪ Y := by
        rw [hXe, Finset.empty_union, hdisj.symmDiff_eq_sup]
        rfl
      rwa [hsymm] at hdDisc1
    have hOYdisc : ¬ connK ends (O \ Y) k zero := by
      have hsymm : O ∆ (X ∪ Y) = O \ Y := by
        rw [hXe, Finset.empty_union, symmDiff_of_ge hYO]
      rwa [hsymm] at hdDisc0
    have hgates := outerCycle_fourthCorner_gates ends M O Y j k l zero
      hloopM hloopO hjk hkl hMsrc hOsrc hMsub hOcard hYO hYsrc hYne
      hMdisc hOdisc hMYdisc hOYdisc
    rcases hcoord with hempty | hnonzero
    · have hrows := rightRows_eq_of_cycleCoordinates_empty
        m M O qt hmidqt houtqt hempty.1 hempty.2
      rw [RowsDisconnect, hrows.1, hrows.2]
      exact ⟨hgates.1, not_conn_empty ends hk0⟩
    · have hrows := rightRows_eq_of_outerCycleCoordinate
        m M O Y qt hmidqt houtqt (by simpa [hXe] using hnonzero.1)
        hnonzero.2
      rw [RowsDisconnect, hrows.1, hrows.2]
      exact ⟨hgates.2.1, hgates.2.2⟩
  · have hYe : Y = ∅ := by simpa only [Y] using hYempty
    have hXne : X ≠ ∅ := by
      intro hXe
      apply hcd
      apply Subtype.ext
      apply Subtype.ext
      calc
        c.1.1 = balancedSwap m X Y c.1.1 := by
          rw [hXe, hYe]
          funext i
          simp [balancedSwap, middleSwapOn, outerSwapOn]
        _ = d.1.1 := hswap
    have hOsub : Subsingleton (boundarySector ends O ∅) := by
      rcases cycleProduct_le_two_factor_card_eq_one ends p hcycle with h | h
      · exfalso
        have hsub := Fintype.card_le_one_iff_subsingleton.mp (by simpa [M] using h.le)
        let x : boundarySector ends M ∅ := ⟨X, hXM, hXsrc⟩
        have hx := congrArg Subtype.val
          (hsub.allEq x (emptyBoundarySector ends M))
        apply hXne
        simpa [x, emptyBoundarySector] using hx
      · exact Fintype.card_le_one_iff_subsingleton.mp (by simpa [O] using h.le)
    have hMcard : Fintype.card (boundarySector ends M ∅) ≤ 2 := by
      have hpos : 0 < Fintype.card (boundarySector ends O ∅) :=
        Fintype.card_pos_iff.mpr ⟨emptyBoundarySector ends O⟩
      dsimp only [M, O] at hpos ⊢
      nlinarith [hcycle]
    have hOXdisc : ¬ connK ends (O ∪ X) k zero := by
      have hdisj : Disjoint O X :=
        (middleMask_disjoint_outerMask m c.1.1).symm.mono
          (by rw [houtc]) hXc
      have hsymm : O ∆ (X ∪ Y) = O ∪ X := by
        rw [hYe, Finset.union_empty, hdisj.symmDiff_eq_sup]
        rfl
      rwa [hsymm] at hdDisc0
    have hMXdisc : ¬ connK ends (M \ X) k zero := by
      have hsymm : M ∆ (X ∪ Y) = M \ X := by
        rw [hYe, Finset.union_empty, symmDiff_of_ge hXM]
      rwa [hsymm] at hdDisc1
    have hgates := middleCycle_fourthCorner_gates ends M O X j k l zero
      hloopM hloopO hjk hkl hMsrc hOsrc hOsub hMcard hXM hXsrc hXne
      hOdisc hMdisc hOXdisc hMXdisc
    rcases hcoord with hempty | hnonzero
    · have hrows := rightRows_eq_of_cycleCoordinates_empty
        m M O qt hmidqt houtqt hempty.1 hempty.2
      rw [RowsDisconnect, hrows.1, hrows.2]
      exact ⟨hgates.1, not_conn_empty ends hk0⟩
    · have hrows := rightRows_eq_of_middleCycleCoordinate
        m M O X qt hmidqt houtqt hnonzero.1
        (by simpa [hYe] using hnonzero.2)
      rw [RowsDisconnect, hrows.1, hrows.2]
      exact ⟨hgates.2.1, hgates.2.2⟩



theorem rightMaskCycleTranslate_comm
    (m : Finset I) (c d q : ↑m → Fin 4) :
    rightMaskCycleTranslate m c d q = rightMaskCycleTranslate m d c q := by
  simp [rightMaskCycleTranslate, balancedMiddleDifference,
    balancedOuterDifference, symmDiff_comm]



theorem rightMaskCycleTranslate_disconnects_of_cycleProduct_le_two
    (ends : I → Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (c d : leftMaskFiber ends m j k l zero p) (hcd : c ≠ d)
    (hcycle : Fintype.card (boundarySector ends p.1 ∅) *
      Fintype.card (boundarySector ends p.2 ∅) ≤ 2)
    (q : rightMaskFiber ends m j k l zero p) :
    RowsDisconnect ends m
      (rightMaskCycleTranslate m c.1.1 d.1.1 q.1.1) k zero := by
  obtain ⟨e, he⟩ := exists_leftMaskFiber_emptyCyclePair_of_cycleProduct_le_two
    ends m j k l zero p c d hcd hcycle
  have hleft : Fintype.card (leftMaskFiber ends m j k l zero p) ≤ 2 :=
    (leftMaskFiber_card_le_cycleProduct ends m j k l zero p).trans hcycle
  rcases eq_or_eq_of_card_le_two c d e hcd hleft with hec | hed
  · subst e
    exact rightMaskCycleTranslate_disconnects_of_first_empty
      ends m j k l zero hloop hjk hkl hk0 p c d hcd he hcycle q
  · subst e
    have h := rightMaskCycleTranslate_disconnects_of_first_empty
      ends m j k l zero hloop hjk hkl hk0 p d c hcd.symm he hcycle q
    rw [rightMaskCycleTranslate_comm m d.1.1 c.1.1 q.1.1] at h
    exact h



theorem exists_rightMaskFiber_pair_of_cycleProduct_le_two
    (ends : I → Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (c d : leftMaskFiber ends m j k l zero p) (hcd : c ≠ d)
    (hcycle : Fintype.card (boundarySector ends p.1 ∅) *
      Fintype.card (boundarySector ends p.2 ∅) ≤ 2) :
    ∃ q r : rightMaskFiber ends m j k l zero p, q ≠ r := by
  let q := Classical.choice
    (rightMaskFiber_nonempty_of_left hloop hjk hkl hk0 p c)
  apply exists_rightMaskFiber_pair_of_cycleTranslate_disconnects
    ends m j k l zero p c d hcd q
  exact rightMaskCycleTranslate_disconnects_of_cycleProduct_le_two
    ends m j k l zero hloop hjk hkl hk0 p c d hcd hcycle q



theorem rowDataRepairHall_of_cycleProduct_le_two
    (ends : I → Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (hcycle : ∀ p : Finset I × Finset I,
      Fintype.card (boundarySector ends p.1 ∅) *
        Fintype.card (boundarySector ends p.2 ∅) ≤ 2) :
    RowDataRepairHall ends m j k l zero := by
  apply rowDataRepairHall_of_cycleProduct_le_two_of_rightPairs
    ends m j k l zero hloop hjk hkl hk0 hcycle
  intro p c d hcd
  exact exists_rightMaskFiber_pair_of_cycleProduct_le_two
    ends m j k l zero hloop hjk hkl hk0 p c d hcd (hcycle p)

end StatMech.GrahamGHS.FourColor

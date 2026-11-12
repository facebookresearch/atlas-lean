/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.Ising.LebowitzPfisterReplicaOrbitRankThree
import Code.Ising.LebowitzPfisterReplicaCutParity










open Finset
open scoped symmDiff

namespace StatMech.Ising

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

local instance lpReplicaRankFourDecidableAdj
    (G : SimpleGraph V) (sites : I -> V) :
    DecidableRel (lpReplicaCurrentGraph G sites).Adj :=
  Classical.decRel _


theorem randomCurrent_sources_singleton_nonempty_of_edgeCopy
    (G : SimpleGraph V) (sites : I -> V)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (c : StatMech.Sharpness.FluxEdgeCopy.Copy
      (lpReplicaCurrentGraph G sites) m) :
    (StatMech.Sharpness.RandomCurrent.sources
      (StatMech.Sharpness.FluxEdgeCopy.endsM
        (lpReplicaCurrentGraph G sites) m) {c}).Nonempty := by
  rcases c with ⟨⟨e, he⟩, k⟩
  induction e using Sym2.inductionOn with
  | _ x y =>
      have hxy : x ≠ y := by
        have hadj : (lpReplicaCurrentGraph G sites).Adj x y := by
          rw [← SimpleGraph.mem_edgeSet]
          exact SimpleGraph.mem_edgeFinset.mp he
        exact hadj.ne
      have hs := randomCurrent_sources_singleton_of_ends_eq
        (StatMech.Sharpness.FluxEdgeCopy.endsM
          (lpReplicaCurrentGraph G sites) m) ⟨⟨s(x, y), he⟩, k⟩
          hxy rfl
      rw [hs]
      exact ⟨x, by simp⟩


theorem lpReplicaOffdiagDecoratedSource_rank_four_all_falseCopies
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites) {i j : I} (hij : i ≠ j)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 4)
    (z : LPReplicaOffdiagDecoratedSource G sites i j q) :
    let d := lpReplicaDecoratedSourceRowGateData G sites i j q z
    lpReplicaCurrentCopies G sites z.1.1.1 d.1 true false = Finset.univ ∧
      ∀ c, d.1 c = (true, false) := by
  dsimp only
  let d := lpReplicaDecoratedSourceRowGateData G sites i j q z
  let E := StatMech.Sharpness.FluxEdgeCopy.endsM
    (lpReplicaCurrentGraph G sites) z.1.1.1
  let K := lpReplicaCurrentCopies G sites z.1.1.1 d.1 true false
  let B :=
    lpMatchingSeamSource
        (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i ∆
      lpMatchingSeamSource
        (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j ∆
      lpMatchingGhostSource
        (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
        lpReplicaCurrentGhost1
  have hcopyCard : Fintype.card
      (StatMech.Sharpness.FluxEdgeCopy.Copy
        (lpReplicaCurrentGraph G sites) z.1.1.1) = 4 := by
    calc
      _ = Fintype.card (LPReplicaOrbitCommonSlot G sites q) :=
        Fintype.card_congr
          (lpReplicaProfileCopyEquivCommonSlot G sites q z.1.1.1
            z.1.1.2 z.2.2)
      _ = 4 := hcard
  have hKsource : StatMech.Sharpness.RandomCurrent.sources E K = B :=
    d.2.2.2.2.1
  have hKlower : 3 ≤ K.card := by
    have hbound := card_randomCurrent_sources_le_two_mul_card E K
    rw [hKsource, card_lpReplica_offdiagSource sites hsite hij] at hbound
    omega
  have hKupper : K.card ≤ 4 := by
    calc
      K.card ≤ Fintype.card
          (StatMech.Sharpness.FluxEdgeCopy.Copy
            (lpReplicaCurrentGraph G sites) z.1.1.1) := Finset.card_le_univ _
      _ = 4 := hcopyCard
  have hfullSource : StatMech.Sharpness.RandomCurrent.sources E Finset.univ =
      B := by
    have h := lpReplicaRowGate_fullSources G sites z.1.1.1 ∅ B d.1 d.2
    calc
      StatMech.Sharpness.RandomCurrent.sources E Finset.univ = ∅ ∆ B := by
        simpa only [E] using h
      _ = B := by
        ext x
        simp [Finset.mem_symmDiff]
  have hKcard : K.card = 4 := by
    by_contra hne
    have hKthree : K.card = 3 := by omega
    have hcompCard : (Finset.univ \ K).card = 1 := by
      rw [Finset.card_sdiff_of_subset (Finset.subset_univ K), Finset.card_univ,
        hcopyCard, hKthree]
    obtain ⟨c, hc⟩ := Finset.card_eq_one.mp hcompCard
    have hcompSource : StatMech.Sharpness.RandomCurrent.sources E
        (Finset.univ \ K) = ∅ := by
      rw [StatMech.GrahamGHS.FourColor.sources_sdiff_of_subset
        (Finset.subset_univ K), hfullSource, hKsource]
      ext x
      simp [Finset.mem_symmDiff]
    rw [hc] at hcompSource
    exact (randomCurrent_sources_singleton_nonempty_of_edgeCopy
      G sites z.1.1.1 c).ne_empty hcompSource
  have hKuniv : K = Finset.univ := by
    apply Finset.eq_of_subset_of_card_le (Finset.subset_univ K)
    rw [Finset.card_univ, hcopyCard, hKcard]
  refine ⟨hKuniv, ?_⟩
  intro c
  have hc : c ∈ K := by rw [hKuniv]; simp
  simpa only [K, lpReplicaCurrentCopies, Finset.mem_filter,
    Finset.mem_univ, true_and] using hc


theorem lpReplicaOffdiagDecoratedSource_rank_four_rowMask_eq_univ
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites) {i j : I} (hij : i ≠ j)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 4)
    (z : LPReplicaOffdiagDecoratedSource G sites i j q) :
    lpReplicaOrbitFourColorSlotRowMask G sites q
        (lpReplicaOffdiagDecoratedSourceSlotState G sites i j q z) =
      Finset.univ := by
  classical
  let d := lpReplicaDecoratedSourceRowGateData G sites i j q z
  have hall := lpReplicaOffdiagDecoratedSource_rank_four_all_falseCopies
    G sites hsite hij q hcard z
  dsimp only at hall
  ext x
  simp only [lpReplicaOrbitFourColorSlotRowMask, Finset.mem_filter,
    Finset.mem_univ, true_and]
  let c := (lpReplicaProfileCopyEquivCommonSlot G sites q z.1.1.1
    z.1.1.2 z.2.2).symm x
  have hc : d.1 c = (true, false) := hall.2 c
  have hc' :
      lpReplicaOrientedFourColorTag G sites ∅
          (lpMatchingSeamSource
              (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i ∆
            lpMatchingSeamSource
              (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j ∆
            lpMatchingGhostSource
              (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
              lpReplicaCurrentGhost1) q
          (lpReplicaDecoratedOrbitAtomEquivOrientedFourColor G sites ∅
            (lpMatchingSeamSource
                (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i ∆
              lpMatchingSeamSource
                (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j ∆
              lpMatchingGhostSource
                (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
                lpReplicaCurrentGhost1) q z) c =
        (true, false) := by
    simpa only [d, lpReplicaDecoratedSourceRowGateData,
      lpReplicaOrientedFourColorTag,
      lpReplicaDecoratedOrbitAtomEquivOrientedFourColor] using hc
  simpa only [lpReplicaOffdiagDecoratedSourceSlotState,
    lpReplicaOrientedFourColorSlotState,
    lpReplicaOrbitFourColorSlotStateOfTag, Equiv.apply_symm_apply,
    Equiv.symm_apply_apply, iff_true] using congrArg Prod.fst hc'


theorem lpReplicaOffdiagDecoratedSourceCrossTraceFiber_rank_four_card_le_one
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites) {i j : I} (hij : i ≠ j)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 4)
    (u : LPReplicaOrbitFourColorSlotState G sites q) :
    (lpReplicaOffdiagDecoratedSourceCrossTraceFiber
      G sites i j q u).card ≤ 1 := by
  classical
  rw [Finset.card_le_one]
  intro z hz w hw
  apply lpReplicaOffdiagDecoratedSourceSlotState_injective G sites i j q
  rw [lpReplicaOrbitFourColorSlotState_eq_iff_crossNormalize_eq_and_rowMask_eq]
  refine ⟨(Finset.mem_filter.mp hz).2.trans
    (Finset.mem_filter.mp hw).2.symm, ?_⟩
  exact (lpReplicaOffdiagDecoratedSource_rank_four_rowMask_eq_univ
    G sites hsite hij q hcard z).trans
      (lpReplicaOffdiagDecoratedSource_rank_four_rowMask_eq_univ
        G sites hsite hij q hcard w).symm



theorem lpReplicaOffdiagDecoratedSource_rank_four_swapped_all_false
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites) {i j : I} (hij : i ≠ j)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 4)
    (z : LPReplicaOffdiagDecoratedSource G sites i j q) :
    let d := lpReplicaDecoratedSourceSwappedRowGateData G sites i j q z
    ∀ c, d.1 c = (false, false) := by
  dsimp only
  intro c
  have hall := (lpReplicaOffdiagDecoratedSource_rank_four_all_falseCopies
    G sites hsite hij q hcard z).2 c
  simpa only [lpReplicaDecoratedSourceSwappedRowGateData,
    lpReplicaSwapRowsTag, hall, Bool.not_true]



theorem lpReplicaOffdiagDecoratedSource_rank_four_orientedTag
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites) {i j : I} (hij : i ≠ j)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 4)
    (z : LPReplicaOffdiagDecoratedSource G sites i j q) :
    let B :=
      lpMatchingSeamSource
          (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i ∆
        lpMatchingSeamSource
          (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j ∆
        lpMatchingGhostSource
          (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
          lpReplicaCurrentGhost1
    let oz := lpReplicaDecoratedOrbitAtomEquivOrientedFourColor
      G sites ∅ B q z
    ∀ c, lpReplicaOrientedFourColorTag G sites ∅ B q oz c =
      (true, false) := by
  dsimp only
  intro c
  let d := lpReplicaDecoratedSourceRowGateData G sites i j q z
  have hc := (lpReplicaOffdiagDecoratedSource_rank_four_all_falseCopies
    G sites hsite hij q hcard z).2 c
  simpa only [d, lpReplicaDecoratedSourceRowGateData,
    lpReplicaOrientedFourColorTag,
    lpReplicaDecoratedOrbitAtomEquivOrientedFourColor] using hc



theorem sum_randomCurrent_degK_le_two_mul_card
    {E W : Type*} [Fintype E] [DecidableEq E]
    [Fintype W] [DecidableEq W]
    (ends : E -> Sym2 W) (K : Finset E) (S : Finset W) :
    (∑ x ∈ S, StatMech.Sharpness.RandomCurrent.degK ends K x) ≤
      2 * K.card := by
  classical
  unfold StatMech.Sharpness.RandomCurrent.degK
  simp only [Finset.card_filter]
  rw [Finset.sum_comm]
  calc
    (∑ e ∈ K, ∑ x ∈ S, if x ∈ ends e then 1 else 0) =
        ∑ e ∈ K, (S.filter fun x => x ∈ ends e).card := by
      apply Finset.sum_congr rfl
      intro e _
      rw [Finset.card_filter]
    _ ≤ ∑ _e ∈ K, 2 := by
      apply Finset.sum_le_sum
      intro e _
      calc
        (S.filter fun x => x ∈ ends e).card ≤ (ends e).toFinset.card := by
          apply Finset.card_le_card
          intro x hx
          exact Sym2.mem_toFinset.mpr (Finset.mem_filter.mp hx).2
        _ ≤ 2 := by
          rw [Sym2.card_toFinset]
          split <;> omega
    _ = 2 * K.card := by simp [Nat.mul_comm]




theorem lpReplicaOffdiagDecoratedSource_rank_four_exists_seamCopy
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites) {i j : I} (hij : i ≠ j)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 4)
    (z : LPReplicaOffdiagDecoratedSource G sites i j q) :
    (∃ c : StatMech.Sharpness.FluxEdgeCopy.Copy
        (lpReplicaCurrentGraph G sites) z.1.1.1,
      c.1.1 = lpReplicaCurrentSeamEdge sites i) ∨
    ∃ c : StatMech.Sharpness.FluxEdgeCopy.Copy
        (lpReplicaCurrentGraph G sites) z.1.1.1,
      c.1.1 = lpReplicaCurrentSeamEdge sites j := by
  classical
  let H := lpReplicaCurrentGraph G sites
  let m := z.1.1.1
  let E := StatMech.Sharpness.FluxEdgeCopy.endsM H m
  let K : Finset (StatMech.Sharpness.FluxEdgeCopy.Copy H m) := Finset.univ
  let B :=
    lpMatchingSeamSource
        (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i ∆
      lpMatchingSeamSource
        (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j ∆
      lpMatchingGhostSource
        (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
        lpReplicaCurrentGhost1
  let d := lpReplicaDecoratedSourceRowGateData G sites i j q z
  have hall := lpReplicaOffdiagDecoratedSource_rank_four_all_falseCopies
    G sites hsite hij q hcard z
  dsimp only at hall
  have hsrc : StatMech.Sharpness.RandomCurrent.sources E K = B := by
    change StatMech.Sharpness.RandomCurrent.sources
      (StatMech.Sharpness.FluxEdgeCopy.endsM
        (lpReplicaCurrentGraph G sites) z.1.1.1) Finset.univ = B
    rw [← hall.1]
    exact d.2.2.2.2.1
  have hcurrentSrc : StatMech.Sharpness.sources H
      (StatMech.Sharpness.ofEdgeFun H m) = B := by
    calc
      _ = StatMech.Sharpness.RandomCurrent.sources E K := by
        change StatMech.Sharpness.sources H
            (StatMech.Sharpness.ofEdgeFun H m) =
          StatMech.Sharpness.RandomCurrent.sources
            (StatMech.Sharpness.FluxEdgeCopy.endsM H m) Finset.univ
        rw [StatMech.Sharpness.FluxEdgeCopy.sources_eq,
          StatMech.Sharpness.FluxEdgeCopy.profileFlux_univ]
      _ = B := hsrc
  have hodd : Odd (#(StatMech.Sharpness.sources H
      (StatMech.Sharpness.ofEdgeFun H m) ∩ lpReplicaCurrentLeftSide)) := by
    rw [hcurrentSrc]
    exact lpReplica_offdiagSource_left_odd sites hsite hij
  obtain ⟨u, hu, v, hv, huv⟩ :=
    lpReplicaCurrent_exists_crossConnection_of_odd_sources G sites m hodd
  obtain ⟨w⟩ := huv
  obtain ⟨r, _, _, hrout, hrin, hradj, _⟩ :=
    StatMech.Sharpness.walk_firstExit w lpReplicaCurrentLeftSide hu hv
  obtain ⟨k, hkedge⟩ := lpReplicaCurrent_crossingEdge_eq_seam
    G sites hrin hrout hradj.1
  have hseamMem : lpReplicaCurrentSeamEdge sites k ∈
      (lpReplicaCurrentGraph G sites).edgeFinset := by
    rw [SimpleGraph.mem_edgeFinset]
    unfold lpReplicaCurrentSeamEdge
    rw [SimpleGraph.mem_edgeSet]
    unfold lpReplicaCurrentLeft lpReplicaCurrentRight
    rw [lpReplicaCurrentGraph_adj_left_right_iff]
    exact ⟨k, rfl, rfl⟩
  let ek : (lpReplicaCurrentGraph G sites).edgeFinset :=
    ⟨lpReplicaCurrentSeamEdge sites k, hseamMem⟩
  have hkpos : 1 ≤ z.1.1.1 ek := by
    have hpos : 1 ≤ StatMech.Sharpness.ofEdgeFun
      (lpReplicaCurrentGraph G sites) z.1.1.1
      (lpReplicaCurrentSeamEdge sites k) := by
      rw [← hkedge]
      exact hradj.2
    unfold StatMech.Sharpness.ofEdgeFun at hpos
    rw [dif_pos hseamMem] at hpos
    simpa only [ek] using hpos
  let c : StatMech.Sharpness.FluxEdgeCopy.Copy
      (lpReplicaCurrentGraph G sites) z.1.1.1 :=
    ⟨ek, ⟨0, hkpos⟩⟩
  have hki_or_hkj : k = i ∨ k = j := by
    by_contra hk
    push_neg at hk
    have hki : k ≠ i := hk.1
    have hkj : k ≠ j := hk.2
    have hsij : sites i ≠ sites j := hsite.ne hij
    have hsji : sites j ≠ sites i := hsij.symm
    have hski : sites k ≠ sites i := hsite.ne hki
    have hskj : sites k ≠ sites j := hsite.ne hkj
    have hsik : sites i ≠ sites k := hski.symm
    have hsjk : sites j ≠ sites k := hskj.symm
    let g0 : LPReplicaCurrentVertex V := lpReplicaCurrentGhost0
    let g1 : LPReplicaCurrentVertex V := lpReplicaCurrentGhost1
    let li := lpReplicaCurrentLeft sites i
    let ri := lpReplicaCurrentRight sites i
    let lj := lpReplicaCurrentLeft sites j
    let rj := lpReplicaCurrentRight sites j
    let lk := lpReplicaCurrentLeft sites k
    let rk := lpReplicaCurrentRight sites k
    let S : Finset (LPReplicaCurrentVertex V) :=
      {g0, g1, li, ri, lj, rj, lk, rk}
    have hsix (x : LPReplicaCurrentVertex V) (hx : x ∈ B) :
        1 ≤ StatMech.Sharpness.RandomCurrent.degK E K x := by
      have hxsrc : x ∈ StatMech.Sharpness.RandomCurrent.sources E K := by
        rw [hsrc]
        exact hx
      rw [StatMech.Sharpness.RandomCurrent.mem_sources] at hxsrc
      rcases hxsrc with ⟨a, ha⟩
      omega
    have hg0 : 1 ≤ StatMech.Sharpness.RandomCurrent.degK E K g0 :=
      hsix g0 (by simp [B, g0, lpMatchingSeamSource,
        lpMatchingGhostSource, lpReplicaCurrentLeft,
        lpReplicaCurrentRight, lpReplicaCurrentGhost0,
        lpReplicaCurrentGhost1, Finset.mem_symmDiff])
    have hg1 : 1 ≤ StatMech.Sharpness.RandomCurrent.degK E K g1 :=
      hsix g1 (by simp [B, g1, lpMatchingSeamSource,
        lpMatchingGhostSource, lpReplicaCurrentLeft,
        lpReplicaCurrentRight, lpReplicaCurrentGhost0,
        lpReplicaCurrentGhost1, Finset.mem_symmDiff])
    have hli : 1 ≤ StatMech.Sharpness.RandomCurrent.degK E K li :=
      hsix li (by simp [B, li, lpMatchingSeamSource,
        lpMatchingGhostSource, lpReplicaCurrentLeft,
        lpReplicaCurrentRight, lpReplicaCurrentGhost0,
        lpReplicaCurrentGhost1, Finset.mem_symmDiff, hsij, hsji])
    have hri : 1 ≤ StatMech.Sharpness.RandomCurrent.degK E K ri :=
      hsix ri (by simp [B, ri, lpMatchingSeamSource,
        lpMatchingGhostSource, lpReplicaCurrentLeft,
        lpReplicaCurrentRight, lpReplicaCurrentGhost0,
        lpReplicaCurrentGhost1, Finset.mem_symmDiff, hsij, hsji])
    have hlj : 1 ≤ StatMech.Sharpness.RandomCurrent.degK E K lj :=
      hsix lj (by simp [B, lj, lpMatchingSeamSource,
        lpMatchingGhostSource, lpReplicaCurrentLeft,
        lpReplicaCurrentRight, lpReplicaCurrentGhost0,
        lpReplicaCurrentGhost1, Finset.mem_symmDiff, hsij, hsji])
    have hrj : 1 ≤ StatMech.Sharpness.RandomCurrent.degK E K rj :=
      hsix rj (by simp [B, rj, lpMatchingSeamSource,
        lpMatchingGhostSource, lpReplicaCurrentLeft,
        lpReplicaCurrentRight, lpReplicaCurrentGhost0,
        lpReplicaCurrentGhost1, Finset.mem_symmDiff, hsij, hsji])
    have hlkNot : lk ∉ B := by
      simp [B, lk, lpMatchingSeamSource, lpMatchingGhostSource,
        lpReplicaCurrentLeft, lpReplicaCurrentRight,
        lpReplicaCurrentGhost0, lpReplicaCurrentGhost1,
        Finset.mem_symmDiff, hski, hskj, hsik, hsjk]
    have hrkNot : rk ∉ B := by
      simp [B, rk, lpMatchingSeamSource, lpMatchingGhostSource,
        lpReplicaCurrentLeft, lpReplicaCurrentRight,
        lpReplicaCurrentGhost0, lpReplicaCurrentGhost1,
        Finset.mem_symmDiff, hski, hskj, hsik, hsjk]
    have hlkEven : Even (StatMech.Sharpness.RandomCurrent.degK E K lk) := by
      rcases Nat.even_or_odd
          (StatMech.Sharpness.RandomCurrent.degK E K lk) with he | ho
      · exact he
      · exact False.elim (hlkNot (by
          rw [← hsrc, StatMech.Sharpness.RandomCurrent.mem_sources]
          exact ho))
    have hrkEven : Even (StatMech.Sharpness.RandomCurrent.degK E K rk) := by
      rcases Nat.even_or_odd
          (StatMech.Sharpness.RandomCurrent.degK E K rk) with he | ho
      · exact he
      · exact False.elim (hrkNot (by
          rw [← hsrc, StatMech.Sharpness.RandomCurrent.mem_sources]
          exact ho))
    have hcK : c ∈ K := Finset.mem_univ c
    have hlkc : lk ∈ E c := by
      simp [E, c, ek, lk, StatMech.Sharpness.FluxEdgeCopy.endsM,
        lpReplicaCurrentSeamEdge, lpReplicaCurrentLeft,
        lpReplicaCurrentRight]
    have hrkc : rk ∈ E c := by
      simp [E, c, ek, rk, StatMech.Sharpness.FluxEdgeCopy.endsM,
        lpReplicaCurrentSeamEdge, lpReplicaCurrentLeft,
        lpReplicaCurrentRight]
    have hlkPos : 1 ≤ StatMech.Sharpness.RandomCurrent.degK E K lk := by
      unfold StatMech.Sharpness.RandomCurrent.degK
      rw [Finset.one_le_card]
      exact ⟨c, Finset.mem_filter.mpr ⟨hcK, hlkc⟩⟩
    have hrkPos : 1 ≤ StatMech.Sharpness.RandomCurrent.degK E K rk := by
      unfold StatMech.Sharpness.RandomCurrent.degK
      rw [Finset.one_le_card]
      exact ⟨c, Finset.mem_filter.mpr ⟨hcK, hrkc⟩⟩
    have hlk : 2 ≤ StatMech.Sharpness.RandomCurrent.degK E K lk := by
      rcases hlkEven with ⟨a, ha⟩
      omega
    have hrk : 2 ≤ StatMech.Sharpness.RandomCurrent.degK E K rk := by
      rcases hrkEven with ⟨a, ha⟩
      omega
    have hdistinct :
        g0 ∉ ({g1, li, ri, lj, rj, lk, rk} :
          Finset (LPReplicaCurrentVertex V)) ∧
        g1 ∉ ({li, ri, lj, rj, lk, rk} :
          Finset (LPReplicaCurrentVertex V)) ∧
        li ∉ ({ri, lj, rj, lk, rk} :
          Finset (LPReplicaCurrentVertex V)) ∧
        ri ∉ ({lj, rj, lk, rk} :
          Finset (LPReplicaCurrentVertex V)) ∧
        lj ∉ ({rj, lk, rk} : Finset (LPReplicaCurrentVertex V)) ∧
        rj ∉ ({lk, rk} : Finset (LPReplicaCurrentVertex V)) ∧
        lk ∉ ({rk} : Finset (LPReplicaCurrentVertex V)) := by
      simp [g0, g1, li, ri, lj, rj, lk, rk,
        lpReplicaCurrentLeft, lpReplicaCurrentRight,
        lpReplicaCurrentGhost0, lpReplicaCurrentGhost1,
        hsij, hsji, hski, hskj, hsik, hsjk]
    have hlower : 10 ≤ ∑ x ∈ S,
        StatMech.Sharpness.RandomCurrent.degK E K x := by
      rcases hdistinct with ⟨h0, h1, h2, h3, h4, h5, h6⟩
      simp only [S]
      rw [Finset.sum_insert h0, Finset.sum_insert h1,
        Finset.sum_insert h2, Finset.sum_insert h3,
        Finset.sum_insert h4, Finset.sum_insert h5,
        Finset.sum_insert h6, Finset.sum_singleton]
      omega
    have hupper := sum_randomCurrent_degK_le_two_mul_card E K S
    have hcopyCard : K.card = 4 := by
      change (Finset.univ : Finset
        (StatMech.Sharpness.FluxEdgeCopy.Copy H m)).card = 4
      rw [Finset.card_univ]
      calc
        Fintype.card (StatMech.Sharpness.FluxEdgeCopy.Copy H m) =
            Fintype.card (LPReplicaOrbitCommonSlot G sites q) :=
          Fintype.card_congr
            (lpReplicaProfileCopyEquivCommonSlot G sites q m
              z.1.1.2 z.2.2)
        _ = 4 := hcard
    rw [hcopyCard] at hupper
    omega
  rcases hki_or_hkj with rfl | rfl
  · exact Or.inl ⟨c, rfl⟩
  · exact Or.inr ⟨c, rfl⟩

set_option maxHeartbeats 800000 in



theorem lpReplicaOrientedFourColorAtom_rank_four_all_falseCurrent
    (G : SimpleGraph V) (sites : I -> V)
    (A B : Finset (LPReplicaCurrentVertex V))
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 4)
    (hA : A.card = 2)
    (hB : (B.map lpReplicaCurrentReflect.toEmbedding).card = 4)
    (z : LPReplicaOrientedFourColorAtom G sites A B q) :
    ∀ c, (lpReplicaOrientedFourColorTag G sites A B q z c).2 = false := by
  classical
  let m := z.1.1
  let tag := lpReplicaOrientedFourColorTag G sites A B q z
  let E := StatMech.Sharpness.FluxEdgeCopy.endsM
    (lpReplicaCurrentGraph G sites) m
  let K0 := lpReplicaCurrentCopies G sites m tag false false
  let K1 := lpReplicaCurrentCopies G sites m tag true false
  let U := lpReplicaCurrentCopies G sites m tag false true ∪
    lpReplicaCurrentCopies G sites m tag true true
  have hgate : LPReplicaRowGate G sites m A
      (B.map lpReplicaCurrentReflect.toEmbedding) tag :=
    (lpReplicaRowGate_iff_leftPattern_tagFourColor G sites m A
      (B.map lpReplicaCurrentReflect.toEmbedding) tag).mpr
      (lpReplicaOrientedFourColorTag_leftPattern G sites A B q z)
  have hcopyCard : Fintype.card
      (StatMech.Sharpness.FluxEdgeCopy.Copy
        (lpReplicaCurrentGraph G sites) m) = 4 := by
    calc
      _ = Fintype.card (LPReplicaOrbitCommonSlot G sites q) :=
        Fintype.card_congr
          (lpReplicaProfileCopyEquivCommonSlot G sites q m z.1.2
            z.2.2.1.2)
      _ = 4 := hcard
  have hK0source : StatMech.Sharpness.RandomCurrent.sources E K0 = A :=
    hgate.1
  have hK1source : StatMech.Sharpness.RandomCurrent.sources E K1 =
      B.map lpReplicaCurrentReflect.toEmbedding := hgate.2.2.2.1
  have hK0lower : 1 ≤ K0.card := by
    have hbound := card_randomCurrent_sources_le_two_mul_card E K0
    rw [hK0source, hA] at hbound
    omega
  have hK1lower : 2 ≤ K1.card := by
    have hbound := card_randomCurrent_sources_le_two_mul_card E K1
    rw [hK1source, hB] at hbound
    omega
  have hfalseDisj : Disjoint K0 K1 := by
    rw [Finset.disjoint_left]
    intro c hc0 hc1
    simp only [K0, K1, lpReplicaCurrentCopies, Finset.mem_filter,
      Finset.mem_univ, true_and] at hc0 hc1
    exact Bool.false_ne_true
      ((congrArg Prod.fst hc0).symm.trans (congrArg Prod.fst hc1))
  have hfalseLower : 3 ≤ (K0 ∪ K1).card := by
    rw [Finset.card_union_of_disjoint hfalseDisj]
    omega
  have hUeq : U = Finset.univ \ (K0 ∪ K1) := by
    ext c
    rcases htag : tag c with ⟨r, b⟩
    cases r <;> cases b <;>
      simp [U, K0, K1, lpReplicaCurrentCopies, htag]
  have hUcard : U.card ≤ 1 := by
    rw [hUeq, Finset.card_sdiff_of_subset (Finset.subset_univ _),
      Finset.card_univ, hcopyCard]
    omega
  have hUsource : StatMech.Sharpness.RandomCurrent.sources E U = ∅ := by
    have hdisj : Disjoint
        (lpReplicaCurrentCopies G sites m tag false true)
        (lpReplicaCurrentCopies G sites m tag true true) := by
      rw [Finset.disjoint_left]
      intro c hc0 hc1
      simp only [lpReplicaCurrentCopies, Finset.mem_filter,
        Finset.mem_univ, true_and] at hc0 hc1
      exact Bool.false_ne_true
        ((congrArg Prod.fst hc0).symm.trans (congrArg Prod.fst hc1))
    change StatMech.Sharpness.RandomCurrent.sources E
      (lpReplicaCurrentCopies G sites m tag false true ∪
        lpReplicaCurrentCopies G sites m tag true true) = ∅
    rw [StatMech.GrahamGHS.FourColor.sources_union_of_disjoint hdisj,
      hgate.2.1, hgate.2.2.2.2.1]
    simp
  intro c
  by_contra hc
  have hcTrue : (tag c).2 = true := by
    cases h : (tag c).2
    · exact False.elim (hc h)
    · rfl
  have hcU : c ∈ U := by
    simp only [U, Finset.mem_union, lpReplicaCurrentCopies,
      Finset.mem_filter, Finset.mem_univ, true_and]
    rcases htag : tag c with ⟨r, b⟩
    cases r <;> cases b <;> simp_all
  have hUnonempty : U.Nonempty := ⟨c, hcU⟩
  have hUone : U.card = 1 := by
    have hpos := hUnonempty.card_pos
    omega
  obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hUone
  rw [ha] at hUsource
  exact (randomCurrent_sources_singleton_nonempty_of_edgeCopy
    G sites m a).ne_empty hUsource



theorem lpReplicaBalancedSelector_rank_four_slotState
    (G : SimpleGraph V) (sites : I -> V)
    (Si Sj T : Finset (LPReplicaCurrentVertex V))
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 4)
    (s : LPReplicaBalancedSelector G sites
      (Si ∆ Sj ∆ T) (Sj ∆ T) q)
    (c : StatMech.Sharpness.FluxEdgeCopy.Copy
      (lpReplicaCurrentGraph G sites) s.profile)
    (sourceTag : StatMech.Sharpness.FluxEdgeCopy.Copy
      (lpReplicaCurrentGraph G sites) s.profile -> LPReplicaRowTag)
    (hbase : ∀ a, s.tag a = (false, false))
    (hsource : ∀ a, sourceTag a = (true, false))
    (hselector : s.selector = Finset.univ \ {c})
    (hfixed : c.1 ∈ lpReplicaCurrentEdgeOrbitFixed G sites)
    (hSiCard : Si.card = 2)
    (hDCard : (Sj ∆ T).card = 4) :
    lpReplicaOrientedFourColorSlotState G sites Si
        ((Sj ∆ T).map lpReplicaCurrentReflect.toEmbedding) q
        (lpReplicaDecoratedOrbitAtomEquivOrientedFourColor G sites Si
          ((Sj ∆ T).map lpReplicaCurrentReflect.toEmbedding) q
          (lpReplicaDecoratedOrbitAtomOfBalancedSelector
            G sites Si Sj T q s)) =
      lpReplicaOrbitFourColorSlotCrossToggle G sites q
        (lpReplicaOrbitCommonSlotsOfCopies G sites q s.profile s.orbit
          s.orbitLabel {c})
        (lpReplicaOrbitFourColorSlotStateOfTag G sites q s.profile s.orbit
          s.orbitLabel sourceTag) := by
  classical
  let moved := lpReplicaToggleRows G sites s.profile s.selector s.tag
  let atom := lpReplicaDecoratedOrbitAtomOfBalancedSelector
    G sites Si Sj T q s
  let oz := lpReplicaDecoratedOrbitAtomEquivOrientedFourColor G sites Si
    ((Sj ∆ T).map lpReplicaCurrentReflect.toEmbedding) q atom
  let targetTag := lpReplicaOrientedFourColorTag G sites Si
    ((Sj ∆ T).map lpReplicaCurrentReflect.toEmbedding) q oz
  have htargetFalse : ∀ a, (targetTag a).2 = false := by
    apply lpReplicaOrientedFourColorAtom_rank_four_all_falseCurrent
      G sites Si ((Sj ∆ T).map lpReplicaCurrentReflect.toEmbedding)
      q hcard hSiCard
    simpa only [Finset.card_map] using hDCard
  have htargetRows : lpReplicaRowCopies G sites s.profile targetTag false =
      lpReplicaRowCopies G sites s.profile moved false := by
    dsimp only [targetTag, oz, atom, moved,
      lpReplicaOrientedFourColorTag,
      lpReplicaDecoratedOrbitAtomEquivOrientedFourColor,
      lpReplicaDecoratedOrbitAtomOfBalancedSelector]
    apply lpReplicaOrbitCollisionSplitTag_rowCopies_false
  have hbaseRows : lpReplicaRowCopies G sites s.profile s.tag false =
      Finset.univ := by
    ext a
    simp [lpReplicaRowCopies, hbase]
  have hmovedRows : lpReplicaRowCopies G sites s.profile moved false = {c} := by
    calc
      _ = lpReplicaRowCopies G sites s.profile s.tag false ∆ s.selector :=
        lpReplicaRowCopies_toggle G sites s.profile s.selector s.tag false
      _ = Finset.univ ∆ (Finset.univ \ {c}) := by
        rw [hbaseRows, hselector]
      _ = {c} := by
        ext a
        simp [Finset.mem_symmDiff]
  have htargetRows' : lpReplicaRowCopies G sites s.profile targetTag false =
      {c} := htargetRows.trans hmovedRows
  have htag : targetTag =
      lpReplicaToggleRows G sites s.profile {c} sourceTag := by
    funext a
    have hrow := Finset.ext_iff.mp htargetRows' a
    simp only [lpReplicaRowCopies, Finset.mem_filter, Finset.mem_univ,
      true_and, Finset.mem_singleton] at hrow
    by_cases hac : a = c
    · subst a
      apply Prod.ext
      · simp only [lpReplicaToggleRows, Finset.mem_singleton, if_pos]
        rw [hsource c]
        exact hrow.mpr rfl
      · simp only [lpReplicaToggleRows, Finset.mem_singleton, if_pos]
        rw [hsource c]
        exact htargetFalse c
    · apply Prod.ext
      · have hnfalse : (targetTag a).1 ≠ false := by
          intro ha
          exact hac (hrow.mp ha)
        have hnotmem : a ∉ ({c} : Finset _) := by
          intro ha
          exact hac (Finset.mem_singleton.mp ha)
        have htoggle : lpReplicaToggleRows G sites s.profile {c} sourceTag a =
            sourceTag a := by
          unfold lpReplicaToggleRows
          exact if_neg hnotmem
        cases hfirst : (targetTag a).1
        · exact (hnfalse hfirst).elim
        · rw [htoggle, hsource a]
      · have hnotmem : a ∉ ({c} : Finset _) := by
          intro ha
          exact hac (Finset.mem_singleton.mp ha)
        have htoggle : lpReplicaToggleRows G sites s.profile {c} sourceTag a =
            sourceTag a := by
          unfold lpReplicaToggleRows
          exact if_neg hnotmem
        rw [htoggle, hsource a]
        exact htargetFalse a
  change lpReplicaOrbitFourColorSlotStateOfTag G sites q s.profile s.orbit
      s.orbitLabel targetTag = _
  rw [lpReplicaOrbitFourColorSlotCrossToggle,
    lpReplicaOrbitFourColorSlotReflect_singletonCopy_of_fixed
      G sites q s.profile s.orbit s.orbitLabel c hfixed,
    lpReplicaOrbitFourColorSlotRowToggle_stateOfTag, htag]

set_option maxHeartbeats 1000000 in


theorem lpReplicaOffdiagDecoratedSource_rank_four_exists_balancedSelector
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites) {i j : I} (hij : i ≠ j)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 4)
    (z : LPReplicaOffdiagDecoratedSource G sites i j q) :
    let Si := lpMatchingSeamSource
      (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i
    let Sj := lpMatchingSeamSource
      (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j
    let T := lpMatchingGhostSource
      (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
      lpReplicaCurrentGhost1
    (∃ s : LPReplicaBalancedSelector G sites
        (Si ∆ Sj ∆ T) (Sj ∆ T) q,
      ∃ c : StatMech.Sharpness.FluxEdgeCopy.Copy
          (lpReplicaCurrentGraph G sites) z.1.1.1,
        s.profile = z.1.1.1 ∧ HEq s.orbitLabel z.2.2 ∧
          c.1.1 = s(lpReplicaCurrentLeft sites i,
            lpReplicaCurrentRight sites i) ∧
          HEq s.selector (Finset.univ \ {c}) ∧
          (∀ a, s.tag a = (false, false)) ∧
          (lpReplicaOffdiagDecoratedTargetBranchedSlotState G sites i j q
              (Sum.inl (lpReplicaDecoratedOrbitAtomOfBalancedSelector_left
                G sites i j q s))).2 =
            lpReplicaOrbitFourColorSlotCrossToggle G sites q
              (lpReplicaOrbitCommonSlotsOfCopies G sites q z.1.1.1
                z.1.1.2 z.2.2 {c})
              (lpReplicaOffdiagDecoratedSourceSlotState
                G sites i j q z)) ∨
      (∃ s : LPReplicaBalancedSelector G sites
        (Sj ∆ Si ∆ T) (Si ∆ T) q,
      ∃ c : StatMech.Sharpness.FluxEdgeCopy.Copy
          (lpReplicaCurrentGraph G sites) z.1.1.1,
        s.profile = z.1.1.1 ∧ HEq s.orbitLabel z.2.2 ∧
          c.1.1 = s(lpReplicaCurrentLeft sites j,
            lpReplicaCurrentRight sites j) ∧
          HEq s.selector (Finset.univ \ {c}) ∧
          (∀ a, s.tag a = (false, false)) ∧
          (lpReplicaOffdiagDecoratedTargetBranchedSlotState G sites i j q
              (Sum.inr (lpReplicaDecoratedOrbitAtomOfBalancedSelector_left
                G sites j i q s))).2 =
            lpReplicaOrbitFourColorSlotCrossToggle G sites q
              (lpReplicaOrbitCommonSlotsOfCopies G sites q z.1.1.1
                z.1.1.2 z.2.2 {c})
              (lpReplicaOffdiagDecoratedSourceSlotState
                G sites i j q z)) := by
  classical
  dsimp only
  let Si := lpMatchingSeamSource
    (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i
  let Sj := lpMatchingSeamSource
    (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j
  let T := lpMatchingGhostSource
    (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
    lpReplicaCurrentGhost1
  let B := Si ∆ Sj ∆ T
  let m := z.1.1.1
  let E := StatMech.Sharpness.FluxEdgeCopy.endsM
    (lpReplicaCurrentGraph G sites) m
  let d := lpReplicaDecoratedSourceSwappedRowGateData G sites i j q z
  have hdall : ∀ c, d.1 c = (false, false) :=
    lpReplicaOffdiagDecoratedSource_rank_four_swapped_all_false
      G sites hsite hij q hcard z
  have hrow0 : lpReplicaRowCopies G sites m d.1 false = Finset.univ := by
    ext c
    simp [lpReplicaRowCopies, hdall]
  have hrow1 : lpReplicaRowCopies G sites m d.1 true = ∅ := by
    ext c
    simp [lpReplicaRowCopies, hdall]
  have htotal : StatMech.Sharpness.RandomCurrent.sources E Finset.univ = B := by
    have h := lpReplicaRowGate_fullSources G sites m B ∅ d.1 d.2
    calc
      StatMech.Sharpness.RandomCurrent.sources E Finset.univ = B ∆ ∅ := by
        simpa only [E] using h
      _ = B := by
        ext x
        simp [Finset.mem_symmDiff]
  have hBswap : B = Sj ∆ Si ∆ T := by
    change Si ∆ Sj ∆ T = Sj ∆ Si ∆ T
    rw [symmDiff_comm Si Sj]
  rcases lpReplicaOffdiagDecoratedSource_rank_four_exists_seamCopy
      G sites hsite hij q hcard z with ⟨c, hc⟩ | ⟨c, hc⟩
  · let P : Finset (StatMech.Sharpness.FluxEdgeCopy.Copy
        (lpReplicaCurrentGraph G sites) m) := Finset.univ \ {c}
    have hfalseFilter : P.filter (fun a => (d.1 a).2 = false) = P := by
      ext a
      simp [P, hdall]
    have htrueFilter : P.filter (fun a => (d.1 a).2 = true) = ∅ := by
      ext a
      simp [P, hdall]
    have hcends : E c = s(lpReplicaCurrentLeft sites i,
        lpReplicaCurrentRight sites i) := by
      simpa only [E, m, StatMech.Sharpness.FluxEdgeCopy.endsM] using hc
    have hsingle : StatMech.Sharpness.RandomCurrent.sources E {c} = Si := by
      simpa only [Si, lpMatchingSeamSource] using
        (randomCurrent_sources_singleton_of_ends_eq E c (by
          simp [lpReplicaCurrentLeft, lpReplicaCurrentRight]) hcends)
    have hfalseSource : StatMech.Sharpness.RandomCurrent.sources E
        (P.filter fun a => (d.1 a).2 = false) = Sj ∆ T := by
      rw [hfalseFilter]
      calc
        StatMech.Sharpness.RandomCurrent.sources E P =
            StatMech.Sharpness.RandomCurrent.sources E Finset.univ ∆
              StatMech.Sharpness.RandomCurrent.sources E {c} := by
          exact StatMech.GrahamGHS.FourColor.sources_sdiff_of_subset (by simp [P])
        _ = B ∆ Si := by rw [htotal, hsingle]
        _ = Sj ∆ T := by
          change (Si ∆ Sj ∆ T) ∆ Si = Sj ∆ T
          rw [symmDiff_assoc Si Sj T,
            symmDiff_symmDiff_self']
    have htrueSource : StatMech.Sharpness.RandomCurrent.sources E
        (P.filter fun a => (d.1 a).2 = true) = ∅ := by
      rw [htrueFilter]
      simp [StatMech.Sharpness.RandomCurrent.sources,
        StatMech.Sharpness.RandomCurrent.degK]
    have hrow0Disconn : ¬ StatMech.Sharpness.RandomCurrent.connK E
        (lpReplicaRowCopies G sites m
          (lpReplicaToggleRows G sites m P d.1) false)
        lpReplicaCurrentGhost0 lpReplicaCurrentGhost1 := by
      have hsub : lpReplicaRowCopies G sites m
          (lpReplicaToggleRows G sites m P d.1) false ⊆
          lpReplicaRowCopies G sites m d.1 false := by
        rw [lpReplicaRowCopies_toggle, hrow0]
        exact Finset.subset_univ _
      exact fun hconn => d.2.2.2.1
        (StatMech.GrahamGHS.FourColor.connK_mono hsub hconn)
    have hrow1Disconn : ¬ StatMech.Sharpness.RandomCurrent.connK E
        (lpReplicaRowCopies G sites m
          (lpReplicaToggleRows G sites m P d.1) true)
        lpReplicaCurrentGhost0 lpReplicaCurrentGhost1 := by
      have hsub : lpReplicaRowCopies G sites m
          (lpReplicaToggleRows G sites m P d.1) true ⊆
          lpReplicaRowCopies G sites m d.1 false := by
        rw [lpReplicaRowCopies_toggle, hrow1, hrow0]
        exact Finset.subset_univ _
      exact fun hconn => d.2.2.2.1
        (StatMech.GrahamGHS.FourColor.connK_mono hsub hconn)
    let s : LPReplicaBalancedSelector G sites (Si ∆ Sj ∆ T)
        (Sj ∆ T) q := {
      profile := m
      orbit := z.1.1.2
      tag := d.1
      gate := d.2
      orbitLabel := z.2.2
      selector := P
      falseSource := hfalseSource
      trueSource := htrueSource
      row0Disconn := hrow0Disconn
      row1Disconn := hrow1Disconn }
    let sourceTag := lpReplicaOrientedFourColorTag G sites ∅ B q
      (lpReplicaDecoratedOrbitAtomEquivOrientedFourColor G sites ∅ B q z)
    have hsourceTag : ∀ a, sourceTag a = (true, false) := by
      exact lpReplicaOffdiagDecoratedSource_rank_four_orientedTag
        G sites hsite hij q hcard z
    have hfixed : c.1 ∈ lpReplicaCurrentEdgeOrbitFixed G sites :=
      lpReplicaCurrentEdge_mem_orbitFixed_of_eq_seam G sites i m c hc
    have hSiCard : Si.card = 2 := by
      exact card_lpReplicaMatchingSeamSource sites i
    have hDCard : (Sj ∆ T).card = 4 := by
      exact card_lpReplicaMatchingSeamSymmDiffGhost sites j
    have hgeneric := lpReplicaBalancedSelector_rank_four_slotState
      G sites Si Sj T q hcard s c sourceTag hdall hsourceTag rfl hfixed
        hSiCard hDCard
    have hmask : lpReplicaOrbitCommonSlotsOfCopies G sites q z.1.1.1
        z.1.1.2 z.2.2 {c} =
        lpReplicaOrbitCommonSlotsOfCopies G sites q s.profile s.orbit
          s.orbitLabel {c} := rfl
    have hsourceState : lpReplicaOffdiagDecoratedSourceSlotState
        G sites i j q z =
        lpReplicaOrbitFourColorSlotStateOfTag G sites q s.profile s.orbit
          s.orbitLabel sourceTag := rfl
    have hfixedD : (Sj ∆ T).map lpReplicaCurrentReflect.toEmbedding =
        Sj ∆ T := lpReplicaCurrentReflect_seam_symmDiff_ghost G sites j
    exact Or.inl ⟨s, c, rfl, HEq.rfl, hc, HEq.rfl, hdall, by
      rw [hmask, hsourceState]
      unfold lpReplicaOffdiagDecoratedTargetBranchedSlotState
      unfold lpReplicaDecoratedOrbitAtomOfBalancedSelector_left
      dsimp only
      rw [lpReplicaOrientedFourColorSlotState_cast_boundary G sites Si
        ((Sj ∆ T).map lpReplicaCurrentReflect.toEmbedding) (Sj ∆ T) q
        hfixedD]
      exact hgeneric⟩
  · let P : Finset (StatMech.Sharpness.FluxEdgeCopy.Copy
        (lpReplicaCurrentGraph G sites) m) := Finset.univ \ {c}
    have hfalseFilter : P.filter (fun a => (d.1 a).2 = false) = P := by
      ext a
      simp [P, hdall]
    have htrueFilter : P.filter (fun a => (d.1 a).2 = true) = ∅ := by
      ext a
      simp [P, hdall]
    have hcends : E c = s(lpReplicaCurrentLeft sites j,
        lpReplicaCurrentRight sites j) := by
      simpa only [E, m, StatMech.Sharpness.FluxEdgeCopy.endsM] using hc
    have hsingle : StatMech.Sharpness.RandomCurrent.sources E {c} = Sj := by
      simpa only [Sj, lpMatchingSeamSource] using
        (randomCurrent_sources_singleton_of_ends_eq E c (by
          simp [lpReplicaCurrentLeft, lpReplicaCurrentRight]) hcends)
    have hfalseSource : StatMech.Sharpness.RandomCurrent.sources E
        (P.filter fun a => (d.1 a).2 = false) = Si ∆ T := by
      rw [hfalseFilter]
      calc
        StatMech.Sharpness.RandomCurrent.sources E P =
            StatMech.Sharpness.RandomCurrent.sources E Finset.univ ∆
              StatMech.Sharpness.RandomCurrent.sources E {c} := by
          exact StatMech.GrahamGHS.FourColor.sources_sdiff_of_subset (by simp [P])
        _ = B ∆ Sj := by rw [htotal, hsingle]
        _ = Si ∆ T := by
          rw [hBswap, symmDiff_assoc Sj Si T,
            symmDiff_symmDiff_self']
    have htrueSource : StatMech.Sharpness.RandomCurrent.sources E
        (P.filter fun a => (d.1 a).2 = true) = ∅ := by
      rw [htrueFilter]
      simp [StatMech.Sharpness.RandomCurrent.sources,
        StatMech.Sharpness.RandomCurrent.degK]
    have hrow0Disconn : ¬ StatMech.Sharpness.RandomCurrent.connK E
        (lpReplicaRowCopies G sites m
          (lpReplicaToggleRows G sites m P d.1) false)
        lpReplicaCurrentGhost0 lpReplicaCurrentGhost1 := by
      have hsub : lpReplicaRowCopies G sites m
          (lpReplicaToggleRows G sites m P d.1) false ⊆
          lpReplicaRowCopies G sites m d.1 false := by
        rw [lpReplicaRowCopies_toggle, hrow0]
        exact Finset.subset_univ _
      exact fun hconn => d.2.2.2.1
        (StatMech.GrahamGHS.FourColor.connK_mono hsub hconn)
    have hrow1Disconn : ¬ StatMech.Sharpness.RandomCurrent.connK E
        (lpReplicaRowCopies G sites m
          (lpReplicaToggleRows G sites m P d.1) true)
        lpReplicaCurrentGhost0 lpReplicaCurrentGhost1 := by
      have hsub : lpReplicaRowCopies G sites m
          (lpReplicaToggleRows G sites m P d.1) true ⊆
          lpReplicaRowCopies G sites m d.1 false := by
        rw [lpReplicaRowCopies_toggle, hrow1, hrow0]
        exact Finset.subset_univ _
      exact fun hconn => d.2.2.2.1
        (StatMech.GrahamGHS.FourColor.connK_mono hsub hconn)
    have hgate : LPReplicaRowGate G sites m (Sj ∆ Si ∆ T) ∅ d.1 := by
      rw [← hBswap]
      exact d.2
    let s : LPReplicaBalancedSelector G sites (Sj ∆ Si ∆ T)
        (Si ∆ T) q := {
      profile := m
      orbit := z.1.1.2
      tag := d.1
      gate := hgate
      orbitLabel := z.2.2
      selector := P
      falseSource := hfalseSource
      trueSource := htrueSource
      row0Disconn := hrow0Disconn
      row1Disconn := hrow1Disconn }
    let sourceTag := lpReplicaOrientedFourColorTag G sites ∅ B q
      (lpReplicaDecoratedOrbitAtomEquivOrientedFourColor G sites ∅ B q z)
    have hsourceTag : ∀ a, sourceTag a = (true, false) := by
      exact lpReplicaOffdiagDecoratedSource_rank_four_orientedTag
        G sites hsite hij q hcard z
    have hfixed : c.1 ∈ lpReplicaCurrentEdgeOrbitFixed G sites :=
      lpReplicaCurrentEdge_mem_orbitFixed_of_eq_seam G sites j m c hc
    have hSjCard : Sj.card = 2 := by
      exact card_lpReplicaMatchingSeamSource sites j
    have hDCard : (Si ∆ T).card = 4 := by
      exact card_lpReplicaMatchingSeamSymmDiffGhost sites i
    have hgeneric := lpReplicaBalancedSelector_rank_four_slotState
      G sites Sj Si T q hcard s c sourceTag hdall hsourceTag rfl hfixed
        hSjCard hDCard
    have hmask : lpReplicaOrbitCommonSlotsOfCopies G sites q z.1.1.1
        z.1.1.2 z.2.2 {c} =
        lpReplicaOrbitCommonSlotsOfCopies G sites q s.profile s.orbit
          s.orbitLabel {c} := rfl
    have hsourceState : lpReplicaOffdiagDecoratedSourceSlotState
        G sites i j q z =
        lpReplicaOrbitFourColorSlotStateOfTag G sites q s.profile s.orbit
          s.orbitLabel sourceTag := rfl
    have hfixedD : (Si ∆ T).map lpReplicaCurrentReflect.toEmbedding =
        Si ∆ T := lpReplicaCurrentReflect_seam_symmDiff_ghost G sites i
    exact Or.inr ⟨s, c, rfl, HEq.rfl, hc, HEq.rfl, hdall, by
      rw [hmask, hsourceState]
      unfold lpReplicaOffdiagDecoratedTargetBranchedSlotState
      unfold lpReplicaDecoratedOrbitAtomOfBalancedSelector_left
      dsimp only
      rw [lpReplicaOrientedFourColorSlotState_cast_boundary G sites Sj
        ((Si ∆ T).map lpReplicaCurrentReflect.toEmbedding) (Si ∆ T) q
        hfixedD]
      exact hgeneric⟩



theorem lpReplicaOffdiagBalancedOutputCrossTraceFiber_rank_four_nonempty
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites) {i j : I} (hij : i ≠ j)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 4)
    (z : LPReplicaOffdiagDecoratedSource G sites i j q) :
    (lpReplicaOffdiagBalancedOutputCrossTraceFiber G sites i j q
      (lpReplicaOffdiagDecoratedSourceCrossTrace G sites i j q z)).Nonempty := by
  classical
  rcases lpReplicaOffdiagDecoratedSource_rank_four_exists_balancedSelector
      G sites hsite hij q hcard z with
    ⟨s, c, _, _, _, _, _, hstate⟩ | ⟨s, c, _, _, _, _, _, hstate⟩
  · let y : LPReplicaOffdiagDecoratedTarget G sites i j q :=
      Sum.inl (lpReplicaDecoratedOrbitAtomOfBalancedSelector_left
        G sites i j q s)
    refine ⟨y, ?_⟩
    simp only [lpReplicaOffdiagBalancedOutputCrossTraceFiber,
      Finset.mem_filter]
    constructor
    · simp only [lpReplicaOffdiagBalancedOutputs, Finset.mem_filter,
        Finset.mem_univ, true_and, LPReplicaOffdiagBalancedOutput]
      exact Or.inl ⟨s, rfl⟩
    · unfold lpReplicaOffdiagDecoratedTargetCrossTrace
        lpReplicaOffdiagDecoratedSourceCrossTrace
      rw [hstate]
      exact lpReplicaOrbitFourColorSlotCrossNormalize_crossToggle
        G sites q _ _
  · let y : LPReplicaOffdiagDecoratedTarget G sites i j q :=
      Sum.inr (lpReplicaDecoratedOrbitAtomOfBalancedSelector_left
        G sites j i q s)
    refine ⟨y, ?_⟩
    simp only [lpReplicaOffdiagBalancedOutputCrossTraceFiber,
      Finset.mem_filter]
    constructor
    · simp only [lpReplicaOffdiagBalancedOutputs, Finset.mem_filter,
        Finset.mem_univ, true_and, LPReplicaOffdiagBalancedOutput]
      exact Or.inr ⟨s, rfl⟩
    · unfold lpReplicaOffdiagDecoratedTargetCrossTrace
        lpReplicaOffdiagDecoratedSourceCrossTrace
      rw [hstate]
      exact lpReplicaOrbitFourColorSlotCrossNormalize_crossToggle
        G sites q _ _


theorem lpReplicaOffdiagCrossTraceFiberCards_rank_four
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites) {i j : I} (hij : i ≠ j)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 4)
    (u : LPReplicaOrbitFourColorSlotState G sites q) :
    (lpReplicaOffdiagDecoratedSourceCrossTraceFiber G sites i j q u).card ≤
      (lpReplicaOffdiagBalancedOutputCrossTraceFiber G sites i j q u).card := by
  classical
  by_cases hs : (lpReplicaOffdiagDecoratedSourceCrossTraceFiber
      G sites i j q u).Nonempty
  · obtain ⟨z, hz⟩ := hs
    have hztrace : lpReplicaOffdiagDecoratedSourceCrossTrace G sites i j q z =
        u := (Finset.mem_filter.mp hz).2
    have ht := lpReplicaOffdiagBalancedOutputCrossTraceFiber_rank_four_nonempty
      G sites hsite hij q hcard z
    have ht' : (lpReplicaOffdiagBalancedOutputCrossTraceFiber
        G sites i j q u).Nonempty := by
      simpa only [hztrace] using ht
    exact (lpReplicaOffdiagDecoratedSourceCrossTraceFiber_rank_four_card_le_one
      G sites hsite hij q hcard u).trans ht'.card_pos
  · rw [Finset.not_nonempty_iff_eq_empty.mp hs]
    exact Nat.zero_le _


theorem lpReplicaOffdiagCrossToggleMaskHall_rank_four
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites) {i j : I} (hij : i ≠ j)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 4) :
    LPReplicaOffdiagCrossToggleMaskHall G sites i j q := by
  apply lpReplicaOffdiagCrossToggleMaskHall_of_crossTraceFiberCards
  intro u
  exact lpReplicaOffdiagCrossTraceFiberCards_rank_four
    G sites hsite hij q hcard u



theorem lpReplicaOffdiagOrbitAtomCardInequality_rank_four
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites) {i j : I} (hij : i ≠ j)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 4) :
    LPReplicaOffdiagOrbitAtomCardInequality G sites i j q := by
  exact lpReplicaOffdiagOrbitAtomCardInequality_of_crossToggleMaskHall
    G sites i j q
      (lpReplicaOffdiagCrossToggleMaskHall_rank_four
        G sites hsite hij q hcard)



end

end StatMech.Ising

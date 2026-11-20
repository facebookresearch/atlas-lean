/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.Ising.LebowitzPfisterReplicaOrbitRankFiveAggregateResidual

open Finset
open scoped symmDiff











namespace StatMech.Ising

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

local instance lpReplicaRankFiveFoldedDecidableAdj
    (G : SimpleGraph V) (sites : I -> V) :
    DecidableRel (lpReplicaCurrentGraph G sites).Adj :=
  Classical.decRel _



def lpReplicaTripleSeamGhostSource (sites : I -> V) (i j k : I) :
    Finset (LPReplicaCurrentVertex V) :=
  lpMatchingSeamSource
        (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i ∆
    lpMatchingSeamSource
        (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j ∆
    lpMatchingSeamSource
        (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) k ∆
    lpMatchingGhostSource
        (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
        lpReplicaCurrentGhost1



theorem card_lpReplicaTripleSeamGhostSource
    (sites : I -> V) (hsite : Function.Injective sites)
    {i j k : I} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    (lpReplicaTripleSeamGhostSource sites i j k).card = 8 := by
  have hsij : sites i ≠ sites j := hsite.ne hij
  have hsik : sites i ≠ sites k := hsite.ne hik
  have hsjk : sites j ≠ sites k := hsite.ne hjk
  have hi : ({lpReplicaCurrentLeft sites i} :
      Finset (LPReplicaCurrentVertex V)) ∆
        {lpReplicaCurrentRight sites i} =
      {lpReplicaCurrentLeft sites i, lpReplicaCurrentRight sites i} := by
    rw [Finset.symmDiff_eq_union]
    · rfl
    · simp [lpReplicaCurrentLeft, lpReplicaCurrentRight]
  have hj : ({lpReplicaCurrentLeft sites j} :
      Finset (LPReplicaCurrentVertex V)) ∆
        {lpReplicaCurrentRight sites j} =
      {lpReplicaCurrentLeft sites j, lpReplicaCurrentRight sites j} := by
    rw [Finset.symmDiff_eq_union]
    · rfl
    · simp [lpReplicaCurrentLeft, lpReplicaCurrentRight]
  have hk : ({lpReplicaCurrentLeft sites k} :
      Finset (LPReplicaCurrentVertex V)) ∆
        {lpReplicaCurrentRight sites k} =
      {lpReplicaCurrentLeft sites k, lpReplicaCurrentRight sites k} := by
    rw [Finset.symmDiff_eq_union]
    · rfl
    · simp [lpReplicaCurrentLeft, lpReplicaCurrentRight]
  have hg : ({(lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)} :
      Finset (LPReplicaCurrentVertex V)) ∆ {lpReplicaCurrentGhost1} =
      {(lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V),
        lpReplicaCurrentGhost1} := by
    rw [Finset.symmDiff_eq_union]
    · rfl
    · simp [lpReplicaCurrentGhost0, lpReplicaCurrentGhost1]
  have hdij : Disjoint
      ({lpReplicaCurrentLeft sites i, lpReplicaCurrentRight sites i} :
        Finset (LPReplicaCurrentVertex V))
      {lpReplicaCurrentLeft sites j, lpReplicaCurrentRight sites j} := by
    simp [lpReplicaCurrentLeft, lpReplicaCurrentRight, hsij, hsij.symm]
  have hdijk : Disjoint
      (({lpReplicaCurrentLeft sites i, lpReplicaCurrentRight sites i} :
          Finset (LPReplicaCurrentVertex V)) ∪
        {lpReplicaCurrentLeft sites j, lpReplicaCurrentRight sites j})
      {lpReplicaCurrentLeft sites k, lpReplicaCurrentRight sites k} := by
    simp [lpReplicaCurrentLeft, lpReplicaCurrentRight, hsik, hsik.symm,
      hsjk, hsjk.symm]
  have hdghost : Disjoint
      ((({lpReplicaCurrentLeft sites i, lpReplicaCurrentRight sites i} :
          Finset (LPReplicaCurrentVertex V)) ∪
        {lpReplicaCurrentLeft sites j, lpReplicaCurrentRight sites j}) ∪
        {lpReplicaCurrentLeft sites k, lpReplicaCurrentRight sites k})
      {(lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V),
        lpReplicaCurrentGhost1} := by
    simp [lpReplicaCurrentLeft, lpReplicaCurrentRight,
      lpReplicaCurrentGhost0, lpReplicaCurrentGhost1]
  unfold lpReplicaTripleSeamGhostSource lpMatchingSeamSource
    lpMatchingGhostSource
  rw [hi, hj, hk, hg]
  rw [Finset.symmDiff_eq_union hdij,
    Finset.symmDiff_eq_union hdijk,
    Finset.symmDiff_eq_union hdghost]
  simp [lpReplicaCurrentLeft, lpReplicaCurrentRight,
    lpReplicaCurrentGhost0, lpReplicaCurrentGhost1,
    hsij, hsij.symm, hsik, hsik.symm, hsjk, hsjk.symm]



def lpReplicaCurrentFold : LPReplicaCurrentVertex V -> V ⊕ Unit
  | .inl (.inl x) => .inl x
  | .inl (.inr x) => .inl x
  | .inr _ => .inr ()

@[simp] theorem lpReplicaCurrentFold_left (x : V) :
    lpReplicaCurrentFold
        (.inl (.inl x) : LPReplicaCurrentVertex V) = Sum.inl x := rfl

@[simp] theorem lpReplicaCurrentFold_right (x : V) :
    lpReplicaCurrentFold
        (.inl (.inr x) : LPReplicaCurrentVertex V) = Sum.inl x := rfl

@[simp] theorem lpReplicaCurrentFold_ghost (b : Bool) :
    lpReplicaCurrentFold (.inr b : LPReplicaCurrentVertex V) =
      Sum.inr () := rfl


@[simp] theorem lpReplicaCurrentFold_reflect
    (x : LPReplicaCurrentVertex V) :
    lpReplicaCurrentFold (lpReplicaCurrentReflect x) =
      lpReplicaCurrentFold x := by
  rcases x with (x | b)
  · rcases x with x | x <;> rfl
  · cases b <;> rfl


def lpReplicaCurrentFoldedEdge
    (G : SimpleGraph V) (sites : I -> V)
    (e : (lpReplicaCurrentGraph G sites).edgeFinset) : Sym2 (V ⊕ Unit) :=
  Sym2.map lpReplicaCurrentFold e.1


@[simp] theorem lpReplicaCurrentFoldedEdge_reflect
    (G : SimpleGraph V) (sites : I -> V)
    (e : (lpReplicaCurrentGraph G sites).edgeFinset) :
    lpReplicaCurrentFoldedEdge G sites
        (lpReplicaCurrentEdgeReflect G sites e) =
      lpReplicaCurrentFoldedEdge G sites e := by
  unfold lpReplicaCurrentFoldedEdge
  rw [lpReplicaCurrentEdgeReflect_val, Sym2.map_map]
  apply Sym2.map_congr
  intro x _
  exact lpReplicaCurrentFold_reflect x




def lpReplicaOrbitFoldedSlotEnds
    (G : SimpleGraph V) (sites : I -> V)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
    LPReplicaOrbitCommonSlot G sites q -> Sym2 (V ⊕ Unit)
  | Sum.inl fixed => lpReplicaCurrentFoldedEdge G sites fixed.1.1
  | Sum.inr strict => lpReplicaCurrentFoldedEdge G sites strict.1.1



theorem lpReplicaOrbitFourColorSlotEnds_fold
    (G : SimpleGraph V) (sites : I -> V)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (s : LPReplicaOrbitFourColorSlotState G sites q)
    (x : LPReplicaOrbitCommonSlot G sites q) :
    Sym2.map lpReplicaCurrentFold
        (lpReplicaOrbitFourColorSlotEnds G sites q s x) =
      lpReplicaOrbitFoldedSlotEnds G sites q x := by
  rcases x with fixed | strict
  · rfl
  · simp only [lpReplicaOrbitFourColorSlotEnds,
      lpReplicaOrbitFourColorSlotEdge, lpReplicaOrbitFoldedSlotEnds]
    by_cases h : strict.2 ∈ s.allocation strict.1
    · simp only [h, if_pos]
      rfl
    · simp only [h, if_neg]
      exact lpReplicaCurrentFoldedEdge_reflect G sites strict.1.1


@[simp] theorem lpReplicaCurrentFoldedEdge_seam
    (G : SimpleGraph V) (sites : I -> V) (i : I)
    (hmem : lpReplicaCurrentSeamEdge sites i ∈
      (lpReplicaCurrentGraph G sites).edgeFinset) :
    lpReplicaCurrentFoldedEdge G sites
        ⟨lpReplicaCurrentSeamEdge sites i, hmem⟩ =
      s(Sum.inl (sites i), Sum.inl (sites i)) := by
  unfold lpReplicaCurrentFoldedEdge lpReplicaCurrentSeamEdge
    lpReplicaCurrentLeft lpReplicaCurrentRight
  rw [Sym2.map_pair_eq]
  rfl


theorem lpReplicaOrbitFoldedSlotEnds_copy
    (G : SimpleGraph V) (sites : I -> V)
    (q m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hm : lpReplicaSymmetrizedProfile G sites m = q)
    (L : LPReplicaProfileOrbitLabel G sites q m)
    (c : StatMech.Sharpness.FluxEdgeCopy.Copy
      (lpReplicaCurrentGraph G sites) m) :
    lpReplicaOrbitFoldedSlotEnds G sites q
        (lpReplicaProfileCopyEquivCommonSlot G sites q m hm L c) =
      lpReplicaCurrentFoldedEdge G sites c.1 := by
  let tag : StatMech.Sharpness.FluxEdgeCopy.Copy
      (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag :=
    fun _ => (false, false)
  have hends := lpReplicaOrbitFourColorSlotEnds_stateOfTag_copy
    G sites q m hm L tag c
  have hfold := lpReplicaOrbitFourColorSlotEnds_fold G sites q
    (lpReplicaOrbitFourColorSlotStateOfTag G sites q m hm L tag)
    (lpReplicaProfileCopyEquivCommonSlot G sites q m hm L c)
  unfold lpReplicaCurrentFoldedEdge
  rw [← hfold, hends]
  rfl



theorem lpReplicaOffdiagDecoratedSource_fullRawSources
    (G : SimpleGraph V) (sites : I -> V) {i j : I}
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (z : LPReplicaOffdiagDecoratedSource G sites i j q) :
    StatMech.Sharpness.RandomCurrent.sources
        (StatMech.Sharpness.FluxEdgeCopy.endsM
          (lpReplicaCurrentGraph G sites) z.1.1.1)
        Finset.univ =
      lpMatchingSeamSource
            (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i ∆
        lpMatchingSeamSource
            (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j ∆
        lpMatchingGhostSource
            (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
            lpReplicaCurrentGhost1 := by
  let d := lpReplicaDecoratedSourceRowGateData G sites i j q z
  let B :=
    lpMatchingSeamSource
          (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i ∆
      lpMatchingSeamSource
          (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j ∆
      lpMatchingGhostSource
          (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
          lpReplicaCurrentGhost1
  have h := lpReplicaRowGate_fullSources G sites z.1.1.1 ∅ B d.1 d.2
  calc
    _ = ∅ ∆ B := h
    _ = B := by
      ext x
      simp [Finset.mem_symmDiff]

set_option maxHeartbeats 2000000 in



theorem lpReplicaOffdiagDecoratedSource_sources_erase_seamCopy
    (G : SimpleGraph V) (sites : I -> V) {i j k : I}
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (z : LPReplicaOffdiagDecoratedSource G sites i j q)
    (c : StatMech.Sharpness.FluxEdgeCopy.Copy
      (lpReplicaCurrentGraph G sites) z.1.1.1)
    (hc : c.1.1 = lpReplicaCurrentSeamEdge sites k) :
    StatMech.Sharpness.RandomCurrent.sources
        (StatMech.Sharpness.FluxEdgeCopy.endsM
          (lpReplicaCurrentGraph G sites) z.1.1.1)
        (Finset.univ \ {c}) =
      lpReplicaTripleSeamGhostSource sites i j k := by
  let E := StatMech.Sharpness.FluxEdgeCopy.endsM
    (lpReplicaCurrentGraph G sites) z.1.1.1
  let Si := lpMatchingSeamSource
    (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i
  let Sj := lpMatchingSeamSource
    (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j
  let Sk := lpMatchingSeamSource
    (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) k
  let T := lpMatchingGhostSource
    (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
    lpReplicaCurrentGhost1
  have hcends : E c = s(lpReplicaCurrentLeft sites k,
      lpReplicaCurrentRight sites k) := by
    simpa only [E, StatMech.Sharpness.FluxEdgeCopy.endsM] using hc
  have hsingle : StatMech.Sharpness.RandomCurrent.sources E {c} = Sk := by
    simpa only [Sk, lpMatchingSeamSource] using
      randomCurrent_sources_singleton_of_ends_eq E c (by
        simp [lpReplicaCurrentLeft, lpReplicaCurrentRight]) hcends
  rw [StatMech.GrahamGHS.FourColor.sources_sdiff_of_subset (by simp),
    lpReplicaOffdiagDecoratedSource_fullRawSources G sites q z]
  rw [hsingle]
  change (Si ∆ Sj ∆ T) ∆ Sk = Si ∆ Sj ∆ Sk ∆ T
  ext x
  simp only [Finset.mem_symmDiff]
  tauto


theorem lpReplicaOffdiagDecoratedSource_card_erase_copy_rankFive
    (G : SimpleGraph V) (sites : I -> V) {i j : I}
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
    (z : LPReplicaOffdiagDecoratedSource G sites i j q)
    (c : StatMech.Sharpness.FluxEdgeCopy.Copy
      (lpReplicaCurrentGraph G sites) z.1.1.1) :
    (Finset.univ \ {c}).card = 4 := by
  have hcopyCard : Fintype.card
      (StatMech.Sharpness.FluxEdgeCopy.Copy
        (lpReplicaCurrentGraph G sites) z.1.1.1) = 5 := by
    calc
      _ = Fintype.card (LPReplicaOrbitCommonSlot G sites q) :=
        Fintype.card_congr
          (lpReplicaProfileCopyEquivCommonSlot G sites q z.1.1.1
            z.1.1.2 z.2.2)
      _ = 5 := hcard
  rw [Finset.card_sdiff_of_subset (Finset.singleton_subset_iff.mpr
    (Finset.mem_univ c)), Finset.card_univ, hcopyCard,
    Finset.card_singleton]



theorem randomCurrent_endpointSupport_eq_sources_of_card_eq_two_mul
    {E W : Type*} [Fintype E] [DecidableEq E]
    [Fintype W] [DecidableEq W]
    (ends : E -> Sym2 W) (K : Finset E)
    (hcard : (StatMech.Sharpness.RandomCurrent.sources ends K).card =
      2 * K.card) :
    K.biUnion (fun e => (ends e).toFinset) =
      StatMech.Sharpness.RandomCurrent.sources ends K := by
  classical
  let support := K.biUnion fun e => (ends e).toFinset
  have hsubset :
      StatMech.Sharpness.RandomCurrent.sources ends K ⊆ support :=
    randomCurrent_sources_subset_endpointSupport ends K
  have hsupportCard : support.card ≤ 2 * K.card := by
    calc
      support.card ≤ ∑ e ∈ K, (ends e).toFinset.card :=
        Finset.card_biUnion_le
      _ ≤ ∑ _e ∈ K, 2 := by
        apply Finset.sum_le_sum
        intro e _
        rw [Sym2.card_toFinset]
        split <;> omega
      _ = 2 * K.card := by simp [Nat.mul_comm]
  symm
  apply Finset.eq_of_subset_of_card_le hsubset
  rw [hcard]
  exact hsupportCard




theorem randomCurrent_existsUnique_copy_of_mem_endpointSupport_of_card_eq_two_mul
    {E W : Type*} [Fintype E] [DecidableEq E]
    [Fintype W] [DecidableEq W]
    (ends : E -> Sym2 W) (K : Finset E)
    (hcard : (StatMech.Sharpness.RandomCurrent.sources ends K).card =
      2 * K.card) {x : W}
    (hx : x ∈ K.biUnion (fun e => (ends e).toFinset)) :
    ∃! e, e ∈ K ∧ x ∈ (ends e).toFinset := by
  classical
  obtain ⟨c, hcK, hxc⟩ := Finset.mem_biUnion.mp hx
  refine ⟨c, ⟨hcK, hxc⟩, ?_⟩
  rintro e ⟨heK, hxe⟩
  by_contra hce
  let f : E -> Finset W := fun a => (ends a).toFinset
  let R := K.erase c
  let supportR := R.biUnion f
  have heR : e ∈ R := Finset.mem_erase.mpr ⟨hce, heK⟩
  have hxinter : x ∈ f c ∩ supportR := by
    apply Finset.mem_inter.mpr
    refine ⟨hxc, ?_⟩
    exact Finset.mem_biUnion.mpr ⟨e, heR, hxe⟩
  have hinterPos : 0 < (f c ∩ supportR).card :=
    Finset.card_pos.mpr ⟨x, hxinter⟩
  have hRcard : R.card + 1 = K.card := by
    have hKpos : 0 < K.card := Finset.card_pos.mpr ⟨c, hcK⟩
    simp only [R, Finset.card_erase_of_mem hcK]
    omega
  have hsupportR : supportR.card ≤ 2 * R.card := by
    calc
      supportR.card ≤ ∑ a ∈ R, (ends a).toFinset.card :=
        Finset.card_biUnion_le
      _ ≤ ∑ _a ∈ R, 2 := by
        apply Finset.sum_le_sum
        intro a _
        rw [Sym2.card_toFinset]
        split <;> omega
      _ = 2 * R.card := by simp [Nat.mul_comm]
  have hfc : (f c).card ≤ 2 := by
    dsimp only [f]
    rw [Sym2.card_toFinset]
    split <;> omega
  have hsupportEq : K.biUnion f = f c ∪ supportR := by
    rw [← Finset.insert_erase hcK, Finset.biUnion_insert]
  have htight : (K.biUnion f).card = 2 * K.card := by
    rw [randomCurrent_endpointSupport_eq_sources_of_card_eq_two_mul
      ends K hcard, hcard]
  have hunion := Finset.card_union_add_card_inter (f c) supportR
  rw [← hsupportEq, htight] at hunion
  omega

set_option maxHeartbeats 2000000 in




theorem lpReplicaAggregateUnmarkedSaturatedSourceRankFive_selectedSeam_perfectMatching
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
    (z : LPReplicaAggregateUnmarkedSaturatedSourceRankFive G sites q) :
    let a := z.toAggregate G sites q
    let k := lpReplicaAggregateDecoratedSourceSelectedSeam
      G sites hsite q a
    ∃ c : StatMech.Sharpness.FluxEdgeCopy.Copy
        (lpReplicaCurrentGraph G sites) a.2.2.2.1.1.1,
      c.1.1 = lpReplicaCurrentSeamEdge sites k ∧
        let K := Finset.univ \ {c}
        let E := StatMech.Sharpness.FluxEdgeCopy.endsM
          (lpReplicaCurrentGraph G sites) a.2.2.2.1.1.1
        K.card = 4 ∧
          StatMech.Sharpness.RandomCurrent.sources E K =
            lpReplicaTripleSeamGhostSource sites a.1 a.2.1 k ∧
          K.biUnion (fun e => (E e).toFinset) =
            lpReplicaTripleSeamGhostSource sites a.1 a.2.1 k ∧
          ∀ x ∈ lpReplicaTripleSeamGhostSource sites a.1 a.2.1 k,
            ∃! e, e ∈ K ∧ x ∈ (E e).toFinset := by
  classical
  dsimp only
  let a := z.toAggregate G sites q
  let k := lpReplicaAggregateDecoratedSourceSelectedSeam
    G sites hsite q a
  obtain ⟨c, hc⟩ :=
    lpReplicaAggregateDecoratedSourceSelectedSeam_exists_copy
      G sites hsite q a
  refine ⟨c, hc, ?_⟩
  let K := Finset.univ \ {c}
  let E := StatMech.Sharpness.FluxEdgeCopy.endsM
    (lpReplicaCurrentGraph G sites) a.2.2.2.1.1.1
  have hij : a.1 ≠ a.2.1 :=
    lpReplicaAggregateDecoratedSource_indices_ne G sites q a
  have hkunmarked :=
    lpReplicaAggregateUnmarkedSaturatedSourceRankFive_selectedSeam_unmarked
      G sites hsite q hcard z
  have hik : a.1 ≠ k := Ne.symm hkunmarked.1
  have hjk : a.2.1 ≠ k := Ne.symm hkunmarked.2
  have hKcard : K.card = 4 := by
    exact lpReplicaOffdiagDecoratedSource_card_erase_copy_rankFive
      G sites q hcard a.2.2.2 c
  have hsources : StatMech.Sharpness.RandomCurrent.sources E K =
      lpReplicaTripleSeamGhostSource sites a.1 a.2.1 k := by
    exact lpReplicaOffdiagDecoratedSource_sources_erase_seamCopy
      G sites q a.2.2.2 c hc
  have htight :
      (StatMech.Sharpness.RandomCurrent.sources E K).card = 2 * K.card := by
    rw [hsources, card_lpReplicaTripleSeamGhostSource sites hsite
      hij hik hjk, hKcard]
  have hsupport : K.biUnion (fun e => (E e).toFinset) =
      lpReplicaTripleSeamGhostSource sites a.1 a.2.1 k :=
    (randomCurrent_endpointSupport_eq_sources_of_card_eq_two_mul
      E K htight).trans hsources
  refine ⟨hKcard, hsources, hsupport, ?_⟩
  intro x hx
  apply randomCurrent_existsUnique_copy_of_mem_endpointSupport_of_card_eq_two_mul
    E K htight
  rw [hsupport]
  exact hx

end

end StatMech.Ising

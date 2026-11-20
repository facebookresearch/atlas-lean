/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.Ising.LebowitzPfisterReplicaOrbitRankFiveHandledStrictInvariant
import Code.Ising.LebowitzPfisterReplicaOrbitRankFivePairedHall










open Finset
open scoped symmDiff

namespace StatMech.Ising

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

local instance lpReplicaRankFiveHighComplementDecidableAdj
    (G : SimpleGraph V) (sites : I -> V) :
    DecidableRel (lpReplicaCurrentGraph G sites).Adj :=
  Classical.decRel _

omit [Fintype I] [DecidableEq I] in


theorem lpReplicaToggleRows_swapRowsTag_eq_compl
    (G : SimpleGraph V) (sites : I -> V)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (P : Finset (StatMech.Sharpness.FluxEdgeCopy.Copy
      (lpReplicaCurrentGraph G sites) m))
    (tag : StatMech.Sharpness.FluxEdgeCopy.Copy
      (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag) :
    lpReplicaToggleRows G sites m P (lpReplicaSwapRowsTag tag) =
      lpReplicaToggleRows G sites m (Finset.univ \ P) tag := by
  funext c
  by_cases hc : c ∈ P
  · rcases htag : tag c with ⟨row, current⟩
    cases row <;> cases current <;>
      simp [lpReplicaToggleRows, lpReplicaSwapRowsTag, hc, htag]
  · rcases htag : tag c with ⟨row, current⟩
    cases row <;> cases current <;>
      simp [lpReplicaToggleRows, lpReplicaSwapRowsTag, hc, htag]

omit [Fintype I] [DecidableEq I] in

theorem lpReplicaToggleRows_self
    (G : SimpleGraph V) (sites : I -> V)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (P : Finset (StatMech.Sharpness.FluxEdgeCopy.Copy
      (lpReplicaCurrentGraph G sites) m))
    (tag : StatMech.Sharpness.FluxEdgeCopy.Copy
      (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag) :
    lpReplicaToggleRows G sites m P
        (lpReplicaToggleRows G sites m P tag) = tag := by
  funext a
  by_cases ha : a ∈ P
  · rcases htag : tag a with ⟨row, current⟩
    cases row <;> cases current <;>
      simp [lpReplicaToggleRows, ha, htag]
  · simp [lpReplicaToggleRows, ha]

omit [Fintype I] [DecidableEq I] in




theorem lpReplicaToggleRows_activeSdiff_swapRowsTag_eq_singleton_after_complement
    (G : SimpleGraph V) (sites : I -> V)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (K : Finset (StatMech.Sharpness.FluxEdgeCopy.Copy
      (lpReplicaCurrentGraph G sites) m))
    (c : StatMech.Sharpness.FluxEdgeCopy.Copy
      (lpReplicaCurrentGraph G sites) m) (hcK : c ∈ K)
    (tag : StatMech.Sharpness.FluxEdgeCopy.Copy
      (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag) :
    lpReplicaToggleRows G sites m (K \ {c}) (lpReplicaSwapRowsTag tag) =
      lpReplicaToggleRows G sites m {c}
        (lpReplicaToggleRows G sites m (Finset.univ \ K) tag) := by
  funext a
  by_cases hac : a = c
  · subst a
    rcases htag : tag c with ⟨row, current⟩
    cases row <;> cases current <;>
      simp [lpReplicaToggleRows, lpReplicaSwapRowsTag, hcK, htag]
  · by_cases haK : a ∈ K
    · rcases htag : tag a with ⟨row, current⟩
      cases row <;> cases current <;>
        simp [lpReplicaToggleRows, lpReplicaSwapRowsTag, hac, haK, htag]
    · rcases htag : tag a with ⟨row, current⟩
      cases row <;> cases current <;>
        simp [lpReplicaToggleRows, lpReplicaSwapRowsTag, hac, haK, htag]

omit [Fintype I] [DecidableEq I] in


theorem
    lpReplicaToggleRows_activeSdiff_swapRowsComplementTag_eq_singleton
    (G : SimpleGraph V) (sites : I -> V)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (K : Finset (StatMech.Sharpness.FluxEdgeCopy.Copy
      (lpReplicaCurrentGraph G sites) m))
    (c : StatMech.Sharpness.FluxEdgeCopy.Copy
      (lpReplicaCurrentGraph G sites) m) (hcK : c ∈ K)
    (tag : StatMech.Sharpness.FluxEdgeCopy.Copy
      (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag) :
    lpReplicaToggleRows G sites m (K \ {c})
        (lpReplicaSwapRowsTag
          (lpReplicaToggleRows G sites m (Finset.univ \ K) tag)) =
      lpReplicaToggleRows G sites m {c} tag := by
  rw [lpReplicaToggleRows_activeSdiff_swapRowsTag_eq_singleton_after_complement
    G sites m K c hcK]
  rw [lpReplicaToggleRows_self]

omit [Fintype I] [DecidableEq I] in


theorem lpReplicaToggleRows_singleton_after_complement_ne_singleton
    (G : SimpleGraph V) (sites : I -> V)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (K : Finset (StatMech.Sharpness.FluxEdgeCopy.Copy
      (lpReplicaCurrentGraph G sites) m))
    (c : StatMech.Sharpness.FluxEdgeCopy.Copy
      (lpReplicaCurrentGraph G sites) m) (hcK : c ∈ K)
    (hC : (Finset.univ \ K).Nonempty)
    (tag : StatMech.Sharpness.FluxEdgeCopy.Copy
      (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag) :
    lpReplicaToggleRows G sites m {c}
        (lpReplicaToggleRows G sites m (Finset.univ \ K) tag) ≠
      lpReplicaToggleRows G sites m {c} tag := by
  obtain ⟨e, heC⟩ := hC
  have heK : e ∉ K := (Finset.mem_sdiff.mp heC).2
  have hec : e ≠ c := by
    intro heq
    exact heK (heq ▸ hcK)
  intro h
  have heq := congrFun h e
  rcases htag : tag e with ⟨row, current⟩
  cases row <;> cases current <;>
    simp [lpReplicaToggleRows, heC, hec, htag] at heq

set_option maxHeartbeats 2000000 in






theorem
    lpReplicaOffdiagDecoratedSource_rankFive_nonsaturatedHigh_iSeam_complementTarget
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites) {i j : I} (hij : i ≠ j)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
    (z : LPReplicaOffdiagDecoratedSource G sites i j q)
    (hhigh :
      let d := lpReplicaDecoratedSourceRowGateData G sites i j q z
      let K := lpReplicaCurrentCopies G sites z.1.1.1 d.1 true false
      K.card = 3 ∧
        ∃ r, r ∈ Finset.univ \ K ∧ (d.1 r).1 = true)
    (c : StatMech.Sharpness.FluxEdgeCopy.Copy
      (lpReplicaCurrentGraph G sites) z.1.1.1)
    (hcK : c ∈ lpReplicaCurrentCopies G sites z.1.1.1
      (lpReplicaDecoratedSourceRowGateData G sites i j q z).1 true false)
    (hc : c.1.1 = lpReplicaCurrentSeamEdge sites i) :
    ∃ s : LPReplicaBalancedSelector G sites
        (lpMatchingSeamSource
              (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i ∆
            lpMatchingSeamSource
              (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j ∆
            lpMatchingGhostSource
              (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
              lpReplicaCurrentGhost1)
        (lpMatchingSeamSource
              (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j ∆
            lpMatchingGhostSource
              (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
              lpReplicaCurrentGhost1) q,
      s.profile = z.1.1.1 ∧ HEq s.orbitLabel z.2.2 ∧
        HEq s.selector
          (lpReplicaCurrentCopies G sites z.1.1.1
              (lpReplicaDecoratedSourceRowGateData G sites i j q z).1
              true false \ {c}) ∧
        @HEq
          (Finset (StatMech.Sharpness.FluxEdgeCopy.Copy
            (lpReplicaCurrentGraph G sites) s.profile))
          (lpReplicaRowCopies G sites s.profile
            (lpReplicaToggleRows G sites s.profile s.selector s.tag) true)
          (Finset (StatMech.Sharpness.FluxEdgeCopy.Copy
            (lpReplicaCurrentGraph G sites) z.1.1.1))
          (lpReplicaCurrentCopies G sites z.1.1.1
              (lpReplicaDecoratedSourceRowGateData G sites i j q z).1
              true false \ {c}) ∧
        ∃ y : LPReplicaDecoratedOrbitAtom G sites
            (lpMatchingSeamSource
              (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i)
            (lpMatchingSeamSource
                (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j ∆
              lpMatchingGhostSource
                (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
                lpReplicaCurrentGhost1) q,
          LPReplicaOffdiagBalancedOutput G sites i j q (Sum.inl y) ∧
            ¬ LPReplicaOffdiagDecoratedTarget.HasStrictPhysicalDoubleIncidence
              G sites i j q (Sum.inl y) ∧
            y = lpReplicaDecoratedOrbitAtomOfBalancedSelector_left
              G sites i j q s := by
  classical
  dsimp only at hhigh
  let Si := lpMatchingSeamSource
    (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i
  let Sj := lpMatchingSeamSource
    (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j
  let T := lpMatchingGhostSource
    (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V) lpReplicaCurrentGhost1
  let B := Si ∆ Sj ∆ T
  let m := z.1.1.1
  let E := StatMech.Sharpness.FluxEdgeCopy.endsM
    (lpReplicaCurrentGraph G sites) m
  let d0 := lpReplicaDecoratedSourceRowGateData G sites i j q z
  let d := lpReplicaDecoratedSourceSwappedRowGateData G sites i j q z
  let K := lpReplicaCurrentCopies G sites m d0.1 true false
  let C := Finset.univ \ K
  let P := K \ {c}
  let Q := {c} ∪ C
  have hthree : K.card = 3 := by
    simpa only [K, d0] using hhigh.1
  obtain ⟨r, hrC, hrrow⟩ := hhigh.2
  change r ∈ C at hrC
  change (d0.1 r).1 = true at hrrow
  have hctag0 : d0.1 c = (true, false) := by
    simpa only [K, lpReplicaCurrentCopies, Finset.mem_filter,
      Finset.mem_univ, true_and] using hcK
  have hconst : ∀ a ∈ C, d0.1 a = d0.1 r := by
    intro a ha
    exact lpReplicaOffdiagDecoratedSource_rank_five_complement_tag_constant
      G sites hsite hij q hcard z hthree a ha r hrC
  have hallRow (a) : (d0.1 a).1 = true := by
    by_cases haK : a ∈ K
    · have hatag : d0.1 a = (true, false) := by
        simpa only [K, lpReplicaCurrentCopies, Finset.mem_filter,
          Finset.mem_univ, true_and] using haK
      simp [hatag]
    · have haC : a ∈ C :=
        Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, haK⟩
      exact congrArg Prod.fst (hconst a haC) |>.trans hrrow
  have hcends : E c = s(lpReplicaCurrentLeft sites i,
      lpReplicaCurrentRight sites i) := by
    simpa only [E, m, StatMech.Sharpness.FluxEdgeCopy.endsM] using hc
  have hsingle : StatMech.Sharpness.RandomCurrent.sources E {c} = Si := by
    simpa only [Si, lpMatchingSeamSource] using
      randomCurrent_sources_singleton_of_ends_eq E c (by
        simp [lpReplicaCurrentLeft, lpReplicaCurrentRight]) hcends
  have hsourceK : StatMech.Sharpness.RandomCurrent.sources E K = B := by
    simpa only [E, K, B, d0] using d0.2.2.2.2.1
  have hcSub : ({c} : Finset _) ⊆ K := by
    simpa only [Finset.singleton_subset_iff] using hcK
  have hsourceP : StatMech.Sharpness.RandomCurrent.sources E P = Sj ∆ T := by
    calc
      _ = StatMech.Sharpness.RandomCurrent.sources E K ∆
          StatMech.Sharpness.RandomCurrent.sources E {c} := by
        simpa only [P] using
          StatMech.GrahamGHS.FourColor.sources_sdiff_of_subset hcSub
      _ = B ∆ Si := by rw [hsourceK, hsingle]
      _ = Sj ∆ T := by
        change (Si ∆ Sj ∆ T) ∆ Si = Sj ∆ T
        rw [symmDiff_assoc Si Sj T, symmDiff_symmDiff_self']
  have hPtag (a) (ha : a ∈ P) : d.1 a = (false, false) := by
    have haK : a ∈ K := (Finset.mem_sdiff.mp ha).1
    have hatag : d0.1 a = (true, false) := by
      simpa only [K, lpReplicaCurrentCopies, Finset.mem_filter,
        Finset.mem_univ, true_and] using haK
    change lpReplicaSwapRowsTag d0.1 a = (false, false)
    simp [lpReplicaSwapRowsTag, hatag]
  have hfilterFalse : P.filter (fun a => (d.1 a).2 = false) = P := by
    ext a
    constructor
    · exact fun ha => (Finset.mem_filter.mp ha).1
    · intro ha
      exact Finset.mem_filter.mpr ⟨ha, by rw [hPtag a ha]⟩
  have hfilterTrue : P.filter (fun a => (d.1 a).2 = true) = ∅ := by
    ext a
    constructor
    · intro ha
      have ha' := Finset.mem_filter.mp ha
      rw [hPtag a ha'.1] at ha'
      simp at ha'
    · intro ha
      simp at ha
  have hfalseSource : StatMech.Sharpness.RandomCurrent.sources E
      (P.filter fun a => (d.1 a).2 = false) = Sj ∆ T := by
    rw [hfilterFalse]
    exact hsourceP
  have htrueSource : StatMech.Sharpness.RandomCurrent.sources E
      (P.filter fun a => (d.1 a).2 = true) = ∅ := by
    rw [hfilterTrue]
    exact randomCurrent_sources_empty E
  have hcompl : Finset.univ \ P = Q := by
    ext a
    by_cases hac : a = c
    · subst a
      simp [P, Q]
    · by_cases haK : a ∈ K
      · simp [P, Q, C, hac, haK]
      · simp [P, Q, C, hac, haK]
  have hmove : lpReplicaToggleRows G sites m P d.1 =
      lpReplicaToggleRows G sites m Q d0.1 := by
    change lpReplicaToggleRows G sites m P
        (lpReplicaSwapRowsTag d0.1) = _
    rw [lpReplicaToggleRows_swapRowsTag_eq_compl, hcompl]
  have hrow1Eq : lpReplicaRowCopies G sites m
      (lpReplicaToggleRows G sites m P d.1) true = P := by
    rw [hmove]
    ext a
    by_cases hac : a = c
    · subst a
      simp [P, Q, C, lpReplicaRowCopies, lpReplicaToggleRows, hctag0]
    · by_cases haK : a ∈ K
      · have hatag : d0.1 a = (true, false) := by
          simpa only [K, lpReplicaCurrentCopies, Finset.mem_filter,
            Finset.mem_univ, true_and] using haK
        simp [P, Q, C, lpReplicaRowCopies, lpReplicaToggleRows, hac,
          haK, hatag]
      · simp [P, Q, C, lpReplicaRowCopies, lpReplicaToggleRows, hac,
          haK, hallRow]
  have hrow0Eq : lpReplicaRowCopies G sites m
      (lpReplicaToggleRows G sites m P d.1) false = Q := by
    rw [hmove]
    ext a
    by_cases haQ : a ∈ Q
    · simp [lpReplicaRowCopies, lpReplicaToggleRows, haQ, hallRow]
    · simp [lpReplicaRowCopies, lpReplicaToggleRows, haQ, hallRow]
  have hrow1Disconn : ¬ StatMech.Sharpness.RandomCurrent.connK E
      (lpReplicaRowCopies G sites m
        (lpReplicaToggleRows G sites m P d.1) true)
      lpReplicaCurrentGhost0 lpReplicaCurrentGhost1 := by
    intro hconn
    apply d0.2.2.2.2.2.2
    apply StatMech.GrahamGHS.FourColor.connK_mono _ hconn
    rw [hrow1Eq]
    intro a ha
    simp only [lpReplicaRowCopies, Finset.mem_filter, Finset.mem_univ,
      true_and]
    exact hallRow a
  have hCcard : C.card = 2 := by
    have hcopyCard : Fintype.card
        (StatMech.Sharpness.FluxEdgeCopy.Copy
          (lpReplicaCurrentGraph G sites) m) = 5 := by
      calc
        _ = Fintype.card (LPReplicaOrbitCommonSlot G sites q) :=
          Fintype.card_congr
            (lpReplicaProfileCopyEquivCommonSlot G sites q m
              z.1.1.2 z.2.2)
        _ = 5 := hcard
    change (Finset.univ \ K).card = 2
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ K),
      Finset.card_univ, hcopyCard, hthree]
  obtain ⟨e0, he0C⟩ : C.Nonempty := Finset.card_pos.mp (by omega)
  have hsame : ∀ e ∈ C, e.1.1 = e0.1.1 := by
    intro e he
    exact lpReplicaOffdiagDecoratedSource_rank_five_complement_same_edge
      G sites hsite hij q hcard z hthree e he e0 he0C
  have hrow0Disconn : ¬ StatMech.Sharpness.RandomCurrent.connK E
      (lpReplicaRowCopies G sites m
        (lpReplicaToggleRows G sites m P d.1) false)
      lpReplicaCurrentGhost0 lpReplicaCurrentGhost1 := by
    rw [hrow0Eq]
    exact lpReplica_seam_union_parallelCopies_ghost_disconnected
      G sites i m c e0 C hc hsame
  have huniqueK :=
    lpReplicaOffdiagDecoratedSource_rankFive_activeCore_uniqueIncidence
      G sites hsite hij q z hthree
  have huniqueP : ∀ x ∈ P.biUnion (fun f =>
      (StatMech.Sharpness.FluxEdgeCopy.endsM
        (lpReplicaCurrentGraph G sites) m f).toFinset),
      ∃! f, f ∈ P ∧
        x ∈ (StatMech.Sharpness.FluxEdgeCopy.endsM
          (lpReplicaCurrentGraph G sites) m f).toFinset := by
    intro x hx
    obtain ⟨f, hfP, hxf⟩ := Finset.mem_biUnion.mp hx
    refine ⟨f, ⟨hfP, hxf⟩, ?_⟩
    intro g hg
    have hxKsupport : x ∈ K.biUnion (fun b =>
        (StatMech.Sharpness.FluxEdgeCopy.endsM
          (lpReplicaCurrentGraph G sites) m b).toFinset) := by
      exact Finset.mem_biUnion.mpr
        ⟨f, (Finset.mem_sdiff.mp hfP).1, hxf⟩
    obtain ⟨_, _, huniq⟩ := huniqueK x hxKsupport
    exact (huniq g ⟨(Finset.mem_sdiff.mp hg.1).1, hg.2⟩).trans
      (huniq f ⟨(Finset.mem_sdiff.mp hfP).1, hxf⟩).symm
  have hnotStrictRaw :
      ¬ LPReplicaStrictPhysicalDoubleIncidenceRaw G sites m P :=
    lpReplica_not_strictPhysicalDoubleIncidence_matching
      G sites m P huniqueP
  let s : LPReplicaBalancedSelector G sites B (Sj ∆ T) q := {
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
  refine ⟨s, rfl, HEq.rfl, HEq.rfl, ?_, ?_⟩
  · exact heq_of_eq hrow1Eq
  · let y := lpReplicaDecoratedOrbitAtomOfBalancedSelector_left
      G sites i j q s
    refine ⟨y, Or.inl ⟨s, rfl⟩, ?_, rfl⟩
    rw [LPReplicaOffdiagDecoratedTarget.HasStrictPhysicalDoubleIncidence]
    rw [lpReplicaDecoratedOrbitAtomOfBalancedSelector_left_hasStrictPhysicalDoubleIncidence]
    rw [hrow1Eq]
    exact hnotStrictRaw



@[simp] theorem
    lpReplicaOffdiagDecoratedTargetToAggregate_hasStrictPhysicalDoubleIncidence
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (y : LPReplicaOffdiagDecoratedTarget G sites i j q) :
    LPReplicaAggregateDecoratedTarget.HasStrictPhysicalDoubleIncidence
        G sites q
          (lpReplicaOffdiagDecoratedTargetToAggregate G sites i j q y) ↔
      LPReplicaOffdiagDecoratedTarget.HasStrictPhysicalDoubleIncidence
        G sites i j q y := by
  cases y <;> rfl



theorem lpReplicaOffdiagDecoratedTargetToAggregate_ne_strictRouteCandidate
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites) {i j : I}
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
    (y : LPReplicaOffdiagDecoratedTarget G sites i j q)
    (hy : ¬ LPReplicaOffdiagDecoratedTarget.HasStrictPhysicalDoubleIncidence
      G sites i j q y)
    (z : LPReplicaAggregateUnmarkedSaturatedSourceRankFive G sites q)
    (d : ↑(lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidates
      G sites hsite q z)) :
    lpReplicaOffdiagDecoratedTargetToAggregate G sites i j q y ≠
      lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidateTarget
        G sites hsite q hcard z d := by
  intro hcollision
  apply hy
  apply
    (lpReplicaOffdiagDecoratedTargetToAggregate_hasStrictPhysicalDoubleIncidence
      G sites i j q y).mp
  rw [hcollision]
  exact
    lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidateTarget_hasDoubleIncidence
      G sites hsite q hcard z d



def lpReplicaAggregateDecoratedTargetMultiplicityFiberEmbedding
    (G : SimpleGraph V) (sites : I -> V)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (y : LPReplicaAggregateDecoratedTarget G sites q) :
    Fin 2 ↪ LPReplicaAggregateDecoratedTarget G sites q where
  toFun b := ⟨b, y.2⟩
  inj' := by
    intro b c h
    exact congrArg Prod.fst h

@[simp] theorem
    lpReplicaAggregateDecoratedTargetMultiplicityFiberEmbedding_self
    (G : SimpleGraph V) (sites : I -> V)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (y : LPReplicaAggregateDecoratedTarget G sites q) :
    lpReplicaAggregateDecoratedTargetMultiplicityFiberEmbedding
      G sites q y y.1 = y := by
  rfl

@[simp] theorem
    lpReplicaAggregateDecoratedTargetMultiplicityFiberEmbedding_flip
    (G : SimpleGraph V) (sites : I -> V)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (y : LPReplicaAggregateDecoratedTarget G sites q) :
    lpReplicaAggregateDecoratedTargetMultiplicityFiberEmbedding G sites q y
        (lpReplicaAggregateDecoratedTargetFlipMultiplicity G sites q y).1 =
      lpReplicaAggregateDecoratedTargetFlipMultiplicity G sites q y := by
  rfl


theorem
    lpReplicaAggregateDecoratedTargetMultiplicityFiberEmbedding_not_strict
    (G : SimpleGraph V) (sites : I -> V)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (y : LPReplicaAggregateDecoratedTarget G sites q)
    (hy : ¬ LPReplicaAggregateDecoratedTarget.HasStrictPhysicalDoubleIncidence
      G sites q y) (b : Fin 2) :
    ¬ LPReplicaAggregateDecoratedTarget.HasStrictPhysicalDoubleIncidence
      G sites q
        (lpReplicaAggregateDecoratedTargetMultiplicityFiberEmbedding
          G sites q y b) := by
  exact hy



theorem
    lpReplicaAggregateDecoratedTargetMultiplicityFiberEmbedding_ne_strictRouteCandidate
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
    (y : LPReplicaAggregateDecoratedTarget G sites q)
    (hy : ¬ LPReplicaAggregateDecoratedTarget.HasStrictPhysicalDoubleIncidence
      G sites q y) (b : Fin 2)
    (z : LPReplicaAggregateUnmarkedSaturatedSourceRankFive G sites q)
    (d : ↑(lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidates
      G sites hsite q z)) :
    lpReplicaAggregateDecoratedTargetMultiplicityFiberEmbedding
        G sites q y b ≠
      lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidateTarget
        G sites hsite q hcard z d := by
  intro hcollision
  have hb :=
    lpReplicaAggregateDecoratedTargetMultiplicityFiberEmbedding_not_strict
      G sites q y hy b
  apply hb
  rw [hcollision]
  exact
    lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidateTarget_hasDoubleIncidence
      G sites hsite q hcard z d



@[simp] theorem
    lpReplicaAggregateDecoratedTargetMultiplicityFiberEmbedding_key
    (G : SimpleGraph V) (sites : I -> V)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (y : LPReplicaAggregateDecoratedTarget G sites q) (b : Fin 2) :
    (lpReplicaAggregateDecoratedTargetMultiplicityFiberEmbedding
      G sites q y b).2 = y.2 := by
  rfl



theorem
    lpReplicaAggregateDecoratedTargetMultiplicityFiberEmbedding_key_eq_of_eq
    (G : SimpleGraph V) (sites : I -> V)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (y w : LPReplicaAggregateDecoratedTarget G sites q) (b c : Fin 2)
    (h : lpReplicaAggregateDecoratedTargetMultiplicityFiberEmbedding
          G sites q y b =
        lpReplicaAggregateDecoratedTargetMultiplicityFiberEmbedding
          G sites q w c) :
    y.2 = w.2 := by
  change (⟨b, y.2⟩ : LPReplicaAggregateDecoratedTarget G sites q) =
    ⟨c, w.2⟩ at h
  exact (Prod.mk.inj h).2



theorem
    lpReplicaAggregateDecoratedTargetMultiplicityFiberEmbedding_ne_of_key_ne
    (G : SimpleGraph V) (sites : I -> V)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (y w : LPReplicaAggregateDecoratedTarget G sites q)
    (hkey : y.2 ≠ w.2) (b c : Fin 2) :
    lpReplicaAggregateDecoratedTargetMultiplicityFiberEmbedding
        G sites q y b ≠
      lpReplicaAggregateDecoratedTargetMultiplicityFiberEmbedding
        G sites q w c := by
  intro h
  exact hkey
    (lpReplicaAggregateDecoratedTargetMultiplicityFiberEmbedding_key_eq_of_eq
      G sites q y w b c h)



def lpReplicaAggregateDecoratedTargetEmbeddingOfMultiplicityPairCode
    {S : Type*} (G : SimpleGraph V) (sites : I -> V)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (bit : S -> Fin 2)
    (key : S -> LPReplicaAggregateDecoratedTargetBase G sites q)
    (hcode : Function.Injective (fun s => (bit s, key s))) :
    S ↪ LPReplicaAggregateDecoratedTarget G sites q where
  toFun s := ⟨bit s, key s⟩
  inj' := hcode



theorem
    lpReplicaAggregateDecoratedTargetEmbeddingOfMultiplicityPairCode_not_strict
    {S : Type*} (G : SimpleGraph V) (sites : I -> V)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (bit : S -> Fin 2)
    (key : S -> LPReplicaAggregateDecoratedTargetBase G sites q)
    (hcode : Function.Injective (fun s => (bit s, key s)))
    (hnonstrict : ∀ s, ¬
      LPReplicaAggregateDecoratedTarget.HasStrictPhysicalDoubleIncidence
        G sites q ⟨0, key s⟩) (s : S) :
    ¬ LPReplicaAggregateDecoratedTarget.HasStrictPhysicalDoubleIncidence
      G sites q
        (lpReplicaAggregateDecoratedTargetEmbeddingOfMultiplicityPairCode
          G sites q bit key hcode s) := by
  exact hnonstrict s



noncomputable def lpReplicaAggregateRankFiveStrictRouteNeighbors
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
    (z : LPReplicaAggregateUnmarkedSaturatedSourceRankFive G sites q) :
    Finset (LPReplicaAggregateDecoratedTarget G sites q) := by
  classical
  exact Finset.univ.filter fun y =>
    LPReplicaAggregateRankFiveStrictRouteRelated
      G sites hsite q hcard z y

set_option maxHeartbeats 1000000 in



structure LPReplicaAggregateRankFiveSupportedStrictRouteEmbedding
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5) where
  toEmbedding : LPReplicaAggregateUnmarkedSaturatedSourceRankFive G sites q ↪
    LPReplicaAggregateDecoratedTarget G sites q
  related : ∀ z, LPReplicaAggregateRankFiveStrictRouteRelated
    G sites hsite q hcard z (toEmbedding z)


theorem nonempty_lpReplicaAggregateRankFiveSupportedStrictRouteEmbedding
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5) :
    Nonempty (LPReplicaAggregateRankFiveSupportedStrictRouteEmbedding
      G sites hsite q hcard) := by
  classical
  let N := lpReplicaAggregateRankFiveStrictRouteNeighbors
    G sites hsite q hcard
  have hHall : ∀ S : Finset
      (LPReplicaAggregateUnmarkedSaturatedSourceRankFive G sites q),
      S.card ≤ (S.biUnion N).card := by
    intro S
    have h := LPReplicaAggregateRankFiveStrictRouteHall
      G sites hsite q hcard S
    have heq : S.biUnion N = Finset.univ.filter fun target :
        LPReplicaAggregateDecoratedTarget G sites q =>
          ∃ source ∈ S,
            LPReplicaAggregateRankFiveStrictRouteRelated
              G sites hsite q hcard source target := by
      ext y
      simp [N, lpReplicaAggregateRankFiveStrictRouteNeighbors]
    rw [heq]
    exact h
  obtain ⟨move, hmove, hmem⟩ :=
    (Finset.all_card_le_biUnion_card_iff_exists_injective N).mp hHall
  refine ⟨⟨⟨move, hmove⟩, ?_⟩⟩
  intro z
  have hz := hmem z
  simpa only [N, lpReplicaAggregateRankFiveStrictRouteNeighbors,
    Finset.mem_filter, Finset.mem_univ, true_and] using hz


noncomputable def lpReplicaAggregateRankFiveSupportedStrictRouteEmbedding
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5) :
    LPReplicaAggregateRankFiveSupportedStrictRouteEmbedding
      G sites hsite q hcard :=
  Classical.choice
    (nonempty_lpReplicaAggregateRankFiveSupportedStrictRouteEmbedding
      G sites hsite q hcard)



theorem lpReplicaAggregateRankFiveSupportedStrictRouteEmbedding_strict
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
    (z : LPReplicaAggregateUnmarkedSaturatedSourceRankFive G sites q) :
    LPReplicaAggregateDecoratedTarget.HasStrictPhysicalDoubleIncidence
      G sites q
        ((lpReplicaAggregateRankFiveSupportedStrictRouteEmbedding
          G sites hsite q hcard).toEmbedding z) := by
  obtain ⟨d, hd⟩ :=
    (lpReplicaAggregateRankFiveSupportedStrictRouteEmbedding
      G sites hsite q hcard).related z
  rw [← hd]
  exact
    lpReplicaAggregateUnmarkedSaturatedSourceRankFiveStrictRouteCandidateTarget_hasDoubleIncidence
      G sites hsite q hcard z d



def embeddingSumOfDisjointImages {A B C : Type*}
    (f : A ↪ C) (g : B ↪ C) (hdisjoint : ∀ a b, f a ≠ g b) :
    A ⊕ B ↪ C where
  toFun
    | Sum.inl a => f a
    | Sum.inr b => g b
  inj' := by
    intro x y hxy
    cases x with
    | inl a =>
        cases y with
        | inl a' => exact congrArg Sum.inl (f.injective hxy)
        | inr b => exact (hdisjoint a b hxy).elim
    | inr b =>
        cases y with
        | inl a => exact (hdisjoint a b hxy.symm).elim
        | inr b' => exact congrArg Sum.inr (g.injective hxy)



noncomputable def
    lpReplicaAggregateRankFiveCombinedEmbeddingOfNonstrictEmbedding
    {S : Type*} (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
    (handled : S ↪ LPReplicaAggregateDecoratedTarget G sites q)
    (hnonstrict : ∀ s, ¬
      LPReplicaAggregateDecoratedTarget.HasStrictPhysicalDoubleIncidence
        G sites q (handled s)) :
    S ⊕ LPReplicaAggregateUnmarkedSaturatedSourceRankFive G sites q ↪
      LPReplicaAggregateDecoratedTarget G sites q := by
  let strict := lpReplicaAggregateRankFiveSupportedStrictRouteEmbedding
    G sites hsite q hcard
  apply embeddingSumOfDisjointImages handled strict.toEmbedding
  intro s z hcollision
  apply hnonstrict s
  rw [hcollision]
  exact lpReplicaAggregateRankFiveSupportedStrictRouteEmbedding_strict
    G sites hsite q hcard z




noncomputable def lpReplicaOffdiagRankFiveOutputCollisionClass
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (output : LPReplicaOffdiagDecoratedSource G sites i j q ->
      LPReplicaOffdiagDecoratedTarget G sites i j q)
    (y : LPReplicaOffdiagDecoratedTarget G sites i j q) :
    Finset (LPReplicaOffdiagDecoratedSource G sites i j q) := by
  classical
  exact (lpReplicaOffdiagDecoratedSourceCrossTraceFiber G sites i j q
      (lpReplicaOffdiagDecoratedTargetCrossTrace G sites i j q y)).filter
    fun z => output z = y




theorem lpReplicaOffdiagRankFiveOutputCollisionClass_card_le_four
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites) {i j : I} (hij : i ≠ j)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
    (output : LPReplicaOffdiagDecoratedSource G sites i j q ->
      LPReplicaOffdiagDecoratedTarget G sites i j q)
    (y : LPReplicaOffdiagDecoratedTarget G sites i j q) :
    (lpReplicaOffdiagRankFiveOutputCollisionClass
      G sites i j q output y).card ≤ 4 := by
  classical
  exact (Finset.card_le_card (Finset.filter_subset _ _)).trans
    (lpReplicaOffdiagDecoratedSourceCrossTraceFiber_rank_five_card_le_four
      G sites hsite hij q hcard
        (lpReplicaOffdiagDecoratedTargetCrossTrace G sites i j q y))


noncomputable def lpReplicaOffdiagRankFiveOutputCollisionClassLow
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (output : LPReplicaOffdiagDecoratedSource G sites i j q ->
      LPReplicaOffdiagDecoratedTarget G sites i j q)
    (y : LPReplicaOffdiagDecoratedTarget G sites i j q) :
    Finset (LPReplicaOffdiagDecoratedSource G sites i j q) := by
  classical
  exact (lpReplicaOffdiagRankFiveOutputCollisionClass
    G sites i j q output y).filter
      (LPReplicaOffdiagDecoratedSource.IsLowRowRankFive G sites i j q)


noncomputable def lpReplicaOffdiagRankFiveOutputCollisionClassHigh
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (output : LPReplicaOffdiagDecoratedSource G sites i j q ->
      LPReplicaOffdiagDecoratedTarget G sites i j q)
    (y : LPReplicaOffdiagDecoratedTarget G sites i j q) :
    Finset (LPReplicaOffdiagDecoratedSource G sites i j q) := by
  classical
  exact (lpReplicaOffdiagRankFiveOutputCollisionClass
    G sites i j q output y).filter
      (LPReplicaOffdiagDecoratedSource.IsHighRowRankFive G sites i j q)


theorem lpReplicaOffdiagRankFiveOutputCollisionClassLow_card_le_three
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites) {i j : I} (hij : i ≠ j)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
    (output : LPReplicaOffdiagDecoratedSource G sites i j q ->
      LPReplicaOffdiagDecoratedTarget G sites i j q)
    (y : LPReplicaOffdiagDecoratedTarget G sites i j q) :
    (lpReplicaOffdiagRankFiveOutputCollisionClassLow
      G sites i j q output y).card ≤ 3 := by
  classical
  let u := lpReplicaOffdiagDecoratedTargetCrossTrace G sites i j q y
  have hsub : lpReplicaOffdiagRankFiveOutputCollisionClassLow
      G sites i j q output y ⊆
      lpReplicaOffdiagDecoratedSourceCrossTraceFiberLowRowRankFive
        G sites i j q u := by
    intro z hz
    simp only [lpReplicaOffdiagRankFiveOutputCollisionClassLow,
      lpReplicaOffdiagRankFiveOutputCollisionClass,
      lpReplicaOffdiagDecoratedSourceCrossTraceFiberLowRowRankFive,
      Finset.mem_filter] at hz ⊢
    exact ⟨hz.1.1, hz.2⟩
  exact (Finset.card_le_card hsub).trans
    (lpReplicaOffdiagDecoratedSourceCrossTraceFiberLowRowRankFive_card_le_three
      G sites hsite hij q hcard u)


theorem lpReplicaOffdiagRankFiveOutputCollisionClassHigh_card_le_one
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites) {i j : I} (hij : i ≠ j)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
    (output : LPReplicaOffdiagDecoratedSource G sites i j q ->
      LPReplicaOffdiagDecoratedTarget G sites i j q)
    (y : LPReplicaOffdiagDecoratedTarget G sites i j q) :
    (lpReplicaOffdiagRankFiveOutputCollisionClassHigh
      G sites i j q output y).card ≤ 1 := by
  classical
  let u := lpReplicaOffdiagDecoratedTargetCrossTrace G sites i j q y
  have hsub : lpReplicaOffdiagRankFiveOutputCollisionClassHigh
      G sites i j q output y ⊆
      lpReplicaOffdiagDecoratedSourceCrossTraceFiberHighRowRankFive
        G sites i j q u := by
    intro z hz
    simp only [lpReplicaOffdiagRankFiveOutputCollisionClassHigh,
      lpReplicaOffdiagRankFiveOutputCollisionClass,
      lpReplicaOffdiagDecoratedSourceCrossTraceFiberHighRowRankFive,
      Finset.mem_filter] at hz ⊢
    exact ⟨hz.1.1, hz.2⟩
  exact (Finset.card_le_card hsub).trans
    (lpReplicaOffdiagDecoratedSourceCrossTraceFiberHighRowRankFive_card_le_one
      G sites hsite hij q hcard u)

set_option maxHeartbeats 1000000 in



theorem lpReplicaOffdiagRankFiveOutputCollisionClass_eq_low_union_high
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites) {i j : I} (hij : i ≠ j)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
    (output : LPReplicaOffdiagDecoratedSource G sites i j q ->
      LPReplicaOffdiagDecoratedTarget G sites i j q)
    (y : LPReplicaOffdiagDecoratedTarget G sites i j q) : by
      classical
      exact lpReplicaOffdiagRankFiveOutputCollisionClass
          G sites i j q output y =
        (lpReplicaOffdiagRankFiveOutputCollisionClassLow
          G sites i j q output y)
          ∪ (lpReplicaOffdiagRankFiveOutputCollisionClassHigh
            G sites i j q output y) := by
  classical
  let u := lpReplicaOffdiagDecoratedTargetCrossTrace G sites i j q y
  have hsplit :=
    lpReplicaOffdiagDecoratedSourceCrossTraceFiber_rank_five_eq_low_union_high
      G sites hsite hij q hcard u
  ext z
  constructor
  · intro hz
    have hz' := Finset.mem_filter.mp hz
    have hzSplit : z ∈
        lpReplicaOffdiagDecoratedSourceCrossTraceFiberLowOrHighRankFive
          G sites i j q u := by
      rw [← hsplit]
      exact hz'.1
    rcases Finset.mem_union.mp hzSplit with hzLow | hzHigh
    · apply Finset.mem_union_left
      exact Finset.mem_filter.mpr ⟨hz, (Finset.mem_filter.mp hzLow).2⟩
    · apply Finset.mem_union_right
      exact Finset.mem_filter.mpr ⟨hz, (Finset.mem_filter.mp hzHigh).2⟩
  · intro hz
    rcases Finset.mem_union.mp hz with hz | hz
    · exact (Finset.mem_filter.mp hz).1
    · exact (Finset.mem_filter.mp hz).1



theorem
    lpReplicaOffdiagRankFiveOutputCollisionClassLow_card_ge_two_of_three_le
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites) {i j : I} (hij : i ≠ j)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
    (output : LPReplicaOffdiagDecoratedSource G sites i j q ->
      LPReplicaOffdiagDecoratedTarget G sites i j q)
    (y : LPReplicaOffdiagDecoratedTarget G sites i j q)
    (hthree : 3 ≤ (lpReplicaOffdiagRankFiveOutputCollisionClass
      G sites i j q output y).card) :
    2 ≤ (lpReplicaOffdiagRankFiveOutputCollisionClassLow
      G sites i j q output y).card := by
  classical
  have hunion :=
    lpReplicaOffdiagRankFiveOutputCollisionClass_eq_low_union_high
      G sites hsite hij q hcard output y
  have hle : (lpReplicaOffdiagRankFiveOutputCollisionClass
      G sites i j q output y).card ≤
      (lpReplicaOffdiagRankFiveOutputCollisionClassLow
          G sites i j q output y).card +
        (lpReplicaOffdiagRankFiveOutputCollisionClassHigh
          G sites i j q output y).card := by
    rw [hunion]
    exact Finset.card_union_le
      (lpReplicaOffdiagRankFiveOutputCollisionClassLow
        G sites i j q output y)
      (lpReplicaOffdiagRankFiveOutputCollisionClassHigh
        G sites i j q output y)
  have hhigh :=
    lpReplicaOffdiagRankFiveOutputCollisionClassHigh_card_le_one
      G sites hsite hij q hcard output y
  omega

end

end StatMech.Ising

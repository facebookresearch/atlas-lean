/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.Ising.LebowitzPfisterReplicaOrbitRankFour
import Code.Ising.LebowitzPfisterReplicaOrbitPooledTraceFiber
import Code.Ising.LebowitzPfisterReplicaOrbitExactTagSlotMove
import Code.Ising.LebowitzPfisterReplicaOrbitMultiplicityClass
import Code.Ising.LebowitzPfisterReplicaOrbitPairedCutMatching











open Finset
open scoped symmDiff

namespace StatMech.Ising

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

local instance lpReplicaRankFiveDecidableAdj
    (G : SimpleGraph V) (sites : I -> V) :
    DecidableRel (lpReplicaCurrentGraph G sites).Adj :=
  Classical.decRel _


theorem randomCurrent_sources_singleton_eq_ends_toFinset_of_not_isDiag
    {W ι : Type*} [Fintype W] [DecidableEq W]
    [Fintype ι] [DecidableEq ι]
    (ends : ι -> Sym2 W) (c : ι) (hdiag : ¬ (ends c).IsDiag) :
    StatMech.Sharpness.RandomCurrent.sources ends {c} =
      (ends c).toFinset := by
  induction hends : ends c using Sym2.inductionOn with
  | _ x y =>
      have hxy : x ≠ y := by
        intro h
        subst y
        apply hdiag
        rw [hends]
        exact Sym2.mk_isDiag_iff.mpr rfl
      rw [randomCurrent_sources_singleton_of_ends_eq ends c hxy hends]
      simpa only [hends, Sym2.toFinset_mk_eq]



theorem exists_mem_ends_of_connK_of_ne
    {W ι : Type*} [Fintype W] [DecidableEq W]
    [Fintype ι] [DecidableEq ι]
    (ends : ι -> Sym2 W) (S : Finset ι) {a b : W}
    (hab : a ≠ b)
    (hconn : StatMech.Sharpness.RandomCurrent.connK ends S a b) :
    ∃ e ∈ S, a ∈ ends e := by
  have htrans : Relation.TransGen
      (StatMech.Sharpness.RandomCurrent.adjStep ends S) a b :=
    (Relation.reflTransGen_iff_eq_or_transGen.mp hconn).resolve_left hab.symm
  obtain ⟨x, hstep, _⟩ := Relation.TransGen.head'_iff.mp htrans
  exact ⟨hstep.choose, hstep.choose_spec.1,
    hstep.choose_spec.2.1⟩



theorem randomCurrent_connK_insert_parallel_iff
    {W ι : Type*} [Fintype W] [DecidableEq W]
    [Fintype ι] [DecidableEq ι]
    (ends : ι -> Sym2 W) (K : Finset ι) (c e : ι)
    (he : e ∈ K) (hparallel : ends c = ends e) (a b : W) :
    StatMech.Sharpness.RandomCurrent.connK ends (insert c K) a b ↔
      StatMech.Sharpness.RandomCurrent.connK ends K a b := by
  constructor
  · apply Relation.ReflTransGen.mono
    rintro x y ⟨f, hf, hx, hy, hxy⟩
    by_cases hfc : f = c
    · subst f
      exact ⟨e, he, by simpa only [hparallel] using hx,
        by simpa only [hparallel] using hy, hxy⟩
    · exact ⟨f, (Finset.mem_insert.mp hf).resolve_left hfc,
        hx, hy, hxy⟩
  · exact StatMech.GrahamGHS.FourColor.connK_mono
      (Finset.subset_insert c K)



theorem lpReplica_seam_union_parallelCopies_ghost_disconnected
    (G : SimpleGraph V) (sites : I -> V) (i : I)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (c e0 : StatMech.Sharpness.FluxEdgeCopy.Copy
      (lpReplicaCurrentGraph G sites) m)
    (C : Finset (StatMech.Sharpness.FluxEdgeCopy.Copy
      (lpReplicaCurrentGraph G sites) m))
    (hc : c.1.1 = lpReplicaCurrentSeamEdge sites i)
    (hsame : ∀ e ∈ C, e.1.1 = e0.1.1) :
    ¬ StatMech.Sharpness.RandomCurrent.connK
      (StatMech.Sharpness.FluxEdgeCopy.endsM
        (lpReplicaCurrentGraph G sites) m)
      ({c} ∪ C) lpReplicaCurrentGhost0 lpReplicaCurrentGhost1 := by
  classical
  let E := StatMech.Sharpness.FluxEdgeCopy.endsM
    (lpReplicaCurrentGraph G sites) m
  intro hconn
  have hghost : (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V) ≠
      lpReplicaCurrentGhost1 := by
    simp [lpReplicaCurrentGhost0, lpReplicaCurrentGhost1]
  obtain ⟨a, haS, hg0a⟩ := exists_mem_ends_of_connK_of_ne E
    ({c} ∪ C) hghost hconn
  obtain ⟨b, hbS, hg1b⟩ := exists_mem_ends_of_connK_of_ne E
    ({c} ∪ C) hghost.symm
      (StatMech.Sharpness.RandomCurrent.connK_symm E _ hconn)
  have haC : a ∈ C := by
    simp only [Finset.mem_union, Finset.mem_singleton] at haS
    rcases haS with rfl | haC
    · change (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V) ∈ a.1.1 at hg0a
      rw [hc] at hg0a
      simp [lpReplicaCurrentSeamEdge, lpReplicaCurrentLeft,
        lpReplicaCurrentRight, lpReplicaCurrentGhost0] at hg0a
    · exact haC
  have hbC : b ∈ C := by
    simp only [Finset.mem_union, Finset.mem_singleton] at hbS
    rcases hbS with rfl | hbC
    · change (lpReplicaCurrentGhost1 : LPReplicaCurrentVertex V) ∈ b.1.1 at hg1b
      rw [hc] at hg1b
      simp [lpReplicaCurrentSeamEdge, lpReplicaCurrentLeft,
        lpReplicaCurrentRight, lpReplicaCurrentGhost1] at hg1b
    · exact hbC
  have hg0 : (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V) ∈ e0.1.1 := by
    change (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V) ∈ a.1.1 at hg0a
    rw [hsame a haC] at hg0a
    exact hg0a
  have hg1 : (lpReplicaCurrentGhost1 : LPReplicaCurrentVertex V) ∈ e0.1.1 := by
    change (lpReplicaCurrentGhost1 : LPReplicaCurrentVertex V) ∈ b.1.1 at hg1b
    rw [hsame b hbC] at hg1b
    exact hg1b
  have hedge : e0.1.1 = s((lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V),
      lpReplicaCurrentGhost1) :=
    sym2_eq_mk_of_mem_of_mem_of_ne hg0 hg1 hghost
  have hm := SimpleGraph.mem_edgeFinset.mp e0.1.2
  rw [hedge] at hm
  simpa [lpReplicaCurrentGraph, lpReplicaCurrentRel, lpReplicaCurrentGhost0,
    lpReplicaCurrentGhost1] using hm




theorem lpReplicaToggleRows_univ_sdiff_singleton_swapRowsTag
    (G : SimpleGraph V) (sites : I -> V)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (tag : StatMech.Sharpness.FluxEdgeCopy.Copy
      (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag)
    (c : StatMech.Sharpness.FluxEdgeCopy.Copy
      (lpReplicaCurrentGraph G sites) m) :
    lpReplicaToggleRows G sites m (Finset.univ \ {c})
        (lpReplicaSwapRowsTag tag) =
      lpReplicaToggleRows G sites m {c} tag := by
  funext a
  by_cases hac : a = c
  · subst a
    rcases htag : tag c with ⟨row, current⟩
    cases row <;> cases current <;>
      simp [lpReplicaToggleRows, lpReplicaSwapRowsTag, htag]
  · rcases htag : tag a with ⟨row, current⟩
    cases row <;> cases current <;>
      simp [lpReplicaToggleRows, lpReplicaSwapRowsTag, htag, hac]

set_option maxHeartbeats 800000 in




theorem lpReplicaRowGate_compl_singleton_currentSources
    (G : SimpleGraph V) (sites : I -> V)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (B : Finset (LPReplicaCurrentVertex V))
    (tag : StatMech.Sharpness.FluxEdgeCopy.Copy
      (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag)
    (hgate : LPReplicaRowGate G sites m B ∅ tag)
    (c : StatMech.Sharpness.FluxEdgeCopy.Copy
      (lpReplicaCurrentGraph G sites) m)
    (hcurrent : (tag c).2 = false) :
    let E := StatMech.Sharpness.FluxEdgeCopy.endsM
      (lpReplicaCurrentGraph G sites) m
    let P := Finset.univ \ {c}
    StatMech.Sharpness.RandomCurrent.sources E
        (P.filter fun a => (tag a).2 = false) =
          B ∆ StatMech.Sharpness.RandomCurrent.sources E {c} ∧
      StatMech.Sharpness.RandomCurrent.sources E
        (P.filter fun a => (tag a).2 = true) = ∅ := by
  classical
  dsimp only
  let E := StatMech.Sharpness.FluxEdgeCopy.endsM
    (lpReplicaCurrentGraph G sites) m
  let F0 := lpReplicaCurrentCopies G sites m tag false false
  let F1 := lpReplicaCurrentCopies G sites m tag true false
  let T0 := lpReplicaCurrentCopies G sites m tag false true
  let T1 := lpReplicaCurrentCopies G sites m tag true true
  have hFdis : Disjoint F0 F1 := by
    rw [Finset.disjoint_left]
    intro a ha0 ha1
    simp only [F0, F1, lpReplicaCurrentCopies, Finset.mem_filter,
      Finset.mem_univ, true_and] at ha0 ha1
    exact Bool.false_ne_true ((congrArg Prod.fst ha0).symm.trans
      (congrArg Prod.fst ha1))
  have hTdis : Disjoint T0 T1 := by
    rw [Finset.disjoint_left]
    intro a ha0 ha1
    simp only [T0, T1, lpReplicaCurrentCopies, Finset.mem_filter,
      Finset.mem_univ, true_and] at ha0 ha1
    exact Bool.false_ne_true ((congrArg Prod.fst ha0).symm.trans
      (congrArg Prod.fst ha1))
  have hfalseSet : (Finset.univ \ {c}).filter
      (fun a => (tag a).2 = false) = (F0 ∪ F1) \ {c} := by
    ext a
    rcases htag : tag a with ⟨row, current⟩
    cases row <;> cases current <;>
      simp [F0, F1, lpReplicaCurrentCopies, htag]
  have htrueSet : (Finset.univ \ {c}).filter
      (fun a => (tag a).2 = true) = T0 ∪ T1 := by
    ext a
    by_cases hac : a = c
    · subst a
      rcases htag : tag c with ⟨row, current⟩
      cases row <;> cases current <;>
        simp_all [T0, T1, lpReplicaCurrentCopies]
    · rcases htag : tag a with ⟨row, current⟩
      cases row <;> cases current <;>
        simp [T0, T1, lpReplicaCurrentCopies, htag, hac]
  have hcF : c ∈ F0 ∪ F1 := by
    rcases htag : tag c with ⟨row, current⟩
    cases row <;> cases current <;>
      simp_all [F0, F1, lpReplicaCurrentCopies]
  constructor
  · rw [hfalseSet,
      StatMech.GrahamGHS.FourColor.sources_sdiff_of_subset (by
        simpa only [Finset.singleton_subset_iff] using hcF),
      StatMech.GrahamGHS.FourColor.sources_union_of_disjoint hFdis,
      hgate.1, hgate.2.2.2.1]
    simp

  · rw [htrueSet,
      StatMech.GrahamGHS.FourColor.sources_union_of_disjoint hTdis,
      hgate.2.1, hgate.2.2.2.2.1]
    simp




theorem lpReplicaOffdiagDecoratedSource_rank_five_active_card
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites) {i j : I} (hij : i ≠ j)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
    (z : LPReplicaOffdiagDecoratedSource G sites i j q) :
    let d := lpReplicaDecoratedSourceRowGateData G sites i j q z
    let K := lpReplicaCurrentCopies G sites z.1.1.1 d.1 true false
    (K.card = 3 ∧
        (Finset.univ \ K).card = 2 ∧
        StatMech.Sharpness.RandomCurrent.sources
          (StatMech.Sharpness.FluxEdgeCopy.endsM
            (lpReplicaCurrentGraph G sites) z.1.1.1)
          (Finset.univ \ K) = ∅) ∨
      K = Finset.univ := by
  classical
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
        (lpReplicaCurrentGraph G sites) z.1.1.1) = 5 := by
    calc
      _ = Fintype.card (LPReplicaOrbitCommonSlot G sites q) :=
        Fintype.card_congr
          (lpReplicaProfileCopyEquivCommonSlot G sites q z.1.1.1
            z.1.1.2 z.2.2)
      _ = 5 := hcard
  have hKsource : StatMech.Sharpness.RandomCurrent.sources E K = B :=
    d.2.2.2.2.1
  have hKlower : 3 ≤ K.card := by
    have hbound := card_randomCurrent_sources_le_two_mul_card E K
    rw [hKsource, card_lpReplica_offdiagSource sites hsite hij] at hbound
    omega
  have hKupper : K.card ≤ 5 := by
    calc
      K.card ≤ Fintype.card
          (StatMech.Sharpness.FluxEdgeCopy.Copy
            (lpReplicaCurrentGraph G sites) z.1.1.1) := Finset.card_le_univ _
      _ = 5 := hcopyCard
  have hfullSource : StatMech.Sharpness.RandomCurrent.sources E Finset.univ =
      B := by
    have h := lpReplicaRowGate_fullSources G sites z.1.1.1 ∅ B d.1 d.2
    calc
      StatMech.Sharpness.RandomCurrent.sources E Finset.univ = ∅ ∆ B := by
        simpa only [E] using h
      _ = B := by
        ext x
        simp [Finset.mem_symmDiff]
  have hcompSource : StatMech.Sharpness.RandomCurrent.sources E
      (Finset.univ \ K) = ∅ := by
    rw [StatMech.GrahamGHS.FourColor.sources_sdiff_of_subset
      (Finset.subset_univ K), hfullSource, hKsource]
    ext x
    simp [Finset.mem_symmDiff]
  have hKneFour : K.card ≠ 4 := by
    intro hfour
    have hcompCard : (Finset.univ \ K).card = 1 := by
      rw [Finset.card_sdiff_of_subset (Finset.subset_univ K),
        Finset.card_univ, hcopyCard, hfour]
    obtain ⟨c, hc⟩ := Finset.card_eq_one.mp hcompCard
    rw [hc] at hcompSource
    exact (randomCurrent_sources_singleton_nonempty_of_edgeCopy
      G sites z.1.1.1 c).ne_empty hcompSource
  by_cases hthree : K.card = 3
  · left
    refine ⟨hthree, ?_, hcompSource⟩
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ K),
      Finset.card_univ, hcopyCard, hthree]
  · have hfive : K.card = 5 := by omega
    right
    apply Finset.eq_of_subset_of_card_le (Finset.subset_univ K)
    rw [Finset.card_univ, hcopyCard, hfive]



theorem lpReplicaOffdiagDecoratedSource_rank_five_saturated_all_falseCopies
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites) {i j : I} (hij : i ≠ j)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
    (z : LPReplicaOffdiagDecoratedSource G sites i j q)
    (hsat : lpReplicaCurrentCopies G sites z.1.1.1
      (lpReplicaDecoratedSourceRowGateData G sites i j q z).1 true false =
        Finset.univ) :
    ∀ c, (lpReplicaDecoratedSourceRowGateData G sites i j q z).1 c =
      (true, false) := by
  intro c
  have hc : c ∈ lpReplicaCurrentCopies G sites z.1.1.1
      (lpReplicaDecoratedSourceRowGateData G sites i j q z).1 true false := by
    rw [hsat]
    simp
  simpa only [lpReplicaCurrentCopies, Finset.mem_filter, Finset.mem_univ,
    true_and] using hc


theorem lpReplicaOffdiagDecoratedSource_rank_five_saturated_rowMask_eq_univ
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites) {i j : I} (hij : i ≠ j)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
    (z : LPReplicaOffdiagDecoratedSource G sites i j q)
    (hsat : lpReplicaCurrentCopies G sites z.1.1.1
      (lpReplicaDecoratedSourceRowGateData G sites i j q z).1 true false =
        Finset.univ) :
    lpReplicaOrbitFourColorSlotRowMask G sites q
        (lpReplicaOffdiagDecoratedSourceSlotState G sites i j q z) =
      Finset.univ := by
  classical
  let d := lpReplicaDecoratedSourceRowGateData G sites i j q z
  have hall := lpReplicaOffdiagDecoratedSource_rank_five_saturated_all_falseCopies
    G sites hsite hij q hcard z hsat
  ext x
  simp only [lpReplicaOrbitFourColorSlotRowMask, Finset.mem_filter,
    Finset.mem_univ, true_and]
  let c := (lpReplicaProfileCopyEquivCommonSlot G sites q z.1.1.1
    z.1.1.2 z.2.2).symm x
  have hc : d.1 c = (true, false) := hall c
  have htag := lpReplicaOffdiagDecoratedSource_orientedTag_eq_rowGateData
    G sites i j q z
  have hc' := congrFun htag c
  rw [hc] at hc'
  simpa only [lpReplicaOffdiagDecoratedSourceSlotState,
    lpReplicaOrientedFourColorSlotState,
    lpReplicaOrbitFourColorSlotStateOfTag, Equiv.apply_symm_apply,
    Equiv.symm_apply_apply, iff_true] using congrArg Prod.fst hc'


theorem lpReplicaOffdiagDecoratedSource_rank_five_saturated_eq_of_crossTrace_eq
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites) {i j : I} (hij : i ≠ j)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
    (z w : LPReplicaOffdiagDecoratedSource G sites i j q)
    (hsatZ : lpReplicaCurrentCopies G sites z.1.1.1
      (lpReplicaDecoratedSourceRowGateData G sites i j q z).1 true false =
        Finset.univ)
    (hsatW : lpReplicaCurrentCopies G sites w.1.1.1
      (lpReplicaDecoratedSourceRowGateData G sites i j q w).1 true false =
        Finset.univ)
    (htrace : lpReplicaOffdiagDecoratedSourceCrossTrace G sites i j q z =
      lpReplicaOffdiagDecoratedSourceCrossTrace G sites i j q w) : z = w := by
  apply lpReplicaOffdiagDecoratedSourceSlotState_injective G sites i j q
  rw [lpReplicaOrbitFourColorSlotState_eq_iff_crossNormalize_eq_and_rowMask_eq]
  exact ⟨htrace,
    (lpReplicaOffdiagDecoratedSource_rank_five_saturated_rowMask_eq_univ
      G sites hsite hij q hcard z hsatZ).trans
      (lpReplicaOffdiagDecoratedSource_rank_five_saturated_rowMask_eq_univ
        G sites hsite hij q hcard w hsatW).symm⟩




theorem lpReplicaOffdiagDecoratedSource_rank_five_complement_tag_constant
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites) {i j : I} (hij : i ≠ j)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
    (z : LPReplicaOffdiagDecoratedSource G sites i j q)
    (hthree : (lpReplicaCurrentCopies G sites z.1.1.1
      (lpReplicaDecoratedSourceRowGateData G sites i j q z).1
        true false).card = 3) :
    let d := lpReplicaDecoratedSourceRowGateData G sites i j q z
    let K := lpReplicaCurrentCopies G sites z.1.1.1 d.1 true false
    ∀ c ∈ Finset.univ \ K, ∀ e ∈ Finset.univ \ K,
      d.1 c = d.1 e := by
  classical
  dsimp only
  let d := lpReplicaDecoratedSourceRowGateData G sites i j q z
  let K := lpReplicaCurrentCopies G sites z.1.1.1 d.1 true false
  let C := Finset.univ \ K
  let E := StatMech.Sharpness.FluxEdgeCopy.endsM
    (lpReplicaCurrentGraph G sites) z.1.1.1
  have hcopyCard : Fintype.card
      (StatMech.Sharpness.FluxEdgeCopy.Copy
        (lpReplicaCurrentGraph G sites) z.1.1.1) = 5 := by
    calc
      _ = Fintype.card (LPReplicaOrbitCommonSlot G sites q) :=
        Fintype.card_congr
          (lpReplicaProfileCopyEquivCommonSlot G sites q z.1.1.1
            z.1.1.2 z.2.2)
      _ = 5 := hcard
  have hCcard : C.card = 2 := by
    have hKcard : K.card = 3 := by
      simpa only [K, d] using hthree
    change (Finset.univ \ K).card = 2
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ K),
      Finset.card_univ, hcopyCard, hKcard]
  intro c hc e he
  change c ∈ C at hc
  change e ∈ C at he
  by_contra htag
  have hce : c ≠ e := by
    intro h
    exact htag (congrArg d.1 h)
  have hCeq : C = {c, e} := by
    obtain ⟨x, y, hxy, hCxy⟩ := Finset.card_eq_two.mp hCcard
    have hcxy : c = x ∨ c = y := by
      rw [hCxy] at hc
      simpa only [Finset.mem_insert, Finset.mem_singleton] using hc
    have hexy : e = x ∨ e = y := by
      rw [hCxy] at he
      simpa only [Finset.mem_insert, Finset.mem_singleton] using he
    rcases hcxy with rfl | rfl <;> rcases hexy with rfl | rfl
    · exact False.elim (hce rfl)
    · simpa only [hCxy]
    · simpa only [hCxy, Finset.pair_comm]
    · exact False.elim (hce rfl)
  rcases hdc : d.1 c with ⟨row, current⟩
  let F := lpReplicaCurrentCopies G sites z.1.1.1 d.1 row current
  have hcF : c ∈ F := by
    simp only [F, lpReplicaCurrentCopies, Finset.mem_filter,
      Finset.mem_univ, true_and, hdc]
  have hneActive : (row, current) ≠ (true, false) := by
    intro hactive
    have hcK : c ∈ K := by
      simp only [K, lpReplicaCurrentCopies, Finset.mem_filter,
        Finset.mem_univ, true_and]
      exact hdc.trans hactive
    exact (Finset.mem_sdiff.mp hc).2 hcK
  have hFsub : F ⊆ C := by
    intro a ha
    have hatag : d.1 a = (row, current) := by
      simpa only [F, lpReplicaCurrentCopies, Finset.mem_filter,
        Finset.mem_univ, true_and] using ha
    apply Finset.mem_sdiff.mpr
    refine ⟨Finset.mem_univ a, ?_⟩
    intro haK
    have haActive : d.1 a = (true, false) := by
      simpa only [K, lpReplicaCurrentCopies, Finset.mem_filter,
        Finset.mem_univ, true_and] using haK
    exact hneActive (hatag.symm.trans haActive)
  have heNotF : e ∉ F := by
    intro heF
    have hetag : d.1 e = (row, current) := by
      simpa only [F, lpReplicaCurrentCopies, Finset.mem_filter,
        Finset.mem_univ, true_and] using heF
    exact htag (hdc.trans hetag.symm)
  have hF : F = {c} := by
    ext a
    constructor
    · intro ha
      have haC := hFsub ha
      rw [hCeq] at haC
      simp only [Finset.mem_insert, Finset.mem_singleton] at haC
      rcases haC with rfl | rfl
      · simp
      · exact False.elim (heNotF ha)
    · intro ha
      simp only [Finset.mem_singleton] at ha
      subst a
      exact hcF
  have hFsource : StatMech.Sharpness.RandomCurrent.sources E F = ∅ := by
    cases row <;> cases current
    · simpa only [E, F] using d.2.1
    · simpa only [E, F] using d.2.2.1
    · exact False.elim (hneActive rfl)
    · simpa only [E, F] using d.2.2.2.2.2.1
  rw [hF] at hFsource
  exact (randomCurrent_sources_singleton_nonempty_of_edgeCopy
    G sites z.1.1.1 c).ne_empty hFsource



theorem lpReplicaOffdiagDecoratedSource_rank_five_complement_same_edge
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites) {i j : I} (hij : i ≠ j)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
    (z : LPReplicaOffdiagDecoratedSource G sites i j q)
    (hthree : (lpReplicaCurrentCopies G sites z.1.1.1
      (lpReplicaDecoratedSourceRowGateData G sites i j q z).1
        true false).card = 3) :
    let d := lpReplicaDecoratedSourceRowGateData G sites i j q z
    let K := lpReplicaCurrentCopies G sites z.1.1.1 d.1 true false
    ∀ c ∈ Finset.univ \ K, ∀ e ∈ Finset.univ \ K,
      c.1.1 = e.1.1 := by
  classical
  dsimp only
  let d := lpReplicaDecoratedSourceRowGateData G sites i j q z
  let K := lpReplicaCurrentCopies G sites z.1.1.1 d.1 true false
  let C := Finset.univ \ K
  let E := StatMech.Sharpness.FluxEdgeCopy.endsM
    (lpReplicaCurrentGraph G sites) z.1.1.1
  have hcopyCard : Fintype.card
      (StatMech.Sharpness.FluxEdgeCopy.Copy
        (lpReplicaCurrentGraph G sites) z.1.1.1) = 5 := by
    calc
      _ = Fintype.card (LPReplicaOrbitCommonSlot G sites q) :=
        Fintype.card_congr
          (lpReplicaProfileCopyEquivCommonSlot G sites q z.1.1.1
            z.1.1.2 z.2.2)
      _ = 5 := hcard
  have hKcard : K.card = 3 := by
    simpa only [K, d] using hthree
  have hCcard : C.card = 2 := by
    change (Finset.univ \ K).card = 2
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ K),
      Finset.card_univ, hcopyCard, hKcard]
  have hCsource : StatMech.Sharpness.RandomCurrent.sources E C = ∅ := by
    have hsplit := lpReplicaOffdiagDecoratedSource_rank_five_active_card
      G sites hsite hij q hcard z
    dsimp only at hsplit
    rcases hsplit with hsmall | hfull
    · simpa only [E, C, K, d] using hsmall.2.2
    · have hfull' : K = Finset.univ := by
        simpa only [K, d] using hfull
      have : K.card = 5 := by
        rw [hfull', Finset.card_univ, hcopyCard]
      omega
  intro c hc e he
  change c ∈ C at hc
  change e ∈ C at he
  by_cases hce : c = e
  · exact congrArg (fun a => a.1.1) hce
  have hCeq : C = {c, e} := by
    obtain ⟨x, y, hxy, hCxy⟩ := Finset.card_eq_two.mp hCcard
    have hcxy : c = x ∨ c = y := by
      rw [hCxy] at hc
      simpa only [Finset.mem_insert, Finset.mem_singleton] using hc
    have hexy : e = x ∨ e = y := by
      rw [hCxy] at he
      simpa only [Finset.mem_insert, Finset.mem_singleton] using he
    rcases hcxy with rfl | rfl <;> rcases hexy with rfl | rfl
    · exact False.elim (hce rfl)
    · simpa only [hCxy]
    · simpa only [hCxy, Finset.pair_comm]
    · exact False.elim (hce rfl)
  have hpairSource : StatMech.Sharpness.RandomCurrent.sources E {c, e} = ∅ := by
    rw [← hCeq]
    exact hCsource
  have hdisjoint : Disjoint ({c} : Finset _) {e} := by
    simp [hce]
  have hsingleSymm :
      StatMech.Sharpness.RandomCurrent.sources E {c} ∆
        StatMech.Sharpness.RandomCurrent.sources E {e} = ∅ := by
    calc
      _ = StatMech.Sharpness.RandomCurrent.sources E ({c} ∪ {e}) :=
        (StatMech.GrahamGHS.FourColor.sources_union_of_disjoint
          hdisjoint).symm
      _ = StatMech.Sharpness.RandomCurrent.sources E {c, e} := by
        congr 2
      _ = ∅ := hpairSource
  have hsingle : StatMech.Sharpness.RandomCurrent.sources E {c} =
      StatMech.Sharpness.RandomCurrent.sources E {e} :=
    Finset.symmDiff_eq_empty.mp hsingleSymm
  have hfin : (E c).toFinset = (E e).toFinset := by
    rw [← randomCurrent_sources_singleton_eq_ends_toFinset_of_not_isDiag
        E c,
      ← randomCurrent_sources_singleton_eq_ends_toFinset_of_not_isDiag E e]
    · exact hsingle
    · exact StatMech.Sharpness.FluxEdgeCopy.endsM_not_isDiag
        (lpReplicaCurrentGraph G sites) z.1.1.1 e
    · exact StatMech.Sharpness.FluxEdgeCopy.endsM_not_isDiag
        (lpReplicaCurrentGraph G sites) z.1.1.1 c
  have hedge : E c = E e := by
    apply Sym2.ext
    intro x
    rw [← Sym2.mem_toFinset, ← Sym2.mem_toFinset, hfin]
  simpa only [E, StatMech.Sharpness.FluxEdgeCopy.endsM] using hedge



theorem lpReplicaOffdiagDecoratedSource_rank_five_complement_is_tagClass
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites) {i j : I} (hij : i ≠ j)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
    (z : LPReplicaOffdiagDecoratedSource G sites i j q)
    (hthree : (lpReplicaCurrentCopies G sites z.1.1.1
      (lpReplicaDecoratedSourceRowGateData G sites i j q z).1
        true false).card = 3) :
    let d := lpReplicaDecoratedSourceRowGateData G sites i j q z
    let K := lpReplicaCurrentCopies G sites z.1.1.1 d.1 true false
    ∃ row current, (row, current) ≠ (true, false) ∧
      lpReplicaCurrentCopies G sites z.1.1.1 d.1 row current =
        Finset.univ \ K := by
  classical
  dsimp only
  let d := lpReplicaDecoratedSourceRowGateData G sites i j q z
  let K := lpReplicaCurrentCopies G sites z.1.1.1 d.1 true false
  let C := Finset.univ \ K
  have hcopyCard : Fintype.card
      (StatMech.Sharpness.FluxEdgeCopy.Copy
        (lpReplicaCurrentGraph G sites) z.1.1.1) = 5 := by
    calc
      _ = Fintype.card (LPReplicaOrbitCommonSlot G sites q) :=
        Fintype.card_congr
          (lpReplicaProfileCopyEquivCommonSlot G sites q z.1.1.1
            z.1.1.2 z.2.2)
      _ = 5 := hcard
  have hKcard : K.card = 3 := by
    simpa only [K, d] using hthree
  have hCcard : C.card = 2 := by
    change (Finset.univ \ K).card = 2
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ K),
      Finset.card_univ, hcopyCard, hKcard]
  have hCnonempty : C.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨c, hc⟩ := hCnonempty
  rcases hdc : d.1 c with ⟨row, current⟩
  refine ⟨row, current, ?_, ?_⟩
  · intro hactive
    have hcK : c ∈ K := by
      simp only [K, lpReplicaCurrentCopies, Finset.mem_filter,
        Finset.mem_univ, true_and]
      exact hdc.trans hactive
    exact (Finset.mem_sdiff.mp hc).2 hcK
  · apply Finset.Subset.antisymm
    · intro a ha
      apply Finset.mem_sdiff.mpr
      refine ⟨Finset.mem_univ a, ?_⟩
      intro haK
      have haActive : d.1 a = (true, false) := by
        simpa only [K, lpReplicaCurrentCopies, Finset.mem_filter,
          Finset.mem_univ, true_and] using haK
      have haTag : d.1 a = (row, current) := by
        simpa only [lpReplicaCurrentCopies, Finset.mem_filter,
          Finset.mem_univ, true_and] using ha
      exact (show (row, current) ≠ (true, false) from
        fun h => (Finset.mem_sdiff.mp hc).2 (by
          simp only [K, lpReplicaCurrentCopies, Finset.mem_filter,
            Finset.mem_univ, true_and]
          exact hdc.trans h)) (haTag.symm.trans haActive)
    · intro a ha
      have hconst :=
        lpReplicaOffdiagDecoratedSource_rank_five_complement_tag_constant
          G sites hsite hij q hcard z hthree a ha c hc
      simp only [lpReplicaCurrentCopies, Finset.mem_filter,
        Finset.mem_univ, true_and]
      exact hconst.trans hdc

set_option maxHeartbeats 1500000 in



theorem lpReplicaOffdiagDecoratedSource_rank_five_rowMask_eq_activeSlots
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites) {i j : I} (hij : i ≠ j)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
    (z : LPReplicaOffdiagDecoratedSource G sites i j q)
    (hthree : (lpReplicaCurrentCopies G sites z.1.1.1
      (lpReplicaDecoratedSourceRowGateData G sites i j q z).1
        true false).card = 3)
    (c : StatMech.Sharpness.FluxEdgeCopy.Copy
      (lpReplicaCurrentGraph G sites) z.1.1.1)
    (hcC : c ∈ Finset.univ \ lpReplicaCurrentCopies G sites z.1.1.1
      (lpReplicaDecoratedSourceRowGateData G sites i j q z).1 true false)
    (hctag : (lpReplicaDecoratedSourceRowGateData G sites i j q z).1 c =
      (false, false)) :
    lpReplicaOrbitFourColorSlotRowMask G sites q
        (lpReplicaOffdiagDecoratedSourceSlotState G sites i j q z) =
      lpReplicaOrbitCommonSlotsOfCopies G sites q z.1.1.1
        z.1.1.2 z.2.2
        (lpReplicaCurrentCopies G sites z.1.1.1
          (lpReplicaDecoratedSourceRowGateData G sites i j q z).1
          true false) := by
  classical
  let d := lpReplicaDecoratedSourceRowGateData G sites i j q z
  let K := lpReplicaCurrentCopies G sites z.1.1.1 d.1 true false
  let C := Finset.univ \ K
  have hconst : ∀ a ∈ C, d.1 a = d.1 c := by
    intro a ha
    exact lpReplicaOffdiagDecoratedSource_rank_five_complement_tag_constant
      G sites hsite hij q hcard z hthree a ha c hcC
  have hnoTrueTrue (a) : d.1 a ≠ (true, true) := by
    intro ha
    have haNotK : a ∉ K := by
      intro haK
      have haActive : d.1 a = (true, false) := by
        simpa only [K, lpReplicaCurrentCopies, Finset.mem_filter,
          Finset.mem_univ, true_and] using haK
      exact Bool.false_ne_true
        (congrArg Prod.snd (haActive.symm.trans ha))
    have haC : a ∈ C := Finset.mem_sdiff.mpr ⟨Finset.mem_univ a, haNotK⟩
    have h := hconst a haC
    rw [ha, hctag] at h
    simpa using congrArg Prod.fst h
  have hrow1 : lpReplicaRowCopies G sites z.1.1.1 d.1 true = K := by
    ext a
    rcases ha : d.1 a with ⟨row, current⟩
    cases row <;> cases current <;>
      simp [lpReplicaRowCopies, K, lpReplicaCurrentCopies, ha]
    exact False.elim (hnoTrueTrue a ha)
  have hsourceTag :=
    lpReplicaOffdiagDecoratedSource_orientedTag_eq_rowGateData
      G sites i j q z
  change lpReplicaOrbitFourColorSlotRowMask G sites q
      (lpReplicaOrbitFourColorSlotStateOfTag G sites q z.1.1.1
        z.1.1.2 z.2.2 _) = _
  rw [hsourceTag,
    lpReplicaOrbitFourColorSlotRowMask_stateOfTag, hrow1]



theorem lpReplicaOffdiagDecoratedSource_rank_five_rowMask_card_eq_three
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites) {i j : I} (hij : i ≠ j)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
    (z : LPReplicaOffdiagDecoratedSource G sites i j q)
    (hthree : (lpReplicaCurrentCopies G sites z.1.1.1
      (lpReplicaDecoratedSourceRowGateData G sites i j q z).1
        true false).card = 3)
    (c : StatMech.Sharpness.FluxEdgeCopy.Copy
      (lpReplicaCurrentGraph G sites) z.1.1.1)
    (hcC : c ∈ Finset.univ \ lpReplicaCurrentCopies G sites z.1.1.1
      (lpReplicaDecoratedSourceRowGateData G sites i j q z).1 true false)
    (hctag : (lpReplicaDecoratedSourceRowGateData G sites i j q z).1 c =
      (false, false)) :
    (lpReplicaOrbitFourColorSlotRowMask G sites q
      (lpReplicaOffdiagDecoratedSourceSlotState G sites i j q z)).card = 3 := by
  rw [lpReplicaOffdiagDecoratedSource_rank_five_rowMask_eq_activeSlots
    G sites hsite hij q hcard z hthree c hcC hctag,
    lpReplicaOrbitCommonSlotsOfCopies, Finset.card_map, hthree]



theorem lpReplicaOffdiagDecoratedSource_rank_five_crossTrace_edge_of_inactive
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites) {i j : I} (hij : i ≠ j)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
    (z : LPReplicaOffdiagDecoratedSource G sites i j q)
    (hthree : (lpReplicaCurrentCopies G sites z.1.1.1
      (lpReplicaDecoratedSourceRowGateData G sites i j q z).1
        true false).card = 3)
    (c e : StatMech.Sharpness.FluxEdgeCopy.Copy
      (lpReplicaCurrentGraph G sites) z.1.1.1)
    (hcC : c ∈ Finset.univ \ lpReplicaCurrentCopies G sites z.1.1.1
      (lpReplicaDecoratedSourceRowGateData G sites i j q z).1 true false)
    (hctag : (lpReplicaDecoratedSourceRowGateData G sites i j q z).1 c =
      (false, false))
    (heC : e ∈ Finset.univ \ lpReplicaCurrentCopies G sites z.1.1.1
      (lpReplicaDecoratedSourceRowGateData G sites i j q z).1 true false) :
    lpReplicaOrbitFourColorSlotEdge G sites q
        (lpReplicaOffdiagDecoratedSourceCrossTrace G sites i j q z)
        (lpReplicaProfileCopyEquivCommonSlot G sites q z.1.1.1
          z.1.1.2 z.2.2 e) = e.1 := by
  let state := lpReplicaOffdiagDecoratedSourceSlotState G sites i j q z
  let slot := lpReplicaProfileCopyEquivCommonSlot G sites q z.1.1.1
    z.1.1.2 z.2.2 e
  have hmask := lpReplicaOffdiagDecoratedSource_rank_five_rowMask_eq_activeSlots
    G sites hsite hij q hcard z hthree c hcC hctag
  have hslot : slot ∉ lpReplicaOrbitFourColorSlotRowMask G sites q state := by
    rw [hmask, mem_lpReplicaOrbitCommonSlotsOfCopies_iff]
    simpa only [slot, Equiv.symm_apply_apply] using
      (Finset.mem_sdiff.mp heC).2
  unfold lpReplicaOffdiagDecoratedSourceCrossTrace
    lpReplicaOrbitFourColorSlotCrossNormalize
  rw [lpReplicaOrbitFourColorSlotEdge_crossToggle_of_not_mem
    G sites q _ state slot hslot]
  exact lpReplicaOrbitFourColorSlotEdge_stateOfTag_copy
    G sites q z.1.1.1 z.1.1.2 z.2.2 _ e




theorem lpReplica_threeCopyOffdiag_endpointSupport
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites) {i j : I} (hij : i ≠ j)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (K : Finset (StatMech.Sharpness.FluxEdgeCopy.Copy
      (lpReplicaCurrentGraph G sites) m))
    (hKcard : K.card = 3)
    (hsource : StatMech.Sharpness.RandomCurrent.sources
      (StatMech.Sharpness.FluxEdgeCopy.endsM
        (lpReplicaCurrentGraph G sites) m) K =
      lpMatchingSeamSource
            (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i ∆
          lpMatchingSeamSource
            (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j ∆
          lpMatchingGhostSource
            (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
            lpReplicaCurrentGhost1) :
    let E := StatMech.Sharpness.FluxEdgeCopy.endsM
      (lpReplicaCurrentGraph G sites) m
    (K.biUnion fun c => (E c).toFinset) =
      lpMatchingSeamSource
            (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i ∆
          lpMatchingSeamSource
            (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j ∆
          lpMatchingGhostSource
            (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
            lpReplicaCurrentGhost1 := by
  classical
  dsimp only
  let E := StatMech.Sharpness.FluxEdgeCopy.endsM
    (lpReplicaCurrentGraph G sites) m
  let support : Finset (LPReplicaCurrentVertex V) :=
    K.biUnion fun c => (E c).toFinset
  have hsupportCard : support.card ≤ 6 := by
    calc
      support.card ≤ ∑ c ∈ K, (E c).toFinset.card :=
        Finset.card_biUnion_le
      _ ≤ ∑ _c ∈ K, 2 := by
        apply Finset.sum_le_sum
        intro c _
        rw [Sym2.card_toFinset]
        split <;> omega
      _ = 6 := by simp [hKcard]
  have hsubset :
      lpMatchingSeamSource
            (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i ∆
          lpMatchingSeamSource
            (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j ∆
          lpMatchingGhostSource
            (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
            lpReplicaCurrentGhost1 ⊆ support := by
    rw [← hsource]
    exact randomCurrent_sources_subset_endpointSupport E K
  have hoffdiagCard := card_lpReplica_offdiagSource sites hsite hij
  have heq :
      lpMatchingSeamSource
            (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i ∆
          lpMatchingSeamSource
            (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j ∆
          lpMatchingGhostSource
            (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
            lpReplicaCurrentGhost1 = support := by
    apply Finset.eq_of_subset_of_card_le hsubset
    omega
  exact heq.symm



theorem lpReplica_threeCopyOffdiag_edge_injective
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites) {i j : I} (hij : i ≠ j)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (K : Finset (StatMech.Sharpness.FluxEdgeCopy.Copy
      (lpReplicaCurrentGraph G sites) m))
    (hKcard : K.card = 3)
    (hsource : StatMech.Sharpness.RandomCurrent.sources
      (StatMech.Sharpness.FluxEdgeCopy.endsM
        (lpReplicaCurrentGraph G sites) m) K =
      lpMatchingSeamSource
            (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i ∆
          lpMatchingSeamSource
            (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j ∆
          lpMatchingGhostSource
            (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
            lpReplicaCurrentGhost1) :
    Set.InjOn (fun c : StatMech.Sharpness.FluxEdgeCopy.Copy
      (lpReplicaCurrentGraph G sites) m => c.1.1) K := by
  classical
  intro c hc e he hedge
  by_contra hce
  let E := StatMech.Sharpness.FluxEdgeCopy.endsM
    (lpReplicaCurrentGraph G sites) m
  let R := K.erase c
  have heR : e ∈ R := Finset.mem_erase.mpr ⟨Ne.symm hce, he⟩
  have hEcEe : E c = E e := by
    simpa only [E, StatMech.Sharpness.FluxEdgeCopy.endsM] using hedge
  have hsupportSub : (K.biUnion fun a => (E a).toFinset) ⊆
      R.biUnion fun a => (E a).toFinset := by
    intro x hx
    obtain ⟨a, haK, hxa⟩ := Finset.mem_biUnion.mp hx
    by_cases hac : a = c
    · subst a
      apply Finset.mem_biUnion.mpr
      exact ⟨e, heR, by simpa only [hEcEe] using hxa⟩
    · apply Finset.mem_biUnion.mpr
      exact ⟨a, Finset.mem_erase.mpr ⟨hac, haK⟩, hxa⟩
  have hRcard : R.card = 2 := by
    change (K.erase c).card = 2
    rw [Finset.card_erase_of_mem hc, hKcard]
  have hsupportCard : (K.biUnion fun a => (E a).toFinset).card ≤ 4 := by
    calc
      _ ≤ (R.biUnion fun a => (E a).toFinset).card :=
        Finset.card_le_card hsupportSub
      _ ≤ ∑ a ∈ R, (E a).toFinset.card := Finset.card_biUnion_le
      _ ≤ ∑ _a ∈ R, 2 := by
        apply Finset.sum_le_sum
        intro a _
        rw [Sym2.card_toFinset]
        split <;> omega
      _ = 4 := by simp [hRcard]
  have hsupport := lpReplica_threeCopyOffdiag_endpointSupport
    G sites hsite hij m K hKcard hsource
  have hBcard := card_lpReplica_offdiagSource sites hsite hij
  dsimp only at hsupport
  rw [hsupport, hBcard] at hsupportCard
  omega



theorem lpReplicaOffdiagDecoratedSource_rank_five_crossTrace_edge_injOn_active
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites) {i j : I} (hij : i ≠ j)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
    (z : LPReplicaOffdiagDecoratedSource G sites i j q)
    (hthree : (lpReplicaCurrentCopies G sites z.1.1.1
      (lpReplicaDecoratedSourceRowGateData G sites i j q z).1
        true false).card = 3)
    (c0 : StatMech.Sharpness.FluxEdgeCopy.Copy
      (lpReplicaCurrentGraph G sites) z.1.1.1)
    (hc0C : c0 ∈ Finset.univ \ lpReplicaCurrentCopies G sites z.1.1.1
      (lpReplicaDecoratedSourceRowGateData G sites i j q z).1 true false)
    (hc0tag : (lpReplicaDecoratedSourceRowGateData G sites i j q z).1 c0 =
      (false, false)) :
    Set.InjOn (lpReplicaOrbitFourColorSlotEdge G sites q
      (lpReplicaOffdiagDecoratedSourceCrossTrace G sites i j q z))
      (lpReplicaOrbitCommonSlotsOfCopies G sites q z.1.1.1
        z.1.1.2 z.2.2
        (lpReplicaCurrentCopies G sites z.1.1.1
          (lpReplicaDecoratedSourceRowGateData G sites i j q z).1
          true false)) := by
  classical
  let d := lpReplicaDecoratedSourceRowGateData G sites i j q z
  let K := lpReplicaCurrentCopies G sites z.1.1.1 d.1 true false
  let state := lpReplicaOffdiagDecoratedSourceSlotState G sites i j q z
  let E := lpReplicaProfileCopyEquivCommonSlot G sites q z.1.1.1
    z.1.1.2 z.2.2
  have hmask : lpReplicaOrbitFourColorSlotRowMask G sites q state =
      lpReplicaOrbitCommonSlotsOfCopies G sites q z.1.1.1
        z.1.1.2 z.2.2 K :=
    lpReplicaOffdiagDecoratedSource_rank_five_rowMask_eq_activeSlots
      G sites hsite hij q hcard z hthree c0 hc0C hc0tag
  have hKsource : StatMech.Sharpness.RandomCurrent.sources
      (StatMech.Sharpness.FluxEdgeCopy.endsM
        (lpReplicaCurrentGraph G sites) z.1.1.1) K =
      lpMatchingSeamSource
            (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i ∆
          lpMatchingSeamSource
            (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j ∆
          lpMatchingGhostSource
            (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
            lpReplicaCurrentGhost1 := by
    exact d.2.2.2.2.1
  have hrawInj := lpReplica_threeCopyOffdiag_edge_injective
    G sites hsite hij z.1.1.1 K (by simpa only [K, d] using hthree) hKsource
  intro x hx y hy hedge
  let cx := E.symm x
  let cy := E.symm y
  have hcxK : cx ∈ K := by
    exact (mem_lpReplicaOrbitCommonSlotsOfCopies_iff
      G sites q z.1.1.1 z.1.1.2 z.2.2 K x).mp hx
  have hcyK : cy ∈ K := by
    exact (mem_lpReplicaOrbitCommonSlotsOfCopies_iff
      G sites q z.1.1.1 z.1.1.2 z.2.2 K y).mp hy
  have hxmask : x ∈ lpReplicaOrbitFourColorSlotRowMask G sites q state := by
    rw [hmask]
    exact hx
  have hymask : y ∈ lpReplicaOrbitFourColorSlotRowMask G sites q state := by
    rw [hmask]
    exact hy
  have hstateEdge (a : LPReplicaOrbitCommonSlot G sites q) :
      lpReplicaOrbitFourColorSlotEdge G sites q state a = (E.symm a).1 := by
    let ca := E.symm a
    have h := lpReplicaOrbitFourColorSlotEdge_stateOfTag_copy
      G sites q z.1.1.1 z.1.1.2 z.2.2
        (lpReplicaOrientedFourColorTag G sites ∅
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
                  lpReplicaCurrentGhost1) q z)) ca
    simpa only [state, lpReplicaOffdiagDecoratedSourceSlotState,
      lpReplicaOrientedFourColorSlotState, ca, E,
      Equiv.apply_symm_apply] using h
  have hxnorm := lpReplicaOrbitFourColorSlotEdge_crossToggle_of_mem
    G sites q (lpReplicaOrbitFourColorSlotRowMask G sites q state)
      state x hxmask
  have hynorm := lpReplicaOrbitFourColorSlotEdge_crossToggle_of_mem
    G sites q (lpReplicaOrbitFourColorSlotRowMask G sites q state)
      state y hymask
  have hreflect : lpReplicaCurrentEdgeReflect G sites cx.1 =
      lpReplicaCurrentEdgeReflect G sites cy.1 := by
    calc
      _ = lpReplicaOrbitFourColorSlotEdge G sites q
          (lpReplicaOffdiagDecoratedSourceCrossTrace G sites i j q z) x := by
        simpa only [lpReplicaOffdiagDecoratedSourceCrossTrace,
          lpReplicaOrbitFourColorSlotCrossNormalize, state, cx,
          hstateEdge] using hxnorm.symm
      _ = lpReplicaOrbitFourColorSlotEdge G sites q
          (lpReplicaOffdiagDecoratedSourceCrossTrace G sites i j q z) y := hedge
      _ = _ := by
        simpa only [lpReplicaOffdiagDecoratedSourceCrossTrace,
          lpReplicaOrbitFourColorSlotCrossNormalize, state, cy,
          hstateEdge] using hynorm
  have hedgeFin : cx.1 = cy.1 :=
    (lpReplicaCurrentEdgeReflect_involutive G sites).injective hreflect
  have hcxy : cx = cy := hrawInj hcxK hcyK
    (congrArg Subtype.val hedgeFin)
  exact E.symm.injective hcxy

set_option maxHeartbeats 800000 in



theorem lpReplicaOffdiagDecoratedSource_rank_five_inactivePair_mem_eligible
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites) {i j : I} (hij : i ≠ j)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
    (z : LPReplicaOffdiagDecoratedSource G sites i j q)
    (hthree : (lpReplicaCurrentCopies G sites z.1.1.1
      (lpReplicaDecoratedSourceRowGateData G sites i j q z).1
        true false).card = 3)
    (c0 : StatMech.Sharpness.FluxEdgeCopy.Copy
      (lpReplicaCurrentGraph G sites) z.1.1.1)
    (hc0C : c0 ∈ Finset.univ \ lpReplicaCurrentCopies G sites z.1.1.1
      (lpReplicaDecoratedSourceRowGateData G sites i j q z).1 true false)
    (hc0tag : (lpReplicaDecoratedSourceRowGateData G sites i j q z).1 c0 =
      (false, false)) :
    Finset.univ \ lpReplicaOrbitFourColorSlotRowMask G sites q
        (lpReplicaOffdiagDecoratedSourceSlotState G sites i j q z) ∈
      lpReplicaEligibleInactivePairs
        (lpReplicaOrbitFourColorSlotEdge G sites q
          (lpReplicaOffdiagDecoratedSourceCrossTrace G sites i j q z)) := by
  classical
  let d := lpReplicaDecoratedSourceRowGateData G sites i j q z
  let K := lpReplicaCurrentCopies G sites z.1.1.1 d.1 true false
  let state := lpReplicaOffdiagDecoratedSourceSlotState G sites i j q z
  let M := lpReplicaOrbitFourColorSlotRowMask G sites q state
  let C := Finset.univ \ M
  let E := lpReplicaProfileCopyEquivCommonSlot G sites q z.1.1.1
    z.1.1.2 z.2.2
  have hM : M = lpReplicaOrbitCommonSlotsOfCopies G sites q z.1.1.1
      z.1.1.2 z.2.2 K := by
    exact lpReplicaOffdiagDecoratedSource_rank_five_rowMask_eq_activeSlots
      G sites hsite hij q hcard z hthree c0 hc0C hc0tag
  have hMcard : M.card = 3 := by
    exact lpReplicaOffdiagDecoratedSource_rank_five_rowMask_card_eq_three
      G sites hsite hij q hcard z hthree c0 hc0C hc0tag
  have hCcard : C.card = 2 := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ M),
      Finset.card_univ, hcard, hMcard]
  have hactive :=
    lpReplicaOffdiagDecoratedSource_rank_five_crossTrace_edge_injOn_active
      G sites hsite hij q hcard z hthree c0 hc0C hc0tag
  have hsame :=
    lpReplicaOffdiagDecoratedSource_rank_five_complement_same_edge
      G sites hsite hij q hcard z hthree
  have hinactive (x : LPReplicaOrbitCommonSlot G sites q) (hx : x ∈ C) :
      E.symm x ∈ Finset.univ \ K := by
    apply Finset.mem_sdiff.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    intro hxK
    have hxM : x ∈ M := by
      rw [hM, mem_lpReplicaOrbitCommonSlotsOfCopies_iff]
      simpa only [E, Equiv.symm_apply_apply] using hxK
    exact (Finset.mem_sdiff.mp hx).2 hxM
  have hedge (x : LPReplicaOrbitCommonSlot G sites q) (hx : x ∈ C) :
      lpReplicaOrbitFourColorSlotEdge G sites q
          (lpReplicaOffdiagDecoratedSourceCrossTrace G sites i j q z) x =
        (E.symm x).1 := by
    simpa only [E, Equiv.apply_symm_apply] using
      (lpReplicaOffdiagDecoratedSource_rank_five_crossTrace_edge_of_inactive
        G sites hsite hij q hcard z hthree (c := c0) (e := E.symm x)
          hc0C hc0tag
          (hinactive x hx))
  simp only [lpReplicaEligibleInactivePairs, Finset.mem_filter,
    Finset.mem_powersetCard, Finset.subset_univ, true_and]
  change C.card = 2 ∧ _
  refine ⟨hCcard, ?_, ?_⟩
  · have hdouble : Finset.univ \ C = M := by
      ext x
      simp only [C, Finset.mem_sdiff, Finset.mem_univ, true_and, not_not]
    rw [hdouble, hM]
    exact hactive
  · intro x hx y hy
    rw [hedge x hx, hedge y hy]
    exact Subtype.ext
      (hsame (E.symm x) (hinactive x hx) (E.symm y) (hinactive y hy))

set_option maxHeartbeats 800000 in


def LPReplicaOffdiagDecoratedSource.IsErasedRankFive
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (z : LPReplicaOffdiagDecoratedSource G sites i j q) : Prop :=
  ∃ c : StatMech.Sharpness.FluxEdgeCopy.Copy
      (lpReplicaCurrentGraph G sites) z.1.1.1,
    c ∈ Finset.univ \ lpReplicaCurrentCopies G sites z.1.1.1
      (lpReplicaDecoratedSourceRowGateData G sites i j q z).1 true false ∧
    (lpReplicaDecoratedSourceRowGateData G sites i j q z).1 c =
      (false, false) ∧
    (lpReplicaCurrentCopies G sites z.1.1.1
      (lpReplicaDecoratedSourceRowGateData G sites i j q z).1
        true false).card = 3

set_option maxHeartbeats 800000 in


noncomputable def lpReplicaOffdiagDecoratedSourceCrossTraceFiberErasedRankFive
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (u : LPReplicaOrbitFourColorSlotState G sites q) :
    Finset (LPReplicaOffdiagDecoratedSource G sites i j q) := by
  classical
  exact (lpReplicaOffdiagDecoratedSourceCrossTraceFiber
    G sites i j q u).filter
      (LPReplicaOffdiagDecoratedSource.IsErasedRankFive G sites i j q)

set_option maxHeartbeats 800000 in

@[simp] theorem mem_lpReplicaOffdiagDecoratedSourceCrossTraceFiberErasedRankFive
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (u : LPReplicaOrbitFourColorSlotState G sites q)
    (z : LPReplicaOffdiagDecoratedSource G sites i j q) :
    z ∈ lpReplicaOffdiagDecoratedSourceCrossTraceFiberErasedRankFive
        G sites i j q u ↔
      z ∈ lpReplicaOffdiagDecoratedSourceCrossTraceFiber G sites i j q u ∧
        LPReplicaOffdiagDecoratedSource.IsErasedRankFive
          G sites i j q z := by
  classical
  simp [lpReplicaOffdiagDecoratedSourceCrossTraceFiberErasedRankFive]

set_option maxHeartbeats 800000 in



theorem lpReplicaOffdiagDecoratedSourceCrossTraceFiberErasedRankFive_card_le_eligible
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites) {i j : I} (hij : i ≠ j)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
    (u : LPReplicaOrbitFourColorSlotState G sites q) :
    (lpReplicaOffdiagDecoratedSourceCrossTraceFiberErasedRankFive
        G sites i j q u).card ≤
      (lpReplicaEligibleInactivePairs
        (lpReplicaOrbitFourColorSlotEdge G sites q u)).card := by
  classical
  let inactivePair := fun z : LPReplicaOffdiagDecoratedSource G sites i j q =>
    Finset.univ \ lpReplicaOrbitFourColorSlotRowMask G sites q
      (lpReplicaOffdiagDecoratedSourceSlotState G sites i j q z)
  apply Finset.card_le_card_of_injOn inactivePair
  · intro z hz
    simp only [Finset.mem_coe] at hz ⊢
    rw [mem_lpReplicaOffdiagDecoratedSourceCrossTraceFiberErasedRankFive]
      at hz
    obtain ⟨c, hcC, hctag, hthree⟩ := hz.2
    have hmem :=
      lpReplicaOffdiagDecoratedSource_rank_five_inactivePair_mem_eligible
        G sites hsite hij q hcard z hthree c hcC hctag
    have htrace : lpReplicaOffdiagDecoratedSourceCrossTrace
        G sites i j q z = u := (Finset.mem_filter.mp hz.1).2
    simpa only [inactivePair, htrace] using hmem
  · intro z hz w hw hpairs
    simp only [Finset.mem_coe] at hz hw
    rw [mem_lpReplicaOffdiagDecoratedSourceCrossTraceFiberErasedRankFive]
      at hz hw
    apply lpReplicaOffdiagDecoratedSourceRowMask_injOn_crossTraceFiber
      G sites i j q u hz.1 hw.1
    exact (sdiff_right_inj (Finset.subset_univ _) (Finset.subset_univ _)).mp
      hpairs



theorem lpReplicaOffdiagDecoratedSourceCrossTraceFiberErasedRankFive_card_le_three
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites) {i j : I} (hij : i ≠ j)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
    (u : LPReplicaOrbitFourColorSlotState G sites q) :
    (lpReplicaOffdiagDecoratedSourceCrossTraceFiberErasedRankFive
        G sites i j q u).card ≤ 3 := by
  exact (lpReplicaOffdiagDecoratedSourceCrossTraceFiberErasedRankFive_card_le_eligible
    G sites hsite hij q hcard u).trans
      (lpReplicaEligibleInactivePairs_card_le_three
        (lpReplicaOrbitFourColorSlotEdge G sites q u))


def LPReplicaOffdiagDecoratedSource.IsSaturatedRankFive
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (z : LPReplicaOffdiagDecoratedSource G sites i j q) : Prop :=
  lpReplicaCurrentCopies G sites z.1.1.1
    (lpReplicaDecoratedSourceRowGateData G sites i j q z).1 true false =
      Finset.univ


noncomputable def lpReplicaOffdiagDecoratedSourceCrossTraceFiberSaturatedRankFive
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (u : LPReplicaOrbitFourColorSlotState G sites q) :
    Finset (LPReplicaOffdiagDecoratedSource G sites i j q) := by
  classical
  exact (lpReplicaOffdiagDecoratedSourceCrossTraceFiber
    G sites i j q u).filter
      (LPReplicaOffdiagDecoratedSource.IsSaturatedRankFive G sites i j q)

@[simp] theorem mem_lpReplicaOffdiagDecoratedSourceCrossTraceFiberSaturatedRankFive
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (u : LPReplicaOrbitFourColorSlotState G sites q)
    (z : LPReplicaOffdiagDecoratedSource G sites i j q) :
    z ∈ lpReplicaOffdiagDecoratedSourceCrossTraceFiberSaturatedRankFive
        G sites i j q u ↔
      z ∈ lpReplicaOffdiagDecoratedSourceCrossTraceFiber G sites i j q u ∧
        LPReplicaOffdiagDecoratedSource.IsSaturatedRankFive
          G sites i j q z := by
  classical
  simp [lpReplicaOffdiagDecoratedSourceCrossTraceFiberSaturatedRankFive]


theorem lpReplicaOffdiagDecoratedSourceCrossTraceFiberSaturatedRankFive_card_le_one
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites) {i j : I} (hij : i ≠ j)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
    (u : LPReplicaOrbitFourColorSlotState G sites q) :
    (lpReplicaOffdiagDecoratedSourceCrossTraceFiberSaturatedRankFive
      G sites i j q u).card ≤ 1 := by
  classical
  rw [Finset.card_le_one]
  intro z hz w hw
  rw [mem_lpReplicaOffdiagDecoratedSourceCrossTraceFiberSaturatedRankFive]
    at hz hw
  apply lpReplicaOffdiagDecoratedSource_rank_five_saturated_eq_of_crossTrace_eq
    G sites hsite hij q hcard z w hz.2 hw.2
  exact (Finset.mem_filter.mp hz.1).2.trans
    (Finset.mem_filter.mp hw.1).2.symm

noncomputable def lpReplicaOffdiagDecoratedSourceCrossTraceFiberErasedOrSaturatedRankFive
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (u : LPReplicaOrbitFourColorSlotState G sites q) :
    Finset (LPReplicaOffdiagDecoratedSource G sites i j q) := by
  classical
  exact lpReplicaOffdiagDecoratedSourceCrossTraceFiberErasedRankFive
      G sites i j q u ∪
    lpReplicaOffdiagDecoratedSourceCrossTraceFiberSaturatedRankFive
      G sites i j q u



theorem lpReplicaOffdiagDecoratedSourceCrossTraceFiber_erased_union_saturated_card_le_four
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites) {i j : I} (hij : i ≠ j)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
    (u : LPReplicaOrbitFourColorSlotState G sites q) :
    (lpReplicaOffdiagDecoratedSourceCrossTraceFiberErasedOrSaturatedRankFive
      G sites i j q u).card ≤ 4 := by
  classical
  unfold lpReplicaOffdiagDecoratedSourceCrossTraceFiberErasedOrSaturatedRankFive
  calc
    _ ≤ (lpReplicaOffdiagDecoratedSourceCrossTraceFiberErasedRankFive
          G sites i j q u).card +
        (lpReplicaOffdiagDecoratedSourceCrossTraceFiberSaturatedRankFive
          G sites i j q u).card := Finset.card_union_le _ _
    _ ≤ 3 + 1 := Nat.add_le_add
      (lpReplicaOffdiagDecoratedSourceCrossTraceFiberErasedRankFive_card_le_three
        G sites hsite hij q hcard u)
      (lpReplicaOffdiagDecoratedSourceCrossTraceFiberSaturatedRankFive_card_le_one
        G sites hsite hij q hcard u)
    _ = 4 := rfl



theorem lpReplica_threeCopyOffdiag_exists_seamCopy
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites) {i j : I} (hij : i ≠ j)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (K : Finset (StatMech.Sharpness.FluxEdgeCopy.Copy
      (lpReplicaCurrentGraph G sites) m))
    (hKcard : K.card = 3)
    (hsource : StatMech.Sharpness.RandomCurrent.sources
      (StatMech.Sharpness.FluxEdgeCopy.endsM
        (lpReplicaCurrentGraph G sites) m) K =
      lpMatchingSeamSource
            (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i ∆
          lpMatchingSeamSource
            (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j ∆
          lpMatchingGhostSource
            (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
            lpReplicaCurrentGhost1) :
    (∃ c ∈ K, c.1.1 = lpReplicaCurrentSeamEdge sites i) ∨
      ∃ c ∈ K, c.1.1 = lpReplicaCurrentSeamEdge sites j := by
  classical
  let E := StatMech.Sharpness.FluxEdgeCopy.endsM
    (lpReplicaCurrentGraph G sites) m
  let B :=
    lpMatchingSeamSource
          (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i ∆
        lpMatchingSeamSource
          (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j ∆
        lpMatchingGhostSource
          (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
          lpReplicaCurrentGhost1
  have hsupport := lpReplica_threeCopyOffdiag_endpointSupport
    G sites hsite hij m K hKcard hsource
  have hsupport' : K.biUnion (fun c => (E c).toFinset) = B := by
    simpa only [E, B] using hsupport
  have hsij : sites i ≠ sites j := hsite.ne hij
  have hex (x : LPReplicaCurrentVertex V) (hx : x ∈ B) :
      ∃ c ∈ K, x ∈ E c := by
    have hx' : x ∈ K.biUnion fun c => (E c).toFinset := by
      rw [hsupport']
      exact hx
    obtain ⟨c, hcK, hxc⟩ := Finset.mem_biUnion.mp hx'
    exact ⟨c, hcK, Sym2.mem_toFinset.mp hxc⟩
  have hg0B : (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V) ∈ B := by
    simp [B, lpMatchingSeamSource, lpMatchingGhostSource,
      lpReplicaCurrentLeft, lpReplicaCurrentRight,
      lpReplicaCurrentGhost0, lpReplicaCurrentGhost1,
      Finset.mem_symmDiff]
  have hg1B : (lpReplicaCurrentGhost1 : LPReplicaCurrentVertex V) ∈ B := by
    simp [B, lpMatchingSeamSource, lpMatchingGhostSource,
      lpReplicaCurrentLeft, lpReplicaCurrentRight,
      lpReplicaCurrentGhost0, lpReplicaCurrentGhost1,
      Finset.mem_symmDiff]
  obtain ⟨c0, hc0K, hc0ghost⟩ := hex _ hg0B
  obtain ⟨c1, hc1K, hc1ghost⟩ := hex _ hg1B
  obtain ⟨x0, hc0edge⟩ := lpReplicaCurrentEdge_eq_ghost0_left_of_mem
    G sites c0.1.1 c0.1.2 hc0ghost
  obtain ⟨x1, hc1edge⟩ := lpReplicaCurrentEdge_eq_ghost1_right_of_mem
    G sites c1.1.1 c1.1.2 hc1ghost
  have hx0B : (.inl (.inl x0) : LPReplicaCurrentVertex V) ∈ B := by
    rw [← hsupport']
    apply Finset.mem_biUnion.mpr
    exact ⟨c0, hc0K, Sym2.mem_toFinset.mpr (by
      have h : (.inl (.inl x0) : LPReplicaCurrentVertex V) ∈ c0.1.1 := by
        rw [hc0edge]
        simp
      simpa only [E, StatMech.Sharpness.FluxEdgeCopy.endsM] using h)⟩
  have hx1B : (.inl (.inr x1) : LPReplicaCurrentVertex V) ∈ B := by
    rw [← hsupport']
    apply Finset.mem_biUnion.mpr
    exact ⟨c1, hc1K, Sym2.mem_toFinset.mpr (by
      have h : (.inl (.inr x1) : LPReplicaCurrentVertex V) ∈ c1.1.1 := by
        rw [hc1edge]
        simp
      simpa only [E, StatMech.Sharpness.FluxEdgeCopy.endsM] using h)⟩
  have hx0 : x0 = sites i ∨ x0 = sites j := by
    have h := hx0B
    simp [B, lpMatchingSeamSource, lpMatchingGhostSource,
      lpReplicaCurrentLeft, lpReplicaCurrentRight,
      lpReplicaCurrentGhost0, lpReplicaCurrentGhost1,
      Finset.mem_symmDiff, hsij, hsij.symm] at h
    exact h.imp And.left And.left
  have hx1 : x1 = sites i ∨ x1 = sites j := by
    have h := hx1B
    simp [B, lpMatchingSeamSource, lpMatchingGhostSource,
      lpReplicaCurrentLeft, lpReplicaCurrentRight,
      lpReplicaCurrentGhost0, lpReplicaCurrentGhost1,
      Finset.mem_symmDiff, hsij, hsij.symm] at h
    exact h.imp And.left And.left
  have hc01 : c0 ≠ c1 := by
    intro h
    subst c1
    change (lpReplicaCurrentGhost1 : LPReplicaCurrentVertex V) ∈ c0.1.1 at hc1ghost
    rw [hc0edge] at hc1ghost
    simp [lpReplicaCurrentGhost0, lpReplicaCurrentGhost1] at hc1ghost
  have ne_c0_of_mem {a : StatMech.Sharpness.FluxEdgeCopy.Copy
      (lpReplicaCurrentGraph G sites) m} {v : LPReplicaCurrentVertex V}
      (ha : v ∈ E a) (hv : v ∉ c0.1.1) : a ≠ c0 := by
    intro h
    subst a
    exact hv ha
  have ne_c1_of_mem {a : StatMech.Sharpness.FluxEdgeCopy.Copy
      (lpReplicaCurrentGraph G sites) m} {v : LPReplicaCurrentVertex V}
      (ha : v ∈ E a) (hv : v ∉ c1.1.1) : a ≠ c1 := by
    intro h
    subst a
    exact hv ha
  have third_eq {a b : StatMech.Sharpness.FluxEdgeCopy.Copy
      (lpReplicaCurrentGraph G sites) m}
      (haK : a ∈ K) (hbK : b ∈ K)
      (ha0 : a ≠ c0) (ha1 : a ≠ c1)
      (hb0 : b ≠ c0) (hb1 : b ≠ c1) : a = b := by
    by_contra hab
    have hfour : ({c0, c1, a, b} : Finset
        (StatMech.Sharpness.FluxEdgeCopy.Copy
          (lpReplicaCurrentGraph G sites) m)).card = 4 := by
      simp [hc01, ha0, ha1, hb0, hb1, hab,
        Ne.symm hc01, Ne.symm ha0, Ne.symm ha1,
        Ne.symm hb0, Ne.symm hb1, Ne.symm hab]
    have hsub : ({c0, c1, a, b} : Finset
        (StatMech.Sharpness.FluxEdgeCopy.Copy
          (lpReplicaCurrentGraph G sites) m)) ⊆ K := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> assumption
    have hle := Finset.card_le_card hsub
    rw [hfour, hKcard] at hle
    omega
  rcases hx0 with rfl | rfl <;> rcases hx1 with rfl | rfl
  · right
    have hLjB : lpReplicaCurrentLeft sites j ∈ B := by
      simp [B, lpMatchingSeamSource, lpMatchingGhostSource,
        lpReplicaCurrentLeft, lpReplicaCurrentRight,
        lpReplicaCurrentGhost0, lpReplicaCurrentGhost1,
        Finset.mem_symmDiff, hsij, hsij.symm]
    have hRjB : lpReplicaCurrentRight sites j ∈ B := by
      simp [B, lpMatchingSeamSource, lpMatchingGhostSource,
        lpReplicaCurrentLeft, lpReplicaCurrentRight,
        lpReplicaCurrentGhost0, lpReplicaCurrentGhost1,
        Finset.mem_symmDiff, hsij, hsij.symm]
    obtain ⟨a, haK, ha⟩ := hex _ hLjB
    obtain ⟨b, hbK, hb⟩ := hex _ hRjB
    have ha0 := ne_c0_of_mem ha (by
      rw [hc0edge]
      simp [lpReplicaCurrentLeft, lpReplicaCurrentRight,
        lpReplicaCurrentGhost0, lpReplicaCurrentGhost1, hsij, hsij.symm])
    have ha1 := ne_c1_of_mem ha (by
      rw [hc1edge]
      simp [lpReplicaCurrentLeft, lpReplicaCurrentRight,
        lpReplicaCurrentGhost0, lpReplicaCurrentGhost1, hsij, hsij.symm])
    have hb0 := ne_c0_of_mem hb (by
      rw [hc0edge]
      simp [lpReplicaCurrentLeft, lpReplicaCurrentRight,
        lpReplicaCurrentGhost0, lpReplicaCurrentGhost1, hsij, hsij.symm])
    have hb1 := ne_c1_of_mem hb (by
      rw [hc1edge]
      simp [lpReplicaCurrentLeft, lpReplicaCurrentRight,
        lpReplicaCurrentGhost0, lpReplicaCurrentGhost1, hsij, hsij.symm])
    have hab := third_eq haK hbK ha0 ha1 hb0 hb1
    subst b
    exact ⟨a, haK, sym2_eq_mk_of_mem_of_mem_of_ne ha hb (by
      simp [lpReplicaCurrentLeft, lpReplicaCurrentRight])⟩

  · exfalso
    have hRiB : lpReplicaCurrentRight sites i ∈ B := by
      simp [B, lpMatchingSeamSource, lpMatchingGhostSource,
        lpReplicaCurrentLeft, lpReplicaCurrentRight,
        lpReplicaCurrentGhost0, lpReplicaCurrentGhost1,
        Finset.mem_symmDiff, hsij, hsij.symm]
    have hLjB : lpReplicaCurrentLeft sites j ∈ B := by
      simp [B, lpMatchingSeamSource, lpMatchingGhostSource,
        lpReplicaCurrentLeft, lpReplicaCurrentRight,
        lpReplicaCurrentGhost0, lpReplicaCurrentGhost1,
        Finset.mem_symmDiff, hsij, hsij.symm]
    obtain ⟨a, haK, ha⟩ := hex _ hRiB
    obtain ⟨b, hbK, hb⟩ := hex _ hLjB
    have ha0 := ne_c0_of_mem ha (by
      rw [hc0edge]
      simp [lpReplicaCurrentLeft, lpReplicaCurrentRight,
        lpReplicaCurrentGhost0, lpReplicaCurrentGhost1, hsij, hsij.symm])
    have ha1 := ne_c1_of_mem ha (by
      rw [hc1edge]
      simp [lpReplicaCurrentLeft, lpReplicaCurrentRight,
        lpReplicaCurrentGhost0, lpReplicaCurrentGhost1, hsij, hsij.symm])
    have hb0 := ne_c0_of_mem hb (by
      rw [hc0edge]
      simp [lpReplicaCurrentLeft, lpReplicaCurrentRight,
        lpReplicaCurrentGhost0, lpReplicaCurrentGhost1, hsij, hsij.symm])
    have hb1 := ne_c1_of_mem hb (by
      rw [hc1edge]
      simp [lpReplicaCurrentLeft, lpReplicaCurrentRight,
        lpReplicaCurrentGhost0, lpReplicaCurrentGhost1, hsij, hsij.symm])
    have hab := third_eq haK hbK ha0 ha1 hb0 hb1
    subst b
    have hedge : a.1.1 = s(lpReplicaCurrentRight sites i,
        lpReplicaCurrentLeft sites j) :=
      sym2_eq_mk_of_mem_of_mem_of_ne ha hb (by
        simp [lpReplicaCurrentLeft, lpReplicaCurrentRight])
    have hadj : (lpReplicaCurrentGraph G sites).Adj
        (lpReplicaCurrentLeft sites j) (lpReplicaCurrentRight sites i) := by
      rw [← SimpleGraph.mem_edgeSet]
      have hm := SimpleGraph.mem_edgeFinset.mp a.1.2
      rw [hedge] at hm
      simpa only [Sym2.eq_swap] using hm
    obtain ⟨k, hkj, hki⟩ := (lpReplicaCurrentGraph_adj_left_right_iff
      G sites (sites j) (sites i)).mp hadj
    exact hsij (hki.symm.trans hkj)
  · exfalso
    have hLiB : lpReplicaCurrentLeft sites i ∈ B := by
      simp [B, lpMatchingSeamSource, lpMatchingGhostSource,
        lpReplicaCurrentLeft, lpReplicaCurrentRight,
        lpReplicaCurrentGhost0, lpReplicaCurrentGhost1,
        Finset.mem_symmDiff, hsij, hsij.symm]
    have hRjB : lpReplicaCurrentRight sites j ∈ B := by
      simp [B, lpMatchingSeamSource, lpMatchingGhostSource,
        lpReplicaCurrentLeft, lpReplicaCurrentRight,
        lpReplicaCurrentGhost0, lpReplicaCurrentGhost1,
        Finset.mem_symmDiff, hsij, hsij.symm]
    obtain ⟨a, haK, ha⟩ := hex _ hLiB
    obtain ⟨b, hbK, hb⟩ := hex _ hRjB
    have ha0 := ne_c0_of_mem ha (by
      rw [hc0edge]
      simp [lpReplicaCurrentLeft, lpReplicaCurrentRight,
        lpReplicaCurrentGhost0, lpReplicaCurrentGhost1, hsij, hsij.symm])
    have ha1 := ne_c1_of_mem ha (by
      rw [hc1edge]
      simp [lpReplicaCurrentLeft, lpReplicaCurrentRight,
        lpReplicaCurrentGhost0, lpReplicaCurrentGhost1, hsij, hsij.symm])
    have hb0 := ne_c0_of_mem hb (by
      rw [hc0edge]
      simp [lpReplicaCurrentLeft, lpReplicaCurrentRight,
        lpReplicaCurrentGhost0, lpReplicaCurrentGhost1, hsij, hsij.symm])
    have hb1 := ne_c1_of_mem hb (by
      rw [hc1edge]
      simp [lpReplicaCurrentLeft, lpReplicaCurrentRight,
        lpReplicaCurrentGhost0, lpReplicaCurrentGhost1, hsij, hsij.symm])
    have hab := third_eq haK hbK ha0 ha1 hb0 hb1
    subst b
    have hedge : a.1.1 = s(lpReplicaCurrentLeft sites i,
        lpReplicaCurrentRight sites j) :=
      sym2_eq_mk_of_mem_of_mem_of_ne ha hb (by
        simp [lpReplicaCurrentLeft, lpReplicaCurrentRight])
    have hadj : (lpReplicaCurrentGraph G sites).Adj
        (lpReplicaCurrentLeft sites i) (lpReplicaCurrentRight sites j) := by
      rw [← SimpleGraph.mem_edgeSet]
      have hm := SimpleGraph.mem_edgeFinset.mp a.1.2
      rwa [hedge] at hm
    obtain ⟨k, hki, hkj⟩ := (lpReplicaCurrentGraph_adj_left_right_iff
      G sites (sites i) (sites j)).mp hadj
    exact hsij (hki.symm.trans hkj)
  · left
    have hLiB : lpReplicaCurrentLeft sites i ∈ B := by
      simp [B, lpMatchingSeamSource, lpMatchingGhostSource,
        lpReplicaCurrentLeft, lpReplicaCurrentRight,
        lpReplicaCurrentGhost0, lpReplicaCurrentGhost1,
        Finset.mem_symmDiff, hsij, hsij.symm]
    have hRiB : lpReplicaCurrentRight sites i ∈ B := by
      simp [B, lpMatchingSeamSource, lpMatchingGhostSource,
        lpReplicaCurrentLeft, lpReplicaCurrentRight,
        lpReplicaCurrentGhost0, lpReplicaCurrentGhost1,
        Finset.mem_symmDiff, hsij, hsij.symm]
    obtain ⟨a, haK, ha⟩ := hex _ hLiB
    obtain ⟨b, hbK, hb⟩ := hex _ hRiB
    have ha0 := ne_c0_of_mem ha (by
      rw [hc0edge]
      simp [lpReplicaCurrentLeft, lpReplicaCurrentRight,
        lpReplicaCurrentGhost0, lpReplicaCurrentGhost1, hsij, hsij.symm])
    have ha1 := ne_c1_of_mem ha (by
      rw [hc1edge]
      simp [lpReplicaCurrentLeft, lpReplicaCurrentRight,
        lpReplicaCurrentGhost0, lpReplicaCurrentGhost1, hsij, hsij.symm])
    have hb0 := ne_c0_of_mem hb (by
      rw [hc0edge]
      simp [lpReplicaCurrentLeft, lpReplicaCurrentRight,
        lpReplicaCurrentGhost0, lpReplicaCurrentGhost1, hsij, hsij.symm])
    have hb1 := ne_c1_of_mem hb (by
      rw [hc1edge]
      simp [lpReplicaCurrentLeft, lpReplicaCurrentRight,
        lpReplicaCurrentGhost0, lpReplicaCurrentGhost1, hsij, hsij.symm])
    have hab := third_eq haK hbK ha0 ha1 hb0 hb1
    subst b
    exact ⟨a, haK, sym2_eq_mk_of_mem_of_mem_of_ne ha hb (by
      simp [lpReplicaCurrentLeft, lpReplicaCurrentRight])⟩



theorem lpReplicaOffdiagDecoratedSource_rank_five_exists_seamCopy_of_active_card_eq_three
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites) {i j : I} (hij : i ≠ j)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
    (z : LPReplicaOffdiagDecoratedSource G sites i j q)
    (hthree : (lpReplicaCurrentCopies G sites z.1.1.1
      (lpReplicaDecoratedSourceRowGateData G sites i j q z).1
        true false).card = 3) :
    let d := lpReplicaDecoratedSourceRowGateData G sites i j q z
    let K := lpReplicaCurrentCopies G sites z.1.1.1 d.1 true false
    (∃ c ∈ K, c.1.1 = lpReplicaCurrentSeamEdge sites i) ∨
      ∃ c ∈ K, c.1.1 = lpReplicaCurrentSeamEdge sites j := by
  dsimp only
  let d := lpReplicaDecoratedSourceRowGateData G sites i j q z
  let K := lpReplicaCurrentCopies G sites z.1.1.1 d.1 true false
  exact lpReplica_threeCopyOffdiag_exists_seamCopy
    G sites hsite hij z.1.1.1 K (by simpa only [K, d] using hthree)
      d.2.2.2.2.1

set_option maxHeartbeats 1000000 in



theorem lpReplicaOffdiagDecoratedSource_rank_five_balancedSelector_of_iSeam
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites) {i j : I} (hij : i ≠ j)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
    (z : LPReplicaOffdiagDecoratedSource G sites i j q)
    (hthree : (lpReplicaCurrentCopies G sites z.1.1.1
      (lpReplicaDecoratedSourceRowGateData G sites i j q z).1
        true false).card = 3)
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
        HEq s.selector (Finset.univ \ {c}) ∧
        @HEq
          (StatMech.Sharpness.FluxEdgeCopy.Copy
            (lpReplicaCurrentGraph G sites) s.profile -> LPReplicaRowTag)
          (lpReplicaToggleRows G sites s.profile s.selector s.tag)
          (StatMech.Sharpness.FluxEdgeCopy.Copy
            (lpReplicaCurrentGraph G sites) z.1.1.1 -> LPReplicaRowTag)
          (lpReplicaToggleRows G sites z.1.1.1 {c}
            (lpReplicaDecoratedSourceRowGateData G sites i j q z).1) ∧
        ∃ y : LPReplicaDecoratedOrbitAtom G sites
            (lpMatchingSeamSource
              (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i)
            (lpMatchingSeamSource
                (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j ∆
              lpMatchingGhostSource
                (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
                lpReplicaCurrentGhost1) q,
          LPReplicaOffdiagBalancedOutput G sites i j q (Sum.inl y) ∧
            (lpReplicaOffdiagDecoratedTargetBranchedSlotState G sites i j q
                (Sum.inl y)).2 =
              lpReplicaOrbitFourColorSlotCrossToggle G sites q
                (lpReplicaOrbitCommonSlotsOfCopies G sites q z.1.1.1
                  z.1.1.2 z.2.2 {c})
                (lpReplicaOffdiagDecoratedSourceSlotState
                  G sites i j q z) ∧
            y = lpReplicaDecoratedOrbitAtomOfBalancedSelector_left
              G sites i j q s := by
  classical
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
  let P : Finset (StatMech.Sharpness.FluxEdgeCopy.Copy
      (lpReplicaCurrentGraph G sites) m) := Finset.univ \ {c}
  have hctag0 : d0.1 c = (true, false) := by
    simpa only [K, lpReplicaCurrentCopies, Finset.mem_filter,
      Finset.mem_univ, true_and] using hcK
  have hcurrent : (d.1 c).2 = false := by
    change (lpReplicaSwapRowsTag d0.1 c).2 = false
    simp only [lpReplicaSwapRowsTag, hctag0]
  have hcurr := lpReplicaRowGate_compl_singleton_currentSources
    G sites m B d.1 d.2 c hcurrent
  have hcends : E c = s(lpReplicaCurrentLeft sites i,
      lpReplicaCurrentRight sites i) := by
    simpa only [E, m, StatMech.Sharpness.FluxEdgeCopy.endsM] using hc
  have hsingle : StatMech.Sharpness.RandomCurrent.sources E {c} = Si := by
    simpa only [Si, lpMatchingSeamSource] using
      randomCurrent_sources_singleton_of_ends_eq E c (by
        simp [lpReplicaCurrentLeft, lpReplicaCurrentRight]) hcends
  have hfalseSource : StatMech.Sharpness.RandomCurrent.sources E
      (P.filter fun a => (d.1 a).2 = false) = Sj ∆ T := by
    calc
      _ = B ∆ StatMech.Sharpness.RandomCurrent.sources E {c} := by
        simpa only [P, E] using hcurr.1
      _ = B ∆ Si := by rw [hsingle]
      _ = Sj ∆ T := by
        change (Si ∆ Sj ∆ T) ∆ Si = Sj ∆ T
        rw [symmDiff_assoc Si Sj T, symmDiff_symmDiff_self']
  have htrueSource : StatMech.Sharpness.RandomCurrent.sources E
      (P.filter fun a => (d.1 a).2 = true) = ∅ := by
    simpa only [P, E, B] using hcurr.2
  have hmove : lpReplicaToggleRows G sites m P d.1 =
      lpReplicaToggleRows G sites m {c} d0.1 := by
    simpa only [P, d, d0,
      lpReplicaDecoratedSourceSwappedRowGateData] using
        lpReplicaToggleRows_univ_sdiff_singleton_swapRowsTag
          G sites m d0.1 c
  have hrow1Eq : lpReplicaRowCopies G sites m
      (lpReplicaToggleRows G sites m P d.1) true =
        lpReplicaRowCopies G sites m d0.1 true \ {c} := by
    rw [hmove]
    ext a
    by_cases hac : a = c
    · subst a
      simp [lpReplicaRowCopies, lpReplicaToggleRows, hctag0]
    · simp [lpReplicaRowCopies, lpReplicaToggleRows, hac]
  have hrow1Disconn : ¬ StatMech.Sharpness.RandomCurrent.connK E
      (lpReplicaRowCopies G sites m
        (lpReplicaToggleRows G sites m P d.1) true)
      lpReplicaCurrentGhost0 lpReplicaCurrentGhost1 := by
    intro hconn
    apply d0.2.2.2.2.2.2
    apply StatMech.GrahamGHS.FourColor.connK_mono _ hconn
    rw [hrow1Eq]
    exact Finset.sdiff_subset
  have hrow0Sub : lpReplicaRowCopies G sites m
      (lpReplicaToggleRows G sites m P d.1) false ⊆ {c} ∪ C := by
    rw [hmove]
    intro a ha
    simp only [lpReplicaRowCopies, lpReplicaToggleRows, Finset.mem_filter,
      Finset.mem_univ, true_and, Finset.mem_union, Finset.mem_singleton] at ha ⊢
    by_cases hac : a = c
    · exact Or.inl hac
    · right
      apply Finset.mem_sdiff.mpr
      refine ⟨Finset.mem_univ a, ?_⟩
      intro haK
      have hatag : d0.1 a = (true, false) := by
        simpa only [K, lpReplicaCurrentCopies, Finset.mem_filter,
          Finset.mem_univ, true_and] using haK
      simp [hac, hatag] at ha
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
      Finset.card_univ, hcopyCard]
    have hKcard : K.card = 3 := by
      simpa only [K, d0] using hthree
    omega
  obtain ⟨e0, he0C⟩ : C.Nonempty := Finset.card_pos.mp (by omega)
  have hsame : ∀ e ∈ C, e.1.1 = e0.1.1 := by
    intro e he
    exact lpReplicaOffdiagDecoratedSource_rank_five_complement_same_edge
      G sites hsite hij q hcard z hthree e he e0 he0C
  have hrow0Disconn : ¬ StatMech.Sharpness.RandomCurrent.connK E
      (lpReplicaRowCopies G sites m
        (lpReplicaToggleRows G sites m P d.1) false)
      lpReplicaCurrentGhost0 lpReplicaCurrentGhost1 := by
    intro hconn
    exact lpReplica_seam_union_parallelCopies_ghost_disconnected
      G sites i m c e0 C hc hsame
        (StatMech.GrahamGHS.FourColor.connK_mono hrow0Sub hconn)
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
  refine ⟨s, rfl, HEq.rfl, HEq.rfl, heq_of_eq hmove, ?_⟩
  let sourceTag := lpReplicaOrientedFourColorTag G sites ∅ B q
    (lpReplicaDecoratedOrbitAtomEquivOrientedFourColor G sites ∅ B q z)
  have hsourceTag : sourceTag = d0.1 := by
    exact lpReplicaOffdiagDecoratedSource_orientedTag_eq_rowGateData
      G sites i j q z
  have hfixed : c.1 ∈ lpReplicaCurrentEdgeOrbitFixed G sites :=
    lpReplicaCurrentEdge_mem_orbitFixed_of_eq_seam G sites i m c hc
  have hgeneric := lpReplicaBalancedSelector_slotState_of_singletonToggle
    G sites Si Sj T q s c sourceTag (by
      rw [hsourceTag]
      exact hmove) hfixed
  have hfixedD : (Sj ∆ T).map lpReplicaCurrentReflect.toEmbedding =
      Sj ∆ T := lpReplicaCurrentReflect_seam_symmDiff_ghost G sites j
  refine ⟨lpReplicaDecoratedOrbitAtomOfBalancedSelector_left
    G sites i j q s, Or.inl ⟨s, rfl⟩, ?_, rfl⟩
  unfold lpReplicaOffdiagDecoratedTargetBranchedSlotState
  unfold lpReplicaDecoratedOrbitAtomOfBalancedSelector_left
  dsimp only
  rw [lpReplicaOrientedFourColorSlotState_cast_boundary G sites Si
    ((Sj ∆ T).map lpReplicaCurrentReflect.toEmbedding) (Sj ∆ T) q hfixedD]
  exact hgeneric

set_option maxHeartbeats 1200000 in




theorem lpReplicaOffdiagDecoratedSource_rank_five_target_of_iSeam_parallelInactive
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites) {i j : I} (hij : i ≠ j)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
    (z : LPReplicaOffdiagDecoratedSource G sites i j q)
    (hthree : (lpReplicaCurrentCopies G sites z.1.1.1
      (lpReplicaDecoratedSourceRowGateData G sites i j q z).1
        true false).card = 3)
    (k c : StatMech.Sharpness.FluxEdgeCopy.Copy
      (lpReplicaCurrentGraph G sites) z.1.1.1)
    (hkK : k ∈ lpReplicaCurrentCopies G sites z.1.1.1
      (lpReplicaDecoratedSourceRowGateData G sites i j q z).1 true false)
    (hk : k.1.1 = lpReplicaCurrentSeamEdge sites i)
    (hcC : c ∈ Finset.univ \ lpReplicaCurrentCopies G sites z.1.1.1
      (lpReplicaDecoratedSourceRowGateData G sites i j q z).1 true false)
    (hck : c.1.1 = k.1.1)
    (hctag : (lpReplicaDecoratedSourceRowGateData G sites i j q z).1 c =
      (false, false)) :
    ∃ y : LPReplicaDecoratedOrbitAtom G sites
        (lpMatchingSeamSource
          (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i)
        (lpMatchingSeamSource
            (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j ∆
          lpMatchingGhostSource
            (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
            lpReplicaCurrentGhost1) q,
      LPReplicaOffdiagBalancedOutput G sites i j q (Sum.inl y) ∧
        (lpReplicaOffdiagDecoratedTargetBranchedSlotState G sites i j q
            (Sum.inl y)).2 =
          lpReplicaOrbitFourColorSlotCrossToggle G sites q
            (lpReplicaOrbitCommonSlotsOfCopies G sites q z.1.1.1
              z.1.1.2 z.2.2 {c})
            (lpReplicaOffdiagDecoratedSourceSlotState G sites i j q z) := by
  classical
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
  let P : Finset (StatMech.Sharpness.FluxEdgeCopy.Copy
      (lpReplicaCurrentGraph G sites) m) := Finset.univ \ {c}
  have hcNotK : c ∉ K := (Finset.mem_sdiff.mp hcC).2
  have hctag' : d0.1 c = (false, false) := hctag
  have hcurrent : (d.1 c).2 = false := by
    change (lpReplicaSwapRowsTag d0.1 c).2 = false
    simp only [lpReplicaSwapRowsTag, hctag']
  have hcurr := lpReplicaRowGate_compl_singleton_currentSources
    G sites m B d.1 d.2 c hcurrent
  have hcSeam : c.1.1 = lpReplicaCurrentSeamEdge sites i := hck.trans hk
  have hcends : E c = s(lpReplicaCurrentLeft sites i,
      lpReplicaCurrentRight sites i) := by
    simpa only [E, m, StatMech.Sharpness.FluxEdgeCopy.endsM] using hcSeam
  have hsingle : StatMech.Sharpness.RandomCurrent.sources E {c} = Si := by
    simpa only [Si, lpMatchingSeamSource] using
      randomCurrent_sources_singleton_of_ends_eq E c (by
        simp [lpReplicaCurrentLeft, lpReplicaCurrentRight]) hcends
  have hfalseSource : StatMech.Sharpness.RandomCurrent.sources E
      (P.filter fun a => (d.1 a).2 = false) = Sj ∆ T := by
    calc
      _ = B ∆ StatMech.Sharpness.RandomCurrent.sources E {c} := by
        simpa only [P, E] using hcurr.1
      _ = B ∆ Si := by rw [hsingle]
      _ = Sj ∆ T := by
        change (Si ∆ Sj ∆ T) ∆ Si = Sj ∆ T
        rw [symmDiff_assoc Si Sj T, symmDiff_symmDiff_self']
  have htrueSource : StatMech.Sharpness.RandomCurrent.sources E
      (P.filter fun a => (d.1 a).2 = true) = ∅ := by
    simpa only [P, E, B] using hcurr.2
  have hmove : lpReplicaToggleRows G sites m P d.1 =
      lpReplicaToggleRows G sites m {c} d0.1 := by
    simpa only [P, d, d0,
      lpReplicaDecoratedSourceSwappedRowGateData] using
        lpReplicaToggleRows_univ_sdiff_singleton_swapRowsTag
          G sites m d0.1 c
  have hcompConst : ∀ a ∈ C, d0.1 a = d0.1 c := by
    intro a ha
    exact lpReplicaOffdiagDecoratedSource_rank_five_complement_tag_constant
      G sites hsite hij q hcard z hthree a ha c hcC
  have hnoTrueTrue (a) : d0.1 a ≠ (true, true) := by
    intro ha
    have haNotK : a ∉ K := by
      intro haK
      have haActive : d0.1 a = (true, false) := by
        simpa only [K, lpReplicaCurrentCopies, Finset.mem_filter,
          Finset.mem_univ, true_and] using haK
      exact Bool.false_ne_true
        (congrArg Prod.snd (haActive.symm.trans ha))
    have haC : a ∈ C := Finset.mem_sdiff.mpr ⟨Finset.mem_univ a, haNotK⟩
    have := hcompConst a haC
    rw [ha, hctag'] at this
    simpa using congrArg Prod.fst this
  have hrow1Original : lpReplicaRowCopies G sites m d0.1 true = K := by
    ext a
    rcases ha : d0.1 a with ⟨row, current⟩
    cases row <;> cases current <;>
      simp [lpReplicaRowCopies, K, lpReplicaCurrentCopies, ha]
    exact False.elim (hnoTrueTrue a ha)
  have hrow1Eq : lpReplicaRowCopies G sites m
      (lpReplicaToggleRows G sites m P d.1) true = insert c K := by
    rw [hmove, lpReplicaRowCopies_toggle, hrow1Original]
    ext a
    simp only [Finset.mem_symmDiff, Finset.mem_singleton,
      Finset.mem_insert]
    constructor <;> intro ha
    · rcases ha with ⟨haK, hac⟩ | ⟨hac, haK⟩
      · exact Or.inr haK
      · exact Or.inl hac
    · rcases ha with rfl | haK
      · exact Or.inr ⟨rfl, hcNotK⟩
      · exact Or.inl ⟨haK, fun hac => hcNotK (hac ▸ haK)⟩
  have hparallelEnds : E c = E k := by
    simpa only [E, StatMech.Sharpness.FluxEdgeCopy.endsM] using hck
  have hrow1Disconn : ¬ StatMech.Sharpness.RandomCurrent.connK E
      (lpReplicaRowCopies G sites m
        (lpReplicaToggleRows G sites m P d.1) true)
      lpReplicaCurrentGhost0 lpReplicaCurrentGhost1 := by
    intro hconn
    apply d0.2.2.2.2.2.2
    rw [hrow1Original]
    exact (randomCurrent_connK_insert_parallel_iff E K c k hkK
      hparallelEnds lpReplicaCurrentGhost0 lpReplicaCurrentGhost1).mp
        (hrow1Eq ▸ hconn)
  have hrow0Sub : lpReplicaRowCopies G sites m
      (lpReplicaToggleRows G sites m P d.1) false ⊆ {k} ∪ C := by
    rw [hmove]
    intro a ha
    simp only [lpReplicaRowCopies, lpReplicaToggleRows, Finset.mem_filter,
      Finset.mem_univ, true_and, Finset.mem_union, Finset.mem_singleton] at ha ⊢
    by_cases hak : a = k
    · exact Or.inl hak
    · right
      apply Finset.mem_sdiff.mpr
      refine ⟨Finset.mem_univ a, ?_⟩
      intro haK
      have hatag : d0.1 a = (true, false) := by
        simpa only [K, lpReplicaCurrentCopies, Finset.mem_filter,
          Finset.mem_univ, true_and] using haK
      by_cases hac : a = c
      · subst a
        exact Bool.false_ne_true (congrArg Prod.fst (hctag.symm.trans hatag))
      · simp [hac, hatag] at ha
  obtain ⟨e0, he0C⟩ : C.Nonempty := ⟨c, hcC⟩
  have hsame : ∀ e ∈ C, e.1.1 = e0.1.1 := by
    intro e he
    exact lpReplicaOffdiagDecoratedSource_rank_five_complement_same_edge
      G sites hsite hij q hcard z hthree e he e0 he0C
  have hrow0Disconn : ¬ StatMech.Sharpness.RandomCurrent.connK E
      (lpReplicaRowCopies G sites m
        (lpReplicaToggleRows G sites m P d.1) false)
      lpReplicaCurrentGhost0 lpReplicaCurrentGhost1 := by
    intro hconn
    exact lpReplica_seam_union_parallelCopies_ghost_disconnected
      G sites i m k e0 C hk hsame
        (StatMech.GrahamGHS.FourColor.connK_mono hrow0Sub hconn)
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
  let sourceTag := lpReplicaOrientedFourColorTag G sites ∅ B q
    (lpReplicaDecoratedOrbitAtomEquivOrientedFourColor G sites ∅ B q z)
  have hsourceTag : sourceTag = d0.1 := by
    exact lpReplicaOffdiagDecoratedSource_orientedTag_eq_rowGateData
      G sites i j q z
  have hfixed : c.1 ∈ lpReplicaCurrentEdgeOrbitFixed G sites :=
    lpReplicaCurrentEdge_mem_orbitFixed_of_eq_seam G sites i m c hcSeam
  have hgeneric := lpReplicaBalancedSelector_slotState_of_singletonToggle
    G sites Si Sj T q s c sourceTag (by
      rw [hsourceTag]
      exact hmove) hfixed
  have hfixedD : (Sj ∆ T).map lpReplicaCurrentReflect.toEmbedding =
      Sj ∆ T := lpReplicaCurrentReflect_seam_symmDiff_ghost G sites j
  refine ⟨lpReplicaDecoratedOrbitAtomOfBalancedSelector_left
    G sites i j q s, Or.inl ⟨s, rfl⟩, ?_⟩
  unfold lpReplicaOffdiagDecoratedTargetBranchedSlotState
  unfold lpReplicaDecoratedOrbitAtomOfBalancedSelector_left
  dsimp only
  rw [lpReplicaOrientedFourColorSlotState_cast_boundary G sites Si
    ((Sj ∆ T).map lpReplicaCurrentReflect.toEmbedding) (Sj ∆ T) q hfixedD]
  exact hgeneric

set_option maxHeartbeats 1200000 in




theorem lpReplicaOffdiagDecoratedSource_rank_five_target_of_jSeam_parallelInactive
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites) {i j : I} (hij : i ≠ j)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
    (z : LPReplicaOffdiagDecoratedSource G sites i j q)
    (hthree : (lpReplicaCurrentCopies G sites z.1.1.1
      (lpReplicaDecoratedSourceRowGateData G sites i j q z).1
        true false).card = 3)
    (k c : StatMech.Sharpness.FluxEdgeCopy.Copy
      (lpReplicaCurrentGraph G sites) z.1.1.1)
    (hkK : k ∈ lpReplicaCurrentCopies G sites z.1.1.1
      (lpReplicaDecoratedSourceRowGateData G sites i j q z).1 true false)
    (hk : k.1.1 = lpReplicaCurrentSeamEdge sites j)
    (hcC : c ∈ Finset.univ \ lpReplicaCurrentCopies G sites z.1.1.1
      (lpReplicaDecoratedSourceRowGateData G sites i j q z).1 true false)
    (hck : c.1.1 = k.1.1)
    (hctag : (lpReplicaDecoratedSourceRowGateData G sites i j q z).1 c =
      (false, false)) :
    ∃ y : LPReplicaDecoratedOrbitAtom G sites
        (lpMatchingSeamSource
          (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j)
        (lpMatchingSeamSource
            (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i ∆
          lpMatchingGhostSource
            (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
            lpReplicaCurrentGhost1) q,
      LPReplicaOffdiagBalancedOutput G sites i j q (Sum.inr y) ∧
        (lpReplicaOffdiagDecoratedTargetBranchedSlotState G sites i j q
            (Sum.inr y)).2 =
          lpReplicaOrbitFourColorSlotCrossToggle G sites q
            (lpReplicaOrbitCommonSlotsOfCopies G sites q z.1.1.1
              z.1.1.2 z.2.2 {c})
            (lpReplicaOffdiagDecoratedSourceSlotState G sites i j q z) := by
  classical
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
  let P : Finset (StatMech.Sharpness.FluxEdgeCopy.Copy
      (lpReplicaCurrentGraph G sites) m) := Finset.univ \ {c}
  have hcNotK : c ∉ K := (Finset.mem_sdiff.mp hcC).2
  have hctag' : d0.1 c = (false, false) := hctag
  have hcurrent : (d.1 c).2 = false := by
    change (lpReplicaSwapRowsTag d0.1 c).2 = false
    simp only [lpReplicaSwapRowsTag, hctag']
  have hcurr := lpReplicaRowGate_compl_singleton_currentSources
    G sites m B d.1 d.2 c hcurrent
  have hcSeam : c.1.1 = lpReplicaCurrentSeamEdge sites j := hck.trans hk
  have hcends : E c = s(lpReplicaCurrentLeft sites j,
      lpReplicaCurrentRight sites j) := by
    simpa only [E, m, StatMech.Sharpness.FluxEdgeCopy.endsM] using hcSeam
  have hsingle : StatMech.Sharpness.RandomCurrent.sources E {c} = Sj := by
    simpa only [Sj, lpMatchingSeamSource] using
      randomCurrent_sources_singleton_of_ends_eq E c (by
        simp [lpReplicaCurrentLeft, lpReplicaCurrentRight]) hcends
  have hfalseSource : StatMech.Sharpness.RandomCurrent.sources E
      (P.filter fun a => (d.1 a).2 = false) = Si ∆ T := by
    calc
      _ = B ∆ StatMech.Sharpness.RandomCurrent.sources E {c} := by
        simpa only [P, E] using hcurr.1
      _ = B ∆ Sj := by rw [hsingle]
      _ = Si ∆ T := by
        change (Si ∆ Sj ∆ T) ∆ Sj = Si ∆ T
        rw [symmDiff_comm Si Sj, symmDiff_assoc Sj Si T,
          symmDiff_symmDiff_self']
  have htrueSource : StatMech.Sharpness.RandomCurrent.sources E
      (P.filter fun a => (d.1 a).2 = true) = ∅ := by
    simpa only [P, E, B] using hcurr.2
  have hmove : lpReplicaToggleRows G sites m P d.1 =
      lpReplicaToggleRows G sites m {c} d0.1 := by
    simpa only [P, d, d0,
      lpReplicaDecoratedSourceSwappedRowGateData] using
        lpReplicaToggleRows_univ_sdiff_singleton_swapRowsTag
          G sites m d0.1 c
  have hcompConst : ∀ a ∈ C, d0.1 a = d0.1 c := by
    intro a ha
    exact lpReplicaOffdiagDecoratedSource_rank_five_complement_tag_constant
      G sites hsite hij q hcard z hthree a ha c hcC
  have hnoTrueTrue (a) : d0.1 a ≠ (true, true) := by
    intro ha
    have haNotK : a ∉ K := by
      intro haK
      have haActive : d0.1 a = (true, false) := by
        simpa only [K, lpReplicaCurrentCopies, Finset.mem_filter,
          Finset.mem_univ, true_and] using haK
      exact Bool.false_ne_true
        (congrArg Prod.snd (haActive.symm.trans ha))
    have haC : a ∈ C := Finset.mem_sdiff.mpr ⟨Finset.mem_univ a, haNotK⟩
    have := hcompConst a haC
    rw [ha, hctag'] at this
    simpa using congrArg Prod.fst this
  have hrow1Original : lpReplicaRowCopies G sites m d0.1 true = K := by
    ext a
    rcases ha : d0.1 a with ⟨row, current⟩
    cases row <;> cases current <;>
      simp [lpReplicaRowCopies, K, lpReplicaCurrentCopies, ha]
    exact False.elim (hnoTrueTrue a ha)
  have hrow1Eq : lpReplicaRowCopies G sites m
      (lpReplicaToggleRows G sites m P d.1) true = insert c K := by
    rw [hmove, lpReplicaRowCopies_toggle, hrow1Original]
    ext a
    simp only [Finset.mem_symmDiff, Finset.mem_singleton,
      Finset.mem_insert]
    constructor <;> intro ha
    · rcases ha with ⟨haK, hac⟩ | ⟨hac, haK⟩
      · exact Or.inr haK
      · exact Or.inl hac
    · rcases ha with rfl | haK
      · exact Or.inr ⟨rfl, hcNotK⟩
      · exact Or.inl ⟨haK, fun hac => hcNotK (hac ▸ haK)⟩
  have hparallelEnds : E c = E k := by
    simpa only [E, StatMech.Sharpness.FluxEdgeCopy.endsM] using hck
  have hrow1Disconn : ¬ StatMech.Sharpness.RandomCurrent.connK E
      (lpReplicaRowCopies G sites m
        (lpReplicaToggleRows G sites m P d.1) true)
      lpReplicaCurrentGhost0 lpReplicaCurrentGhost1 := by
    intro hconn
    apply d0.2.2.2.2.2.2
    rw [hrow1Original]
    exact (randomCurrent_connK_insert_parallel_iff E K c k hkK
      hparallelEnds lpReplicaCurrentGhost0 lpReplicaCurrentGhost1).mp
        (hrow1Eq ▸ hconn)
  have hrow0Sub : lpReplicaRowCopies G sites m
      (lpReplicaToggleRows G sites m P d.1) false ⊆ {k} ∪ C := by
    rw [hmove]
    intro a ha
    simp only [lpReplicaRowCopies, lpReplicaToggleRows, Finset.mem_filter,
      Finset.mem_univ, true_and, Finset.mem_union, Finset.mem_singleton] at ha ⊢
    by_cases hak : a = k
    · exact Or.inl hak
    · right
      apply Finset.mem_sdiff.mpr
      refine ⟨Finset.mem_univ a, ?_⟩
      intro haK
      have hatag : d0.1 a = (true, false) := by
        simpa only [K, lpReplicaCurrentCopies, Finset.mem_filter,
          Finset.mem_univ, true_and] using haK
      by_cases hac : a = c
      · subst a
        exact Bool.false_ne_true (congrArg Prod.fst (hctag.symm.trans hatag))
      · simp [hac, hatag] at ha
  obtain ⟨e0, he0C⟩ : C.Nonempty := ⟨c, hcC⟩
  have hsame : ∀ e ∈ C, e.1.1 = e0.1.1 := by
    intro e he
    exact lpReplicaOffdiagDecoratedSource_rank_five_complement_same_edge
      G sites hsite hij q hcard z hthree e he e0 he0C
  have hrow0Disconn : ¬ StatMech.Sharpness.RandomCurrent.connK E
      (lpReplicaRowCopies G sites m
        (lpReplicaToggleRows G sites m P d.1) false)
      lpReplicaCurrentGhost0 lpReplicaCurrentGhost1 := by
    intro hconn
    exact lpReplica_seam_union_parallelCopies_ghost_disconnected
      G sites j m k e0 C hk hsame
        (StatMech.GrahamGHS.FourColor.connK_mono hrow0Sub hconn)
  let s : LPReplicaBalancedSelector G sites B (Si ∆ T) q := {
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
  have hsourceTag : sourceTag = d0.1 := by
    exact lpReplicaOffdiagDecoratedSource_orientedTag_eq_rowGateData
      G sites i j q z
  have hfixed : c.1 ∈ lpReplicaCurrentEdgeOrbitFixed G sites :=
    lpReplicaCurrentEdge_mem_orbitFixed_of_eq_seam G sites j m c hcSeam
  let s' : LPReplicaBalancedSelector G sites (Sj ∆ Si ∆ T) (Si ∆ T) q := {
    profile := s.profile
    orbit := s.orbit
    tag := s.tag
    gate := by
      change LPReplicaRowGate G sites s.profile (Sj ∆ Si ∆ T) ∅ s.tag
      rw [symmDiff_comm Sj Si]
      exact s.gate
    orbitLabel := s.orbitLabel
    selector := s.selector
    falseSource := s.falseSource
    trueSource := s.trueSource
    row0Disconn := s.row0Disconn
    row1Disconn := s.row1Disconn }
  have hgeneric := lpReplicaBalancedSelector_slotState_of_singletonToggle
    G sites Sj Si T q s' c sourceTag (by
      rw [hsourceTag]
      exact hmove) hfixed
  have hfixedD : (Si ∆ T).map lpReplicaCurrentReflect.toEmbedding =
      Si ∆ T := lpReplicaCurrentReflect_seam_symmDiff_ghost G sites i
  let y := lpReplicaDecoratedOrbitAtomOfBalancedSelector_left
    G sites j i q s'
  refine ⟨y, Or.inr ⟨s', rfl⟩, ?_⟩
  change (lpReplicaOffdiagDecoratedTargetBranchedSlotState G sites j i q
    (Sum.inl y)).2 = _
  unfold lpReplicaOffdiagDecoratedTargetBranchedSlotState
  unfold y lpReplicaDecoratedOrbitAtomOfBalancedSelector_left
  dsimp only
  rw [lpReplicaOrientedFourColorSlotState_cast_boundary G sites Sj
    ((Si ∆ T).map lpReplicaCurrentReflect.toEmbedding) (Si ∆ T) q hfixedD]
  exact hgeneric


set_option maxHeartbeats 1000000 in


theorem lpReplicaOffdiagDecoratedSource_rank_five_balancedSelector_of_jSeam
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites) {i j : I} (hij : i ≠ j)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
    (z : LPReplicaOffdiagDecoratedSource G sites i j q)
    (hthree : (lpReplicaCurrentCopies G sites z.1.1.1
      (lpReplicaDecoratedSourceRowGateData G sites i j q z).1
        true false).card = 3)
    (c : StatMech.Sharpness.FluxEdgeCopy.Copy
      (lpReplicaCurrentGraph G sites) z.1.1.1)
    (hcK : c ∈ lpReplicaCurrentCopies G sites z.1.1.1
      (lpReplicaDecoratedSourceRowGateData G sites i j q z).1 true false)
    (hc : c.1.1 = lpReplicaCurrentSeamEdge sites j) :
    ∃ s : LPReplicaBalancedSelector G sites
        (lpMatchingSeamSource
              (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i ∆
            lpMatchingSeamSource
              (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j ∆
            lpMatchingGhostSource
              (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
              lpReplicaCurrentGhost1)
        (lpMatchingSeamSource
              (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i ∆
            lpMatchingGhostSource
              (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
              lpReplicaCurrentGhost1) q,
      s.profile = z.1.1.1 ∧ HEq s.orbitLabel z.2.2 ∧
        HEq s.selector (Finset.univ \ {c}) ∧
        @HEq
          (StatMech.Sharpness.FluxEdgeCopy.Copy
            (lpReplicaCurrentGraph G sites) s.profile -> LPReplicaRowTag)
          (lpReplicaToggleRows G sites s.profile s.selector s.tag)
          (StatMech.Sharpness.FluxEdgeCopy.Copy
            (lpReplicaCurrentGraph G sites) z.1.1.1 -> LPReplicaRowTag)
          (lpReplicaToggleRows G sites z.1.1.1 {c}
            (lpReplicaDecoratedSourceRowGateData G sites i j q z).1) ∧
        ∃ y : LPReplicaDecoratedOrbitAtom G sites
            (lpMatchingSeamSource
              (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j)
            (lpMatchingSeamSource
                (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i ∆
              lpMatchingGhostSource
                (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
                lpReplicaCurrentGhost1) q,
          LPReplicaOffdiagBalancedOutput G sites i j q (Sum.inr y) ∧
            (lpReplicaOffdiagDecoratedTargetBranchedSlotState G sites i j q
                (Sum.inr y)).2 =
              lpReplicaOrbitFourColorSlotCrossToggle G sites q
                (lpReplicaOrbitCommonSlotsOfCopies G sites q z.1.1.1
                  z.1.1.2 z.2.2 {c})
                (lpReplicaOffdiagDecoratedSourceSlotState
                  G sites i j q z) ∧
            ∃ s' : LPReplicaBalancedSelector G sites
                (lpMatchingSeamSource
                      (lpReplicaCurrentLeft sites)
                      (lpReplicaCurrentRight sites) j ∆
                    lpMatchingSeamSource
                      (lpReplicaCurrentLeft sites)
                      (lpReplicaCurrentRight sites) i ∆
                    lpMatchingGhostSource
                      (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
                      lpReplicaCurrentGhost1)
                (lpMatchingSeamSource
                      (lpReplicaCurrentLeft sites)
                      (lpReplicaCurrentRight sites) i ∆
                    lpMatchingGhostSource
                      (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
                      lpReplicaCurrentGhost1) q,
              y = lpReplicaDecoratedOrbitAtomOfBalancedSelector_left
                  G sites j i q s' ∧
                s'.profile = s.profile ∧
                HEq s'.selector s.selector ∧ HEq s'.tag s.tag := by
  classical
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
  let P : Finset (StatMech.Sharpness.FluxEdgeCopy.Copy
      (lpReplicaCurrentGraph G sites) m) := Finset.univ \ {c}
  have hctag0 : d0.1 c = (true, false) := by
    simpa only [K, lpReplicaCurrentCopies, Finset.mem_filter,
      Finset.mem_univ, true_and] using hcK
  have hcurrent : (d.1 c).2 = false := by
    change (lpReplicaSwapRowsTag d0.1 c).2 = false
    simp only [lpReplicaSwapRowsTag, hctag0]
  have hcurr := lpReplicaRowGate_compl_singleton_currentSources
    G sites m B d.1 d.2 c hcurrent
  have hcends : E c = s(lpReplicaCurrentLeft sites j,
      lpReplicaCurrentRight sites j) := by
    simpa only [E, m, StatMech.Sharpness.FluxEdgeCopy.endsM] using hc
  have hsingle : StatMech.Sharpness.RandomCurrent.sources E {c} = Sj := by
    simpa only [Sj, lpMatchingSeamSource] using
      randomCurrent_sources_singleton_of_ends_eq E c (by
        simp [lpReplicaCurrentLeft, lpReplicaCurrentRight]) hcends
  have hBswap : B = Sj ∆ Si ∆ T := by
    change Si ∆ Sj ∆ T = Sj ∆ Si ∆ T
    rw [symmDiff_comm Si Sj]
  have hfalseSource : StatMech.Sharpness.RandomCurrent.sources E
      (P.filter fun a => (d.1 a).2 = false) = Si ∆ T := by
    calc
      _ = B ∆ StatMech.Sharpness.RandomCurrent.sources E {c} := by
        simpa only [P, E] using hcurr.1
      _ = B ∆ Sj := by rw [hsingle]
      _ = Si ∆ T := by
        rw [hBswap, symmDiff_assoc Sj Si T,
          symmDiff_symmDiff_self']
  have htrueSource : StatMech.Sharpness.RandomCurrent.sources E
      (P.filter fun a => (d.1 a).2 = true) = ∅ := by
    simpa only [P, E, B] using hcurr.2
  have hmove : lpReplicaToggleRows G sites m P d.1 =
      lpReplicaToggleRows G sites m {c} d0.1 := by
    simpa only [P, d, d0,
      lpReplicaDecoratedSourceSwappedRowGateData] using
        lpReplicaToggleRows_univ_sdiff_singleton_swapRowsTag
          G sites m d0.1 c
  have hrow1Eq : lpReplicaRowCopies G sites m
      (lpReplicaToggleRows G sites m P d.1) true =
        lpReplicaRowCopies G sites m d0.1 true \ {c} := by
    rw [hmove]
    ext a
    by_cases hac : a = c
    · subst a
      simp [lpReplicaRowCopies, lpReplicaToggleRows, hctag0]
    · simp [lpReplicaRowCopies, lpReplicaToggleRows, hac]
  have hrow1Disconn : ¬ StatMech.Sharpness.RandomCurrent.connK E
      (lpReplicaRowCopies G sites m
        (lpReplicaToggleRows G sites m P d.1) true)
      lpReplicaCurrentGhost0 lpReplicaCurrentGhost1 := by
    intro hconn
    apply d0.2.2.2.2.2.2
    apply StatMech.GrahamGHS.FourColor.connK_mono _ hconn
    rw [hrow1Eq]
    exact Finset.sdiff_subset
  have hrow0Sub : lpReplicaRowCopies G sites m
      (lpReplicaToggleRows G sites m P d.1) false ⊆ {c} ∪ C := by
    rw [hmove]
    intro a ha
    simp only [lpReplicaRowCopies, lpReplicaToggleRows, Finset.mem_filter,
      Finset.mem_univ, true_and, Finset.mem_union, Finset.mem_singleton] at ha ⊢
    by_cases hac : a = c
    · exact Or.inl hac
    · right
      apply Finset.mem_sdiff.mpr
      refine ⟨Finset.mem_univ a, ?_⟩
      intro haK
      have hatag : d0.1 a = (true, false) := by
        simpa only [K, lpReplicaCurrentCopies, Finset.mem_filter,
          Finset.mem_univ, true_and] using haK
      simp [hac, hatag] at ha
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
      Finset.card_univ, hcopyCard]
    have hKcard : K.card = 3 := by
      simpa only [K, d0] using hthree
    omega
  obtain ⟨e0, he0C⟩ : C.Nonempty := Finset.card_pos.mp (by omega)
  have hsame : ∀ e ∈ C, e.1.1 = e0.1.1 := by
    intro e he
    exact lpReplicaOffdiagDecoratedSource_rank_five_complement_same_edge
      G sites hsite hij q hcard z hthree e he e0 he0C
  have hrow0Disconn : ¬ StatMech.Sharpness.RandomCurrent.connK E
      (lpReplicaRowCopies G sites m
        (lpReplicaToggleRows G sites m P d.1) false)
      lpReplicaCurrentGhost0 lpReplicaCurrentGhost1 := by
    intro hconn
    exact lpReplica_seam_union_parallelCopies_ghost_disconnected
      G sites j m c e0 C hc hsame
        (StatMech.GrahamGHS.FourColor.connK_mono hrow0Sub hconn)
  let s : LPReplicaBalancedSelector G sites B (Si ∆ T) q := {
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
  refine ⟨s, rfl, HEq.rfl, HEq.rfl, heq_of_eq hmove, ?_⟩
  let sourceTag := lpReplicaOrientedFourColorTag G sites ∅ B q
    (lpReplicaDecoratedOrbitAtomEquivOrientedFourColor G sites ∅ B q z)
  have hsourceTag : sourceTag = d0.1 := by
    exact lpReplicaOffdiagDecoratedSource_orientedTag_eq_rowGateData
      G sites i j q z
  have hfixed : c.1 ∈ lpReplicaCurrentEdgeOrbitFixed G sites :=
    lpReplicaCurrentEdge_mem_orbitFixed_of_eq_seam G sites j m c hc
  let s' : LPReplicaBalancedSelector G sites (Sj ∆ Si ∆ T) (Si ∆ T) q := {
    profile := s.profile
    orbit := s.orbit
    tag := s.tag
    gate := by
      change LPReplicaRowGate G sites s.profile (Sj ∆ Si ∆ T) ∅ s.tag
      rw [symmDiff_comm Sj Si]
      exact s.gate
    orbitLabel := s.orbitLabel
    selector := s.selector
    falseSource := s.falseSource
    trueSource := s.trueSource
    row0Disconn := s.row0Disconn
    row1Disconn := s.row1Disconn }
  have hgeneric := lpReplicaBalancedSelector_slotState_of_singletonToggle
    G sites Sj Si T q s' c sourceTag (by
      rw [hsourceTag]
      exact hmove) hfixed
  have hfixedD : (Si ∆ T).map lpReplicaCurrentReflect.toEmbedding =
      Si ∆ T := lpReplicaCurrentReflect_seam_symmDiff_ghost G sites i
  let y := lpReplicaDecoratedOrbitAtomOfBalancedSelector_left
    G sites j i q s'
  refine ⟨y, Or.inr ⟨s', rfl⟩, ?_,
    ⟨s', rfl, rfl, HEq.rfl, HEq.rfl⟩⟩
  change (lpReplicaOffdiagDecoratedTargetBranchedSlotState G sites j i q
    (Sum.inl y)).2 = _
  unfold lpReplicaOffdiagDecoratedTargetBranchedSlotState
  unfold y lpReplicaDecoratedOrbitAtomOfBalancedSelector_left
  dsimp only
  rw [lpReplicaOrientedFourColorSlotState_cast_boundary G sites Sj
    ((Si ∆ T).map lpReplicaCurrentReflect.toEmbedding) (Si ∆ T) q hfixedD]
  exact hgeneric



noncomputable def lpReplicaDecoratedOrbitAtomOfBalancedSelector_right
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (s : LPReplicaBalancedSelector G sites
      (lpMatchingSeamSource
            (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i ∆
          lpMatchingSeamSource
            (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j ∆
          lpMatchingGhostSource
            (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
            lpReplicaCurrentGhost1)
      (lpMatchingSeamSource
            (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i ∆
          lpMatchingGhostSource
            (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
            lpReplicaCurrentGhost1) q) :
    LPReplicaDecoratedOrbitAtom G sites
      (lpMatchingSeamSource
        (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j)
      (lpMatchingSeamSource
          (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i ∆
        lpMatchingGhostSource
          (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
          lpReplicaCurrentGhost1) q := by
  let s' : LPReplicaBalancedSelector G sites
      (lpMatchingSeamSource
            (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j ∆
          lpMatchingSeamSource
            (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i ∆
          lpMatchingGhostSource
            (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
            lpReplicaCurrentGhost1)
      (lpMatchingSeamSource
            (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i ∆
          lpMatchingGhostSource
            (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
            lpReplicaCurrentGhost1) q := {
    profile := s.profile
    orbit := s.orbit
    tag := s.tag
    gate := by
      simpa only [symmDiff_comm
        (lpMatchingSeamSource
          (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i)
        (lpMatchingSeamSource
          (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j)] using
        s.gate
    orbitLabel := s.orbitLabel
    selector := s.selector
    falseSource := s.falseSource
    trueSource := s.trueSource
    row0Disconn := s.row0Disconn
    row1Disconn := s.row1Disconn }
  exact lpReplicaDecoratedOrbitAtomOfBalancedSelector_left
    G sites j i q s'

set_option maxHeartbeats 1000000 in



theorem lpReplicaOffdiagDecoratedSource_rank_five_saturated_target_of_iSeam
    (G : SimpleGraph V) (sites : I -> V) {i j : I}
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (z : LPReplicaOffdiagDecoratedSource G sites i j q)
    (hsat : lpReplicaCurrentCopies G sites z.1.1.1
      (lpReplicaDecoratedSourceRowGateData G sites i j q z).1 true false =
        Finset.univ)
    (c : StatMech.Sharpness.FluxEdgeCopy.Copy
      (lpReplicaCurrentGraph G sites) z.1.1.1)
    (hc : c.1.1 = lpReplicaCurrentSeamEdge sites i) :
    ∃ y : LPReplicaDecoratedOrbitAtom G sites
        (lpMatchingSeamSource
          (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i)
        (lpMatchingSeamSource
            (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j ∆
          lpMatchingGhostSource
            (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
            lpReplicaCurrentGhost1) q,
      LPReplicaOffdiagBalancedOutput G sites i j q (Sum.inl y) ∧
        (lpReplicaOffdiagDecoratedTargetBranchedSlotState G sites i j q
            (Sum.inl y)).2 =
          lpReplicaOrbitFourColorSlotCrossToggle G sites q
            (lpReplicaOrbitCommonSlotsOfCopies G sites q z.1.1.1
              z.1.1.2 z.2.2 {c})
            (lpReplicaOffdiagDecoratedSourceSlotState G sites i j q z) := by
  classical
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
  let P : Finset (StatMech.Sharpness.FluxEdgeCopy.Copy
      (lpReplicaCurrentGraph G sites) m) := Finset.univ \ {c}
  have hall (a) : d0.1 a = (true, false) := by
    have ha : a ∈ lpReplicaCurrentCopies G sites m d0.1 true false := by
      rw [hsat]
      exact Finset.mem_univ a
    simpa only [lpReplicaCurrentCopies, Finset.mem_filter,
      Finset.mem_univ, true_and] using ha
  have hctag0 : d0.1 c = (true, false) := hall c
  have hcurrent : (d.1 c).2 = false := by
    change (lpReplicaSwapRowsTag d0.1 c).2 = false
    simp only [lpReplicaSwapRowsTag, hctag0]
  have hcurr := lpReplicaRowGate_compl_singleton_currentSources
    G sites m B d.1 d.2 c hcurrent
  have hcends : E c = s(lpReplicaCurrentLeft sites i,
      lpReplicaCurrentRight sites i) := by
    simpa only [E, m, StatMech.Sharpness.FluxEdgeCopy.endsM] using hc
  have hsingle : StatMech.Sharpness.RandomCurrent.sources E {c} = Si := by
    simpa only [Si, lpMatchingSeamSource] using
      randomCurrent_sources_singleton_of_ends_eq E c (by
        simp [lpReplicaCurrentLeft, lpReplicaCurrentRight]) hcends
  have hfalseSource : StatMech.Sharpness.RandomCurrent.sources E
      (P.filter fun a => (d.1 a).2 = false) = Sj ∆ T := by
    calc
      _ = B ∆ StatMech.Sharpness.RandomCurrent.sources E {c} := by
        simpa only [P, E] using hcurr.1
      _ = B ∆ Si := by rw [hsingle]
      _ = Sj ∆ T := by
        change (Si ∆ Sj ∆ T) ∆ Si = Sj ∆ T
        rw [symmDiff_assoc Si Sj T, symmDiff_symmDiff_self']
  have htrueSource : StatMech.Sharpness.RandomCurrent.sources E
      (P.filter fun a => (d.1 a).2 = true) = ∅ := by
    simpa only [P, E, B] using hcurr.2
  have hmove : lpReplicaToggleRows G sites m P d.1 =
      lpReplicaToggleRows G sites m {c} d0.1 := by
    simpa only [P, d, d0,
      lpReplicaDecoratedSourceSwappedRowGateData] using
        lpReplicaToggleRows_univ_sdiff_singleton_swapRowsTag
          G sites m d0.1 c
  have hrow1Sub : lpReplicaRowCopies G sites m
      (lpReplicaToggleRows G sites m P d.1) true ⊆
        lpReplicaRowCopies G sites m d0.1 true := by
    rw [hmove]
    intro a ha
    simp only [lpReplicaRowCopies, lpReplicaToggleRows, Finset.mem_filter,
      Finset.mem_univ, true_and] at ha ⊢
    exact congrArg Prod.fst (hall a)
  have hrow1Disconn : ¬ StatMech.Sharpness.RandomCurrent.connK E
      (lpReplicaRowCopies G sites m
        (lpReplicaToggleRows G sites m P d.1) true)
      lpReplicaCurrentGhost0 lpReplicaCurrentGhost1 := by
    intro hconn
    exact d0.2.2.2.2.2.2
      (StatMech.GrahamGHS.FourColor.connK_mono hrow1Sub hconn)
  have hrow0Sub : lpReplicaRowCopies G sites m
      (lpReplicaToggleRows G sites m P d.1) false ⊆ {c} := by
    rw [hmove]
    intro a ha
    simp only [lpReplicaRowCopies, lpReplicaToggleRows, Finset.mem_filter,
      Finset.mem_univ, true_and, Finset.mem_singleton] at ha ⊢
    by_contra hac
    simp only [hac, if_neg] at ha
    exact Bool.false_ne_true (ha.symm.trans (congrArg Prod.fst (hall a)))
  have hsingleDisconn : ¬ StatMech.Sharpness.RandomCurrent.connK E {c}
      lpReplicaCurrentGhost0 lpReplicaCurrentGhost1 := by
    intro hconn
    have hghost : (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V) ≠
        lpReplicaCurrentGhost1 := by
      simp [lpReplicaCurrentGhost0, lpReplicaCurrentGhost1]
    obtain ⟨a, ha, hg0⟩ := exists_mem_ends_of_connK_of_ne E
      {c} hghost hconn
    have hac : a = c := by simpa only [Finset.mem_singleton] using ha
    subst a
    change (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V) ∈ c.1.1 at hg0
    rw [hc] at hg0
    simp [lpReplicaCurrentSeamEdge, lpReplicaCurrentLeft,
      lpReplicaCurrentRight, lpReplicaCurrentGhost0] at hg0
  have hrow0Disconn : ¬ StatMech.Sharpness.RandomCurrent.connK E
      (lpReplicaRowCopies G sites m
        (lpReplicaToggleRows G sites m P d.1) false)
      lpReplicaCurrentGhost0 lpReplicaCurrentGhost1 := by
    intro hconn
    exact hsingleDisconn
      (StatMech.GrahamGHS.FourColor.connK_mono hrow0Sub hconn)
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
  let sourceTag := lpReplicaOrientedFourColorTag G sites ∅ B q
    (lpReplicaDecoratedOrbitAtomEquivOrientedFourColor G sites ∅ B q z)
  have hsourceTag : sourceTag = d0.1 :=
    lpReplicaOffdiagDecoratedSource_orientedTag_eq_rowGateData
      G sites i j q z
  have hfixed : c.1 ∈ lpReplicaCurrentEdgeOrbitFixed G sites :=
    lpReplicaCurrentEdge_mem_orbitFixed_of_eq_seam G sites i m c hc
  have hgeneric := lpReplicaBalancedSelector_slotState_of_singletonToggle
    G sites Si Sj T q s c sourceTag (by
      rw [hsourceTag]
      exact hmove) hfixed
  have hfixedD : (Sj ∆ T).map lpReplicaCurrentReflect.toEmbedding =
      Sj ∆ T := lpReplicaCurrentReflect_seam_symmDiff_ghost G sites j
  refine ⟨lpReplicaDecoratedOrbitAtomOfBalancedSelector_left
    G sites i j q s, Or.inl ⟨s, rfl⟩, ?_⟩
  unfold lpReplicaOffdiagDecoratedTargetBranchedSlotState
  unfold lpReplicaDecoratedOrbitAtomOfBalancedSelector_left
  dsimp only
  rw [lpReplicaOrientedFourColorSlotState_cast_boundary G sites Si
    ((Sj ∆ T).map lpReplicaCurrentReflect.toEmbedding) (Sj ∆ T) q hfixedD]
  exact hgeneric

set_option maxHeartbeats 600000 in



theorem lpReplicaOffdiagDecoratedSource_rank_five_saturated_target_mask_four_of_iSeam
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites) {i j : I} (hij : i ≠ j)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
    (z : LPReplicaOffdiagDecoratedSource G sites i j q)
    (hsat : lpReplicaCurrentCopies G sites z.1.1.1
      (lpReplicaDecoratedSourceRowGateData G sites i j q z).1 true false =
        Finset.univ)
    (c : StatMech.Sharpness.FluxEdgeCopy.Copy
      (lpReplicaCurrentGraph G sites) z.1.1.1)
    (hc : c.1.1 = lpReplicaCurrentSeamEdge sites i) :
    ∃ y : LPReplicaOffdiagDecoratedTarget G sites i j q,
      LPReplicaOffdiagBalancedOutput G sites i j q y ∧
        lpReplicaOffdiagDecoratedTargetCrossTrace G sites i j q y =
          lpReplicaOffdiagDecoratedSourceCrossTrace G sites i j q z ∧
        (lpReplicaOrbitFourColorSlotRowMask G sites q
          (lpReplicaOffdiagDecoratedTargetBranchedSlotState
            G sites i j q y).2).card = 4 := by
  classical
  obtain ⟨y, hyBal, hstate⟩ :=
    lpReplicaOffdiagDecoratedSource_rank_five_saturated_target_of_iSeam
      G sites q z hsat c hc
  let Y : LPReplicaOffdiagDecoratedTarget G sites i j q := Sum.inl y
  refine ⟨Y, hyBal, ?_, ?_⟩
  · unfold lpReplicaOffdiagDecoratedTargetCrossTrace
      lpReplicaOffdiagDecoratedSourceCrossTrace
    rw [hstate]
    exact lpReplicaOrbitFourColorSlotCrossNormalize_crossToggle
      G sites q _ _
  · let slot := lpReplicaProfileCopyEquivCommonSlot G sites q z.1.1.1
      z.1.1.2 z.2.2 c
    have hsourceMask :=
      lpReplicaOffdiagDecoratedSource_rank_five_saturated_rowMask_eq_univ
        G sites hsite hij q hcard z hsat
    change (lpReplicaOrbitFourColorSlotRowMask G sites q
      (lpReplicaOffdiagDecoratedTargetBranchedSlotState
        G sites i j q (Sum.inl y)).2).card = 4
    rw [hstate, lpReplicaOrbitFourColorSlotRowMask_crossToggle, hsourceMask]
    have hslots : lpReplicaOrbitCommonSlotsOfCopies G sites q z.1.1.1
        z.1.1.2 z.2.2 {c} = {slot} := by
      unfold lpReplicaOrbitCommonSlotsOfCopies
      rw [Finset.map_singleton]
      rfl
    have hdiff : (Finset.univ ∆ ({slot} : Finset
        (LPReplicaOrbitCommonSlot G sites q))) = Finset.univ \ {slot} := by
      ext x
      simp [Finset.mem_symmDiff]
    rw [hslots, hdiff, Finset.card_sdiff_of_subset (Finset.subset_univ _),
      Finset.card_univ, hcard, Finset.card_singleton]



theorem lpReplicaOffdiagDecoratedSource_rank_five_saturated_pairedCut_half_eq_empty
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (z : LPReplicaOffdiagDecoratedSource G sites i j q)
    (hsat : lpReplicaCurrentCopies G sites z.1.1.1
      (lpReplicaDecoratedSourceRowGateData G sites i j q z).1 true false =
        Finset.univ)
    (cut : LPReplicaCoupledPairedCut G sites z.1.1.1
      (lpMatchingSeamSource
            (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i ∆
          lpMatchingSeamSource
            (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j ∆
          lpMatchingGhostSource
            (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
            lpReplicaCurrentGhost1)
      (lpReplicaDecoratedSourceSwappedRowGateData G sites i j q z).1) :
    cut.half = ∅ := by
  classical
  let d0 := lpReplicaDecoratedSourceRowGateData G sites i j q z
  let d := lpReplicaDecoratedSourceSwappedRowGateData G sites i j q z
  have hall (a) : d0.1 a = (true, false) := by
    have ha : a ∈ lpReplicaCurrentCopies G sites z.1.1.1
        d0.1 true false := by
      rw [hsat]
      exact Finset.mem_univ a
    simpa only [lpReplicaCurrentCopies, Finset.mem_filter,
      Finset.mem_univ, true_and] using ha
  have hempty : lpReplicaCurrentCopies G sites z.1.1.1
      d.1 true false = ∅ := by
    ext a
    constructor
    · intro ha
      have htag : d.1 a = (true, false) := by
        simpa only [lpReplicaCurrentCopies, Finset.mem_filter,
          Finset.mem_univ, true_and] using ha
      change lpReplicaSwapRowsTag d0.1 a = (true, false) at htag
      simp [lpReplicaSwapRowsTag, hall a] at htag
    · simp
  apply LPReplicaCoupledPairedCut.half_eq_empty_of_row1False_empty
    G sites z.1.1.1
      (lpMatchingSeamSource
            (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i ∆
          lpMatchingSeamSource
            (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j ∆
          lpMatchingGhostSource
            (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
            lpReplicaCurrentGhost1)
      d.1 cut
  simpa only [d, lpReplicaDecoratedSourceSwappedRowGateData] using hempty



theorem lpReplicaOffdiagDecoratedSource_rank_five_saturated_pairedCut_doubledHalf_eq_empty
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (z : LPReplicaOffdiagDecoratedSource G sites i j q)
    (hsat : lpReplicaCurrentCopies G sites z.1.1.1
      (lpReplicaDecoratedSourceRowGateData G sites i j q z).1 true false =
        Finset.univ)
    (cut : LPReplicaCoupledPairedCut G sites z.1.1.1
      (lpMatchingSeamSource
            (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i ∆
          lpMatchingSeamSource
            (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j ∆
          lpMatchingGhostSource
            (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
            lpReplicaCurrentGhost1)
      (lpReplicaDecoratedSourceSwappedRowGateData G sites i j q z).1) :
    cut.half ∆ cut.half.map lpReplicaCurrentReflect.toEmbedding = ∅ := by
  rw [lpReplicaOffdiagDecoratedSource_rank_five_saturated_pairedCut_half_eq_empty
    G sites i j q z hsat cut]
  simp

set_option maxHeartbeats 1200000 in



theorem lpReplicaOffdiagDecoratedSource_rank_five_exists_target_of_active_card_eq_three
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites) {i j : I} (hij : i ≠ j)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
    (z : LPReplicaOffdiagDecoratedSource G sites i j q)
    (hthree : (lpReplicaCurrentCopies G sites z.1.1.1
      (lpReplicaDecoratedSourceRowGateData G sites i j q z).1
        true false).card = 3) :
    ∃ (y : LPReplicaOffdiagDecoratedTarget G sites i j q)
      (c : StatMech.Sharpness.FluxEdgeCopy.Copy
        (lpReplicaCurrentGraph G sites) z.1.1.1),
      LPReplicaOffdiagBalancedOutput G sites i j q y ∧
        (c.1.1 = lpReplicaCurrentSeamEdge sites i ∨
          c.1.1 = lpReplicaCurrentSeamEdge sites j) ∧
        (lpReplicaOffdiagDecoratedTargetBranchedSlotState
            G sites i j q y).2 =
          lpReplicaOrbitFourColorSlotCrossToggle G sites q
            (lpReplicaOrbitCommonSlotsOfCopies G sites q z.1.1.1
              z.1.1.2 z.2.2 {c})
            (lpReplicaOffdiagDecoratedSourceSlotState G sites i j q z) := by
  classical
  rcases lpReplicaOffdiagDecoratedSource_rank_five_exists_seamCopy_of_active_card_eq_three
      G sites hsite hij q hcard z hthree with
    ⟨c, hcK, hc⟩ | ⟨c, hcK, hc⟩
  · obtain ⟨_s, _hp, _hL, _hP, _hmove, y, hyBal, hy, _hyPres⟩ :=
      lpReplicaOffdiagDecoratedSource_rank_five_balancedSelector_of_iSeam
        G sites hsite hij q hcard z hthree c hcK hc
    exact ⟨Sum.inl y, c, hyBal, Or.inl hc, hy⟩
  · obtain ⟨_s, _hp, _hL, _hP, _hmove, y, hyBal, hy, _hyPres⟩ :=
      lpReplicaOffdiagDecoratedSource_rank_five_balancedSelector_of_jSeam
        G sites hsite hij q hcard z hthree c hcK hc
    exact ⟨Sum.inr y, c, hyBal, Or.inr hc, hy⟩



theorem lpReplicaOffdiagBalancedOutputCrossTraceFiber_rank_five_nonempty_of_active_card_eq_three
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites) {i j : I} (hij : i ≠ j)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
    (z : LPReplicaOffdiagDecoratedSource G sites i j q)
    (hthree : (lpReplicaCurrentCopies G sites z.1.1.1
      (lpReplicaDecoratedSourceRowGateData G sites i j q z).1
        true false).card = 3) :
    (lpReplicaOffdiagBalancedOutputCrossTraceFiber G sites i j q
      (lpReplicaOffdiagDecoratedSourceCrossTrace G sites i j q z)).Nonempty := by
  classical
  obtain ⟨y, c, hyBal, _, hstate⟩ :=
    lpReplicaOffdiagDecoratedSource_rank_five_exists_target_of_active_card_eq_three
      G sites hsite hij q hcard z hthree
  refine ⟨y, ?_⟩
  simp only [lpReplicaOffdiagBalancedOutputCrossTraceFiber,
    Finset.mem_filter]
  constructor
  · simp only [lpReplicaOffdiagBalancedOutputs, Finset.mem_filter,
      Finset.mem_univ, true_and]
    exact hyBal
  · unfold lpReplicaOffdiagDecoratedTargetCrossTrace
      lpReplicaOffdiagDecoratedSourceCrossTrace
    rw [hstate]
    exact lpReplicaOrbitFourColorSlotCrossNormalize_crossToggle
      G sites q _ _



theorem lpReplicaOffdiagBalancedOutputCrossTraceFiber_rank_five_card_ge_three_of_iSeam_parallelPair
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites) {i j : I} (hij : i ≠ j)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
    (z : LPReplicaOffdiagDecoratedSource G sites i j q)
    (hthree : (lpReplicaCurrentCopies G sites z.1.1.1
      (lpReplicaDecoratedSourceRowGateData G sites i j q z).1
        true false).card = 3)
    (k c e : StatMech.Sharpness.FluxEdgeCopy.Copy
      (lpReplicaCurrentGraph G sites) z.1.1.1)
    (hkK : k ∈ lpReplicaCurrentCopies G sites z.1.1.1
      (lpReplicaDecoratedSourceRowGateData G sites i j q z).1 true false)
    (hk : k.1.1 = lpReplicaCurrentSeamEdge sites i)
    (hcC : c ∈ Finset.univ \ lpReplicaCurrentCopies G sites z.1.1.1
      (lpReplicaDecoratedSourceRowGateData G sites i j q z).1 true false)
    (heC : e ∈ Finset.univ \ lpReplicaCurrentCopies G sites z.1.1.1
      (lpReplicaDecoratedSourceRowGateData G sites i j q z).1 true false)
    (hck : c.1.1 = k.1.1) (hek : e.1.1 = k.1.1)
    (hctag : (lpReplicaDecoratedSourceRowGateData G sites i j q z).1 c =
      (false, false))
    (hetag : (lpReplicaDecoratedSourceRowGateData G sites i j q z).1 e =
      (false, false))
    (hce : c ≠ e) :
    3 ≤ (lpReplicaOffdiagBalancedOutputCrossTraceFiber G sites i j q
      (lpReplicaOffdiagDecoratedSourceCrossTrace G sites i j q z)).card := by
  classical
  obtain ⟨_s, _hp, _hL, _hP, _hmove, yk, hykBal, hykState,
      _hykPres⟩ :=
    lpReplicaOffdiagDecoratedSource_rank_five_balancedSelector_of_iSeam
      G sites hsite hij q hcard z hthree k hkK hk
  obtain ⟨yc, hycBal, hycState⟩ :=
    lpReplicaOffdiagDecoratedSource_rank_five_target_of_iSeam_parallelInactive
      G sites hsite hij q hcard z hthree k c hkK hk hcC hck hctag
  obtain ⟨ye, hyeBal, hyeState⟩ :=
    lpReplicaOffdiagDecoratedSource_rank_five_target_of_iSeam_parallelInactive
      G sites hsite hij q hcard z hthree k e hkK hk heC hek hetag
  let Yk : LPReplicaOffdiagDecoratedTarget G sites i j q := Sum.inl yk
  let Yc : LPReplicaOffdiagDecoratedTarget G sites i j q := Sum.inl yc
  let Ye : LPReplicaOffdiagDecoratedTarget G sites i j q := Sum.inl ye
  have targetMem (y : LPReplicaOffdiagDecoratedTarget G sites i j q)
      (hyBal : LPReplicaOffdiagBalancedOutput G sites i j q y)
      (P : Finset (LPReplicaOrbitCommonSlot G sites q))
      (hstate : (lpReplicaOffdiagDecoratedTargetBranchedSlotState
          G sites i j q y).2 =
        lpReplicaOrbitFourColorSlotCrossToggle G sites q P
          (lpReplicaOffdiagDecoratedSourceSlotState G sites i j q z)) :
      y ∈ lpReplicaOffdiagBalancedOutputCrossTraceFiber G sites i j q
        (lpReplicaOffdiagDecoratedSourceCrossTrace G sites i j q z) := by
    simp only [lpReplicaOffdiagBalancedOutputCrossTraceFiber,
      Finset.mem_filter]
    constructor
    · simp only [lpReplicaOffdiagBalancedOutputs, Finset.mem_filter,
        Finset.mem_univ, true_and]
      exact hyBal
    · unfold lpReplicaOffdiagDecoratedTargetCrossTrace
        lpReplicaOffdiagDecoratedSourceCrossTrace
      rw [hstate]
      exact lpReplicaOrbitFourColorSlotCrossNormalize_crossToggle
        G sites q _ _
  have hYk := targetMem Yk hykBal _ hykState
  have hYc := targetMem Yc hycBal _ hycState
  have hYe := targetMem Ye hyeBal _ hyeState
  have hkc : k ≠ c := by
    intro h
    subst c
    exact (Finset.mem_sdiff.mp hcC).2 hkK
  have hke : k ≠ e := by
    intro h
    subst e
    exact (Finset.mem_sdiff.mp heC).2 hkK
  have hYkc : Yk ≠ Yc :=
    lpReplicaOffdiagDecoratedTarget_ne_of_singletonCrossToggle
      G sites i j q z Yk Yc k c hykState hycState hkc
  have hYke : Yk ≠ Ye :=
    lpReplicaOffdiagDecoratedTarget_ne_of_singletonCrossToggle
      G sites i j q z Yk Ye k e hykState hyeState hke
  have hYce : Yc ≠ Ye :=
    lpReplicaOffdiagDecoratedTarget_ne_of_singletonCrossToggle
      G sites i j q z Yc Ye c e hycState hyeState hce
  calc
    3 = ({Yk, Yc, Ye} : Finset
        (LPReplicaOffdiagDecoratedTarget G sites i j q)).card := by
      simp [hYkc, hYke, hYce]
    _ ≤ (lpReplicaOffdiagBalancedOutputCrossTraceFiber G sites i j q
        (lpReplicaOffdiagDecoratedSourceCrossTrace G sites i j q z)).card :=
      Finset.card_le_card (by
        intro y hy
        simp only [Finset.mem_insert, Finset.mem_singleton] at hy
        rcases hy with rfl | rfl | rfl
        · exact hYk
        · exact hYc
        · exact hYe)
 



theorem lpReplicaOffdiagBalancedOutputCrossTraceFiber_rank_five_card_ge_three_of_jSeam_parallelPair
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites) {i j : I} (hij : i ≠ j)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
    (z : LPReplicaOffdiagDecoratedSource G sites i j q)
    (hthree : (lpReplicaCurrentCopies G sites z.1.1.1
      (lpReplicaDecoratedSourceRowGateData G sites i j q z).1
        true false).card = 3)
    (k c e : StatMech.Sharpness.FluxEdgeCopy.Copy
      (lpReplicaCurrentGraph G sites) z.1.1.1)
    (hkK : k ∈ lpReplicaCurrentCopies G sites z.1.1.1
      (lpReplicaDecoratedSourceRowGateData G sites i j q z).1 true false)
    (hk : k.1.1 = lpReplicaCurrentSeamEdge sites j)
    (hcC : c ∈ Finset.univ \ lpReplicaCurrentCopies G sites z.1.1.1
      (lpReplicaDecoratedSourceRowGateData G sites i j q z).1 true false)
    (heC : e ∈ Finset.univ \ lpReplicaCurrentCopies G sites z.1.1.1
      (lpReplicaDecoratedSourceRowGateData G sites i j q z).1 true false)
    (hck : c.1.1 = k.1.1) (hek : e.1.1 = k.1.1)
    (hctag : (lpReplicaDecoratedSourceRowGateData G sites i j q z).1 c =
      (false, false))
    (hetag : (lpReplicaDecoratedSourceRowGateData G sites i j q z).1 e =
      (false, false))
    (hce : c ≠ e) :
    3 ≤ (lpReplicaOffdiagBalancedOutputCrossTraceFiber G sites i j q
      (lpReplicaOffdiagDecoratedSourceCrossTrace G sites i j q z)).card := by
  classical
  obtain ⟨_s, _hp, _hL, _hP, _hmove, yk, hykBal, hykState,
      _hykPres⟩ :=
    lpReplicaOffdiagDecoratedSource_rank_five_balancedSelector_of_jSeam
      G sites hsite hij q hcard z hthree k hkK hk
  obtain ⟨yc, hycBal, hycState⟩ :=
    lpReplicaOffdiagDecoratedSource_rank_five_target_of_jSeam_parallelInactive
      G sites hsite hij q hcard z hthree k c hkK hk hcC hck hctag
  obtain ⟨ye, hyeBal, hyeState⟩ :=
    lpReplicaOffdiagDecoratedSource_rank_five_target_of_jSeam_parallelInactive
      G sites hsite hij q hcard z hthree k e hkK hk heC hek hetag
  let Yk : LPReplicaOffdiagDecoratedTarget G sites i j q := Sum.inr yk
  let Yc : LPReplicaOffdiagDecoratedTarget G sites i j q := Sum.inr yc
  let Ye : LPReplicaOffdiagDecoratedTarget G sites i j q := Sum.inr ye
  have targetMem (y : LPReplicaOffdiagDecoratedTarget G sites i j q)
      (hyBal : LPReplicaOffdiagBalancedOutput G sites i j q y)
      (P : Finset (LPReplicaOrbitCommonSlot G sites q))
      (hstate : (lpReplicaOffdiagDecoratedTargetBranchedSlotState
          G sites i j q y).2 =
        lpReplicaOrbitFourColorSlotCrossToggle G sites q P
          (lpReplicaOffdiagDecoratedSourceSlotState G sites i j q z)) :
      y ∈ lpReplicaOffdiagBalancedOutputCrossTraceFiber G sites i j q
        (lpReplicaOffdiagDecoratedSourceCrossTrace G sites i j q z) := by
    simp only [lpReplicaOffdiagBalancedOutputCrossTraceFiber,
      Finset.mem_filter]
    constructor
    · simp only [lpReplicaOffdiagBalancedOutputs, Finset.mem_filter,
        Finset.mem_univ, true_and]
      exact hyBal
    · unfold lpReplicaOffdiagDecoratedTargetCrossTrace
        lpReplicaOffdiagDecoratedSourceCrossTrace
      rw [hstate]
      exact lpReplicaOrbitFourColorSlotCrossNormalize_crossToggle
        G sites q _ _
  have hYk := targetMem Yk hykBal _ hykState
  have hYc := targetMem Yc hycBal _ hycState
  have hYe := targetMem Ye hyeBal _ hyeState
  have hkc : k ≠ c := by
    intro h
    subst c
    exact (Finset.mem_sdiff.mp hcC).2 hkK
  have hke : k ≠ e := by
    intro h
    subst e
    exact (Finset.mem_sdiff.mp heC).2 hkK
  have hYkc : Yk ≠ Yc :=
    lpReplicaOffdiagDecoratedTarget_ne_of_singletonCrossToggle
      G sites i j q z Yk Yc k c hykState hycState hkc
  have hYke : Yk ≠ Ye :=
    lpReplicaOffdiagDecoratedTarget_ne_of_singletonCrossToggle
      G sites i j q z Yk Ye k e hykState hyeState hke
  have hYce : Yc ≠ Ye :=
    lpReplicaOffdiagDecoratedTarget_ne_of_singletonCrossToggle
      G sites i j q z Yc Ye c e hycState hyeState hce
  calc
    3 = ({Yk, Yc, Ye} : Finset
        (LPReplicaOffdiagDecoratedTarget G sites i j q)).card := by
      simp [hYkc, hYke, hYce]
    _ ≤ (lpReplicaOffdiagBalancedOutputCrossTraceFiber G sites i j q
        (lpReplicaOffdiagDecoratedSourceCrossTrace G sites i j q z)).card :=
      Finset.card_le_card (by
        intro y hy
        simp only [Finset.mem_insert, Finset.mem_singleton] at hy
        rcases hy with rfl | rfl | rfl
        · exact hYk
        · exact hYc
        · exact hYe)



theorem lpReplicaOffdiagOrbitAtomCardInequality_rank_five_of_coupledPairedOutputCard
    (G : SimpleGraph V) (sites : I -> V) {i j : I}
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (_hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
    (houtput : Fintype.card
        (LPReplicaOffdiagDecoratedSource G sites i j q) ≤
      (lpReplicaOffdiagCoupledPairedOutputs G sites i j q).card) :
    LPReplicaOffdiagOrbitAtomCardInequality G sites i j q :=
  lpReplicaOffdiagOrbitAtomCardInequality_of_coupledPairedOutputCard
    G sites i j q houtput



theorem lpReplicaOffdiagOrbitAtomCardInequality_of_commonSlotCard_le_five
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites) {i j : I} (hij : i ≠ j)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hle : Fintype.card (LPReplicaOrbitCommonSlot G sites q) ≤ 5)
    (hfiveOutput : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5 →
      Fintype.card (LPReplicaOffdiagDecoratedSource G sites i j q) ≤
        (lpReplicaOffdiagCoupledPairedOutputs G sites i j q).card) :
    LPReplicaOffdiagOrbitAtomCardInequality G sites i j q := by
  have hcases : Fintype.card (LPReplicaOrbitCommonSlot G sites q) ≤ 2 ∨
      Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 3 ∨
      Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 4 ∨
      Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5 := by
    omega
  rcases hcases with hsmall | hthree | hfour | hrankFive
  · exact lpReplicaOffdiagOrbitAtomCardInequality_of_commonSlotCard_le_two
      G sites hsite hij q hsmall
  · exact lpReplicaOffdiagOrbitAtomCardInequality_rank_three
      G sites hsite hij q hthree
  · exact lpReplicaOffdiagOrbitAtomCardInequality_rank_four
      G sites hsite hij q hfour
  · exact lpReplicaOffdiagOrbitAtomCardInequality_rank_five_of_coupledPairedOutputCard
      G sites q hrankFive (hfiveOutput hrankFive)

end

end StatMech.Ising

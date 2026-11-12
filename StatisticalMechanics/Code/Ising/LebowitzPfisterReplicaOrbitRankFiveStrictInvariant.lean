/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.Ising.LebowitzPfisterReplicaOrbitRankFiveStrictRouteTarget








namespace StatMech.Ising

noncomputable section

open scoped symmDiff

open StatMech.Sharpness
open StatMech.Sharpness.FluxEdgeCopy
open StatMech.Sharpness.RandomCurrent

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

local instance lpReplicaRankFiveStrictInvariantDecidableAdj
    (G : SimpleGraph V) (sites : I -> V) :
    DecidableRel (lpReplicaCurrentGraph G sites).Adj :=
  Classical.decRel _



theorem lpReplicaStrictPhysicalDoubleIncidenceRaw_map_equiv
    (G : SimpleGraph V) (sites : I -> V)
    {m n : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat}
    (E : Copy (lpReplicaCurrentGraph G sites) m ≃
      Copy (lpReplicaCurrentGraph G sites) n)
    (hends : ∀ c,
      endsM (lpReplicaCurrentGraph G sites) n (E c) =
        endsM (lpReplicaCurrentGraph G sites) m c)
    (K : Finset (Copy (lpReplicaCurrentGraph G sites) m))
    (hstrict : LPReplicaStrictPhysicalDoubleIncidenceRaw G sites m K) :
    LPReplicaStrictPhysicalDoubleIncidenceRaw G sites n
      (K.map E.toEmbedding) := by
  classical
  obtain ⟨d, hdK, hdPhysical, hdDouble⟩ := hstrict
  refine ⟨E d, Finset.mem_map.mpr ⟨d, hdK, rfl⟩, ?_, ?_⟩
  · intro hd
    apply hdPhysical
    have hedge : (E d).1.1 = d.1.1 := hends d
    unfold lpReplicaCurrentFoldedEdge at hd ⊢
    rw [hedge] at hd
    exact hd
  · intro x hxd
    rw [hends d] at hxd
    obtain ⟨e, heK, hed, hxe⟩ := hdDouble x hxd
    refine ⟨E e, Finset.mem_map.mpr ⟨e, heK, rfl⟩, E.injective.ne hed, ?_⟩
    rw [hends e]
    exact hxe


@[simp] theorem lpReplicaDecoratedOrbitAtomEquivOrientedFourColor_profile
    (G : SimpleGraph V) (sites : I -> V)
    (A B : Finset (LPReplicaCurrentVertex V))
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (z : LPReplicaDecoratedOrbitAtom G sites A B q) :
    (lpReplicaDecoratedOrbitAtomEquivOrientedFourColor
      G sites A B q z).1.1 = z.1.1.1 := rfl



theorem lpReplicaDecoratedOrbitAtomOfRowGate_hasStrictPhysicalDoubleIncidence
    (G : SimpleGraph V) (sites : I -> V)
    (m q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (tag : Copy (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag)
    (A B : Finset (LPReplicaCurrentVertex V))
    (hm : lpReplicaSymmetrizedProfile G sites m = q)
    (hgate : LPReplicaRowGate G sites m A B tag)
    (L : LPReplicaProfileOrbitLabel G sites q m) :
    LPReplicaDecoratedOrbitAtom.HasStrictPhysicalDoubleIncidence
        G sites A (B.map lpReplicaCurrentReflect.toEmbedding) q
        (lpReplicaDecoratedOrbitAtomOfRowGate
          G sites m q tag A B hm hgate L) ↔
      LPReplicaStrictPhysicalDoubleIncidenceRaw G sites m
        (lpReplicaRowCopies G sites m tag true) := by
  unfold LPReplicaDecoratedOrbitAtom.HasStrictPhysicalDoubleIncidence
  simp only [lpReplicaDecoratedOrbitAtomEquivOrientedFourColor_profile,
    lpReplicaDecoratedOrbitAtomOfRowGate_profile,
    lpReplicaOrientedFourColorTag_ofRowGate]



theorem lpReplicaDecoratedOrbitAtomOfBalancedSelector_hasStrictPhysicalDoubleIncidence
    (G : SimpleGraph V) (sites : I -> V)
    (Si Sj T : Finset (LPReplicaCurrentVertex V))
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (s : LPReplicaBalancedSelector G sites
      (Si ∆ Sj ∆ T) (Sj ∆ T) q) :
    LPReplicaDecoratedOrbitAtom.HasStrictPhysicalDoubleIncidence
        G sites Si ((Sj ∆ T).map lpReplicaCurrentReflect.toEmbedding) q
        (lpReplicaDecoratedOrbitAtomOfBalancedSelector
          G sites Si Sj T q s) ↔
      LPReplicaStrictPhysicalDoubleIncidenceRaw G sites s.profile
        (lpReplicaRowCopies G sites s.profile
          (lpReplicaToggleRows G sites s.profile s.selector s.tag) true) := by
  unfold lpReplicaDecoratedOrbitAtomOfBalancedSelector
  apply lpReplicaDecoratedOrbitAtomOfRowGate_hasStrictPhysicalDoubleIncidence



theorem lpReplicaDecoratedOrbitAtomOfBalancedSelector_left_hasStrictPhysicalDoubleIncidence
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
            (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j ∆
          lpMatchingGhostSource
            (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
            lpReplicaCurrentGhost1) q) :
    LPReplicaDecoratedOrbitAtom.HasStrictPhysicalDoubleIncidence
        G sites
          (lpMatchingSeamSource
            (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i)
          (lpMatchingSeamSource
                (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j ∆
              lpMatchingGhostSource
                (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
                lpReplicaCurrentGhost1) q
          (lpReplicaDecoratedOrbitAtomOfBalancedSelector_left
            G sites i j q s) ↔
      LPReplicaStrictPhysicalDoubleIncidenceRaw G sites s.profile
        (lpReplicaRowCopies G sites s.profile
          (lpReplicaToggleRows G sites s.profile s.selector s.tag) true) := by
  let Sj := lpMatchingSeamSource
    (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j
  let T := lpMatchingGhostSource
    (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V) lpReplicaCurrentGhost1
  have hfixed : (Sj ∆ T).map lpReplicaCurrentReflect.toEmbedding = Sj ∆ T :=
    lpReplicaCurrentReflect_seam_symmDiff_ghost G sites j
  unfold lpReplicaDecoratedOrbitAtomOfBalancedSelector_left
  dsimp only
  rw [LPReplicaDecoratedOrbitAtom.hasStrictPhysicalDoubleIncidence_cast
    G sites _ q hfixed]
  exact lpReplicaDecoratedOrbitAtomOfBalancedSelector_hasStrictPhysicalDoubleIncidence
    G sites _ Sj T q s





theorem lpReplica_not_strictPhysicalDoubleIncidence_insert_diagonal_matching
    (G : SimpleGraph V) (sites : I -> V)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (K : Finset (Copy (lpReplicaCurrentGraph G sites) m))
    (c : Copy (lpReplicaCurrentGraph G sites) m)
    (hcdiag : (lpReplicaCurrentFoldedEdge G sites c.1).IsDiag)
    (hunique : ∀ x ∈ K.biUnion (fun e =>
      (endsM (lpReplicaCurrentGraph G sites) m e).toFinset),
      ∃! e, e ∈ K ∧
        x ∈ (endsM (lpReplicaCurrentGraph G sites) m e).toFinset) :
    ¬ LPReplicaStrictPhysicalDoubleIncidenceRaw G sites m (insert c K) := by
  classical
  intro hstrict
  obtain ⟨d, hdInsert, hdPhysical, hdDouble⟩ := hstrict
  have hdc : d ≠ c := by
    intro hdc
    subst d
    exact hdPhysical hcdiag
  have hdK : d ∈ K := (Finset.mem_insert.mp hdInsert).resolve_left hdc
  have endpoint_mem_c {x : LPReplicaCurrentVertex V}
      (hxd : x ∈ endsM (lpReplicaCurrentGraph G sites) m d) :
      x ∈ endsM (lpReplicaCurrentGraph G sites) m c := by
    obtain ⟨e, heInsert, hed, hxe⟩ := hdDouble x hxd
    rcases Finset.mem_insert.mp heInsert with rfl | heK
    · exact hxe
    · have hxSupport : x ∈ K.biUnion (fun a =>
          (endsM (lpReplicaCurrentGraph G sites) m a).toFinset) := by
        apply Finset.mem_biUnion.mpr
        exact ⟨d, hdK, Sym2.mem_toFinset.mpr hxd⟩
      obtain ⟨_, _, huniqueX⟩ := hunique x hxSupport
      have hedEq : e = d := (huniqueX e
        ⟨heK, Sym2.mem_toFinset.mpr hxe⟩).trans
          (huniqueX d ⟨hdK, Sym2.mem_toFinset.mpr hxd⟩).symm
      exact False.elim (hed hedEq)
  induction hval : (endsM (lpReplicaCurrentGraph G sites) m d) using
      Sym2.inductionOn with
  | _ a b =>
      have hab : a ≠ b := by
        intro hab
        subst b
        apply hdPhysical
        unfold lpReplicaCurrentFoldedEdge
        change (Sym2.map lpReplicaCurrentFold
          (endsM (lpReplicaCurrentGraph G sites) m d)).IsDiag
        rw [hval, Sym2.map_mk, Sym2.mk_isDiag_iff]
      have ha : a ∈ endsM (lpReplicaCurrentGraph G sites) m c :=
        endpoint_mem_c (by rw [hval]; simp)
      have hb : b ∈ endsM (lpReplicaCurrentGraph G sites) m c :=
        endpoint_mem_c (by rw [hval]; simp)
      have hcends : endsM (lpReplicaCurrentGraph G sites) m c = s(a, b) :=
        sym2_eq_mk_of_mem_of_mem_of_ne ha hb hab
      apply hdPhysical
      unfold lpReplicaCurrentFoldedEdge at hcdiag ⊢
      change (Sym2.map lpReplicaCurrentFold
        (endsM (lpReplicaCurrentGraph G sites) m c)).IsDiag at hcdiag
      change (Sym2.map lpReplicaCurrentFold
        (endsM (lpReplicaCurrentGraph G sites) m d)).IsDiag
      rw [hval, ← hcends]
      exact hcdiag


theorem lpReplica_not_strictPhysicalDoubleIncidence_matching
    (G : SimpleGraph V) (sites : I -> V)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (K : Finset (Copy (lpReplicaCurrentGraph G sites) m))
    (hunique : ∀ x ∈ K.biUnion (fun e =>
      (endsM (lpReplicaCurrentGraph G sites) m e).toFinset),
      ∃! e, e ∈ K ∧
        x ∈ (endsM (lpReplicaCurrentGraph G sites) m e).toFinset) :
    ¬ LPReplicaStrictPhysicalDoubleIncidenceRaw G sites m K := by
  classical
  intro hstrict
  obtain ⟨d, hdK, _hdPhysical, hdDouble⟩ := hstrict
  induction hval : endsM (lpReplicaCurrentGraph G sites) m d using
      Sym2.inductionOn with
  | _ a b =>
      have had : a ∈ endsM (lpReplicaCurrentGraph G sites) m d := by
        rw [hval]
        simp
      obtain ⟨e, heK, hed, hae⟩ := hdDouble a had
      have haSupport : a ∈ K.biUnion (fun f =>
          (endsM (lpReplicaCurrentGraph G sites) m f).toFinset) := by
        exact Finset.mem_biUnion.mpr
          ⟨d, hdK, Sym2.mem_toFinset.mpr had⟩
      obtain ⟨_, _, huniqueA⟩ := hunique a haSupport
      have hedEq : e = d := (huniqueA e
        ⟨heK, Sym2.mem_toFinset.mpr hae⟩).trans
          (huniqueA d ⟨hdK, Sym2.mem_toFinset.mpr had⟩).symm
      exact hed hedEq




theorem lpReplica_strictPhysicalDoubleIncidence_insert_parallel_pair_iff
    (G : SimpleGraph V) (sites : I -> V)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (K : Finset (Copy (lpReplicaCurrentGraph G sites) m))
    (c e : Copy (lpReplicaCurrentGraph G sites) m)
    (hce : c ≠ e) (hcK : c ∉ K) (heK : e ∉ K)
    (hparallel : c.1.1 = e.1.1)
    (hunique : ∀ x ∈ K.biUnion (fun f =>
      (endsM (lpReplicaCurrentGraph G sites) m f).toFinset),
      ∃! f, f ∈ K ∧
        x ∈ (endsM (lpReplicaCurrentGraph G sites) m f).toFinset) :
    LPReplicaStrictPhysicalDoubleIncidenceRaw G sites m
        (insert c (insert e K)) ↔
      ¬ (lpReplicaCurrentFoldedEdge G sites c.1).IsDiag := by
  classical
  let E := endsM (lpReplicaCurrentGraph G sites) m
  have hends : E c = E e := by
    simpa only [E, endsM] using hparallel
  constructor
  · intro hstrict hcdiag
    obtain ⟨d, hdInsert, hdPhysical, hdDouble⟩ := hstrict
    have hdc : d ≠ c := by
      intro hdc
      subst d
      exact hdPhysical hcdiag
    have hde : d ≠ e := by
      intro hde
      subst d
      apply hdPhysical
      unfold lpReplicaCurrentFoldedEdge at hcdiag ⊢
      rw [← hparallel]
      exact hcdiag
    have hdK : d ∈ K := by
      rcases Finset.mem_insert.mp hdInsert with h | h
      · exact False.elim (hdc h)
      · rcases Finset.mem_insert.mp h with h | h
        · exact False.elim (hde h)
        · exact h
    have endpoint_mem_c {x : LPReplicaCurrentVertex V}
        (hxd : x ∈ E d) : x ∈ E c := by
      obtain ⟨f, hfInsert, hfd, hxf⟩ := hdDouble x hxd
      rcases Finset.mem_insert.mp hfInsert with rfl | hfInsert
      · exact hxf
      · rcases Finset.mem_insert.mp hfInsert with rfl | hfK
        · rw [hends]
          exact hxf
        · have hxSupport : x ∈ K.biUnion (fun a => (E a).toFinset) := by
            exact Finset.mem_biUnion.mpr
              ⟨d, hdK, Sym2.mem_toFinset.mpr hxd⟩
          obtain ⟨_, _, huniqueX⟩ := hunique x hxSupport
          have hfdEq : f = d := (huniqueX f
            ⟨hfK, Sym2.mem_toFinset.mpr hxf⟩).trans
              (huniqueX d ⟨hdK, Sym2.mem_toFinset.mpr hxd⟩).symm
          exact False.elim (hfd hfdEq)
    induction hval : E d using Sym2.inductionOn with
    | _ a b =>
        have hab : a ≠ b := by
          intro hab
          subst b
          exact (endsM_not_isDiag
            (lpReplicaCurrentGraph G sites) m d) (by
              simpa only [E, hval, Sym2.mk_isDiag_iff])
        have ha : a ∈ E c := endpoint_mem_c (by rw [hval]; simp)
        have hb : b ∈ E c := endpoint_mem_c (by rw [hval]; simp)
        have hcends : E c = s(a, b) :=
          sym2_eq_mk_of_mem_of_mem_of_ne ha hb hab
        apply hdPhysical
        unfold lpReplicaCurrentFoldedEdge at hcdiag ⊢
        change (Sym2.map lpReplicaCurrentFold (E c)).IsDiag at hcdiag
        change (Sym2.map lpReplicaCurrentFold (E d)).IsDiag
        rw [hval, ← hcends]
        exact hcdiag
  · intro hcPhysical
    refine ⟨c, Finset.mem_insert_self c _, hcPhysical, ?_⟩
    intro x hxc
    refine ⟨e, Finset.mem_insert.mpr (Or.inr
      (Finset.mem_insert_self e K)), hce.symm, ?_⟩
    change x ∈ E e
    rw [← hends]
    exact hxc



theorem lpReplicaOffdiagDecoratedSource_rankFive_activeCore_uniqueIncidence
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites) {i j : I} (hij : i ≠ j)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (z : LPReplicaOffdiagDecoratedSource G sites i j q)
    (hthree : (lpReplicaCurrentCopies G sites z.1.1.1
      (lpReplicaDecoratedSourceRowGateData G sites i j q z).1
        true false).card = 3) :
    let d := lpReplicaDecoratedSourceRowGateData G sites i j q z
    let K := lpReplicaCurrentCopies G sites z.1.1.1 d.1 true false
    let E := endsM (lpReplicaCurrentGraph G sites) z.1.1.1
    ∀ x ∈ K.biUnion (fun e => (E e).toFinset),
      ∃! e, e ∈ K ∧ x ∈ (E e).toFinset := by
  classical
  dsimp only
  let d := lpReplicaDecoratedSourceRowGateData G sites i j q z
  let K := lpReplicaCurrentCopies G sites z.1.1.1 d.1 true false
  let E := endsM (lpReplicaCurrentGraph G sites) z.1.1.1
  have hsource : RandomCurrent.sources E K =
      lpMatchingSeamSource
          (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i ∆
        lpMatchingSeamSource
          (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j ∆
        lpMatchingGhostSource
          (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
          lpReplicaCurrentGhost1 := by
    simpa only [E, K, d] using d.2.2.2.2.1
  have htight : (RandomCurrent.sources E K).card = 2 * K.card := by
    rw [hsource, card_lpReplica_offdiagSource sites hsite hij]
    simpa only [K, d, hthree]
  intro x hx
  exact randomCurrent_existsUnique_copy_of_mem_endpointSupport_of_card_eq_two_mul
    E K htight hx



theorem lpReplicaOffdiagDecoratedSource_rankFive_exists_parallelComplementPair
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
    ∃ c e, c ≠ e ∧ Finset.univ \ K = {c, e} ∧ c.1.1 = e.1.1 := by
  classical
  dsimp only
  let d := lpReplicaDecoratedSourceRowGateData G sites i j q z
  let K := lpReplicaCurrentCopies G sites z.1.1.1 d.1 true false
  let C := Finset.univ \ K
  have hcopyCard : Fintype.card
      (Copy (lpReplicaCurrentGraph G sites) z.1.1.1) = 5 := by
    calc
      _ = Fintype.card (LPReplicaOrbitCommonSlot G sites q) :=
        Fintype.card_congr
          (lpReplicaProfileCopyEquivCommonSlot G sites q z.1.1.1
            z.1.1.2 z.2.2)
      _ = 5 := hcard
  have hCcard : C.card = 2 := by
    change (Finset.univ \ K).card = 2
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ K),
      Finset.card_univ, hcopyCard]
    simpa only [K, d, hthree]
  obtain ⟨c, e, hce, hCeq⟩ := Finset.card_eq_two.mp hCcard
  have hcC : c ∈ Finset.univ \ K := by
    change c ∈ C
    rw [hCeq]
    simp
  have heC : e ∈ Finset.univ \ K := by
    change e ∈ C
    rw [hCeq]
    simp
  refine ⟨c, e, hce, hCeq, ?_⟩
  exact lpReplicaOffdiagDecoratedSource_rank_five_complement_same_edge
    G sites hsite hij q hcard z hthree c hcC e heC

set_option maxHeartbeats 1000000 in



theorem
    lpReplicaOffdiagDecoratedSource_rankFive_nonsaturatedHigh_singletonToggle_raw_iff
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
    (a : Copy (lpReplicaCurrentGraph G sites) z.1.1.1)
    (haK : a ∈ lpReplicaCurrentCopies G sites z.1.1.1
      (lpReplicaDecoratedSourceRowGateData G sites i j q z).1
        true false) :
    let d := lpReplicaDecoratedSourceRowGateData G sites i j q z
    let K := lpReplicaCurrentCopies G sites z.1.1.1 d.1 true false
    ∃ c e, c ≠ e ∧ Finset.univ \ K = {c, e} ∧
      (LPReplicaStrictPhysicalDoubleIncidenceRaw G sites z.1.1.1
          (lpReplicaRowCopies G sites z.1.1.1
            (lpReplicaToggleRows G sites z.1.1.1 {a} d.1) true) ↔
        ¬ (lpReplicaCurrentFoldedEdge G sites c.1).IsDiag) := by
  classical
  dsimp only at hhigh ⊢
  let d := lpReplicaDecoratedSourceRowGateData G sites i j q z
  let K := lpReplicaCurrentCopies G sites z.1.1.1 d.1 true false
  let C := Finset.univ \ K
  obtain ⟨hthree, r, hrC, hrrow⟩ := hhigh
  change K.card = 3 at hthree
  change r ∈ C at hrC
  change (d.1 r).1 = true at hrrow
  change a ∈ K at haK
  obtain ⟨c, e, hce, hCeq, hparallel⟩ :=
    lpReplicaOffdiagDecoratedSource_rankFive_exists_parallelComplementPair
      G sites hsite hij q hcard z hthree
  change C = {c, e} at hCeq
  have hcC : c ∈ C := by
    rw [hCeq]
    simp
  have heC : e ∈ C := by
    rw [hCeq]
    simp
  have hrnotK : r ∉ K := (Finset.mem_sdiff.mp hrC).2
  have hrtag : d.1 r = (true, true) := by
    rcases htag : d.1 r with ⟨row, current⟩
    cases row
    · rw [htag] at hrrow
      simp at hrrow
    · cases current
      · exfalso
        apply hrnotK
        simp only [K, lpReplicaCurrentCopies, Finset.mem_filter,
          Finset.mem_univ, true_and]
        exact htag
      · simpa using htag
  have hcTag : d.1 c = (true, true) :=
    (lpReplicaOffdiagDecoratedSource_rank_five_complement_tag_constant
      G sites hsite hij q hcard z hthree c hcC r hrC).trans hrtag
  have heTag : d.1 e = (true, true) :=
    (lpReplicaOffdiagDecoratedSource_rank_five_complement_tag_constant
      G sites hsite hij q hcard z hthree e heC r hrC).trans hrtag
  let K0 := K \ {a}
  have haTag : d.1 a = (true, false) := by
    simpa only [K, d, lpReplicaCurrentCopies, Finset.mem_filter,
      Finset.mem_univ, true_and] using haK
  have hrow : lpReplicaRowCopies G sites z.1.1.1
      (lpReplicaToggleRows G sites z.1.1.1 {a} d.1) true =
        insert c (insert e K0) := by
    ext x
    by_cases hxK : x ∈ K
    · have hxTag : d.1 x = (true, false) := by
        simpa only [K, lpReplicaCurrentCopies, Finset.mem_filter,
          Finset.mem_univ, true_and] using hxK
      by_cases hxa : x = a
      · subst x
        have hac : a ≠ c := fun h =>
          (Finset.mem_sdiff.mp hcC).2 (h ▸ haK)
        have hae : a ≠ e := fun h =>
          (Finset.mem_sdiff.mp heC).2 (h ▸ haK)
        simp [lpReplicaRowCopies, lpReplicaToggleRows, K0, haTag,
          hac, hae]
      · have hxc : x ≠ c := fun h =>
          (Finset.mem_sdiff.mp hcC).2 (h ▸ hxK)
        have hxe : x ≠ e := fun h =>
          (Finset.mem_sdiff.mp heC).2 (h ▸ hxK)
        simp [lpReplicaRowCopies, lpReplicaToggleRows, K0, hxTag, hxK,
          hxa, hxc, hxe]
    · have hxC : x ∈ C := Finset.mem_sdiff.mpr
        ⟨Finset.mem_univ _, hxK⟩
      have hxa : x ≠ a := fun h => hxK (h ▸ haK)
      rw [hCeq] at hxC
      simp only [Finset.mem_insert, Finset.mem_singleton] at hxC
      rcases hxC with rfl | rfl
      · simp [lpReplicaRowCopies, lpReplicaToggleRows, K0, hcTag, hxa]
      · simp [lpReplicaRowCopies, lpReplicaToggleRows, K0, heTag, hxa]
  have huniqueK :=
    lpReplicaOffdiagDecoratedSource_rankFive_activeCore_uniqueIncidence
      G sites hsite hij q z hthree
  have huniqueK0 : ∀ x ∈ K0.biUnion (fun f =>
      (endsM (lpReplicaCurrentGraph G sites) z.1.1.1 f).toFinset),
      ∃! f, f ∈ K0 ∧
        x ∈ (endsM (lpReplicaCurrentGraph G sites) z.1.1.1 f).toFinset := by
    intro x hx
    obtain ⟨f, hfK0, hxf⟩ := Finset.mem_biUnion.mp hx
    refine ⟨f, ⟨hfK0, hxf⟩, ?_⟩
    intro g hg
    have hxKsupport : x ∈ K.biUnion (fun b =>
        (endsM (lpReplicaCurrentGraph G sites) z.1.1.1 b).toFinset) := by
      exact Finset.mem_biUnion.mpr
        ⟨f, (Finset.mem_sdiff.mp hfK0).1, hxf⟩
    obtain ⟨_, _, huniq⟩ := huniqueK x hxKsupport
    exact (huniq g ⟨(Finset.mem_sdiff.mp hg.1).1, hg.2⟩).trans
      (huniq f ⟨(Finset.mem_sdiff.mp hfK0).1, hxf⟩).symm
  have hcK0 : c ∉ K0 := fun hc =>
    (Finset.mem_sdiff.mp hcC).2 (Finset.mem_sdiff.mp hc).1
  have heK0 : e ∉ K0 := fun he =>
    (Finset.mem_sdiff.mp heC).2 (Finset.mem_sdiff.mp he).1
  refine ⟨c, e, hce, hCeq, ?_⟩
  rw [hrow]
  exact lpReplica_strictPhysicalDoubleIncidence_insert_parallel_pair_iff
    G sites z.1.1.1 K0 c e hce hcK0 heK0 hparallel huniqueK0

set_option maxHeartbeats 1000000 in


theorem
    lpReplicaOffdiagDecoratedSource_rankFive_low_singletonToggle_not_strictRaw
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites) {i j : I} (hij : i ≠ j)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
    (z : LPReplicaOffdiagDecoratedSource G sites i j q)
    (hlow :
      let d := lpReplicaDecoratedSourceRowGateData G sites i j q z
      let K := lpReplicaCurrentCopies G sites z.1.1.1 d.1 true false
      K.card = 3 ∧
        ∃ r, r ∈ Finset.univ \ K ∧ (d.1 r).1 = false)
    (a : Copy (lpReplicaCurrentGraph G sites) z.1.1.1)
    (haK : a ∈ lpReplicaCurrentCopies G sites z.1.1.1
      (lpReplicaDecoratedSourceRowGateData G sites i j q z).1
        true false) :
    let d := lpReplicaDecoratedSourceRowGateData G sites i j q z
    ¬ LPReplicaStrictPhysicalDoubleIncidenceRaw G sites z.1.1.1
        (lpReplicaRowCopies G sites z.1.1.1
          (lpReplicaToggleRows G sites z.1.1.1 {a} d.1) true) := by
  classical
  dsimp only at hlow ⊢
  let d := lpReplicaDecoratedSourceRowGateData G sites i j q z
  let K := lpReplicaCurrentCopies G sites z.1.1.1 d.1 true false
  let C := Finset.univ \ K
  obtain ⟨hthree, r, hrC, hrrow⟩ := hlow
  change K.card = 3 at hthree
  change r ∈ C at hrC
  change (d.1 r).1 = false at hrrow
  change a ∈ K at haK
  have hrowC : ∀ x ∈ C, (d.1 x).1 = false := by
    intro x hx
    have htag :=
      lpReplicaOffdiagDecoratedSource_rank_five_complement_tag_constant
        G sites hsite hij q hcard z hthree x hx r hrC
    exact congrArg Prod.fst htag |>.trans hrrow
  let K0 := K \ {a}
  have haTag : d.1 a = (true, false) := by
    simpa only [K, d, lpReplicaCurrentCopies, Finset.mem_filter,
      Finset.mem_univ, true_and] using haK
  have hrow : lpReplicaRowCopies G sites z.1.1.1
      (lpReplicaToggleRows G sites z.1.1.1 {a} d.1) true = K0 := by
    ext x
    by_cases hxK : x ∈ K
    · have hxTag : d.1 x = (true, false) := by
        simpa only [K, lpReplicaCurrentCopies, Finset.mem_filter,
          Finset.mem_univ, true_and] using hxK
      by_cases hxa : x = a
      · subst x
        simp [lpReplicaRowCopies, lpReplicaToggleRows, K0, haTag]
      · simp [lpReplicaRowCopies, lpReplicaToggleRows, K0, hxTag, hxK,
          hxa]
    · have hxC : x ∈ C := Finset.mem_sdiff.mpr
        ⟨Finset.mem_univ _, hxK⟩
      have hxa : x ≠ a := fun h => hxK (h ▸ haK)
      have hxRow := hrowC x hxC
      rcases htag : d.1 x with ⟨row, current⟩
      cases row
      · simp [lpReplicaRowCopies, lpReplicaToggleRows, K0, htag, hxK,
          hxa]
      · simp [htag] at hxRow
  have huniqueK :=
    lpReplicaOffdiagDecoratedSource_rankFive_activeCore_uniqueIncidence
      G sites hsite hij q z hthree
  have huniqueK0 : ∀ x ∈ K0.biUnion (fun f =>
      (endsM (lpReplicaCurrentGraph G sites) z.1.1.1 f).toFinset),
      ∃! f, f ∈ K0 ∧
        x ∈ (endsM (lpReplicaCurrentGraph G sites) z.1.1.1 f).toFinset := by
    intro x hx
    obtain ⟨f, hfK0, hxf⟩ := Finset.mem_biUnion.mp hx
    refine ⟨f, ⟨hfK0, hxf⟩, ?_⟩
    intro g hg
    have hxKsupport : x ∈ K.biUnion (fun b =>
        (endsM (lpReplicaCurrentGraph G sites) z.1.1.1 b).toFinset) := by
      exact Finset.mem_biUnion.mpr
        ⟨f, (Finset.mem_sdiff.mp hfK0).1, hxf⟩
    obtain ⟨_, _, huniq⟩ := huniqueK x hxKsupport
    exact (huniq g ⟨(Finset.mem_sdiff.mp hg.1).1, hg.2⟩).trans
      (huniq f ⟨(Finset.mem_sdiff.mp hfK0).1, hxf⟩).symm
  rw [hrow]
  exact lpReplica_not_strictPhysicalDoubleIncidence_matching
    G sites z.1.1.1 K0 huniqueK0



theorem lpReplicaOffdiagDecoratedSourceStrictRouteTargetAtom_hasDoubleIncidence
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites)
    {i j k u v : I}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hu : u = i ∨ u = j ∨ u = k)
    (hv : v = i ∨ v = j ∨ v = k) (huv : u ≠ v)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (z : LPReplicaOffdiagDecoratedSource G sites i j q)
    (c d : Copy (lpReplicaCurrentGraph G sites) z.1.1.1)
    (hc : c.1.1 = lpReplicaCurrentSeamEdge sites k)
    (hdK : d ∈ Finset.univ \ {c})
    (hfold : lpReplicaCurrentFoldedEdge G sites d.1 =
      s(Sum.inl (sites u), Sum.inl (sites v)))
    (hunique : ∀ x ∈ lpReplicaTripleSeamGhostSource sites i j k,
      ∃! e, e ∈ Finset.univ \ {c} ∧
        x ∈ (endsM (lpReplicaCurrentGraph G sites) z.1.1.1 e).toFinset)
    (hdisc :
      let target := lpReplicaCollisionProfile G sites
        (profileFlux (lpReplicaCurrentGraph G sites) z.1.1.1
          (Finset.univ \ {d}))
        (profileFlux (lpReplicaCurrentGraph G sites) z.1.1.1 {d})
      let K' := lpReplicaPartialReflectCopiesRaw
        G sites z.1.1.1 {d} (Finset.univ \ {c})
      ¬ connK (endsM (lpReplicaCurrentGraph G sites) target) K'
        lpReplicaCurrentGhost0 lpReplicaCurrentGhost1) :
    LPReplicaDecoratedOrbitAtom.HasStrictPhysicalDoubleIncidence
      G sites
        (lpMatchingSeamSource
          (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) k)
        (lpMatchingSeamSource
            (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites)
              (lpReplicaThirdOfThree i j k u v) ∆
          lpMatchingGhostSource
            (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
            lpReplicaCurrentGhost1) q
      (lpReplicaOffdiagDecoratedSourceStrictRouteTargetAtom
        G sites hsite hij hik hjk hu hv huv q z c d hc
          (Ne.symm ((Finset.mem_sdiff.mp hdK).2 ∘
            Finset.mem_singleton.mpr))
          hfold hdisc) := by
  classical
  let m := z.1.1.1
  let target := lpReplicaCollisionProfile G sites
    (profileFlux (lpReplicaCurrentGraph G sites) m (Finset.univ \ {d}))
    (profileFlux (lpReplicaCurrentGraph G sites) m {d})
  let R := lpReplicaPartialReflectCopyEquivRaw G sites m {d}
  let c' := R c
  let tag := lpReplicaSingletonFalseRowTag c'
  let relabel := lpReplicaPartialReflectCanonicalRelabelEquiv
    G sites q m z.1.1.2 z.2.2 {d}
  let movedTag := lpReplicaTransportTag G sites relabel tag
  let Sk := lpMatchingSeamSource
    (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) k
  let Sl := lpMatchingSeamSource
    (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites)
      (lpReplicaThirdOfThree i j k u v)
  let T := lpMatchingGhostSource
    (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
    lpReplicaCurrentGhost1
  have hfixed : (Sl ∆ T).map lpReplicaCurrentReflect.toEmbedding =
      Sl ∆ T :=
    lpReplicaCurrentReflect_seam_symmDiff_ghost G sites
      (lpReplicaThirdOfThree i j k u v)
  have hreflectedSupport : ∀ x ∈
      endsM (lpReplicaCurrentGraph G sites) m d,
      lpReplicaCurrentReflect x ∈
        lpReplicaTripleSeamGhostSource sites i j k :=
    lpReplica_strictPhysicalRoute_reflected_endpoint_mem_tripleSource
      G sites hsite hij hik hjk hu hv huv m d hfold
  have hdisjoint := lpReplica_strictPhysicalRoute_disjoint_reflected_ends
    G sites hsite huv m d hfold
  have hraw : LPReplicaStrictPhysicalDoubleIncidenceRaw G sites target
      (lpReplicaPartialReflectCopiesRaw G sites m {d}
        (Finset.univ \ {c})) := by
    simpa only [m, target] using
      (lpReplica_partialReflect_strictMatchingRoute_hasDoubleIncidence
        G sites hsite huv m (Finset.univ \ {c})
          (lpReplicaTripleSeamGhostSource sites i j k) d hdK hunique
          hreflectedSupport hfold hdisjoint)
  have himage : lpReplicaPartialReflectCopiesRaw G sites m {d}
      (Finset.univ \ {c}) = Finset.univ \ {c'} := by
    simpa only [c', R] using
      (lpReplicaPartialReflectCopiesRaw_sdiff_singleton
        G sites m d c)
  have hrow1 : lpReplicaRowCopies G sites target tag true =
      Finset.univ \ {c'} := by
    exact lpReplicaRowCopies_singletonFalse_true G sites target c'
  have hrawTag : LPReplicaStrictPhysicalDoubleIncidenceRaw G sites target
      (lpReplicaRowCopies G sites target tag true) := by
    rw [hrow1, ← himage]
    exact hraw
  let normalizedTarget := lpReplicaPartialReflectProfile G sites m
    (profileFlux (lpReplicaCurrentGraph G sites) m {d})
  have hmoved : LPReplicaStrictPhysicalDoubleIncidenceRaw G sites
      normalizedTarget
      (lpReplicaRowCopies G sites normalizedTarget movedTag true) := by
    rw [lpReplicaRowCopies_transportTag]
    exact lpReplicaStrictPhysicalDoubleIncidenceRaw_map_equiv
      G sites relabel
        (lpReplicaPartialReflectCanonicalRelabelEquiv_ends
          G sites q m z.1.1.2 z.2.2 {d}) _ hrawTag
  let rawAtom :=
    lpReplicaOffdiagDecoratedSourceStrictRouteTargetAtomRawBoundary
      G sites hsite hij hik hjk hu hv huv q z c d hc
        (Ne.symm ((Finset.mem_sdiff.mp hdK).2 ∘
          Finset.mem_singleton.mpr))
        hfold hdisc
  have hrawAtom :
      LPReplicaDecoratedOrbitAtom.HasStrictPhysicalDoubleIncidence
        G sites Sk ((Sl ∆ T).map lpReplicaCurrentReflect.toEmbedding) q
        rawAtom := by
    dsimp only [rawAtom]
    unfold lpReplicaOffdiagDecoratedSourceStrictRouteTargetAtomRawBoundary
      lpReplicaDecoratedOrbitAtomCanonicalizeRawPartialReflect
    apply (lpReplicaDecoratedOrbitAtomOfRowGate_hasStrictPhysicalDoubleIncidence
      G sites normalizedTarget q movedTag Sk (Sl ∆ T) _ _ _).2
    exact hmoved
  unfold lpReplicaOffdiagDecoratedSourceStrictRouteTargetAtom
  dsimp only
  apply (LPReplicaDecoratedOrbitAtom.hasStrictPhysicalDoubleIncidence_cast
    G sites Sk q hfixed rawAtom).2
  exact hrawAtom

end

end StatMech.Ising

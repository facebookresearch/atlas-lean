/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.Ising.LebowitzPfisterReplicaOrbitRankFiveFoldedGeometry









namespace StatMech.Ising

noncomputable section

open scoped symmDiff

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

local instance lpReplicaRankFiveRoutingDecidableAdj
    (G : SimpleGraph V) (sites : I -> V) :
    DecidableRel (lpReplicaCurrentGraph G sites).Adj :=
  Classical.decRel _



theorem lpReplicaCurrentFoldedEdge_isDiag_iff_exists_seam
    (G : SimpleGraph V) (sites : I -> V)
    (e : (lpReplicaCurrentGraph G sites).edgeFinset) :
    (lpReplicaCurrentFoldedEdge G sites e).IsDiag ↔
      ∃ i, e.1 = lpReplicaCurrentSeamEdge sites i := by
  constructor
  · intro hdiag
    induction hval : e.1 using Sym2.inductionOn with
    | _ x y =>
        have hxy : (lpReplicaCurrentGraph G sites).Adj x y := by
          have hmem := e.2
          rw [SimpleGraph.mem_edgeFinset, hval, SimpleGraph.mem_edgeSet] at hmem
          exact hmem
        unfold lpReplicaCurrentFoldedEdge at hdiag
        rw [hval, Sym2.map_mk, Sym2.mk_isDiag_iff] at hdiag
        rcases x with (x | g) <;> rcases y with (y | h)
        · rcases x with x | x <;> rcases y with y | y
          · simp only [lpReplicaCurrentFold] at hdiag
            have hxy' : x = y := Sum.inl.inj hdiag
            subst y
            exact False.elim
              ((lpReplicaCurrentGraph G sites).loopless.irrefl _ hxy)
          · simp only [lpReplicaCurrentFold, Sum.inl.injEq] at hdiag
            rw [lpReplicaCurrentGraph_adj_left_right_iff] at hxy
            obtain ⟨i, hix, hiy⟩ := hxy
            subst x
            subst y
            exact ⟨i, rfl⟩
          · simp only [lpReplicaCurrentFold, Sum.inl.injEq] at hdiag
            rw [(lpReplicaCurrentGraph G sites).adj_comm,
              lpReplicaCurrentGraph_adj_left_right_iff] at hxy
            obtain ⟨i, hiy, hix⟩ := hxy
            subst x
            subst y
            exact ⟨i, by
              unfold lpReplicaCurrentSeamEdge lpReplicaCurrentLeft
                lpReplicaCurrentRight
              rw [Sym2.eq_iff]
              exact Or.inr ⟨rfl, rfl⟩⟩
          · simp only [lpReplicaCurrentFold] at hdiag
            have hxy' : x = y := Sum.inl.inj hdiag
            subst y
            exact False.elim
              ((lpReplicaCurrentGraph G sites).loopless.irrefl _ hxy)
        · rcases x with x | x <;> cases h <;>
            simp only [lpReplicaCurrentFold, Sum.inl_ne_inr] at hdiag
        · cases g <;> rcases y with y | y <;>
            simp only [lpReplicaCurrentFold, Sum.inr_ne_inl] at hdiag
        · cases g <;> cases h <;>
            simp [lpReplicaCurrentGraph, lpReplicaCurrentRel] at hxy
  · rintro ⟨i, hi⟩
    unfold lpReplicaCurrentFoldedEdge
    rw [hi]
    unfold lpReplicaCurrentSeamEdge lpReplicaCurrentLeft
      lpReplicaCurrentRight
    rw [Sym2.map_mk, Sym2.mk_isDiag_iff]
    rfl



theorem lpReplicaCurrentLeft_mem_tripleSeamGhostSource_iff
    (sites : I -> V) (hsite : Function.Injective sites)
    {i j k t : I} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    lpReplicaCurrentLeft sites t ∈
        lpReplicaTripleSeamGhostSource sites i j k ↔
      t = i ∨ t = j ∨ t = k := by
  have hsij : sites i ≠ sites j := hsite.ne hij
  have hsik : sites i ≠ sites k := hsite.ne hik
  have hsjk : sites j ≠ sites k := hsite.ne hjk
  unfold lpReplicaTripleSeamGhostSource lpMatchingSeamSource
    lpMatchingGhostSource
  simp [lpReplicaCurrentLeft, lpReplicaCurrentRight,
    lpReplicaCurrentGhost0, lpReplicaCurrentGhost1,
    Finset.mem_symmDiff, hsite.eq_iff, hsij, hsij.symm,
    hsik, hsik.symm, hsjk, hsjk.symm]
  constructor
  · rintro (⟨(⟨hti, _⟩ | ⟨htj, _⟩), _⟩ | ⟨htk, _, _⟩)
    · exact Or.inl hti
    · exact Or.inr (Or.inl htj)
    · exact Or.inr (Or.inr htk)
  · rintro (rfl | rfl | rfl)
    · exact Or.inl ⟨Or.inl ⟨rfl, hij⟩, hik⟩
    · exact Or.inl ⟨Or.inr ⟨rfl, Ne.symm hij⟩, hjk⟩
    · exact Or.inr ⟨rfl,
        fun hki => False.elim (hik hki.symm),
        fun hkj => False.elim (hjk hkj.symm)⟩



theorem lpReplicaCurrentRight_mem_tripleSeamGhostSource_iff
    (sites : I -> V) (hsite : Function.Injective sites)
    {i j k t : I} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    lpReplicaCurrentRight sites t ∈
        lpReplicaTripleSeamGhostSource sites i j k ↔
      t = i ∨ t = j ∨ t = k := by
  have hsij : sites i ≠ sites j := hsite.ne hij
  have hsik : sites i ≠ sites k := hsite.ne hik
  have hsjk : sites j ≠ sites k := hsite.ne hjk
  unfold lpReplicaTripleSeamGhostSource lpMatchingSeamSource
    lpMatchingGhostSource
  simp [lpReplicaCurrentLeft, lpReplicaCurrentRight,
    lpReplicaCurrentGhost0, lpReplicaCurrentGhost1,
    Finset.mem_symmDiff, hsite.eq_iff, hsij, hsij.symm,
    hsik, hsik.symm, hsjk, hsjk.symm]
  constructor
  · rintro (⟨(⟨hti, _⟩ | ⟨htj, _⟩), _⟩ | ⟨htk, _, _⟩)
    · exact Or.inl hti
    · exact Or.inr (Or.inl htj)
    · exact Or.inr (Or.inr htk)
  · rintro (rfl | rfl | rfl)
    · exact Or.inl ⟨Or.inl ⟨rfl, hij⟩, hik⟩
    · exact Or.inl ⟨Or.inr ⟨rfl, Ne.symm hij⟩, hjk⟩
    · exact Or.inr ⟨rfl,
        fun hki => False.elim (hik hki.symm),
        fun hkj => False.elim (hjk hkj.symm)⟩

theorem lpReplicaPhysicalLeft_mem_tripleSeamGhostSource_iff
    (sites : I -> V) (hsite : Function.Injective sites)
    {i j k : I} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (x : V) :
    (.inl (.inl x) : LPReplicaCurrentVertex V) ∈
        lpReplicaTripleSeamGhostSource sites i j k ↔
      x = sites i ∨ x = sites j ∨ x = sites k := by
  have hsij : sites i ≠ sites j := hsite.ne hij
  have hsik : sites i ≠ sites k := hsite.ne hik
  have hsjk : sites j ≠ sites k := hsite.ne hjk
  unfold lpReplicaTripleSeamGhostSource lpMatchingSeamSource
    lpMatchingGhostSource
  simp [lpReplicaCurrentLeft, lpReplicaCurrentRight,
    lpReplicaCurrentGhost0, lpReplicaCurrentGhost1,
    Finset.mem_symmDiff]
  constructor
  · rintro (⟨(⟨hxi, _⟩ | ⟨hxj, _⟩), _⟩ | ⟨hxk, _, _⟩)
    · exact Or.inl hxi
    · exact Or.inr (Or.inl hxj)
    · exact Or.inr (Or.inr hxk)
  · rintro (rfl | rfl | rfl)
    · exact Or.inl ⟨Or.inl ⟨rfl, hsij⟩, hsik⟩
    · exact Or.inl ⟨Or.inr ⟨rfl, Ne.symm hsij⟩, hsjk⟩
    · exact Or.inr ⟨rfl,
        fun hki => False.elim (hsik hki.symm),
        fun hkj => False.elim (hsjk hkj.symm)⟩

theorem lpReplicaPhysicalRight_mem_tripleSeamGhostSource_iff
    (sites : I -> V) (hsite : Function.Injective sites)
    {i j k : I} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (x : V) :
    (.inl (.inr x) : LPReplicaCurrentVertex V) ∈
        lpReplicaTripleSeamGhostSource sites i j k ↔
      x = sites i ∨ x = sites j ∨ x = sites k := by
  have hsij : sites i ≠ sites j := hsite.ne hij
  have hsik : sites i ≠ sites k := hsite.ne hik
  have hsjk : sites j ≠ sites k := hsite.ne hjk
  unfold lpReplicaTripleSeamGhostSource lpMatchingSeamSource
    lpMatchingGhostSource
  simp [lpReplicaCurrentLeft, lpReplicaCurrentRight,
    lpReplicaCurrentGhost0, lpReplicaCurrentGhost1,
    Finset.mem_symmDiff]
  constructor
  · rintro (⟨(⟨hxi, _⟩ | ⟨hxj, _⟩), _⟩ | ⟨hxk, _, _⟩)
    · exact Or.inl hxi
    · exact Or.inr (Or.inl hxj)
    · exact Or.inr (Or.inr hxk)
  · rintro (rfl | rfl | rfl)
    · exact Or.inl ⟨Or.inl ⟨rfl, hsij⟩, hsik⟩
    · exact Or.inl ⟨Or.inr ⟨rfl, Ne.symm hsij⟩, hsjk⟩
    · exact Or.inr ⟨rfl,
        fun hki => False.elim (hsik hki.symm),
        fun hkj => False.elim (hsjk hkj.symm)⟩



theorem lpReplicaCurrentFold_eq_site_of_mem_tripleSeamGhostSource
    (sites : I -> V) (hsite : Function.Injective sites)
    {i j k : I} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (x : LPReplicaCurrentVertex V)
    (hx : x ∈ lpReplicaTripleSeamGhostSource sites i j k)
    (hx0 : x ≠ lpReplicaCurrentGhost0)
    (hx1 : x ≠ lpReplicaCurrentGhost1) :
    ∃ u, (u = i ∨ u = j ∨ u = k) ∧
      lpReplicaCurrentFold x = Sum.inl (sites u) := by
  rcases x with (x | b)
  · rcases x with x | x
    · have hx' := (lpReplicaPhysicalLeft_mem_tripleSeamGhostSource_iff
        sites hsite hij hik hjk x).mp hx
      rcases hx' with h | h | h
      · exact ⟨i, Or.inl rfl, by simpa [h]⟩
      · exact ⟨j, Or.inr (Or.inl rfl), by simpa [h]⟩
      · exact ⟨k, Or.inr (Or.inr rfl), by simpa [h]⟩
    · have hx' := (lpReplicaPhysicalRight_mem_tripleSeamGhostSource_iff
        sites hsite hij hik hjk x).mp hx
      rcases hx' with h | h | h
      · exact ⟨i, Or.inl rfl, by simpa [h]⟩
      · exact ⟨j, Or.inr (Or.inl rfl), by simpa [h]⟩
      · exact ⟨k, Or.inr (Or.inr rfl), by simpa [h]⟩
  · cases b
    · exact False.elim (hx0 rfl)
    · exact False.elim (hx1 rfl)


theorem lpReplicaCurrentGhost0_mem_tripleSeamGhostSource
    (sites : I -> V) (i j k : I) :
    (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V) ∈
      lpReplicaTripleSeamGhostSource sites i j k := by
  simp [lpReplicaTripleSeamGhostSource, lpMatchingSeamSource,
    lpMatchingGhostSource, lpReplicaCurrentLeft, lpReplicaCurrentRight,
    lpReplicaCurrentGhost0, lpReplicaCurrentGhost1,
    Finset.mem_symmDiff]

theorem lpReplicaCurrentGhost1_mem_tripleSeamGhostSource
    (sites : I -> V) (i j k : I) :
    (lpReplicaCurrentGhost1 : LPReplicaCurrentVertex V) ∈
      lpReplicaTripleSeamGhostSource sites i j k := by
  simp [lpReplicaTripleSeamGhostSource, lpMatchingSeamSource,
    lpMatchingGhostSource, lpReplicaCurrentLeft, lpReplicaCurrentRight,
    lpReplicaCurrentGhost0, lpReplicaCurrentGhost1,
    Finset.mem_symmDiff]




theorem lpReplica_fourCopyTripleMatching_exists_strictPhysicalRoute
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites)
    {i j k : I} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (K : Finset (StatMech.Sharpness.FluxEdgeCopy.Copy
      (lpReplicaCurrentGraph G sites) m))
    (hKcard : K.card = 4)
    (hsupport :
      K.biUnion (fun e =>
        (StatMech.Sharpness.FluxEdgeCopy.endsM
          (lpReplicaCurrentGraph G sites) m e).toFinset) =
        lpReplicaTripleSeamGhostSource sites i j k)
    (hunique : ∀ x ∈ lpReplicaTripleSeamGhostSource sites i j k,
      ∃! e, e ∈ K ∧ x ∈
        (StatMech.Sharpness.FluxEdgeCopy.endsM
          (lpReplicaCurrentGraph G sites) m e).toFinset)
    (hnoI : ∀ e ∈ K, e.1.1 ≠ lpReplicaCurrentSeamEdge sites i)
    (hnoJ : ∀ e ∈ K, e.1.1 ≠ lpReplicaCurrentSeamEdge sites j) :
    ∃ e ∈ K,
      (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V) ∉
          StatMech.Sharpness.FluxEdgeCopy.endsM
            (lpReplicaCurrentGraph G sites) m e ∧
        (lpReplicaCurrentGhost1 : LPReplicaCurrentVertex V) ∉
          StatMech.Sharpness.FluxEdgeCopy.endsM
            (lpReplicaCurrentGraph G sites) m e ∧
        ¬ (lpReplicaCurrentFoldedEdge G sites e.1).IsDiag := by
  classical
  let E := StatMech.Sharpness.FluxEdgeCopy.endsM
    (lpReplicaCurrentGraph G sites) m
  let A := K.filter fun e =>
    (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V) ∈ E e ∨
      (lpReplicaCurrentGhost1 : LPReplicaCurrentVertex V) ∈ E e
  let D := K.filter fun e =>
    (lpReplicaCurrentFoldedEdge G sites e.1).IsDiag
  obtain ⟨c0, hc0, hc0unique⟩ := hunique lpReplicaCurrentGhost0
    (lpReplicaCurrentGhost0_mem_tripleSeamGhostSource sites i j k)
  obtain ⟨c1, hc1, hc1unique⟩ := hunique lpReplicaCurrentGhost1
    (lpReplicaCurrentGhost1_mem_tripleSeamGhostSource sites i j k)
  have hAsub : A ⊆ {c0, c1} := by
    intro e heA
    obtain ⟨heK, heghost⟩ := Finset.mem_filter.mp heA
    rcases heghost with he0 | he1
    · have heq : e = c0 := hc0unique e
        ⟨heK, Sym2.mem_toFinset.mpr he0⟩
      simp [heq]
    · have heq : e = c1 := hc1unique e
        ⟨heK, Sym2.mem_toFinset.mpr he1⟩
      simp [heq]
  have hAcard : A.card ≤ 2 := by
    exact (Finset.card_le_card hAsub).trans Finset.card_le_two
  have seamK_of_mem_D {e : StatMech.Sharpness.FluxEdgeCopy.Copy
      (lpReplicaCurrentGraph G sites) m} (heD : e ∈ D) :
      e.1.1 = lpReplicaCurrentSeamEdge sites k := by
    obtain ⟨heK, hediag⟩ := Finset.mem_filter.mp heD
    obtain ⟨t, het⟩ :=
      (lpReplicaCurrentFoldedEdge_isDiag_iff_exists_seam
        G sites e.1).mp hediag
    have hleftEnds : lpReplicaCurrentLeft sites t ∈ E e := by
      change lpReplicaCurrentLeft sites t ∈ e.1.1
      rw [het]
      simp [lpReplicaCurrentSeamEdge]
    have hleftBoundary : lpReplicaCurrentLeft sites t ∈
        lpReplicaTripleSeamGhostSource sites i j k := by
      rw [← hsupport]
      apply Finset.mem_biUnion.mpr
      exact ⟨e, heK, Sym2.mem_toFinset.mpr hleftEnds⟩
    have ht := (lpReplicaCurrentLeft_mem_tripleSeamGhostSource_iff
      sites hsite hij hik hjk).mp hleftBoundary
    rcases ht with rfl | rfl | rfl
    · exact False.elim (hnoI e heK het)
    · exact False.elim (hnoJ e heK het)
    · exact het
  have hDcard : D.card ≤ 1 := by
    rw [Finset.card_le_one]
    intro e heD f hfD
    have heK := (Finset.mem_filter.mp heD).1
    have hfK := (Finset.mem_filter.mp hfD).1
    have heSeam := seamK_of_mem_D heD
    have hfSeam := seamK_of_mem_D hfD
    have hleftBoundary : lpReplicaCurrentLeft sites k ∈
        lpReplicaTripleSeamGhostSource sites i j k :=
      (lpReplicaCurrentLeft_mem_tripleSeamGhostSource_iff
        sites hsite hij hik hjk).mpr (Or.inr (Or.inr rfl))
    obtain ⟨d, hd, hdunique⟩ := hunique
      (lpReplicaCurrentLeft sites k) hleftBoundary
    have heLeft : lpReplicaCurrentLeft sites k ∈ E e := by
      change lpReplicaCurrentLeft sites k ∈ e.1.1
      rw [heSeam]
      simp [lpReplicaCurrentSeamEdge]
    have hfLeft : lpReplicaCurrentLeft sites k ∈ E f := by
      change lpReplicaCurrentLeft sites k ∈ f.1.1
      rw [hfSeam]
      simp [lpReplicaCurrentSeamEdge]
    exact (hdunique e ⟨heK, Sym2.mem_toFinset.mpr heLeft⟩).trans
      (hdunique f ⟨hfK, Sym2.mem_toFinset.mpr hfLeft⟩).symm
  have hADcard : (A ∪ D).card ≤ 3 :=
    (Finset.card_union_le A D).trans (by omega)
  have hnotSubset : ¬ K ⊆ A ∪ D := by
    intro hsub
    have hle := Finset.card_le_card hsub
    rw [hKcard] at hle
    omega
  have hex : ∃ e, e ∈ K ∧ e ∉ A ∪ D := by
    by_contra h
    apply hnotSubset
    intro e heK
    by_contra heAD
    rw [not_exists] at h
    exact h e ⟨heK, heAD⟩
  obtain ⟨e, heK, heAD⟩ := hex
  have heA : e ∉ A := by
    intro he
    exact heAD (Finset.mem_union_left D he)
  have heD : e ∉ D := by
    intro he
    exact heAD (Finset.mem_union_right A he)
  have heghost : ¬ ((lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V) ∈ E e ∨
      (lpReplicaCurrentGhost1 : LPReplicaCurrentVertex V) ∈ E e) := by
    intro h
    apply heA
    exact Finset.mem_filter.mpr ⟨heK, h⟩
  refine ⟨e, heK, ?_, ?_, ?_⟩
  · exact fun h => heghost (Or.inl h)
  · exact fun h => heghost (Or.inr h)
  · intro hdiag
    apply heD
    exact Finset.mem_filter.mpr ⟨heK, hdiag⟩



theorem lpReplica_strictPhysicalRoute_folded_labels
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites)
    {i j k : I} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (K : Finset (StatMech.Sharpness.FluxEdgeCopy.Copy
      (lpReplicaCurrentGraph G sites) m))
    (hsupport :
      K.biUnion (fun e =>
        (StatMech.Sharpness.FluxEdgeCopy.endsM
          (lpReplicaCurrentGraph G sites) m e).toFinset) =
        lpReplicaTripleSeamGhostSource sites i j k)
    (d : StatMech.Sharpness.FluxEdgeCopy.Copy
      (lpReplicaCurrentGraph G sites) m)
    (hdK : d ∈ K)
    (hd0 : (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V) ∉
      StatMech.Sharpness.FluxEdgeCopy.endsM
        (lpReplicaCurrentGraph G sites) m d)
    (hd1 : (lpReplicaCurrentGhost1 : LPReplicaCurrentVertex V) ∉
      StatMech.Sharpness.FluxEdgeCopy.endsM
        (lpReplicaCurrentGraph G sites) m d)
    (hddiag : ¬ (lpReplicaCurrentFoldedEdge G sites d.1).IsDiag) :
    ∃ u v,
      (u = i ∨ u = j ∨ u = k) ∧
      (v = i ∨ v = j ∨ v = k) ∧
      u ≠ v ∧
      lpReplicaCurrentFoldedEdge G sites d.1 =
        s(Sum.inl (sites u), Sum.inl (sites v)) := by
  let E := StatMech.Sharpness.FluxEdgeCopy.endsM
    (lpReplicaCurrentGraph G sites) m
  induction hval : d.1.1 using Sym2.inductionOn with
  | _ x y =>
      have hxEnds : x ∈ E d := by
        change x ∈ d.1.1
        rw [hval]
        simp
      have hyEnds : y ∈ E d := by
        change y ∈ d.1.1
        rw [hval]
        simp
      have hxBoundary : x ∈ lpReplicaTripleSeamGhostSource sites i j k := by
        rw [← hsupport]
        exact Finset.mem_biUnion.mpr
          ⟨d, hdK, Sym2.mem_toFinset.mpr hxEnds⟩
      have hyBoundary : y ∈ lpReplicaTripleSeamGhostSource sites i j k := by
        rw [← hsupport]
        exact Finset.mem_biUnion.mpr
          ⟨d, hdK, Sym2.mem_toFinset.mpr hyEnds⟩
      have hx0 : x ≠ lpReplicaCurrentGhost0 := fun h => hd0 (h ▸ hxEnds)
      have hx1 : x ≠ lpReplicaCurrentGhost1 := fun h => hd1 (h ▸ hxEnds)
      have hy0 : y ≠ lpReplicaCurrentGhost0 := fun h => hd0 (h ▸ hyEnds)
      have hy1 : y ≠ lpReplicaCurrentGhost1 := fun h => hd1 (h ▸ hyEnds)
      obtain ⟨u, hu, hxu⟩ :=
        lpReplicaCurrentFold_eq_site_of_mem_tripleSeamGhostSource
          sites hsite hij hik hjk x hxBoundary hx0 hx1
      obtain ⟨v, hv, hyv⟩ :=
        lpReplicaCurrentFold_eq_site_of_mem_tripleSeamGhostSource
          sites hsite hij hik hjk y hyBoundary hy0 hy1
      have hfold : lpReplicaCurrentFoldedEdge G sites d.1 =
          s(Sum.inl (sites u), Sum.inl (sites v)) := by
        unfold lpReplicaCurrentFoldedEdge
        rw [hval, Sym2.map_mk, hxu, hyv]
      have huv : u ≠ v := by
        intro huv
        subst v
        apply hddiag
        rw [hfold, Sym2.mk_isDiag_iff]
      exact ⟨u, v, hu, hv, huv, hfold⟩


def lpReplicaThirdOfThree (i j k u v : I) : I :=
  if i ≠ u ∧ i ≠ v then i
  else if j ≠ u ∧ j ≠ v then j
  else k



theorem lpReplicaThirdOfThree_spec
    {i j k u v : I} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hu : u = i ∨ u = j ∨ u = k)
    (hv : v = i ∨ v = j ∨ v = k) (huv : u ≠ v) :
    let l := lpReplicaThirdOfThree i j k u v
    l ≠ u ∧ l ≠ v ∧ (l = i ∨ l = j ∨ l = k) := by
  dsimp only
  rcases hu with rfl | rfl | rfl <;>
    rcases hv with rfl | rfl | rfl <;>
    simp_all [lpReplicaThirdOfThree] <;> aesop



theorem lpReplicaCurrentEdge_toFinset_symmDiff_reflect_eq_seams
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites)
    (e : (lpReplicaCurrentGraph G sites).edgeFinset)
    {u v : I} (huv : u ≠ v)
    (hfold : lpReplicaCurrentFoldedEdge G sites e =
      s(Sum.inl (sites u), Sum.inl (sites v))) :
    (Sym2.toFinset (e.1)) ∆
        (Sym2.toFinset (Sym2.map lpReplicaCurrentReflect (e.1))) =
      lpMatchingSeamSource
          (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) u ∆
        lpMatchingSeamSource
          (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) v := by
  have hsuv : sites u ≠ sites v := hsite.ne huv
  induction hval : e.1 using Sym2.inductionOn with
  | _ x y =>
      have hxy : (lpReplicaCurrentGraph G sites).Adj x y := by
        have hmem := e.2
        rw [SimpleGraph.mem_edgeFinset, hval, SimpleGraph.mem_edgeSet] at hmem
        exact hmem
      unfold lpReplicaCurrentFoldedEdge at hfold
      rw [hval, Sym2.map_mk] at hfold
      rcases x with (x | g) <;> rcases y with (y | h)
      · rcases x with x | x <;> rcases y with y | y
        · rw [Sym2.eq_iff] at hfold
          simp only [lpReplicaCurrentFold, Sum.inl.injEq] at hfold
          rcases hfold with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
            ext z <;>
            simp [hval, lpMatchingSeamSource, lpReplicaCurrentLeft,
              lpReplicaCurrentRight, lpReplicaCurrentReflect,
              Finset.mem_symmDiff, hsuv, hsuv.symm] <;> aesop
        · rw [lpReplicaCurrentGraph_adj_left_right_iff] at hxy
          obtain ⟨t, htx, hty⟩ := hxy
          have hxy' : x = y := htx.symm.trans hty
          rw [Sym2.eq_iff] at hfold
          simp only [lpReplicaCurrentFold, Sum.inl.injEq] at hfold
          rcases hfold with h | h
          · exact False.elim (hsuv (h.1.symm.trans (hxy'.trans h.2)))
          · exact False.elim (hsuv (h.2.symm.trans (hxy'.symm.trans h.1)))
        · rw [(lpReplicaCurrentGraph G sites).adj_comm,
            lpReplicaCurrentGraph_adj_left_right_iff] at hxy
          obtain ⟨t, hty, htx⟩ := hxy
          have hxy' : x = y := htx.symm.trans hty
          rw [Sym2.eq_iff] at hfold
          simp only [lpReplicaCurrentFold, Sum.inl.injEq] at hfold
          rcases hfold with h | h
          · exact False.elim (hsuv (h.1.symm.trans (hxy'.trans h.2)))
          · exact False.elim (hsuv (h.2.symm.trans (hxy'.symm.trans h.1)))
        · rw [Sym2.eq_iff] at hfold
          simp only [lpReplicaCurrentFold, Sum.inl.injEq] at hfold
          rcases hfold with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
            ext z <;>
            simp [hval, lpMatchingSeamSource, lpReplicaCurrentLeft,
              lpReplicaCurrentRight, lpReplicaCurrentReflect,
              Finset.mem_symmDiff, hsuv, hsuv.symm] <;> aesop
      · rcases x with x | x <;> cases h <;>
          rw [Sym2.eq_iff] at hfold <;>
          simp only [lpReplicaCurrentFold, Sum.inl.injEq,
            Sum.inr.injEq, reduceCtorEq, and_false, false_and,
            or_self] at hfold
      · cases g <;> rcases y with y | y <;>
          rw [Sym2.eq_iff] at hfold <;>
          simp only [lpReplicaCurrentFold, Sum.inl.injEq,
            Sum.inr.injEq, reduceCtorEq, and_false, false_and,
            or_self] at hfold
      · cases g <;> cases h <;>
          rw [Sym2.eq_iff] at hfold <;>
          simp only [lpReplicaCurrentFold, Sum.inl.injEq,
            Sum.inr.injEq, reduceCtorEq, and_false, false_and,
            or_self] at hfold

set_option maxHeartbeats 1200000 in



theorem lpReplicaAggregateUnmarkedSaturatedSourceRankFive_exists_strictPhysicalRoute
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
    (z : LPReplicaAggregateUnmarkedSaturatedSourceRankFive G sites q) :
    let a := z.toAggregate G sites q
    let k := lpReplicaAggregateDecoratedSourceSelectedSeam
      G sites hsite q a
    ∃ c d : StatMech.Sharpness.FluxEdgeCopy.Copy
        (lpReplicaCurrentGraph G sites) a.2.2.2.1.1.1,
      c.1.1 = lpReplicaCurrentSeamEdge sites k ∧
        d ∈ Finset.univ \ {c} ∧
        (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V) ∉
          StatMech.Sharpness.FluxEdgeCopy.endsM
            (lpReplicaCurrentGraph G sites) a.2.2.2.1.1.1 d ∧
        (lpReplicaCurrentGhost1 : LPReplicaCurrentVertex V) ∉
          StatMech.Sharpness.FluxEdgeCopy.endsM
            (lpReplicaCurrentGraph G sites) a.2.2.2.1.1.1 d ∧
        ¬ (lpReplicaCurrentFoldedEdge G sites d.1).IsDiag := by
  classical
  dsimp only
  let a := z.toAggregate G sites q
  let k := lpReplicaAggregateDecoratedSourceSelectedSeam
    G sites hsite q a
  have hpm :=
    lpReplicaAggregateUnmarkedSaturatedSourceRankFive_selectedSeam_perfectMatching
      G sites hsite q hcard z
  change ∃ c : StatMech.Sharpness.FluxEdgeCopy.Copy
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
          ∃! e, e ∈ K ∧ x ∈ (E e).toFinset at hpm
  obtain ⟨c, hc, hKcard, hsources, hsupport, hunique⟩ := hpm
  let K := Finset.univ \ {c}
  have hij : a.1 ≠ a.2.1 :=
    lpReplicaAggregateDecoratedSource_indices_ne G sites q a
  have hkunmarked :=
    lpReplicaAggregateUnmarkedSaturatedSourceRankFive_selectedSeam_unmarked
      G sites hsite q hcard z
  have hik : a.1 ≠ k := Ne.symm hkunmarked.1
  have hjk : a.2.1 ≠ k := Ne.symm hkunmarked.2
  have hunmarked :=
    LPReplicaOffdiagDecoratedSource.isUnmarkedSaturatedRankFive_of_mem_complement
      G sites hsite hij q hcard z.2.2.2.1 z.2.2.2.2
  obtain ⟨d, hdK, hd0, hd1, hddiag⟩ :=
    lpReplica_fourCopyTripleMatching_exists_strictPhysicalRoute
      G sites hsite hij hik hjk a.2.2.2.1.1.1 K hKcard hsupport hunique
        (fun e _ => hunmarked.2.1 e) (fun e _ => hunmarked.2.2 e)
  exact ⟨c, d, hc, hdK, hd0, hd1, hddiag⟩

set_option maxHeartbeats 1200000 in



theorem lpReplicaAggregateUnmarkedSaturatedSourceRankFive_exists_labeledRoute
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
    (z : LPReplicaAggregateUnmarkedSaturatedSourceRankFive G sites q) :
    let a := z.toAggregate G sites q
    let k := lpReplicaAggregateDecoratedSourceSelectedSeam
      G sites hsite q a
    ∃ c d : StatMech.Sharpness.FluxEdgeCopy.Copy
          (lpReplicaCurrentGraph G sites) a.2.2.2.1.1.1,
      ∃ u v,
      c.1.1 = lpReplicaCurrentSeamEdge sites k ∧
        d ∈ Finset.univ \ {c} ∧
        (u = a.1 ∨ u = a.2.1 ∨ u = k) ∧
        (v = a.1 ∨ v = a.2.1 ∨ v = k) ∧
        u ≠ v ∧
        lpReplicaCurrentFoldedEdge G sites d.1 =
          s(Sum.inl (sites u), Sum.inl (sites v)) ∧
        let l := lpReplicaThirdOfThree a.1 a.2.1 k u v
        l ≠ u ∧ l ≠ v ∧ (l = a.1 ∨ l = a.2.1 ∨ l = k) := by
  classical
  dsimp only
  let a := z.toAggregate G sites q
  let k := lpReplicaAggregateDecoratedSourceSelectedSeam
    G sites hsite q a
  have hroute :=
    lpReplicaAggregateUnmarkedSaturatedSourceRankFive_exists_strictPhysicalRoute
      G sites hsite q hcard z
  change ∃ c d : StatMech.Sharpness.FluxEdgeCopy.Copy
      (lpReplicaCurrentGraph G sites) a.2.2.2.1.1.1,
    c.1.1 = lpReplicaCurrentSeamEdge sites k ∧
      d ∈ Finset.univ \ {c} ∧
      (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V) ∉
        StatMech.Sharpness.FluxEdgeCopy.endsM
          (lpReplicaCurrentGraph G sites) a.2.2.2.1.1.1 d ∧
      (lpReplicaCurrentGhost1 : LPReplicaCurrentVertex V) ∉
        StatMech.Sharpness.FluxEdgeCopy.endsM
          (lpReplicaCurrentGraph G sites) a.2.2.2.1.1.1 d ∧
      ¬ (lpReplicaCurrentFoldedEdge G sites d.1).IsDiag at hroute
  obtain ⟨c, d, hc, hdK, hd0, hd1, hddiag⟩ := hroute
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
  have hKcard : K.card = 4 :=
    lpReplicaOffdiagDecoratedSource_card_erase_copy_rankFive
      G sites q hcard a.2.2.2 c
  have hsources : StatMech.Sharpness.RandomCurrent.sources E K =
      lpReplicaTripleSeamGhostSource sites a.1 a.2.1 k :=
    lpReplicaOffdiagDecoratedSource_sources_erase_seamCopy
      G sites q a.2.2.2 c hc
  have htight :
      (StatMech.Sharpness.RandomCurrent.sources E K).card = 2 * K.card := by
    rw [hsources, card_lpReplicaTripleSeamGhostSource sites hsite
      hij hik hjk, hKcard]
  have hsupport : K.biUnion (fun e => (E e).toFinset) =
      lpReplicaTripleSeamGhostSource sites a.1 a.2.1 k :=
    (randomCurrent_endpointSupport_eq_sources_of_card_eq_two_mul
      E K htight).trans hsources
  obtain ⟨u, v, hu, hv, huv, hfold⟩ :=
    lpReplica_strictPhysicalRoute_folded_labels G sites hsite
      hij hik hjk a.2.2.2.1.1.1 K hsupport d hdK hd0 hd1 hddiag
  have hl := lpReplicaThirdOfThree_spec hij hik hjk hu hv huv
  exact ⟨c, d, u, v, hc, hdK, hu, hv, huv, hfold, hl⟩

end

end StatMech.Ising

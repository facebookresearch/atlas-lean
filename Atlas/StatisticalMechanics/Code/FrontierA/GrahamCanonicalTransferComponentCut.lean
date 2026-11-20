/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierA.GrahamCanonicalTransferAmbientQuadrangle
import Code.FrontierA.GrahamWeightedComponent










open Finset
open scoped symmDiff

namespace StatMech.GrahamGHS.FourColor

open StatMech.Sharpness.RandomCurrent

variable {I W : Type*} [Fintype I] [DecidableEq I]
  [Fintype W] [DecidableEq W]



theorem edgeComponent_eq_grahamSuperpositionBondComponent
    (ends : I -> Sym2 W) (K : Finset I) (u : W) :
    edgeComponent ends K u =
      StatMech.FrontierA.grahamSuperpositionBondComponent ends K u := by
  classical
  ext i
  rw [edgeComponent, Finset.mem_filter,
    StatMech.FrontierA.grahamSuperpositionBondComponent,
    StatMech.Walls.gh4_mem_bondCompOf]
  constructor
  · rintro ⟨hiK, hi⟩
    let x := (ends i).out.1
    exact ⟨hiK, x, Sym2.out_fst_mem (ends i),
      hi x (Sym2.out_fst_mem (ends i))⟩
  · rintro ⟨hiK, x, hx, hux⟩
    refine ⟨hiK, ?_⟩
    intro y hy
    by_cases hxy : x = y
    · simpa [hxy] using hux
    · exact hux.tail ⟨i, hiK, hx, hy, hxy⟩



theorem mem_sdiff_edgeComponent_iff_edgeInside_componentComplement
    (ends : I -> Sym2 W) (K : Finset I) (u : W) {i : I} :
    i ∈ K \ edgeComponent ends K u ↔
      i ∈ K ∧
        edgeInsideK ends
          (StatMech.FrontierA.grahamComponentComplement ends K u) i := by
  rw [edgeComponent_eq_grahamSuperpositionBondComponent]
  exact StatMech.FrontierA.mem_sdiff_component_iff_edgeInsideK_complement
    ends K u



theorem edgeComponentComplement_noCrossing_of_subset
    (ends : I -> Sym2 W) (K L : Finset I) (u : W) (hLK : L ⊆ K) :
    NoCrossingK ends L
      (StatMech.FrontierA.grahamComponentComplement ends K u) :=
  StatMech.FrontierA.grahamComponentComplement_noCrossing_of_subset
    ends K L u hLK


theorem connK_mem_of_noCrossing
    {ends : I -> Sym2 W} {K : Finset I} {S : Finset W} {u x : W}
    (hcross : NoCrossingK ends K S) (hu : u ∈ S)
    (hux : connK ends K u x) : x ∈ S := by
  induction hux with
  | refl => exact hu
  | @tail a b _ hstep ih =>
      obtain ⟨i, hiK, ha, hb, -⟩ := hstep
      rcases hcross i hiK with hin | hout
      · exact hin b hb
      · exact False.elim ((Finset.mem_compl.mp (hout a ha)) ih)


theorem connK_not_mem_of_noCrossing
    {ends : I -> Sym2 W} {K : Finset I} {S : Finset W} {u x : W}
    (hcross : NoCrossingK ends K S) (hu : u ∉ S)
    (hux : connK ends K u x) : x ∉ S := by
  intro hx
  exact hu (connK_mem_of_noCrossing hcross hx
    (connK_symm ends K hux))



theorem exists_crossing_edge_mem_sdiff_of_connK
    {ends : I -> Sym2 W} {K L : Finset I} {S : Finset W} {u x : W}
    (hcross : NoCrossingK ends K S) (hu : u ∉ S) (hx : x ∈ S)
    (hux : connK ends L u x) :
    ∃ i, i ∈ L \ K ∧
      ∃ a b, a ∈ ends i ∧ b ∈ ends i ∧ a ∉ S ∧ b ∈ S := by
  have crossing : ∀ y, connK ends L u y -> y ∈ S ->
      ∃ i, i ∈ L \ K ∧
        ∃ a b, a ∈ ends i ∧ b ∈ ends i ∧ a ∉ S ∧ b ∈ S := by
    intro y huy hy
    induction huy with
    | refl => exact False.elim (hu hy)
    | @tail a b hab hstep ih =>
        obtain ⟨i, hiL, ha, hb, -⟩ := hstep
        by_cases haS : a ∈ S
        · exact ih haS
        · refine ⟨i, Finset.mem_sdiff.mpr ⟨hiL, ?_⟩,
            a, b, ha, hb, haS, hy⟩
          intro hiK
          rcases hcross i hiK with hin | hout
          · exact haS (hin a ha)
          · exact (Finset.mem_compl.mp (hout b hb)) hy
  exact crossing x hux hx



theorem edgeInside_compl_componentComplement_of_mem_edgeComponent
    (ends : I -> Sym2 W) (K : Finset I) (u : W) {i : I}
    (hi : i ∈ edgeComponent ends K u) :
    edgeInsideK ends
      (StatMech.FrontierA.grahamComponentComplement ends K u)ᶜ i := by
  classical
  intro x hx
  apply Finset.mem_compl.mpr
  apply connK_not_mem_of_noCrossing
    (StatMech.FrontierA.grahamComponentComplement_noCrossing ends K u)
    (StatMech.FrontierA.grahamComponentComplement_not_mem ends K u)
  rw [edgeComponent, Finset.mem_filter] at hi
  exact hi.2 x hx



theorem mem_edgeComponent_iff_edgeInside_compl_componentComplement
    (ends : I -> Sym2 W) (K : Finset I) (u : W) {i : I} :
    i ∈ edgeComponent ends K u ↔
      i ∈ K ∧ edgeInsideK ends
        (StatMech.FrontierA.grahamComponentComplement ends K u)ᶜ i := by
  classical
  constructor
  · intro hi
    rw [edgeComponent, Finset.mem_filter] at hi
    exact ⟨hi.1,
      edgeInside_compl_componentComplement_of_mem_edgeComponent
        ends K u (by
          rw [edgeComponent, Finset.mem_filter]
          exact hi)⟩
  · rintro ⟨hiK, hout⟩
    let x := (ends i).out.1
    have hx : x ∈ ends i := Sym2.out_fst_mem (ends i)
    have hxNot : x ∉
        StatMech.FrontierA.grahamComponentComplement ends K u :=
      Finset.mem_compl.mp (hout x hx)
    have hux : connK ends K u x := by
      rw [StatMech.FrontierA.grahamComponentComplement,
        mem_notConnCompK] at hxNot
      exact Classical.byContradiction (fun h => hxNot h)
    exact mem_edgeComponent_of_reachable_endpoint hux hiK hx



theorem not_mem_ends_of_mem_sdiff_edgeComponent_of_conn
    (ends : I -> Sym2 W) (K : Finset I) (u v : W) {i : I}
    (hi : i ∈ K \ edgeComponent ends K u) (huv : connK ends K u v) :
    v ∉ ends i := by
  intro hvi
  have hins := (mem_sdiff_edgeComponent_iff_edgeInside_componentComplement
    ends K u).mp hi |>.2 v hvi
  rw [StatMech.FrontierA.grahamComponentComplement,
    mem_notConnCompK] at hins
  exact hins huv



theorem sources_inter_edgeComponent_and_sdiff_eq_empty
    (ends : I -> Sym2 W) (K D : Finset I) (u : W)
    (hDK : D ⊆ K) (hDsrc : sources ends D = ∅) :
    sources ends (D ∩ edgeComponent ends K u) = ∅ ∧
      sources ends (D \ edgeComponent ends K u) = ∅ := by
  have hinter : sources ends (D ∩ edgeComponent ends K u) = ∅ := by
    rw [sources_inter_edgeComponent hDK u, hDsrc]
    simp
  refine ⟨hinter, ?_⟩
  have heq : D \ edgeComponent ends K u =
      D \ (D ∩ edgeComponent ends K u) := by
    ext i
    simp
  rw [heq, sources_sdiff_of_subset Finset.inter_subset_left,
    hDsrc, hinter]
  simp


theorem noCrossing_componentComplement_of_subset
    (ends : I -> Sym2 W) (K D : Finset I) (u : W) (hDK : D ⊆ K) :
    NoCrossingK ends D
      (StatMech.FrontierA.grahamComponentComplement ends K u) :=
  edgeComponentComplement_noCrossing_of_subset ends K D u hDK



theorem sources_canonicalTransferUnion
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l)
    {p : Finset I × Finset I}
    (r : leftMaskFiber ends m j k l zero p) :
    sources ends (canonicalTransferUnion ends m k zero r.1.1) =
      {k, l} := by
  have hv := canonicalTransfers_valid hloop hjk hkl r.1.2
  have hdisj : Disjoint
      (canonicalMiddleTransfer ends m r.1.1 k zero)
      (canonicalOuterTransfer ends m r.1.1 k zero) :=
    (middleMask_disjoint_outerMask m r.1.1).mono
      (by simpa only [middleMask] using hv.1)
      (by simpa only [outerMask] using hv.2.1)
  rw [canonicalTransferUnion, sources_union_of_disjoint hdisj,
    hv.2.2.1, hv.2.2.2]
  simp


theorem sources_canonicalNormalRow
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l)
    {p : Finset I × Finset I}
    (c : leftMaskFiber ends m j k l zero p) :
    sources ends (canonicalNormalRow ends m k zero c.1.1) =
      {j, k} ∆ {k, l} := by
  rw [canonicalNormalRow, sources_symmDiff,
    (leftPattern_rowBoundaries c.1.2).1,
    sources_canonicalTransferUnion hloop hjk hkl c]


theorem sources_canonicalNormalRow_symmDiff_eq_empty
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l)
    {p : Finset I × Finset I}
    (c d : leftMaskFiber ends m j k l zero p) :
    sources ends
      (canonicalNormalRow ends m k zero c.1.1 ∆
        canonicalNormalRow ends m k zero d.1.1) = ∅ := by
  rw [sources_symmDiff,
    sources_canonicalNormalRow hloop hjk hkl c,
    sources_canonicalNormalRow hloop hjk hkl d]
  exact symmDiff_self _


theorem sources_fourfold_canonicalTransferUnion_symmDiff
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l)
    {p : Finset I × Finset I}
    (a b c d : leftMaskFiber ends m j k l zero p) :
    sources ends
      (canonicalTransferUnion ends m k zero a.1.1 ∆
        canonicalTransferUnion ends m k zero b.1.1 ∆
        canonicalTransferUnion ends m k zero c.1.1 ∆
        canonicalTransferUnion ends m k zero d.1.1) = ∅ := by
  rw [sources_symmDiff, sources_symmDiff, sources_symmDiff,
    sources_canonicalTransferUnion hloop hjk hkl a,
    sources_canonicalTransferUnion hloop hjk hkl b,
    sources_canonicalTransferUnion hloop hjk hkl c,
    sources_canonicalTransferUnion hloop hjk hkl d]
  simp




theorem sources_canonicalTransferUnion_symmDiff_eq_empty
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l)
    {p : Finset I × Finset I}
    (a b : leftMaskFiber ends m j k l zero p) :
    sources ends
      (canonicalTransferUnion ends m k zero a.1.1 ∆
        canonicalTransferUnion ends m k zero b.1.1) = ∅ := by
  rw [sources_symmDiff,
    sources_canonicalTransferUnion hloop hjk hkl a,
    sources_canonicalTransferUnion hloop hjk hkl b]
  simp


theorem mem_canonicalTransferUnion_iff_rooted_endpoints
    (ends : I -> Sym2 W) (m : Finset I) (k zero : W)
    (c : ↑m -> Fin 4) (i : I) :
    i ∈ canonicalTransferUnion ends m k zero c ↔
      (i ∈ rowClass m c 0 ∧
          ∀ x ∈ ends i, connK ends (rowClass m c 0) zero x) ∨
        (i ∈ rowClass m c 1 ∧
          ∀ x ∈ ends i, connK ends (rowClass m c 1) k x) := by
  classical
  rw [canonicalTransferUnion, canonicalTransfers_union]
  simp only [Finset.mem_union, edgeComponent, Finset.mem_filter]




theorem mem_canonicalTransferUnion_iff_rootComponents
    (ends : I -> Sym2 W) (m : Finset I) (k zero : W)
    (c : ↑m -> Fin 4) (i : I) :
    i ∈ canonicalTransferUnion ends m k zero c ↔
      i ∈ edgeComponent ends (rowClass m c 0) zero ∨
        i ∈ edgeComponent ends (rowClass m c 1) k := by
  rw [canonicalTransferUnion, canonicalTransfers_union,
    Finset.mem_union]



theorem mem_zeroRootComponent_iff_mem_rowZero_of_mem_canonicalTransferUnion
    (ends : I -> Sym2 W) (m : Finset I) (k zero : W)
    (c : ↑m -> Fin 4) (i : I)
    (hi : i ∈ canonicalTransferUnion ends m k zero c) :
    i ∈ edgeComponent ends (rowClass m c 0) zero ↔
      i ∈ rowClass m c 0 := by
  classical
  constructor
  · intro hiz
    rw [edgeComponent, Finset.mem_filter] at hiz
    exact hiz.1
  · intro hi0
    rcases (mem_canonicalTransferUnion_iff_rootComponents
      ends m k zero c i).mp hi with hiz | hik
    · exact hiz
    · have hi1 := hik
      rw [edgeComponent, Finset.mem_filter] at hi1
      have hi1 := hi1.1
      rw [rowClass_one_eq_sdiff, Finset.mem_sdiff] at hi1
      exact False.elim (hi1.2 hi0)



theorem mem_kRootComponent_iff_not_mem_rowZero_of_mem_canonicalTransferUnion
    (ends : I -> Sym2 W) (m : Finset I) (k zero : W)
    (c : ↑m -> Fin 4) (i : I)
    (hi : i ∈ canonicalTransferUnion ends m k zero c) :
    i ∈ edgeComponent ends (rowClass m c 1) k ↔
      i ∉ rowClass m c 0 := by
  classical
  constructor
  · intro hik hi0
    have hi1 := hik
    rw [edgeComponent, Finset.mem_filter] at hi1
    have hi1 := hi1.1
    rw [rowClass_one_eq_sdiff, Finset.mem_sdiff] at hi1
    exact hi1.2 hi0
  · intro hi0
    rcases (mem_canonicalTransferUnion_iff_rootComponents
      ends m k zero c i).mp hi with hiz | hik
    · have hiz' := hiz
      rw [edgeComponent, Finset.mem_filter] at hiz'
      exact False.elim (hi0 hiz'.1)
    · exact hik



theorem canonicalTransferUnion_disjoint_nonrootRowZero
    (ends : I -> Sym2 W) (m : Finset I) (k zero : W)
    (c : ↑m -> Fin 4) :
    Disjoint (canonicalTransferUnion ends m k zero c)
      (rowClass m c 0 \
        edgeComponent ends (rowClass m c 0) zero) := by
  classical
  rw [Finset.disjoint_left]
  intro i hiT hiOutside
  have hi0 := (Finset.mem_sdiff.mp hiOutside).1
  exact (Finset.mem_sdiff.mp hiOutside).2
    ((mem_zeroRootComponent_iff_mem_rowZero_of_mem_canonicalTransferUnion
      ends m k zero c i hiT).mpr hi0)



theorem canonicalTransferUnion_disjoint_nonrootRowOne
    (ends : I -> Sym2 W) (m : Finset I) (k zero : W)
    (c : ↑m -> Fin 4) :
    Disjoint (canonicalTransferUnion ends m k zero c)
      (rowClass m c 1 \
        edgeComponent ends (rowClass m c 1) k) := by
  classical
  rw [Finset.disjoint_left]
  intro i hiT hiOutside
  have hi1 := (Finset.mem_sdiff.mp hiOutside).1
  rw [rowClass_one_eq_sdiff, Finset.mem_sdiff] at hi1
  exact (Finset.mem_sdiff.mp hiOutside).2
    ((mem_kRootComponent_iff_not_mem_rowZero_of_mem_canonicalTransferUnion
      ends m k zero c i hiT).mpr hi1.2)



def TwoRootSpanning (ends : I -> Sym2 W) (S : Finset I)
    (u v : W) : Prop :=
  ∀ i ∈ S, ∀ x ∈ ends i,
    connK ends S u x ∨ connK ends S v x

private theorem connK_edgeComponent_of_conn_cut
    (ends : I -> Sym2 W) (K : Finset I) (u x : W)
    (hux : connK ends K u x) :
    connK ends (edgeComponent ends K u) u x := by
  classical
  induction hux with
  | refl => exact Relation.ReflTransGen.refl
  | @tail a b _ hstep ih =>
      obtain ⟨i, hiK, ha, hb, hab⟩ := hstep
      have hua : connK ends K u a := by
        apply connK_mono _ ih
        intro e he
        rw [edgeComponent, Finset.mem_filter] at he
        exact he.1
      exact ih.tail ⟨i,
        mem_edgeComponent_of_reachable_endpoint hua hiK ha,
        ha, hb, hab⟩


theorem canonicalTransferUnion_twoRootSpanning
    (ends : I -> Sym2 W) (m : Finset I) (k zero : W)
    (c : ↑m -> Fin 4) :
    TwoRootSpanning ends (canonicalTransferUnion ends m k zero c)
      k zero := by
  classical
  intro i hi x hx
  have hunion := canonicalTransfers_union
    (ends := ends) (m := m) (k := k) (zero := zero) (c := c)
  change i ∈ canonicalMiddleTransfer ends m c k zero ∪
    canonicalOuterTransfer ends m c k zero at hi
  rw [hunion, Finset.mem_union] at hi
  have hzeroSub : edgeComponent ends (rowClass m c 0) zero ⊆
      canonicalTransferUnion ends m k zero c := by
    rw [canonicalTransferUnion, hunion]
    exact Finset.subset_union_left
  have hkSub : edgeComponent ends (rowClass m c 1) k ⊆
      canonicalTransferUnion ends m k zero c := by
    rw [canonicalTransferUnion, hunion]
    exact Finset.subset_union_right
  rcases hi with hi0 | hi1
  · right
    rw [edgeComponent, Finset.mem_filter] at hi0
    exact connK_mono hzeroSub
      (connK_edgeComponent_of_conn_cut ends _ zero x (hi0.2 x hx))
  · left
    rw [edgeComponent, Finset.mem_filter] at hi1
    exact connK_mono hkSub
      (connK_edgeComponent_of_conn_cut ends _ k x (hi1.2 x hx))




theorem exists_twoRootSpanning_crossing_edge_of_mem_sdiff_edgeComponent
    (ends : I -> Sym2 W) (K T : Finset I) (k zero : W)
    (hkzero : connK ends K k zero)
    (hT : TwoRootSpanning ends T k zero)
    {i : I} (hi : i ∈ K \ edgeComponent ends K zero)
    (hiT : i ∈ T) :
    ∃ e, e ∈ T \ K ∧
      ∃ a b, a ∈ ends e ∧ b ∈ ends e ∧
        a ∉ StatMech.FrontierA.grahamComponentComplement ends K zero ∧
        b ∈ StatMech.FrontierA.grahamComponentComplement ends K zero := by
  let S := StatMech.FrontierA.grahamComponentComplement ends K zero
  let x := (ends i).out.1
  have hxend : x ∈ ends i := Sym2.out_fst_mem (ends i)
  have hxS : x ∈ S := by
    exact ((mem_sdiff_edgeComponent_iff_edgeInside_componentComplement
      ends K zero).mp hi).2 x hxend
  have hcross : NoCrossingK ends K S := by
    exact StatMech.FrontierA.grahamComponentComplement_noCrossing
      ends K zero
  have hzeroS : zero ∉ S :=
    StatMech.FrontierA.grahamComponentComplement_not_mem ends K zero
  have hkS : k ∉ S :=
    connK_not_mem_of_noCrossing hcross hzeroS
      (connK_symm ends K hkzero)
  rcases hT i hiT x hxend with hkx | hzerox
  · exact exists_crossing_edge_mem_sdiff_of_connK
      hcross hkS hxS hkx
  · exact exists_crossing_edge_mem_sdiff_of_connK
      hcross hzeroS hxS hzerox


theorem twoRootSpanning_union
    {ends : I -> Sym2 W} {A B : Finset I} {u v : W}
    (hA : TwoRootSpanning ends A u v)
    (hB : TwoRootSpanning ends B u v) :
    TwoRootSpanning ends (A ∪ B) u v := by
  intro i hi x hx
  rcases Finset.mem_union.mp hi with hiA | hiB
  · rcases hA i hiA x hx with h | h
    · exact Or.inl (connK_mono Finset.subset_union_left h)
    · exact Or.inr (connK_mono Finset.subset_union_left h)
  · rcases hB i hiB x hx with h | h
    · exact Or.inl (connK_mono Finset.subset_union_right h)
    · exact Or.inr (connK_mono Finset.subset_union_right h)



theorem rootSpanning_union_of_conn_of_twoRootSpanning
    {ends : I -> Sym2 W} {K S : Finset I} {u v : W}
    (hK : RootSpanning ends K u)
    (huv : connK ends K u v)
    (hS : TwoRootSpanning ends S u v) :
    RootSpanning ends (K ∪ S) u := by
  intro i hi x hx
  rcases Finset.mem_union.mp hi with hiK | hiS
  · exact connK_mono Finset.subset_union_left (hK i hiK x hx)
  · rcases hS i hiS x hx with hux | hvx
    · exact connK_mono Finset.subset_union_right hux
    · exact (connK_mono Finset.subset_union_left huv).trans
        (connK_mono Finset.subset_union_right hvx)



theorem edgeComponent_rootSpanning
    (ends : I -> Sym2 W) (K : Finset I) (u : W) :
    RootSpanning ends (edgeComponent ends K u) u := by
  classical
  intro i hi x hx
  rw [edgeComponent, Finset.mem_filter] at hi
  exact connK_edgeComponent_of_conn_cut ends K u x (hi.2 x hx)





theorem subset_edgeComponent_of_subset_of_rootSpanning_union
    (ends : I -> Sym2 W) (K D : Finset I) (u : W)
    (hDK : D ⊆ K)
    (hroot : RootSpanning ends (edgeComponent ends K u ∪ D) u) :
    D ⊆ edgeComponent ends K u := by
  classical
  have hcompK : edgeComponent ends K u ⊆ K := by
    intro i hi
    rw [edgeComponent, Finset.mem_filter] at hi
    exact hi.1
  have hunionK : edgeComponent ends K u ∪ D ⊆ K :=
    Finset.union_subset hcompK hDK
  intro i hiD
  rw [edgeComponent, Finset.mem_filter]
  refine ⟨hDK hiD, ?_⟩
  intro x hx
  exact connK_mono hunionK
    (hroot i (Finset.mem_union_right _ hiD) x hx)





theorem rootSpanning_union_of_edgeComponents_meet
    (ends : I -> Sym2 W) (E D : Finset I) (u : W)
    (hE : RootSpanning ends E u)
    (hmeet : ∀ i ∈ D, ∀ x ∈ ends i,
      ∃ e ∈ D ∩ E, ∃ y ∈ ends e, connK ends D x y) :
    RootSpanning ends (E ∪ D) u := by
  intro i hi x hx
  rcases Finset.mem_union.mp hi with hiE | hiD
  · exact connK_mono Finset.subset_union_left (hE i hiE x hx)
  · obtain ⟨e, he, y, hy, hxy⟩ := hmeet i hiD x hx
    have heE : e ∈ E := (Finset.mem_inter.mp he).2
    have huy : connK ends E u y := hE e heE y hy
    exact (connK_mono Finset.subset_union_left huy).trans
      (connK_mono Finset.subset_union_right
        (connK_symm ends D hxy))



theorem subset_edgeComponent_of_subset_of_edgeComponents_meet
    (ends : I -> Sym2 W) (K D : Finset I) (u : W)
    (hDK : D ⊆ K)
    (hmeet : ∀ i ∈ D, ∀ x ∈ ends i,
      ∃ e ∈ D ∩ edgeComponent ends K u,
        ∃ y ∈ ends e, connK ends D x y) :
    D ⊆ edgeComponent ends K u := by
  apply subset_edgeComponent_of_subset_of_rootSpanning_union
    ends K D u hDK
  exact rootSpanning_union_of_edgeComponents_meet ends
    (edgeComponent ends K u) D u
      (edgeComponent_rootSpanning ends K u) hmeet



def EveryEdgeComponentMeets
    (ends : I -> Sym2 W) (D E : Finset I) : Prop :=
  ∀ i ∈ D,
    (edgeComponent ends D (ends i).out.1 ∩ E).Nonempty



theorem rootSpanning_union_of_everyEdgeComponentMeets
    (ends : I -> Sym2 W) (E D : Finset I) (u : W)
    (hE : RootSpanning ends E u)
    (hmeet : EveryEdgeComponentMeets ends D E) :
    RootSpanning ends (E ∪ D) u := by
  classical
  apply rootSpanning_union_of_edgeComponents_meet ends E D u hE
  intro i hiD x hx
  obtain ⟨e, he⟩ := hmeet i hiD
  have he' := Finset.mem_inter.mp he
  have heComp : e ∈ edgeComponent ends D (ends i).out.1 := he'.1
  have heE : e ∈ E := he'.2
  let r := (ends i).out.1
  have hr : r ∈ ends i := Sym2.out_fst_mem (ends i)
  have hiComp : i ∈ edgeComponent ends D r :=
    mem_edgeComponent_of_endpoint hiD hr
  have hrx : connK ends D r x := by
    rw [edgeComponent, Finset.mem_filter] at hiComp
    exact hiComp.2 x hx
  obtain ⟨⟨a, b⟩, hab⟩ := (ends e).exists_rep
  have ha : a ∈ ends e := hab ▸ Sym2.mem_mk_left a b
  have hry : connK ends D r a := by
    rw [edgeComponent, Finset.mem_filter] at heComp
    exact heComp.2 a ha
  exact ⟨e, Finset.mem_inter.mpr ⟨
    (by
      rw [edgeComponent, Finset.mem_filter] at heComp
      exact heComp.1), heE⟩,
    a, ha, (connK_symm ends D hrx).trans hry⟩



theorem subset_edgeComponent_of_subset_of_everyEdgeComponentMeets
    (ends : I -> Sym2 W) (K D : Finset I) (u : W)
    (hDK : D ⊆ K)
    (hmeet : EveryEdgeComponentMeets ends D
      (edgeComponent ends K u)) :
    D ⊆ edgeComponent ends K u := by
  apply subset_edgeComponent_of_subset_of_rootSpanning_union
    ends K D u hDK
  exact rootSpanning_union_of_everyEdgeComponentMeets ends
    (edgeComponent ends K u) D u
      (edgeComponent_rootSpanning ends K u) hmeet




theorem everyEdgeComponentMeets_edgeComponent_iff_subset
    (ends : I -> Sym2 W) (K D : Finset I) (u : W)
    (hDK : D ⊆ K) :
    EveryEdgeComponentMeets ends D (edgeComponent ends K u) ↔
      D ⊆ edgeComponent ends K u := by
  classical
  constructor
  · exact subset_edgeComponent_of_subset_of_everyEdgeComponentMeets
      ends K D u hDK
  · intro hD i hiD
    refine ⟨i, Finset.mem_inter.mpr ⟨?_, hD hiD⟩⟩
    exact mem_edgeComponent_of_endpoint hiD
      (Sym2.out_fst_mem (ends i))



theorem mem_canonicalNormalRow_iff
    (ends : I -> Sym2 W) (m : Finset I) (k zero : W)
    (c : ↑m -> Fin 4) (i : I) :
    i ∈ canonicalNormalRow ends m k zero c ↔
      (i ∈ rowClass m c 0 ∧
          i ∉ canonicalTransferUnion ends m k zero c) ∨
        (i ∈ canonicalTransferUnion ends m k zero c ∧
          i ∉ rowClass m c 0) := by
  classical
  simp only [canonicalNormalRow, Finset.mem_symmDiff]


theorem canonicalNormalRow_eq_rowClass_selfSwap
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l)
    {c : ↑m -> Fin 4}
    (hc : LeftPattern ends m {j, k} {k, l} k zero c) :
    canonicalNormalRow ends m k zero c =
      rowClass m
        (balancedSwap m
          (canonicalMiddleTransfer ends m c k zero)
          (canonicalOuterTransfer ends m c k zero) c) 0 := by
  have hv := canonicalTransfers_valid hloop hjk hkl hc
  rw [canonicalNormalRow,
    rowClass_balancedSwap_zero hv.1 hv.2.1,
    canonicalTransferUnion]


theorem canonicalNormalRow_no_incident_zero
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l)
    {c : ↑m -> Fin 4}
    (hc : LeftPattern ends m {j, k} {k, l} k zero c) :
    ∀ i ∈ canonicalNormalRow ends m k zero c, zero ∉ ends i := by
  let d := balancedSwap m
    (canonicalMiddleTransfer ends m c k zero)
    (canonicalOuterTransfer ends m c k zero) c
  have hrows := canonicalBalancedSwap_rows hloop hjk hkl hc
  rw [canonicalNormalRow_eq_rowClass_selfSwap hloop hjk hkl hc,
    hrows.1]
  exact exchangeFirstRow_no_incident_zero hc.2.2.2.2.2


theorem mem_canonicalNormalRow_of_mem_k
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l)
    {c : ↑m -> Fin 4}
    (hc : LeftPattern ends m {j, k} {k, l} k zero c)
    {i : I} (him : i ∈ m) (hik : k ∈ ends i) :
    i ∈ canonicalNormalRow ends m k zero c := by
  let d := balancedSwap m
    (canonicalMiddleTransfer ends m c k zero)
    (canonicalOuterTransfer ends m c k zero) c
  have hrows := canonicalBalancedSwap_rows hloop hjk hkl hc
  have hnotSecond : i ∉ rowClass m d 1 := by
    rw [hrows.2]
    intro hiSecond
    exact exchangeSecondRow_no_incident_k hc.2.2.2.2.1
      i hiSecond hik
  rw [canonicalNormalRow_eq_rowClass_selfSwap hloop hjk hkl hc]
  rw [rowClass_one_eq_sdiff, Finset.mem_sdiff] at hnotSecond
  exact Classical.byContradiction fun hi => hnotSecond ⟨him, hi⟩

private theorem union_pair_symmDiff_eq_union_symmDiff
    {A B C D M O : Finset I}
    (hAM : A ⊆ M) (hBM : B ⊆ M)
    (hCO : C ⊆ O) (hDO : D ⊆ O)
    (hMO : Disjoint M O) :
    (A ∆ B) ∪ (C ∆ D) = (A ∪ C) ∆ (B ∪ D) := by
  classical
  ext i
  have hAC : i ∈ A -> i ∈ C -> False := fun hiA hiC =>
    (Finset.disjoint_left.mp hMO) (hAM hiA) (hCO hiC)
  have hAD : i ∈ A -> i ∈ D -> False := fun hiA hiD =>
    (Finset.disjoint_left.mp hMO) (hAM hiA) (hDO hiD)
  have hBC : i ∈ B -> i ∈ C -> False := fun hiB hiC =>
    (Finset.disjoint_left.mp hMO) (hBM hiB) (hCO hiC)
  have hBD : i ∈ B -> i ∈ D -> False := fun hiB hiD =>
    (Finset.disjoint_left.mp hMO) (hBM hiB) (hDO hiD)
  simp only [Finset.mem_union, Finset.mem_symmDiff]
  tauto

private theorem sdiff_symmDiff_symmDiff
    {A B C m : Finset I} (hA : A ⊆ m) (hB : B ⊆ m) (hC : C ⊆ m) :
    m \ (A ∆ B ∆ C) = (m \ A) ∆ B ∆ C := by
  classical
  ext i
  by_cases him : i ∈ m
  · by_cases hiA : i ∈ A <;>
      by_cases hiB : i ∈ B <;>
      by_cases hiC : i ∈ C <;>
      simp [Finset.mem_sdiff, Finset.mem_symmDiff,
        him, hiA, hiB, hiC]
  · have hiA : i ∉ A := fun hi => him (hA hi)
    have hiB : i ∉ B := fun hi => him (hB hi)
    have hiC : i ∉ C := fun hi => him (hC hi)
    simp [Finset.mem_sdiff, Finset.mem_symmDiff,
      him, hiA, hiB, hiC]



theorem rowClass_canonicalQuadrangleCompletion_zero
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l)
    {p : Finset I × Finset I}
    (a b c : leftMaskFiber ends m j k l zero p) :
    rowClass m
        (canonicalQuadrangleCompletion ends m k zero
          a.1.1 b.1.1 c.1.1) 0 =
      rowClass m c.1.1 0 ∆
        canonicalTransferUnion ends m k zero a.1.1 ∆
        canonicalTransferUnion ends m k zero b.1.1 := by
  let Xa := canonicalMiddleTransfer ends m a.1.1 k zero
  let Xb := canonicalMiddleTransfer ends m b.1.1 k zero
  let Ya := canonicalOuterTransfer ends m a.1.1 k zero
  let Yb := canonicalOuterTransfer ends m b.1.1 k zero
  have hva := canonicalTransfers_valid_on_sameMask hloop hjk hkl a c
  have hvb := canonicalTransfers_valid_on_sameMask hloop hjk hkl b c
  have hX : Xa ∆ Xb ⊆ colorClass m c.1.1 1 ∪
      colorClass m c.1.1 2 := by
    intro i hi
    rcases Finset.mem_symmDiff.mp hi with hi | hi
    · exact hva.1 hi.1
    · exact hvb.1 hi.1
  have hY : Ya ∆ Yb ⊆ colorClass m c.1.1 0 ∪
      colorClass m c.1.1 3 := by
    intro i hi
    rcases Finset.mem_symmDiff.mp hi with hi | hi
    · exact hva.2.1 hi.1
    · exact hvb.2.1 hi.1
  have hunion : (Xa ∆ Xb) ∪ (Ya ∆ Yb) =
      (Xa ∪ Ya) ∆ (Xb ∪ Yb) :=
    union_pair_symmDiff_eq_union_symmDiff
      (by simpa only [Xa, middleMask] using hva.1)
      (by simpa only [Xb, middleMask] using hvb.1)
      (by simpa only [Ya, outerMask] using hva.2.1)
      (by simpa only [Yb, outerMask] using hvb.2.1)
      (middleMask_disjoint_outerMask m c.1.1)
  rw [canonicalQuadrangleCompletion]
  change rowClass m (balancedSwap m (Xa ∆ Xb) (Ya ∆ Yb) c.1.1) 0 = _
  rw [rowClass_balancedSwap_zero hX hY]
  rw [hunion]
  dsimp only [canonicalTransferUnion, Xa, Xb, Ya, Yb]
  rw [symmDiff_assoc]


theorem rowClass_canonicalQuadrangleCompletion_one
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l)
    {p : Finset I × Finset I}
    (a b c : leftMaskFiber ends m j k l zero p) :
    rowClass m
        (canonicalQuadrangleCompletion ends m k zero
          a.1.1 b.1.1 c.1.1) 1 =
      rowClass m c.1.1 1 ∆
        canonicalTransferUnion ends m k zero a.1.1 ∆
        canonicalTransferUnion ends m k zero b.1.1 := by
  classical
  have hTa : canonicalTransferUnion ends m k zero a.1.1 ⊆ m :=
    canonicalTransferUnion_subset_m
    hloop hjk hkl a
  have hTb : canonicalTransferUnion ends m k zero b.1.1 ⊆ m :=
    canonicalTransferUnion_subset_m
    hloop hjk hkl b
  have hzero := rowClass_canonicalQuadrangleCompletion_zero
    hloop hjk hkl a b c
  rw [rowClass_one_eq_sdiff, hzero, rowClass_one_eq_sdiff]
  apply sdiff_symmDiff_symmDiff
  · intro i hi
    rw [rowClass_zero] at hi
    rcases Finset.mem_union.mp hi with hi | hi
    · exact colorClass_subset m c.1.1 0 hi
    · exact colorClass_subset m c.1.1 1 hi
  · exact hTa
  · exact hTb




theorem rowClass_canonicalQuadrangleCompletion
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l)
    {p : Finset I × Finset I}
    (a b c : leftMaskFiber ends m j k l zero p) (rho : Fin 2) :
    rowClass m
        (canonicalQuadrangleCompletion ends m k zero
          a.1.1 b.1.1 c.1.1) rho =
      rowClass m c.1.1 rho ∆
        canonicalTransferUnion ends m k zero a.1.1 ∆
        canonicalTransferUnion ends m k zero b.1.1 := by
  fin_cases rho
  · exact rowClass_canonicalQuadrangleCompletion_zero
      hloop hjk hkl a b c
  · exact rowClass_canonicalQuadrangleCompletion_one
      hloop hjk hkl a b c





theorem canonicalTranslatedRow_quadrangleCompletion
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l)
    {p : Finset I × Finset I}
    (a b c : leftMaskFiber ends m j k l zero p) :
    canonicalTranslatedRow ends m k zero a.1.1 c.1.1 =
      canonicalTranslatedRow ends m k zero b.1.1
        (canonicalQuadrangleCompletion ends m k zero
          a.1.1 b.1.1 c.1.1) := by
  classical
  unfold canonicalTranslatedRow
  rw [rowClass_canonicalQuadrangleCompletion_zero
    hloop hjk hkl a b c]
  exact (symmDiff_symmDiff_cancel_right
    (canonicalTransferUnion ends m k zero b.1.1)
    (rowClass m c.1.1 0 ∆
      canonicalTransferUnion ends m k zero a.1.1)).symm

private theorem mem_iff_mem_symmDiff_of_not_mem_threefold
    (C A B : Finset I) (i : I) (hi : i ∉ C ∆ A ∆ B) :
    (i ∈ C ↔ i ∈ A ∆ B) := by
  classical
  simp only [Finset.mem_symmDiff] at hi ⊢
  tauto





theorem rowClass_pair_parity_of_not_mem_canonicalQuadrangleCompletion
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l)
    {p : Finset I × Finset I}
    (a b c : leftMaskFiber ends m j k l zero p) (rho : Fin 2)
    {i : I}
    (hi : i ∉ rowClass m
      (canonicalQuadrangleCompletion ends m k zero
        a.1.1 b.1.1 c.1.1) rho) :
    (i ∈ rowClass m c.1.1 rho) ↔
      i ∈ canonicalTransferUnion ends m k zero a.1.1 ∆
        canonicalTransferUnion ends m k zero b.1.1 := by
  have hrow := rowClass_canonicalQuadrangleCompletion
    hloop hjk hkl a b c rho
  apply mem_iff_mem_symmDiff_of_not_mem_threefold
  rwa [← hrow]



theorem fourfold_symmDiff_subset_union
    (A B C D : Finset I) :
    A ∆ B ∆ C ∆ D ⊆ ((A ∪ B) ∪ C) ∪ D := by
  classical
  intro i hi
  simp only [Finset.mem_symmDiff, Finset.mem_union] at hi ⊢
  tauto





theorem exists_other_mem_of_mem_of_not_mem_fourfold
    (A B C D : Finset I) (i : I)
    (hiA : i ∈ A) (hnot : i ∉ A ∆ B ∆ C ∆ D) :
    i ∈ B ∨ i ∈ C ∨ i ∈ D := by
  classical
  by_contra hother
  have hiB : i ∉ B := fun hi => hother (Or.inl hi)
  have hiC : i ∉ C := fun hi => hother (Or.inr (Or.inl hi))
  have hiD : i ∉ D := fun hi => hother (Or.inr (Or.inr hi))
  apply hnot
  simp [Finset.mem_symmDiff, hiA, hiB, hiC, hiD]


def AtLeastTwoOfFour (A B C D : Finset I) (i : I) : Prop :=
  (i ∈ A ∧ i ∈ B) ∨ (i ∈ A ∧ i ∈ C) ∨
    (i ∈ A ∧ i ∈ D) ∨ (i ∈ B ∧ i ∈ C) ∨
    (i ∈ B ∧ i ∈ D) ∨ (i ∈ C ∧ i ∈ D)



theorem atLeastTwoOfFour_of_mem_union_of_not_mem_symmDiff
    (A B C D : Finset I) (i : I)
    (hi : i ∈ ((A ∪ B) ∪ C) ∪ D)
    (hnot : i ∉ A ∆ B ∆ C ∆ D) :
    AtLeastTwoOfFour A B C D i := by
  classical
  simp only [AtLeastTwoOfFour, Finset.mem_union,
    Finset.mem_symmDiff] at hi hnot ⊢
  tauto



theorem four_canonicalTransferUnion_twoRootSpanning
    (ends : I -> Sym2 W) (m : Finset I) (k zero : W)
    (a b c d : ↑m -> Fin 4) :
    TwoRootSpanning ends
      (((canonicalTransferUnion ends m k zero a ∪
          canonicalTransferUnion ends m k zero b) ∪
        canonicalTransferUnion ends m k zero c) ∪
        canonicalTransferUnion ends m k zero d) k zero := by
  exact twoRootSpanning_union
    (twoRootSpanning_union
      (twoRootSpanning_union
        (canonicalTransferUnion_twoRootSpanning ends m k zero a)
        (canonicalTransferUnion_twoRootSpanning ends m k zero b))
      (canonicalTransferUnion_twoRootSpanning ends m k zero c))
    (canonicalTransferUnion_twoRootSpanning ends m k zero d)





theorem exists_two_canonicalTransfers_at_failedCutCrossing
    (ends : I -> Sym2 W) (m K : Finset I) (k zero : W)
    (r s x y : ↑m -> Fin 4)
    (hkzero : connK ends K k zero)
    (hD : canonicalTransferUnion ends m k zero r ∆
        canonicalTransferUnion ends m k zero s ∆
        canonicalTransferUnion ends m k zero x ∆
        canonicalTransferUnion ends m k zero y ⊆ K)
    {i : I}
    (hi : i ∈ (canonicalTransferUnion ends m k zero r ∆
        canonicalTransferUnion ends m k zero s ∆
        canonicalTransferUnion ends m k zero x ∆
        canonicalTransferUnion ends m k zero y) \
      edgeComponent ends K zero) :
    ∃ e,
      e ∈ (((canonicalTransferUnion ends m k zero r ∪
          canonicalTransferUnion ends m k zero s) ∪
        canonicalTransferUnion ends m k zero x) ∪
        canonicalTransferUnion ends m k zero y) \ K ∧
      (∃ a b, a ∈ ends e ∧ b ∈ ends e ∧
        a ∉ StatMech.FrontierA.grahamComponentComplement ends K zero ∧
        b ∈ StatMech.FrontierA.grahamComponentComplement ends K zero) ∧
      AtLeastTwoOfFour
        (canonicalTransferUnion ends m k zero r)
        (canonicalTransferUnion ends m k zero s)
        (canonicalTransferUnion ends m k zero x)
        (canonicalTransferUnion ends m k zero y) e := by
  have hi' := Finset.mem_sdiff.mp hi
  have hiK : i ∈ K \ edgeComponent ends K zero :=
    Finset.mem_sdiff.mpr ⟨hD hi'.1, hi'.2⟩
  have hiUnion : i ∈
      ((canonicalTransferUnion ends m k zero r ∪
          canonicalTransferUnion ends m k zero s) ∪
        canonicalTransferUnion ends m k zero x) ∪
        canonicalTransferUnion ends m k zero y :=
    fourfold_symmDiff_subset_union
      (canonicalTransferUnion ends m k zero r)
      (canonicalTransferUnion ends m k zero s)
      (canonicalTransferUnion ends m k zero x)
      (canonicalTransferUnion ends m k zero y) hi'.1
  obtain ⟨e, he, hcut⟩ :=
    exists_twoRootSpanning_crossing_edge_of_mem_sdiff_edgeComponent
      ends K
        (((canonicalTransferUnion ends m k zero r ∪
            canonicalTransferUnion ends m k zero s) ∪
          canonicalTransferUnion ends m k zero x) ∪
          canonicalTransferUnion ends m k zero y)
        k zero hkzero
        (four_canonicalTransferUnion_twoRootSpanning
          ends m k zero r s x y)
        hiK hiUnion
  have he' := Finset.mem_sdiff.mp he
  have heNotD : e ∉ canonicalTransferUnion ends m k zero r ∆
      canonicalTransferUnion ends m k zero s ∆
      canonicalTransferUnion ends m k zero x ∆
      canonicalTransferUnion ends m k zero y :=
    fun heD => he'.2 (hD heD)
  exact ⟨e, he, hcut,
    atLeastTwoOfFour_of_mem_union_of_not_mem_symmDiff
      (canonicalTransferUnion ends m k zero r)
      (canonicalTransferUnion ends m k zero s)
      (canonicalTransferUnion ends m k zero x)
      (canonicalTransferUnion ends m k zero y)
      e he'.1 heNotD⟩





theorem exists_second_canonicalTransfer_at_failedCutCrossing
    (ends : I -> Sym2 W) (m K : Finset I) (k zero : W)
    (r s x y : ↑m -> Fin 4)
    (hkzero : connK ends K k zero)
    (hD : canonicalTransferUnion ends m k zero r ∆
        canonicalTransferUnion ends m k zero s ∆
        canonicalTransferUnion ends m k zero x ∆
        canonicalTransferUnion ends m k zero y ⊆ K)
    {i : I} (hi : i ∈ K \ edgeComponent ends K zero)
    (hir : i ∈ canonicalTransferUnion ends m k zero r) :
    ∃ e,
      e ∈ canonicalTransferUnion ends m k zero r \ K ∧
      (∃ a b, a ∈ ends e ∧ b ∈ ends e ∧
        a ∉ StatMech.FrontierA.grahamComponentComplement ends K zero ∧
        b ∈ StatMech.FrontierA.grahamComponentComplement ends K zero) ∧
      (e ∈ canonicalTransferUnion ends m k zero s ∨
        e ∈ canonicalTransferUnion ends m k zero x ∨
        e ∈ canonicalTransferUnion ends m k zero y) := by
  obtain ⟨e, he, hcut⟩ :=
    exists_twoRootSpanning_crossing_edge_of_mem_sdiff_edgeComponent
      ends K (canonicalTransferUnion ends m k zero r) k zero
        hkzero
        (canonicalTransferUnion_twoRootSpanning ends m k zero r)
        hi hir
  have he' := Finset.mem_sdiff.mp he
  have heNotD : e ∉ canonicalTransferUnion ends m k zero r ∆
      canonicalTransferUnion ends m k zero s ∆
      canonicalTransferUnion ends m k zero x ∆
      canonicalTransferUnion ends m k zero y := by
    intro heD
    exact he'.2 (hD heD)
  exact ⟨e, he, hcut,
    exists_other_mem_of_mem_of_not_mem_fourfold
      (canonicalTransferUnion ends m k zero r)
      (canonicalTransferUnion ends m k zero s)
      (canonicalTransferUnion ends m k zero x)
      (canonicalTransferUnion ends m k zero y)
      e he'.1 heNotD⟩






theorem canonicalNormalRow_symmDiff_eq_of_translatedRow_eq
    (ends : I -> Sym2 W) (m : Finset I) (k zero : W)
    (r s x y : ↑m -> Fin 4)
    (hxy : canonicalTranslatedRow ends m k zero r x =
      canonicalTranslatedRow ends m k zero s y) :
    canonicalNormalRow ends m k zero x ∆
        canonicalNormalRow ends m k zero y =
      canonicalTransferUnion ends m k zero r ∆
        canonicalTransferUnion ends m k zero s ∆
        canonicalTransferUnion ends m k zero x ∆
        canonicalTransferUnion ends m k zero y := by
  have hrow := rowSymmDiff_eq_transferSymmDiff_of_translatedRow_eq
    r s x y hxy
  unfold canonicalNormalRow
  calc
    (rowClass m x 0 ∆ canonicalTransferUnion ends m k zero x) ∆
          (rowClass m y 0 ∆ canonicalTransferUnion ends m k zero y) =
        (rowClass m x 0 ∆ rowClass m y 0) ∆
          (canonicalTransferUnion ends m k zero x ∆
            canonicalTransferUnion ends m k zero y) := by ac_rfl
    _ = (canonicalTransferUnion ends m k zero r ∆
          canonicalTransferUnion ends m k zero s) ∆
        (canonicalTransferUnion ends m k zero x ∆
          canonicalTransferUnion ends m k zero y) := by rw [hrow]
    _ = canonicalTransferUnion ends m k zero r ∆
        canonicalTransferUnion ends m k zero s ∆
        canonicalTransferUnion ends m k zero x ∆
        canonicalTransferUnion ends m k zero y := by ac_rfl




theorem canonicalNormalRow_symmDiff_eq_pairDifferences_of_translatedRow_eq
    (ends : I -> Sym2 W) (m : Finset I) (k zero : W)
    (r s x y : ↑m -> Fin 4)
    (hxy : canonicalTranslatedRow ends m k zero r x =
      canonicalTranslatedRow ends m k zero s y) :
    canonicalNormalRow ends m k zero x ∆
        canonicalNormalRow ends m k zero y =
      (canonicalTransferUnion ends m k zero r ∆
        canonicalTransferUnion ends m k zero x) ∆
      (canonicalTransferUnion ends m k zero s ∆
        canonicalTransferUnion ends m k zero y) := by
  rw [canonicalNormalRow_symmDiff_eq_of_translatedRow_eq
    ends m k zero r s x y hxy]
  ac_rfl





theorem canonicalQuadrangleCompletion_normalRowDiscrepancy
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l)
    {p : Finset I × Finset I}
    (a b c : leftMaskFiber ends m j k l zero p) :
    let d := canonicalQuadrangleCompletion ends m k zero
      a.1.1 b.1.1 c.1.1
    canonicalNormalRow ends m k zero c.1.1 ∆
        canonicalNormalRow ends m k zero d =
      canonicalTransferUnion ends m k zero a.1.1 ∆
        canonicalTransferUnion ends m k zero b.1.1 ∆
        canonicalTransferUnion ends m k zero c.1.1 ∆
        canonicalTransferUnion ends m k zero d := by
  dsimp only
  exact canonicalNormalRow_symmDiff_eq_of_translatedRow_eq
    ends m k zero a.1.1 b.1.1 c.1.1
      (canonicalQuadrangleCompletion ends m k zero
        a.1.1 b.1.1 c.1.1)
      (canonicalTranslatedRow_quadrangleCompletion
        hloop hjk hkl a b c)

private theorem mem_threefold_of_mem_fourfold_of_not_mem_fourth
    (A B C D : Finset I) {i : I}
    (hi : i ∈ A ∆ B ∆ C ∆ D) (hiD : i ∉ D) :
    i ∈ A ∆ B ∆ C := by
  classical
  simp only [Finset.mem_symmDiff] at hi ⊢
  tauto





theorem canonicalQuadrangleCompletion_nonrootRowZero_discrepancy_threeLabels
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l)
    {p : Finset I × Finset I}
    (a b c : leftMaskFiber ends m j k l zero p)
    {i : I}
    (hiD : i ∈ canonicalNormalRow ends m k zero c.1.1 ∆
      canonicalNormalRow ends m k zero
        (canonicalQuadrangleCompletion ends m k zero
          a.1.1 b.1.1 c.1.1))
    (hiK : i ∈ rowClass m
        (canonicalQuadrangleCompletion ends m k zero
          a.1.1 b.1.1 c.1.1) 0 \
      edgeComponent ends
        (rowClass m
          (canonicalQuadrangleCompletion ends m k zero
            a.1.1 b.1.1 c.1.1) 0) zero) :
    i ∈ canonicalTransferUnion ends m k zero a.1.1 ∆
      canonicalTransferUnion ends m k zero b.1.1 ∆
      canonicalTransferUnion ends m k zero c.1.1 := by
  classical
  have hfour := hiD
  rw [canonicalQuadrangleCompletion_normalRowDiscrepancy
    hloop hjk hkl a b c] at hfour
  have hnot : i ∉ canonicalTransferUnion ends m k zero
      (canonicalQuadrangleCompletion ends m k zero
        a.1.1 b.1.1 c.1.1) := by
    intro hiT
    exact (Finset.disjoint_left.mp
      (canonicalTransferUnion_disjoint_nonrootRowZero
        ends m k zero
          (canonicalQuadrangleCompletion ends m k zero
            a.1.1 b.1.1 c.1.1))) hiT hiK
  exact mem_threefold_of_mem_fourfold_of_not_mem_fourth
    _ _ _ _ hfour hnot



theorem canonicalQuadrangleCompletion_nonrootRowOne_discrepancy_threeLabels
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l)
    {p : Finset I × Finset I}
    (a b c : leftMaskFiber ends m j k l zero p)
    {i : I}
    (hiD : i ∈ canonicalNormalRow ends m k zero c.1.1 ∆
      canonicalNormalRow ends m k zero
        (canonicalQuadrangleCompletion ends m k zero
          a.1.1 b.1.1 c.1.1))
    (hiK : i ∈ rowClass m
        (canonicalQuadrangleCompletion ends m k zero
          a.1.1 b.1.1 c.1.1) 1 \
      edgeComponent ends
        (rowClass m
          (canonicalQuadrangleCompletion ends m k zero
            a.1.1 b.1.1 c.1.1) 1) k) :
    i ∈ canonicalTransferUnion ends m k zero a.1.1 ∆
      canonicalTransferUnion ends m k zero b.1.1 ∆
      canonicalTransferUnion ends m k zero c.1.1 := by
  classical
  have hfour := hiD
  rw [canonicalQuadrangleCompletion_normalRowDiscrepancy
    hloop hjk hkl a b c] at hfour
  have hnot : i ∉ canonicalTransferUnion ends m k zero
      (canonicalQuadrangleCompletion ends m k zero
        a.1.1 b.1.1 c.1.1) := by
    intro hiT
    exact (Finset.disjoint_left.mp
      (canonicalTransferUnion_disjoint_nonrootRowOne
        ends m k zero
          (canonicalQuadrangleCompletion ends m k zero
            a.1.1 b.1.1 c.1.1))) hiT hiK
  exact mem_threefold_of_mem_fourfold_of_not_mem_fourth
    _ _ _ _ hfour hnot





theorem canonicalTransferPairDifference_eq_translatedRow_symmDiff_normalRow
    (ends : I -> Sym2 W) (m : Finset I) (k zero : W)
    (r x : ↑m -> Fin 4) :
    canonicalTransferUnion ends m k zero r ∆
        canonicalTransferUnion ends m k zero x =
      canonicalTranslatedRow ends m k zero r x ∆
        canonicalNormalRow ends m k zero x := by
  unfold canonicalTranslatedRow canonicalNormalRow
  symm
  calc
    (rowClass m x 0 ∆ canonicalTransferUnion ends m k zero r) ∆
          (rowClass m x 0 ∆ canonicalTransferUnion ends m k zero x) =
        (rowClass m x 0 ∆ rowClass m x 0) ∆
          (canonicalTransferUnion ends m k zero r ∆
            canonicalTransferUnion ends m k zero x) := by ac_rfl
    _ = canonicalTransferUnion ends m k zero r ∆
        canonicalTransferUnion ends m k zero x := by simp





theorem canonicalNormalRow_sdiff_eq_of_component_meets
    (ends : I -> Sym2 W) (m : Finset I) (k zero : W)
    (K : Finset I) (x y : ↑m -> Fin 4)
    (hrow : canonicalNormalRow ends m k zero x ∆
        canonicalNormalRow ends m k zero y ⊆ K)
    (hmeet : EveryEdgeComponentMeets ends
      (canonicalNormalRow ends m k zero x ∆
        canonicalNormalRow ends m k zero y)
      (edgeComponent ends K zero)) :
    canonicalNormalRow ends m k zero x \
        edgeComponent ends K zero =
      canonicalNormalRow ends m k zero y \
        edgeComponent ends K zero := by
  have hcomponent : canonicalNormalRow ends m k zero x ∆
      canonicalNormalRow ends m k zero y ⊆
        edgeComponent ends K zero :=
    subset_edgeComponent_of_subset_of_everyEdgeComponentMeets
      ends K
        (canonicalNormalRow ends m k zero x ∆
          canonicalNormalRow ends m k zero y)
        zero hrow hmeet
  classical
  ext i
  by_cases hiE : i ∈ edgeComponent ends K zero
  · simp [hiE]
  · have hnot : i ∉ canonicalNormalRow ends m k zero x ∆
        canonicalNormalRow ends m k zero y :=
      fun hi => hiE (hcomponent hi)
    by_cases hix : i ∈ canonicalNormalRow ends m k zero x <;>
      by_cases hiy : i ∈ canonicalNormalRow ends m k zero y <;>
      simp [Finset.mem_sdiff, Finset.mem_symmDiff,
        hiE, hix, hiy] at hnot ⊢

theorem not_mem_symmDiff_iff_mem_iff
    (A B : Finset I) (i : I) : i ∉ A ∆ B ↔ (i ∈ A ↔ i ∈ B) := by
  classical
  by_cases hiA : i ∈ A <;> by_cases hiB : i ∈ B <;>
    simp [Finset.mem_symmDiff, hiA, hiB]

set_option maxHeartbeats 1000000 in



theorem transfer_pair_parity_of_translatedRow_eq_of_root_incident
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    (hloop : ∀ e ∈ m, ¬ (ends e).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l)
    {p : Finset I × Finset I}
    (r s x y : leftMaskFiber ends m j k l zero p)
    (hrs : canonicalTranslatedRow ends m k zero r.1.1 x.1.1 =
      canonicalTranslatedRow ends m k zero s.1.1 y.1.1)
    {i : I} (him : i ∈ m) (hroot : k ∈ ends i ∨ zero ∈ ends i) :
    (i ∈ canonicalTransferUnion ends m k zero r.1.1 ∆
          canonicalTransferUnion ends m k zero s.1.1) ↔
      i ∈ canonicalTransferUnion ends m k zero x.1.1 ∆
        canonicalTransferUnion ends m k zero y.1.1 := by
  have hnormal := canonicalNormalRow_symmDiff_eq_of_translatedRow_eq
    ends m k zero r.1.1 s.1.1 x.1.1 y.1.1 hrs
  have hsame :
      (i ∈ canonicalNormalRow ends m k zero x.1.1) ↔
        i ∈ canonicalNormalRow ends m k zero y.1.1 := by
    rcases hroot with hik | hiz
    · exact iff_of_true
        (mem_canonicalNormalRow_of_mem_k hloop hjk hkl x.1.2 him hik)
        (mem_canonicalNormalRow_of_mem_k hloop hjk hkl y.1.2 him hik)
    · exact iff_of_false
        (fun hi => (canonicalNormalRow_no_incident_zero hloop hjk hkl
          x.1.2 i hi) hiz)
        (fun hi => (canonicalNormalRow_no_incident_zero hloop hjk hkl
          y.1.2 i hi) hiz)
  have hnot : i ∉ canonicalNormalRow ends m k zero x.1.1 ∆
      canonicalNormalRow ends m k zero y.1.1 :=
    (not_mem_symmDiff_iff_mem_iff _ _ i).mpr hsame
  rw [hnormal] at hnot
  have hgroup :
      canonicalTransferUnion ends m k zero r.1.1 ∆
          canonicalTransferUnion ends m k zero s.1.1 ∆
          canonicalTransferUnion ends m k zero x.1.1 ∆
          canonicalTransferUnion ends m k zero y.1.1 =
        (canonicalTransferUnion ends m k zero r.1.1 ∆
          canonicalTransferUnion ends m k zero s.1.1) ∆
        (canonicalTransferUnion ends m k zero x.1.1 ∆
          canonicalTransferUnion ends m k zero y.1.1) := by ac_rfl
  rw [hgroup] at hnot
  exact (not_mem_symmDiff_iff_mem_iff _ _ i).mp hnot


theorem transfer_pair_parity_of_not_mem_total
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    (hloop : ∀ e ∈ m, ¬ (ends e).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l)
    {p : Finset I × Finset I}
    (r s x y : leftMaskFiber ends m j k l zero p)
    {i : I} (him : i ∉ m) :
    (i ∈ canonicalTransferUnion ends m k zero r.1.1 ∆
          canonicalTransferUnion ends m k zero s.1.1) ↔
      i ∈ canonicalTransferUnion ends m k zero x.1.1 ∆
        canonicalTransferUnion ends m k zero y.1.1 := by
  have hr : i ∉ canonicalTransferUnion ends m k zero r.1.1 :=
    fun hi => him (canonicalTransferUnion_subset_m hloop hjk hkl r hi)
  have hs : i ∉ canonicalTransferUnion ends m k zero s.1.1 :=
    fun hi => him (canonicalTransferUnion_subset_m hloop hjk hkl s hi)
  have hx : i ∉ canonicalTransferUnion ends m k zero x.1.1 :=
    fun hi => him (canonicalTransferUnion_subset_m hloop hjk hkl x hi)
  have hy : i ∉ canonicalTransferUnion ends m k zero y.1.1 :=
    fun hi => him (canonicalTransferUnion_subset_m hloop hjk hkl y hi)
  simp [Finset.mem_symmDiff, hr, hs, hx, hy]



theorem exists_opposite_badQuadrangle_of_coverage_card_le
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    (hloop : ∀ e ∈ m, ¬ (ends e).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l)
    {p : Finset I × Finset I}
    (a b c : leftMaskFiber ends m j k l zero p)
    (hab : CanonicalMaskTransferOrbit ends m j k l zero p a b)
    (hc : c ∈ canonicalCoverageExclusiveBadQuadrangles
      ends m j k l zero p a b)
    (hcard : #(canonicalMaskOrbitCoverage ends m j k l zero p a) ≤
      #(canonicalMaskOrbitCoverage ends m j k l zero p b)) :
    ∃ d, d ∈ canonicalCoverageExclusiveBadQuadrangles
      ends m j k l zero p b a := by
  by_contra h
  have hempty : canonicalCoverageExclusiveBadQuadrangles
      ends m j k l zero p b a = ∅ := by
    exact Finset.eq_empty_iff_forall_notMem.mpr fun d hd => h ⟨d, hd⟩
  have hlt := coverage_card_lt_of_mem_bad_of_opposite_bad_eq_empty
    ends m j k l zero hloop hjk hkl p a b c hab hc hempty
  exact (Nat.not_lt_of_ge hcard) hlt





theorem canonicalCoverageExclusiveBadQuadrangle_typedData
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    (hloop : ∀ e ∈ m, ¬ (ends e).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l)
    {p : Finset I × Finset I}
    (a b c : leftMaskFiber ends m j k l zero p)
    (hab : CanonicalMaskTransferOrbit ends m j k l zero p a b)
    (hc : c ∈ canonicalCoverageExclusiveBadQuadrangles
      ends m j k l zero p a b) :
    let d := canonicalQuadrangleCompletion ends m k zero
      a.1.1 b.1.1 c.1.1
    CanonicalMaskTransferOrbit ends m j k l zero p a c ∧
      CanonicalMaskTransferOrbit ends m j k l zero p b c ∧
      CanonicalTransferWorks ends m k zero a.1.1 c.1.1 ∧
      ¬ CanonicalTransferWorks ends m k zero b.1.1 c.1.1 ∧
      CanonicalTransferWorks ends m k zero b.1.1 d ∧
      ((connK ends (rowClass m d 0) k zero ∧
          sources ends (edgeComponent ends (rowClass m d 0) zero) = {j, k} ∧
          sources ends (rowClass m d 0 \
            edgeComponent ends (rowClass m d 0) zero) = ∅ ∧
          Disjoint (canonicalTransferUnion ends m k zero d)
            (rowClass m d 0 \
              edgeComponent ends (rowClass m d 0) zero)) ∨
        (connK ends (rowClass m d 1) k zero ∧
          sources ends (edgeComponent ends (rowClass m d 1) k) = {k, l} ∧
          sources ends (rowClass m d 1 \
            edgeComponent ends (rowClass m d 1) k) = ∅ ∧
          Disjoint (canonicalTransferUnion ends m k zero d)
            (rowClass m d 1 \
              edgeComponent ends (rowClass m d 1) k))) := by
  dsimp only
  have hc' := (mem_canonicalCoverageExclusiveBadQuadrangles_iff
    ends m j k l zero p a b c).mp hc
  have hac := (mem_canonicalMaskOrbitCoverage_iff
    ends m j k l zero p a c).mp hc'.1
  have hbcOrbit : CanonicalMaskTransferOrbit
      ends m j k l zero p b c :=
    (canonicalMaskTransferOrbit_symm
      ends m j k l zero p hab).trans hac.1
  have hbc : ¬ CanonicalTransferWorks ends m k zero b.1.1 c.1.1 := by
    intro hworks
    exact hc'.2.1 ((mem_canonicalMaskOrbitCoverage_iff
      ends m j k l zero p b c).mpr ⟨hbcOrbit, hworks⟩)
  refine ⟨hac.1, hbcOrbit, hac.2, hbc,
    canonicalTransferWorks_quadrangleCompletion
      ends m k zero a.1.1 b.1.1 c.1.1 hac.2, ?_⟩
  rcases canonicalQuadrangleCompletion_failedGate_boundaryCertificate
      hloop hjk hkl a b c hc'.2.2 with hzero | hone
  · exact Or.inl ⟨hzero.1, hzero.2.1, hzero.2.2,
      canonicalTransferUnion_disjoint_nonrootRowZero
        ends m k zero _⟩
  · rcases hone with ⟨hconn, hsrc, hcompl⟩
    have heq : edgeComponent ends
        (rowClass m
          (canonicalQuadrangleCompletion ends m k zero
            a.1.1 b.1.1 c.1.1) 1) k =
      edgeComponent ends
        (rowClass m
          (canonicalQuadrangleCompletion ends m k zero
            a.1.1 b.1.1 c.1.1) 1) zero :=
      edgeComponent_eq_of_conn ends _ k zero hconn
    exact Or.inr ⟨hconn, (congrArg (sources ends) heq).trans hsrc,
      by rwa [heq],
      canonicalTransferUnion_disjoint_nonrootRowOne
        ends m k zero _⟩




theorem canonicalCoverageExclusiveBadQuadrangle_nonroot_noRootIncidence
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    (hloop : ∀ e ∈ m, ¬ (ends e).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l)
    {p : Finset I × Finset I}
    (a b c : leftMaskFiber ends m j k l zero p)
    (hc : c ∈ canonicalCoverageExclusiveBadQuadrangles
      ends m j k l zero p a b) :
    let d := canonicalQuadrangleCompletion ends m k zero
      a.1.1 b.1.1 c.1.1
    (∀ i ∈ rowClass m d 0 \
        edgeComponent ends (rowClass m d 0) zero,
        k ∉ ends i ∧ zero ∉ ends i) ∨
      (∀ i ∈ rowClass m d 1 \
        edgeComponent ends (rowClass m d 1) k,
        k ∉ ends i ∧ zero ∉ ends i) := by
  dsimp only
  have hc' := (mem_canonicalCoverageExclusiveBadQuadrangles_iff
    ends m j k l zero p a b c).mp hc
  rcases canonicalQuadrangleCompletion_failedGate_boundaryCertificate
      hloop hjk hkl a b c hc'.2.2 with hzero | hone
  · left
    intro i hi
    constructor
    · exact not_mem_ends_of_mem_sdiff_edgeComponent_of_conn
        ends _ zero k hi
          (connK_symm ends _ hzero.1)
    · exact not_mem_ends_of_mem_sdiff_edgeComponent_of_conn
        ends _ zero zero hi Relation.ReflTransGen.refl
  · right
    intro i hi
    have heq : edgeComponent ends
        (rowClass m
          (canonicalQuadrangleCompletion ends m k zero
            a.1.1 b.1.1 c.1.1) 1) k =
      edgeComponent ends
        (rowClass m
          (canonicalQuadrangleCompletion ends m k zero
            a.1.1 b.1.1 c.1.1) 1) zero :=
      edgeComponent_eq_of_conn ends _ k zero hone.1
    constructor
    · exact not_mem_ends_of_mem_sdiff_edgeComponent_of_conn
        ends _ k k hi Relation.ReflTransGen.refl
    · rw [heq] at hi
      exact not_mem_ends_of_mem_sdiff_edgeComponent_of_conn
        ends _ zero zero hi Relation.ReflTransGen.refl



theorem exists_transfer_symmDiff_eq_normalRow_symmDiff_of_adjacent
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l)
    {p : Finset I × Finset I}
    (x y : leftMaskFiber ends m j k l zero p)
    (hxy : CanonicalMaskTransferAdjacent ends m j k l zero p x y) :
    ∃ r s : leftMaskFiber ends m j k l zero p,
      canonicalNormalRow ends m k zero x.1.1 ∆
          canonicalNormalRow ends m k zero y.1.1 =
        canonicalTransferUnion ends m k zero r.1.1 ∆
          canonicalTransferUnion ends m k zero s.1.1 ∆
          canonicalTransferUnion ends m k zero x.1.1 ∆
          canonicalTransferUnion ends m k zero y.1.1 := by
  obtain ⟨r, s, -, -, hrs⟩ :=
    (canonicalMaskTransferAdjacent_iff_exists_works_rowSymmDiff
      hloop hjk hkl x y).mp hxy
  refine ⟨r, s, ?_⟩
  exact canonicalNormalRow_symmDiff_eq_of_translatedRow_eq
    ends m k zero r.1.1 s.1.1 x.1.1 y.1.1 hrs



theorem sdiff_eq_sdiff_of_symmDiff_subset
    (A B E : Finset I) (hAB : A ∆ B ⊆ E) : A \ E = B \ E := by
  classical
  ext i
  by_cases hiE : i ∈ E
  · simp [hiE]
  · have hiSame : i ∈ A ↔ i ∈ B := by
      by_contra h
      have hiAB : i ∈ A ∆ B := by
        simp only [Finset.mem_symmDiff]
        tauto
      exact hiE (hAB hiAB)
    simp [hiE, hiSame]



theorem fourfold_symmDiff_subset_of_outside_pair_membership
    (A B C D E : Finset I)
    (hout : ∀ i, i ∉ E -> (i ∈ A ∆ B ↔ i ∈ C ∆ D)) :
    A ∆ B ∆ C ∆ D ⊆ E := by
  classical
  intro i hi
  by_contra hiE
  have hpairs := hout i hiE
  simp only [Finset.mem_symmDiff] at hi hpairs
  tauto




theorem canonicalNormalRow_symmDiff_subset_of_translatedRow_eq
    (ends : I -> Sym2 W) (m K : Finset I) (k zero : W)
    (r s x y : ↑m -> Fin 4)
    (hrs : canonicalTranslatedRow ends m k zero r x =
      canonicalTranslatedRow ends m k zero s y)
    (hout : ∀ i, i ∉ K ->
      (i ∈ canonicalTransferUnion ends m k zero r ∆
          canonicalTransferUnion ends m k zero s ↔
        i ∈ canonicalTransferUnion ends m k zero x ∆
          canonicalTransferUnion ends m k zero y)) :
    canonicalNormalRow ends m k zero x ∆
        canonicalNormalRow ends m k zero y ⊆ K := by
  rw [canonicalNormalRow_symmDiff_eq_of_translatedRow_eq
    ends m k zero r s x y hrs]
  exact fourfold_symmDiff_subset_of_outside_pair_membership
    _ _ _ _ K hout






theorem canonicalNormalRow_symmDiff_subset_canonicalQuadrangleRow
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l)
    {p : Finset I × Finset I}
    (a b c : leftMaskFiber ends m j k l zero p) (rho : Fin 2)
    (K : Finset I)
    (hK : K = rowClass m
      (canonicalQuadrangleCompletion ends m k zero
        a.1.1 b.1.1 c.1.1) rho)
    (r s x y : ↑m -> Fin 4)
    (hrs : canonicalTranslatedRow ends m k zero r x =
      canonicalTranslatedRow ends m k zero s y)
    (href : ∀ i, i ∉ K ->
      (i ∈ canonicalTransferUnion ends m k zero r ∆
          canonicalTransferUnion ends m k zero s ↔
        i ∈ rowClass m c.1.1 rho))
    (hend : ∀ i, i ∉ K ->
      (i ∈ canonicalTransferUnion ends m k zero x ∆
          canonicalTransferUnion ends m k zero y ↔
        i ∈ canonicalTransferUnion ends m k zero a.1.1 ∆
          canonicalTransferUnion ends m k zero b.1.1)) :
    canonicalNormalRow ends m k zero x ∆
        canonicalNormalRow ends m k zero y ⊆ K := by
  apply canonicalNormalRow_symmDiff_subset_of_translatedRow_eq
    ends m K k zero r s x y hrs
  intro i hiK
  have hiRow : i ∉ rowClass m
      (canonicalQuadrangleCompletion ends m k zero
        a.1.1 b.1.1 c.1.1) rho := by
    rw [← hK]
    exact hiK
  calc
    (i ∈ canonicalTransferUnion ends m k zero r ∆
        canonicalTransferUnion ends m k zero s) ↔
        i ∈ rowClass m c.1.1 rho := href i hiK
    _ ↔ i ∈ canonicalTransferUnion ends m k zero a.1.1 ∆
        canonicalTransferUnion ends m k zero b.1.1 :=
      rowClass_pair_parity_of_not_mem_canonicalQuadrangleCompletion
        hloop hjk hkl a b c rho hiRow
    _ ↔ i ∈ canonicalTransferUnion ends m k zero x ∆
        canonicalTransferUnion ends m k zero y := (hend i hiK).symm





theorem canonicalNormalRow_sdiff_eq_of_adjacent_of_outside_transfer_membership
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l)
    {p : Finset I × Finset I}
    (E : Finset I)
    (x y : leftMaskFiber ends m j k l zero p)
    (hxy : CanonicalMaskTransferAdjacent ends m j k l zero p x y)
    (hcancel : ∀ r s : leftMaskFiber ends m j k l zero p,
      canonicalTranslatedRow ends m k zero r.1.1 x.1.1 =
          canonicalTranslatedRow ends m k zero s.1.1 y.1.1 ->
        ∀ i, i ∉ E ->
          (i ∈ canonicalTransferUnion ends m k zero r.1.1 ∆
              canonicalTransferUnion ends m k zero s.1.1 ↔
            i ∈ canonicalTransferUnion ends m k zero x.1.1 ∆
              canonicalTransferUnion ends m k zero y.1.1)) :
    canonicalNormalRow ends m k zero x.1.1 \ E =
      canonicalNormalRow ends m k zero y.1.1 \ E := by
  obtain ⟨r, s, -, -, hrs⟩ :=
    (canonicalMaskTransferAdjacent_iff_exists_works_rowSymmDiff
      hloop hjk hkl x y).mp hxy
  have hnormal := canonicalNormalRow_symmDiff_eq_of_translatedRow_eq
    ends m k zero r.1.1 s.1.1 x.1.1 y.1.1 hrs
  apply sdiff_eq_sdiff_of_symmDiff_subset
  rw [hnormal]
  exact fourfold_symmDiff_subset_of_outside_pair_membership
    _ _ _ _ E (hcancel r s hrs)



theorem canonicalNormalRow_sdiff_eq_of_orbit_of_adjacent
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    {p : Finset I × Finset I}
    (E : Finset I)
    (hstep : ∀ x y : leftMaskFiber ends m j k l zero p,
      CanonicalMaskTransferAdjacent ends m j k l zero p x y ->
        canonicalNormalRow ends m k zero x.1.1 \ E =
          canonicalNormalRow ends m k zero y.1.1 \ E)
    (c d : leftMaskFiber ends m j k l zero p)
    (hcd : CanonicalMaskTransferOrbit ends m j k l zero p c d) :
    canonicalNormalRow ends m k zero c.1.1 \ E =
      canonicalNormalRow ends m k zero d.1.1 \ E := by
  induction hcd with
  | refl => rfl
  | @tail x y _ hxy ih => exact ih.trans (hstep x y hxy)


theorem symmDiff_subset_union_symmDiff
    (A B C : Finset I) : A ∆ C ⊆ (A ∆ B) ∪ (B ∆ C) := by
  classical
  intro i hi
  simp only [Finset.mem_symmDiff, Finset.mem_union] at hi ⊢
  tauto





theorem canonicalNormalRow_symmDiff_subset_of_orbit_of_adjacent
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    {p : Finset I × Finset I}
    (E : Finset I)
    (hstep : ∀ x y : leftMaskFiber ends m j k l zero p,
      CanonicalMaskTransferAdjacent ends m j k l zero p x y ->
        canonicalNormalRow ends m k zero x.1.1 ∆
          canonicalNormalRow ends m k zero y.1.1 ⊆ E)
    (c d : leftMaskFiber ends m j k l zero p)
    (hcd : CanonicalMaskTransferOrbit ends m j k l zero p c d) :
    canonicalNormalRow ends m k zero c.1.1 ∆
      canonicalNormalRow ends m k zero d.1.1 ⊆ E := by
  induction hcd with
  | refl => simp
  | @tail x y hcx hxy ih =>
      exact (symmDiff_subset_union_symmDiff
        (canonicalNormalRow ends m k zero c.1.1)
        (canonicalNormalRow ends m k zero x.1.1)
        (canonicalNormalRow ends m k zero y.1.1)).trans
          (Finset.union_subset ih (hstep x y hxy))

end StatMech.GrahamGHS.FourColor

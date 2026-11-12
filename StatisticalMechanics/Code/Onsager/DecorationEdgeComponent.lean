/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.Onsager.DecorationWalkSign
import Code.Ising.KWDualBijection









namespace StatMech.Onsager

open Finset SimpleGraph StatMech.Ising

private theorem incCount_union_of_disjoint
    {V : Type*} [DecidableEq V]
    (A B : Finset (Sym2 V)) (hdisj : Disjoint A B) (v : V) :
    incCount (A ∪ B) v = incCount A v + incCount B v := by
  unfold incCount
  rw [Finset.filter_union, Finset.card_union_of_disjoint]
  exact hdisj.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _)



theorem ons_decorated_split_cycle_at_external
    (L : ℕ) [Fact (2 < L)]
    (D : ons_DecoratedEvenSubgraph L) (d : ons_Dart L)
    (hd : s(d, ons_dartRev L d) ∈ D.1) :
    ∃ (q : (ons_decGraph L).Walk d d)
      (R : ons_DecoratedEvenSubgraph L),
      q.IsCycle ∧ q.snd = ons_dartRev L d ∧
      D.1 = q.edges.toFinset ∪ R.1 ∧
      Disjoint q.edges.toFinset R.1 ∧
      (∀ v ∈ q.support, incCount R.1 v = 0) ∧
      incCount R.1 d = 0 ∧
      incCount R.1 (ons_dartRev L d) = 0 := by
  classical
  obtain ⟨ι, hiFintype, hiDecidable, base, p, hpcycle,
      hcover, hedgeDisj, hvertDisj⟩ :=
    ons_trivalent_even_cycle_decomposition (ons_decGraph L)
      (ons_decGraph_degree_le_three L) D.1 D.2
  letI : Fintype ι := hiFintype
  letI : DecidableEq ι := hiDecidable
  have hdi : ∃ i : ι, s(d, ons_dartRev L d) ∈
      (p i).edges.toFinset := by
    rw [hcover, Finset.mem_biUnion] at hd
    simpa using hd
  obtain ⟨i, hdi⟩ := hdi
  obtain ⟨q, hqcycle, hqsnd, hqedges⟩ :=
    ons_decCycle_root_at_external (p i) (hpcycle i) d hdi
  let C := (p i).edges.toFinset
  have hCD : C ⊆ D.1 := by
    intro edge hedge
    rw [hcover, Finset.mem_biUnion]
    exact ⟨i, Finset.mem_univ i, hedge⟩
  have hCmem : C ∈ evenSubgraphs (ons_decGraph L) :=
    ons_cycle_edges_evenSubgraph (ons_decGraph L) (p i) (hpcycle i)
  let Rfin := symmDiff D.1 C
  have hRsubD : Rfin ⊆ D.1 := by
    intro edge hedge
    change edge ∈ symmDiff D.1 C at hedge
    rw [Finset.mem_symmDiff] at hedge
    rcases hedge with hedge | hedge
    · exact hedge.1
    · exact (hedge.2 (hCD hedge.1)).elim
  have hDdata : D.1 ⊆ (ons_decGraph L).edgeFinset ∧
      IsEvenSubgraph D.1 := by
    have hmem : D.1 ∈
        (ons_decGraph L).edgeFinset.powerset.filter IsEvenSubgraph := by
      simpa only [evenSubgraphs] using D.2
    have hdata := Finset.mem_filter.mp hmem
    exact ⟨Finset.mem_powerset.mp hdata.1, hdata.2⟩
  have hCdata : C ⊆ (ons_decGraph L).edgeFinset ∧
      IsEvenSubgraph C := by
    have hmem : C ∈
        (ons_decGraph L).edgeFinset.powerset.filter IsEvenSubgraph := by
      simpa only [evenSubgraphs] using hCmem
    have hdata := Finset.mem_filter.mp hmem
    exact ⟨Finset.mem_powerset.mp hdata.1, hdata.2⟩
  have hRmem : Rfin ∈ evenSubgraphs (ons_decGraph L) := by
    simpa [evenSubgraphs] using
      (show Rfin ⊆ (ons_decGraph L).edgeFinset ∧ IsEvenSubgraph Rfin from
        ⟨hRsubD.trans hDdata.1,
          isEvenSubgraph_symmDiff hDdata.2 hCdata.2⟩)
  let R : ons_DecoratedEvenSubgraph L := ⟨Rfin, hRmem⟩
  have hsplit : D.1 = C ∪ Rfin := by
    ext edge
    by_cases heC : edge ∈ C
    · have heD := hCD heC
      simp [Rfin, heC, heD]
    · simp only [Finset.mem_union, heC, false_or]
      change edge ∈ D.1 ↔ edge ∈ symmDiff D.1 C
      rw [Finset.mem_symmDiff]
      tauto
  have hdisj : Disjoint C Rfin := by
    rw [Finset.disjoint_left]
    intro edge heC heR
    change edge ∈ symmDiff D.1 C at heR
    rw [Finset.mem_symmDiff] at heR
    rcases heR with heR | heR
    · exact heR.2 heC
    · exact heR.2 (hCD heC)
  have hcountD (v : ons_Dart L)
      (hv : s(d, ons_dartRev L d) ∈ D.1)
      (hvend : v = d ∨ v = ons_dartRev L d) :
      incCount D.1 v = 2 := by
    rcases incCount_eq_zero_or_two_of_trivalent (ons_decGraph L)
        (ons_decGraph_degree_le_three L) D.1 D.2 v with hzero | htwo
    · have hpos : 0 < incCount D.1 v := by
        unfold incCount
        apply Finset.card_pos.mpr
        refine ⟨s(d, ons_dartRev L d), Finset.mem_filter.mpr ⟨hv, ?_⟩⟩
        rcases hvend with rfl | rfl <;> simp
      omega
    · exact htwo
  have hcountC (v : ons_Dart L)
      (hvend : v = d ∨ v = ons_dartRev L d) :
      incCount C v = 2 := by
    rcases incCount_eq_zero_or_two_of_trivalent (ons_decGraph L)
        (ons_decGraph_degree_le_three L) C hCmem v with hzero | htwo
    · have hpos : 0 < incCount C v := by
        unfold incCount
        apply Finset.card_pos.mpr
        refine ⟨s(d, ons_dartRev L d), Finset.mem_filter.mpr ⟨hdi, ?_⟩⟩
        rcases hvend with rfl | rfl <;> simp
      omega
    · exact htwo
  have hcountR (v : ons_Dart L)
      (hvend : v = d ∨ v = ons_dartRev L d) :
      incCount Rfin v = 0 := by
    have hsum := incCount_union_of_disjoint C Rfin hdisj v
    rw [← hsplit, hcountD v hd hvend, hcountC v hvend] at hsum
    omega
  have hcountRSupport (v : ons_Dart L) (hvq : v ∈ q.support) :
      incCount Rfin v = 0 := by
    have hvpi : v ∈ (p i).toSubgraph.verts := by
      rw [SimpleGraph.Walk.mem_verts_toSubgraph]
      rw [q.mem_support_iff_exists_mem_edges_of_not_nil hqcycle.not_nil] at hvq
      obtain ⟨edge, hedgeq, hvedge⟩ := hvq
      apply (p i).mem_support_of_mem_edges
      · apply List.mem_toFinset.mp
        rw [← hqedges]
        exact List.mem_toFinset.mpr hedgeq
      · exact hvedge
    unfold incCount
    rw [Finset.card_eq_zero]
    rw [Finset.filter_eq_empty_iff]
    intro edge hedgeR hvedge
    have hedgeD : edge ∈ D.1 := hRsubD hedgeR
    rw [hcover, Finset.mem_biUnion] at hedgeD
    obtain ⟨j, -, hedgej⟩ := hedgeD
    have hvpj : v ∈ (p j).toSubgraph.verts := by
      rw [SimpleGraph.Walk.mem_verts_toSubgraph]
      exact (p j).mem_support_of_mem_edges
        (List.mem_toFinset.mp hedgej) hvedge
    by_cases hij : i = j
    · subst j
      exact (Finset.disjoint_left.mp hdisj) hedgej hedgeR
    · exact (Set.disjoint_left.mp
        (hvertDisj (Finset.mem_univ i) (Finset.mem_univ j) hij)) hvpi hvpj
  refine ⟨q, R, hqcycle, hqsnd, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [R, C, hqedges] using hsplit
  · simpa [R, C, hqedges] using hdisj
  · intro v hv
    exact hcountRSupport v hv
  · exact hcountR d (Or.inl rfl)
  · exact hcountR (ons_dartRev L d) (Or.inr rfl)



theorem ons_cycle_vertices_disjoint_of_incCount_zero
    {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    {u v : V} (q : G.Walk u u) (p : G.Walk v v)
    (hp : p.IsCycle) (F : Finset (Sym2 V))
    (hzero : ∀ w ∈ q.support, incCount F w = 0)
    (hpF : p.edges.toFinset ⊆ F) :
    Disjoint q.toSubgraph.verts p.toSubgraph.verts := by
  rw [Set.disjoint_left]
  intro w hwq hwp
  have hwq' : w ∈ q.support := q.mem_verts_toSubgraph.mp hwq
  have hwp' : w ∈ p.support := p.mem_verts_toSubgraph.mp hwp
  rw [p.mem_support_iff_exists_mem_edges_of_not_nil hp.not_nil] at hwp'
  obtain ⟨edge, hedgep, hwedge⟩ := hwp'
  have hedgeF : edge ∈ F := hpF (List.mem_toFinset.mpr hedgep)
  have hpos : 0 < incCount F w := by
    unfold incCount
    apply Finset.card_pos.mpr
    exact ⟨edge, Finset.mem_filter.mpr ⟨hedgeF, hwedge⟩⟩
  rw [hzero w hwq'] at hpos
  omega



theorem ons_originalEdgesOfDecorated_split
    (L : ℕ) [Fact (2 < L)]
    (D R : ons_DecoratedEvenSubgraph L) {d : ons_Dart L}
    (q : (ons_decGraph L).Walk d d)
    (hsplit : D.1 = q.edges.toFinset ∪ R.1) :
    ons_originalEdgesOfDecorated L D =
      ons_walkOriginalEdges q ∪ ons_originalEdgesOfDecorated L R := by
  classical
  rw [← ons_decoratedExternalEdges_image L D,
    ← ons_decoratedExternalEdges_image L R]
  unfold ons_walkOriginalEdges ons_walkExternalEdges
  have hext : ons_decoratedExternalEdges D.1 =
      ons_decoratedExternalEdges q.edges.toFinset ∪
        ons_decoratedExternalEdges R.1 := by
    ext edge
    simp only [ons_decoratedExternalEdges, Finset.mem_filter,
      Finset.mem_union]
    rw [hsplit, Finset.mem_union]
    tauto
  rw [hext, Finset.image_union]



theorem ons_originalEdgesOfDecorated_split_disjoint
    (L : ℕ) [Fact (2 < L)]
    (R : ons_DecoratedEvenSubgraph L) {d : ons_Dart L}
    (q : (ons_decGraph L).Walk d d)
    (hdisj : Disjoint q.edges.toFinset R.1) :
    Disjoint (ons_walkOriginalEdges q)
      (ons_originalEdgesOfDecorated L R) := by
  classical
  rw [← ons_decoratedExternalEdges_image L R]
  unfold ons_walkOriginalEdges ons_walkExternalEdges
  rw [Finset.disjoint_left]
  intro edge heq heR
  rcases Finset.mem_image.mp heq with ⟨eq, heqExt, heqProj⟩
  rcases Finset.mem_image.mp heR with ⟨eR, heRExt, heRProj⟩
  have heqData := Finset.mem_filter.mp heqExt
  have heRData := Finset.mem_filter.mp heRExt
  have hproj : ons_decEdgeProjection eR = ons_decEdgeProjection eq :=
    heRProj.trans heqProj.symm
  have hedge : eq = eR :=
    ons_decEdgeProjection_injective_of_external L
      heqData.2 heRData.2 hproj.symm
  subst eR
  exact (Finset.disjoint_left.mp hdisj) heqData.1 heRData.1

theorem ons_originalHomology_split
    (L : ℕ) [Fact (2 < L)]
    (D R : ons_DecoratedEvenSubgraph L) {d : ons_Dart L}
    (q : (ons_decGraph L).Walk d d)
    (hsplit : D.1 = q.edges.toFinset ∪ R.1)
    (hdisj : Disjoint q.edges.toFinset R.1) :
    ons_evenHomology L (ons_originalEdgesOfDecorated L D) =
      ons_evenHomology L (ons_walkOriginalEdges q) +
        ons_evenHomology L (ons_originalEdgesOfDecorated L R) := by
  rw [ons_originalEdgesOfDecorated_split L D R q hsplit]
  exact ons_evenHomology_union L _ _
    (ons_originalEdgesOfDecorated_split_disjoint L R q hdisj)

theorem ons_originalWeight_split
    (L : ℕ) [Fact (2 < L)]
    (D R : ons_DecoratedEvenSubgraph L) {d : ons_Dart L}
    (q : (ons_decGraph L).Walk d d)
    (hsplit : D.1 = q.edges.toFinset ∪ R.1)
    (hdisj : Disjoint q.edges.toFinset R.1)
    (weight : Sym2 (ZMod L × ZMod L) → ℂ) :
    (∏ edge ∈ ons_originalEdgesOfDecorated L D, weight edge) =
      (∏ edge ∈ ons_walkOriginalEdges q, weight edge) *
        ∏ edge ∈ ons_originalEdgesOfDecorated L R, weight edge := by
  rw [ons_originalEdgesOfDecorated_split L D R q hsplit]
  exact Finset.prod_union
    (ons_originalEdgesOfDecorated_split_disjoint L R q hdisj)



theorem ons_decoratedWeightedSpinWeight_split_of_isotropic
    (L : ℕ) [Fact (2 < L)]
    (D R : ons_DecoratedEvenSubgraph L) {d : ons_Dart L}
    (q : (ons_decGraph L).Walk d d)
    (hsplit : D.1 = q.edges.toFinset ∪ R.1)
    (hdisj : Disjoint q.edges.toFinset R.1)
    (weight : Sym2 (ZMod L × ZMod L) → ℂ) (a b : Fin 2)
    (hisotropic : ons_homologyIntersection
      (ons_evenHomology L (ons_walkOriginalEdges q))
      (ons_evenHomology L (ons_originalEdgesOfDecorated L R)) = 0) :
    ons_decoratedWeightedSpinWeight L weight a b D =
      ((ons_spinCharacter a b
          (ons_evenHomology L (ons_walkOriginalEdges q)) : ℂ) *
        ∏ edge ∈ ons_walkOriginalEdges q, weight edge) *
      ons_decoratedWeightedSpinWeight L weight a b R := by
  have hcharReal := ons_spinCharacter_add_of_intersection_zero a b
    (ons_evenHomology L (ons_walkOriginalEdges q))
    (ons_evenHomology L (ons_originalEdgesOfDecorated L R)) hisotropic
  have hchar :
      (ons_spinCharacter a b
        (ons_evenHomology L (ons_walkOriginalEdges q) +
          ons_evenHomology L (ons_originalEdgesOfDecorated L R)) : ℂ) =
        (ons_spinCharacter a b
          (ons_evenHomology L (ons_walkOriginalEdges q)) : ℂ) *
        (ons_spinCharacter a b
          (ons_evenHomology L (ons_originalEdgesOfDecorated L R)) : ℂ) := by
    exact_mod_cast hcharReal
  rw [ons_decoratedWeightedSpinWeight,
    ons_originalHomology_split L D R q hsplit hdisj, hchar,
    ons_originalWeight_split L D R q hsplit hdisj,
    ons_decoratedWeightedSpinWeight]
  ring

end StatMech.Onsager

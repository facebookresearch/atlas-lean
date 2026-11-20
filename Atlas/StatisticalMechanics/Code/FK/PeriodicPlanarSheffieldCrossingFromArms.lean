/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FK.PeriodicPlanarSheffieldDualTranslated










open Filter MeasureTheory Set SimpleGraph Topology

namespace StatMech.FK.PeriodicPlanar

open BeffaraDC Lattice

variable {V : Type*} [DecidableEq V] [Countable V]
  {P : PeriodicGraph V}




theorem PeriodicGraph.exists_boundary_walk_of_walk_to_compl
    (P : PeriodicGraph V) (omega : ConfigSpace (Sym2 V)) (A : Set V)
    {x y : V} (p : (P.openSubgraph omega).Walk x y)
    (hx : x ∈ A) (hy : y ∉ A) :
    ∃ b ∈ A, ∃ z : V, P.graph.Adj b z ∧ z ∉ A ∧
      ∃ q : (P.openSubgraph omega).Walk x b,
        (∀ v ∈ q.support, v ∈ A) ∧
        ∀ v ∈ q.support, v ∈ p.support := by
  induction p with
  | nil => exact (hy hx).elim
  | @cons x z y hxz p ih =>
      by_cases hz : z ∈ A
      · obtain ⟨b, hb, w, hbw, hw, q, hqA, hqp⟩ := ih hz hy
        refine ⟨b, hb, w, hbw, hw, q.cons hxz, ?_, ?_⟩
        · intro v hv
          rw [SimpleGraph.Walk.support_cons] at hv
          rcases List.mem_cons.mp hv with rfl | hv
          · exact hx
          · exact hqA v hv
        · intro v hv
          rw [SimpleGraph.Walk.support_cons] at hv ⊢
          rcases List.mem_cons.mp hv with rfl | hv
          · exact List.mem_cons_self
          · exact List.mem_cons_of_mem x (hqp v hv)
      · refine ⟨x, hx, z, hxz.1, hz, .nil, ?_, ?_⟩
        · simpa using hx
        · intro v hv
          rw [SimpleGraph.Walk.support_nil] at hv
          rw [SimpleGraph.Walk.support_cons]
          have hvx : v = x := by simpa using hv
          exact List.mem_cons.2 (Or.inl hvx)



theorem PeriodicPlaneEmbedding.openSub_rectRestrict_eq_induce
    (E : PeriodicPlaneEmbedding P) (a b c d : Real)
    (omega : ConfigSpace (Sym2 V)) :
    FK.openSub (E.rectGraph a b c d) (E.rectRestrict a b c d omega) =
      (P.openSubgraph omega).induce (E.rectVertices a b c d) := by
  ext x y
  simp only [FK.openSub_adj, SimpleGraph.induce_adj,
    PeriodicGraph.openSubgraph_adj]
  rfl


theorem PeriodicPlaneEmbedding.verticalCrossingEvent_mono_right
    (E : PeriodicPlaneEmbedding P) {a b b' c d : Real} (hbb' : b ≤ b') :
    E.verticalCrossingEvent a b c d ⊆
      E.verticalCrossingEvent a b' c d := by
  intro omega homega
  change E.rectRestrict a b c d omega ∈
    E.finiteVerticalCrossing a b c d at homega
  obtain ⟨x, y, hxBottom, hyTop, hxy⟩ := homega
  have hx' : x.1 ∈ E.rectVertices a b' c d :=
    ⟨x.2.1, x.2.2.1.trans hbb', x.2.2.2⟩
  have hy' : y.1 ∈ E.rectVertices a b' c d :=
    ⟨y.2.1, y.2.2.1.trans hbb', y.2.2.2⟩
  have hxBottom' : E.rectBottomBoundary a b' c d ⟨x.1, hx'⟩ := by
    obtain ⟨z, hxz, hz⟩ := hxBottom
    exact ⟨z, hxz, hz⟩
  have hyTop' : E.rectTopBoundary a b' c d ⟨y.1, hy'⟩ := by
    obtain ⟨z, hyz, hz⟩ := hyTop
    exact ⟨z, hyz, hz⟩
  rw [E.openSub_rectRestrict_eq_induce] at hxy
  obtain ⟨p⟩ := hxy
  let pAmbient : (P.openSubgraph omega).Walk x.1 y.1 :=
    p.map (SimpleGraph.Embedding.induce (E.rectVertices a b c d)).toHom
  have hpAmbient : ∀ v ∈ pAmbient.support,
      v ∈ E.rectVertices a b' c d := by
    intro v hv
    have hv' : v ∈
        (p.map (SimpleGraph.Embedding.induce
          (E.rectVertices a b c d)).toHom).support := by
      exact hv
    simp only [SimpleGraph.Walk.support_map, List.mem_map] at hv'
    obtain ⟨w, _hw, rfl⟩ := hv'
    exact ⟨w.2.1, w.2.2.1.trans hbb', w.2.2.2⟩
  have hxy' :
      ((P.openSubgraph omega).induce (E.rectVertices a b' c d)).Reachable
        ⟨x.1, hx'⟩ ⟨y.1, hy'⟩ :=
    ⟨pAmbient.induce (E.rectVertices a b' c d) hpAmbient⟩
  change E.rectRestrict a b' c d omega ∈
    E.finiteVerticalCrossing a b' c d
  refine ⟨⟨x.1, hx'⟩, ⟨y.1, hy'⟩, hxBottom', hyTop', ?_⟩
  rw [E.openSub_rectRestrict_eq_induce]
  exact hxy'

theorem PeriodicPlaneEmbedding.verticalCrossing_measureReal_mono_right
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsFiniteMeasure mu]
    {a b b' c d : Real}
    (hbb' : b ≤ b') :
    mu.real (E.verticalCrossingEvent a b c d) ≤
      mu.real (E.verticalCrossingEvent a b' c d) :=
  measureReal_mono (E.verticalCrossingEvent_mono_right hbb')



theorem PeriodicPlaneEmbedding.finiteStripJoinedBoundaryArmEvent_subset_verticalCrossing
    (E : PeriodicPlaneEmbedding P) {B r c d : Real} {n : Nat}
    {L R : Finset V}
    (hB : ∀ {x y : V} (hxy : P.graph.Adj x y) (t) (i : Fin 2),
      |E.coordinates (E.edgeArc hxy t - E.vertex x) i| ≤ B)
    (hB0 : 0 ≤ B)
    (hgap : 3 * B < d - c) :
    E.finiteStripJoinedBoundaryArmEvent r c d n L R ⊆
      E.verticalCrossingEvent r (r + n)
        ((2 * c + d) / 3) ((c + 2 * d) / 3) := by
  intro omega homega
  let C : Real := (2 * c + d) / 3
  let D : Real := (c + 2 * d) / 3
  obtain ⟨xl, hxl, xu, hxu, j, lower, upper, _hjL,
    hlowerStrip, hupperStrip⟩ :=
      E.finiteStripJoinedBoundaryArmEvent_openWalks homega
  let p : (P.openSubgraph omega).Walk xu xl := upper.append lower.reverse
  have hpStrip : ∀ v ∈ p.support,
      v ∈ E.rightHalfPlaneStripVertices r n := by
    intro v hv
    dsimp only [p] at hv
    rw [SimpleGraph.Walk.support_append,
      SimpleGraph.Walk.support_reverse] at hv
    rcases List.mem_append.mp hv with hv | hv
    · exact hupperStrip v hv
    · exact hlowerStrip v (by simpa using List.mem_of_mem_tail hv)
  have hxuC : xu ∈ {v : V | C ≤ E.vertexCoord v 1} := by
    change C ≤ E.vertexCoord xu 1
    have hxu' := hxu.2
    change d ≤ E.vertexCoord xu 1 at hxu'
    dsimp only [C]
    have hcd : c < d := by linarith
    linarith
  have hxlC : xl ∉ {v : V | C ≤ E.vertexCoord v 1} := by
    change ¬ C ≤ E.vertexCoord xl 1
    have hxl' := hxl.2
    change E.vertexCoord xl 1 ≤ c at hxl'
    dsimp only [C]
    have hcd : c < d := by linarith
    linarith
  obtain ⟨xb, hxbC, zb, hxbzb, hzbC, q, hqC, hqp⟩ :=
    P.exists_boundary_walk_of_walk_to_compl omega
      {v : V | C ≤ E.vertexCoord v 1} p hxuC hxlC
  have hxbLt : E.vertexCoord xb 1 < C + B := by
    have hdisp := hB hxbzb (1 : unitInterval) (1 : Fin 2)
    have heq :
        E.coordinates (E.edgeArc hxbzb (1 : unitInterval) - E.vertex xb) 1 =
          E.vertexCoord zb 1 - E.vertexCoord xb 1 := by
      rw [Path.target]
      simp [PeriodicPlaneEmbedding.vertexCoord, map_sub]
    rw [heq] at hdisp
    have hlow := (abs_le.mp hdisp).1
    change ¬ C ≤ E.vertexCoord zb 1 at hzbC
    have hzbLt : E.vertexCoord zb 1 < C := lt_of_not_ge hzbC
    linarith
  have hxbD : xb ∈ {v : V | E.vertexCoord v 1 ≤ D} := by
    change E.vertexCoord xb 1 ≤ D
    dsimp only [C, D] at hxbLt ⊢
    linarith
  have hxuD : xu ∉ {v : V | E.vertexCoord v 1 ≤ D} := by
    change ¬ E.vertexCoord xu 1 ≤ D
    have hxu' := hxu.2
    change d ≤ E.vertexCoord xu 1 at hxu'
    dsimp only [D]
    have hcd : c < d := by linarith
    linarith
  obtain ⟨xt, hxtD, zt, hxtzt, hztD, qRect0, hqD, hqsub⟩ :=
    P.exists_boundary_walk_of_walk_to_compl omega
      {v : V | E.vertexCoord v 1 ≤ D} q.reverse hxbD hxuD
  have hqRectC : ∀ v ∈ qRect0.support, C ≤ E.vertexCoord v 1 := by
    intro v hv
    have hvrev : v ∈ q.reverse.support := hqsub v hv
    have hvq : v ∈ q.support := by simpa using hvrev
    exact hqC v hvq
  have hqRectStrip : ∀ v ∈ qRect0.support,
      v ∈ E.rightHalfPlaneStripVertices r n := by
    intro v hv
    have hvrev : v ∈ q.reverse.support := hqsub v hv
    have hvq : v ∈ q.support := by simpa using hvrev
    exact hpStrip v (hqp v hvq)
  have hqRectVertices : ∀ v ∈ qRect0.support,
      v ∈ E.rectVertices r (r + n) C D := by
    intro v hv
    have hvStrip := hqRectStrip v hv
    change r ≤ E.vertexCoord v 0 ∧ E.vertexCoord v 0 ≤ r + (n : Real) ∧
      C ≤ E.vertexCoord v 1 ∧ E.vertexCoord v 1 ≤ D
    exact ⟨hvStrip.1, hvStrip.2, hqRectC v hv, hqD v hv⟩
  have hxbRect := hqRectVertices xb qRect0.start_mem_support
  have hxtRect := hqRectVertices xt qRect0.end_mem_support
  have hbottom : E.rectBottomBoundary r (r + n) C D ⟨xb, hxbRect⟩ := by
    refine ⟨zb, hxbzb, ?_⟩
    change ¬ C ≤ E.vertexCoord zb 1 at hzbC
    exact lt_of_not_ge hzbC
  have htop : E.rectTopBoundary r (r + n) C D ⟨xt, hxtRect⟩ := by
    refine ⟨zt, hxtzt, ?_⟩
    change ¬ E.vertexCoord zt 1 ≤ D at hztD
    exact lt_of_not_ge hztD
  have hreach :
      ((P.openSubgraph omega).induce (E.rectVertices r (r + n) C D)).Reachable
        ⟨xb, hxbRect⟩ ⟨xt, hxtRect⟩ :=
    ⟨qRect0.induce (E.rectVertices r (r + n) C D) hqRectVertices⟩
  change E.rectRestrict r (r + n) C D omega ∈
    E.finiteVerticalCrossing r (r + n) C D
  refine ⟨⟨xb, hxbRect⟩, ⟨xt, hxtRect⟩, hbottom, htop, ?_⟩
  rw [E.openSub_rectRestrict_eq_induce]
  exact hreach






theorem PeriodicPlaneEmbedding.verticalCrossing_tendsto_one_of_finiteStripJoinedBoundaryArms
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (B : Real)
    (hB : ∀ {x y : V} (hxy : P.graph.Adj x y) (u) (i : Fin 2),
      |E.coordinates (E.edgeArc hxy u - E.vertex x) i| ≤ B)
    (hB0 : 0 ≤ B)
    (r c d : Nat → Real) (width : Nat → Nat)
    (lower upper : Nat → Finset V)
    (hgap : ∀ n, 3 * B < d n - c n)
    (harms : Tendsto (fun n ↦ mu.real
      (E.finiteStripJoinedBoundaryArmEvent
        (r n) (c n) (d n) (width n) (lower n) (upper n)))
      atTop (nhds 1)) :
    Tendsto (fun n ↦ mu.real
      (E.verticalCrossingEvent (r n) (r n + width n)
        ((2 * c n + d n) / 3) ((c n + 2 * d n) / 3)))
      atTop (nhds 1) := by
  exact harms.squeeze tendsto_const_nhds
    (fun n ↦ measureReal_mono
      (E.finiteStripJoinedBoundaryArmEvent_subset_verticalCrossing
        hB hB0 (hgap n)))
    (fun _ ↦ measureReal_le_one)



theorem PeriodicPlaneEmbedding.exists_verticalCrossing_measureReal_gt_of_unique
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hFKG : IsFKG mu) (hTI : P.IsTranslationInvariant mu)
    (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
    (r B s : Real) (hB0 : 0 ≤ B)
    (hB : ∀ {x y : V} (hxy : P.graph.Adj x y) (u) (i : Fin 2),
      |E.coordinates (E.edgeArc hxy u - E.vertex x) i| ≤ B)
    (t : Int) (ht : 3 * B < t) (m : Nat)
    {epsilon : Real} (hepsilon : 0 < epsilon) :
    ∃ n : Nat, m ≤ n ∧ 1 - epsilon <
      mu.real (E.verticalCrossingEvent r (r + n)
        ((2 * s + (s + t)) / 3) ((s + 2 * (s + t)) / 3)) := by
  obtain ⟨L, U, n, _hL, hprob⟩ :=
    E.exists_highProbability_finiteStripJoinedBoundaryArmEvent_with_separation
      mu hFKG hTI hunique (le_refl r) s t hepsilon
  let N := max n m
  have hprobN : 1 - epsilon <
      mu.real (E.finiteStripJoinedBoundaryArmEvent r s (s + t) N L U) :=
    hprob.trans_le (measureReal_mono
      (E.finiteStripJoinedBoundaryArmEvent_mono r s (s + t) L U
        (Nat.le_max_left n m)))
  refine ⟨N, Nat.le_max_right n m, hprobN.trans_le (measureReal_mono ?_)⟩
  apply E.finiteStripJoinedBoundaryArmEvent_subset_verticalCrossing hB hB0
  norm_num at ht ⊢
  exact ht



theorem PeriodicPlaneEmbedding.exists_cofinal_verticalCrossing_tendsto_one_of_unique
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hFKG : IsFKG mu) (hTI : P.IsTranslationInvariant mu)
    (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
    (r B s : Real) (hB0 : 0 ≤ B)
    (hB : ∀ {x y : V} (hxy : P.graph.Adj x y) (u) (i : Fin 2),
      |E.coordinates (E.edgeArc hxy u - E.vertex x) i| ≤ B)
    (t : Int) (ht : 3 * B < t) :
    ∃ width : Nat → Nat,
      Tendsto width atTop atTop ∧
      Tendsto (fun k => mu.real
        (E.verticalCrossingEvent r (r + width k)
          ((2 * s + (s + t)) / 3) ((s + 2 * (s + t)) / 3)))
        atTop (nhds 1) := by
  choose width hwidth hprob using fun k : Nat =>
    E.exists_verticalCrossing_measureReal_gt_of_unique
      mu hFKG hTI hunique r B s hB0 hB t ht k
        (show 0 < (1 : Real) / (k + 1) by positivity)
  have hwidthTop : Tendsto width atTop atTop := by
    rw [tendsto_atTop]
    intro m
    filter_upwards [eventually_ge_atTop m] with k hk
    exact hk.trans (hwidth k)
  have hlower : Tendsto (fun k : Nat =>
      1 - (1 : Real) / (k + 1)) atTop (nhds 1) := by
    simpa using (tendsto_const_nhds (x := (1 : Real))).sub
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := Real))
  refine ⟨width, hwidthTop,
    tendsto_of_tendsto_of_tendsto_of_le_of_le hlower
      tendsto_const_nhds (fun k => le_of_lt (hprob k)) ?_⟩
  intro k
  exact measureReal_le_one



theorem PeriodicPlanarDualPair.exists_cofinal_complementaryDual_verticalCrossing_tendsto_one
    {W : Type*} [DecidableEq W] [Countable W]
    {Pdual : PeriodicGraph W}
    (D : PeriodicPlanarDualPair P Pdual)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hdualFKG : IsFKG (D.dualMeasure mu))
    (hTI : P.IsTranslationInvariant mu)
    (hdualUnique : D.dualMeasure mu
      {eta | Pdual.HasUniqueInfiniteCluster eta} = 1)
    (r B s : Real) (hB0 : 0 ≤ B)
    (hB : ∀ {x y : W} (hxy : Pdual.graph.Adj x y) (u) (i : Fin 2),
      |D.dualEmbedding.coordinates
        (D.dualEmbedding.edgeArc hxy u - D.dualEmbedding.vertex x) i| ≤ B)
    (t : Int) (ht : 3 * B < t) :
    ∃ width : Nat → Nat,
      Tendsto width atTop atTop ∧
      Tendsto (fun k => mu.real ((dualConfigEquiv D.edgeDual) ⁻¹'
        D.dualEmbedding.verticalCrossingEvent r (r + width k)
          ((2 * s + (s + t)) / 3) ((s + 2 * (s + t)) / 3)))
        atTop (nhds 1) := by
  let muDual := D.dualMeasure mu
  letI : IsProbabilityMeasure muDual := by
    dsimp only [muDual, PeriodicPlanarDualPair.dualMeasure]
    exact Measure.isProbabilityMeasure_map
      (continuous_dualConfigEquiv D.edgeDual).measurable.aemeasurable
  obtain ⟨width, hwidth, hlimit⟩ :=
    D.dualEmbedding.exists_cofinal_verticalCrossing_tendsto_one_of_unique
      muDual hdualFKG (D.dualMeasure_isTranslationInvariant mu hTI)
        hdualUnique r B s hB0 hB t ht
  refine ⟨width, hwidth, hlimit.congr' ?_⟩
  filter_upwards with k
  exact D.dualMeasure_measureReal mu
    (D.dualEmbedding.verticalCrossingEvent_measurableSet
      r (r + width k) ((2 * s + (s + t)) / 3)
        ((s + 2 * (s + t)) / 3))

end StatMech.FK.PeriodicPlanar

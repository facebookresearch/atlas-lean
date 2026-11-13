/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FK.PeriodicPlanarSheffieldHalfPlaneJoinedArmsHighProbability








open Filter MeasureTheory Set SimpleGraph Topology

namespace StatMech.FK.PeriodicPlanar

open BeffaraDC Lattice

variable {V : Type*} [DecidableEq V] [Countable V]
  {P : PeriodicGraph V}

theorem PeriodicGraph.infiniteSetConnectionWithin_mono_region
    (P : PeriodicGraph V) {A B : Set V} (hAB : A ⊆ B) (S T : Set V) :
    P.infiniteSetConnectionWithin A S T ⊆
      P.infiniteSetConnectionWithin B S T := by
  rintro omega ⟨x, hx, hinf, y, hy, hxy⟩
  exact ⟨x, hx, hinf, y, hy,
    P.connectedWithinSet_mono_region hAB x y hxy⟩



def PeriodicPlaneEmbedding.finiteStripJoinedBoundaryArmEvent
    (E : PeriodicPlaneEmbedding P) (r c d : Real) (n : Nat)
    (L R : Finset V) : Set (ConfigSpace (Sym2 V)) :=
  (P.infiniteSetConnectionWithin (E.rightHalfPlaneStripVertices r n)
      (L : Set V) (E.lowerBoundaryRayVertices r c) ∩
    P.infiniteSetConnectionWithin (E.rightHalfPlaneStripVertices r n)
      (R : Set V) (E.upperBoundaryRayVertices r d)) \
    E.halfPlaneStripPairMergeErrorUnion r n L R

theorem PeriodicPlaneEmbedding.finiteStripJoinedBoundaryArmEvent_measurableSet
    (E : PeriodicPlaneEmbedding P) (r c d : Real) (n : Nat)
    (L R : Finset V) :
    MeasurableSet (E.finiteStripJoinedBoundaryArmEvent r c d n L R) :=
  ((P.infiniteSetConnectionWithin_measurableSet
      (E.rightHalfPlaneStripVertices r n) (L : Set V)
      (E.lowerBoundaryRayVertices r c)).inter
    (P.infiniteSetConnectionWithin_measurableSet
      (E.rightHalfPlaneStripVertices r n) (R : Set V)
      (E.upperBoundaryRayVertices r d))).diff
    (E.halfPlaneStripPairMergeErrorUnion_measurableSet r n L R)

theorem PeriodicPlaneEmbedding.finiteStripJoinedBoundaryArmEvent_mono
    (E : PeriodicPlaneEmbedding P) (r c d : Real) (L R : Finset V) :
    Monotone (fun n => E.finiteStripJoinedBoundaryArmEvent r c d n L R) := by
  intro n N hnN omega h
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · exact P.infiniteSetConnectionWithin_mono_region
      (E.rightHalfPlaneStripVertices_mono r hnN)
      (L : Set V) (E.lowerBoundaryRayVertices r c) h.1.1
  · exact P.infiniteSetConnectionWithin_mono_region
      (E.rightHalfPlaneStripVertices_mono r hnN)
      (R : Set V) (E.upperBoundaryRayVertices r d) h.1.2
  · intro herror
    exact h.2 (E.halfPlaneStripPairMergeErrorUnion_antitone
      r L R hnN herror)



theorem PeriodicPlaneEmbedding.finiteJoinedBoundaryArmEvent_subset_iUnion_finiteStrip
    (E : PeriodicPlaneEmbedding P) (r c d : Real) (n₀ : Nat)
    (L R : Finset V) :
    E.finiteJoinedBoundaryArmEvent r c d n₀ L R ⊆
      ⋃ n : Nat, E.finiteStripJoinedBoundaryArmEvent r c d n L R := by
  intro omega h
  obtain ⟨x, hxL, hxinf, b, hb, hxb⟩ := h.1.1
  obtain ⟨y, hyR, hyinf, u, hu, hyu⟩ := h.1.2
  obtain ⟨nx, hxbx⟩ :=
    E.connectedWithin_rightHalfPlane_exists_strip omega r x b hxb
  obtain ⟨ny, hyuy⟩ :=
    E.connectedWithin_rightHalfPlane_exists_strip omega r y u hyu
  let n := max n₀ (max nx ny)
  apply Set.mem_iUnion.2
  refine ⟨n, ⟨⟨⟨x, hxL, hxinf, b, hb, ?_⟩,
    ⟨y, hyR, hyinf, u, hu, ?_⟩⟩, ?_⟩⟩
  · exact P.connectedWithinSet_mono_region
      (E.rightHalfPlaneStripVertices_mono r
        (le_max_of_le_right (le_max_left _ _))) x b hxbx
  · exact P.connectedWithinSet_mono_region
      (E.rightHalfPlaneStripVertices_mono r
        (le_max_of_le_right (le_max_right _ _))) y u hyuy
  · intro herror
    exact h.2 (E.halfPlaneStripPairMergeErrorUnion_antitone
      r L R (le_max_left _ _) herror)

theorem PeriodicPlaneEmbedding.finiteStripJoinedBoundaryArmEvent_measureReal_tendsto
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsFiniteMeasure mu]
    (r c d : Real) (L R : Finset V) :
    Tendsto (fun n => mu.real
      (E.finiteStripJoinedBoundaryArmEvent r c d n L R)) atTop
      (nhds (mu.real (⋃ n : Nat,
        E.finiteStripJoinedBoundaryArmEvent r c d n L R))) := by
  have hmeasure := tendsto_measure_iUnion_atTop (μ := mu)
    (E.finiteStripJoinedBoundaryArmEvent_mono r c d L R)
  exact (ENNReal.tendsto_toReal (measure_ne_top mu _)).comp hmeasure



theorem PeriodicPlaneEmbedding.exists_finiteStripJoinedBoundaryArmEvent_measureReal_gt
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (r c d : Real) (n₀ : Nat) (L R : Finset V) {epsilon : Real}
    (hprob : 1 - epsilon <
      mu.real (E.finiteJoinedBoundaryArmEvent r c d n₀ L R)) :
    ∃ n : Nat, 1 - epsilon <
      mu.real (E.finiteStripJoinedBoundaryArmEvent r c d n L R) := by
  let U := ⋃ n : Nat, E.finiteStripJoinedBoundaryArmEvent r c d n L R
  have hsub : E.finiteJoinedBoundaryArmEvent r c d n₀ L R ⊆ U :=
    E.finiteJoinedBoundaryArmEvent_subset_iUnion_finiteStrip r c d n₀ L R
  have hU : 1 - epsilon < mu.real U :=
    hprob.trans_le (measureReal_mono hsub)
  have ht := E.finiteStripJoinedBoundaryArmEvent_measureReal_tendsto
    mu r c d L R
  have hev : ∀ᶠ n in atTop, 1 - epsilon <
      mu.real (E.finiteStripJoinedBoundaryArmEvent r c d n L R) :=
    (tendsto_order.1 ht).1 (1 - epsilon) (by simpa only [U] using hU)
  exact hev.exists



theorem PeriodicPlaneEmbedding.exists_highProbability_finiteJoinedBoundaryArmEvent_with_separation
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hFKG : IsFKG mu) (hTI : P.IsTranslationInvariant mu)
    (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
    {r R : Real} (hrR : r ≤ R) (s : Real) (t : Int)
    {epsilon : Real} (hepsilon : 0 < epsilon) :
    ∃ L U : Finset V, ∃ n : Nat,
      (L : Set V) ⊆ E.rightHalfPlaneVertices R ∧
      1 - epsilon <
        mu.real (E.finiteJoinedBoundaryArmEvent r s (s + t) n L U) := by
  have hexists : mu {omega | P.HasInfiniteCluster omega} = 1 := by
    apply le_antisymm prob_le_one
    rw [← hunique]
    exact measure_mono fun omega h => h.1
  have hbox := P.orbitBoxHitsInfinite_real_tendsto_one mu hexists
  have hsq : Tendsto
      (fun N => (mu.real (P.orbitBoxHitsInfinite N)) ^ 2)
      atTop (nhds 1) := by
    simpa using hbox.pow 2
  have hmiss : Tendsto
      (fun N => 1 - (mu.real (P.orbitBoxHitsInfinite N)) ^ 2)
      atTop (nhds 0) := by
    simpa using (tendsto_const_nhds (x := (1 : Real))).sub hsq
  have hroot : Tendsto
      (fun N => Real.sqrt
        (1 - (mu.real (P.orbitBoxHitsInfinite N)) ^ 2))
      atTop (nhds 0) := by
    simpa using hmiss.sqrt
  have htwo : Tendsto
      (fun N => 2 * Real.sqrt
        (1 - (mu.real (P.orbitBoxHitsInfinite N)) ^ 2))
      atTop (nhds 0) := by
    simpa using (tendsto_const_nhds (x := (2 : Real))).mul hroot
  have hev : ∀ᶠ N in atTop,
      2 * Real.sqrt (1 - (mu.real (P.orbitBoxHitsInfinite N)) ^ 2) <
        epsilon / 2 :=
    (tendsto_order.1 htwo).2 (epsilon / 2) (half_pos hepsilon)
  obtain ⟨N, hN⟩ := hev.exists
  have heta : 0 < epsilon / 6 := div_pos hepsilon (by norm_num)
  obtain ⟨z₀, z, n, hS, hSlo, hjoined⟩ :=
    E.exists_inward_separated_finiteJoinedBoundaryArmEvent_with_margin_measureReal_gt
      mu hFKG hTI hunique hrR s t (P.orbitBox N) heta
  let S := (P.orbitBox N).image (P.shift z₀)
  let Slo := S.image (P.shift (verticalShift z))
  let Shi := (S.image (P.shift (verticalShift (1 + t)))).image
    (P.shift (verticalShift z))
  have hfull : (mu.real (P.orbitBoxHitsInfinite N)) ^ 2 ≤
      mu.real (P.infiniteSetConnectionWithin (E.rightHalfPlaneVertices r)
        (S : Set V) (E.rightHalfPlaneBoundaryVertices r)) := by
    have hSr : P.shift z₀ '' (P.orbitBox N : Set V) ⊆
        E.rightHalfPlaneVertices r := by
      intro x hx
      exact hrR.trans (hS (by simpa only [S, Finset.coe_image] using hx))
    have hbound := E.infiniteBoundaryConnection_measureReal_ge_orbitBox_sq_of_shift
      mu hFKG hTI hunique r N z₀ hSr
    simpa only [S, Finset.coe_image] using hbound
  have hsqrt : Real.sqrt (1 - mu.real
      (P.infiniteSetConnectionWithin (E.rightHalfPlaneVertices r)
        (S : Set V) (E.rightHalfPlaneBoundaryVertices r))) ≤
      Real.sqrt (1 - (mu.real (P.orbitBoxHitsInfinite N)) ^ 2) :=
    Real.sqrt_le_sqrt (sub_le_sub_left hfull 1)
  refine ⟨Slo, Shi, n, hSlo, ?_⟩
  linarith




theorem PeriodicPlaneEmbedding.exists_highProbability_finiteStripJoinedBoundaryArmEvent_with_separation
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hFKG : IsFKG mu) (hTI : P.IsTranslationInvariant mu)
    (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
    {r R : Real} (hrR : r ≤ R) (s : Real) (t : Int)
    {epsilon : Real} (hepsilon : 0 < epsilon) :
    ∃ L U : Finset V, ∃ n : Nat,
      (L : Set V) ⊆ E.rightHalfPlaneVertices R ∧
      1 - epsilon <
        mu.real (E.finiteStripJoinedBoundaryArmEvent r s (s + t) n L U) := by
  obtain ⟨L, U, n₀, hL, hprob⟩ :=
    E.exists_highProbability_finiteJoinedBoundaryArmEvent_with_separation
      mu hFKG hTI hunique hrR s t hepsilon
  obtain ⟨n, hn⟩ :=
    E.exists_finiteStripJoinedBoundaryArmEvent_measureReal_gt
      mu r s (s + t) n₀ L U hprob
  exact ⟨L, U, n, hL, hn⟩





theorem PeriodicPlaneEmbedding.exists_rowwise_finiteStripJoinedBoundaryArms_tendsto_one
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hFKG : IsFKG mu) (hTI : P.IsTranslationInvariant mu)
    (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
    (r R s : Nat → Real) (t : Nat → Int)
    (hrR : ∀ n, r n ≤ R n) (minimumWidth : Nat → Nat) :
    ∃ lower upper : Nat → Finset V, ∃ width : Nat → Nat,
      (∀ n, minimumWidth n ≤ width n) ∧
      (∀ n, (lower n : Set V) ⊆ E.rightHalfPlaneVertices (R n)) ∧
      Tendsto (fun n ↦ mu.real
        (E.finiteStripJoinedBoundaryArmEvent
          (r n) (s n) (s n + t n) (width n) (lower n) (upper n)))
        atTop (nhds 1) := by
  let epsilon : Nat → Real := fun n ↦ 1 / (n + 1 : Real)
  have hepsilon (n : Nat) : 0 < epsilon n := by
    dsimp only [epsilon]
    positivity
  choose lower upper initialWidth hlower hprob using fun n ↦
    E.exists_highProbability_finiteStripJoinedBoundaryArmEvent_with_separation
      mu hFKG hTI hunique (hrR n) (s n) (t n) (hepsilon n)
  let width : Nat → Nat := fun n ↦ max (initialWidth n) (minimumWidth n)
  have hprob' (n : Nat) : 1 - epsilon n < mu.real
      (E.finiteStripJoinedBoundaryArmEvent
        (r n) (s n) (s n + t n) (width n) (lower n) (upper n)) := by
    exact (hprob n).trans_le (measureReal_mono
      (E.finiteStripJoinedBoundaryArmEvent_mono
        (r n) (s n) (s n + t n) (lower n) (upper n)
        (Nat.le_max_left _ _)))
  have hlowerLimit : Tendsto (fun n ↦ 1 - epsilon n)
      atTop (nhds 1) := by
    have hepsilonZero : Tendsto epsilon atTop (nhds 0) := by
      simpa only [epsilon] using
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := Real))
    simpa using (tendsto_const_nhds (x := (1 : Real))).sub hepsilonZero
  refine ⟨lower, upper, width, fun n ↦ Nat.le_max_right _ _, hlower, ?_⟩
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le
    hlowerLimit tendsto_const_nhds (fun n ↦ le_of_lt (hprob' n))
      (fun _ ↦ measureReal_le_one)



theorem PeriodicPlaneEmbedding.finiteStripJoinedBoundaryArmEvent_openWalks
    (E : PeriodicPlaneEmbedding P) {omega : ConfigSpace (Sym2 V)}
    {r c d : Real} {n : Nat} {L R : Finset V}
    (h : omega ∈ E.finiteStripJoinedBoundaryArmEvent r c d n L R) :
    ∃ b ∈ E.lowerBoundaryRayVertices r c,
      ∃ u ∈ E.upperBoundaryRayVertices r d,
        ∃ j : V,
          ∃ lower : (P.openSubgraph omega).Walk b j,
          ∃ upper : (P.openSubgraph omega).Walk u j,
            j ∈ L ∧
            (∀ v ∈ lower.support,
              v ∈ E.rightHalfPlaneStripVertices r n) ∧
            ∀ v ∈ upper.support,
              v ∈ E.rightHalfPlaneStripVertices r n := by
  obtain ⟨x, hxL, hxinf, b, hb, hxb⟩ := h.1.1
  obtain ⟨y, hyR, hyinf, u, hu, hyu⟩ := h.1.2
  have hxy : omega ∈ P.connectedWithinSet
      (E.rightHalfPlaneStripVertices r n) x y := by
    by_contra hnot
    apply h.2
    apply Set.mem_iUnion.2
    refine ⟨⟨(x, y), Finset.mem_product.2 ⟨hxL, hyR⟩⟩, ?_⟩
    exact ⟨⟨hxinf, hyinf⟩, hnot⟩
  obtain ⟨qxb, hqxb⟩ := P.connectedWithinSet_exists_openSubgraphWalk hxb
  obtain ⟨qyu, hqyu⟩ := P.connectedWithinSet_exists_openSubgraphWalk hyu
  obtain ⟨qxy, hqxy⟩ := P.connectedWithinSet_exists_openSubgraphWalk hxy
  let lower := qxb.reverse
  let upper := qyu.reverse.append qxy.reverse
  refine ⟨b, hb, u, hu, x, lower, upper, hxL, ?_, ?_⟩
  · intro v hv
    exact hqxb v (by simpa [lower] using hv)
  · intro v hv
    rw [SimpleGraph.Walk.support_append] at hv
    rcases List.mem_append.mp hv with hv | hv
    · exact hqyu v (by simpa using hv)
    · have hv' : v ∈ qxy.reverse.support := List.mem_of_mem_tail hv
      exact hqxy v (by simpa using hv')


theorem PeriodicPlaneEmbedding.finiteStripJoinedBoundaryArmEvent_graphWalks
    (E : PeriodicPlaneEmbedding P) {omega : ConfigSpace (Sym2 V)}
    {r c d : Real} {n : Nat} {L R : Finset V}
    (h : omega ∈ E.finiteStripJoinedBoundaryArmEvent r c d n L R) :
    ∃ b ∈ E.lowerBoundaryRayVertices r c,
      ∃ u ∈ E.upperBoundaryRayVertices r d,
        ∃ j : V, ∃ lower : P.graph.Walk b j,
          ∃ upper : P.graph.Walk u j,
            j ∈ L ∧
            (∀ {x y : V}, s(x, y) ∈ lower.edges →
              omega s(x, y) = true) ∧
            (∀ {x y : V}, s(x, y) ∈ upper.edges →
              omega s(x, y) = true) ∧
            (∀ v ∈ lower.support,
              v ∈ E.rightHalfPlaneStripVertices r n) ∧
            ∀ v ∈ upper.support,
              v ∈ E.rightHalfPlaneStripVertices r n := by
  obtain ⟨b, hb, u, hu, j, lower₀, upper₀, hjL,
    hlowerS, hupperS⟩ := E.finiteStripJoinedBoundaryArmEvent_openWalks h
  obtain ⟨lower, hlowerSupport, hlowerOpen⟩ :=
    P.openSubgraphWalk_exists_graphWalk omega lower₀
  obtain ⟨upper, hupperSupport, hupperOpen⟩ :=
    P.openSubgraphWalk_exists_graphWalk omega upper₀
  refine ⟨b, hb, u, hu, j, lower, upper, hjL,
    hlowerOpen, hupperOpen, ?_, ?_⟩
  · intro v hv
    exact hlowerS v (by rwa [← hlowerSupport])
  · intro v hv
    exact hupperS v (by rwa [← hupperSupport])



theorem PeriodicPlaneEmbedding.walkArc_horizontal_strict_bounds_of_strip
    (E : PeriodicPlaneEmbedding P) {B r : Real} {n : Nat} {x y : V}
    (hB : ∀ {u v : V} (huv : P.graph.Adj u v) (t) (i : Fin 2),
      |E.coordinates (E.edgeArc huv t - E.vertex u) i| ≤ B)
    (hB0 : 0 ≤ B)
    (p : P.graph.Walk x y)
    (hp : ∀ v ∈ p.support, v ∈ E.rightHalfPlaneStripVertices r n) :
    ∀ t : unitInterval,
      r - B - 1 < E.coordinates (E.walkArc p t) 0 ∧
        E.coordinates (E.walkArc p t) 0 < r + n + B + 1 := by
  intro t
  have hq : E.walkArc p t ∈ Set.range (E.walkArc p) := ⟨t, rfl⟩
  rcases E.mem_walkArc_range_cases p hq with hstart | hedge
  · have hx := hp x (by simp)
    change E.walkArc p t = E.vertex x at hstart
    rw [hstart]
    change r - B - 1 < E.vertexCoord x 0 ∧
      E.vertexCoord x 0 < r + (n : Real) + B + 1
    rcases hx with ⟨hxr, hxn⟩
    change E.vertexCoord x 0 ≤ r + (n : Real) at hxn
    change r ≤ E.vertexCoord x 0 at hxr
    constructor <;> linarith
  · obtain ⟨u, v, huv, hedge, q, hq⟩ := hedge
    have hu := hp u (p.fst_mem_support_of_mem_edges hedge)
    have hlo := E.vertex_sub_le_edgeArc_coord hB huv q (0 : Fin 2)
    have hhi := E.edgeArc_coord_le_vertex_add hB huv q (0 : Fin 2)
    change E.edgeArc huv q = E.walkArc p t at hq
    rw [← hq]
    rcases hu with ⟨hur, hun⟩
    change r ≤ E.vertexCoord u 0 at hur
    change E.vertexCoord u 0 ≤ r + (n : Real) at hun
    constructor <;> linarith



theorem PeriodicPlaneEmbedding.finiteStripJoinedBoundaryArmEvent_barrierGeometry
    (E : PeriodicPlaneEmbedding P) {omega : ConfigSpace (Sym2 V)}
    {B r c d : Real} {n : Nat} {L R : Finset V}
    (hB : ∀ {x y : V} (hxy : P.graph.Adj x y) (t) (i : Fin 2),
      |E.coordinates (E.edgeArc hxy t - E.vertex x) i| ≤ B)
    (hB0 : 0 ≤ B)
    (hcd : c < d)
    (hLdeep : (L : Set V) ⊆ E.rightHalfPlaneVertices (r + B))
    (h : omega ∈ E.finiteStripJoinedBoundaryArmEvent r c d n L R) :
    let a := r - B - 1
    let b := r + n + B + 1
    let C := (2 * c + d) / 3
    let D := (c + 2 * d) / 3
    a < b ∧ C < D ∧
      ∃ xl xu xj : V, ∃ lower : P.graph.Walk xl xj,
        ∃ upper : P.graph.Walk xu xj,
          ¬ lower.Nil ∧ ¬ upper.Nil ∧
          (∀ {x y : V}, s(x, y) ∈ lower.edges →
            omega s(x, y) = true) ∧
          (∀ {x y : V}, s(x, y) ∈ upper.edges →
            omega s(x, y) = true) ∧
          E.vertexCoord xl 1 < C ∧ D < E.vertexCoord xu 1 ∧
          (∀ t : unitInterval,
            a < E.coordinates (E.walkArc lower t) 0 ∧
              E.coordinates (E.walkArc lower t) 0 < b) ∧
          ∀ t : unitInterval,
            a < E.coordinates (E.walkArc upper t) 0 ∧
              E.coordinates (E.walkArc upper t) 0 < b := by
  dsimp only
  obtain ⟨xl, hxl, xu, hxu, xj, lower, upper, hxjL,
    hlowerOpen, hupperOpen, hlowerS, hupperS⟩ :=
      E.finiteStripJoinedBoundaryArmEvent_graphWalks h
  have hxjDeep := hLdeep hxjL
  have hxlRight := E.rightHalfPlaneBoundary_coord_lt hB hxl.1
  have hxuRight := E.rightHalfPlaneBoundary_coord_lt hB hxu.1
  have hlowerNil : ¬ lower.Nil := by
    apply SimpleGraph.Walk.not_nil_of_ne
    intro heq
    subst xj
    exact (not_lt_of_ge hxjDeep) hxlRight
  have hupperNil : ¬ upper.Nil := by
    apply SimpleGraph.Walk.not_nil_of_ne
    intro heq
    subst xj
    exact (not_lt_of_ge hxjDeep) hxuRight
  have hxlC : E.vertexCoord xl 1 < (2 * c + d) / 3 := by
    have hxl' := hxl.2
    change E.vertexCoord xl 1 ≤ c at hxl'
    linarith
  have hDxu : (c + 2 * d) / 3 < E.vertexCoord xu 1 := by
    have hxu' := hxu.2
    change d ≤ E.vertexCoord xu 1 at hxu'
    linarith
  refine ⟨?_, by linarith, xl, xu, xj, lower, upper,
    hlowerNil, hupperNil, hlowerOpen, hupperOpen,
    hxlC, hDxu, ?_, ?_⟩
  · have hn0 : (0 : Real) ≤ n := by positivity
    linarith
  · exact E.walkArc_horizontal_strict_bounds_of_strip hB hB0 lower hlowerS
  · exact E.walkArc_horizontal_strict_bounds_of_strip hB hB0 upper hupperS

end StatMech.FK.PeriodicPlanar

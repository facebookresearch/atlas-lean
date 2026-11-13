/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FK.PeriodicPlanarSheffieldHalfPlaneInfiniteArm
import Code.FK.PeriodicPlanarSheffieldHalfPlaneStripUnion









open Filter MeasureTheory Set SimpleGraph Topology

namespace StatMech.FK.PeriodicPlanar

open BeffaraDC Lattice

variable {V : Type*} [DecidableEq V] [Countable V]
  {P : PeriodicGraph V}





def walkOfChain (G : SimpleGraph V) (x : V) :
    (l : List V) → List.IsChain G.Adj (x :: l) →
      G.Walk x ((x :: l).getLast (List.cons_ne_nil _ _))
  | [], _ => .nil
  | y :: l, h => by
      have h' : G.Adj x y ∧ List.IsChain G.Adj (y :: l) := by
        simpa only [List.isChain_cons_cons] using h
      exact .cons h'.1 (walkOfChain G y l h'.2)

@[simp] theorem walkOfChain_support (G : SimpleGraph V) (x : V)
    (l : List V) (h : List.IsChain G.Adj (x :: l)) :
    (walkOfChain G x l h).support = x :: l := by
  induction l generalizing x with
  | nil => rfl
  | cons y l ih =>
      have h' : G.Adj x y ∧ List.IsChain G.Adj (y :: l) := by
        simpa only [List.isChain_cons_cons] using h
      simp only [walkOfChain, SimpleGraph.Walk.support_cons]
      congr 1
      exact ih y _



theorem PeriodicGraph.connectedWithinSet_exists_openSubgraphWalk
    (P : PeriodicGraph V) {omega : ConfigSpace (Sym2 V)}
    {A : Set V} {x y : V}
    (h : omega ∈ P.connectedWithinSet A x y) :
    ∃ q : (P.openSubgraph omega).Walk x y,
      ∀ v ∈ q.support, v ∈ A := by
  rcases h with ⟨l, hchain, hlast, hregion⟩
  let q₀ := walkOfChain (P.openSubgraph omega) x l hchain
  let q : (P.openSubgraph omega).Walk x y := q₀.copy rfl hlast
  refine ⟨q, ?_⟩
  intro v hv
  apply hregion v
  have hv₀ : v ∈ q₀.support := by
    simpa only [q, SimpleGraph.Walk.support_copy] using hv
  rwa [walkOfChain_support] at hv₀



theorem PeriodicGraph.openSubgraphWalk_exists_graphWalk
    (P : PeriodicGraph V) (omega : ConfigSpace (Sym2 V)) {x y : V}
    (q : (P.openSubgraph omega).Walk x y) :
    ∃ qG : P.graph.Walk x y,
      qG.support = q.support ∧
      ∀ {u v : V}, s(u, v) ∈ qG.edges → omega s(u, v) = true := by
  have hle : P.openSubgraph omega ≤ P.graph := by
    intro u v huv
    exact huv.1
  have hedge : ∀ e, e ∈ q.edges → e ∈ P.graph.edgeSet := by
    intro e he
    exact SimpleGraph.edgeSet_mono hle (q.edges_subset_edgeSet he)
  let qG := q.transfer P.graph hedge
  refine ⟨qG, by simp [qG], ?_⟩
  intro u v huv
  have huv' : s(u, v) ∈ q.edges := by
    simpa [qG] using huv
  have hadj := q.adj_of_mem_edges huv'
  exact hadj.2



def PeriodicPlaneEmbedding.finiteJoinedBoundaryArmEvent
    (E : PeriodicPlaneEmbedding P) (r c d : Real) (n : Nat)
    (L R : Finset V) : Set (ConfigSpace (Sym2 V)) :=
  (P.infiniteSetConnectionWithin (E.rightHalfPlaneVertices r) (L : Set V)
      (E.lowerBoundaryRayVertices r c) ∩
    P.infiniteSetConnectionWithin (E.rightHalfPlaneVertices r) (R : Set V)
      (E.upperBoundaryRayVertices r d)) \
    E.halfPlaneStripPairMergeErrorUnion r n L R

theorem PeriodicPlaneEmbedding.finiteJoinedBoundaryArmEvent_measurableSet
    (E : PeriodicPlaneEmbedding P) (r c d : Real) (n : Nat)
    (L R : Finset V) :
    MeasurableSet (E.finiteJoinedBoundaryArmEvent r c d n L R) :=
  ((P.infiniteSetConnectionWithin_measurableSet
      (E.rightHalfPlaneVertices r) (L : Set V)
      (E.lowerBoundaryRayVertices r c)).inter
    (P.infiniteSetConnectionWithin_measurableSet
      (E.rightHalfPlaneVertices r) (R : Set V)
      (E.upperBoundaryRayVertices r d))).diff
    (E.halfPlaneStripPairMergeErrorUnion_measurableSet r n L R)



theorem PeriodicPlaneEmbedding.finiteJoinedBoundaryArmEvent_witnesses
    (E : PeriodicPlaneEmbedding P) {omega : ConfigSpace (Sym2 V)}
    {r c d : Real} {n : Nat} {L R : Finset V}
    (h : omega ∈ E.finiteJoinedBoundaryArmEvent r c d n L R) :
    ∃ x ∈ L, (P.cluster omega x).Infinite ∧
      ∃ b ∈ E.lowerBoundaryRayVertices r c,
        omega ∈ P.connectedWithinSet (E.rightHalfPlaneVertices r) x b ∧
      ∃ y ∈ R, (P.cluster omega y).Infinite ∧
        ∃ u ∈ E.upperBoundaryRayVertices r d,
          omega ∈ P.connectedWithinSet (E.rightHalfPlaneVertices r) y u ∧
          omega ∈ P.connectedWithinSet
            (E.rightHalfPlaneStripVertices r n) x y := by
  rcases h.1.1 with ⟨x, hxL, hxinf, b, hb, hxb⟩
  rcases h.1.2 with ⟨y, hyR, hyinf, u, hu, hyu⟩
  have hxy : omega ∈ P.connectedWithinSet
      (E.rightHalfPlaneStripVertices r n) x y := by
    by_contra hnot
    apply h.2
    apply Set.mem_iUnion.2
    refine ⟨⟨(x, y), Finset.mem_product.2 ⟨hxL, hyR⟩⟩, ?_⟩
    exact ⟨⟨hxinf, hyinf⟩, hnot⟩
  exact ⟨x, hxL, hxinf, b, hb, hxb, y, hyR, hyinf,
    u, hu, hyu, hxy⟩



theorem PeriodicPlaneEmbedding.finiteJoinedBoundaryArmEvent_openWalks
    (E : PeriodicPlaneEmbedding P) {omega : ConfigSpace (Sym2 V)}
    {r c d : Real} {n : Nat} {L R : Finset V}
    (h : omega ∈ E.finiteJoinedBoundaryArmEvent r c d n L R) :
    ∃ b ∈ E.lowerBoundaryRayVertices r c,
      ∃ u ∈ E.upperBoundaryRayVertices r d,
        ∃ j : V,
          ∃ lower : (P.openSubgraph omega).Walk b j,
          ∃ upper : (P.openSubgraph omega).Walk u j,
            j ∈ L ∧
            (∀ v ∈ lower.support, v ∈ E.rightHalfPlaneVertices r) ∧
            (∀ v ∈ upper.support, v ∈ E.rightHalfPlaneVertices r) := by
  obtain ⟨x, hxL, _hxinf, b, hb, hxb,
    y, _hyR, _hyinf, u, hu, hyu, hxy⟩ :=
      E.finiteJoinedBoundaryArmEvent_witnesses h
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
    · have hv' : v ∈ qxy.reverse.support :=
        List.mem_of_mem_tail hv
      have hvxy : v ∈ qxy.support := by simpa using hv'
      exact E.rightHalfPlaneStripVertices_subset r n (hqxy v hvxy)




theorem PeriodicPlaneEmbedding.finiteJoinedBoundaryArmEvent_threeWallWalks
    (E : PeriodicPlaneEmbedding P) {omega : ConfigSpace (Sym2 V)}
    {r c d : Real} {n : Nat} {L R : Finset V}
    (h : omega ∈ E.finiteJoinedBoundaryArmEvent r c d n L R) :
    ∃ b ∈ E.lowerBoundaryRayVertices r c,
      ∃ u ∈ E.upperBoundaryRayVertices r d,
        ∃ x ∈ L, ∃ y ∈ R,
          ∃ lower : P.graph.Walk b x,
          ∃ right : P.graph.Walk x y,
          ∃ upper : P.graph.Walk y u,
            (∀ {v w : V}, s(v, w) ∈ lower.edges →
              omega s(v, w) = true) ∧
            (∀ {v w : V}, s(v, w) ∈ right.edges →
              omega s(v, w) = true) ∧
            (∀ {v w : V}, s(v, w) ∈ upper.edges →
              omega s(v, w) = true) ∧
            (∀ v ∈ lower.support, v ∈ E.rightHalfPlaneVertices r) ∧
            (∀ v ∈ right.support,
              v ∈ E.rightHalfPlaneStripVertices r n) ∧
            ∀ v ∈ upper.support, v ∈ E.rightHalfPlaneVertices r := by
  obtain ⟨x, hxL, _hxinf, b, hb, hxb,
    y, hyR, _hyinf, u, hu, hyu, hxy⟩ :=
      E.finiteJoinedBoundaryArmEvent_witnesses h
  obtain ⟨qxb, hqxb⟩ := P.connectedWithinSet_exists_openSubgraphWalk hxb
  obtain ⟨qxy, hqxy⟩ := P.connectedWithinSet_exists_openSubgraphWalk hxy
  obtain ⟨qyu, hqyu⟩ := P.connectedWithinSet_exists_openSubgraphWalk hyu
  obtain ⟨lower, hlowerSupport, hlowerOpen⟩ :=
    P.openSubgraphWalk_exists_graphWalk omega qxb.reverse
  obtain ⟨right, hrightSupport, hrightOpen⟩ :=
    P.openSubgraphWalk_exists_graphWalk omega qxy
  obtain ⟨upper, hupperSupport, hupperOpen⟩ :=
    P.openSubgraphWalk_exists_graphWalk omega qyu
  refine ⟨b, hb, u, hu, x, hxL, y, hyR,
    lower, right, upper, hlowerOpen, hrightOpen, hupperOpen, ?_, ?_, ?_⟩
  · intro v hv
    apply hqxb v
    rw [hlowerSupport] at hv
    simpa using hv
  · intro v hv
    exact hqxy v (hrightSupport ▸ hv)
  · intro v hv
    exact hqyu v (hupperSupport ▸ hv)




theorem PeriodicPlaneEmbedding.finiteJoinedBoundaryArmEvent_threeWallCrosscutWalk
    (E : PeriodicPlaneEmbedding P) {omega : ConfigSpace (Sym2 V)}
    {r c d : Real} {n : Nat} {L R : Finset V} (hcd : c < d)
    (h : omega ∈ E.finiteJoinedBoundaryArmEvent r c d n L R) :
    ∃ b ∈ E.lowerBoundaryRayVertices r c,
      ∃ u ∈ E.upperBoundaryRayVertices r d,
        ∃ x ∈ L, ∃ y ∈ R,
          ∃ p : P.graph.Walk b u,
            ¬ p.Nil ∧
            (∀ {v w : V}, s(v, w) ∈ p.edges →
              omega s(v, w) = true) ∧
            (∀ v ∈ p.support, v ∈ E.rightHalfPlaneVertices r) ∧
            x ∈ p.support ∧ y ∈ p.support := by
  obtain ⟨b, hb, u, hu, x, hxL, y, hyR, lower, right, upper,
    hlowerOpen, hrightOpen, hupperOpen, hlowerH, hrightS, hupperH⟩ :=
      E.finiteJoinedBoundaryArmEvent_threeWallWalks h
  let p : P.graph.Walk b u := lower.append (right.append upper)
  have hbu : b ≠ u := by
    intro hbu
    subst u
    have hbY := hb.2
    have huY := hu.2
    change E.vertexCoord b 1 ≤ c at hbY
    change d ≤ E.vertexCoord b 1 at huY
    linarith
  refine ⟨b, hb, u, hu, x, hxL, y, hyR, p,
    SimpleGraph.Walk.not_nil_of_ne hbu, ?_, ?_, ?_, ?_⟩
  · intro v w hvw
    simp only [p, SimpleGraph.Walk.edges_append] at hvw
    rcases List.mem_append.mp hvw with hvwLower | hvwRest
    · exact hlowerOpen hvwLower
    · rcases List.mem_append.mp hvwRest with hvwRight | hvwUpper
      · exact hrightOpen hvwRight
      · exact hupperOpen hvwUpper
  · intro v hv
    simp only [p, SimpleGraph.Walk.mem_support_append_iff] at hv
    rcases hv with hvLower | hvRest
    · exact hlowerH v hvLower
    · rcases hvRest with hvRight | hvUpper
      · exact E.rightHalfPlaneStripVertices_subset r n (hrightS v hvRight)
      · exact hupperH v hvUpper
  · dsimp only [p]
    simp only [SimpleGraph.Walk.mem_support_append_iff]
    exact Or.inr (Or.inl right.start_mem_support)
  · dsimp only [p]
    simp only [SimpleGraph.Walk.mem_support_append_iff]
    exact Or.inr (Or.inl right.end_mem_support)



theorem PeriodicPlaneEmbedding.finiteJoinedBoundaryArmEvent_graphWalks
    (E : PeriodicPlaneEmbedding P) {omega : ConfigSpace (Sym2 V)}
    {r c d : Real} {n : Nat} {L R : Finset V}
    (h : omega ∈ E.finiteJoinedBoundaryArmEvent r c d n L R) :
    ∃ b ∈ E.lowerBoundaryRayVertices r c,
      ∃ u ∈ E.upperBoundaryRayVertices r d,
        ∃ j : V,
          ∃ lower : P.graph.Walk b j,
          ∃ upper : P.graph.Walk u j,
            j ∈ L ∧
            (∀ {x y : V}, s(x, y) ∈ lower.edges →
              omega s(x, y) = true) ∧
            (∀ {x y : V}, s(x, y) ∈ upper.edges →
              omega s(x, y) = true) ∧
            (∀ v ∈ lower.support, v ∈ E.rightHalfPlaneVertices r) ∧
            (∀ v ∈ upper.support, v ∈ E.rightHalfPlaneVertices r) := by
  obtain ⟨b, hb, u, hu, j, lower₀, upper₀, hjL, hlowerH, hupperH⟩ :=
    E.finiteJoinedBoundaryArmEvent_openWalks h
  obtain ⟨lower, hlowerSupport, hlowerOpen⟩ :=
    P.openSubgraphWalk_exists_graphWalk omega lower₀
  obtain ⟨upper, hupperSupport, hupperOpen⟩ :=
    P.openSubgraphWalk_exists_graphWalk omega upper₀
  refine ⟨b, hb, u, hu, j, lower, upper, hjL,
    hlowerOpen, hupperOpen, ?_, ?_⟩
  · intro v hv
    exact hlowerH v (by rwa [← hlowerSupport])
  · intro v hv
    exact hupperH v (by rwa [← hupperSupport])



theorem PeriodicPlaneEmbedding.finiteJoinedBoundaryArmEvent_graphWalks_notNil
    (E : PeriodicPlaneEmbedding P) {omega : ConfigSpace (Sym2 V)}
    {B r c d : Real} {n : Nat} {L R : Finset V}
    (hB : ∀ {x y : V} (hxy : P.graph.Adj x y) (t) (i : Fin 2),
      |E.coordinates (E.edgeArc hxy t - E.vertex x) i| ≤ B)
    (hLdeep : (L : Set V) ⊆ E.rightHalfPlaneVertices (r + B))
    (h : omega ∈ E.finiteJoinedBoundaryArmEvent r c d n L R) :
    ∃ b ∈ E.lowerBoundaryRayVertices r c,
      ∃ u ∈ E.upperBoundaryRayVertices r d,
        ∃ j : V,
          ∃ lower : P.graph.Walk b j,
          ∃ upper : P.graph.Walk u j,
            ¬ lower.Nil ∧ ¬ upper.Nil ∧
            (∀ {x y : V}, s(x, y) ∈ lower.edges →
              omega s(x, y) = true) ∧
            (∀ {x y : V}, s(x, y) ∈ upper.edges →
              omega s(x, y) = true) ∧
            (∀ v ∈ lower.support, v ∈ E.rightHalfPlaneVertices r) ∧
            (∀ v ∈ upper.support, v ∈ E.rightHalfPlaneVertices r) := by
  obtain ⟨b, hb, u, hu, j, lower, upper, hjL,
    hlowerOpen, hupperOpen, hlowerH, hupperH⟩ :=
      E.finiteJoinedBoundaryArmEvent_graphWalks h
  have hjdeep := hLdeep hjL
  have hbRight := E.rightHalfPlaneBoundary_coord_lt hB hb.1
  have huRight := E.rightHalfPlaneBoundary_coord_lt hB hu.1
  have hbj : b ≠ j := by
    intro hbj
    subst j
    exact (not_lt_of_ge hjdeep) hbRight
  have huj : u ≠ j := by
    intro huj
    subst j
    exact (not_lt_of_ge hjdeep) huRight
  exact ⟨b, hb, u, hu, j, lower, upper,
    SimpleGraph.Walk.not_nil_of_ne hbj,
    SimpleGraph.Walk.not_nil_of_ne huj,
    hlowerOpen, hupperOpen, hlowerH, hupperH⟩


theorem PeriodicPlaneEmbedding.exists_walkArc_horizontal_strict_bounds
    (E : PeriodicPlaneEmbedding P) {x y z : V}
    (lower : P.graph.Walk x z) (upper : P.graph.Walk y z) :
    ∃ a b : Real, a < b ∧
      (∀ t : unitInterval,
        a < E.coordinates (E.walkArc lower t) 0 ∧
          E.coordinates (E.walkArc lower t) 0 < b) ∧
      (∀ t : unitInterval,
        a < E.coordinates (E.walkArc upper t) 0 ∧
          E.coordinates (E.walkArc upper t) 0 < b) := by
  let f : ℂ → Real := fun w => E.coordinates w 0
  let fl : unitInterval → Real := fun t => f (E.walkArc lower t)
  let fu : unitInterval → Real := fun t => f (E.walkArc upper t)
  have hf : Continuous f :=
    (continuous_apply 0).comp E.coordinates.continuous
  have hfl : Continuous fl := hf.comp (E.walkArc lower).continuous
  have hfu : Continuous fu := hf.comp (E.walkArc upper).continuous
  let K : Set Real := Set.range fl ∪ Set.range fu
  have hK : IsCompact K :=
    (isCompact_range hfl).union (isCompact_range hfu)
  obtain ⟨a₀, ha₀⟩ := hK.bddBelow
  obtain ⟨b₀, hb₀⟩ := hK.bddAbove
  refine ⟨a₀ - 1, b₀ + 1, ?_, ?_, ?_⟩
  · have hlow : a₀ ≤ fl 0 := ha₀ (Or.inl ⟨0, rfl⟩)
    have hupp : fl 0 ≤ b₀ := hb₀ (Or.inl ⟨0, rfl⟩)
    linarith
  · intro t
    have hlow : a₀ ≤ fl t := ha₀ (Or.inl ⟨t, rfl⟩)
    have hupp : fl t ≤ b₀ := hb₀ (Or.inl ⟨t, rfl⟩)
    dsimp only [fl, f] at hlow hupp
    constructor <;> linarith
  · intro t
    have hlow : a₀ ≤ fu t := ha₀ (Or.inr ⟨t, rfl⟩)
    have hupp : fu t ≤ b₀ := hb₀ (Or.inr ⟨t, rfl⟩)
    dsimp only [fu, f] at hlow hupp
    constructor <;> linarith



theorem PeriodicPlaneEmbedding.finiteJoinedBoundaryArmEvent_barrierReady
    (E : PeriodicPlaneEmbedding P) {omega : ConfigSpace (Sym2 V)}
    {B r c d : Real} {n : Nat} {L R : Finset V}
    (hB : ∀ {x y : V} (hxy : P.graph.Adj x y) (t) (i : Fin 2),
      |E.coordinates (E.edgeArc hxy t - E.vertex x) i| ≤ B)
    (hcd : c < d)
    (hLdeep : (L : Set V) ⊆ E.rightHalfPlaneVertices (r + B))
    (h : omega ∈ E.finiteJoinedBoundaryArmEvent r c d n L R) :
    ∃ a b C D : Real, a < b ∧ C < D ∧
      ∃ xl xu xj : V,
      ∃ lower : P.graph.Walk xl xj,
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
        (∀ t : unitInterval,
          a < E.coordinates (E.walkArc upper t) 0 ∧
            E.coordinates (E.walkArc upper t) 0 < b) := by
  obtain ⟨xl, hxl, xu, hxu, xj, lower, upper,
    hlowerNil, hupperNil, hlowerOpen, hupperOpen, _hlowerH, _hupperH⟩ :=
      E.finiteJoinedBoundaryArmEvent_graphWalks_notNil hB hLdeep h
  obtain ⟨a, b, hab, hlowerX, hupperX⟩ :=
    E.exists_walkArc_horizontal_strict_bounds lower upper
  let C := (2 * c + d) / 3
  let D := (c + 2 * d) / 3
  have hCD : C < D := by dsimp only [C, D]; linarith
  have hxlC : E.vertexCoord xl 1 < C := by
    have hxl' := hxl.2
    change E.vertexCoord xl 1 ≤ c at hxl'
    dsimp only [C]
    linarith
  have hDxu : D < E.vertexCoord xu 1 := by
    have hxu' := hxu.2
    change d ≤ E.vertexCoord xu 1 at hxu'
    dsimp only [D]
    linarith
  exact ⟨a, b, C, D, hab, hCD, xl, xu, xj, lower, upper,
    hlowerNil, hupperNil, hlowerOpen, hupperOpen,
    hxlC, hDxu, hlowerX, hupperX⟩


theorem PeriodicPlaneEmbedding.finiteJoinedBoundaryArmEvent_measureReal_ge
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (r c d : Real) (n : Nat) (L R : Finset V) :
    mu.real (P.infiniteSetConnectionWithin (E.rightHalfPlaneVertices r)
        (L : Set V) (E.lowerBoundaryRayVertices r c)) +
      mu.real (P.infiniteSetConnectionWithin (E.rightHalfPlaneVertices r)
        (R : Set V) (E.upperBoundaryRayVertices r d)) -
      mu.real (E.halfPlaneStripPairMergeErrorUnion r n L R) - 1 ≤
        mu.real (E.finiteJoinedBoundaryArmEvent r c d n L R) := by
  let A := P.infiniteSetConnectionWithin (E.rightHalfPlaneVertices r)
    (L : Set V) (E.lowerBoundaryRayVertices r c)
  let B := P.infiniteSetConnectionWithin (E.rightHalfPlaneVertices r)
    (R : Set V) (E.upperBoundaryRayVertices r d)
  let C := E.halfPlaneStripPairMergeErrorUnion r n L R
  have hthree := three_event_intersection_lower_bound mu
    (P.infiniteSetConnectionWithin_measurableSet
      (E.rightHalfPlaneVertices r) (R : Set V)
      (E.upperBoundaryRayVertices r d))
    (E.halfPlaneStripPairMergeErrorUnion_measurableSet r n L R).compl
    (A := A) (B := B) (C := Cᶜ)
  have hC : mu.real Cᶜ = 1 - mu.real C := by
    rw [measureReal_compl
      (E.halfPlaneStripPairMergeErrorUnion_measurableSet r n L R),
      probReal_univ]
  rw [hC] at hthree
  change mu.real A + mu.real B - mu.real C - 1 ≤
    mu.real ((A ∩ B) \ C)
  convert hthree using 1 <;> ring




theorem PeriodicPlaneEmbedding.finiteJoinedBoundaryArmEvent_measureReal_gt
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (r c d : Real) (n : Nat) (L R : Finset V) {epsilon : Real}
    (hL : 1 - epsilon < mu.real
      (P.infiniteSetConnectionWithin (E.rightHalfPlaneVertices r)
        (L : Set V) (E.lowerBoundaryRayVertices r c)))
    (hR : 1 - epsilon < mu.real
      (P.infiniteSetConnectionWithin (E.rightHalfPlaneVertices r)
        (R : Set V) (E.upperBoundaryRayVertices r d)))
    (hmerge : mu.real
      (E.halfPlaneStripPairMergeErrorUnion r n L R) < epsilon) :
    1 - 3 * epsilon <
      mu.real (E.finiteJoinedBoundaryArmEvent r c d n L R) := by
  have hbound := E.finiteJoinedBoundaryArmEvent_measureReal_ge
    mu r c d n L R
  linarith



theorem PeriodicPlaneEmbedding.exists_inward_finiteJoinedBoundaryArmEvent_measureReal_gt
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hFKG : IsFKG mu) (hTI : P.IsTranslationInvariant mu)
    (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
    (r : Real) (L : Finset V) {epsilon : Real} (hepsilon : 0 < epsilon) :
    ∃ z₀ : Site 2, ∃ z : Int, ∃ n : Nat,
      let S := L.image (P.shift z₀)
      let Slo := S.image (P.shift (verticalShift z))
      let Shi := (S.image (P.shift (verticalShift 1))).image
        (P.shift (verticalShift z))
      1 - 2 * Real.sqrt (1 - mu.real
          (P.infiniteSetConnectionWithin (E.rightHalfPlaneVertices r)
            (S : Set V) (E.rightHalfPlaneBoundaryVertices r))) -
          3 * epsilon <
        mu.real (E.finiteJoinedBoundaryArmEvent r 0 0 n Slo Shi) := by
  obtain ⟨z₀, n, _hSH, _hS1H, hmerge⟩ :=
    E.exists_inward_adjacent_stripPlacement
      mu hTI hunique r L hepsilon
  let S := L.image (P.shift z₀)
  obtain ⟨z, hlower, hupper⟩ :=
    E.exists_adjacent_infiniteBoundaryRays_measureReal_ge
      mu hFKG hTI r 0 (S : Set V) hepsilon
  let Slo := S.image (P.shift (verticalShift z))
  let Sone := S.image (P.shift (verticalShift 1))
  let Shi := Sone.image (P.shift (verticalShift z))
  have hShi : Shi = S.image (P.shift (verticalShift (z + 1))) := by
    ext y
    simp only [Shi, Sone, Finset.mem_image]
    constructor
    · rintro ⟨x, ⟨u, hu, rfl⟩, rfl⟩
      refine ⟨u, hu, ?_⟩
      rw [← P.shift_add]
      congr 2
      ext i
      fin_cases i <;> simp [verticalShift, add_comm]
    · rintro ⟨u, hu, rfl⟩
      refine ⟨P.shift (verticalShift 1) u, ⟨u, hu, rfl⟩, ?_⟩
      rw [← P.shift_add]
      congr 2
      ext i
      fin_cases i <;> simp [verticalShift, add_comm]
  have hmerge' : mu.real (E.halfPlaneStripPairMergeErrorUnion r n Slo Shi) <
      epsilon := by
    have hv := E.halfPlaneStripPairMergeErrorUnion_measureReal_vertical
      mu hTI z r n S Sone
    change mu.real (E.halfPlaneStripPairMergeErrorUnion r n Slo Shi) < epsilon
    change mu.real (E.halfPlaneStripPairMergeErrorUnion r n
      (S.image (P.shift (verticalShift z)))
      (Sone.image (P.shift (verticalShift z)))) < epsilon
    rw [hv]
    exact hmerge
  have hlower' : 1 - Real.sqrt (1 - mu.real
      (P.infiniteSetConnectionWithin (E.rightHalfPlaneVertices r)
        (S : Set V) (E.rightHalfPlaneBoundaryVertices r))) - epsilon ≤
      mu.real (P.infiniteSetConnectionWithin (E.rightHalfPlaneVertices r)
        (Slo : Set V) (E.lowerBoundaryRayVertices r 0)) := by
    simpa only [Slo, Finset.coe_image] using hlower
  have hupper' : 1 - Real.sqrt (1 - mu.real
      (P.infiniteSetConnectionWithin (E.rightHalfPlaneVertices r)
        (S : Set V) (E.rightHalfPlaneBoundaryVertices r))) - epsilon ≤
      mu.real (P.infiniteSetConnectionWithin (E.rightHalfPlaneVertices r)
        (Shi : Set V) (E.upperBoundaryRayVertices r 0)) := by
    rw [hShi]
    simpa only [Finset.coe_image] using hupper
  refine ⟨z₀, z, n, ?_⟩
  dsimp only
  have hbound := E.finiteJoinedBoundaryArmEvent_measureReal_ge
    mu r 0 0 n Slo Shi
  linarith




theorem PeriodicPlaneEmbedding.exists_inward_finiteJoinedBoundaryArmEvent_with_margin_measureReal_gt
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hFKG : IsFKG mu) (hTI : P.IsTranslationInvariant mu)
    (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
    {r R : Real} (hrR : r ≤ R) (L : Finset V)
    {epsilon : Real} (hepsilon : 0 < epsilon) :
    ∃ z₀ : Site 2, ∃ z : Int, ∃ n : Nat,
      let S := L.image (P.shift z₀)
      let Slo := S.image (P.shift (verticalShift z))
      let Shi := (S.image (P.shift (verticalShift 2))).image
        (P.shift (verticalShift z))
      (S : Set V) ⊆ E.rightHalfPlaneVertices R ∧
      (Slo : Set V) ⊆ E.rightHalfPlaneVertices R ∧
      1 - 2 * Real.sqrt (1 - mu.real
          (P.infiniteSetConnectionWithin (E.rightHalfPlaneVertices r)
            (S : Set V) (E.rightHalfPlaneBoundaryVertices r))) -
          3 * epsilon <
        mu.real (E.finiteJoinedBoundaryArmEvent r 0 1 n Slo Shi) := by
  obtain ⟨z₀, n, hSH, _hS1H, hmerge⟩ :=
    E.exists_inward_twoStep_stripPlacement_with_margin
      mu hTI hunique hrR L hepsilon
  let S := L.image (P.shift z₀)
  obtain ⟨z, hlower, hupper⟩ :=
    E.exists_twoStep_infiniteBoundaryRays_measureReal_ge
      mu hFKG hTI r (S : Set V) hepsilon
  let Slo := S.image (P.shift (verticalShift z))
  let Stwo := S.image (P.shift (verticalShift 2))
  let Shi := Stwo.image (P.shift (verticalShift z))
  have hShi : Shi = S.image (P.shift (verticalShift (z + 2))) := by
    ext y
    simp only [Shi, Stwo, Finset.mem_image]
    constructor
    · rintro ⟨x, ⟨u, hu, rfl⟩, rfl⟩
      refine ⟨u, hu, ?_⟩
      rw [← P.shift_add]
      congr 2
      ext i
      fin_cases i <;> simp [verticalShift, add_comm]
    · rintro ⟨u, hu, rfl⟩
      refine ⟨P.shift (verticalShift 2) u, ⟨u, hu, rfl⟩, ?_⟩
      rw [← P.shift_add]
      congr 2
      ext i
      fin_cases i <;> simp [verticalShift, add_comm]
  have hSloR : (Slo : Set V) ⊆ E.rightHalfPlaneVertices R := by
    intro x hx
    change x ∈ S.image (P.shift (verticalShift z)) at hx
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hx
    exact (E.shift_mem_rightHalfPlaneVertices_vertical z R u).mpr (hSH hu)
  have hmerge' : mu.real (E.halfPlaneStripPairMergeErrorUnion r n Slo Shi) <
      epsilon := by
    have hv := E.halfPlaneStripPairMergeErrorUnion_measureReal_vertical
      mu hTI z r n S Stwo
    change mu.real (E.halfPlaneStripPairMergeErrorUnion r n
      (S.image (P.shift (verticalShift z)))
      (Stwo.image (P.shift (verticalShift z)))) < epsilon
    rw [hv]
    exact hmerge
  have hlower' : 1 - Real.sqrt (1 - mu.real
      (P.infiniteSetConnectionWithin (E.rightHalfPlaneVertices r)
        (S : Set V) (E.rightHalfPlaneBoundaryVertices r))) - epsilon ≤
      mu.real (P.infiniteSetConnectionWithin (E.rightHalfPlaneVertices r)
        (Slo : Set V) (E.lowerBoundaryRayVertices r 0)) := by
    simpa only [Slo, Finset.coe_image] using hlower
  have hupper' : 1 - Real.sqrt (1 - mu.real
      (P.infiniteSetConnectionWithin (E.rightHalfPlaneVertices r)
        (S : Set V) (E.rightHalfPlaneBoundaryVertices r))) - epsilon ≤
      mu.real (P.infiniteSetConnectionWithin (E.rightHalfPlaneVertices r)
        (Shi : Set V) (E.upperBoundaryRayVertices r 1)) := by
    rw [hShi]
    simpa only [Finset.coe_image] using hupper
  refine ⟨z₀, z, n, ?_⟩
  dsimp only
  refine ⟨hSH, hSloR, ?_⟩
  have hbound := E.finiteJoinedBoundaryArmEvent_measureReal_ge
    mu r 0 1 n Slo Shi
  linarith




theorem PeriodicPlaneEmbedding.exists_inward_separated_finiteJoinedBoundaryArmEvent_with_margin_measureReal_gt
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hFKG : IsFKG mu) (hTI : P.IsTranslationInvariant mu)
    (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
    {r R : Real} (hrR : r ≤ R) (s : Real) (t : Int) (L : Finset V)
    {epsilon : Real} (hepsilon : 0 < epsilon) :
    ∃ z₀ : Site 2, ∃ z : Int, ∃ n : Nat,
      let S := L.image (P.shift z₀)
      let Slo := S.image (P.shift (verticalShift z))
      let Shi := (S.image (P.shift (verticalShift (1 + t)))).image
        (P.shift (verticalShift z))
      (S : Set V) ⊆ E.rightHalfPlaneVertices R ∧
      (Slo : Set V) ⊆ E.rightHalfPlaneVertices R ∧
      1 - 2 * Real.sqrt (1 - mu.real
          (P.infiniteSetConnectionWithin (E.rightHalfPlaneVertices r)
            (S : Set V) (E.rightHalfPlaneBoundaryVertices r))) -
          3 * epsilon <
        mu.real (E.finiteJoinedBoundaryArmEvent r s (s + t) n Slo Shi) := by
  obtain ⟨z₀, n, hSH, _hSsepH, hmerge⟩ :=
    E.exists_inward_separated_stripPlacement_with_margin
      mu hTI hunique hrR t L hepsilon
  let S := L.image (P.shift z₀)
  obtain ⟨z, hlower, hupper⟩ :=
    E.exists_separated_infiniteBoundaryRays_measureReal_ge
      mu hFKG hTI r s t (S : Set V) hepsilon
  let Slo := S.image (P.shift (verticalShift z))
  let Ssep := S.image (P.shift (verticalShift (1 + t)))
  let Shi := Ssep.image (P.shift (verticalShift z))
  have hShi : Shi =
      S.image (P.shift (verticalShift (z + 1 + t))) := by
    ext y
    simp only [Shi, Ssep, Finset.mem_image]
    constructor
    · rintro ⟨x, ⟨u, hu, rfl⟩, rfl⟩
      refine ⟨u, hu, ?_⟩
      have hvec : verticalShift (1 + t) + verticalShift z =
          verticalShift (z + 1 + t) := by
        rw [← verticalShift_add]
        congr 1
        ring
      have hcomp :
        P.shift (verticalShift z)
            (P.shift (verticalShift (1 + t)) u) =
            P.shift (verticalShift (1 + t) + verticalShift z) u :=
          (P.shift_add _ _ _).symm
      rw [hvec] at hcomp
      exact hcomp.symm
    · rintro ⟨u, hu, rfl⟩
      refine ⟨P.shift (verticalShift (1 + t)) u, ⟨u, hu, rfl⟩, ?_⟩
      have hvec : verticalShift (1 + t) + verticalShift z =
          verticalShift (z + 1 + t) := by
        rw [← verticalShift_add]
        congr 1
        ring
      have hcomp :
        P.shift (verticalShift z)
            (P.shift (verticalShift (1 + t)) u) =
            P.shift (verticalShift (1 + t) + verticalShift z) u :=
          (P.shift_add _ _ _).symm
      rw [hvec] at hcomp
      exact hcomp
  have hSloR : (Slo : Set V) ⊆ E.rightHalfPlaneVertices R := by
    intro x hx
    change x ∈ S.image (P.shift (verticalShift z)) at hx
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hx
    exact (E.shift_mem_rightHalfPlaneVertices_vertical z R u).mpr (hSH hu)
  have hmerge' : mu.real (E.halfPlaneStripPairMergeErrorUnion r n Slo Shi) <
      epsilon := by
    have hv := E.halfPlaneStripPairMergeErrorUnion_measureReal_vertical
      mu hTI z r n S Ssep
    change mu.real (E.halfPlaneStripPairMergeErrorUnion r n
      (S.image (P.shift (verticalShift z)))
      (Ssep.image (P.shift (verticalShift z)))) < epsilon
    rw [hv]
    exact hmerge
  have hlower' : 1 - Real.sqrt (1 - mu.real
      (P.infiniteSetConnectionWithin (E.rightHalfPlaneVertices r)
        (S : Set V) (E.rightHalfPlaneBoundaryVertices r))) - epsilon ≤
      mu.real (P.infiniteSetConnectionWithin (E.rightHalfPlaneVertices r)
        (Slo : Set V) (E.lowerBoundaryRayVertices r s)) := by
    simpa only [Slo, Finset.coe_image] using hlower
  have hupper' : 1 - Real.sqrt (1 - mu.real
      (P.infiniteSetConnectionWithin (E.rightHalfPlaneVertices r)
        (S : Set V) (E.rightHalfPlaneBoundaryVertices r))) - epsilon ≤
      mu.real (P.infiniteSetConnectionWithin (E.rightHalfPlaneVertices r)
        (Shi : Set V) (E.upperBoundaryRayVertices r (s + t))) := by
    rw [hShi]
    simpa only [Finset.coe_image] using hupper
  refine ⟨z₀, z, n, ?_⟩
  dsimp only
  refine ⟨hSH, hSloR, ?_⟩
  have hbound := E.finiteJoinedBoundaryArmEvent_measureReal_ge
    mu r s (s + t) n Slo Shi
  linarith

end StatMech.FK.PeriodicPlanar

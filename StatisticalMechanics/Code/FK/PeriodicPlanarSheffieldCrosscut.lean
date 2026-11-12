/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FK.PeriodicPlanarSheffieldHalfPlaneBarrier
import Code.FK.PeriodicPlanarSheffieldHalfPlaneJoinedArms











open Set SimpleGraph Topology
open scoped unitInterval

namespace StatMech.FK.PeriodicPlanar

variable {V : Type*} [DecidableEq V] [Countable V]
  {P : PeriodicGraph V}




noncomputable def PeriodicPlaneEmbedding.simpleWalkArc
    (E : PeriodicPlaneEmbedding P) :
    ∀ {x y : V}, P.graph.Walk x y → Path (E.vertex x) (E.vertex y)
  | _, _, .nil => Path.refl _
  | _, _, .cons h .nil => E.edgeArc h
  | _, _, .cons h (.cons h' p) =>
      (E.edgeArc h).trans (E.simpleWalkArc (.cons h' p))

@[simp] theorem PeriodicPlaneEmbedding.simpleWalkArc_nil
    (E : PeriodicPlaneEmbedding P) (x : V) :
    E.simpleWalkArc (.nil : P.graph.Walk x x) = Path.refl _ := rfl

@[simp] theorem PeriodicPlaneEmbedding.simpleWalkArc_single
    (E : PeriodicPlaneEmbedding P) {x y : V} (hxy : P.graph.Adj x y) :
    E.simpleWalkArc (.cons hxy .nil) = E.edgeArc hxy := rfl

@[simp] theorem PeriodicPlaneEmbedding.simpleWalkArc_cons_cons
    (E : PeriodicPlaneEmbedding P) {x y z w : V}
    (hxy : P.graph.Adj x y) (hyz : P.graph.Adj y z)
    (p : P.graph.Walk z w) :
    E.simpleWalkArc (.cons hxy (.cons hyz p)) =
      (E.edgeArc hxy).trans (E.simpleWalkArc (.cons hyz p)) := rfl



theorem PeriodicPlaneEmbedding.simpleWalkArc_range
    (E : PeriodicPlaneEmbedding P) {x y : V} (p : P.graph.Walk x y) :
    Set.range (E.simpleWalkArc p) = Set.range (E.walkArc p) := by
  induction p with
  | nil => rfl
  | @cons x y z hxy p ih =>
      cases p with
      | nil =>
          rw [E.simpleWalkArc_single, E.walkArc_cons, E.walkArc_nil,
            Path.trans_range]
          apply Set.Subset.antisymm
          · exact Set.subset_union_left
          · intro q hq
            rcases hq with hq | hq
            · exact hq
            · obtain ⟨t, rfl⟩ := hq
              refine ⟨1, ?_⟩
              simp
      | cons hyz p =>
          rw [E.simpleWalkArc_cons_cons, E.walkArc_cons,
            Path.trans_range, Path.trans_range, ih]



theorem PeriodicPlaneEmbedding.edgeArc_inter_simpleWalkArc_eq_join
    (E : PeriodicPlaneEmbedding P) {x y z : V}
    (hxy : P.graph.Adj x y) (p : P.graph.Walk y z)
    (hpath : (p.cons hxy).IsPath)
    {q : ℂ}
    (hqEdge : q ∈ Set.range (E.edgeArc hxy))
    (hqRest : q ∈ Set.range (E.simpleWalkArc p)) :
    q = E.vertex y := by
  have hp : p.IsPath := hpath.of_cons
  have hxNot : x ∉ p.support := (Walk.cons_isPath_iff hxy p).mp hpath |>.2
  have hqRest' : q ∈ Set.range (E.walkArc p) := by
    rwa [← E.simpleWalkArc_range p]
  rcases E.mem_walkArc_range_cases p hqRest' with hstart | hedge
  · simpa [hstart]
  · obtain ⟨u, v, huv, huvEdges, hqUV⟩ := hedge
    have hne : s(x, y) ≠ s(u, v) := by
      intro heq
      rw [Sym2.eq_iff] at heq
      rcases heq with heq | heq
      · apply hxNot
        simpa only [heq.1] using p.fst_mem_support_of_mem_edges huvEdges
      · apply hxNot
        simpa only [heq.1] using p.snd_mem_support_of_mem_edges huvEdges
    obtain ⟨w, hwXY, hwUV, hwq⟩ :=
      E.edgeArc_intersection hxy huv q hne hqEdge hqUV
    have huSupport : u ∈ p.support := p.fst_mem_support_of_mem_edges huvEdges
    have hvSupport : v ∈ p.support := p.snd_mem_support_of_mem_edges huvEdges
    have hwNeX : w ≠ x := by
      intro hwx
      subst w
      rcases hwUV with rfl | rfl
      · exact hxNot huSupport
      · exact hxNot hvSupport
    have hwy : w = y := hwXY.resolve_left hwNeX
    simpa [hwy] using hwq.symm



theorem pathTrans_injective_of_range_inter
    {X : Type*} [TopologicalSpace X] {x y z : X}
    (gamma : Path x y) (eta : Path y z)
    (hgamma : Function.Injective gamma)
    (heta : Function.Injective eta)
    (hinter : ∀ q, q ∈ Set.range gamma → q ∈ Set.range eta → q = y) :
    Function.Injective (gamma.trans eta) := by
  intro t s hts
  rw [Path.trans_apply, Path.trans_apply] at hts
  split_ifs at hts with ht hs
  · have hscaled := hgamma hts
    apply Subtype.ext
    exact (mul_left_cancel₀ (by norm_num : (2 : ℝ) ≠ 0)
      (congrArg Subtype.val hscaled))
  · let t2 : unitInterval := ⟨2 * (t : ℝ), by
        constructor <;> linarith [t.2.1, t.2.2]⟩
    let s2 : unitInterval := ⟨2 * (s : ℝ) - 1, by
        constructor <;> linarith [s.2.1, s.2.2]⟩
    change gamma t2 = eta s2 at hts
    have hjoin : gamma t2 = y := by
      apply hinter _ ⟨_, rfl⟩ ⟨_, hts.symm⟩
    have htOne :
        t2 = 1 := by
      apply hgamma
      simpa using hjoin
    have hsZero :
        s2 = 0 := by
      apply heta
      simpa using hts.symm.trans hjoin
    have htVal := congrArg Subtype.val htOne
    have hsVal := congrArg Subtype.val hsZero
    apply Subtype.ext
    dsimp only [t2, s2] at htVal hsVal ⊢
    norm_num at htVal hsVal
    linarith
  · let t2 : unitInterval := ⟨2 * (t : ℝ) - 1, by
        constructor <;> linarith [t.2.1, t.2.2]⟩
    let s2 : unitInterval := ⟨2 * (s : ℝ), by
        constructor <;> linarith [s.2.1, s.2.2]⟩
    change eta t2 = gamma s2 at hts
    have hjoin : gamma s2 = y := by
      apply hinter _ ⟨_, rfl⟩ ⟨_, hts⟩
    have htZero : t2 = 0 := by
      apply heta
      simpa using hts.trans hjoin
    have hsOne : s2 = 1 := by
      apply hgamma
      simpa using hjoin
    have htVal := congrArg Subtype.val htZero
    have hsVal := congrArg Subtype.val hsOne
    apply Subtype.ext
    dsimp only [t2, s2] at htVal hsVal ⊢
    norm_num at htVal hsVal
    linarith
  · have hscaled := heta hts
    apply Subtype.ext
    have := congrArg Subtype.val hscaled
    linarith



theorem PeriodicPlaneEmbedding.simpleWalkArc_injective_of_isPath
    (E : PeriodicPlaneEmbedding P) {x y : V}
    (p : P.graph.Walk x y) (hp : p.IsPath) (hnil : ¬ p.Nil) :
    Function.Injective (E.simpleWalkArc p) := by
  induction p with
  | nil => exact (hnil (by simp)).elim
  | @cons x y z hxy p ih =>
      cases p with
      | nil => exact E.edgeArc_injective hxy
      | @cons y z w hyz p =>
          rw [E.simpleWalkArc_cons_cons]
          apply pathTrans_injective_of_range_inter
          · exact E.edgeArc_injective hxy
          · exact ih hp.of_cons (by simp)
          · intro q hqEdge hqRest
            exact E.edgeArc_inter_simpleWalkArc_eq_join
              hxy (.cons hyz p) hp hqEdge hqRest



theorem PeriodicPlaneEmbedding.exists_injective_walkArc_toPath
    (E : PeriodicPlaneEmbedding P) {x y : V} (p : P.graph.Walk x y)
    (hxy : x ≠ y) :
    Function.Injective (E.simpleWalkArc (p.toPath : P.graph.Walk x y)) ∧
      (p.toPath : P.graph.Walk x y).edges ⊆ p.edges := by
  have hnil : ¬ (p.toPath : P.graph.Walk x y).Nil :=
    SimpleGraph.Walk.not_nil_of_ne hxy
  exact ⟨E.simpleWalkArc_injective_of_isPath (p.toPath : P.graph.Walk x y)
      p.toPath.isPath hnil,
    p.edges_toPath_subset⟩





theorem PeriodicPlaneEmbedding.finiteJoinedBoundaryArmEvent_simpleCrosscut
    (E : PeriodicPlaneEmbedding P) {omega : ConfigSpace (Sym2 V)}
    {r c d : Real} {n : Nat} {L R : Finset V} (hcd : c < d)
    (h : omega ∈ E.finiteJoinedBoundaryArmEvent r c d n L R) :
    ∃ b ∈ E.lowerBoundaryRayVertices r c,
      ∃ u ∈ E.upperBoundaryRayVertices r d,
        ∃ q : P.graph.Walk b u,
          q.IsPath ∧ ¬ q.Nil ∧
          Function.Injective (E.simpleWalkArc q) ∧
          (∀ {x y : V}, s(x, y) ∈ q.edges →
            omega s(x, y) = true) ∧
          ∀ v ∈ q.support, v ∈ E.rightHalfPlaneVertices r := by
  obtain ⟨b, hb, u, hu, j, lower, upper, _hjL,
    hlowerOpen, hupperOpen, hlowerH, hupperH⟩ :=
      E.finiteJoinedBoundaryArmEvent_graphWalks h
  have hbu : b ≠ u := by
    intro hbu
    subst u
    have hbY := hb.2
    have huY := hu.2
    change E.vertexCoord b 1 ≤ c at hbY
    change d ≤ E.vertexCoord b 1 at huY
    linarith
  let joined : P.graph.Walk b u := lower.append upper.reverse
  let q : P.graph.Walk b u := joined.toPath
  have hqEdges : q.edges ⊆ joined.edges := by
    exact joined.edges_toPath_subset
  have hqSupport : q.support ⊆ joined.support := by
    exact joined.support_toPath_subset
  have hqNil : ¬ q.Nil := SimpleGraph.Walk.not_nil_of_ne hbu
  have hqPath : q.IsPath := by
    dsimp only [q]
    exact joined.toPath.isPath
  refine ⟨b, hb, u, hu, q, hqPath, hqNil,
    E.simpleWalkArc_injective_of_isPath q hqPath hqNil, ?_, ?_⟩
  · intro x y hxy
    have hxyJoined := hqEdges hxy
    simp only [joined, SimpleGraph.Walk.edges_append,
      SimpleGraph.Walk.edges_reverse] at hxyJoined
    rcases List.mem_append.mp hxyJoined with hxyLower | hxyUpper
    · exact hlowerOpen hxyLower
    · exact hupperOpen (by simpa using hxyUpper)
  · intro v hv
    have hvJoined := hqSupport hv
    simp only [joined, SimpleGraph.Walk.mem_support_append_iff] at hvJoined
    rcases hvJoined with hvLower | hvUpper
    · exact hlowerH v hvLower
    · exact hupperH v (by simpa using hvUpper)

variable {W : Type*} [DecidableEq W] [Countable W]
  {Pdual : PeriodicGraph W}

namespace PeriodicPlanarDualPair



theorem no_open_primal_dual_simpleWalkArc_crossing
    (D : PeriodicPlanarDualPair P Pdual)
    (omega : ConfigSpace (Sym2 V))
    {x y : V} {a b : W}
    (p : P.graph.Walk x y) (q : Pdual.graph.Walk a b)
    (hp : ¬ p.Nil) (hq : ¬ q.Nil)
    (hpopen : ∀ {u v : V}, s(u, v) ∈ p.edges →
      omega s(u, v) = true)
    (hqopen : ∀ {u v : W}, s(u, v) ∈ q.edges →
      dualConfigEquiv D.edgeDual omega s(u, v) = true) :
    Disjoint (Set.range (D.primalEmbedding.simpleWalkArc p))
      (Set.range (D.dualEmbedding.simpleWalkArc q)) := by
  rw [D.primalEmbedding.simpleWalkArc_range,
    D.dualEmbedding.simpleWalkArc_range]
  exact D.no_open_primal_dual_walkArc_crossing
    omega p q hp hq hpopen hqopen

end PeriodicPlanarDualPair

end StatMech.FK.PeriodicPlanar

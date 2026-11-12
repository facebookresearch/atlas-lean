/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






import Code.FK.PeriodicPlanarCoverage
import Code.FK.ContinuousRectangleCrossing
import Code.Foundations.Ergodicity

open Filter MeasureTheory Set SimpleGraph Topology

namespace StatMech.FK.PeriodicPlanar

open BeffaraDC Lattice

variable {V W : Type*} [DecidableEq V] [DecidableEq W]
  [Countable V] [Countable W]
  {P : PeriodicGraph V} {Pdual : PeriodicGraph W}




noncomputable def PeriodicPlaneEmbedding.vertexCoord
    (E : PeriodicPlaneEmbedding P) (x : V) : Fin 2 → ℝ :=
  E.coordinates (E.vertex x)

@[simp] theorem PeriodicPlaneEmbedding.vertexCoord_shift
    (E : PeriodicPlaneEmbedding P) (z : Site 2) (x : V) (i : Fin 2) :
    E.vertexCoord (P.shift z x) i = E.vertexCoord x i + z i := by
  rw [PeriodicPlaneEmbedding.vertexCoord, E.vertex_shift,
    map_add]
  change E.coordinates (E.vertex x) i + E.coordinates (E.period z) i =
    E.vertexCoord x i + z i
  rw [E.coordinates_period]
  rfl








noncomputable def PeriodicPlaneEmbedding.fundamentalArcDisplacements
    (E : PeriodicPlaneEmbedding P) : Set (Fin 2 → ℝ) := by
  letI : SimpleGraph.LocallyFinite P.graph := P.locallyFinite
  letI : DecidableRel P.graph.Adj := Classical.decRel _
  exact ⋃ u ∈ P.fundamentalDomain, ⋃ y ∈ P.graph.neighborFinset u,
    if h : P.graph.Adj u y then
      Set.range (fun t => E.coordinates (E.edgeArc h t - E.vertex u))
    else ∅

theorem PeriodicPlaneEmbedding.fundamentalArcDisplacements_isCompact
    (E : PeriodicPlaneEmbedding P) :
    IsCompact E.fundamentalArcDisplacements := by
  letI : SimpleGraph.LocallyFinite P.graph := P.locallyFinite
  letI : DecidableRel P.graph.Adj := Classical.decRel _
  unfold PeriodicPlaneEmbedding.fundamentalArcDisplacements
  apply Finset.isCompact_biUnion
  intro u hu
  apply Finset.isCompact_biUnion
  intro y hy
  split_ifs with h
  · simpa only [Set.image_univ] using isCompact_univ.image
      (E.coordinates.continuous.comp
        ((E.edgeArc h).continuous.sub continuous_const))
  · exact isCompact_empty



theorem PeriodicPlaneEmbedding.exists_edgeArc_displacement_bound
    (E : PeriodicPlaneEmbedding P) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ {x y : V} (hxy : P.graph.Adj x y) (t) (i : Fin 2),
      |E.coordinates (E.edgeArc hxy t - E.vertex x) i| ≤ B := by
  letI : SimpleGraph.LocallyFinite P.graph := P.locallyFinite
  letI : DecidableRel P.graph.Adj := Classical.decRel _
  obtain ⟨R, hR⟩ :=
    E.fundamentalArcDisplacements_isCompact.isBounded.subset_closedBall
      (0 : Fin 2 → ℝ)
  refine ⟨max R 0, le_max_right _ _, ?_⟩
  intro x y hxy t i
  obtain ⟨z, u, hu, hzu⟩ := P.covers x
  subst x
  let u₀ := P.shift (-z) (P.shift z u)
  let y₀ := P.shift (-z) y
  have hback : u₀ = u := by
    have h := P.shift_add z (-z) u
    rw [add_neg_cancel, P.shift_zero] at h
    exact (show P.shift (-z) (P.shift z u) = u from h.symm)
  have hu₀ : u₀ ∈ P.fundamentalDomain := by simpa only [hback] using hu
  let hbackEdge : P.graph.Adj u₀ y₀ :=
    (P.shift_adj (-z) (P.shift z u) y).2 hxy
  have ht : E.edgeArc hxy t + E.period (-z) ∈
      Set.range (E.edgeArc hbackEdge) := by
    have hrhs : E.edgeArc hxy t + E.period (-z) ∈
        (fun p => p + E.period (-z)) '' Set.range (E.edgeArc hxy) :=
      ⟨E.edgeArc hxy t, ⟨t, rfl⟩, rfl⟩
    rw [← E.edgeArc_shift (-z) hxy] at hrhs
    simpa only using hrhs
  obtain ⟨s, hs⟩ := ht
  have hdisp :
      E.coordinates (E.edgeArc hxy t - E.vertex (P.shift z u)) =
        E.coordinates (E.edgeArc hbackEdge s - E.vertex u₀) := by
    apply congrArg E.coordinates
    calc
      E.edgeArc hxy t - E.vertex (P.shift z u) =
          E.edgeArc hxy t - (E.vertex u + E.period z) :=
        congrArg (E.edgeArc hxy t - ·) (E.vertex_shift z u)
      _ = (E.edgeArc hxy t + E.period (-z)) - E.vertex u := by
        rw [map_neg]
        abel
      _ = E.edgeArc hbackEdge s - E.vertex u := by rw [hs]
      _ = E.edgeArc hbackEdge s - E.vertex u₀ :=
        congrArg (E.edgeArc hbackEdge s - ·)
          (congrArg E.vertex hback).symm
  have hmem : E.coordinates (E.edgeArc hbackEdge s - E.vertex u₀) ∈
      E.fundamentalArcDisplacements := by
    unfold PeriodicPlaneEmbedding.fundamentalArcDisplacements
    apply Set.mem_iUnion.2
    refine ⟨u₀, Set.mem_iUnion.2 ⟨hu₀, ?_⟩⟩
    apply Set.mem_iUnion.2
    refine ⟨y₀, Set.mem_iUnion.2 ⟨?_, ?_⟩⟩
    · exact (SimpleGraph.mem_neighborFinset P.graph u₀ y₀).2 hbackEdge
    · rw [dif_pos hbackEdge]
      exact ⟨s, rfl⟩
  have hnorm := hR hmem
  rw [Metric.mem_closedBall, dist_zero_right] at hnorm
  rw [hdisp]
  have hi : |E.coordinates (E.edgeArc hbackEdge s - E.vertex u₀) i| ≤
      ‖E.coordinates (E.edgeArc hbackEdge s - E.vertex u₀)‖ := by
    simpa only [Real.norm_eq_abs] using
      norm_le_pi_norm (E.coordinates (E.edgeArc hbackEdge s - E.vertex u₀)) i
  exact hi.trans (hnorm.trans (le_max_left _ _))


def PeriodicPlaneEmbedding.planeRect
    (E : PeriodicPlaneEmbedding P) (a b c d : ℝ) : Set ℂ :=
  {p | a ≤ E.coordinates p 0 ∧ E.coordinates p 0 ≤ b ∧
    c ≤ E.coordinates p 1 ∧ E.coordinates p 1 ≤ d}

theorem PeriodicPlaneEmbedding.edgeArc_mem_expanded_planeRect
    (E : PeriodicPlaneEmbedding P) {B : ℝ}
    (hB : ∀ {x y : V} (hxy : P.graph.Adj x y) (t) (i : Fin 2),
      |E.coordinates (E.edgeArc hxy t - E.vertex x) i| ≤ B)
    {a b c d : ℝ} {x y : V} (hxy : P.graph.Adj x y)
    (hx : E.vertex x ∈ E.planeRect a b c d) (t) :
    E.edgeArc hxy t ∈ E.planeRect (a - B) (b + B) (c - B) (d + B) := by
  have hcoord (i : Fin 2) :
      E.coordinates (E.edgeArc hxy t - E.vertex x) i =
        E.coordinates (E.edgeArc hxy t) i - E.vertexCoord x i := by
    simp [PeriodicPlaneEmbedding.vertexCoord, map_sub]
  have h₀ := hB hxy t (0 : Fin 2)
  have h₁ := hB hxy t (1 : Fin 2)
  rw [hcoord] at h₀ h₁
  have h₀' := (abs_le.mp h₀)
  have h₁' := (abs_le.mp h₁)
  change a ≤ E.vertexCoord x 0 ∧ E.vertexCoord x 0 ≤ b ∧
    c ≤ E.vertexCoord x 1 ∧ E.vertexCoord x 1 ≤ d at hx
  change a - B ≤ E.coordinates (E.edgeArc hxy t) 0 ∧
    E.coordinates (E.edgeArc hxy t) 0 ≤ b + B ∧
    c - B ≤ E.coordinates (E.edgeArc hxy t) 1 ∧
    E.coordinates (E.edgeArc hxy t) 1 ≤ d + B
  rcases hx with ⟨hxa, hxb, hxc, hxd⟩
  constructor
  · exact le_trans (sub_le_sub_right hxa B) (by linarith [h₀'.1])
  constructor
  · have ht : E.coordinates (E.edgeArc hxy t) 0 ≤
        E.vertexCoord x 0 + B := by linarith [h₀'.2]
    linarith [ht, hxb]
  constructor
  · exact le_trans (sub_le_sub_right hxc B) (by linarith [h₁'.1])
  · have ht : E.coordinates (E.edgeArc hxy t) 1 ≤
        E.vertexCoord x 1 + B := by linarith [h₁'.2]
    linarith [ht, hxd]

theorem PeriodicPlaneEmbedding.edgeArc_coord_le_vertex_add
    (E : PeriodicPlaneEmbedding P) {B : ℝ}
    (hB : ∀ {x y : V} (hxy : P.graph.Adj x y) (t) (i : Fin 2),
      |E.coordinates (E.edgeArc hxy t - E.vertex x) i| ≤ B)
    {x y : V} (hxy : P.graph.Adj x y) (t) (i : Fin 2) :
    E.coordinates (E.edgeArc hxy t) i ≤ E.vertexCoord x i + B := by
  change E.coordinates (E.edgeArc hxy t) i ≤
    E.coordinates (E.vertex x) i + B
  have h := (abs_le.mp (hB hxy t i)).2
  simp only [map_sub, Pi.sub_apply] at h
  linarith

theorem PeriodicPlaneEmbedding.vertex_sub_le_edgeArc_coord
    (E : PeriodicPlaneEmbedding P) {B : ℝ}
    (hB : ∀ {x y : V} (hxy : P.graph.Adj x y) (t) (i : Fin 2),
      |E.coordinates (E.edgeArc hxy t - E.vertex x) i| ≤ B)
    {x y : V} (hxy : P.graph.Adj x y) (t) (i : Fin 2) :
    E.vertexCoord x i - B ≤ E.coordinates (E.edgeArc hxy t) i := by
  change E.coordinates (E.vertex x) i - B ≤
    E.coordinates (E.edgeArc hxy t) i
  have h := (abs_le.mp (hB hxy t i)).1
  simp only [map_sub, Pi.sub_apply] at h
  linarith


noncomputable def PeriodicPlaneEmbedding.walkArc
    (E : PeriodicPlaneEmbedding P) :
    ∀ {x y : V}, P.graph.Walk x y → Path (E.vertex x) (E.vertex y)
  | _, _, .nil => Path.refl _
  | _, _, .cons h p => (E.edgeArc h).trans (E.walkArc p)

@[simp] theorem PeriodicPlaneEmbedding.walkArc_nil
    (E : PeriodicPlaneEmbedding P) (x : V) :
    E.walkArc (.nil : P.graph.Walk x x) = Path.refl _ := rfl

@[simp] theorem PeriodicPlaneEmbedding.walkArc_cons
    (E : PeriodicPlaneEmbedding P) {x y z : V}
    (hxy : P.graph.Adj x y) (p : P.graph.Walk y z) :
    E.walkArc (p.cons hxy) = (E.edgeArc hxy).trans (E.walkArc p) := rfl



theorem PeriodicPlaneEmbedding.mem_walkArc_range_cases
    (E : PeriodicPlaneEmbedding P) {x y : V} (p : P.graph.Walk x y)
    {q : ℂ} (hq : q ∈ Set.range (E.walkArc p)) :
    q = E.vertex x ∨
      ∃ u v : V, ∃ huv : P.graph.Adj u v,
        s(u, v) ∈ p.edges ∧ q ∈ Set.range (E.edgeArc huv) := by
  induction p with
  | @nil u =>
      left
      obtain ⟨t, rfl⟩ := hq
      rfl
  | @cons u v w huv p ih =>
      rw [PeriodicPlaneEmbedding.walkArc_cons, Path.trans_range] at hq
      rcases hq with hq | hq
      · right
        exact ⟨u, v, huv, by simp, hq⟩
      · rcases ih hq with hstart | hedge
        · right
          refine ⟨u, v, huv, by simp, ?_⟩
          refine ⟨1, ?_⟩
          simpa only [Path.target] using hstart.symm
        · obtain ⟨a, b, hab, habmem, hqedge⟩ := hedge
          right
          exact ⟨a, b, hab, by simp [habmem], hqedge⟩




theorem PeriodicPlaneEmbedding.mem_walkArc_range_of_not_nil
    (E : PeriodicPlaneEmbedding P) {x y : V} (p : P.graph.Walk x y)
    (hp : ¬ p.Nil) {q : ℂ} (hq : q ∈ Set.range (E.walkArc p)) :
    ∃ u v : V, ∃ huv : P.graph.Adj u v,
      s(u, v) ∈ p.edges ∧ q ∈ Set.range (E.edgeArc huv) := by
  rcases E.mem_walkArc_range_cases p hq with hstart | hedge
  · obtain ⟨v, huv, p', rfl⟩ := SimpleGraph.Walk.not_nil_iff.mp hp
    refine ⟨x, v, huv, by simp, ?_⟩
    refine ⟨0, ?_⟩
    simpa only [Path.source] using hstart.symm
  · exact hedge

theorem PeriodicPlaneEmbedding.walkArc_range_subset_expanded_planeRect
    (E : PeriodicPlaneEmbedding P) {B : ℝ}
    (hB0 : 0 ≤ B)
    (hB : ∀ {x y : V} (hxy : P.graph.Adj x y) (t) (i : Fin 2),
      |E.coordinates (E.edgeArc hxy t - E.vertex x) i| ≤ B)
    {a b c d : ℝ} {x y : V} (p : P.graph.Walk x y)
    (hp : ∀ v, v ∈ p.support → E.vertex v ∈ E.planeRect a b c d) :
    Set.range (E.walkArc p) ⊆
      E.planeRect (a - B) (b + B) (c - B) (d + B) := by
  induction p with
  | @nil u =>
      intro q hq
      obtain ⟨t, rfl⟩ := hq
      rw [PeriodicPlaneEmbedding.walkArc_nil]
      simp only [Path.refl_apply]
      have hx := hp u (by simp)
      change a ≤ E.vertexCoord u 0 ∧ E.vertexCoord u 0 ≤ b ∧
        c ≤ E.vertexCoord u 1 ∧ E.vertexCoord u 1 ≤ d at hx
      change a - B ≤ E.vertexCoord u 0 ∧ E.vertexCoord u 0 ≤ b + B ∧
        c - B ≤ E.vertexCoord u 1 ∧ E.vertexCoord u 1 ≤ d + B
      rcases hx with ⟨hxa, hxb, hxc, hxd⟩
      exact ⟨by linarith, by linarith, by linarith, by linarith⟩
  | @cons x y z hxy p ih =>
      rw [PeriodicPlaneEmbedding.walkArc_cons, Path.trans_range]
      intro q hq
      rcases hq with hq | hq
      · obtain ⟨t, rfl⟩ := hq
        exact E.edgeArc_mem_expanded_planeRect hB hxy
          (hp x (by simp)) t
      · exact ih (fun v hv => hp v (by simp [hv])) hq



def PeriodicPlaneEmbedding.rectVertices
    (E : PeriodicPlaneEmbedding P) (a b c d : ℝ) : Set V :=
  {x | a ≤ E.vertexCoord x 0 ∧ E.vertexCoord x 0 ≤ b ∧
    c ≤ E.vertexCoord x 1 ∧ E.vertexCoord x 1 ≤ d}

theorem PeriodicPlaneEmbedding.rectVertices_finite
    (E : PeriodicPlaneEmbedding P) (a b c d : ℝ) :
    (E.rectVertices a b c d).Finite := by
  let lo : Fin 2 → ℝ := fun i => if i = 0 then a else c
  let hi : Fin 2 → ℝ := fun i => if i = 0 then b else d
  let K : Set ℂ := E.coordinates.symm '' Set.Icc lo hi
  have hKcompact : IsCompact K :=
    isCompact_Icc.image E.coordinates.symm.continuous
  obtain ⟨R, hR⟩ := hKcompact.isBounded.subset_closedBall (0 : ℂ)
  apply (E.proper R).subset
  intro x hx
  change a ≤ E.vertexCoord x 0 ∧ E.vertexCoord x 0 ≤ b ∧
    c ≤ E.vertexCoord x 1 ∧ E.vertexCoord x 1 ≤ d at hx
  rcases hx with ⟨hxa, hxb, hxc, hxd⟩
  have hcoord : E.coordinates (E.vertex x) ∈ Set.Icc lo hi := by
    rw [Set.mem_Icc]
    constructor
    · intro i
      fin_cases i
      · simpa [lo, PeriodicPlaneEmbedding.vertexCoord] using hxa
      · simpa [lo, PeriodicPlaneEmbedding.vertexCoord] using hxc
    · intro i
      fin_cases i
      · simpa [hi, PeriodicPlaneEmbedding.vertexCoord] using hxb
      · simpa [hi, PeriodicPlaneEmbedding.vertexCoord] using hxd
  have hvK : (E.vertex x : ℂ) ∈ K := by
    refine ⟨E.coordinates (E.vertex x), hcoord, ?_⟩
    simp
  have hvball := hR hvK
  simpa [Metric.mem_closedBall, dist_zero_left] using hvball

abbrev PeriodicPlaneEmbedding.RectVertex
    (E : PeriodicPlaneEmbedding P) (a b c d : ℝ) :=
  E.rectVertices a b c d

noncomputable instance PeriodicPlaneEmbedding.instFintypeRectVertex
    (E : PeriodicPlaneEmbedding P) (a b c d : ℝ) :
    Fintype (E.RectVertex a b c d) :=
  (E.rectVertices_finite a b c d).fintype

instance PeriodicPlaneEmbedding.instDecidableEqRectVertex
    (E : PeriodicPlaneEmbedding P) (a b c d : ℝ) :
    DecidableEq (E.RectVertex a b c d) := Subtype.instDecidableEq


def PeriodicPlaneEmbedding.rectGraph
    (E : PeriodicPlaneEmbedding P) (a b c d : ℝ) :
    SimpleGraph (E.RectVertex a b c d) :=
  P.graph.induce (E.rectVertices a b c d)


def PeriodicPlaneEmbedding.openRectHom
    (E : PeriodicPlaneEmbedding P) (a b c d : ℝ)
    (eta : ConfigSpace (Sym2 (E.RectVertex a b c d))) :
    FK.openSub (E.rectGraph a b c d) eta →g P.graph where
  toFun := Subtype.val
  map_rel' := by
    intro x y hxy
    rw [FK.openSub_adj] at hxy
    exact SimpleGraph.induce_adj.mp hxy.1

theorem PeriodicPlaneEmbedding.openRectWalkArc_range_subset
    (E : PeriodicPlaneEmbedding P) {B : ℝ}
    (hB0 : 0 ≤ B)
    (hB : ∀ {x y : V} (hxy : P.graph.Adj x y) (t) (i : Fin 2),
      |E.coordinates (E.edgeArc hxy t - E.vertex x) i| ≤ B)
    {a b c d : ℝ} {eta : ConfigSpace (Sym2 (E.RectVertex a b c d))}
    {x y : E.RectVertex a b c d}
    (p : (FK.openSub (E.rectGraph a b c d) eta).Walk x y) :
    Set.range (E.walkArc (p.map (E.openRectHom a b c d eta))) ⊆
      E.planeRect (a - B) (b + B) (c - B) (d + B) := by
  apply E.walkArc_range_subset_expanded_planeRect hB0 hB
  intro v hv
  rw [SimpleGraph.Walk.support_map] at hv
  obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hv
  change a ≤ E.vertexCoord w.1 0 ∧ E.vertexCoord w.1 0 ≤ b ∧
    c ≤ E.vertexCoord w.1 1 ∧ E.vertexCoord w.1 1 ≤ d
  exact w.2


def PeriodicPlaneEmbedding.rectRestrict
    (E : PeriodicPlaneEmbedding P) (a b c d : ℝ)
    (omega : ConfigSpace (Sym2 V)) :
    ConfigSpace (Sym2 (E.RectVertex a b c d)) :=
  fun e => omega (Sym2.map Subtype.val e)

theorem PeriodicPlaneEmbedding.continuous_rectRestrict
    (E : PeriodicPlaneEmbedding P) (a b c d : ℝ) :
    Continuous (E.rectRestrict a b c d) :=
  continuous_pi fun e => continuous_apply (Sym2.map Subtype.val e)



theorem PeriodicPlaneEmbedding.openRectWalk_edge_open
    (E : PeriodicPlaneEmbedding P) {a b c d : ℝ}
    {omega : ConfigSpace (Sym2 V)}
    {x y : E.RectVertex a b c d}
    (p : (FK.openSub (E.rectGraph a b c d)
      (E.rectRestrict a b c d omega)).Walk x y)
    {u v : V}
    (huv : s(u, v) ∈
      (p.map (E.openRectHom a b c d
        (E.rectRestrict a b c d omega))).edges) :
    omega s(u, v) = true := by
  rw [SimpleGraph.Walk.edges_map] at huv
  obtain ⟨e, he, hmap⟩ := List.mem_map.mp huv
  induction e using Sym2.inductionOn with
  | _ r s =>
      have hrs := p.adj_of_mem_edges he
      rw [FK.openSub_adj] at hrs
      simp only [PeriodicPlaneEmbedding.rectRestrict,
        PeriodicPlaneEmbedding.openRectHom, Sym2.map_mk] at hrs hmap
      rw [← hmap]
      exact hrs.2



theorem PeriodicPlaneEmbedding.mem_openRectWalkArc_range
    (E : PeriodicPlaneEmbedding P) {a b c d : ℝ}
    {omega : ConfigSpace (Sym2 V)}
    {x y : E.RectVertex a b c d}
    (p : (FK.openSub (E.rectGraph a b c d)
      (E.rectRestrict a b c d omega)).Walk x y)
    (hp : ¬ (p.map (E.openRectHom a b c d
      (E.rectRestrict a b c d omega))).Nil)
    {q : ℂ}
    (hq : q ∈ Set.range (E.walkArc
      (p.map (E.openRectHom a b c d
        (E.rectRestrict a b c d omega))))) :
    ∃ u v : V, ∃ huv : P.graph.Adj u v,
      omega s(u, v) = true ∧ q ∈ Set.range (E.edgeArc huv) := by
  obtain ⟨u, v, huv, hedge, hqedge⟩ :=
    E.mem_walkArc_range_of_not_nil _ hp hq
  exact ⟨u, v, huv, E.openRectWalk_edge_open p hedge, hqedge⟩

def PeriodicPlaneEmbedding.rectLeftBoundary
    (E : PeriodicPlaneEmbedding P) (a b c d : ℝ)
    (x : E.RectVertex a b c d) : Prop :=
  ∃ y : V, P.graph.Adj x.1 y ∧ E.vertexCoord y 0 < a

def PeriodicPlaneEmbedding.rectRightBoundary
    (E : PeriodicPlaneEmbedding P) (a b c d : ℝ)
    (x : E.RectVertex a b c d) : Prop :=
  ∃ y : V, P.graph.Adj x.1 y ∧ b < E.vertexCoord y 0

def PeriodicPlaneEmbedding.rectBottomBoundary
    (E : PeriodicPlaneEmbedding P) (a b c d : ℝ)
    (x : E.RectVertex a b c d) : Prop :=
  ∃ y : V, P.graph.Adj x.1 y ∧ E.vertexCoord y 1 < c

def PeriodicPlaneEmbedding.rectTopBoundary
    (E : PeriodicPlaneEmbedding P) (a b c d : ℝ)
    (x : E.RectVertex a b c d) : Prop :=
  ∃ y : V, P.graph.Adj x.1 y ∧ d < E.vertexCoord y 1

theorem PeriodicPlaneEmbedding.rectLeftBoundary_coord_lt
    (E : PeriodicPlaneEmbedding P) {B a b c d : ℝ}
    (hB : ∀ {x y : V} (hxy : P.graph.Adj x y) (t) (i : Fin 2),
      |E.coordinates (E.edgeArc hxy t - E.vertex x) i| ≤ B)
    {x : E.RectVertex a b c d} (hx : E.rectLeftBoundary a b c d x) :
    E.vertexCoord x.1 0 < a + B := by
  obtain ⟨y, hxy, hy⟩ := hx
  have hd := hB hxy (1 : unitInterval) (0 : Fin 2)
  have heq : E.coordinates (E.edgeArc hxy (1 : unitInterval) - E.vertex x.1) 0 =
      E.vertexCoord y 0 - E.vertexCoord x.1 0 := by
    rw [Path.target]
    simp [PeriodicPlaneEmbedding.vertexCoord, map_sub]
  rw [heq] at hd
  have hd' := abs_le.mp hd
  linarith

theorem PeriodicPlaneEmbedding.rectRightBoundary_coord_gt
    (E : PeriodicPlaneEmbedding P) {B a b c d : ℝ}
    (hB : ∀ {x y : V} (hxy : P.graph.Adj x y) (t) (i : Fin 2),
      |E.coordinates (E.edgeArc hxy t - E.vertex x) i| ≤ B)
    {x : E.RectVertex a b c d} (hx : E.rectRightBoundary a b c d x) :
    b - B < E.vertexCoord x.1 0 := by
  obtain ⟨y, hxy, hy⟩ := hx
  have hd := hB hxy (1 : unitInterval) (0 : Fin 2)
  have heq : E.coordinates (E.edgeArc hxy (1 : unitInterval) - E.vertex x.1) 0 =
      E.vertexCoord y 0 - E.vertexCoord x.1 0 := by
    rw [Path.target]
    simp [PeriodicPlaneEmbedding.vertexCoord, map_sub]
  rw [heq] at hd
  have hd' := abs_le.mp hd
  linarith

theorem PeriodicPlaneEmbedding.rectBottomBoundary_coord_lt
    (E : PeriodicPlaneEmbedding P) {B a b c d : ℝ}
    (hB : ∀ {x y : V} (hxy : P.graph.Adj x y) (t) (i : Fin 2),
      |E.coordinates (E.edgeArc hxy t - E.vertex x) i| ≤ B)
    {x : E.RectVertex a b c d} (hx : E.rectBottomBoundary a b c d x) :
    E.vertexCoord x.1 1 < c + B := by
  obtain ⟨y, hxy, hy⟩ := hx
  have hd := hB hxy (1 : unitInterval) (1 : Fin 2)
  have heq : E.coordinates (E.edgeArc hxy (1 : unitInterval) - E.vertex x.1) 1 =
      E.vertexCoord y 1 - E.vertexCoord x.1 1 := by
    rw [Path.target]
    simp [PeriodicPlaneEmbedding.vertexCoord, map_sub]
  rw [heq] at hd
  have hd' := abs_le.mp hd
  linarith

theorem PeriodicPlaneEmbedding.rectTopBoundary_coord_gt
    (E : PeriodicPlaneEmbedding P) {B a b c d : ℝ}
    (hB : ∀ {x y : V} (hxy : P.graph.Adj x y) (t) (i : Fin 2),
      |E.coordinates (E.edgeArc hxy t - E.vertex x) i| ≤ B)
    {x : E.RectVertex a b c d} (hx : E.rectTopBoundary a b c d x) :
    d - B < E.vertexCoord x.1 1 := by
  obtain ⟨y, hxy, hy⟩ := hx
  have hd := hB hxy (1 : unitInterval) (1 : Fin 2)
  have heq : E.coordinates (E.edgeArc hxy (1 : unitInterval) - E.vertex x.1) 1 =
      E.vertexCoord y 1 - E.vertexCoord x.1 1 := by
    rw [Path.target]
    simp [PeriodicPlaneEmbedding.vertexCoord, map_sub]
  rw [heq] at hd
  have hd' := abs_le.mp hd
  linarith


def PeriodicPlaneEmbedding.finiteHorizontalCrossing
    (E : PeriodicPlaneEmbedding P) (a b c d : ℝ) :
    Set (ConfigSpace (Sym2 (E.RectVertex a b c d))) :=
  {eta | ∃ x y : E.RectVertex a b c d,
    E.rectLeftBoundary a b c d x ∧ E.rectRightBoundary a b c d y ∧
      (FK.openSub (E.rectGraph a b c d) eta).Reachable x y}


def PeriodicPlaneEmbedding.horizontalCrossingEvent
    (E : PeriodicPlaneEmbedding P) (a b c d : ℝ) :
    Set (ConfigSpace (Sym2 V)) :=
  E.rectRestrict a b c d ⁻¹' E.finiteHorizontalCrossing a b c d

theorem PeriodicPlaneEmbedding.finiteHorizontalCrossing_isIncreasing
    (E : PeriodicPlaneEmbedding P) (a b c d : ℝ) :
    IsIncreasing (E.finiteHorizontalCrossing a b c d) := by
  intro eta theta hle
  rintro ⟨x, y, hx, hy, hreach⟩
  refine ⟨x, y, hx, hy, hreach.mono ?_⟩
  intro u v huv
  rw [FK.openSub_adj] at huv ⊢
  refine ⟨huv.1, Bool.eq_true_of_true_le ?_⟩
  simpa [huv.2] using hle s(u, v)

theorem PeriodicPlaneEmbedding.rectRestrict_mono
    (E : PeriodicPlaneEmbedding P) (a b c d : ℝ) :
    Monotone (E.rectRestrict a b c d) := by
  intro omega eta hle e
  exact hle (Sym2.map Subtype.val e)

theorem PeriodicPlaneEmbedding.horizontalCrossingEvent_isIncreasing
    (E : PeriodicPlaneEmbedding P) (a b c d : ℝ) :
    IsIncreasing (E.horizontalCrossingEvent a b c d) := by
  intro omega eta hle homega
  exact E.finiteHorizontalCrossing_isIncreasing a b c d
    (E.rectRestrict_mono a b c d hle) homega

theorem PeriodicPlaneEmbedding.horizontalCrossingEvent_measurableSet
    (E : PeriodicPlaneEmbedding P) (a b c d : ℝ) :
    MeasurableSet (E.horizontalCrossingEvent a b c d) :=
  (IsClopen.preimage ⟨isClosed_discrete _, isOpen_discrete _⟩
    (E.continuous_rectRestrict a b c d)).isOpen.measurableSet



theorem PeriodicPlaneEmbedding.finiteHorizontalCrossing_embeddedPath
    (E : PeriodicPlaneEmbedding P) {B : ℝ}
    (hB0 : 0 ≤ B)
    (hB : ∀ {x y : V} (hxy : P.graph.Adj x y) (t) (i : Fin 2),
      |E.coordinates (E.edgeArc hxy t - E.vertex x) i| ≤ B)
    {a b c d : ℝ} {eta : ConfigSpace (Sym2 (E.RectVertex a b c d))}
    (heta : eta ∈ E.finiteHorizontalCrossing a b c d) :
    ∃ x y : E.RectVertex a b c d,
      E.rectLeftBoundary a b c d x ∧ E.rectRightBoundary a b c d y ∧
      ∃ gamma : Path (E.vertex x.1) (E.vertex y.1),
        Set.range gamma ⊆
          E.planeRect (a - B) (b + B) (c - B) (d + B) := by
  rcases heta with ⟨x, y, hx, hy, hreach⟩
  obtain ⟨p⟩ := hreach
  refine ⟨x, y, hx, hy,
    E.walkArc (p.map (E.openRectHom a b c d eta)), ?_⟩
  exact E.openRectWalkArc_range_subset hB0 hB p



theorem PeriodicPlaneEmbedding.finiteHorizontalCrossing_openWalk_of_wide
    (E : PeriodicPlaneEmbedding P) {B : ℝ}
    (hB : ∀ {x y : V} (hxy : P.graph.Adj x y) (t) (i : Fin 2),
      |E.coordinates (E.edgeArc hxy t - E.vertex x) i| ≤ B)
    {a b c d : ℝ} (hwide : a + B ≤ b - B)
    {eta : ConfigSpace (Sym2 (E.RectVertex a b c d))}
    (heta : eta ∈ E.finiteHorizontalCrossing a b c d) :
    ∃ x y : E.RectVertex a b c d,
      E.rectLeftBoundary a b c d x ∧ E.rectRightBoundary a b c d y ∧
      ∃ p : (FK.openSub (E.rectGraph a b c d) eta).Walk x y,
        ¬ (p.map (E.openRectHom a b c d eta)).Nil := by
  rcases heta with ⟨x, y, hx, hy, hreach⟩
  obtain ⟨p⟩ := hreach
  have hxcoord := E.rectLeftBoundary_coord_lt hB hx
  have hycoord := E.rectRightBoundary_coord_gt hB hy
  have hxy : x.1 ≠ y.1 := by
    intro heq
    rw [heq] at hxcoord
    linarith
  exact ⟨x, y, hx, hy, p, SimpleGraph.Walk.not_nil_of_ne hxy⟩




theorem PeriodicPlaneEmbedding.finiteHorizontalCrossing_extendedPath
    (E : PeriodicPlaneEmbedding P) {B : ℝ}
    (hB0 : 0 ≤ B)
    (hB : ∀ {x y : V} (hxy : P.graph.Adj x y) (t) (i : Fin 2),
      |E.coordinates (E.edgeArc hxy t - E.vertex x) i| ≤ B)
    {a b c d : ℝ} {eta : ConfigSpace (Sym2 (E.RectVertex a b c d))}
    (heta : eta ∈ E.finiteHorizontalCrossing a b c d) :
    ∃ xl xr : V, ∃ gamma : Path (E.vertex xl) (E.vertex xr),
      E.vertexCoord xl 0 < a ∧ b < E.vertexCoord xr 0 ∧
      Set.range gamma ⊆
        E.planeRect (a - B) (b + B) (c - B) (d + B) := by
  obtain ⟨x, y, hx, hy, gamma, hgamma⟩ :=
    E.finiteHorizontalCrossing_embeddedPath hB0 hB heta
  obtain ⟨xl, hxl, hxlcoord⟩ := hx
  obtain ⟨xr, hxr, hxrcoord⟩ := hy
  let gamma' := (E.edgeArc hxl).symm.trans (gamma.trans (E.edgeArc hxr))
  refine ⟨xl, xr, gamma', hxlcoord, hxrcoord, ?_⟩
  intro q hq
  simp only [gamma', Path.trans_range, Set.mem_union] at hq
  rcases hq with hq | hq | hq
  · rw [Path.symm_range] at hq
    obtain ⟨t, rfl⟩ := hq
    exact E.edgeArc_mem_expanded_planeRect hB hxl (by exact x.2) t
  · exact hgamma hq
  · obtain ⟨t, rfl⟩ := hq
    exact E.edgeArc_mem_expanded_planeRect hB hxr (by exact y.2) t


def PeriodicPlaneEmbedding.finiteVerticalCrossing
    (E : PeriodicPlaneEmbedding P) (a b c d : ℝ) :
    Set (ConfigSpace (Sym2 (E.RectVertex a b c d))) :=
  {eta | ∃ x y : E.RectVertex a b c d,
    E.rectBottomBoundary a b c d x ∧ E.rectTopBoundary a b c d y ∧
      (FK.openSub (E.rectGraph a b c d) eta).Reachable x y}

def PeriodicPlaneEmbedding.verticalCrossingEvent
    (E : PeriodicPlaneEmbedding P) (a b c d : ℝ) :
    Set (ConfigSpace (Sym2 V)) :=
  E.rectRestrict a b c d ⁻¹' E.finiteVerticalCrossing a b c d

theorem PeriodicPlaneEmbedding.finiteVerticalCrossing_isIncreasing
    (E : PeriodicPlaneEmbedding P) (a b c d : ℝ) :
    IsIncreasing (E.finiteVerticalCrossing a b c d) := by
  intro eta theta hle
  rintro ⟨x, y, hx, hy, hreach⟩
  refine ⟨x, y, hx, hy, hreach.mono ?_⟩
  intro u v huv
  rw [FK.openSub_adj] at huv ⊢
  refine ⟨huv.1, Bool.eq_true_of_true_le ?_⟩
  simpa [huv.2] using hle s(u, v)

theorem PeriodicPlaneEmbedding.verticalCrossingEvent_isIncreasing
    (E : PeriodicPlaneEmbedding P) (a b c d : ℝ) :
    IsIncreasing (E.verticalCrossingEvent a b c d) := by
  intro omega eta hle homega
  exact E.finiteVerticalCrossing_isIncreasing a b c d
    (E.rectRestrict_mono a b c d hle) homega

theorem PeriodicPlaneEmbedding.verticalCrossingEvent_measurableSet
    (E : PeriodicPlaneEmbedding P) (a b c d : ℝ) :
    MeasurableSet (E.verticalCrossingEvent a b c d) :=
  (IsClopen.preimage ⟨isClosed_discrete _, isOpen_discrete _⟩
    (E.continuous_rectRestrict a b c d)).isOpen.measurableSet


theorem PeriodicPlaneEmbedding.finiteVerticalCrossing_embeddedPath
    (E : PeriodicPlaneEmbedding P) {B : ℝ}
    (hB0 : 0 ≤ B)
    (hB : ∀ {x y : V} (hxy : P.graph.Adj x y) (t) (i : Fin 2),
      |E.coordinates (E.edgeArc hxy t - E.vertex x) i| ≤ B)
    {a b c d : ℝ} {eta : ConfigSpace (Sym2 (E.RectVertex a b c d))}
    (heta : eta ∈ E.finiteVerticalCrossing a b c d) :
    ∃ x y : E.RectVertex a b c d,
      E.rectBottomBoundary a b c d x ∧ E.rectTopBoundary a b c d y ∧
      ∃ gamma : Path (E.vertex x.1) (E.vertex y.1),
        Set.range gamma ⊆
          E.planeRect (a - B) (b + B) (c - B) (d + B) := by
  rcases heta with ⟨x, y, hx, hy, hreach⟩
  obtain ⟨p⟩ := hreach
  refine ⟨x, y, hx, hy,
    E.walkArc (p.map (E.openRectHom a b c d eta)), ?_⟩
  exact E.openRectWalkArc_range_subset hB0 hB p



theorem PeriodicPlaneEmbedding.finiteVerticalCrossing_openWalk_of_tall
    (E : PeriodicPlaneEmbedding P) {B : ℝ}
    (hB : ∀ {x y : V} (hxy : P.graph.Adj x y) (t) (i : Fin 2),
      |E.coordinates (E.edgeArc hxy t - E.vertex x) i| ≤ B)
    {a b c d : ℝ} (htall : c + B ≤ d - B)
    {eta : ConfigSpace (Sym2 (E.RectVertex a b c d))}
    (heta : eta ∈ E.finiteVerticalCrossing a b c d) :
    ∃ x y : E.RectVertex a b c d,
      E.rectBottomBoundary a b c d x ∧ E.rectTopBoundary a b c d y ∧
      ∃ p : (FK.openSub (E.rectGraph a b c d) eta).Walk x y,
        ¬ (p.map (E.openRectHom a b c d eta)).Nil := by
  rcases heta with ⟨x, y, hx, hy, hreach⟩
  obtain ⟨p⟩ := hreach
  have hxcoord := E.rectBottomBoundary_coord_lt hB hx
  have hycoord := E.rectTopBoundary_coord_gt hB hy
  have hxy : x.1 ≠ y.1 := by
    intro heq
    rw [heq] at hxcoord
    linarith
  exact ⟨x, y, hx, hy, p, SimpleGraph.Walk.not_nil_of_ne hxy⟩


theorem PeriodicPlaneEmbedding.finiteVerticalCrossing_extendedPath
    (E : PeriodicPlaneEmbedding P) {B : ℝ}
    (hB0 : 0 ≤ B)
    (hB : ∀ {x y : V} (hxy : P.graph.Adj x y) (t) (i : Fin 2),
      |E.coordinates (E.edgeArc hxy t - E.vertex x) i| ≤ B)
    {a b c d : ℝ} {eta : ConfigSpace (Sym2 (E.RectVertex a b c d))}
    (heta : eta ∈ E.finiteVerticalCrossing a b c d) :
    ∃ xb xt : V, ∃ gamma : Path (E.vertex xb) (E.vertex xt),
      E.vertexCoord xb 1 < c ∧ d < E.vertexCoord xt 1 ∧
      Set.range gamma ⊆
        E.planeRect (a - B) (b + B) (c - B) (d + B) := by
  obtain ⟨x, y, hx, hy, gamma, hgamma⟩ :=
    E.finiteVerticalCrossing_embeddedPath hB0 hB heta
  obtain ⟨xb, hxb, hxbcoord⟩ := hx
  obtain ⟨xt, hxt, hxtcoord⟩ := hy
  let gamma' := (E.edgeArc hxb).symm.trans (gamma.trans (E.edgeArc hxt))
  refine ⟨xb, xt, gamma', hxbcoord, hxtcoord, ?_⟩
  intro q hq
  simp only [gamma', Path.trans_range, Set.mem_union] at hq
  rcases hq with hq | hq | hq
  · rw [Path.symm_range] at hq
    obtain ⟨t, rfl⟩ := hq
    exact E.edgeArc_mem_expanded_planeRect hB hxb (by exact x.2) t
  · exact hgamma hq
  · obtain ⟨t, rfl⟩ := hq
    exact E.edgeArc_mem_expanded_planeRect hB hxt (by exact y.2) t




def PeriodicGraph.configTranslate (P : PeriodicGraph V) (z : Site 2)
    (omega : ConfigSpace (Sym2 V)) : ConfigSpace (Sym2 V) :=
  fun e => omega (Sym2.map (P.shift (-z)) e)

@[simp] theorem PeriodicGraph.shift_neg_shift
    (P : PeriodicGraph V) (z : Site 2) (x : V) :
    P.shift (-z) (P.shift z x) = x := by
  have h := P.shift_add z (-z) x
  rw [add_neg_cancel, P.shift_zero] at h
  exact h.symm

@[simp] theorem PeriodicGraph.shift_shift_neg
    (P : PeriodicGraph V) (z : Site 2) (x : V) :
    P.shift z (P.shift (-z) x) = x := by
  simpa only [neg_neg] using P.shift_neg_shift (-z) x

@[simp] theorem PeriodicGraph.configTranslate_neg
    (P : PeriodicGraph V) (z : Site 2)
    (omega : ConfigSpace (Sym2 V)) :
    P.configTranslate (-z) (P.configTranslate z omega) = omega := by
  funext e
  induction e using Sym2.inductionOn with
  | _ x y => simp [PeriodicGraph.configTranslate]

theorem PeriodicGraph.measurable_configTranslate
    (P : PeriodicGraph V) (z : Site 2) :
    Measurable (P.configTranslate z) :=
  measurable_pi_lambda _ fun e => ConfigSpace.measurable_eval _


def PeriodicGraph.IsTranslationInvariant
    (P : PeriodicGraph V) (mu : Measure (ConfigSpace (Sym2 V))) : Prop :=
  ∀ z, MeasurePreserving (P.configTranslate z) mu mu

theorem PeriodicGraph.configTranslate_mono
    (P : PeriodicGraph V) (z : Site 2) :
    Monotone (P.configTranslate z) := by
  intro omega eta hle e
  exact hle (Sym2.map (P.shift (-z)) e)


def PeriodicGraph.translateEvent
    (P : PeriodicGraph V) (z : Site 2)
    (A : Set (ConfigSpace (Sym2 V))) :
    Set (ConfigSpace (Sym2 V)) :=
  P.configTranslate z ⁻¹' A

theorem PeriodicGraph.translateEvent_measurableSet
    (P : PeriodicGraph V) (z : Site 2)
    {A : Set (ConfigSpace (Sym2 V))} (hA : MeasurableSet A) :
    MeasurableSet (P.translateEvent z A) :=
  hA.preimage (P.measurable_configTranslate z)

theorem PeriodicGraph.translateEvent_isIncreasing
    (P : PeriodicGraph V) (z : Site 2)
    {A : Set (ConfigSpace (Sym2 V))} (hA : IsIncreasing A) :
    IsIncreasing (P.translateEvent z A) :=
  fun _ _ home hmem => hA (P.configTranslate_mono z home) hmem

theorem PeriodicGraph.translateEvent_measure_eq
    (P : PeriodicGraph V) (mu : Measure (ConfigSpace (Sym2 V)))
    (hTI : P.IsTranslationInvariant mu) (z : Site 2)
    {A : Set (ConfigSpace (Sym2 V))} (hA : MeasurableSet A) :
    mu (P.translateEvent z A) = mu A :=
  (hTI z).measure_preimage hA.nullMeasurableSet



def PeriodicGraph.openSubgraphTranslateHom
    (P : PeriodicGraph V) (z : Site 2)
    (omega : ConfigSpace (Sym2 V)) :
    SimpleGraph.Hom (P.openSubgraph omega)
      (P.openSubgraph (P.configTranslate z omega)) where
  toFun := P.shift z
  map_rel' := by
    intro x y hxy
    rw [P.openSubgraph_adj] at hxy ⊢
    refine ⟨(P.shift_adj z x y).2 hxy.1, ?_⟩
    simpa [PeriodicGraph.configTranslate] using hxy.2

@[simp] theorem PeriodicGraph.openSubgraphTranslateHom_apply
    (P : PeriodicGraph V) (z : Site 2)
    (omega : ConfigSpace (Sym2 V)) (x : V) :
    P.openSubgraphTranslateHom z omega x = P.shift z x := rfl

theorem PeriodicGraph.reachable_configTranslate
    (P : PeriodicGraph V) (z : Site 2)
    (omega : ConfigSpace (Sym2 V)) (x y : V) :
    (P.openSubgraph (P.configTranslate z omega)).Reachable
        (P.shift z x) (P.shift z y) ↔
      (P.openSubgraph omega).Reachable x y := by
  constructor
  · intro h
    have hmapped := h.map
      (P.openSubgraphTranslateHom (-z) (P.configTranslate z omega))
    simpa [PeriodicGraph.configTranslate, P.shift_neg_shift] using hmapped
  · exact fun h => h.map (P.openSubgraphTranslateHom z omega)

theorem PeriodicGraph.cluster_configTranslate
    (P : PeriodicGraph V) (z : Site 2)
    (omega : ConfigSpace (Sym2 V)) (x : V) :
    P.cluster (P.configTranslate z omega) (P.shift z x) =
      P.shift z '' P.cluster omega x := by
  ext y
  constructor
  · intro hy
    refine ⟨P.shift (-z) y, ?_, P.shift_shift_neg z y⟩
    have hreach :
        (P.openSubgraph (P.configTranslate z omega)).Reachable
          (P.shift z x) (P.shift z (P.shift (-z) y)) := by
      simpa using hy
    exact (P.reachable_configTranslate z omega x (P.shift (-z) y)).mp hreach
  · rintro ⟨y, hy, rfl⟩
    exact (P.reachable_configTranslate z omega x y).mpr hy

theorem PeriodicGraph.cluster_infinite_configTranslate
    (P : PeriodicGraph V) (z : Site 2)
    (omega : ConfigSpace (Sym2 V)) (x : V) :
    (P.cluster (P.configTranslate z omega) (P.shift z x)).Infinite ↔
      (P.cluster omega x).Infinite := by
  rw [P.cluster_configTranslate z omega x]
  exact Set.infinite_image_iff
    (Set.injOn_of_injective (P.shift z).injective)



def IsFKG (mu : Measure (ConfigSpace (Sym2 V))) : Prop :=
  forall A B : Set (ConfigSpace (Sym2 V)),
    MeasurableSet A -> MeasurableSet B ->
    IsIncreasing A -> IsIncreasing B ->
      mu.real A * mu.real B <= mu.real (A ∩ B)


theorem measurable_sqrt_trick
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hFKG : IsFKG mu) {A B : Set (ConfigSpace (Sym2 V))}
    (hA : IsIncreasing A) (hB : IsIncreasing B)
    (hAm : MeasurableSet A) (hBm : MeasurableSet B) :
    1 - Real.sqrt (1 - mu.real (A ∪ B)) <=
      max (mu.real A) (mu.real B) := by
  have hfkg := hFKG A B hAm hBm hA hB
  have hie : mu.real (A ∪ B) + mu.real (A ∩ B) =
      mu.real A + mu.real B := measureReal_union_add_inter hBm
  apply Universality.sqrt_trick_max_real measureReal_le_one measureReal_le_one
  nlinarith




theorem four_event_sqrt_trick
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hFKG : IsFKG mu) {A B C D : Set (ConfigSpace (Sym2 V))}
    (hA : IsIncreasing A) (hB : IsIncreasing B)
    (hC : IsIncreasing C) (hD : IsIncreasing D)
    (hAm : MeasurableSet A) (hBm : MeasurableSet B)
    (hCm : MeasurableSet C) (hDm : MeasurableSet D) :
    1 - Real.sqrt (Real.sqrt (1 - mu.real (A ∪ (B ∪ (C ∪ D))))) ≤
      max (max (mu.real A) (mu.real B))
        (max (mu.real C) (mu.real D)) := by
  have houter := measurable_sqrt_trick mu hFKG
    (hA.union hB) (hC.union hD) (hAm.union hBm) (hCm.union hDm)
  simp only [Set.union_assoc] at houter
  have hAB := measurable_sqrt_trick mu hFKG hA hB hAm hBm
  have hCD := measurable_sqrt_trick mu hFKG hC hD hCm hDm
  by_cases hle : mu.real (A ∪ B) ≤ mu.real (C ∪ D)
  · rw [max_eq_right hle] at houter
    have hmiss : 1 - mu.real (C ∪ D) ≤
        Real.sqrt (1 - mu.real (A ∪ (B ∪ (C ∪ D)))) := by
      linarith
    have hsqrt := Real.sqrt_le_sqrt hmiss
    exact le_trans (by linarith)
      (le_max_right (max (mu.real A) (mu.real B))
        (max (mu.real C) (mu.real D)))
  · have hle' : mu.real (C ∪ D) ≤ mu.real (A ∪ B) := le_of_not_ge hle
    rw [max_eq_left hle'] at houter
    have hmiss : 1 - mu.real (A ∪ B) ≤
        Real.sqrt (1 - mu.real (A ∪ (B ∪ (C ∪ D)))) := by
      linarith
    have hsqrt := Real.sqrt_le_sqrt hmiss
    exact le_trans (by linarith)
      (le_max_left (max (mu.real A) (mu.real B))
        (max (mu.real C) (mu.real D)))

theorem four_event_max_tendsto_one
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hFKG : IsFKG mu)
    (A B C D : ℕ → Set (ConfigSpace (Sym2 V)))
    (hA : ∀ n, IsIncreasing (A n)) (hB : ∀ n, IsIncreasing (B n))
    (hC : ∀ n, IsIncreasing (C n)) (hD : ∀ n, IsIncreasing (D n))
    (hAm : ∀ n, MeasurableSet (A n)) (hBm : ∀ n, MeasurableSet (B n))
    (hCm : ∀ n, MeasurableSet (C n)) (hDm : ∀ n, MeasurableSet (D n))
    (hunion : Tendsto (fun n =>
      mu.real (A n ∪ (B n ∪ (C n ∪ D n)))) atTop (nhds 1)) :
    Tendsto (fun n => max (max (mu.real (A n)) (mu.real (B n)))
      (max (mu.real (C n)) (mu.real (D n)))) atTop (nhds 1) := by
  have hmiss : Tendsto (fun n =>
      1 - mu.real (A n ∪ (B n ∪ (C n ∪ D n)))) atTop (nhds 0) := by
    simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub hunion
  have hlower : Tendsto (fun n => 1 - Real.sqrt (Real.sqrt
      (1 - mu.real (A n ∪ (B n ∪ (C n ∪ D n))))))
      atTop (nhds 1) := by
    simpa using tendsto_const_nhds.sub hmiss.sqrt.sqrt
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le hlower tendsto_const_nhds
  · intro n
    exact four_event_sqrt_trick mu hFKG
      (hA n) (hB n) (hC n) (hD n)
      (hAm n) (hBm n) (hCm n) (hDm n)
  · intro n
    exact max_le (max_le measureReal_le_one measureReal_le_one)
      (max_le measureReal_le_one measureReal_le_one)




theorem min_tendsto_zero_of_matched_exclusion
    (primalH primalV dualV dualH : ℕ → ℝ)
    (hH0 : ∀ n, 0 ≤ primalH n) (hV0 : ∀ n, 0 ≤ primalV n)
    (hmatchH : ∀ n, primalH n + dualV n ≤ 1)
    (hmatchV : ∀ n, primalV n + dualH n ≤ 1)
    (hdual : Tendsto (fun n => max (dualV n) (dualH n)) atTop (nhds 1)) :
    Tendsto (fun n => min (primalH n) (primalV n)) atTop (nhds 0) := by
  have hupper : ∀ n,
      min (primalH n) (primalV n) ≤
        1 - max (dualV n) (dualH n) := by
    intro n
    by_cases hle : dualV n ≤ dualH n
    · rw [max_eq_right hle]
      exact (min_le_right _ _).trans (by linarith [hmatchV n])
    · rw [max_eq_left (le_of_not_ge hle)]
      exact (min_le_left _ _).trans (by linarith [hmatchH n])
  have hrhs : Tendsto (fun n => 1 - max (dualV n) (dualH n))
      atTop (nhds 0) := by
    simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub hdual
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le
    (tendsto_const_nhds (x := (0 : ℝ))) hrhs
  · intro n
    exact le_min (hH0 n) (hV0 n)
  · exact hupper





theorem balanced_aspect_crossing_contradiction
    (h v hNext vNext : ℕ → ℝ)
    (hbalance : ∀ n, h n ≤ v n)
    (hnext : ∀ n, vNext n < hNext n)
    (hmax : Tendsto (fun n => max (h n) (vNext n)) atTop (nhds 1))
    (hmin : Tendsto (fun n => min (v n) (h n)) atTop (nhds 0))
    (hminNext : Tendsto (fun n => min (vNext n) (hNext n))
      atTop (nhds 0)) : False := by
  have hh : Tendsto h atTop (nhds 0) := by
    convert hmin using 1
    funext n
    exact (min_eq_right (hbalance n)).symm
  have hvNext : Tendsto vNext atTop (nhds 0) := by
    convert hminNext using 1
    funext n
    exact (min_eq_left (hnext n).le).symm
  have hmaxZero : Tendsto (fun n => max (h n) (vNext n))
      atTop (nhds 0) := by
    simpa using hh.max hvNext
  have h01 : (1 : ℝ) = 0 := tendsto_nhds_unique hmax hmaxZero
  norm_num at h01






theorem balanced_aspect_crossing_contradiction_of_error
    (h v hNext vNext error : ℕ → ℝ)
    (hh0 : ∀ n, 0 ≤ h n) (hvNext0 : ∀ n, 0 ≤ vNext n)
    (herror0 : ∀ n, 0 ≤ error n)
    (hbalance : ∀ n, h n ≤ v n + error n)
    (hnext : ∀ n, vNext n ≤ hNext n + error n)
    (herror : Tendsto error atTop (nhds 0))
    (hmax : Tendsto (fun n => max (h n) (vNext n)) atTop (nhds 1))
    (hmin : Tendsto (fun n => min (v n) (h n)) atTop (nhds 0))
    (hminNext : Tendsto (fun n => min (vNext n) (hNext n))
      atTop (nhds 0)) : False := by
  have hhUpper : ∀ n, h n ≤ min (v n) (h n) + error n := by
    intro n
    by_cases hvh : v n ≤ h n
    · rw [min_eq_left hvh]
      exact hbalance n
    · rw [min_eq_right (le_of_not_ge hvh)]
      exact le_add_of_nonneg_right (herror0 n)
  have hvNextUpper : ∀ n,
      vNext n ≤ min (vNext n) (hNext n) + error n := by
    intro n
    by_cases hvh : vNext n ≤ hNext n
    · rw [min_eq_left hvh]
      exact le_add_of_nonneg_right (herror0 n)
    · rw [min_eq_right (le_of_not_ge hvh)]
      exact hnext n
  have hh : Tendsto h atTop (nhds 0) := by
    have hupper : Tendsto (fun n => min (v n) (h n) + error n)
        atTop (nhds 0) := by
      simpa only [zero_add] using hmin.add herror
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le
      (tendsto_const_nhds (x := (0 : ℝ))) hupper
    · exact hh0
    · exact hhUpper
  have hvNext : Tendsto vNext atTop (nhds 0) := by
    have hupper : Tendsto (fun n => min (vNext n) (hNext n) + error n)
        atTop (nhds 0) := by
      simpa only [zero_add] using hminNext.add herror
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le
      (tendsto_const_nhds (x := (0 : ℝ))) hupper
    · exact hvNext0
    · exact hvNextUpper
  have hmaxZero : Tendsto (fun n => max (h n) (vNext n))
      atTop (nhds 0) := by
    simpa using hh.max hvNext
  have h01 : (1 : ℝ) = 0 := tendsto_nhds_unique hmax hmaxZero
  norm_num at h01


def forceOpenFinset (F : Finset (Sym2 V))
    (omega : ConfigSpace (Sym2 V)) : ConfigSpace (Sym2 V) :=
  fun e => if e ∈ F then true else omega e

theorem measurable_forceOpenFinset (F : Finset (Sym2 V)) :
    Measurable (forceOpenFinset F :
      ConfigSpace (Sym2 V) → ConfigSpace (Sym2 V)) :=
  measurable_pi_lambda _ fun e => by
    by_cases he : e ∈ F
    · simpa [forceOpenFinset, he] using (measurable_const :
        Measurable (fun _ : ConfigSpace (Sym2 V) => true))
    · simpa [forceOpenFinset, he] using ConfigSpace.measurable_eval e



def HasFiniteEnergy
    (mu : Measure (ConfigSpace (Sym2 V))) : Prop :=
  ∀ F : Finset (Sym2 V), mu.map (forceOpenFinset F) ≪ mu



theorem PeriodicGraph.measurableSet_openChain_sheffield
    (P : PeriodicGraph V) (l : List V) :
    MeasurableSet {omega : ConfigSpace (Sym2 V) |
      List.IsChain (P.openSubgraph omega).Adj l} := by
  induction l with
  | nil => simp only [List.isChain_nil, Set.setOf_true, MeasurableSet.univ]
  | cons a l ih =>
      cases l with
      | nil => simp only [List.isChain_singleton, Set.setOf_true, MeasurableSet.univ]
      | cons b l =>
          have heq :
              {omega : ConfigSpace (Sym2 V) |
                  List.IsChain (P.openSubgraph omega).Adj (a :: b :: l)} =
                ({omega | P.graph.Adj a b} ∩
                  {omega | omega s(a, b) = true}) ∩
                {omega | List.IsChain (P.openSubgraph omega).Adj (b :: l)} := by
            ext omega
            simp only [Set.mem_setOf_eq, Set.mem_inter_iff,
              List.isChain_cons_cons, P.openSubgraph_adj]
          rw [heq]
          apply MeasurableSet.inter
          · by_cases hab : P.graph.Adj a b
            · simpa [hab] using measurableSet_eq_fun
                (ConfigSpace.measurable_eval s(a, b)) measurable_const
            · simp [hab]
          · exact ih

theorem PeriodicGraph.reachable_iff_openChain_sheffield
    (P : PeriodicGraph V) (omega : ConfigSpace (Sym2 V)) (x y : V) :
    (P.openSubgraph omega).Reachable x y ↔
      ∃ l : List V, List.IsChain (P.openSubgraph omega).Adj (x :: l) ∧
        (x :: l).getLast (List.cons_ne_nil _ _) = y := by
  rw [SimpleGraph.reachable_iff_reflTransGen]
  constructor
  · intro h
    obtain ⟨l, hchain, hlast⟩ :=
      List.exists_isChain_cons_of_relationReflTransGen h
    exact ⟨l, hchain, hlast⟩
  · rintro ⟨l, hchain, hlast⟩
    exact List.relationReflTransGen_of_exists_isChain_cons l hchain hlast



def PeriodicGraph.connectedWithinOrbit
    (P : PeriodicGraph V) (x y : V) (N : ℕ) :
    Set (ConfigSpace (Sym2 V)) :=
  {omega | ∃ l : List V,
    List.IsChain (P.openSubgraph omega).Adj (x :: l) ∧
    (x :: l).getLast (List.cons_ne_nil _ _) = y ∧
    ∀ v ∈ x :: l, v ∈ P.orbitBox (P.bufferedRadius N)}

theorem PeriodicGraph.connectedWithinOrbit_measurableSet
    (P : PeriodicGraph V) (x y : V) (N : ℕ) :
    MeasurableSet (P.connectedWithinOrbit x y N) := by
  have heq : P.connectedWithinOrbit x y N =
      ⋃ l : List V, if
        (x :: l).getLast (List.cons_ne_nil _ _) = y ∧
          ∀ v ∈ x :: l, v ∈ P.orbitBox (P.bufferedRadius N)
        then {omega | List.IsChain (P.openSubgraph omega).Adj (x :: l)}
        else ∅ := by
    ext omega
    simp only [PeriodicGraph.connectedWithinOrbit, Set.mem_setOf_eq,
      Set.mem_iUnion]
    constructor
    · rintro ⟨l, hchain, hlast, hbox⟩
      refine ⟨l, ?_⟩
      rw [if_pos ⟨hlast, hbox⟩]
      exact hchain
    · rintro ⟨l, hl⟩
      split_ifs at hl with h
      · exact ⟨l, hl, h.1, h.2⟩
      · exact False.elim (by simpa using hl)
  rw [heq]
  exact MeasurableSet.iUnion fun l => by
    split_ifs
    · exact P.measurableSet_openChain_sheffield (x :: l)
    · exact MeasurableSet.empty

theorem PeriodicGraph.connectedWithinOrbit_isIncreasing
    (P : PeriodicGraph V) (x y : V) (N : ℕ) :
    IsIncreasing (P.connectedWithinOrbit x y N) := by
  intro omega eta home
  rintro ⟨l, hchain, hlast, hbox⟩
  refine ⟨l, hchain.imp ?_, hlast, hbox⟩
  intro a b hab
  rw [P.openSubgraph_adj] at hab ⊢
  refine ⟨hab.1, Bool.eq_true_of_true_le ?_⟩
  simpa [hab.2] using home s(a, b)

theorem PeriodicGraph.connectedWithinOrbit_mono
    (P : PeriodicGraph V) (x y : V) :
    Monotone (P.connectedWithinOrbit x y) := by
  intro n m hnm omega
  rintro ⟨l, hchain, hlast, hbox⟩
  refine ⟨l, hchain, hlast, ?_⟩
  intro v hv
  exact P.orbitBox_mono (P.bufferedRadius_strictMono.monotone hnm) (hbox v hv)

theorem PeriodicGraph.iUnion_connectedWithinOrbit
    (P : PeriodicGraph V) (x y : V) :
    (⋃ N, P.connectedWithinOrbit x y N) = P.twoPointEvent x y := by
  ext omega
  simp only [Set.mem_iUnion, PeriodicGraph.connectedWithinOrbit,
    Set.mem_setOf_eq, PeriodicGraph.twoPointEvent]
  constructor
  · rintro ⟨N, l, hchain, hlast, _hbox⟩
    exact (P.reachable_iff_openChain_sheffield omega x y).2
      ⟨l, hchain, hlast⟩
  · intro hreach
    obtain ⟨l, hchain, hlast⟩ :=
      (P.reachable_iff_openChain_sheffield omega x y).1 hreach
    obtain ⟨N, hN⟩ := P.finite_subset_orbitBox (x :: l).toFinset
    refine ⟨N, l, hchain, hlast, ?_⟩
    intro v hv
    exact P.orbitBox_mono (P.id_le_bufferedRadius N)
      (hN v (by simpa using hv))





def PeriodicGraph.HasUniqueInfiniteCluster
    (P : PeriodicGraph V) (omega : ConfigSpace (Sym2 V)) : Prop :=
  P.HasInfiniteCluster omega ∧
    ∀ x y, (P.cluster omega x).Infinite →
      (P.cluster omega y).Infinite →
        (P.openSubgraph omega).Reachable x y


def PeriodicGraph.orbitBoxHitsInfinite
    (P : PeriodicGraph V) (n : ℕ) :
    Set (ConfigSpace (Sym2 V)) :=
  {omega | ∃ x ∈ P.orbitBox n, (P.cluster omega x).Infinite}


def PeriodicGraph.translatedOrbitBoxHitsInfinite
    (P : PeriodicGraph V) (z : Site 2) (n : ℕ) :
    Set (ConfigSpace (Sym2 V)) :=
  {omega | ∃ x ∈ P.orbitBox n,
    (P.cluster omega (P.shift z x)).Infinite}

theorem PeriodicGraph.hasUniqueInfiniteCluster_configTranslate
    (P : PeriodicGraph V) (z : Site 2)
    (omega : ConfigSpace (Sym2 V)) :
    P.HasUniqueInfiniteCluster (P.configTranslate z omega) ↔
      P.HasUniqueInfiniteCluster omega := by
  constructor
  · rintro ⟨⟨x, hx⟩, huniq⟩
    refine ⟨⟨P.shift (-z) x, ?_⟩, ?_⟩
    · exact (P.cluster_infinite_configTranslate z omega
        (P.shift (-z) x)).mp (by simpa using hx)
    · intro a b ha hb
      have ha' : (P.cluster (P.configTranslate z omega)
          (P.shift z a)).Infinite :=
        (P.cluster_infinite_configTranslate z omega a).2 ha
      have hb' : (P.cluster (P.configTranslate z omega)
          (P.shift z b)).Infinite :=
        (P.cluster_infinite_configTranslate z omega b).2 hb
      exact (P.reachable_configTranslate z omega a b).mp
        (huniq (P.shift z a) (P.shift z b) ha' hb')
  · rintro ⟨⟨x, hx⟩, huniq⟩
    refine ⟨⟨P.shift z x,
      (P.cluster_infinite_configTranslate z omega x).2 hx⟩, ?_⟩
    intro a b ha hb
    let a0 := P.shift (-z) a
    let b0 := P.shift (-z) b
    have ha0 : (P.cluster omega a0).Infinite :=
      (P.cluster_infinite_configTranslate z omega a0).mp
        (by simpa [a0] using ha)
    have hb0 : (P.cluster omega b0).Infinite :=
      (P.cluster_infinite_configTranslate z omega b0).mp
        (by simpa [b0] using hb)
    have hab := huniq a0 b0 ha0 hb0
    simpa [a0, b0] using
      (P.reachable_configTranslate z omega a0 b0).mpr hab

theorem PeriodicGraph.clusterInfinite_isIncreasing
    (P : PeriodicGraph V) (x : V) :
    IsIncreasing {omega : ConfigSpace (Sym2 V) |
      (P.cluster omega x).Infinite} := by
  intro omega eta home hinfinite
  have hgraph : P.openSubgraph omega ≤ P.openSubgraph eta := by
    intro a b hab
    rw [P.openSubgraph_adj] at hab ⊢
    refine ⟨hab.1, Bool.eq_true_of_true_le ?_⟩
    simpa [hab.2] using home s(a, b)
  exact hinfinite.mono fun y hy => hy.mono hgraph

theorem PeriodicGraph.orbitBoxHitsInfinite_measurableSet
    (P : PeriodicGraph V) (n : ℕ) :
    MeasurableSet (P.orbitBoxHitsInfinite n) := by
  have heq : P.orbitBoxHitsInfinite n =
      ⋃ x : V, if x ∈ P.orbitBox n then
        {omega : ConfigSpace (Sym2 V) |
          (P.cluster omega x).Infinite} else ∅ := by
    ext omega
    simp only [PeriodicGraph.orbitBoxHitsInfinite, Set.mem_setOf_eq,
      Set.mem_iUnion]
    constructor
    · rintro ⟨x, hx, hinf⟩
      exact ⟨x, by simp [hx, hinf]⟩
    · rintro ⟨x, hx⟩
      by_cases hxb : x ∈ P.orbitBox n
      · exact ⟨x, hxb, by simpa [hxb] using hx⟩
      · simp [hxb] at hx
  rw [heq]
  exact MeasurableSet.iUnion fun x => by
    by_cases hx : x ∈ P.orbitBox n
    · simpa [hx] using P.measurableSet_cluster_infinite x
    · simp [hx]

theorem PeriodicGraph.orbitBoxHitsInfinite_isIncreasing
    (P : PeriodicGraph V) (n : ℕ) :
    IsIncreasing (P.orbitBoxHitsInfinite n) := by
  intro omega eta home
  rintro ⟨x, hx, hinfinite⟩
  exact ⟨x, hx, P.clusterInfinite_isIncreasing x home hinfinite⟩

theorem PeriodicGraph.translatedOrbitBoxHitsInfinite_preimage
    (P : PeriodicGraph V) (z : Site 2) (n : ℕ) :
    P.configTranslate z ⁻¹' P.translatedOrbitBoxHitsInfinite z n =
      P.orbitBoxHitsInfinite n := by
  ext omega
  simp only [Set.mem_preimage, PeriodicGraph.translatedOrbitBoxHitsInfinite,
    PeriodicGraph.orbitBoxHitsInfinite, Set.mem_setOf_eq]
  constructor
  · rintro ⟨x, hx, hinf⟩
    exact ⟨x, hx, (P.cluster_infinite_configTranslate z omega x).mp hinf⟩
  · rintro ⟨x, hx, hinf⟩
    exact ⟨x, hx, (P.cluster_infinite_configTranslate z omega x).mpr hinf⟩

theorem PeriodicGraph.translatedOrbitBoxHitsInfinite_measurableSet
    (P : PeriodicGraph V) (z : Site 2) (n : ℕ) :
    MeasurableSet (P.translatedOrbitBoxHitsInfinite z n) := by
  have heq : P.translatedOrbitBoxHitsInfinite z n =
      ⋃ x : V, if x ∈ P.orbitBox n then
        {omega : ConfigSpace (Sym2 V) |
          (P.cluster omega (P.shift z x)).Infinite} else ∅ := by
    ext omega
    simp only [PeriodicGraph.translatedOrbitBoxHitsInfinite,
      Set.mem_setOf_eq, Set.mem_iUnion]
    constructor
    · rintro ⟨x, hx, hinf⟩
      exact ⟨x, by simp [hx, hinf]⟩
    · rintro ⟨x, hx⟩
      by_cases hxb : x ∈ P.orbitBox n
      · exact ⟨x, hxb, by simpa [hxb] using hx⟩
      · simp [hxb] at hx
  rw [heq]
  exact MeasurableSet.iUnion fun x => by
    by_cases hx : x ∈ P.orbitBox n
    · simpa [hx] using P.measurableSet_cluster_infinite (P.shift z x)
    · simp [hx]

theorem PeriodicGraph.translatedOrbitBoxHitsInfinite_measure_eq
    (P : PeriodicGraph V) (mu : Measure (ConfigSpace (Sym2 V)))
    (hTI : P.IsTranslationInvariant mu) (z : Site 2) (n : ℕ) :
    mu (P.translatedOrbitBoxHitsInfinite z n) =
      mu (P.orbitBoxHitsInfinite n) := by
  rw [← P.translatedOrbitBoxHitsInfinite_preimage z n]
  exact ((hTI z).measure_preimage
    (P.translatedOrbitBoxHitsInfinite_measurableSet z n).nullMeasurableSet).symm

theorem PeriodicGraph.orbitBoxHitsInfinite_mono
    (P : PeriodicGraph V) : Monotone P.orbitBoxHitsInfinite := by
  intro n m hnm omega
  rintro ⟨x, hx, hinf⟩
  exact ⟨x, P.orbitBox_mono hnm hx, hinf⟩

theorem PeriodicGraph.iUnion_orbitBoxHitsInfinite
    (P : PeriodicGraph V) :
    (⋃ n, P.orbitBoxHitsInfinite n) =
      {omega | P.HasInfiniteCluster omega} := by
  ext omega
  simp only [Set.mem_iUnion, PeriodicGraph.orbitBoxHitsInfinite,
    PeriodicGraph.HasInfiniteCluster, Set.mem_setOf_eq]
  constructor
  · rintro ⟨n, x, _hx, hinf⟩
    exact ⟨x, hinf⟩
  · rintro ⟨x, hinf⟩
    obtain ⟨n, hx⟩ := P.mem_orbitBox_of_eventually x
    exact ⟨n, x, hx, hinf⟩

theorem PeriodicGraph.orbitBoxHitsInfinite_real_tendsto_one
    (P : PeriodicGraph V) (mu : Measure (ConfigSpace (Sym2 V)))
    [IsProbabilityMeasure mu]
    (hexists : mu {omega | P.HasInfiniteCluster omega} = 1) :
    Tendsto (fun n => mu.real (P.orbitBoxHitsInfinite n))
      atTop (nhds 1) := by
  have hmeasure := tendsto_measure_iUnion_atTop
    (μ := mu) P.orbitBoxHitsInfinite_mono
  rw [P.iUnion_orbitBoxHitsInfinite, hexists] at hmeasure
  exact (ENNReal.tendsto_toReal (by norm_num : (1 : ENNReal) ≠ ⊤)).comp
    hmeasure

theorem PeriodicGraph.measurableSet_hasUniqueInfiniteCluster
    (P : PeriodicGraph V) :
    MeasurableSet {omega : ConfigSpace (Sym2 V) |
      P.HasUniqueInfiniteCluster omega} := by
  let Inf := fun x : V =>
    {omega : ConfigSpace (Sym2 V) | (P.cluster omega x).Infinite}
  let Conn := fun x y : V => P.twoPointEvent x y
  have heq : {omega : ConfigSpace (Sym2 V) |
        P.HasUniqueInfiniteCluster omega} =
      {omega | P.HasInfiniteCluster omega} ∩
        ⋂ x : V, ⋂ y : V, ((Inf x ∩ Inf y) ∩ (Conn x y)ᶜ)ᶜ := by
    ext omega
    simp only [PeriodicGraph.HasUniqueInfiniteCluster, Set.mem_setOf_eq,
      Set.mem_inter_iff, Set.mem_iInter, Set.mem_compl_iff,
      not_and, Inf, Conn, PeriodicGraph.twoPointEvent]
    aesop
  rw [heq]
  apply P.measurableSet_hasInfiniteCluster.inter
  exact MeasurableSet.iInter fun x => MeasurableSet.iInter fun y =>
    (((P.measurableSet_cluster_infinite x).inter
      (P.measurableSet_cluster_infinite y)).inter
      (P.measurableSet_twoPointEvent x y).compl).compl



def PeriodicGraph.pairMergeError
    (P : PeriodicGraph V) (x y : V) (N : ℕ) :
    Set (ConfigSpace (Sym2 V)) :=
  ({omega | (P.cluster omega x).Infinite} ∩
    {omega | (P.cluster omega y).Infinite}) \ P.connectedWithinOrbit x y N

theorem PeriodicGraph.pairMergeError_measurableSet
    (P : PeriodicGraph V) (x y : V) (N : ℕ) :
    MeasurableSet (P.pairMergeError x y N) :=
  ((P.measurableSet_cluster_infinite x).inter
    (P.measurableSet_cluster_infinite y)).diff
      (P.connectedWithinOrbit_measurableSet x y N)

theorem PeriodicGraph.pairMergeError_antitone
    (P : PeriodicGraph V) (x y : V) :
    Antitone (P.pairMergeError x y) := by
  intro n m hnm omega herror
  exact ⟨herror.1, fun hm =>
    herror.2 (P.connectedWithinOrbit_mono x y hnm hm)⟩

theorem PeriodicGraph.iInter_pairMergeError_subset_not_unique
    (P : PeriodicGraph V) (x y : V) :
    (⋂ N, P.pairMergeError x y N) ⊆
      {omega | P.HasUniqueInfiniteCluster omega}ᶜ := by
  intro omega herror hunique
  have hzero := Set.mem_iInter.mp herror 0
  have hxinf := hzero.1.1
  have hyinf := hzero.1.2
  have hreach := hunique.2 x y hxinf hyinf
  have htwo : omega ∈ P.twoPointEvent x y := hreach
  rw [← P.iUnion_connectedWithinOrbit x y] at htwo
  obtain ⟨N, hN⟩ := Set.mem_iUnion.mp htwo
  exact (Set.mem_iInter.mp herror N).2 hN




theorem PeriodicGraph.pairMergeError_real_tendsto_zero
    (P : PeriodicGraph V) (mu : Measure (ConfigSpace (Sym2 V)))
    [IsProbabilityMeasure mu]
    (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
    (x y : V) :
    Tendsto (fun N => mu.real (P.pairMergeError x y N))
      atTop (nhds 0) := by
  have hlim : Tendsto (fun N : ℕ => mu (P.pairMergeError x y N)) atTop
      (nhds (mu (⋂ N, P.pairMergeError x y N))) :=
    tendsto_measure_iInter_atTop
      (μ := mu)
      (fun N => (P.pairMergeError_measurableSet x y N).nullMeasurableSet)
      (P.pairMergeError_antitone x y)
      ⟨0, measure_ne_top mu _⟩
  have hcomplement :
      mu {omega | P.HasUniqueInfiniteCluster omega}ᶜ = 0 :=
    (prob_compl_eq_zero_iff P.measurableSet_hasUniqueInfiniteCluster).2 hunique
  have hinter : mu (⋂ N, P.pairMergeError x y N) = 0 :=
    measure_mono_null (P.iInter_pairMergeError_subset_not_unique x y)
      hcomplement
  rw [hinter] at hlim
  exact (ENNReal.tendsto_toReal (by simp : (0 : ENNReal) ≠ ⊤)).comp hlim


def PeriodicGraph.pairMergeErrorUnion
    (P : PeriodicGraph V) (L R : Finset V) (N : ℕ) :
    Set (ConfigSpace (Sym2 V)) :=
  ⋃ x ∈ L, ⋃ y ∈ R, P.pairMergeError x y N

theorem PeriodicGraph.pairMergeErrorUnion_real_tendsto_zero
    (P : PeriodicGraph V) (mu : Measure (ConfigSpace (Sym2 V)))
    [IsProbabilityMeasure mu]
    (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
    (L R : Finset V) :
    Tendsto (fun N => mu.real (P.pairMergeErrorUnion L R N))
      atTop (nhds 0) := by
  let F : ℕ → ℝ := fun N =>
    ∑ x ∈ L, ∑ y ∈ R, mu.real (P.pairMergeError x y N)
  have hF : Tendsto F atTop (nhds 0) := by
    dsimp [F]
    convert tendsto_finsetSum L (fun x _ =>
      tendsto_finsetSum R (fun y _ =>
        P.pairMergeError_real_tendsto_zero mu hunique x y)) using 1 <;> simp
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hF
  · intro N
    exact measureReal_nonneg
  · intro N
    exact le_trans (measureReal_biUnion_finset_le _ _)
      (Finset.sum_le_sum fun x _ => measureReal_biUnion_finset_le _ _)

theorem PeriodicGraph.hasUniqueInfiniteCluster_translate_preimage
    (P : PeriodicGraph V) (z : Site 2) :
    P.configTranslate z ⁻¹'
        {omega | P.HasUniqueInfiniteCluster omega} =
      {omega | P.HasUniqueInfiniteCluster omega} := by
  ext omega
  exact P.hasUniqueInfiniteCluster_configTranslate z omega

theorem PeriodicGraph.clusterInfinite_translate_preimage
    (P : PeriodicGraph V) (z : Site 2) (x : V) :
    P.configTranslate z ⁻¹'
        {omega | (P.cluster omega (P.shift z x)).Infinite} =
      {omega | (P.cluster omega x).Infinite} := by
  ext omega
  exact P.cluster_infinite_configTranslate z omega x




theorem PeriodicGraph.exists_fundamental_clusterInfinite_pos
    (P : PeriodicGraph V) (mu : Measure (ConfigSpace (Sym2 V)))
    [IsProbabilityMeasure mu] (hTI : P.IsTranslationInvariant mu)
    (hexists : mu {omega | P.HasInfiniteCluster omega} = 1) :
    ∃ u ∈ P.fundamentalDomain,
      0 < mu {omega | (P.cluster omega u).Infinite} := by
  by_contra hnone
  push Not at hnone
  have hrepzero : ∀ u ∈ P.fundamentalDomain,
      mu {omega | (P.cluster omega u).Infinite} = 0 := by
    intro u hu
    exact le_antisymm (hnone u hu) bot_le
  have hallzero : ∀ x : V,
      mu {omega | (P.cluster omega x).Infinite} = 0 := by
    intro x
    obtain ⟨z, u, hu, rfl⟩ := P.covers x
    calc
      mu {omega | (P.cluster omega (P.shift z u)).Infinite} =
          mu (P.configTranslate z ⁻¹'
            {omega | (P.cluster omega (P.shift z u)).Infinite}) :=
        ((hTI z).measure_preimage
          (P.measurableSet_cluster_infinite
            (P.shift z u)).nullMeasurableSet).symm
      _ = mu {omega | (P.cluster omega u).Infinite} := by
        rw [P.clusterInfinite_translate_preimage]
      _ = 0 := hrepzero u hu
  have hunion : mu (⋃ x : V,
      {omega : ConfigSpace (Sym2 V) |
        (P.cluster omega x).Infinite}) = 0 :=
    MeasureTheory.measure_iUnion_null hallzero
  have heq : {omega : ConfigSpace (Sym2 V) |
      P.HasInfiniteCluster omega} =
      ⋃ x : V, {omega : ConfigSpace (Sym2 V) |
        (P.cluster omega x).Infinite} := by
    ext omega
    simp [PeriodicGraph.HasInfiniteCluster]
  rw [heq, hunion] at hexists
  exact one_ne_zero hexists.symm

namespace PeriodicPlanarDualPair



theorem dual_planeRect_eq
    (D : PeriodicPlanarDualPair P Pdual) (a b c d : ℝ) :
    D.dualEmbedding.planeRect a b c d =
      D.primalEmbedding.planeRect a b c d := by
  ext z
  simp only [PeriodicPlaneEmbedding.planeRect, Set.mem_setOf_eq]
  rw [D.coordinates_eq]



theorem exists_common_edgeArc_displacement_bound
    (D : PeriodicPlanarDualPair P Pdual) :
    ∃ B : ℝ, 0 < B ∧
      (∀ {x y : V} (hxy : P.graph.Adj x y) (t) (i : Fin 2),
        |D.primalEmbedding.coordinates
          (D.primalEmbedding.edgeArc hxy t - D.primalEmbedding.vertex x) i| ≤ B) ∧
      (∀ {x y : W} (hxy : Pdual.graph.Adj x y) (t) (i : Fin 2),
        |D.dualEmbedding.coordinates
          (D.dualEmbedding.edgeArc hxy t - D.dualEmbedding.vertex x) i| ≤ B) := by
  obtain ⟨Bp, hBp0, hBp⟩ :=
    D.primalEmbedding.exists_edgeArc_displacement_bound
  obtain ⟨Bd, hBd0, hBd⟩ :=
    D.dualEmbedding.exists_edgeArc_displacement_bound
  let B := max Bp Bd + 1
  refine ⟨B, by dsimp [B]; linarith [le_max_left Bp Bd, hBp0], ?_, ?_⟩
  · intro x y hxy t i
    exact (hBp hxy t i).trans (by dsimp [B]; linarith [le_max_left Bp Bd])
  · intro x y hxy t i
    exact (hBd hxy t i).trans (by dsimp [B]; linarith [le_max_right Bp Bd])

theorem dualConfigEquiv_configTranslate
    (D : PeriodicPlanarDualPair P Pdual) (z : Site 2)
    (omega : ConfigSpace (Sym2 V)) :
    dualConfigEquiv D.edgeDual (P.configTranslate z omega) =
      Pdual.configTranslate z (dualConfigEquiv D.edgeDual omega) := by
  funext e
  have hshift := D.edgeDual_shift (-z) (D.edgeDual.symm e)
  simp only [Equiv.apply_symm_apply] at hshift
  have hsymm : D.edgeDual.symm
        (Sym2.map (Pdual.shift (-z)) e) =
      Sym2.map (P.shift (-z)) (D.edgeDual.symm e) := by
    rw [← hshift]
    simp
  simp only [dualConfigEquiv_apply, PeriodicGraph.configTranslate]
  rw [hsymm]



noncomputable def dualMeasure
    (D : PeriodicPlanarDualPair P Pdual)
    (mu : Measure (ConfigSpace (Sym2 V))) :
    Measure (ConfigSpace (Sym2 W)) :=
  mu.map (dualConfigEquiv D.edgeDual)

theorem dualMeasure_isTranslationInvariant
    (D : PeriodicPlanarDualPair P Pdual)
    (mu : Measure (ConfigSpace (Sym2 V)))
    (hTI : P.IsTranslationInvariant mu) :
    Pdual.IsTranslationInvariant (D.dualMeasure mu) := by
  intro z
  refine MeasurePreserving.mk (Pdual.measurable_configTranslate z) ?_
  unfold dualMeasure
  rw [Measure.map_map (Pdual.measurable_configTranslate z)
    (continuous_dualConfigEquiv D.edgeDual).measurable]
  have hcomp : Pdual.configTranslate z ∘ dualConfigEquiv D.edgeDual =
      dualConfigEquiv D.edgeDual ∘ P.configTranslate z := by
    funext omega
    exact (D.dualConfigEquiv_configTranslate z omega).symm
  rw [hcomp, ← Measure.map_map
    (continuous_dualConfigEquiv D.edgeDual).measurable
    (P.measurable_configTranslate z), (hTI z).map_eq]



theorem no_open_primal_dual_edge_crossing
    (D : PeriodicPlanarDualPair P Pdual)
    (omega : ConfigSpace (Sym2 V))
    {x y : V} {a b : W}
    (hxy : P.graph.Adj x y) (hab : Pdual.graph.Adj a b)
    (hopen : omega s(x, y) = true)
    (hdualOpen : dualConfigEquiv D.edgeDual omega s(a, b) = true)
    {t u} (hcross : D.primalEmbedding.edgeArc hxy t =
      D.dualEmbedding.edgeArc hab u) : False := by
  have hedge := D.edgeDual_of_crossing hxy hab t u hcross
  have hinv : D.edgeDual.symm s(a, b) = s(x, y) := by
    rw [← hedge]
    simp
  simp only [dualConfigEquiv_apply, hinv, hopen, Bool.not_true] at hdualOpen
  exact Bool.false_ne_true hdualOpen




theorem no_open_primal_dual_walkArc_crossing
    (D : PeriodicPlanarDualPair P Pdual)
    (omega : ConfigSpace (Sym2 V))
    {x y : V} {a b : W}
    (p : P.graph.Walk x y) (q : Pdual.graph.Walk a b)
    (hp : ¬ p.Nil) (hq : ¬ q.Nil)
    (hpopen : ∀ {u v : V}, s(u, v) ∈ p.edges →
      omega s(u, v) = true)
    (hqopen : ∀ {u v : W}, s(u, v) ∈ q.edges →
      dualConfigEquiv D.edgeDual omega s(u, v) = true) :
    Disjoint (Set.range (D.primalEmbedding.walkArc p))
      (Set.range (D.dualEmbedding.walkArc q)) := by
  rw [Set.disjoint_left]
  intro z hzp hzd
  obtain ⟨u, v, huv, huvEdge, huvArc⟩ :=
    D.primalEmbedding.mem_walkArc_range_of_not_nil p hp hzp
  obtain ⟨r, s, hrs, hrsEdge, hrsArc⟩ :=
    D.dualEmbedding.mem_walkArc_range_of_not_nil q hq hzd
  obtain ⟨t, ht⟩ := huvArc
  obtain ⟨w, hw⟩ := hrsArc
  exact D.no_open_primal_dual_edge_crossing omega huv hrs
    (hpopen huvEdge) (hqopen hrsEdge) (ht.trans hw.symm)



theorem no_openRectWalkArc_crossing
    (D : PeriodicPlanarDualPair P Pdual)
    (omega : ConfigSpace (Sym2 V))
    {ap bp cp dp ad bd cd dd : ℝ}
    {xp yp : D.primalEmbedding.RectVertex ap bp cp dp}
    {xd yd : D.dualEmbedding.RectVertex ad bd cd dd}
    (p : (FK.openSub (D.primalEmbedding.rectGraph ap bp cp dp)
      (D.primalEmbedding.rectRestrict ap bp cp dp omega)).Walk xp yp)
    (q : (FK.openSub (D.dualEmbedding.rectGraph ad bd cd dd)
      (D.dualEmbedding.rectRestrict ad bd cd dd
        (dualConfigEquiv D.edgeDual omega))).Walk xd yd)
    (hp : ¬ (p.map (D.primalEmbedding.openRectHom ap bp cp dp
      (D.primalEmbedding.rectRestrict ap bp cp dp omega))).Nil)
    (hq : ¬ (q.map (D.dualEmbedding.openRectHom ad bd cd dd
      (D.dualEmbedding.rectRestrict ad bd cd dd
        (dualConfigEquiv D.edgeDual omega)))).Nil) :
    Disjoint
      (Set.range (D.primalEmbedding.walkArc
        (p.map (D.primalEmbedding.openRectHom ap bp cp dp
          (D.primalEmbedding.rectRestrict ap bp cp dp omega)))))
      (Set.range (D.dualEmbedding.walkArc
        (q.map (D.dualEmbedding.openRectHom ad bd cd dd
          (D.dualEmbedding.rectRestrict ad bd cd dd
            (dualConfigEquiv D.edgeDual omega)))))) := by
  apply D.no_open_primal_dual_walkArc_crossing omega _ _ hp hq
  · intro u v huv
    exact D.primalEmbedding.openRectWalk_edge_open p huv
  · intro u v huv
    exact D.dualEmbedding.openRectWalk_edge_open q huv





theorem matchedCrossingEvents_disjoint
    (D : PeriodicPlanarDualPair P Pdual) {B a b c d : ℝ}
    (hBpos : 0 < B)
    (hBp : ∀ {x y : V} (hxy : P.graph.Adj x y) (t) (i : Fin 2),
      |D.primalEmbedding.coordinates
        (D.primalEmbedding.edgeArc hxy t - D.primalEmbedding.vertex x) i| ≤ B)
    (hBd : ∀ {x y : W} (hxy : Pdual.graph.Adj x y) (t) (i : Fin 2),
      |D.dualEmbedding.coordinates
        (D.dualEmbedding.edgeArc hxy t - D.dualEmbedding.vertex x) i| ≤ B)
    (hab : a + 5 * B < b - 5 * B)
    (hcd : c + 5 * B < d - 5 * B) :
    Disjoint
      (D.primalEmbedding.horizontalCrossingEvent
        a b (c + 4 * B) (d - 4 * B))
      ((dualConfigEquiv D.edgeDual) ⁻¹'
        D.dualEmbedding.verticalCrossingEvent
          (a + 4 * B) (b - 4 * B) c d) := by
  rw [Set.disjoint_left]
  intro omega hH hV
  change D.primalEmbedding.rectRestrict a b (c + 4 * B) (d - 4 * B) omega ∈
    D.primalEmbedding.finiteHorizontalCrossing
      a b (c + 4 * B) (d - 4 * B) at hH
  change D.dualEmbedding.rectRestrict (a + 4 * B) (b - 4 * B) c d
      (dualConfigEquiv D.edgeDual omega) ∈
    D.dualEmbedding.finiteVerticalCrossing
      (a + 4 * B) (b - 4 * B) c d at hV
  rcases hH with ⟨xp, yp, hxp, hyp, hpReach⟩
  rcases hV with ⟨xd, yd, hxd, hyd, hdReach⟩
  obtain ⟨p⟩ := hpReach
  obtain ⟨q⟩ := hdReach
  obtain ⟨xl, hxl, hxlcoord⟩ := hxp
  obtain ⟨xr, hxr, hxrcoord⟩ := hyp
  obtain ⟨xb, hxb, hxbcoord⟩ := hxd
  obtain ⟨xt, hxt, hxtcoord⟩ := hyd
  let pfull : P.graph.Walk xp.1 yp.1 := p.map (D.primalEmbedding.openRectHom
    a b (c + 4 * B) (d - 4 * B)
      (D.primalEmbedding.rectRestrict
        a b (c + 4 * B) (d - 4 * B) omega))
  let qfull : Pdual.graph.Walk xd.1 yd.1 := q.map (D.dualEmbedding.openRectHom
    (a + 4 * B) (b - 4 * B) c d
      (D.dualEmbedding.rectRestrict (a + 4 * B) (b - 4 * B) c d
        (dualConfigEquiv D.edgeDual omega)))
  let gamma0 := D.primalEmbedding.walkArc pfull
  let eta0 := D.dualEmbedding.walkArc qfull
  let gamma := (D.primalEmbedding.edgeArc hxl).symm.trans
    (gamma0.trans (D.primalEmbedding.edgeArc hxr))
  let eta := (D.dualEmbedding.edgeArc hxb).symm.trans
    (eta0.trans (D.dualEmbedding.edgeArc hxt))
  have hxpNear := D.primalEmbedding.rectLeftBoundary_coord_lt hBp
    (show D.primalEmbedding.rectLeftBoundary
      a b (c + 4 * B) (d - 4 * B) xp from ⟨xl, hxl, hxlcoord⟩)
  have hypNear := D.primalEmbedding.rectRightBoundary_coord_gt hBp
    (show D.primalEmbedding.rectRightBoundary
      a b (c + 4 * B) (d - 4 * B) yp from ⟨xr, hxr, hxrcoord⟩)
  have hxdNear := D.dualEmbedding.rectBottomBoundary_coord_lt hBd
    (show D.dualEmbedding.rectBottomBoundary
      (a + 4 * B) (b - 4 * B) c d xd from ⟨xb, hxb, hxbcoord⟩)
  have hydNear := D.dualEmbedding.rectTopBoundary_coord_gt hBd
    (show D.dualEmbedding.rectTopBoundary
      (a + 4 * B) (b - 4 * B) c d yd from ⟨xt, hxt, hxtcoord⟩)
  have hpNotNil : ¬ pfull.Nil := by
    apply SimpleGraph.Walk.not_nil_of_ne
    change xp.1 ≠ yp.1
    intro heq
    rw [heq] at hxpNear
    linarith
  have hqNotNil : ¬ qfull.Nil := by
    apply SimpleGraph.Walk.not_nil_of_ne
    change xd.1 ≠ yd.1
    intro heq
    rw [heq] at hxdNear
    linarith
  have hgammaRect : Set.range gamma ⊆
      D.primalEmbedding.planeRect
        (a - B) (b + B) ((c + 4 * B) - B) ((d - 4 * B) + B) := by
    intro z hz
    dsimp only [gamma] at hz
    rw [Path.trans_range] at hz
    rcases hz with hleft | hrest
    rw [Path.symm_range] at hleft
    · obtain ⟨t, rfl⟩ := hleft
      exact D.primalEmbedding.edgeArc_mem_expanded_planeRect hBp hxl xp.2 t
    · simp only [Path.trans_range, Set.mem_union] at hrest
      rcases hrest with hcore | hright
      · exact D.primalEmbedding.openRectWalkArc_range_subset
          hBpos.le hBp p hcore
      · obtain ⟨t, rfl⟩ := hright
        exact D.primalEmbedding.edgeArc_mem_expanded_planeRect hBp hxr yp.2 t
  have hetaRectDual : Set.range eta ⊆
      D.dualEmbedding.planeRect
        ((a + 4 * B) - B) ((b - 4 * B) + B) (c - B) (d + B) := by
    intro z hz
    dsimp only [eta] at hz
    rw [Path.trans_range] at hz
    rcases hz with hbottom | hrest
    rw [Path.symm_range] at hbottom
    · obtain ⟨t, rfl⟩ := hbottom
      exact D.dualEmbedding.edgeArc_mem_expanded_planeRect hBd hxb xd.2 t
    · simp only [Path.trans_range, Set.mem_union] at hrest
      rcases hrest with hcore | htop
      · exact D.dualEmbedding.openRectWalkArc_range_subset
          hBpos.le hBd q hcore
      · obtain ⟨t, rfl⟩ := htop
        exact D.dualEmbedding.edgeArc_mem_expanded_planeRect hBd hxt yd.2 t
  let gammaC := gamma.map D.primalEmbedding.coordinates.continuous
  let etaC := eta.map D.primalEmbedding.coordinates.continuous
  have hgammaY : ∀ t : unitInterval,
      c < gammaC t 1 ∧ gammaC t 1 < d := by
    intro t
    have ht := hgammaRect ⟨t, rfl⟩
    change c < D.primalEmbedding.coordinates (gamma t) 1 ∧
      D.primalEmbedding.coordinates (gamma t) 1 < d
    change a - B ≤ D.primalEmbedding.coordinates (gamma t) 0 ∧
      D.primalEmbedding.coordinates (gamma t) 0 ≤ b + B ∧
      (c + 4 * B) - B ≤ D.primalEmbedding.coordinates (gamma t) 1 ∧
      D.primalEmbedding.coordinates (gamma t) 1 ≤ (d - 4 * B) + B at ht
    constructor <;> linarith
  have hetaX : ∀ t : unitInterval,
      a < etaC t 0 ∧ etaC t 0 < b := by
    intro t
    have ht := hetaRectDual ⟨t, rfl⟩
    rw [D.dual_planeRect_eq] at ht
    change a < D.primalEmbedding.coordinates (eta t) 0 ∧
      D.primalEmbedding.coordinates (eta t) 0 < b
    change (a + 4 * B) - B ≤ D.primalEmbedding.coordinates (eta t) 0 ∧
      D.primalEmbedding.coordinates (eta t) 0 ≤ (b - 4 * B) + B ∧
      c - B ≤ D.primalEmbedding.coordinates (eta t) 1 ∧
      D.primalEmbedding.coordinates (eta t) 1 ≤ d + B at ht
    constructor <;> linarith
  have hgammaLeft : D.primalEmbedding.coordinates
      (D.primalEmbedding.vertex xl) 0 < a := by
    change D.primalEmbedding.vertexCoord xl 0 < a
    exact hxlcoord
  have hgammaRight : b < D.primalEmbedding.coordinates
      (D.primalEmbedding.vertex xr) 0 := by
    change b < D.primalEmbedding.vertexCoord xr 0
    exact hxrcoord
  have hetaBottom : D.primalEmbedding.coordinates
      (D.dualEmbedding.vertex xb) 1 < c := by
    change D.primalEmbedding.coordinates (D.dualEmbedding.vertex xb) 1 < c
    rw [D.coordinates_eq]
    exact hxbcoord
  have hetaTop : d < D.primalEmbedding.coordinates
      (D.dualEmbedding.vertex xt) 1 := by
    change d < D.primalEmbedding.coordinates (D.dualEmbedding.vertex xt) 1
    rw [D.coordinates_eq]
    exact hxtcoord
  have hab0 : a < b := by linarith
  have hcd0 : c < d := by linarith
  obtain ⟨t, s, hcrossC⟩ :=
    ContinuousRectangleCrossing.strip_paths_intersect hab0 hcd0 gammaC etaC
      hgammaLeft hgammaRight hetaBottom hetaTop hgammaY hetaX
  have hcross : gamma t = eta s := by
    apply D.primalEmbedding.coordinates.injective
    simpa [gammaC, etaC] using hcrossC
  have htRect := hgammaRect ⟨t, rfl⟩
  have hsRect := hetaRectDual ⟨s, rfl⟩
  rw [D.dual_planeRect_eq] at hsRect
  change a - B ≤ D.primalEmbedding.coordinates (gamma t) 0 ∧
    D.primalEmbedding.coordinates (gamma t) 0 ≤ b + B ∧
    (c + 4 * B) - B ≤ D.primalEmbedding.coordinates (gamma t) 1 ∧
    D.primalEmbedding.coordinates (gamma t) 1 ≤ (d - 4 * B) + B at htRect
  change (a + 4 * B) - B ≤ D.primalEmbedding.coordinates (eta s) 0 ∧
    D.primalEmbedding.coordinates (eta s) 0 ≤ (b - 4 * B) + B ∧
    c - B ≤ D.primalEmbedding.coordinates (eta s) 1 ∧
    D.primalEmbedding.coordinates (eta s) 1 ≤ d + B at hsRect
  have htCore : gamma t ∈ Set.range gamma0 := by
    have ht : gamma t ∈ Set.range gamma := ⟨t, rfl⟩
    dsimp only [gamma] at ht
    rw [Path.trans_range] at ht
    rcases ht with hleft | hrest
    rw [Path.symm_range] at hleft
    · obtain ⟨r, hr⟩ := hleft
      have hu := D.primalEmbedding.edgeArc_coord_le_vertex_add hBp hxl r 0
      rw [hr] at hu
      rw [hcross] at hu
      linarith
    · simp only [Path.trans_range, Set.mem_union] at hrest
      rcases hrest with hcore | hright
      · exact hcore
      · obtain ⟨r, hr⟩ := hright
        have hu := D.primalEmbedding.vertex_sub_le_edgeArc_coord hBp hxr r 0
        rw [hr] at hu
        rw [hcross] at hu
        linarith
  have hsCore : eta s ∈ Set.range eta0 := by
    have hs : eta s ∈ Set.range eta := ⟨s, rfl⟩
    dsimp only [eta] at hs
    rw [Path.trans_range] at hs
    rcases hs with hbottom | hrest
    rw [Path.symm_range] at hbottom
    · obtain ⟨r, hr⟩ := hbottom
      have hu := D.dualEmbedding.edgeArc_coord_le_vertex_add hBd hxb r 1
      rw [hr] at hu
      rw [← D.coordinates_eq] at hu
      rw [← hcross] at hu
      linarith
    · simp only [Path.trans_range, Set.mem_union] at hrest
      rcases hrest with hcore | htop
      · exact hcore
      · obtain ⟨r, hr⟩ := htop
        have hu := D.dualEmbedding.vertex_sub_le_edgeArc_coord hBd hxt r 1
        rw [hr] at hu
        rw [← D.coordinates_eq] at hu
        rw [← hcross] at hu
        linarith
  have hdisj := D.no_openRectWalkArc_crossing omega p q hpNotNil hqNotNil
  exact Set.disjoint_left.mp hdisj htCore (hcross.symm ▸ hsCore)

theorem matchedCrossing_measureReal_add_le_one
    (D : PeriodicPlanarDualPair P Pdual)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    {B a b c d : ℝ}
    (hBpos : 0 < B)
    (hBp : ∀ {x y : V} (hxy : P.graph.Adj x y) (t) (i : Fin 2),
      |D.primalEmbedding.coordinates
        (D.primalEmbedding.edgeArc hxy t - D.primalEmbedding.vertex x) i| ≤ B)
    (hBd : ∀ {x y : W} (hxy : Pdual.graph.Adj x y) (t) (i : Fin 2),
      |D.dualEmbedding.coordinates
        (D.dualEmbedding.edgeArc hxy t - D.dualEmbedding.vertex x) i| ≤ B)
    (hab : a + 5 * B < b - 5 * B)
    (hcd : c + 5 * B < d - 5 * B) :
    mu.real (D.primalEmbedding.horizontalCrossingEvent
        a b (c + 4 * B) (d - 4 * B)) +
      mu.real ((dualConfigEquiv D.edgeDual) ⁻¹'
        D.dualEmbedding.verticalCrossingEvent
          (a + 4 * B) (b - 4 * B) c d) ≤ 1 := by
  let H := D.primalEmbedding.horizontalCrossingEvent
    a b (c + 4 * B) (d - 4 * B)
  let Vd := (dualConfigEquiv D.edgeDual) ⁻¹'
    D.dualEmbedding.verticalCrossingEvent (a + 4 * B) (b - 4 * B) c d
  have hdisj : Disjoint H Vd :=
    D.matchedCrossingEvents_disjoint hBpos hBp hBd hab hcd
  have hVd : MeasurableSet Vd :=
    (D.dualEmbedding.verticalCrossingEvent_measurableSet
      (a + 4 * B) (b - 4 * B) c d).preimage
        (continuous_dualConfigEquiv D.edgeDual).measurable
  have hu : mu.real (H ∪ Vd) ≤ 1 := measureReal_le_one
  rw [measureReal_union hdisj hVd] at hu
  exact hu




theorem exists_buffer_matchedCrossing_measureReal_add_le_one
    (D : PeriodicPlanarDualPair P Pdual)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu] :
    ∃ B : ℝ, 0 < B ∧ ∀ {a b c d : ℝ},
      a + 5 * B < b - 5 * B → c + 5 * B < d - 5 * B →
      mu.real (D.primalEmbedding.horizontalCrossingEvent
          a b (c + 4 * B) (d - 4 * B)) +
        mu.real ((dualConfigEquiv D.edgeDual) ⁻¹'
          D.dualEmbedding.verticalCrossingEvent
            (a + 4 * B) (b - 4 * B) c d) ≤ 1 := by
  obtain ⟨B, hBpos, hBp, hBd⟩ :=
    D.exists_common_edgeArc_displacement_bound
  refine ⟨B, hBpos, ?_⟩
  intro a b c d hab hcd
  exact D.matchedCrossing_measureReal_add_le_one
    mu hBpos hBp hBd hab hcd



def commonUniqueInfiniteClusterEvent
    (D : PeriodicPlanarDualPair P Pdual) :
    Set (ConfigSpace (Sym2 V)) :=
  {omega | P.HasUniqueInfiniteCluster omega} ∩
    (dualConfigEquiv D.edgeDual) ⁻¹'
      {eta | Pdual.HasUniqueInfiniteCluster eta}

theorem commonUniqueInfiniteClusterEvent_measurableSet
    (D : PeriodicPlanarDualPair P Pdual) :
    MeasurableSet D.commonUniqueInfiniteClusterEvent :=
  P.measurableSet_hasUniqueInfiniteCluster.inter
    (Pdual.measurableSet_hasUniqueInfiniteCluster.preimage
      (continuous_dualConfigEquiv D.edgeDual).measurable)

theorem commonUniqueInfiniteClusterEvent_translate_preimage
    (D : PeriodicPlanarDualPair P Pdual) (z : Site 2) :
    P.configTranslate z ⁻¹' D.commonUniqueInfiniteClusterEvent =
      D.commonUniqueInfiniteClusterEvent := by
  ext omega
  simp only [commonUniqueInfiniteClusterEvent, Set.mem_preimage,
    Set.mem_inter_iff, Set.mem_setOf_eq]
  rw [P.hasUniqueInfiniteCluster_configTranslate,
    D.dualConfigEquiv_configTranslate,
    Pdual.hasUniqueInfiniteCluster_configTranslate]

theorem commonUniqueInfiniteClusterEvent_measure_eq_one
    (D : PeriodicPlanarDualPair P Pdual)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hprimal : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
    (hdual : mu ((dualConfigEquiv D.edgeDual) ⁻¹'
      {eta | Pdual.HasUniqueInfiniteCluster eta}) = 1) :
    mu D.commonUniqueInfiniteClusterEvent = 1 := by
  let A := {omega : ConfigSpace (Sym2 V) |
    P.HasUniqueInfiniteCluster omega}
  let B := (dualConfigEquiv D.edgeDual) ⁻¹'
    {eta | Pdual.HasUniqueInfiniteCluster eta}
  have hAmeas : MeasurableSet A :=
    P.measurableSet_hasUniqueInfiniteCluster
  have hBmeas : MeasurableSet B :=
    Pdual.measurableSet_hasUniqueInfiniteCluster.preimage
      (continuous_dualConfigEquiv D.edgeDual).measurable
  have hAc : mu Aᶜ = 0 := (prob_compl_eq_zero_iff hAmeas).2 hprimal
  have hBc : mu Bᶜ = 0 := (prob_compl_eq_zero_iff hBmeas).2 hdual
  have hinterc : mu (A ∩ B)ᶜ = 0 := by
    rw [compl_inter]
    exact MeasureTheory.measure_union_null hAc hBc
  change mu (A ∩ B) = 1
  simpa using MeasureTheory.measure_of_measure_compl_eq_zero hinterc

theorem exists_primal_dual_fundamental_clusterInfinite_pos
    (D : PeriodicPlanarDualPair P Pdual)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hTI : P.IsTranslationInvariant mu)
    (hprimal : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
    (hdual : mu ((dualConfigEquiv D.edgeDual) ⁻¹'
      {eta | Pdual.HasUniqueInfiniteCluster eta}) = 1) :
    (∃ u ∈ P.fundamentalDomain,
      0 < mu {omega | (P.cluster omega u).Infinite}) ∧
    (∃ w ∈ Pdual.fundamentalDomain,
      0 < D.dualMeasure mu
        {eta | (Pdual.cluster eta w).Infinite}) := by
  have hprimalExists : mu {omega | P.HasInfiniteCluster omega} = 1 := by
    apply le_antisymm prob_le_one
    rw [← hprimal]
    exact measure_mono fun omega h => h.1
  have hleft := P.exists_fundamental_clusterInfinite_pos
    mu hTI hprimalExists
  letI : IsProbabilityMeasure (D.dualMeasure mu) :=
    Measure.isProbabilityMeasure_map
      (continuous_dualConfigEquiv D.edgeDual).measurable.aemeasurable
  have hdualUnique : D.dualMeasure mu
      {eta | Pdual.HasUniqueInfiniteCluster eta} = 1 := by
    unfold dualMeasure
    rw [Measure.map_apply
      (continuous_dualConfigEquiv D.edgeDual).measurable
      Pdual.measurableSet_hasUniqueInfiniteCluster]
    exact hdual
  have hdualExists : D.dualMeasure mu
      {eta | Pdual.HasInfiniteCluster eta} = 1 := by
    apply le_antisymm prob_le_one
    rw [← hdualUnique]
    exact measure_mono fun eta h => h.1
  have hright := Pdual.exists_fundamental_clusterInfinite_pos
    (D.dualMeasure mu) (D.dualMeasure_isTranslationInvariant mu hTI)
      hdualExists
  exact ⟨hleft, hright⟩

end PeriodicPlanarDualPair

end StatMech.FK.PeriodicPlanar

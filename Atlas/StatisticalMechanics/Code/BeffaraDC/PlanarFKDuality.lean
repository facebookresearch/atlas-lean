/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/












import Code.Ising.KWGeometricDual
import Code.BeffaraDC.Duality

open Finset SimpleGraph Set

namespace StatMech
namespace BeffaraDC

open Lattice Ising Walls




noncomputable def pfdClosedDual (P : PlanarZ2Subgraph) (K : SimpleGraph P.V) :
    SimpleGraph (kwg_Face P) where
  Adj C D := C ≠ D ∧ ∃ e : kwg_Edge P,
    e.1 ∉ K.edgeSet ∧ kwg_dualEnds P e = s(C, D)
  symm := by
    rintro C D ⟨hne, e, heK, he⟩
    exact ⟨hne.symm, e, heK, he.trans Sym2.eq_swap⟩
  loopless := ⟨fun C h => h.1 rfl⟩

@[simp] theorem pfdClosedDual_adj (P : PlanarZ2Subgraph) (K : SimpleGraph P.V)
    (C D : kwg_Face P) :
    (pfdClosedDual P K).Adj C D ↔ C ≠ D ∧ ∃ e : kwg_Edge P,
      e.1 ∉ K.edgeSet ∧ kwg_dualEnds P e = s(C, D) :=
  Iff.rfl


noncomputable def pfdFace (P : PlanarZ2Subgraph) (f : Site 2) : kwg_Face P :=
  (whb_faceRegion (imageGraph P)).connectedComponentMk f



theorem pfd_faceStep (P : PlanarZ2Subgraph) (K : SimpleGraph P.V)
    {f g : Site 2} (hfg : (whb_faceRegion (jei_pushGraph P K)).Adj f g) :
    (pfdClosedDual P K).Reachable (pfdFace P f) (pfdFace P g) := by
  classical
  by_cases hwall : sharedPrimalEdge f g ∈ (imageGraph P).edgeSet
  · induction hshared : sharedPrimalEdge f g using Sym2.inductionOn with
    | _ a b =>
      have hab : (imageGraph P).Adj a b := by
        rw [← SimpleGraph.mem_edgeSet]
        exact hshared ▸ hwall
      rw [imageGraph_adj] at hab
      obtain ⟨x, y, hxy, hx, hy⟩ := hab
      have hnotK : ¬ K.Adj x y := by
        intro hKxy
        apply hfg.2
        rw [hshared, SimpleGraph.mem_edgeSet, jei_pushGraph_adj]
        refine ⟨x, y, hKxy, hx, hy⟩
      let e : kwg_Edge P := ⟨s(x, y), (SimpleGraph.mem_edgeSet P.G).mpr hxy⟩
      have heK : e.1 ∉ K.edgeSet := by
        rw [SimpleGraph.mem_edgeSet]
        exact hnotK
      have hemb : kwg_embeddedEdge P e = sharedPrimalEdge f g := by
        rw [hshared, ← hx, ← hy]
        rfl
      have hflank : s(kwg_flankLeft P e, kwg_flankRight P e) = s(f, g) :=
        (jce_sharedPrimalEdge_inj (kwg_flanks_adj P e) hfg.1).mpr
          ((kwg_flanks_shared P e).trans hemb)
      have hends : kwg_dualEnds P e = s(pfdFace P f, pfdFace P g) := by
        unfold kwg_dualEnds pfdFace
        exact congrArg (Sym2.map
          ((whb_faceRegion (imageGraph P)).connectedComponentMk)) hflank
      by_cases heq : pfdFace P f = pfdFace P g
      · simpa [heq]
      · exact (pfdClosedDual_adj P K _ _).2 ⟨heq, e, heK, hends⟩ |>.reachable
  · have hamb : (whb_faceRegion (imageGraph P)).Adj f g := ⟨hfg.1, hwall⟩
    have heq : pfdFace P f = pfdFace P g :=
      ConnectedComponent.connectedComponentMk_eq_of_adj hamb
    simpa [heq]


theorem pfd_regionReachable_to_dual (P : PlanarZ2Subgraph) (K : SimpleGraph P.V)
    {f g : Site 2}
    (hfg : (whb_faceRegion (jei_pushGraph P K)).Reachable f g) :
    (pfdClosedDual P K).Reachable (pfdFace P f) (pfdFace P g) := by
  rcases hfg with ⟨w⟩
  induction w with
  | nil => exact ⟨Walk.nil⟩
  | @cons a b c hab w ih => exact (pfd_faceStep P K hab).trans ih



theorem pfd_embeddedEdge_not_mem_push (P : PlanarZ2Subgraph) (K : SimpleGraph P.V)
    (e : kwg_Edge P) (heK : e.1 ∉ K.edgeSet) :
    kwg_embeddedEdge P e ∉ (jei_pushGraph P K).edgeSet := by
  rcases e with ⟨e, heG⟩
  induction e using Sym2.inductionOn with
  | _ x y =>
      intro hmem
      have hadj : (jei_pushGraph P K).Adj (P.emb x) (P.emb y) := by
        rw [← SimpleGraph.mem_edgeSet]
        exact hmem
      rw [jei_pushGraph_adj] at hadj
      obtain ⟨a, b, hab, ha, hb⟩ := hadj
      have hax : a = x := P.emb.injective ha
      have hby : b = y := P.emb.injective hb
      subst a
      subst b
      exact heK ((SimpleGraph.mem_edgeSet K).mpr hab)



theorem pfd_ambientFace_le_openFace (P : PlanarZ2Subgraph) (K : SimpleGraph P.V)
    (hKP : K ≤ P.G) :
    whb_faceRegion (imageGraph P) ≤ whb_faceRegion (jei_pushGraph P K) := by
  apply jwc_faceRegion_antitone
  rw [← jei_pushGraph_G P]
  exact jwc_pushGraph_mono P hKP



theorem pfd_dualAdj_to_regionReachable (P : PlanarZ2Subgraph) (K : SimpleGraph P.V)
    (hKP : K ≤ P.G) {f g : Site 2}
    (hfg : (pfdClosedDual P K).Adj (pfdFace P f) (pfdFace P g)) :
    (whb_faceRegion (jei_pushGraph P K)).Reachable f g := by
  classical
  obtain ⟨_, e, heK, hends⟩ := (pfdClosedDual_adj P K _ _).mp hfg
  let R := whb_faceRegion (imageGraph P)
  let L := kwg_flankLeft P e
  let U := kwg_flankRight P e
  have hLU : (whb_faceRegion (jei_pushGraph P K)).Adj L U := by
    refine ⟨kwg_flanks_adj P e, ?_⟩
    rw [kwg_flanks_shared P e]
    exact pfd_embeddedEdge_not_mem_push P K e heK
  have hpair : s(R.connectedComponentMk L, R.connectedComponentMk U) =
      s(R.connectedComponentMk f, R.connectedComponentMk g) := by
    simpa only [R, L, U, pfdFace, kwg_dualEnds] using hends
  rw [Sym2.eq_iff] at hpair
  rcases hpair with hpair | hpair
  · have hfL : R.connectedComponentMk f = R.connectedComponentMk L := hpair.1.symm
    have hUg : R.connectedComponentMk U = R.connectedComponentMk g := hpair.2
    exact ((ConnectedComponent.eq.mp hfL).mono (pfd_ambientFace_le_openFace P K hKP)).trans
      (hLU.reachable.trans
        ((ConnectedComponent.eq.mp hUg).mono (pfd_ambientFace_le_openFace P K hKP)))
  · have hfU : R.connectedComponentMk f = R.connectedComponentMk U := hpair.2.symm
    have hLg : R.connectedComponentMk L = R.connectedComponentMk g := hpair.1
    exact ((ConnectedComponent.eq.mp hfU).mono (pfd_ambientFace_le_openFace P K hKP)).trans
      (hLU.symm.reachable.trans
        ((ConnectedComponent.eq.mp hLg).mono (pfd_ambientFace_le_openFace P K hKP)))



theorem pfd_dualWalk_to_regionReachable (P : PlanarZ2Subgraph) (K : SimpleGraph P.V)
    (hKP : K ≤ P.G) {C D : kwg_Face P}
    (w : (pfdClosedDual P K).Walk C D) {f g : Site 2}
    (hf : pfdFace P f = C) (hg : pfdFace P g = D) :
    (whb_faceRegion (jei_pushGraph P K)).Reachable f g := by
  induction w generalizing f with
  | nil =>
      have hcomp : pfdFace P f = pfdFace P g := hf.trans hg.symm
      exact (ConnectedComponent.eq.mp hcomp).mono (pfd_ambientFace_le_openFace P K hKP)
  | @cons A B E hAB w ih =>
      have hout : pfdFace P B.out = B := by
        exact B.out_eq
      have hadj : (pfdClosedDual P K).Adj (pfdFace P f) (pfdFace P B.out) := by
        simpa only [hf, hout] using hAB
      exact (pfd_dualAdj_to_regionReachable P K hKP hadj).trans
        (ih hout hg)



theorem pfd_regionReachable_iff_dual (P : PlanarZ2Subgraph) (K : SimpleGraph P.V)
    (hKP : K ≤ P.G) {f g : Site 2} :
    (whb_faceRegion (jei_pushGraph P K)).Reachable f g ↔
      (pfdClosedDual P K).Reachable (pfdFace P f) (pfdFace P g) := by
  constructor
  · exact pfd_regionReachable_to_dual P K
  · rintro ⟨w⟩
    exact pfd_dualWalk_to_regionReachable P K hKP w rfl rfl



noncomputable def pfdComponentMap (P : PlanarZ2Subgraph) (K : SimpleGraph P.V) :
    (whb_faceRegion (jei_pushGraph P K)).ConnectedComponent →
      (pfdClosedDual P K).ConnectedComponent :=
  fun C => (pfdClosedDual P K).connectedComponentMk (pfdFace P C.out)



noncomputable def pfdComponentEquiv (P : PlanarZ2Subgraph) (K : SimpleGraph P.V)
    (hKP : K ≤ P.G) :
    (whb_faceRegion (jei_pushGraph P K)).ConnectedComponent ≃
      (pfdClosedDual P K).ConnectedComponent := by
  apply Equiv.ofBijective (pfdComponentMap P K)
  constructor
  · intro C D hCD
    have hdual : (pfdClosedDual P K).Reachable (pfdFace P C.out) (pfdFace P D.out) :=
      ConnectedComponent.eq.mp hCD
    have hface := (pfd_regionReachable_iff_dual P K hKP).mpr hdual
    rw [← C.out_eq, ← D.out_eq]
    exact ConnectedComponent.sound hface
  · intro D
    let C := (whb_faceRegion (jei_pushGraph P K)).connectedComponentMk D.out.out
    refine ⟨C, ?_⟩
    rw [← D.out_eq]
    apply ConnectedComponent.sound
    have hface : (whb_faceRegion (jei_pushGraph P K)).Reachable C.out D.out.out :=
      ConnectedComponent.exact C.out_eq
    have hdual := pfd_regionReachable_to_dual P K hface
    have hout : pfdFace P D.out.out = D.out := D.out.out_eq
    simpa only [pfdComponentMap, C, hout] using hdual


theorem pfd_numDualClusters_eq_faceComponents (P : PlanarZ2Subgraph)
    (K : SimpleGraph P.V) (hKP : K ≤ P.G) :
    Nat.card (pfdClosedDual P K).ConnectedComponent =
      Nat.card (whb_faceRegion (jei_pushGraph P K)).ConnectedComponent := by
  rw [Nat.card_congr (pfdComponentEquiv P K hKP)]


def pfdOpenPlanar (P : PlanarZ2Subgraph) (K : SimpleGraph P.V) (hKP : K ≤ P.G) :
    PlanarZ2Subgraph where
  V := P.V
  finV := P.finV
  decV := P.decV
  G := K
  emb := P.emb
  isSub := by
    intro x y h
    exact P.isSub (hKP h)

@[simp] theorem pfdOpenPlanar_imageGraph (P : PlanarZ2Subgraph)
    (K : SimpleGraph P.V) (hKP : K ≤ P.G) :
    imageGraph (pfdOpenPlanar P K hKP) = jei_pushGraph P K := by
  ext a b
  simp only [imageGraph_adj, jei_pushGraph_adj, pfdOpenPlanar]

@[simp] theorem pfdOpenPlanar_graph (P : PlanarZ2Subgraph)
    (K : SimpleGraph P.V) (hKP : K ≤ P.G) :
    (pfdOpenPlanar P K hKP).G = K := rfl



theorem pfd_numFaceComponents_eq_faceCount (P : PlanarZ2Subgraph)
    (K : SimpleGraph P.V) (hKP : K ≤ P.G) :
    Nat.card (whb_faceRegion (jei_pushGraph P K)).ConnectedComponent = faceCount K := by
  have h := kwg_card_face_eq_faceCount (pfdOpenPlanar P K hKP)
  simpa only [kwg_Face, pfdOpenPlanar_imageGraph, pfdOpenPlanar_graph] using h



theorem pfd_numDualClusters_eq_faceCount (P : PlanarZ2Subgraph)
    (K : SimpleGraph P.V) (hKP : K ≤ P.G) :
    Nat.card (pfdClosedDual P K).ConnectedComponent = faceCount K := by
  rw [pfd_numDualClusters_eq_faceComponents P K hKP,
    pfd_numFaceComponents_eq_faceCount P K hKP]








theorem pfd_clusterEuler (P : PlanarZ2Subgraph) (K : SimpleGraph P.V)
    (hKP : K ≤ P.G) :
    Nat.card P.V + Nat.card (pfdClosedDual P K).ConnectedComponent =
      K.edgeSet.ncard + Nat.card K.ConnectedComponent + 1 := by
  rw [pfd_numDualClusters_eq_faceCount P K hKP]
  exact euler_relation K





noncomputable def pfdPrimalWeight (P : PlanarZ2Subgraph) (p q : ℝ)
    (K : SimpleGraph P.V) : ℝ :=
  edgeProductCount p P.G.edgeFinset.card K.edgeSet.ncard *
    q ^ Nat.card K.ConnectedComponent



noncomputable def pfdDualWeight (P : PlanarZ2Subgraph) (p q : ℝ)
    (K : SimpleGraph P.V) : ℝ :=
  edgeProductCount p P.G.edgeFinset.card
      (P.G.edgeFinset.card - K.edgeSet.ncard) *
    q ^ Nat.card (pfdClosedDual P K).ConnectedComponent

theorem pfd_subgraph_edgeCount_le (P : PlanarZ2Subgraph) (K : SimpleGraph P.V)
    (hKP : K ≤ P.G) : K.edgeSet.ncard ≤ P.G.edgeFinset.card := by
  have hset : K.edgeSet ⊆ P.G.edgeSet := SimpleGraph.edgeSet_mono hKP
  have hn := Set.ncard_le_ncard hset (Set.toFinite P.G.edgeSet)
  simpa only [SimpleGraph.edgeFinset, Set.ncard_eq_toFinset_card'] using hn





theorem pfd_weight_duality (P : PlanarZ2Subgraph) (K : SimpleGraph P.V)
    (hKP : K ≤ P.G) {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) :
    pfdPrimalWeight P p q K * q ^ (P.G.edgeFinset.card + 1) =
      (p / (1 - dualParam p q)) ^ P.G.edgeFinset.card * q ^ Nat.card P.V *
        pfdDualWeight P (dualParam p q) q K := by
  let m := P.G.edgeFinset.card
  let o := K.edgeSet.ncard
  let k := Nat.card K.ConnectedComponent
  let kd := Nat.card (pfdClosedDual P K).ConnectedComponent
  let v := Nat.card P.V
  have hom : o ≤ m := pfd_subgraph_edgeCount_le P K hKP
  have hedge := dlt_edgeProduct_duality hp hp1 hq m o hom
  have heuler : v + kd = o + k + 1 := pfd_clusterEuler P K hKP
  have hpow : q ^ o * q ^ k * q = q ^ v * q ^ kd := by
    calc
      q ^ o * q ^ k * q = q ^ (o + k + 1) := by
        rw [← pow_add, ← pow_succ]
      _ = q ^ (v + kd) := congrArg (q ^ ·) heuler.symm
      _ = q ^ v * q ^ kd := pow_add q v kd
  unfold pfdPrimalWeight pfdDualWeight
  change edgeProductCount p m o * q ^ k * q ^ (m + 1) =
    (p / (1 - dualParam p q)) ^ m * q ^ v *
      (edgeProductCount (dualParam p q) m (m - o) * q ^ kd)
  calc
    edgeProductCount p m o * q ^ k * q ^ (m + 1) =
        (edgeProductCount p m o * q ^ m) * (q ^ k * q) := by
      rw [pow_succ]
      ring
    _ = ((p / (1 - dualParam p q)) ^ m * q ^ o *
          edgeProductCount (dualParam p q) m (m - o)) * (q ^ k * q) := by
      rw [hedge]
    _ = (p / (1 - dualParam p q)) ^ m *
          edgeProductCount (dualParam p q) m (m - o) * (q ^ o * q ^ k * q) := by
      ring
    _ = (p / (1 - dualParam p q)) ^ m * q ^ v *
          (edgeProductCount (dualParam p q) m (m - o) * q ^ kd) := by
      rw [hpow]
      ring




theorem pfd_openSub_edge_ncard {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (omega : ConfigSpace (Sym2 V)) :
    (FK.openSub G omega).edgeSet.ncard = FK.openCount G omega := by
  classical
  rw [Set.ncard_eq_toFinset_card']
  unfold FK.openCount
  congr 1
  ext e
  induction e using Sym2.inductionOn with
  | _ x y =>
      simp only [Set.mem_toFinset, SimpleGraph.mem_edgeSet, FK.openSub_adj,
        Finset.mem_filter, SimpleGraph.mem_edgeFinset]



theorem pfd_primalWeight_openSub (P : PlanarZ2Subgraph)
    (p q : ℝ) (omega : ConfigSpace (Sym2 P.V)) :
    pfdPrimalWeight P p q (FK.openSub P.G omega) = FK.fkWeight P.G p q omega := by
  unfold pfdPrimalWeight FK.fkWeight
  rw [pfd_openSub_edge_ncard]
  rw [dlt_edgeProduct_eq_count]
  unfold FK.numClusters
  rw [Nat.card_eq_fintype_card]



theorem pfd_fkWeight_duality (P : PlanarZ2Subgraph)
    (omega : ConfigSpace (Sym2 P.V)) {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) :
    FK.fkWeight P.G p q omega * q ^ (P.G.edgeFinset.card + 1) =
      (p / (1 - dualParam p q)) ^ P.G.edgeFinset.card * q ^ Nat.card P.V *
        pfdDualWeight P (dualParam p q) q (FK.openSub P.G omega) := by
  rw [← pfd_primalWeight_openSub P p q omega]
  exact pfd_weight_duality P (FK.openSub P.G omega) (FK.openSub_le P.G omega) hp hp1 hq





noncomputable def pfdDualZ (P : PlanarZ2Subgraph) (p q : ℝ) : ℝ :=
  ∑ omega : ConfigSpace (Sym2 P.V),
    pfdDualWeight P p q (FK.openSub P.G omega)



noncomputable def pfdDualProb (P : PlanarZ2Subgraph) (p q : ℝ)
    (omega : ConfigSpace (Sym2 P.V)) : ℝ :=
  pfdDualWeight P p q (FK.openSub P.G omega) / pfdDualZ P p q

theorem pfd_dualWeight_pos (P : PlanarZ2Subgraph) (K : SimpleGraph P.V)
    {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) :
    0 < pfdDualWeight P p q K := by
  unfold pfdDualWeight edgeProductCount
  have h1p : 0 < 1 - p := by linarith
  exact mul_pos (mul_pos (pow_pos hp _) (pow_pos h1p _)) (pow_pos hq _)

theorem pfd_dualZ_pos (P : PlanarZ2Subgraph) {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) :
    0 < pfdDualZ P p q := by
  unfold pfdDualZ
  exact Finset.sum_pos
    (fun omega _ => pfd_dualWeight_pos P (FK.openSub P.G omega) hp hp1 hq)
    Finset.univ_nonempty



theorem pfd_partition_duality (P : PlanarZ2Subgraph) {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) :
    FK.fkZ P.G p q * q ^ (P.G.edgeFinset.card + 1) =
      (p / (1 - dualParam p q)) ^ P.G.edgeFinset.card * q ^ Nat.card P.V *
        pfdDualZ P (dualParam p q) q := by
  unfold FK.fkZ pfdDualZ
  rw [Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro omega _
  exact pfd_fkWeight_duality P omega hp hp1 hq





theorem pfd_fkProb_duality (P : PlanarZ2Subgraph)
    (omega : ConfigSpace (Sym2 P.V)) {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) :
    FK.fkProb P.G p q omega = pfdDualProb P (dualParam p q) q omega := by
  have hps0 : 0 < dualParam p q := dualParam_pos hp hp1 hq
  have hps1 : dualParam p q < 1 := dualParam_lt_one hp hp1 hq
  have hZp : FK.fkZ P.G p q ≠ 0 := FK.fkZ_ne_zero P.G hp hp1 hq
  have hZd : pfdDualZ P (dualParam p q) q ≠ 0 :=
    (pfd_dualZ_pos P hps0 hps1 hq).ne'
  let A := q ^ (P.G.edgeFinset.card + 1)
  let B := (p / (1 - dualParam p q)) ^ P.G.edgeFinset.card * q ^ Nat.card P.V
  let wp := FK.fkWeight P.G p q omega
  let wd := pfdDualWeight P (dualParam p q) q (FK.openSub P.G omega)
  have hA : 0 < A := pow_pos hq _
  have hB : 0 < B := by
    have hden : 0 < 1 - dualParam p q := by linarith
    exact mul_pos (pow_pos (div_pos hp hden) _) (pow_pos hq _)
  have hw : wp * A = B * wd := pfd_fkWeight_duality P omega hp hp1 hq
  have hZ : FK.fkZ P.G p q * A = B * pfdDualZ P (dualParam p q) q :=
    pfd_partition_duality P hp hp1 hq
  have hcross : wp * pfdDualZ P (dualParam p q) q = wd * FK.fkZ P.G p q := by
    apply mul_left_cancel₀ hB.ne'
    calc
      B * (wp * pfdDualZ P (dualParam p q) q) =
          wp * (B * pfdDualZ P (dualParam p q) q) := by ring
      _ = wp * (FK.fkZ P.G p q * A) := by rw [hZ]
      _ = (wp * A) * FK.fkZ P.G p q := by ring
      _ = (B * wd) * FK.fkZ P.G p q := by rw [hw]
      _ = B * (wd * FK.fkZ P.G p q) := by ring
  unfold FK.fkProb pfdDualProb
  apply (div_eq_div_iff hZp hZd).2
  simpa only [wp, wd] using hcross

end BeffaraDC
end StatMech

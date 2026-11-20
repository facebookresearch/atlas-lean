/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/











import Code.BeffaraDC.Duality
import Code.BeffaraDC.TorusGeometricEuler

open SimpleGraph Set

namespace StatMech.BeffaraDC

open StatMech.Onsager



def torusDualConfig (L : ℕ)
    (ω : ConfigSpace (Sym2 (ZMod L × ZMod L))) :
    ConfigSpace (Sym2 (ZMod L × ZMod L)) :=
  fun e => !(ω (Sym2.map (torusQuarterTurn L) e))


def torusQuarterTurnEdge (L : ℕ) :
    Sym2 (ZMod L × ZMod L) ≃ Sym2 (ZMod L × ZMod L) where
  toFun := Sym2.map (torusQuarterTurn L)
  invFun := Sym2.map (torusQuarterTurn L).symm
  left_inv e := by
    calc
      _ = Sym2.map ((torusQuarterTurn L).symm ∘ torusQuarterTurn L) e := by
        exact (congrFun (Sym2.map_comp (g := (torusQuarterTurn L).symm)
          (f := torusQuarterTurn L)) e).symm
      _ = Sym2.map id e := by
        congr 2
        funext x
        exact (torusQuarterTurn L).symm_apply_apply x
      _ = e := congrFun Sym2.map_id e
  right_inv e := by
    calc
      _ = Sym2.map (torusQuarterTurn L ∘ (torusQuarterTurn L).symm) e := by
        exact (congrFun (Sym2.map_comp (g := torusQuarterTurn L)
          (f := (torusQuarterTurn L).symm)) e).symm
      _ = Sym2.map id e := by
        congr 2
        funext x
        exact (torusQuarterTurn L).apply_symm_apply x
      _ = e := congrFun Sym2.map_id e


theorem torusQuarterTurnEdge_mem_edgeFinset (L : ℕ) [Fact (2 < L)]
    (e : Sym2 (ZMod L × ZMod L)) :
    e ∈ (onsTorusGraph L).edgeFinset ↔
      torusQuarterTurnEdge L e ∈ (onsTorusGraph L).edgeFinset := by
  induction e using Sym2.inductionOn with
  | _ x y =>
      simp only [SimpleGraph.mem_edgeFinset, torusQuarterTurnEdge,
        Equiv.coe_fn_mk, Sym2.map_mk]
      exact (torusQuarterTurn_adj_iff L x y).symm



theorem torus_dual_openCount (L : ℕ) [Fact (2 < L)]
    (ω : ConfigSpace (Sym2 (ZMod L × ZMod L))) :
    FK.openCount (onsTorusGraph L) (torusDualConfig L ω) =
      (onsTorusGraph L).edgeFinset.card - FK.openCount (onsTorusGraph L) ω := by
  classical
  unfold FK.openCount
  have hopen : (onsTorusGraph L).edgeFinset.filter
      (fun e => torusDualConfig L ω e = true) =
      (onsTorusGraph L).edgeFinset.filter
        (fun e => ω (torusQuarterTurnEdge L e) = false) := by
    ext e
    simp only [Finset.mem_filter, torusDualConfig, torusQuarterTurnEdge,
      Equiv.coe_fn_mk]
    cases h : ω (Sym2.map (torusQuarterTurn L) e) <;> simp
  rw [hopen, show ((onsTorusGraph L).edgeFinset.filter
      (fun e => ω (torusQuarterTurnEdge L e) = false)).card =
      ((onsTorusGraph L).edgeFinset.filter (fun e => ω e = false)).card from by
    apply Finset.card_bij (fun e _ => torusQuarterTurnEdge L e)
    · intro e he
      simp only [Finset.mem_filter] at he ⊢
      exact ⟨(torusQuarterTurnEdge_mem_edgeFinset L e).mp he.1, he.2⟩
    · intro a ha b hb hab
      exact (torusQuarterTurnEdge L).injective hab
    · intro b hb
      refine ⟨(torusQuarterTurnEdge L).symm b, ?_,
        (torusQuarterTurnEdge L).apply_symm_apply b⟩
      simp only [Finset.mem_filter] at hb ⊢
      exact ⟨(torusQuarterTurnEdge_mem_edgeFinset L
        ((torusQuarterTurnEdge L).symm b)).mpr (by simpa using hb.1), by simpa using hb.2⟩]
  have hc := Finset.card_filter_add_card_filter_not
    (s := (onsTorusGraph L).edgeFinset) (fun e => ω e = true)
  have hnot : (onsTorusGraph L).edgeFinset.filter (fun e => ¬ω e = true) =
      (onsTorusGraph L).edgeFinset.filter (fun e => ω e = false) := by
    ext e
    simp only [Finset.mem_filter]
    cases ω e <;> simp
  rw [hnot] at hc
  omega


theorem torus_openSub_dualConfig (L : ℕ) [Fact (2 < L)]
    (ω : ConfigSpace (Sym2 (ZMod L × ZMod L))) :
    FK.openSub (onsTorusGraph L) (torusDualConfig L ω) =
      torusDualCutGraph L (FK.openSub (onsTorusGraph L) ω) := by
  ext f g
  simp only [FK.openSub_adj, torusDualCutGraph_adj, torusDualConfig, Sym2.map_mk]
  rw [torusQuarterTurn_adj_iff]
  by_cases h : (onsTorusGraph L).Adj f g <;> simp [h]


theorem torus_numClusters_dualConfig (L : ℕ) [Fact (2 < L)]
    (ω : ConfigSpace (Sym2 (ZMod L × ZMod L))) :
    FK.numClusters (onsTorusGraph L) (torusDualConfig L ω) =
      torusGeometricFaceCount L (FK.openSub (onsTorusGraph L) ω) := by
  unfold FK.numClusters torusGeometricFaceCount
  rw [← Nat.card_eq_fintype_card]
  exact congrArg (fun G : SimpleGraph (ZMod L × ZMod L) =>
    Nat.card G.ConnectedComponent) (torus_openSub_dualConfig L ω)



noncomputable def torusPrimalWeight (L : ℕ) [Fact (2 < L)] (p q : ℝ)
    (K : SimpleGraph (ZMod L × ZMod L)) : ℝ :=
  edgeProductCount p (onsTorusGraph L).edgeFinset.card K.edgeSet.ncard *
    q ^ Nat.card K.ConnectedComponent



noncomputable def torusDualWeight (L : ℕ) [Fact (2 < L)] (p q : ℝ)
    (K : SimpleGraph (ZMod L × ZMod L)) : ℝ :=
  edgeProductCount p (onsTorusGraph L).edgeFinset.card
      ((onsTorusGraph L).edgeFinset.card - K.edgeSet.ncard) *
    q ^ torusGeometricFaceCount L K


theorem torus_openSub_edge_ncard {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (ω : ConfigSpace (Sym2 V)) :
    (FK.openSub G ω).edgeSet.ncard = FK.openCount G ω := by
  classical
  rw [Set.ncard_eq_toFinset_card']
  unfold FK.openCount
  congr 1
  ext e
  induction e using Sym2.inductionOn with
  | _ x y =>
      simp only [Set.mem_toFinset, SimpleGraph.mem_edgeSet, FK.openSub_adj,
        Finset.mem_filter, SimpleGraph.mem_edgeFinset]


theorem torus_primalWeight_openSub (L : ℕ) [Fact (2 < L)] (p q : ℝ)
    (ω : ConfigSpace (Sym2 (ZMod L × ZMod L))) :
    torusPrimalWeight L p q (FK.openSub (onsTorusGraph L) ω) =
      FK.fkWeight (onsTorusGraph L) p q ω := by
  unfold torusPrimalWeight FK.fkWeight
  rw [torus_openSub_edge_ncard, dlt_edgeProduct_eq_count]
  unfold FK.numClusters
  rw [Nat.card_eq_fintype_card]



theorem torus_dualWeight_openSub (L : ℕ) [Fact (2 < L)] (p q : ℝ)
    (ω : ConfigSpace (Sym2 (ZMod L × ZMod L))) :
    torusDualWeight L p q (FK.openSub (onsTorusGraph L) ω) =
      FK.fkWeight (onsTorusGraph L) p q (torusDualConfig L ω) := by
  unfold torusDualWeight FK.fkWeight
  rw [torus_openSub_edge_ncard, ← torus_dual_openCount,
    ← dlt_edgeProduct_eq_count, torus_numClusters_dualConfig]

theorem torusPrimalWeight_pos (L : ℕ) [Fact (2 < L)]
    (K : SimpleGraph (ZMod L × ZMod L)) {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) :
    0 < torusPrimalWeight L p q K := by
  unfold torusPrimalWeight edgeProductCount
  have h1p : 0 < 1 - p := by linarith
  positivity

theorem torusDualWeight_pos (L : ℕ) [Fact (2 < L)]
    (K : SimpleGraph (ZMod L × ZMod L)) {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) :
    0 < torusDualWeight L p q K := by
  unfold torusDualWeight edgeProductCount
  have h1p : 0 < 1 - p := by linarith
  positivity



theorem torus_subgraph_edgeCount_le (L : ℕ) [Fact (2 < L)]
    (K : SimpleGraph (ZMod L × ZMod L)) (hK : K ≤ onsTorusGraph L) :
    K.edgeSet.ncard ≤ (onsTorusGraph L).edgeFinset.card := by
  have hset : K.edgeSet ⊆ (onsTorusGraph L).edgeSet := SimpleGraph.edgeSet_mono hK
  have hn := Set.ncard_le_ncard hset (Set.toFinite (onsTorusGraph L).edgeSet)
  simpa only [SimpleGraph.edgeFinset, Set.ncard_eq_toFinset_card'] using hn




theorem torus_clusterEuler_signed (L : ℕ) [Fact (2 < L)]
    (K : SimpleGraph (ZMod L × ZMod L)) :
    ((K.edgeSet.ncard + Nat.card K.ConnectedComponent + 1 : ℕ) : ℤ) =
      ((Nat.card (ZMod L × ZMod L) + torusGeometricFaceCount L K : ℕ) : ℤ) +
        torusGeometricDefect L K := by
  have h := geometric_euler_torus L K
  push_cast at h ⊢
  linarith






theorem torus_weight_duality_signed (L : ℕ) [Fact (2 < L)]
    (K : SimpleGraph (ZMod L × ZMod L)) (hK : K ≤ onsTorusGraph L)
    {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) :
    torusPrimalWeight L p q K * q ^ ((onsTorusGraph L).edgeFinset.card + 1) =
      (p / (1 - dualParam p q)) ^ (onsTorusGraph L).edgeFinset.card *
        q ^ Nat.card (ZMod L × ZMod L) *
        torusDualWeight L (dualParam p q) q K *
        q ^ torusGeometricDefect L K := by
  let m := (onsTorusGraph L).edgeFinset.card
  let o := K.edgeSet.ncard
  let k := Nat.card K.ConnectedComponent
  let f := torusGeometricFaceCount L K
  let v := Nat.card (ZMod L × ZMod L)
  let d := torusGeometricDefect L K
  have hom : o ≤ m := torus_subgraph_edgeCount_le L K hK
  have hedge := dlt_edgeProduct_duality hp hp1 hq m o hom
  have heuler : ((o + k + 1 : ℕ) : ℤ) = ((v + f : ℕ) : ℤ) + d := by
    simpa only [o, k, v, f, d] using torus_clusterEuler_signed L K
  have hqne : q ≠ 0 := ne_of_gt hq
  have hpow : q ^ (o + k + 1) = q ^ (v + f) * q ^ d := by
    rw [← zpow_natCast, ← zpow_natCast]
    rw [heuler, zpow_add₀ hqne]
  unfold torusPrimalWeight torusDualWeight
  change edgeProductCount p m o * q ^ k * q ^ (m + 1) =
    (p / (1 - dualParam p q)) ^ m * q ^ v *
      (edgeProductCount (dualParam p q) m (m - o) * q ^ f) * q ^ d
  calc
    edgeProductCount p m o * q ^ k * q ^ (m + 1) =
        (edgeProductCount p m o * q ^ m) * (q ^ k * q) := by
      rw [pow_succ]
      ring
    _ = ((p / (1 - dualParam p q)) ^ m * q ^ o *
          edgeProductCount (dualParam p q) m (m - o)) * (q ^ k * q) := by
      rw [hedge]
    _ = (p / (1 - dualParam p q)) ^ m *
          edgeProductCount (dualParam p q) m (m - o) * q ^ (o + k + 1) := by
      rw [pow_add, pow_succ]
      ring
    _ = (p / (1 - dualParam p q)) ^ m *
          edgeProductCount (dualParam p q) m (m - o) * (q ^ (v + f) * q ^ d) := by
      rw [hpow]
    _ = (p / (1 - dualParam p q)) ^ m * q ^ v *
          (edgeProductCount (dualParam p q) m (m - o) * q ^ f) * q ^ d := by
      rw [pow_add]
      ring



theorem torus_fkWeight_duality_signed (L : ℕ) [Fact (2 < L)]
    (ω : ConfigSpace (Sym2 (ZMod L × ZMod L)))
    {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) :
    FK.fkWeight (onsTorusGraph L) p q ω *
        q ^ ((onsTorusGraph L).edgeFinset.card + 1) =
      (p / (1 - dualParam p q)) ^ (onsTorusGraph L).edgeFinset.card *
        q ^ Nat.card (ZMod L × ZMod L) *
        FK.fkWeight (onsTorusGraph L) (dualParam p q) q
          (torusDualConfig L ω) *
        q ^ torusGeometricDefect L (FK.openSub (onsTorusGraph L) ω) := by
  rw [← torus_primalWeight_openSub L p q ω,
    ← torus_dualWeight_openSub L (dualParam p q) q ω]
  exact torus_weight_duality_signed L (FK.openSub (onsTorusGraph L) ω)
    (FK.openSub_le (onsTorusGraph L) ω) hp hp1 hq



theorem torus_weight_duality_of_defect (L : ℕ) [Fact (2 < L)]
    (K : SimpleGraph (ZMod L × ZMod L)) (hK : K ≤ onsTorusGraph L)
    {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) (δ : ℕ)
    (hδ : torusGeometricDefect L K = δ) :
    torusPrimalWeight L p q K * q ^ ((onsTorusGraph L).edgeFinset.card + 1) =
      (p / (1 - dualParam p q)) ^ (onsTorusGraph L).edgeFinset.card *
        q ^ Nat.card (ZMod L × ZMod L) *
        torusDualWeight L (dualParam p q) q K * q ^ δ := by
  rw [torus_weight_duality_signed L K hK hp hp1 hq, hδ, zpow_natCast]


def TorusDefectClassified (L : ℕ) [Fact (2 < L)] : Prop :=
  ∀ K : SimpleGraph (ZMod L × ZMod L), K ≤ onsTorusGraph L →
    torusGeometricDefect L K = 0 ∨ torusGeometricDefect L K = 1 ∨
      torusGeometricDefect L K = 2




theorem torus_weight_q_sandwich (L : ℕ) [Fact (2 < L)]
    (hclass : TorusDefectClassified L)
    (K : SimpleGraph (ZMod L × ZMod L)) (hK : K ≤ onsTorusGraph L)
    {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq1 : 1 ≤ q) :
    let primal := torusPrimalWeight L p q K *
      q ^ ((onsTorusGraph L).edgeFinset.card + 1)
    let dual := (p / (1 - dualParam p q)) ^ (onsTorusGraph L).edgeFinset.card *
      q ^ Nat.card (ZMod L × ZMod L) * q *
      torusDualWeight L (dualParam p q) q K
    primal ≤ q * dual ∧ dual ≤ q * primal := by
  have hq : 0 < q := lt_of_lt_of_le one_pos hq1
  have hps0 : 0 < dualParam p q := dualParam_pos hp hp1 hq
  have hps1 : dualParam p q < 1 := dualParam_lt_one hp hp1 hq
  have hP0 : 0 ≤ torusPrimalWeight L p q K *
      q ^ ((onsTorusGraph L).edgeFinset.card + 1) :=
    (mul_pos (torusPrimalWeight_pos L K hp hp1 hq) (pow_pos hq _)).le
  have hD0 : 0 ≤ (p / (1 - dualParam p q)) ^ (onsTorusGraph L).edgeFinset.card *
      q ^ Nat.card (ZMod L × ZMod L) * q *
      torusDualWeight L (dualParam p q) q K := by
    have hden : 0 < 1 - dualParam p q := by linarith
    exact (mul_pos
      (mul_pos (mul_pos (pow_pos (div_pos hp hden) _) (pow_pos hq _)) hq)
      (torusDualWeight_pos L K hps0 hps1 hq)).le
  dsimp only
  rcases hclass K hK with hδ | hδ | hδ
  · have heq := torus_weight_duality_of_defect L K hK hp hp1 hq 0 hδ
    simp only [pow_zero, mul_one] at heq
    have hrel : (p / (1 - dualParam p q)) ^ (onsTorusGraph L).edgeFinset.card *
        q ^ Nat.card (ZMod L × ZMod L) * q *
        torusDualWeight L (dualParam p q) q K =
        q * (torusPrimalWeight L p q K *
          q ^ ((onsTorusGraph L).edgeFinset.card + 1)) := by
      rw [heq]
      ring
    constructor
    · rw [hrel]
      nlinarith
    · rw [hrel]
  · have heq := torus_weight_duality_of_defect L K hK hp hp1 hq 1 hδ
    simp only [pow_one] at heq
    have heq' : torusPrimalWeight L p q K *
        q ^ ((onsTorusGraph L).edgeFinset.card + 1) =
        (p / (1 - dualParam p q)) ^ (onsTorusGraph L).edgeFinset.card *
          q ^ Nat.card (ZMod L × ZMod L) * q *
          torusDualWeight L (dualParam p q) q K := by
      calc
        _ = (p / (1 - dualParam p q)) ^ (onsTorusGraph L).edgeFinset.card *
            q ^ Nat.card (ZMod L × ZMod L) *
            torusDualWeight L (dualParam p q) q K * q := heq
        _ = _ := by ring
    constructor
    · rw [heq']
      nlinarith
    · rw [heq']
      nlinarith
  · have heq := torus_weight_duality_of_defect L K hK hp hp1 hq 2 hδ
    simp only [pow_two] at heq
    have heq' : torusPrimalWeight L p q K *
        q ^ ((onsTorusGraph L).edgeFinset.card + 1) =
        q * ((p / (1 - dualParam p q)) ^ (onsTorusGraph L).edgeFinset.card *
          q ^ Nat.card (ZMod L × ZMod L) * q *
          torusDualWeight L (dualParam p q) q K) := by
      calc
        _ = (p / (1 - dualParam p q)) ^ (onsTorusGraph L).edgeFinset.card *
            q ^ Nat.card (ZMod L × ZMod L) *
            torusDualWeight L (dualParam p q) q K * (q * q) := heq
        _ = _ := by ring
    constructor
    · rw [heq']
    · rw [heq']
      nlinarith





theorem torus_normalized_event_comparison (L : ℕ) [Fact (2 < L)]
    (hclass : TorusDefectClassified L) {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq1 : 1 ≤ q)
    (A : Finset (ConfigSpace (Sym2 (ZMod L × ZMod L)))) :
    let w := fun ω : ConfigSpace (Sym2 (ZMod L × ZMod L)) =>
      torusPrimalWeight L p q (FK.openSub (onsTorusGraph L) ω) *
        q ^ ((onsTorusGraph L).edgeFinset.card + 1)
    let w' := fun ω : ConfigSpace (Sym2 (ZMod L × ZMod L)) =>
      (p / (1 - dualParam p q)) ^ (onsTorusGraph L).edgeFinset.card *
        q ^ Nat.card (ZMod L × ZMod L) * q *
        torusDualWeight L (dualParam p q) q (FK.openSub (onsTorusGraph L) ω)
    (∑ ω ∈ A, w ω) / (∑ ω, w ω) ≤
      q ^ 2 * ((∑ ω ∈ A, w' ω) / (∑ ω, w' ω)) := by
  have hq : 0 < q := lt_of_lt_of_le one_pos hq1
  have hps0 : 0 < dualParam p q := dualParam_pos hp hp1 hq
  have hps1 : dualParam p q < 1 := dualParam_lt_one hp hp1 hq
  dsimp only
  apply dlt_rn_sandwich
      (fun ω : ConfigSpace (Sym2 (ZMod L × ZMod L)) =>
        torusPrimalWeight L p q (FK.openSub (onsTorusGraph L) ω) *
          q ^ ((onsTorusGraph L).edgeFinset.card + 1))
      (fun ω : ConfigSpace (Sym2 (ZMod L × ZMod L)) =>
        (p / (1 - dualParam p q)) ^ (onsTorusGraph L).edgeFinset.card *
          q ^ Nat.card (ZMod L × ZMod L) * q *
          torusDualWeight L (dualParam p q) q (FK.openSub (onsTorusGraph L) ω))
      q hq1 1
  · intro ω
    have hden : 0 < 1 - dualParam p q := by linarith
    exact mul_pos
      (mul_pos (mul_pos (pow_pos (div_pos hp hden) _) (pow_pos hq _)) hq)
      (torusDualWeight_pos L (FK.openSub (onsTorusGraph L) ω) hps0 hps1 hq)
  · intro ω
    exact mul_pos
      (torusPrimalWeight_pos L (FK.openSub (onsTorusGraph L) ω) hp hp1 hq)
      (pow_pos hq _)
  · intro ω
    have hs := torus_weight_q_sandwich L hclass
      (FK.openSub (onsTorusGraph L) ω) (FK.openSub_le (onsTorusGraph L) ω)
      hp hp1 hq1
    dsimp only at hs
    rw [zpow_neg, zpow_natCast, pow_one]
    exact (inv_mul_le_iff₀ hq).2 hs.2
  · intro ω
    have hs := torus_weight_q_sandwich L hclass
      (FK.openSub (onsTorusGraph L) ω) (FK.openSub_le (onsTorusGraph L) ω)
      hp hp1 hq1
    dsimp only at hs
    simpa using hs.1

end StatMech.BeffaraDC

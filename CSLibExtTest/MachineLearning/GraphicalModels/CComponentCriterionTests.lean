/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.MachineLearning.GraphicalModels.CComponentCriterion
public import CSLibExt.MachineLearning.GraphicalModels.LatentConfounding
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Tests for the single-intervention criterion

The bow graph `X → Y`, `X ↔ Y` violates the criterion's condition, and there the effect of `X`
on `Y` is not identified, even among networks with a strictly positive observed law in which no
latent node is a descendant of an observed node: two networks on the latent-confounding triangle
`U → X`, `U → Y`, `X → Y` (with `U` latent) have the same strictly positive law of `(X, Y)` but
give `P(Y = 1 | do(X = 1))` the values `5 / 8` and `1 / 2`.
-/

@[expose] public section

namespace Cslib.MachineLearning.GraphicalModels

namespace BayesNet

private theorem crit_aux_extendObs_obs {α : Type*} {n : ℕ} [Nonempty α] (L : Finset (Fin n))
    (v : {i : Fin n // i ∉ L} → α) (x : {i : Fin n // i ∉ L}) :
    extendObs L v (↑x) = v x := by
  unfold extendObs
  rw [dite_eq_right x.2]

end BayesNet

namespace LatentConfounding

open Finset

/-- The observed nodes `X = 1` and `Y = 2` of the latent-confounding triangle; `U = 0` is
latent. -/
abbrev Obs : Type := {i : Fin 3 // i ∉ ({0} : Finset (Fin 3))}

/-- The observed node `X = 1`. -/
def xNode : Obs := ⟨1, by decide⟩

/-- The observed node `Y = 2`. -/
def yNode : Obs := ⟨2, by decide⟩

/-- The bow graph on the observed nodes: the arrow `X → Y` and the bidirected edge `X ↔ Y`. -/
def bow : ADMG Obs where
  dir u w := u = xNode ∧ w = yNode
  bidir := ⊤
  acyclic v h := by
    obtain ⟨c, ⟨rfl, -⟩, -⟩ := Relation.TransGen.head'_iff.mp h
    obtain ⟨d, -, -, hv⟩ := Relation.TransGen.tail'_iff.mp h
    exact absurd hv (by decide)

/-- The bow graph violates the criterion's condition: the child `Y` of `X` lies in the
c-component of `X`. -/
theorem bow_not_noBidirPathToChild : ¬ bow.NoBidirPathToChild xNode := by
  intro h
  have hdir : bow.dir xNode yNode := ⟨rfl, rfl⟩
  have hmem : yNode ∈ bow.cComponent xNode := by
    rw [ADMG.mem_cComponent_iff]
    have hadj : bow.bidir.Adj xNode yNode := by
      show (⊤ : SimpleGraph Obs).Adj xNode yNode
      rw [SimpleGraph.top_adj]
      decide
    exact SimpleGraph.Adj.reachable hadj
  exact (h yNode hdir) hmem

private theorem crit_aux_obs_cases (u : Obs) : u = xNode ∨ u = yNode := by
  have htri : ∀ i : Fin 3, i = 0 ∨ i = 1 ∨ i = 2 := by
    intro i
    fin_cases i <;> simp
  have h3 := htri u.val
  have hne : u.val ≠ 0 := by
    intro h0
    have hmem : u.val ∈ ({0} : Finset (Fin 3)) := by simp [h0]
    exact u.2 hmem
  rcases h3 with h0 | h1 | h2
  · exact absurd h0 hne
  · left
    apply Subtype.ext
    simpa [xNode] using h1
  · right
    apply Subtype.ext
    simpa [yNode] using h2

private theorem crit_aux_edge01 (b : BayesNet Bool 3) (hb : OnConfoundedTriangle b) : b.Edge 0 1 := by
  unfold BayesNet.Edge
  rw [hb.2.1]
  exact ⟨by decide, Finset.mem_univ _⟩

private theorem crit_aux_edge02 (b : BayesNet Bool 3) (hb : OnConfoundedTriangle b) : b.Edge 0 2 := by
  unfold BayesNet.Edge
  rw [hb.2.2]
  exact ⟨by decide, Finset.mem_univ _⟩

private theorem crit_aux_edge12 (b : BayesNet Bool 3) (hb : OnConfoundedTriangle b) : b.Edge 1 2 := by
  unfold BayesNet.Edge
  rw [hb.2.2]
  exact ⟨by decide, Finset.mem_univ _⟩

private theorem crit_aux_edge_lt (b : BayesNet Bool 3) {i j : Fin 3} (h : b.Edge i j) : i < j := by
  obtain ⟨hlt, _⟩ := h
  exact hlt

private theorem crit_aux_reflTransGen_le (b : BayesNet Bool 3) (L : Finset (Fin 3)) {a c : Fin 3}
    (h : Relation.ReflTransGen (fun x y => b.Edge x y ∧ y ∈ L) a c) : a ≤ c := by
  induction h with
  | refl => exact le_refl _
  | tail _ h2 ih =>
    obtain ⟨hedge, _⟩ := h2
    have hlt := crit_aux_edge_lt b hedge
    exact le_trans ih (le_of_lt hlt)

private theorem crit_aux_latentPath_lt (b : BayesNet Bool 3) (L : Finset (Fin 3)) {u w : Fin 3}
    (h : b.LatentPath L u w) : u < w := by
  obtain ⟨m, hseg, hedge⟩ := h
  have hle : u ≤ m := crit_aux_reflTransGen_le b L hseg
  have hlt := crit_aux_edge_lt b hedge
  exact lt_of_le_of_lt hle hlt

private theorem crit_aux_latentPath_of_edge (b : BayesNet Bool 3) (L : Finset (Fin 3)) (l j : Fin 3)
    (h : b.Edge l j) : b.LatentPath L l j :=
  ⟨l, Relation.ReflTransGen.refl, h⟩

/-- The latent projection of a network on the latent-confounding triangle, with `U` latent, is
the bow graph. -/
theorem latentProjection_eq_bow {b : BayesNet Bool 3} (hb : OnConfoundedTriangle b) :
    b.latentProjection {0} = bow := by
  unfold BayesNet.latentProjection bow
  congr 1
  · funext u w
    apply propext
    constructor
    · intro hlat
      rcases crit_aux_obs_cases u with rfl | rfl
      · rcases crit_aux_obs_cases w with rfl | rfl
        · exfalso
          have hlt := crit_aux_latentPath_lt b {0} hlat
          exact absurd hlt (by decide)
        · exact ⟨rfl, rfl⟩
      · rcases crit_aux_obs_cases w with rfl | rfl
        · exfalso
          have hlt := crit_aux_latentPath_lt b {0} hlat
          exact absurd hlt (by decide)
        · exfalso
          have hlt := crit_aux_latentPath_lt b {0} hlat
          exact absurd hlt (by decide)
    · rintro ⟨rfl, rfl⟩
      exact crit_aux_latentPath_of_edge b {0} _ _ (crit_aux_edge12 b hb)
  · apply SimpleGraph.ext
    funext u w
    apply propext
    rw [SimpleGraph.top_adj]
    constructor
    · rintro ⟨hne, _⟩
      exact hne
    · intro hne
      refine ⟨hne, 0, by simp, ?_, ?_⟩
      · rcases crit_aux_obs_cases u with rfl | rfl
        · exact crit_aux_latentPath_of_edge b {0} _ _ (crit_aux_edge01 b hb)
        · exact crit_aux_latentPath_of_edge b {0} _ _ (crit_aux_edge02 b hb)
      · rcases crit_aux_obs_cases w with rfl | rfl
        · exact crit_aux_latentPath_of_edge b {0} _ _ (crit_aux_edge01 b hb)
        · exact crit_aux_latentPath_of_edge b {0} _ _ (crit_aux_edge02 b hb)

/-- With node `0` latent, no latent node is a descendant of an observed node: the nodes are
listed in a topological order, so every network on three nodes meets the semi-Markovian
convention. -/
theorem noObservedAncestorOfLatent_zero (b : BayesNet Bool 3) :
    b.NoObservedAncestorOfLatent {0} := by
  intro u hu w hw hdesc
  simp only [Finset.mem_singleton] at hu
  subst hu
  unfold BayesNet.IsDescendant at hdesc
  obtain rfl | ⟨p, -, hp0⟩ := Relation.ReflTransGen.cases_tail hdesc
  · simp at hw
  · have hlt : p < (0 : Fin 3) := BayesNet.edge_lt b hp0
    have hall : ∀ q : Fin 3, ¬ q < 0 := by decide
    exact absurd hlt (hall p)

/-- With `U` latent, the observed law `BayesNet.observedLaw` is the law `observedLaw` of
`(X, Y)`. -/
theorem observedLaw_eq (b : BayesNet Bool 3) (v : Obs → Bool) :
    b.observedLaw {0} v = observedLaw b (v xNode) (v yNode) := by
  have e1 : extendObs ({0} : Finset (Fin 3)) v ↑xNode = v xNode :=
    BayesNet.crit_aux_extendObs_obs {0} v xNode
  have e1' : extendObs ({0} : Finset (Fin 3)) v 1 = v xNode := e1
  have e2 : extendObs ({0} : Finset (Fin 3)) v ↑yNode = v yNode :=
    BayesNet.crit_aux_extendObs_obs {0} v yNode
  have e2' : extendObs ({0} : Finset (Fin 3)) v 2 = v yNode := e2
  have hval : ∀ k : Fin 3, k = 0 ∨ k = 1 ∨ k = 2 := by
    intro k
    by_cases h0 : k.val = 0
    · exact Or.inl (Fin.ext h0)
    · by_cases h1 : k.val = 1
      · exact Or.inr (Or.inl (Fin.ext h1))
      · by_cases h2 : k.val = 2
        · exact Or.inr (Or.inr (Fin.ext h2))
        · have h3 := k.isLt
          have h10 : 1 ≤ k.val := Nat.pos_of_ne_zero h0
          have h21 : 2 ≤ k.val := by
            rcases lt_or_gt_of_ne h1 with h | h
            · exact absurd (lt_of_lt_of_le h h10) (lt_irrefl _)
            · exact h
          have h32 : 3 ≤ k.val := by
            rcases lt_or_gt_of_ne h2 with h | h
            · exact absurd (lt_of_lt_of_le h h21) (lt_irrefl _)
            · exact h
          exact absurd h3 (not_lt.mpr h32)
  have hfw : ∀ y : Fin 3 → Bool,
      (∀ w ∈ (↑(({0} : Finset (Fin 3))ᶜ) : Set (Fin 3)), y w = extendObs {0} v w) →
      ![y 0, v xNode, v yNode] = y := by
    intro y hy
    have h1 : (1 : Fin 3) ∈ (↑(({0} : Finset (Fin 3))ᶜ) : Set (Fin 3)) := by
      rw [Finset.mem_coe, Finset.mem_compl]
      decide
    have h2 : (2 : Fin 3) ∈ (↑(({0} : Finset (Fin 3))ᶜ) : Set (Fin 3)) := by
      rw [Finset.mem_coe, Finset.mem_compl]
      decide
    have hy1 : y 1 = v xNode := by rw [hy 1 h1, e1']
    have hy2 : y 2 = v yNode := by rw [hy 2 h2, e2']
    funext i
    rcases hval i with rfl | rfl | rfl
    · simp
    · simp [hy1]
    · simp [Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, hy2]
  have hrev : ∀ u : Bool, ∀ w ∈ (↑(({0} : Finset (Fin 3))ᶜ) : Set (Fin 3)),
      (![u, v xNode, v yNode] : Fin 3 → Bool) w = extendObs {0} v w := by
    intro u w hw
    rw [Finset.mem_coe, Finset.mem_compl, Finset.mem_singleton] at hw
    have hw' : w = 1 ∨ w = 2 := by
      rcases hval w with rfl | h | h
      · simp at hw
      · exact Or.inl h
      · exact Or.inr h
    rcases hw' with rfl | rfl
    · rw [e1']
      simp
    · rw [e2']
      simp [Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  unfold BayesNet.observedLaw LatentConfounding.observedLaw
    MetaMathlibExt.FiniteWeight.marginal
  refine Finset.sum_nbij' (fun y : Fin 3 → Bool => y 0)
    (fun u : Bool => ![u, v xNode, v yNode]) ?_ ?_ ?_ ?_ ?_
  · intro y _
    exact Finset.mem_univ _
  · intro u _
    simp only [Finset.mem_filter]
    exact ⟨Finset.mem_univ _, hrev u⟩
  · intro y hy
    simp only [Finset.mem_filter] at hy
    exact hfw y hy.2
  · intro u _
    simp
  · intro y hy
    simp only [Finset.mem_filter] at hy
    exact congrArg b.joint (hfw y hy.2).symm

private theorem crit_aux_obs_two_eq (u : Obs) : u = xNode ∨ u = yNode := by
  have hlt : u.val.val < 3 := u.val.isLt
  have hne : u.val ≠ 0 := by
    rintro hcon
    have hu2 := u.2
    simp [hcon] at hu2
  have hval : u.val.val ≠ 0 := fun hcon => hne (Fin.ext (b := (0 : Fin 3)) hcon)
  have h12 : u.val.val = 1 ∨ u.val.val = 2 := by omega
  have hx1 : ((xNode : Obs) : Fin 3) = 1 := rfl
  have hy2 : ((yNode : Obs) : Fin 3) = 2 := rfl
  rcases h12 with h1 | h2
  · exact Or.inl (Subtype.ext (by rw [hx1]; exact Fin.ext (b := (1 : Fin 3)) h1))
  · exact Or.inr (Subtype.ext (by rw [hy2]; exact Fin.ext (b := (2 : Fin 3)) h2))

private theorem crit_aux_erase_xNode : (univ.erase xNode : Finset Obs) = {yNode} := by
  ext u
  simp only [Finset.mem_erase, Finset.mem_univ, and_true, Finset.mem_singleton]
  constructor
  · intro hne
    rcases crit_aux_obs_two_eq u with rfl | rfl
    · exact absurd rfl hne
    · rfl
  · rintro rfl
    decide

private theorem crit_aux_erase_map_xNode :
    (univ.erase xNode).map (Function.Embedding.subtype (· ∉ ({0} : Finset (Fin 3)))) =
      {(2 : Fin 3)} := by
  rw [crit_aux_erase_xNode, Finset.map_singleton]
  rfl

private theorem crit_aux_extendObs_two (v : Obs → Bool) :
    extendObs ({0} : Finset (Fin 3)) v 2 = v yNode := by
  have h := BayesNet.crit_aux_extendObs_obs ({0} : Finset (Fin 3)) v yNode
  have hy2 : ((yNode : Obs) : Fin 3) = 2 := rfl
  rw [hy2] at h
  exact h

private theorem crit_aux_mk3_eq (v : Obs → Bool) (y : Fin 3 → Bool)
    (hy : ∀ v_1 ∈ (↑({(2 : Fin 3)} : Finset (Fin 3)) : Set (Fin 3)),
      y v_1 = extendObs ({0} : Finset (Fin 3)) v v_1) :
    ((![y 0, y 1, v yNode] : Fin 3 → Bool) = y) := by
  have hy2 : y 2 = v yNode := by
    have h2mem : (2 : Fin 3) ∈ (↑({(2 : Fin 3)} : Finset (Fin 3)) : Set (Fin 3)) := by
      simp
    have h2 := hy 2 h2mem
    rw [crit_aux_extendObs_two v] at h2
    exact h2
  funext i
  have hi : i = 0 ∨ i = 1 ∨ i = 2 := by fin_cases i <;> simp
  rcases hi with rfl | rfl | rfl
  · simp [Matrix.cons_val_zero]
  · simp [Matrix.cons_val_one, Matrix.cons_val_zero]
  · simp [Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons, hy2]

private theorem crit_aux_marginal_intervene_eq (b : BayesNet Bool 3) (v : Obs → Bool) :
    MetaMathlibExt.FiniteWeight.marginal (b.intervene ↑xNode (v xNode)).joint
        ↑((univ.erase xNode).map (Function.Embedding.subtype (· ∉ ({0} : Finset (Fin 3)))))
        (extendObs {0} v)
      = ∑ u : Bool, ∑ x' : Bool, (b.intervene (1 : Fin 3) (v xNode)).joint ![u, x', v yNode] := by
  rw [crit_aux_erase_map_xNode]
  unfold MetaMathlibExt.FiniteWeight.marginal
  have hx1 : ((xNode : Obs) : Fin 3) = 1 := rfl
  refine (Finset.sum_bij' (t := (Finset.univ : Finset (Bool × Bool)))
    (g := fun p : Bool × Bool => (b.intervene ↑xNode (v xNode)).joint ![p.1, p.2, v yNode])
    (fun (y : Fin 3 → Bool) _ => (y 0, y 1))
    (fun (p : Bool × Bool) _ => ((![p.1, p.2, v yNode] : Fin 3 → Bool)))
    (fun y _ => Finset.mem_univ _) ?_ ?_ ?_ ?_).trans ?_
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    intro v_1 hv
    simp only [Finset.mem_coe, Finset.mem_singleton] at hv
    subst hv
    show ((![p.1, p.2, v yNode] : Fin 3 → Bool) 2 = extendObs ({0} : Finset (Fin 3)) v 2)
    rw [crit_aux_extendObs_two v]
    simp [Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]
  · intro y hy
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy
    show ((![y 0, y 1, v yNode] : Fin 3 → Bool) = y)
    exact crit_aux_mk3_eq v y hy
  · intro p hp
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Prod.mk.eta]
  · intro y hy
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy
    exact congrArg _ (crit_aux_mk3_eq v y hy).symm
  · rw [Fintype.sum_prod_type]
    simp only [hx1]

/-- With `U` latent, the Q-factor of `{Y}`, the effect of `X` on `Y`, is the interventional
probability `doProb`. -/
theorem qFactor_erase_eq_doProb (b : BayesNet Bool 3) (v : Obs → Bool) :
    b.qFactor {0} (univ.erase xNode) v = doProb b (v xNode) (v yNode) := by
  have hN4 : b.qFactor {0} (univ.erase xNode) v =
      MetaMathlibExt.FiniteWeight.marginal (b.intervene ↑xNode (v xNode)).joint
        ↑((univ.erase xNode).map (Function.Embedding.subtype (· ∉ ({0} : Finset (Fin 3)))))
        (extendObs {0} v) :=
    BayesNet.qFactor_erase_eq_marginal_intervene b {0} xNode v
  exact hN4.trans (crit_aux_marginal_intervene_eq b v)

private noncomputable def crit_aux_bern (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    Convexity.StdSimplex ℝ Bool where
  weights := Finsupp.equivFunOnFinite.symm (fun b => if b then p else 1 - p)
  nonneg := by
    intro b
    simp only [Finsupp.coe_zero, Pi.zero_apply]
    cases b <;> simp_all
  total := by
    rw [Finsupp.sum_fintype _ _ fun _ => rfl]
    simp

private theorem crit_aux_bern_true (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (crit_aux_bern p hp0 hp1).weights true = p := by
  simp [crit_aux_bern]

private theorem crit_aux_bern_false (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (crit_aux_bern p hp0 hp1).weights false = 1 - p := by
  simp [crit_aux_bern]

private theorem crit_aux_fair_weights (b : Bool) : fairCoin.weights b = 1 / 2 := by
  simp [fairCoin]

private theorem crit_aux_sum_bool (f : Bool → ℝ) : ∑ u : Bool, f u = f false + f true := by
  have h : (Finset.univ : Finset Bool) = {false, true} := by decide
  rw [h, Finset.sum_insert (by decide), Finset.sum_singleton]

private noncomputable def crit_aux_c1 : BayesNet Bool 3 where
  pa := fun _ => Finset.univ
  cpt := fun k z =>
    match k with
    | ⟨0, _⟩ => fairCoin
    | ⟨1, _⟩ => fairCoin
    | ⟨2, _⟩ =>
      if z ⟨1, Finset.mem_univ 1⟩ then crit_aux_bern (5 / 8) (by norm_num) (by norm_num)
      else crit_aux_bern (3 / 8) (by norm_num) (by norm_num)
    | ⟨n + 3, h⟩ => False.elim (by omega)

private noncomputable def crit_aux_c2 : BayesNet Bool 3 where
  pa := fun _ => Finset.univ
  cpt := fun k z =>
    match k with
    | ⟨0, _⟩ => fairCoin
    | ⟨1, _⟩ =>
      if z ⟨0, Finset.mem_univ 0⟩ then crit_aux_bern (5 / 8) (by norm_num) (by norm_num)
      else crit_aux_bern (3 / 8) (by norm_num) (by norm_num)
    | ⟨2, _⟩ =>
      if z ⟨0, Finset.mem_univ 0⟩ then crit_aux_bern 1 (by norm_num) (by norm_num)
      else crit_aux_bern 0 (by norm_num) (by norm_num)
    | ⟨n + 3, h⟩ => False.elim (by omega)

private theorem crit_aux_c1_tri : OnConfoundedTriangle crit_aux_c1 := by
  unfold OnConfoundedTriangle
  refine ⟨?_, rfl, rfl⟩
  show Finset.univ = ∅
  decide

private theorem crit_aux_c2_tri : OnConfoundedTriangle crit_aux_c2 := by
  unfold OnConfoundedTriangle
  refine ⟨?_, rfl, rfl⟩
  show Finset.univ = ∅
  decide

private theorem crit_aux_c1_cpt0 (z : crit_aux_c1.pa 0 → Bool) :
    crit_aux_c1.cpt 0 z = fairCoin :=
  rfl

private theorem crit_aux_c1_cpt1 (z : crit_aux_c1.pa 1 → Bool) :
    crit_aux_c1.cpt 1 z = fairCoin :=
  rfl

private theorem crit_aux_c1_cpt2 (z : crit_aux_c1.pa 2 → Bool) :
    crit_aux_c1.cpt 2 z =
      (if z ⟨⟨1, by decide⟩, Finset.mem_univ _⟩ then
        crit_aux_bern (5 / 8) (by norm_num) (by norm_num)
      else crit_aux_bern (3 / 8) (by norm_num) (by norm_num)) :=
  rfl

private theorem crit_aux_c2_cpt0 (z : crit_aux_c2.pa 0 → Bool) :
    crit_aux_c2.cpt 0 z = fairCoin :=
  rfl

private theorem crit_aux_c2_cpt1 (z : crit_aux_c2.pa 1 → Bool) :
    crit_aux_c2.cpt 1 z =
      (if z ⟨⟨0, by decide⟩, Finset.mem_univ _⟩ then
        crit_aux_bern (5 / 8) (by norm_num) (by norm_num)
      else crit_aux_bern (3 / 8) (by norm_num) (by norm_num)) :=
  rfl

private theorem crit_aux_c2_cpt2 (z : crit_aux_c2.pa 2 → Bool) :
    crit_aux_c2.cpt 2 z =
      (if z ⟨⟨0, by decide⟩, Finset.mem_univ _⟩ then
        crit_aux_bern 1 (by norm_num) (by norm_num)
      else crit_aux_bern 0 (by norm_num) (by norm_num)) :=
  rfl

private theorem crit_aux_c1_par2 (u x y : Bool) :
    ![u, x, y] (Fin.castLE (2 : Fin 3).2.le
      ↑(⟨⟨1, by decide⟩, Finset.mem_univ _⟩ : crit_aux_c1.pa 2)) = x :=
  rfl

private theorem crit_aux_c2_par1 (u x y : Bool) :
    ![u, x, y] (Fin.castLE (1 : Fin 3).2.le
      ↑(⟨⟨0, by decide⟩, Finset.mem_univ _⟩ : crit_aux_c2.pa 1)) = u :=
  rfl

private theorem crit_aux_c2_par2 (u x y : Bool) :
    ![u, x, y] (Fin.castLE (2 : Fin 3).2.le
      ↑(⟨⟨0, by decide⟩, Finset.mem_univ _⟩ : crit_aux_c2.pa 2)) = u :=
  rfl

private theorem crit_aux_idx0 (u x y : Bool) : ![u, x, y] 0 = u :=
  rfl

private theorem crit_aux_idx1 (u x y : Bool) : ![u, x, y] 1 = x :=
  rfl

private theorem crit_aux_idx2 (u x y : Bool) : ![u, x, y] 2 = y :=
  rfl

private theorem crit_aux_erase1 : Finset.univ.erase (1 : Fin 3) = {0, 2} := by
  decide

private theorem crit_aux_c1_joint (u x y : Bool) :
    crit_aux_c1.joint ![u, x, y] =
      (1 / 2) * (1 / 2) *
        (if x then (if y then (5 / 8 : ℝ) else 3 / 8)
        else (if y then 3 / 8 else 5 / 8)) := by
  rw [BayesNet.joint_eq_prod, Fin.prod_univ_three, crit_aux_c1_cpt0, crit_aux_c1_cpt1,
    crit_aux_c1_cpt2, crit_aux_c1_par2, crit_aux_idx0, crit_aux_idx1, crit_aux_idx2]
  cases u <;> cases x <;> cases y <;>
    norm_num [crit_aux_fair_weights, crit_aux_bern_true, crit_aux_bern_false]

private theorem crit_aux_c2_joint (u x y : Bool) :
    crit_aux_c2.joint ![u, x, y] =
      (1 / 2) * (if u then (if x then (5 / 8 : ℝ) else 3 / 8) else (if x then 3 / 8 else 5 / 8)) *
        (if u then (if y then (1 : ℝ) else 0) else (if y then 0 else 1)) := by
  rw [BayesNet.joint_eq_prod, Fin.prod_univ_three, crit_aux_c2_cpt0, crit_aux_c2_cpt1,
    crit_aux_c2_cpt2, crit_aux_c2_par1, crit_aux_c2_par2, crit_aux_idx0, crit_aux_idx1,
    crit_aux_idx2]
  cases u <;> cases x <;> cases y <;>
    norm_num [crit_aux_fair_weights, crit_aux_bern_true, crit_aux_bern_false]

private theorem crit_aux_c1_obs (x y : Bool) :
    observedLaw crit_aux_c1 x y =
      (if x then (if y then (5 / 16 : ℝ) else 3 / 16)
      else (if y then 3 / 16 else 5 / 16)) := by
  simp only [observedLaw, crit_aux_sum_bool, crit_aux_c1_joint]
  cases x <;> cases y <;> norm_num

private theorem crit_aux_c2_obs (x y : Bool) :
    observedLaw crit_aux_c2 x y =
      (if x then (if y then (5 / 16 : ℝ) else 3 / 16)
      else (if y then 3 / 16 else 5 / 16)) := by
  simp only [observedLaw, crit_aux_sum_bool, crit_aux_c2_joint]
  cases x <;> cases y <;> norm_num

private theorem crit_aux_c1_int (u x' y x₀ : Bool) :
    (crit_aux_c1.intervene 1 x₀).joint ![u, x', y] =
      (if x' = x₀ then (1 / 2) *
        (if x' then (if y then (5 / 8 : ℝ) else 3 / 8) else (if y then 3 / 8 else 5 / 8))
      else 0) := by
  rw [BayesNet.joint_intervene, crit_aux_idx1, crit_aux_erase1,
    Finset.prod_insert (by decide), Finset.prod_singleton]
  simp only [BayesNet.paVal, crit_aux_c1_cpt0, crit_aux_c1_cpt2, crit_aux_idx0,
    crit_aux_idx2]
  cases u <;> cases x' <;> cases y <;> cases x₀ <;>
    norm_num [crit_aux_fair_weights, crit_aux_bern_true, crit_aux_bern_false]

private theorem crit_aux_c2_int (u x' y x₀ : Bool) :
    (crit_aux_c2.intervene 1 x₀).joint ![u, x', y] =
      (if x' = x₀ then (1 / 2) *
        (if u then (if y then (1 : ℝ) else 0) else (if y then 0 else 1))
      else 0) := by
  rw [BayesNet.joint_intervene, crit_aux_idx1, crit_aux_erase1,
    Finset.prod_insert (by decide), Finset.prod_singleton]
  simp only [BayesNet.paVal, crit_aux_c2_cpt0, crit_aux_c2_cpt2, crit_aux_idx0,
    crit_aux_idx2]
  cases u <;> cases x' <;> cases y <;> cases x₀ <;>
    norm_num [crit_aux_fair_weights, crit_aux_bern_true, crit_aux_bern_false]

private theorem crit_aux_c1_do : doProb crit_aux_c1 true true = 5 / 8 := by
  simp only [doProb, crit_aux_sum_bool, crit_aux_c1_int]
  norm_num

private theorem crit_aux_c2_do : doProb crit_aux_c2 true true = 1 / 2 := by
  simp only [doProb, crit_aux_sum_bool, crit_aux_c2_int]
  norm_num

/-- Two networks on the latent-confounding triangle with the same strictly positive law of
`(X, Y)` and different interventional probabilities `P(Y = 1 | do(X = 1))`, `5 / 8` and
`1 / 2`. For example, `X` a fair coin with `P(Y = 1 | X = 1) = 5 / 8` and
`P(Y = 1 | X = 0) = 3 / 8`, against a fair `U` with `Y` equal to `U` deterministically and
`X` equal to `U` with probability `5 / 8`: both laws are `(5, 3, 3, 5) / 16` on `(false, false)`, `(false, true)`,
`(true, false)`, `(true, true)`. The witnesses of `exists_same_observedLaw_ne_doProb` put no
mass on `X ≠ Y`, so they do not have a strictly positive law. -/
theorem exists_pos_same_observedLaw_ne_doProb :
    ∃ c₁ c₂ : BayesNet Bool 3, OnConfoundedTriangle c₁ ∧ OnConfoundedTriangle c₂ ∧
      (∀ x y, 0 < observedLaw c₁ x y) ∧ (∀ x y, observedLaw c₁ x y = observedLaw c₂ x y) ∧
      doProb c₁ true true = 5 / 8 ∧ doProb c₂ true true = 1 / 2 := by
  refine ⟨crit_aux_c1, crit_aux_c2, crit_aux_c1_tri, crit_aux_c2_tri, ?_, ?_, crit_aux_c1_do,
    crit_aux_c2_do⟩
  · intro x y
    rw [crit_aux_c1_obs]
    cases x <;> cases y <;> norm_num
  · intro x y
    rw [crit_aux_c1_obs, crit_aux_c2_obs]

/-- **Bow-graph non-identification**: on the bow graph the effect of `X` on `Y` is not
identified from the observed law, even among networks with a strictly positive observed law in
which no latent node is a descendant of an observed node. -/
theorem not_identifiedOn_bow :
    ¬ IdentifiedOn (BayesNet.tianClass (α := Bool) ({0} : Finset (Fin 3)) bow)
      (fun b : BayesNet Bool 3 => b.observedLaw {0})
      (fun b => b.qFactor {0} (univ.erase xNode)) := by
  intro hIdent
  obtain ⟨c₁, c₂, hTri1, hTri2, hpos1, hObsEq, hDo1, hDo2⟩ := exists_pos_same_observedLaw_ne_doProb
  have hpos1' : ∀ v, 0 < c₁.observedLaw {0} v := fun v => by
    rw [observedLaw_eq]
    exact hpos1 _ _
  have hpos2' : ∀ v, 0 < c₂.observedLaw {0} v := fun v => by
    rw [observedLaw_eq]
    rw [← hObsEq]
    exact hpos1 _ _
  have hmem1 : c₁ ∈ BayesNet.tianClass (α := Bool) ({0} : Finset (Fin 3)) bow :=
    ⟨noObservedAncestorOfLatent_zero c₁, latentProjection_eq_bow hTri1, hpos1'⟩
  have hmem2 : c₂ ∈ BayesNet.tianClass (α := Bool) ({0} : Finset (Fin 3)) bow :=
    ⟨noObservedAncestorOfLatent_zero c₂, latentProjection_eq_bow hTri2, hpos2'⟩
  have hSame : c₁.observedLaw {0} = c₂.observedLaw {0} := by
    funext v
    rw [observedLaw_eq, observedLaw_eq, hObsEq]
  have hQeq := hIdent c₁ hmem1 c₂ hmem2 hSame
  have hQv := congrFun hQeq (fun _ : Obs => true)
  dsimp only at hQv
  rw [qFactor_erase_eq_doProb, qFactor_erase_eq_doProb] at hQv
  rw [hDo1, hDo2] at hQv
  norm_num at hQv

end LatentConfounding

end Cslib.MachineLearning.GraphicalModels

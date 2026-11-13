/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/







































import Mathlib
import Code.FK.Potts
import Code.FK.RandomCluster

open scoped BigOperators

namespace StatMech

namespace FK

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]






def esEdgeFactor {q : ℕ} (p : ℝ) (σ : V → Fin q) (ω : ConfigSpace (Sym2 V)) (e : Sym2 V) : ℝ :=
  if ω e then p * Potts.monoIndicator σ e else 1 - p



def esWeight {q : ℕ} (p : ℝ) (σ : V → Fin q) (ω : ConfigSpace (Sym2 V)) : ℝ :=
  ∏ e ∈ G.edgeFinset, esEdgeFactor p σ ω e

omit [DecidableEq V] in


theorem esWeight_nonneg {q : ℕ} {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (σ : V → Fin q) (ω : ConfigSpace (Sym2 V)) : 0 ≤ esWeight G p σ ω := by
  unfold esWeight esEdgeFactor
  apply Finset.prod_nonneg
  intro e _
  split
  · exact mul_nonneg hp (Potts.monoIndicator_nonneg σ e)
  · linarith






def ConstOnOpen {q : ℕ} (ω : ConfigSpace (Sym2 V)) (σ : V → Fin q) : Prop :=
  ∀ x y, (openSub G ω).Adj x y → σ x = σ y

instance instDecidableConstOnOpen {q : ℕ} (ω : ConfigSpace (Sym2 V)) (σ : V → Fin q) :
    Decidable (ConstOnOpen G ω σ) := by
  unfold ConstOnOpen
  infer_instance

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in


theorem constOnOpen_reachable {q : ℕ} (ω : ConfigSpace (Sym2 V)) (σ : V → Fin q)
    (h : ConstOnOpen G ω σ) {x y : V} (r : (openSub G ω).Reachable x y) : σ x = σ y := by
  rw [SimpleGraph.reachable_iff_reflTransGen] at r
  induction r with
  | refl => rfl
  | tail _ hab ih => rw [ih]; exact h _ _ hab

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in


theorem esEdgeFactor_eq {q : ℕ} (p : ℝ) (σ : V → Fin q) (ω : ConfigSpace (Sym2 V)) (e : Sym2 V) :
    esEdgeFactor p σ ω e =
      (if ω e then p else 1 - p) * (if ω e then Potts.monoIndicator σ e else 1) := by
  unfold esEdgeFactor
  split
  · ring
  · ring

omit [DecidableEq V] in


theorem esWeight_factor {q : ℕ} (p : ℝ) (σ : V → Fin q) (ω : ConfigSpace (Sym2 V)) :
    esWeight G p σ ω = edgeProduct G p ω *
      ∏ e ∈ G.edgeFinset, (if ω e then Potts.monoIndicator σ e else 1) := by
  unfold esWeight edgeProduct
  rw [← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun e _ => esEdgeFactor_eq p σ ω e

omit [DecidableEq V] in


theorem monoProd_eq_indicator {q : ℕ} (σ : V → Fin q) (ω : ConfigSpace (Sym2 V)) :
    (∏ e ∈ G.edgeFinset, (if ω e then Potts.monoIndicator σ e else 1)) =
      if ConstOnOpen G ω σ then 1 else 0 := by
  by_cases h : ConstOnOpen G ω σ
  · rw [if_pos h]
    apply Finset.prod_eq_one
    intro e he
    induction e with
    | _ x y =>
      by_cases hω : ω s(x, y) = true
      · rw [if_pos hω, Potts.monoIndicator_mk]
        have hadj : (openSub G ω).Adj x y :=
          ⟨(SimpleGraph.mem_edgeFinset.1 he), hω⟩
        rw [if_pos (h x y hadj)]
      · simp only [Bool.not_eq_true] at hω
        rw [if_neg (by rw [hω]; simp)]
  · rw [if_neg h]
    rw [Finset.prod_eq_zero_iff]
    simp only [ConstOnOpen, not_forall] at h
    obtain ⟨x, y, hadj, hne⟩ := h
    refine ⟨s(x, y), ?_, ?_⟩
    · exact SimpleGraph.mem_edgeFinset.2 hadj.1
    · rw [if_pos hadj.2, Potts.monoIndicator_mk, if_neg hne]




noncomputable def constOnOpenEquiv {q : ℕ} (ω : ConfigSpace (Sym2 V)) :
    ((openSub G ω).ConnectedComponent → Fin q) ≃ {σ : V → Fin q // ConstOnOpen G ω σ} where
  toFun τ := ⟨fun v => τ ((openSub G ω).connectedComponentMk v), by
    intro x y hxy
    simp only
    congr 1
    exact SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hxy⟩
  invFun σ := SimpleGraph.ConnectedComponent.lift σ.1 (by
    intro v w p _
    exact constOnOpen_reachable G ω σ.1 σ.2 p.reachable)
  left_inv τ := by
    funext c
    induction c using SimpleGraph.ConnectedComponent.ind with
    | _ v => rfl
  right_inv σ := by
    apply Subtype.ext
    funext v
    rfl



theorem card_constOnOpen {q : ℕ} (ω : ConfigSpace (Sym2 V)) :
    Nat.card {σ : V → Fin q // ConstOnOpen G ω σ} = q ^ numClusters G ω := by
  classical
  rw [Nat.card_congr (constOnOpenEquiv G ω).symm]
  rw [Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_fin]
  rfl




theorem esWeight_sum {q : ℕ} (p : ℝ) (ω : ConfigSpace (Sym2 V)) :
    (∑ σ : V → Fin q, esWeight G p σ ω) = fkWeight G p (q : ℝ) ω := by
  classical
  have hfac : (∑ σ : V → Fin q, esWeight G p σ ω)
      = edgeProduct G p ω * ∑ σ : V → Fin q, (if ConstOnOpen G ω σ then (1 : ℝ) else 0) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro σ _
    rw [esWeight_factor, monoProd_eq_indicator]
  rw [hfac, Finset.sum_boole]
  unfold fkWeight
  congr 1
  have hcard : ({x | ConstOnOpen G ω x} : Finset (V → Fin q)).card = q ^ numClusters G ω := by
    rw [← card_constOnOpen G ω, Nat.card_eq_fintype_card, Fintype.card_subtype]
  rw [hcard]
  push_cast
  rfl





def esCoeff {q : ℕ} (p : ℝ) (σ : V → Fin q) (e : Sym2 V) (b : Bool) : ℝ :=
  if e ∈ G.edgeFinset then (if b then p * Potts.monoIndicator σ e else 1 - p) else 1



theorem esWeight_eq_prod_univ {q : ℕ} (p : ℝ) (σ : V → Fin q) (ω : ConfigSpace (Sym2 V)) :
    esWeight G p σ ω = ∏ e : Sym2 V, esCoeff G p σ e (ω e) := by
  have hstep : (∏ e ∈ G.edgeFinset, esCoeff G p σ e (ω e))
      = ∏ e : Sym2 V, esCoeff G p σ e (ω e) := by
    apply Finset.prod_subset (Finset.subset_univ _)
    intro e _ he
    unfold esCoeff
    rw [if_neg he]
  rw [← hstep]
  unfold esWeight esCoeff esEdgeFactor
  apply Finset.prod_congr rfl
  intro e he
  rw [if_pos he]


theorem esWeight_sum_omega {q : ℕ} (p : ℝ) (σ : V → Fin q) :
    (∑ ω : ConfigSpace (Sym2 V), esWeight G p σ ω)
      = ∏ e : Sym2 V, ∑ b : Bool, esCoeff G p σ e b := by
  have hrw : (∑ ω : ConfigSpace (Sym2 V), esWeight G p σ ω)
      = ∑ ω : ConfigSpace (Sym2 V), ∏ e : Sym2 V, esCoeff G p σ e (ω e) := by
    apply Finset.sum_congr rfl
    intro ω _
    exact esWeight_eq_prod_univ G p σ ω
  rw [hrw, ← Fintype.prod_sum]



theorem esCoeff_bool_sum {q : ℕ} (p : ℝ) (σ : V → Fin q) (e : Sym2 V) :
    (∑ b : Bool, esCoeff G p σ e b)
      = if e ∈ G.edgeFinset then (1 - p) + p * Potts.monoIndicator σ e else 2 := by
  unfold esCoeff
  rw [Fintype.sum_bool]
  by_cases he : e ∈ G.edgeFinset
  · simp only [if_pos he, if_true]
    norm_num
    ring
  · simp only [if_neg he]
    norm_num

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in



theorem edge_sum_eq_exp {q : ℕ} (β J : ℝ) (σ : V → Fin q) (e : Sym2 V) :
    (1 - (1 - Real.exp (-(β * J)))) + (1 - Real.exp (-(β * J))) * Potts.monoIndicator σ e
      = Real.exp (-(β * J)) * Real.exp (β * J * Potts.monoIndicator σ e) := by
  induction e with
  | _ x y =>
    rw [Potts.monoIndicator_mk]
    by_cases h : σ x = σ y
    · rw [if_pos h, mul_one, ← Real.exp_add]
      rw [show -(β * J) + β * J * 1 = 0 by ring, Real.exp_zero]
      ring
    · rw [if_neg h]
      simp only [mul_zero, Real.exp_zero, mul_one]
      ring



noncomputable def esFirstConst (β J : ℝ) : ℝ :=
  2 ^ (Fintype.card (Sym2 V) - G.edgeFinset.card)
    * Real.exp (-(β * J)) ^ G.edgeFinset.card

omit [DecidableEq V] in
theorem esFirstConst_pos (β J : ℝ) : 0 < esFirstConst G β J := by
  unfold esFirstConst
  exact mul_pos (pow_pos (by norm_num) _) (pow_pos (Real.exp_pos _) _)



theorem esWeight_sum_eq_pottsWeight {q : ℕ} (β J : ℝ) (σ : V → Fin q) :
    (∑ ω : ConfigSpace (Sym2 V), esWeight G (1 - Real.exp (-(β * J))) σ ω)
      = esFirstConst G β J * Potts.pottsWeight G β J σ := by
  set p := 1 - Real.exp (-(β * J)) with hp
  rw [esWeight_sum_omega]
  have hcoeff : ∀ e : Sym2 V, (∑ b : Bool, esCoeff G p σ e b)
      = if e ∈ G.edgeFinset then
          Real.exp (-(β * J)) * Real.exp (β * J * Potts.monoIndicator σ e) else 2 := by
    intro e
    rw [esCoeff_bool_sum]
    by_cases he : e ∈ G.edgeFinset
    · rw [if_pos he, if_pos he, hp]
      exact edge_sum_eq_exp β J σ e
    · rw [if_neg he, if_neg he]
  rw [Finset.prod_congr rfl (fun e _ => hcoeff e)]
  rw [← Finset.prod_filter_mul_prod_filter_not Finset.univ (· ∈ G.edgeFinset)]
  have hedge : (∏ e ∈ Finset.univ.filter (· ∈ G.edgeFinset),
        if e ∈ G.edgeFinset then
          Real.exp (-(β * J)) * Real.exp (β * J * Potts.monoIndicator σ e) else 2)
      = Real.exp (-(β * J)) ^ G.edgeFinset.card * Potts.pottsWeight G β J σ := by
    rw [Finset.filter_mem_eq_inter, Finset.univ_inter]
    rw [Finset.prod_congr rfl (fun e he => if_pos he)]
    rw [Finset.prod_mul_distrib, Finset.prod_const]
    unfold Potts.pottsWeight Potts.agreement
    rw [← Real.exp_sum, Finset.mul_sum]
  have hnon : (∏ e ∈ Finset.univ.filter (fun e => ¬ e ∈ G.edgeFinset),
        if e ∈ G.edgeFinset then
          Real.exp (-(β * J)) * Real.exp (β * J * Potts.monoIndicator σ e) else 2)
      = 2 ^ (Fintype.card (Sym2 V) - G.edgeFinset.card) := by
    rw [Finset.prod_congr rfl (fun e he => if_neg (Finset.mem_filter.1 he).2)]
    rw [Finset.prod_const]
    congr 1
    rw [Finset.filter_not, Finset.card_sdiff]
    rw [Finset.filter_mem_eq_inter, Finset.univ_inter, Finset.card_univ, Finset.inter_univ]
  rw [hedge, hnon]
  unfold esFirstConst
  ring




noncomputable def esZ (q : ℕ) (p : ℝ) : ℝ :=
  ∑ ω : ConfigSpace (Sym2 V), ∑ σ : V → Fin q, esWeight G p σ ω



theorem esZ_eq_fkZ (q : ℕ) (p : ℝ) : esZ G q p = fkZ G p (q : ℝ) := by
  unfold esZ fkZ
  exact Finset.sum_congr rfl fun ω _ => esWeight_sum G p ω


theorem esZ_eq_pottsZ (q : ℕ) [NeZero q] (β J : ℝ) :
    esZ G q (1 - Real.exp (-(β * J))) = esFirstConst G β J * Potts.pottsZ G q β J := by
  unfold esZ
  rw [Finset.sum_comm]
  unfold Potts.pottsZ
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro σ _
  exact esWeight_sum_eq_pottsWeight G β J σ



theorem esZ_pos {q : ℕ} {p : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < (q : ℝ)) :
    0 < esZ G q p := by
  rw [esZ_eq_fkZ]
  exact fkZ_pos G hp hp1 hq




noncomputable def esSecondMarginal (q : ℕ) (p : ℝ) (ω : ConfigSpace (Sym2 V)) : ℝ :=
  (∑ σ : V → Fin q, esWeight G p σ ω) / esZ G q p




noncomputable def esFirstMarginal (q : ℕ) (p : ℝ) (σ : V → Fin q) : ℝ :=
  (∑ ω : ConfigSpace (Sym2 V), esWeight G p σ ω) / esZ G q p



theorem esSecondMarginal_eq_fkProb (q : ℕ) (p : ℝ) (ω : ConfigSpace (Sym2 V)) :
    esSecondMarginal G q p ω = fkProb G p (q : ℝ) ω := by
  unfold esSecondMarginal fkProb
  rw [esWeight_sum, esZ_eq_fkZ]




theorem esFirstMarginal_eq_pottsProb (q : ℕ) [NeZero q] (β J : ℝ) (σ : V → Fin q) :
    esFirstMarginal G q (1 - Real.exp (-(β * J))) σ = Potts.pottsProb G q β J σ := by
  unfold esFirstMarginal Potts.pottsProb
  rw [esWeight_sum_eq_pottsWeight, esZ_eq_pottsZ]
  rw [mul_div_mul_left _ _ (esFirstConst_pos G β J).ne']


theorem esSecondMarginal_nonneg {q : ℕ} {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (hq : 0 < (q : ℝ)) (ω : ConfigSpace (Sym2 V)) :
    0 ≤ esSecondMarginal G q p ω := by
  rw [esSecondMarginal_eq_fkProb]
  exact fkProb_nonneg G hp hp1 hq ω


theorem esSecondMarginal_sum_eq_one {q : ℕ} {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (hq : 0 < (q : ℝ)) :
    (∑ ω : ConfigSpace (Sym2 V), esSecondMarginal G q p ω) = 1 := by
  rw [Finset.sum_congr rfl fun ω _ => esSecondMarginal_eq_fkProb G q p ω]
  exact fkProb_sum_eq_one G hp hp1 hq


theorem esFirstMarginal_nonneg {q : ℕ} [NeZero q] (β J : ℝ) (σ : V → Fin q) :
    0 ≤ esFirstMarginal G q (1 - Real.exp (-(β * J))) σ := by
  rw [esFirstMarginal_eq_pottsProb]
  exact Potts.pottsProb_nonneg G q β J σ


theorem esFirstMarginal_sum_eq_one {q : ℕ} [NeZero q] (β J : ℝ) :
    (∑ σ : V → Fin q, esFirstMarginal G q (1 - Real.exp (-(β * J))) σ) = 1 := by
  rw [Finset.sum_congr rfl fun σ _ => esFirstMarginal_eq_pottsProb G q β J σ]
  exact Potts.pottsProb_sum_eq_one G q β J






theorem edwardsSokal_secondMarginal (q : ℕ) (β J : ℝ) (ω : ConfigSpace (Sym2 V)) :
    esSecondMarginal G q (1 - Real.exp (-(β * J))) ω
      = fkProb G (1 - Real.exp (-(β * J))) (q : ℝ) ω :=
  esSecondMarginal_eq_fkProb G q (1 - Real.exp (-(β * J))) ω




theorem edwardsSokal_firstMarginal (q : ℕ) [NeZero q] (β J : ℝ) (σ : V → Fin q) :
    esFirstMarginal G q (1 - Real.exp (-(β * J))) σ = Potts.pottsProb G q β J σ :=
  esFirstMarginal_eq_pottsProb G q β J σ

end FK

end StatMech

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import PhyslibExt.StatisticalMechanics.RandomCluster.Potts
public import PhyslibExt.StatisticalMechanics.RandomCluster.RandomCluster

/-!
# The Edwards–Sokal coupling

The Edwards–Sokal joint measure on Potts spins and bond configurations of a finite graph, and its
two marginals: the `q`-state Potts model and the random-cluster model.

## i. Overview

For a finite graph `G`, an integer `q ≥ 1`, and `p ∈ [0, 1]`, the Edwards–Sokal weight of a pair
`(σ, ω)` of a spin configuration `σ : V → Fin q` and a bond configuration `ω` is
`∏_{e ∈ E(G)} ((1 - p) 1[ω(e) = 0] + p 1[ω(e) = 1] 1[σ constant on e])`. Summing over `σ` gives
the random-cluster weight `p^{o(ω)} (1 - p)^{c(ω)} q^{k(ω)}`; summing over `ω` with
`p = 1 - e^{-βJ}` gives `e^{-βJ |E|}` times the Potts weight `exp(βJ · #agreeing edges)`. Hence
both marginals of the normalized joint measure are the FK and Potts measures.

## ii. Key results

- `StatMech.FK.esWeight_sum` : the spin marginal of the joint weight is the FK weight.
- `StatMech.FK.esWeight_sum_eq_pottsWeight` : the bond marginal is a constant times the Potts
  weight.
- `StatMech.FK.edwardsSokal_secondMarginal`, `StatMech.FK.edwardsSokal_firstMarginal` : the
  normalized marginals are the random-cluster and Potts measures.

## iii. Table of contents

- A. The joint weight
- B. Spin marginal: counting colorings constant on clusters
- C. Bond marginal: the Potts weight
- D. Partition functions and marginals

## iv. References

- R. G. Edwards and A. D. Sokal, *Generalization of the Fortuin–Kasteleyn–Swendsen–Wang
  representation and Monte Carlo algorithm*, Phys. Rev. D 38 (1988).
- H. Duminil-Copin, *Lectures on the Ising and Potts models on the hypercubic lattice* (2017), §1.
-/

@[expose] public section

open scoped BigOperators

namespace StatMech

namespace FK

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-! ## A. The joint weight -/

/-- The Edwards–Sokal factor of an edge `e`: `1 - p` if `e` is closed in `ω`, and `p` times the
indicator that `σ` agrees at the endpoints if `e` is open.
-/
def esEdgeFactor {q : ℕ} (p : ℝ) (σ : V → Fin q) (ω : ConfigSpace (Sym2 V)) (e : Sym2 V) : ℝ :=
  if ω e then p * Potts.monoIndicator σ e else 1 - p

/-- The Edwards–Sokal joint weight of a spin configuration `σ` and a bond configuration `ω`: the
product of `esEdgeFactor` over the edges of `G`.
-/
def esWeight {q : ℕ} (p : ℝ) (σ : V → Fin q) (ω : ConfigSpace (Sym2 V)) : ℝ :=
  ∏ e ∈ G.edgeFinset, esEdgeFactor p σ ω e

omit [DecidableEq V] in
lemma esWeight_nonneg {q : ℕ} {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (σ : V → Fin q) (ω : ConfigSpace (Sym2 V)) : 0 ≤ esWeight G p σ ω := by
  unfold esWeight esEdgeFactor
  apply Finset.prod_nonneg
  intro e _
  split
  · exact mul_nonneg hp (Potts.monoIndicator_nonneg σ e)
  · linarith

/-! ## B. Spin marginal: counting colorings constant on clusters -/

/-- `σ` is constant on every open edge of `ω`, i.e. on every open cluster. -/
def ConstOnOpen {q : ℕ} (ω : ConfigSpace (Sym2 V)) (σ : V → Fin q) : Prop :=
  ∀ x y, (openSub G ω).Adj x y → σ x = σ y

/-- Decidability of `ConstOnOpen` (a finite conjunction over the edges of `G`). -/
instance instDecidableConstOnOpen {q : ℕ} (ω : ConfigSpace (Sym2 V)) (σ : V → Fin q) :
    Decidable (ConstOnOpen G ω σ) := by
  unfold ConstOnOpen
  infer_instance

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
lemma constOnOpen_reachable {q : ℕ} (ω : ConfigSpace (Sym2 V)) (σ : V → Fin q)
    (h : ConstOnOpen G ω σ) {x y : V} (r : (openSub G ω).Reachable x y) : σ x = σ y := by
  rw [SimpleGraph.reachable_iff_reflTransGen] at r
  induction r with
  | refl => rfl
  | tail _ hab ih => rw [ih]; exact h _ _ hab

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
lemma esEdgeFactor_eq {q : ℕ} (p : ℝ) (σ : V → Fin q) (ω : ConfigSpace (Sym2 V)) (e : Sym2 V) :
    esEdgeFactor p σ ω e =
      (if ω e then p else 1 - p) * (if ω e then Potts.monoIndicator σ e else 1) := by
  unfold esEdgeFactor
  split
  · ring
  · ring

omit [DecidableEq V] in
lemma esWeight_factor {q : ℕ} (p : ℝ) (σ : V → Fin q) (ω : ConfigSpace (Sym2 V)) :
    esWeight G p σ ω = edgeProduct G p ω *
      ∏ e ∈ G.edgeFinset, (if ω e then Potts.monoIndicator σ e else 1) := by
  unfold esWeight edgeProduct
  rw [← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun e _ => esEdgeFactor_eq p σ ω e

omit [DecidableEq V] in
lemma monoProd_eq_indicator {q : ℕ} (σ : V → Fin q) (ω : ConfigSpace (Sym2 V)) :
    (∏ e ∈ G.edgeFinset, (if ω e then Potts.monoIndicator σ e else 1)) =
      if ConstOnOpen G ω σ then 1 else 0 := by
  by_cases h : ConstOnOpen G ω σ
  · rw [ite_eq_left h]
    apply Finset.prod_eq_one
    intro e he
    induction e with
    | _ x y =>
      by_cases hω : ω s(x, y) = true
      · rw [ite_eq_left hω, Potts.monoIndicator_mk]
        have hadj : (openSub G ω).Adj x y :=
          ⟨(SimpleGraph.mem_edgeFinset.1 he), hω⟩
        rw [ite_eq_left (h x y hadj)]
      · simp only [Bool.not_eq_true] at hω
        rw [ite_eq_right (by rw [hω]; simp)]
  · rw [ite_eq_right h]
    rw [Finset.prod_eq_zero_iff]
    simp only [ConstOnOpen, not_forall] at h
    obtain ⟨x, y, hadj, hne⟩ := h
    refine ⟨s(x, y), ?_, ?_⟩
    · exact SimpleGraph.mem_edgeFinset.2 hadj.1
    · rw [ite_eq_left hadj.2, Potts.monoIndicator_mk, ite_eq_right hne]

/-- Colorings constant on open clusters correspond to colorings of the connected components of the
open subgraph.
-/
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

/-- There are `q ^ k(ω)` colorings constant on the open clusters, where `k(ω)` is the number of
clusters.
-/
lemma card_constOnOpen {q : ℕ} (ω : ConfigSpace (Sym2 V)) :
    Nat.card {σ : V → Fin q // ConstOnOpen G ω σ} = q ^ numClusters G ω := by
  classical
  rw [Nat.card_congr (constOnOpenEquiv G ω).symm]
  rw [Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_fin]
  rfl

/-- Spin marginal of the Edwards–Sokal weight: summing over spins gives the random-cluster weight
`p^{o(ω)} (1 - p)^{c(ω)} q^{k(ω)}`.
-/
lemma esWeight_sum {q : ℕ} (p : ℝ) (ω : ConfigSpace (Sym2 V)) :
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

/-! ## C. Bond marginal: the Potts weight -/

/-- The Edwards–Sokal factor of an edge `e` written for an arbitrary pair `(e, b)` with `b` the
state
of `e`; edges outside `G` get factor `1`.
-/
def esCoeff {q : ℕ} (p : ℝ) (σ : V → Fin q) (e : Sym2 V) (b : Bool) : ℝ :=
  if e ∈ G.edgeFinset then (if b then p * Potts.monoIndicator σ e else 1 - p) else 1

lemma esWeight_eq_prod_univ {q : ℕ} (p : ℝ) (σ : V → Fin q) (ω : ConfigSpace (Sym2 V)) :
    esWeight G p σ ω = ∏ e : Sym2 V, esCoeff G p σ e (ω e) := by
  have hstep : (∏ e ∈ G.edgeFinset, esCoeff G p σ e (ω e))
      = ∏ e : Sym2 V, esCoeff G p σ e (ω e) := by
    apply Finset.prod_subset (Finset.subset_univ _)
    intro e _ he
    unfold esCoeff
    rw [ite_eq_right he]
  rw [← hstep]
  unfold esWeight esCoeff esEdgeFactor
  apply Finset.prod_congr rfl
  intro e he
  rw [ite_eq_left he]

lemma esWeight_sum_omega {q : ℕ} (p : ℝ) (σ : V → Fin q) :
    (∑ ω : ConfigSpace (Sym2 V), esWeight G p σ ω)
      = ∏ e : Sym2 V, ∑ b : Bool, esCoeff G p σ e b := by
  have hrw : (∑ ω : ConfigSpace (Sym2 V), esWeight G p σ ω)
      = ∑ ω : ConfigSpace (Sym2 V), ∏ e : Sym2 V, esCoeff G p σ e (ω e) := by
    apply Finset.sum_congr rfl
    intro ω _
    exact esWeight_eq_prod_univ G p σ ω
  rw [hrw, ← Fintype.prod_sum]

lemma esCoeff_bool_sum {q : ℕ} (p : ℝ) (σ : V → Fin q) (e : Sym2 V) :
    (∑ b : Bool, esCoeff G p σ e b)
      = if e ∈ G.edgeFinset then (1 - p) + p * Potts.monoIndicator σ e else 2 := by
  unfold esCoeff
  rw [Fintype.sum_bool]
  by_cases he : e ∈ G.edgeFinset
  · simp only [ite_eq_left he, ite_true]
    norm_num
    ring
  · simp only [ite_eq_right he]
    norm_num

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
lemma edge_sum_eq_exp {q : ℕ} (β J : ℝ) (σ : V → Fin q) (e : Sym2 V) :
    (1 - (1 - Real.exp (-(β * J)))) + (1 - Real.exp (-(β * J))) * Potts.monoIndicator σ e
      = Real.exp (-(β * J)) * Real.exp (β * J * Potts.monoIndicator σ e) := by
  induction e with
  | _ x y =>
    rw [Potts.monoIndicator_mk]
    by_cases h : σ x = σ y
    · rw [ite_eq_left h, mul_one, ← Real.exp_add]
      rw [show -(β * J) + β * J * 1 = 0 by ring, Real.exp_zero]
      ring
    · rw [ite_eq_right h]
      simp only [mul_zero, Real.exp_zero, mul_one]
      ring

/-- The normalizing constant `e^{-βJ |E(G)|}` relating the bond marginal to the Potts weight. -/
noncomputable def esFirstConst (β J : ℝ) : ℝ :=
  2 ^ (Fintype.card (Sym2 V) - G.edgeFinset.card)
    * Real.exp (-(β * J)) ^ G.edgeFinset.card

omit [DecidableEq V] in
lemma esFirstConst_pos (β J : ℝ) : 0 < esFirstConst G β J := by
  unfold esFirstConst
  exact mul_pos (pow_pos (by norm_num) _) (pow_pos (Real.exp_pos _) _)

/-- Bond marginal of the Edwards–Sokal weight: with `p = 1 - e^{-βJ}`, summing over bond
configurations gives `e^{-βJ |E|}` times the Potts weight of `σ`.
-/
lemma esWeight_sum_eq_pottsWeight {q : ℕ} (β J : ℝ) (σ : V → Fin q) :
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
    · rw [ite_eq_left he, ite_eq_left he, hp]
      exact edge_sum_eq_exp β J σ e
    · rw [ite_eq_right he, ite_eq_right he]
  rw [Finset.prod_congr rfl (fun e _ => hcoeff e)]
  rw [← Finset.prod_filter_mul_prod_filter_not Finset.univ (· ∈ G.edgeFinset)]
  have hedge : (∏ e ∈ Finset.univ.filter (· ∈ G.edgeFinset),
        if e ∈ G.edgeFinset then
          Real.exp (-(β * J)) * Real.exp (β * J * Potts.monoIndicator σ e) else 2)
      = Real.exp (-(β * J)) ^ G.edgeFinset.card * Potts.pottsWeight G β J σ := by
    rw [Finset.filter_mem_eq_inter, Finset.univ_inter]
    rw [Finset.prod_congr rfl (fun e he => ite_eq_left he)]
    rw [Finset.prod_mul_distrib, Finset.prod_const]
    unfold Potts.pottsWeight Potts.agreement
    rw [← Real.exp_sum, Finset.mul_sum]
  have hnon : (∏ e ∈ Finset.univ.filter (fun e => ¬ e ∈ G.edgeFinset),
        if e ∈ G.edgeFinset then
          Real.exp (-(β * J)) * Real.exp (β * J * Potts.monoIndicator σ e) else 2)
      = 2 ^ (Fintype.card (Sym2 V) - G.edgeFinset.card) := by
    rw [Finset.prod_congr rfl (fun e he => ite_eq_right (Finset.mem_filter.1 he).2)]
    rw [Finset.prod_const]
    congr 1
    rw [Finset.filter_not, Finset.card_sdiff]
    rw [Finset.filter_mem_eq_inter, Finset.univ_inter, Finset.card_univ, Finset.inter_univ]
  rw [hedge, hnon]
  unfold esFirstConst
  ring

/-! ## D. Partition functions and marginals -/

/-- The Edwards–Sokal partition function: the total joint weight. -/
noncomputable def esZ (q : ℕ) (p : ℝ) : ℝ :=
  ∑ ω : ConfigSpace (Sym2 V), ∑ σ : V → Fin q, esWeight G p σ ω

lemma esZ_eq_fkZ (q : ℕ) (p : ℝ) : esZ G q p = fkZ G p (q : ℝ) := by
  unfold esZ fkZ
  exact Finset.sum_congr rfl fun ω _ => esWeight_sum G p ω

lemma esZ_eq_pottsZ (q : ℕ) [NeZero q] (β J : ℝ) :
    esZ G q (1 - Real.exp (-(β * J))) = esFirstConst G β J * Potts.pottsZ G q β J := by
  unfold esZ
  rw [Finset.sum_comm]
  unfold Potts.pottsZ
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro σ _
  exact esWeight_sum_eq_pottsWeight G β J σ

lemma esZ_pos {q : ℕ} {p : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < (q : ℝ)) :
    0 < esZ G q p := by
  rw [esZ_eq_fkZ]
  exact fkZ_pos G hp hp1 hq

/-- The bond marginal of the normalized Edwards–Sokal measure. -/
noncomputable def esSecondMarginal (q : ℕ) (p : ℝ) (ω : ConfigSpace (Sym2 V)) : ℝ :=
  (∑ σ : V → Fin q, esWeight G p σ ω) / esZ G q p

/-- The spin marginal of the normalized Edwards–Sokal measure. -/
noncomputable def esFirstMarginal (q : ℕ) (p : ℝ) (σ : V → Fin q) : ℝ :=
  (∑ ω : ConfigSpace (Sym2 V), esWeight G p σ ω) / esZ G q p

lemma esSecondMarginal_eq_fkProb (q : ℕ) (p : ℝ) (ω : ConfigSpace (Sym2 V)) :
    esSecondMarginal G q p ω = fkProb G p (q : ℝ) ω := by
  unfold esSecondMarginal fkProb
  rw [esWeight_sum, esZ_eq_fkZ]

lemma esFirstMarginal_eq_pottsProb (q : ℕ) [NeZero q] (β J : ℝ) (σ : V → Fin q) :
    esFirstMarginal G q (1 - Real.exp (-(β * J))) σ = Potts.pottsProb G q β J σ := by
  unfold esFirstMarginal Potts.pottsProb
  rw [esWeight_sum_eq_pottsWeight, esZ_eq_pottsZ]
  rw [mul_div_mul_left _ _ (esFirstConst_pos G β J).ne']

lemma esSecondMarginal_nonneg {q : ℕ} {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (hq : 0 < (q : ℝ)) (ω : ConfigSpace (Sym2 V)) :
    0 ≤ esSecondMarginal G q p ω := by
  rw [esSecondMarginal_eq_fkProb]
  exact fkProb_nonneg G hp hp1 hq ω

lemma esSecondMarginal_sum_eq_one {q : ℕ} {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (hq : 0 < (q : ℝ)) :
    (∑ ω : ConfigSpace (Sym2 V), esSecondMarginal G q p ω) = 1 := by
  rw [Finset.sum_congr rfl fun ω _ => esSecondMarginal_eq_fkProb G q p ω]
  exact fkProb_sum_eq_one G hp hp1 hq

lemma esFirstMarginal_nonneg {q : ℕ} [NeZero q] (β J : ℝ) (σ : V → Fin q) :
    0 ≤ esFirstMarginal G q (1 - Real.exp (-(β * J))) σ := by
  rw [esFirstMarginal_eq_pottsProb]
  exact Potts.pottsProb_nonneg G q β J σ

lemma esFirstMarginal_sum_eq_one {q : ℕ} [NeZero q] (β J : ℝ) :
    (∑ σ : V → Fin q, esFirstMarginal G q (1 - Real.exp (-(β * J))) σ) = 1 := by
  rw [Finset.sum_congr rfl fun σ _ => esFirstMarginal_eq_pottsProb G q β J σ]
  exact Potts.pottsProb_sum_eq_one G q β J

/-- The bond marginal of the Edwards–Sokal measure is the random-cluster measure with parameters
`(1 - e^{-βJ}, q)`.
-/
lemma edwardsSokal_secondMarginal (q : ℕ) (β J : ℝ) (ω : ConfigSpace (Sym2 V)) :
    esSecondMarginal G q (1 - Real.exp (-(β * J))) ω
      = fkProb G (1 - Real.exp (-(β * J))) (q : ℝ) ω :=
  esSecondMarginal_eq_fkProb G q (1 - Real.exp (-(β * J))) ω

/-- The spin marginal of the Edwards–Sokal measure is the `q`-state Potts measure at inverse
temperature `β` and coupling `J`.
-/
lemma edwardsSokal_firstMarginal (q : ℕ) [NeZero q] (β J : ℝ) (σ : V → Fin q) :
    esFirstMarginal G q (1 - Real.exp (-(β * J))) σ = Potts.pottsProb G q β J σ :=
  esFirstMarginal_eq_pottsProb G q β J σ

end FK

end StatMech

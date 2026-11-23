/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Probability.CorrelationInequalities.Pivotal
public import PhyslibExt.StatisticalMechanics.RandomCluster.Comparison
/-!
# Finite energy of the random-cluster measure

Conditional on all other edges, an edge of `G` is open under `φ_{G,p,q}` with probability
bounded away from `0` and `1`, uniformly in the boundary condition.

## i. Overview

For an edge `e` and a configuration `ω`, `condOpen G p q e ω` is the probability of
`setOpen e ω` among the two configurations that agree with `ω` off `e`, that is, the conditional
probability that `e` is open given the states of all other edges. Opening `e` merges at most two
clusters, so the cluster count drops by `0` or `1`
(`numClusters_setOpen_le`, `numClusters_setClosed_le_setOpen_succ`). For `q ≥ 1` this gives
`p / (p + q (1 - p)) ≤ condOpen G p q e ω ≤ p`, and `finite_energy` records the symmetric form
`cFE p q ≤ condOpen ≤ 1 - cFE p q` with `cFE p q = min (p / (p + q (1 - p))) (1 - p)`.
For `e` not an edge of `G` the weight ignores `e` and `condOpen = 1 / 2`.

## ii. Key results

- `StatMech.FK.numClusters_setOpen_le`, `StatMech.FK.numClusters_setClosed_le_setOpen_succ` :
  opening an edge lowers the cluster count by at most one.
- `StatMech.FK.condOpen` : the single-edge conditional probability of being open.
- `StatMech.FK.cFE` : the finite-energy constant.
- `StatMech.FK.finite_energy` : the finite-energy bounds for `q ≥ 1`.

## iii. Table of contents

- A. Cluster counts under a single-edge flip
- B. Weights under a single-edge flip
- C. The single-edge conditional probability
- D. The finite-energy bound

## iv. References

- G. Grimmett, *The Random-Cluster Model*, Springer (2006), Chapter 3.

-/

@[expose] public section

open scoped BigOperators
open Module SimpleGraph

namespace StatMech

namespace FK

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-!

## A. Cluster counts under a single-edge flip

-/

lemma numClusters_congr_openSub {ω ω' : ConfigSpace (Sym2 V)}
    (h : openSub G ω = openSub G ω') : numClusters G ω = numClusters G ω' := by
  unfold numClusters
  exact Fintype.card_congr (Equiv.cast (by rw [h]))

/-- Off the edges of `G`, flipping `e` does not change the open subgraph. -/
lemma openSub_setOpen_eq_setClosed_of_notMem {e : Sym2 V} (he : e ∉ G.edgeFinset)
    (ω : ConfigSpace (Sym2 V)) :
    openSub G (setOpen e ω) = openSub G (setClosed e ω) := by
  ext a b
  simp only [openSub_adj]
  constructor
  · rintro ⟨hadj, hopen⟩
    have hne : s(a, b) ≠ e := fun h => he (by rw [SimpleGraph.mem_edgeFinset, ← h]; exact hadj)
    exact ⟨hadj, by rw [setClosed_of_ne hne]; rw [setOpen_of_ne hne] at hopen; exact hopen⟩
  · rintro ⟨hadj, hopen⟩
    have hne : s(a, b) ≠ e := fun h => he (by rw [SimpleGraph.mem_edgeFinset, ← h]; exact hadj)
    exact ⟨hadj, by rw [setOpen_of_ne hne]; rw [setClosed_of_ne hne] at hopen; exact hopen⟩

/-- Opening an edge does not increase the number of clusters. This is a special case of
Mathlib's `SimpleGraph.ConnectedComponent.card_le_card_of_le`, which proves it. -/
lemma numClusters_setOpen_le (e : Sym2 V) (ω : ConfigSpace (Sym2 V)) :
    numClusters G (setOpen e ω) ≤ numClusters G (setClosed e ω) := by
  unfold numClusters
  rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card]
  apply SimpleGraph.ConnectedComponent.card_le_card_of_le
  intro i j hij
  rw [openSub_adj] at hij ⊢
  refine ⟨hij.1, ?_⟩
  have hle := setClosed_le_setOpen e ω s(i, j)
  rw [hij.2] at hle
  exact le_antisymm (by simp) hle

/-- Opening an edge lowers the number of clusters by at most one. -/
lemma numClusters_setClosed_le_setOpen_succ (e : Sym2 V) (ω : ConfigSpace (Sym2 V)) :
    numClusters G (setClosed e ω) ≤ numClusters G (setOpen e ω) + 1 := by
  by_cases he : e ∈ G.edgeFinset
  · obtain ⟨i0, j0, hadj, heq⟩ : ∃ i j, G.Adj i j ∧ e = s(i, j) := by
      rw [SimpleGraph.mem_edgeFinset] at he
      induction e with
      | h i j => exact ⟨i, j, he, rfl⟩
    rw [numClusters_eq_finrank, numClusters_eq_finrank]
    set f : (V → ℝ) →ₗ[ℝ] ℝ :=
      { toFun := fun x => x i0 - x j0
        map_add' := by intro x y; simp; ring
        map_smul' := by intro c x; simp; ring } with hf
    have hkey : kerLap G (setOpen e ω) = kerLap G (setClosed e ω) ⊓ LinearMap.ker f := by
      apply le_antisymm
      · intro x hx
        rw [mem_kerLap] at hx
        refine Submodule.mem_inf.mpr ⟨(mem_kerLap _ _ _).mpr ?_, ?_⟩
        · intro a b hab
          apply hx
          rw [openSub_adj] at hab ⊢
          refine ⟨hab.1, ?_⟩
          have hle := setClosed_le_setOpen e ω s(a, b)
          rw [hab.2] at hle
          exact le_antisymm (by simp) hle
        · rw [LinearMap.mem_ker]
          change x i0 - x j0 = 0
          have hopenadj : (openSub G (setOpen e ω)).Adj i0 j0 := by
            rw [openSub_adj]
            refine ⟨hadj, ?_⟩
            rw [heq]
            exact setOpen_self _ ω
          have := hx i0 j0 hopenadj
          linarith
      · intro x hx
        obtain ⟨hx1, hx2⟩ := Submodule.mem_inf.mp hx
        rw [mem_kerLap] at hx1 ⊢
        rw [LinearMap.mem_ker] at hx2
        have hx2' : x i0 = x j0 := by have : x i0 - x j0 = 0 := hx2; linarith
        intro a b hab
        rw [openSub_adj] at hab
        by_cases hc : setClosed e ω s(a, b) = true
        · exact hx1 a b ((openSub_adj _ _ _ _).mpr ⟨hab.1, hc⟩)
        · have hsab : s(a, b) = e := by
            by_contra hne
            rw [setClosed_of_ne hne] at hc
            rw [setOpen_of_ne hne] at hab
            exact hc hab.2
          rw [heq, Sym2.eq_iff] at hsab
          rcases hsab with ⟨ha, hb⟩ | ⟨ha, hb⟩
          · subst ha; subst hb; exact hx2'
          · subst ha; subst hb; exact hx2'.symm
    rw [hkey]
    have hsub := Submodule.finrank_sup_add_finrank_inf_eq
      (kerLap G (setClosed e ω)) (LinearMap.ker f)
    have htop : finrank ℝ ((kerLap G (setClosed e ω)) ⊔ LinearMap.ker f :
        Submodule ℝ (V → ℝ)) ≤ finrank ℝ (V → ℝ) := Submodule.finrank_le _
    have hkerf : finrank ℝ (V → ℝ) ≤ finrank ℝ (LinearMap.ker f) + 1 := by
      have h1 := LinearMap.finrank_range_add_finrank_ker f
      have h2 : finrank ℝ (LinearMap.range f) ≤ 1 := by
        calc finrank ℝ (LinearMap.range f) ≤ finrank ℝ ℝ := Submodule.finrank_le _
          _ = 1 := by simp
      omega
    omega
  · have hopen_eq := openSub_setOpen_eq_setClosed_of_notMem G he ω
    have : numClusters G (setClosed e ω) = numClusters G (setOpen e ω) :=
      numClusters_congr_openSub G hopen_eq.symm
    omega

/-!

## B. Weights under a single-edge flip

-/

/-- The Bernoulli product over the edges of `G` other than `e`. -/
noncomputable def edgeRest (p : ℝ) (e : Sym2 V) (ω : ConfigSpace (Sym2 V)) : ℝ :=
  ∏ e' ∈ G.edgeFinset \ {e}, (if ω e' then p else 1 - p)

lemma edgeRest_pos {p : ℝ} (hp : 0 < p) (hp1 : p < 1) (e : Sym2 V)
    (ω : ConfigSpace (Sym2 V)) : 0 < edgeRest G p e ω := by
  unfold edgeRest
  apply Finset.prod_pos
  intro e' _
  split
  · exact hp
  · linarith

lemma edgeProduct_setOpen (p : ℝ) {e : Sym2 V} (he : e ∈ G.edgeFinset)
    (ω : ConfigSpace (Sym2 V)) :
    edgeProduct G p (setOpen e ω) = edgeRest G p e ω * p := by
  unfold edgeProduct edgeRest
  rw [← Finset.prod_sdiff (Finset.singleton_subset_iff.mpr he)]
  have h1 : (∏ e' ∈ G.edgeFinset \ {e}, (if (setOpen e ω) e' then p else 1 - p))
      = ∏ e' ∈ G.edgeFinset \ {e}, (if ω e' then p else 1 - p) := by
    apply Finset.prod_congr rfl
    intro e' he'
    have : e' ≠ e := by
      simp only [Finset.mem_sdiff, Finset.mem_singleton] at he'; exact he'.2
    rw [setOpen_of_ne this]
  rw [h1]
  simp [setOpen_self]

lemma edgeProduct_setClosed (p : ℝ) {e : Sym2 V} (he : e ∈ G.edgeFinset)
    (ω : ConfigSpace (Sym2 V)) :
    edgeProduct G p (setClosed e ω) = edgeRest G p e ω * (1 - p) := by
  unfold edgeProduct edgeRest
  rw [← Finset.prod_sdiff (Finset.singleton_subset_iff.mpr he)]
  have h1 : (∏ e' ∈ G.edgeFinset \ {e}, (if (setClosed e ω) e' then p else 1 - p))
      = ∏ e' ∈ G.edgeFinset \ {e}, (if ω e' then p else 1 - p) := by
    apply Finset.prod_congr rfl
    intro e' he'
    have : e' ≠ e := by
      simp only [Finset.mem_sdiff, Finset.mem_singleton] at he'; exact he'.2
    rw [setClosed_of_ne this]
  rw [h1]
  simp [setClosed_self]

lemma fkWeight_lo {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    {e : Sym2 V} (he : e ∈ G.edgeFinset) (ω : ConfigSpace (Sym2 V)) :
    (1 - p) * fkWeight G p q (setOpen e ω) ≤ p * fkWeight G p q (setClosed e ω) := by
  unfold fkWeight
  rw [edgeProduct_setOpen G p he, edgeProduct_setClosed G p he]
  set R := edgeRest G p e ω with hR
  set k1 := numClusters G (setOpen e ω)
  set k0 := numClusters G (setClosed e ω)
  have hRpos := edgeRest_pos G hp hp1 e ω
  have hpow : q ^ k1 ≤ q ^ k0 := pow_le_pow_right₀ hq (numClusters_setOpen_le G e ω)
  have hfac : (0 : ℝ) ≤ R * p * (1 - p) := by positivity
  nlinarith [mul_le_mul_of_nonneg_left hpow hfac]

lemma fkWeight_hi {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    {e : Sym2 V} (he : e ∈ G.edgeFinset) (ω : ConfigSpace (Sym2 V)) :
    p * fkWeight G p q (setClosed e ω) ≤ q * (1 - p) * fkWeight G p q (setOpen e ω) := by
  unfold fkWeight
  rw [edgeProduct_setOpen G p he, edgeProduct_setClosed G p he]
  set R := edgeRest G p e ω with hR
  set k1 := numClusters G (setOpen e ω)
  set k0 := numClusters G (setClosed e ω)
  have hRpos := edgeRest_pos G hp hp1 e ω
  have hpow : q ^ k0 ≤ q ^ (k1 + 1) :=
    pow_le_pow_right₀ hq (numClusters_setClosed_le_setOpen_succ G e ω)
  rw [pow_succ] at hpow
  have hqp1 : (0 : ℝ) ≤ 1 - p := by linarith
  have hfac : (0 : ℝ) ≤ R * p * (1 - p) := by positivity
  nlinarith [mul_le_mul_of_nonneg_left hpow hfac]

/-!

## C. The single-edge conditional probability

-/

/-- The conditional probability under `φ_{G,p,q}` that `e` is open given the states of all
other edges: `φ(setOpen e ω) / (φ(setOpen e ω) + φ(setClosed e ω))`. -/
noncomputable def condOpen (p q : ℝ) (e : Sym2 V) (ω : ConfigSpace (Sym2 V)) : ℝ :=
  fkProb G p q (setOpen e ω) /
    (fkProb G p q (setOpen e ω) + fkProb G p q (setClosed e ω))

lemma condOpen_eq_weightRatio {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (e : Sym2 V) (ω : ConfigSpace (Sym2 V)) :
    condOpen G p q e ω = fkWeight G p q (setOpen e ω) /
      (fkWeight G p q (setOpen e ω) + fkWeight G p q (setClosed e ω)) := by
  unfold condOpen fkProb
  rw [← add_div]
  exact div_div_div_cancel_right₀ (fkZ_ne_zero G hp hp1 hq) _ _

lemma condOpen_eq_half {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    {e : Sym2 V} (he : e ∉ G.edgeFinset) (ω : ConfigSpace (Sym2 V)) :
    condOpen G p q e ω = 1 / 2 := by
  rw [condOpen_eq_weightRatio G hp hp1 hq]
  have hep : edgeProduct G p (setOpen e ω) = edgeProduct G p (setClosed e ω) := by
    unfold edgeProduct
    apply Finset.prod_congr rfl
    intro e' he'
    have hne : e' ≠ e := fun h => he (h ▸ he')
    rw [setOpen_of_ne hne, setClosed_of_ne hne]
  have hk : numClusters G (setOpen e ω) = numClusters G (setClosed e ω) :=
    numClusters_congr_openSub G (openSub_setOpen_eq_setClosed_of_notMem G he ω)
  have hweq : fkWeight G p q (setOpen e ω) = fkWeight G p q (setClosed e ω) := by
    unfold fkWeight; rw [hep, hk]
  rw [hweq]
  have hpos := fkWeight_pos G hp hp1 hq (setClosed e ω)
  rw [← two_mul, div_eq_div_iff (by positivity) (by norm_num)]
  ring

/-!

## D. The finite-energy bound

-/

/-- The finite-energy constant `min (p / (p + q (1 - p))) (1 - p)`. -/
noncomputable def cFE (p q : ℝ) : ℝ := min (p / (p + q * (1 - p))) (1 - p)

lemma cFE_pos {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q) : 0 < cFE p q := by
  unfold cFE
  apply lt_min
  · apply div_pos hp; nlinarith
  · linarith

lemma cFE_le_half {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q) : cFE p q ≤ 1 / 2 := by
  unfold cFE
  rcases le_or_gt p (1 / 2) with h | h
  · refine le_trans (min_le_left _ _) ?_
    rw [div_le_iff₀ (by nlinarith)]
    nlinarith
  · exact le_trans (min_le_right _ _) (by linarith)

/-- **Finite-energy property** of the random-cluster measure. For `p ∈ (0, 1)` and `q ≥ 1`, the
conditional probability that an edge is open given all other edges lies in
`[cFE p q, 1 - cFE p q]`. For edges of `G` the sharper bounds `p / (p + q (1 - p))` and `p` are
proved along the way. See G. Grimmett, *The Random-Cluster Model* (2006), Chapter 3. -/
theorem finite_energy {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    (e : Sym2 V) (ω : ConfigSpace (Sym2 V)) :
    cFE p q ≤ condOpen G p q e ω ∧ condOpen G p q e ω ≤ 1 - cFE p q := by
  by_cases he : e ∈ G.edgeFinset
  · rw [condOpen_eq_weightRatio G hp hp1 (by linarith)]
    set W1 := fkWeight G p q (setOpen e ω) with hW1
    set W0 := fkWeight G p q (setClosed e ω) with hW0
    have hW1pos : 0 < W1 := fkWeight_pos G hp hp1 (by linarith) _
    have hW0pos : 0 < W0 := fkWeight_pos G hp hp1 (by linarith) _
    have hlo : (1 - p) * W1 ≤ p * W0 := fkWeight_lo G hp hp1 hq he ω
    have hhi : p * W0 ≤ q * (1 - p) * W1 := fkWeight_hi G hp hp1 hq he ω
    have hsum : 0 < W1 + W0 := by linarith
    have hden2 : 0 < p + q * (1 - p) := by nlinarith
    have hub : W1 / (W1 + W0) ≤ p := by rw [div_le_iff₀ hsum]; nlinarith
    have hlb : p / (p + q * (1 - p)) ≤ W1 / (W1 + W0) := by
      rw [div_le_div_iff₀ hden2 hsum]; nlinarith
    refine ⟨le_trans (min_le_left _ _) hlb, ?_⟩
    have hgap : 1 - cFE p q ≥ p := by
      unfold cFE
      have := min_le_right (p / (p + q * (1 - p))) (1 - p)
      linarith
    linarith
  · rw [condOpen_eq_half G hp hp1 (by linarith) he]
    have hc := cFE_le_half hp hp1 hq
    exact ⟨hc, by linarith⟩

end FK

end StatMech

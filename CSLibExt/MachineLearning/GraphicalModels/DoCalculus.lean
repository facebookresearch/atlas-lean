/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.MachineLearning.GraphicalModels.CausalAdjustment
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# The three rules of the do-calculus

Pearl's three rules of the do-calculus (Pearl 1995, Theorem 3; Pearl 2009, Theorem 3.4.1) for a
causal Bayesian network `b : BayesNet α n` (finite state space, nodes in topological order) and
pairwise disjoint sets of nodes `X`, `Y`, `Z`, `W`. All values are read off one assignment `x`,
so an observed value of `Z` equals its intervened value. `P(y | do(x), z, w)` is the ratio
`marginal (b.mutilateSet X x).joint ↑(Y ∪ Z ∪ W) x / marginal (b.mutilateSet X x).joint ↑(Z ∪ W) x`,
and each rule assumes only that the denominators of its two ratios are nonzero. The graph
`G_{\bar X}` (arrows into `X` removed) is the graph of `b.mutilateSet X x`, and `(Y ⫫ Z | X, W)_G`
is d-separation (`BayesNet.DSeparated`).

## Main definitions

* `BayesNet.cutOut b Z z`: the network with the arrows out of `Z` removed (the graph
  `G_{\underline Z}`); only its graph enters the rules (`BayesNet.edge_cutOut_iff`).

## Main results

* `BayesNet.doCalculus_rule1` (insertion or deletion of observations):
  `P(y | do(x), z, w) = P(y | do(x), w)` if `(Y ⫫ Z | X, W)` holds in `G_{\bar X}`.
* `BayesNet.doCalculus_rule2` (action/observation exchange):
  `P(y | do(x), do(z), w) = P(y | do(x), z, w)` if `(Y ⫫ Z | X, W)` holds in
  `G_{\bar X \underline Z}`.
* `BayesNet.doCalculus_rule3` (insertion or deletion of actions):
  `P(y | do(x), do(z), w) = P(y | do(x), w)` if `(Y ⫫ Z | X, W)` holds in
  `G_{\bar X \overline{Z(W)}}`, where `Z(W)` is the set of nodes of `Z` that are not ancestors of
  any node of `W` in `G_{\bar X}`.

## Implementation notes

Rules 1 and 2 apply the global Markov property (`BayesNet.condIndep_of_dSeparated_finset`) to
`b.mutilateSet X x` and to `(b.mutilateSet X x).cutOut Z x`. Rule 3 follows Pearl's proof with an
intervention indicator: no node of `Z(W)` is an ancestor of `Y ∪ W` in `G_{\bar X}`, so
intervening on `Z(W)` leaves the law of `Y ∪ W` unchanged; for the other nodes of `Z`, a network
with one extra root node that switches them between their own tables and the intervention, and
the global Markov property in that network, give the equality without any positivity assumption
beyond the two denominators.

## References

* J. Pearl, *Causal diagrams for empirical research*, Biometrika 82(4) (1995), 669–688,
  Theorem 3.
* J. Pearl, *Causality: Models, Reasoning, and Inference*, 2nd ed., Cambridge University Press
  (2009), Theorem 3.4.1.
-/

@[expose] public section

namespace Cslib.MachineLearning.GraphicalModels

open Finset MetaMathlibExt.FiniteWeight

namespace BayesNet

/-- The network with **the arrows out of `Z` removed** (the graph `G_{\underline Z}` of Pearl
2009, §3.4): each node keeps only its parents outside `Z`, and its table reads every dropped
parent at its fixed value in `z`. Only the graph of this network enters the do-calculus
(`edge_cutOut_iff`); the tables are a concrete choice that keeps it a `BayesNet`. -/
noncomputable def cutOut {α : Type*} {n : ℕ} (b : BayesNet α n) (Z : Finset (Fin n))
    (z : Fin n → α) : BayesNet α n where
  pa j := (b.pa j).filter fun i => Fin.castLE j.2.le i ∉ Z
  cpt j u := b.cpt j fun i =>
    if h : Fin.castLE j.2.le i.1 ∈ Z then z (Fin.castLE j.2.le i.1)
    else u ⟨i.1, Finset.mem_filter.2 ⟨i.2, h⟩⟩

/-- Absorption of the intervened set (a copy of the private lemma
`marginal_mutilateSet_union` of `CausalAdjustment.lean`): under `do(X_W = w)`,
the marginal over `S ∪ W` at an assignment agreeing with `w` on `W` equals the marginal over
`S`. -/
private lemma marginal_mutilateSet_union_absorb {α : Type*} {n : ℕ} [Fintype α] [Nonempty α]
    (b : BayesNet α n)
    (W : Finset (Fin n)) (w : Fin n → α) (S : Finset (Fin n)) {x' : Fin n → α}
    (hx' : ∀ j ∈ W, x' j = w j) :
    marginal (b.mutilateSet W w).joint ((S ∪ W : Finset (Fin n)) : Set (Fin n)) x' =
      marginal (b.mutilateSet W w).joint (S : Set (Fin n)) x' := by
  classical
  simp only [marginal_coe]
  symm
  rw [← sum_filter_of_ne (p := fun x => ∀ j ∈ W, x j = w j), filter_filter]
  · refine sum_congr (filter_congr fun x _ => ?_) fun _ _ => rfl
    simp only [mem_union]
    constructor
    · rintro ⟨h1, h2⟩ i (hi | hi)
      · exact h1 i hi
      · exact (h2 i hi).trans (hx' i hi).symm
    · intro h
      exact ⟨fun i hi => h i (Or.inl hi), fun j hj => (h j (Or.inr hj)).trans (hx' j hj)⟩
  · intro x _ hx j hj
    by_contra hne
    apply hx
    rw [joint_mutilateSet]
    exact prod_eq_zero (mem_univ j) (by simp [hj, hne])

/-- Ratio form of conditional independence with the intervened set absorbed: from
`Y ⫫ Z | T ∪ W'` and absorption of `T`, `P(y | z, w') = P(y | w')`. -/
private theorem condRatio_of_condIndep {α : Type*} [Fintype α] [DecidableEq α] {n : ℕ}
    {P : (Fin n → α) → ℝ} {Y Z W' T : Finset (Fin n)} {x : Fin n → α}
    (hCI : CondIndep P (Y : Set (Fin n)) (Z : Set (Fin n))
      ((T ∪ W' : Finset (Fin n)) : Set (Fin n)))
    (habs : ∀ S : Finset (Fin n),
      marginal P ((S ∪ T : Finset (Fin n)) : Set (Fin n)) x = marginal P (S : Set (Fin n)) x)
    (hzw : marginal P ((Z ∪ W' : Finset (Fin n)) : Set (Fin n)) x ≠ 0)
    (hw : marginal P (W' : Set (Fin n)) x ≠ 0) :
    marginal P ((Y ∪ Z ∪ W' : Finset (Fin n)) : Set (Fin n)) x /
        marginal P ((Z ∪ W' : Finset (Fin n)) : Set (Fin n)) x =
      marginal P ((Y ∪ W' : Finset (Fin n)) : Set (Fin n)) x /
        marginal P (W' : Set (Fin n)) x := by
  have h := hCI x
  have e1 : ((Y : Set (Fin n)) ∪ (Z : Set (Fin n)) ∪ ((T ∪ W' : Finset (Fin n)) : Set (Fin n))) =
      ((((Y ∪ Z ∪ W') ∪ T : Finset (Fin n))) : Set (Fin n)) := by
    ext i
    simp only [Finset.coe_union, Set.mem_union, Finset.mem_coe, Finset.mem_union]
    tauto
  have e2 : (((T ∪ W' : Finset (Fin n))) : Set (Fin n)) =
      (((W' ∪ T : Finset (Fin n))) : Set (Fin n)) := by
    rw [Finset.union_comm T W']
  have e3 : ((Y : Set (Fin n)) ∪ ((T ∪ W' : Finset (Fin n)) : Set (Fin n))) =
      ((((Y ∪ W') ∪ T : Finset (Fin n))) : Set (Fin n)) := by
    ext i
    simp only [Finset.coe_union, Set.mem_union, Finset.mem_coe, Finset.mem_union]
    tauto
  have e4 : ((Z : Set (Fin n)) ∪ ((T ∪ W' : Finset (Fin n)) : Set (Fin n))) =
      ((((Z ∪ W') ∪ T : Finset (Fin n))) : Set (Fin n)) := by
    ext i
    simp only [Finset.coe_union, Set.mem_union, Finset.mem_coe, Finset.mem_union]
    tauto
  rw [e1, e3, e4, e2] at h
  simp only [habs] at h
  rw [div_eq_div_iff hzw hw]
  exact h

/-- For `v` agreeing with `z` on `Z`, the `cutOut` network has the same joint as the original
(children of `Z` read `x` there anyway). -/
private theorem joint_cutOut_eq_of_agree {α : Type*} {n : ℕ} [Fintype α] [Nonempty α]
    (M : BayesNet α n) (Z : Finset (Fin n)) (z v : Fin n → α)
    (hv : ∀ j ∈ Z, v j = z j) : (M.cutOut Z z).joint v = M.joint v := by
  simp only [joint_eq_prod]
  refine prod_congr rfl fun j _ => ?_
  have hfun : (fun i : M.pa j =>
        if h : Fin.castLE j.2.le i.1 ∈ Z then z (Fin.castLE j.2.le i.1)
        else v (Fin.castLE j.2.le i.1)) =
      (fun i : M.pa j => v (Fin.castLE j.2.le i)) := by
    funext i
    by_cases h : Fin.castLE j.2.le i.1 ∈ Z
    · simp only [dif_pos h]
      exact (hv _ h).symm
    · simp only [dif_neg h]
  simp only [cutOut, hfun]

/-- The `cutOut` marginal over a set containing `Z` equals the original marginal. -/
private theorem margCutOut_eq_of_superset {α : Type*} {n : ℕ} [Fintype α] [DecidableEq α]
    [Nonempty α]
    (M : BayesNet α n) (Z : Finset (Fin n)) (z : Fin n → α) (T : Finset (Fin n))
    (hTZ : Z ⊆ T) (x : Fin n → α) (hx : ∀ j ∈ Z, x j = z j) :
    marginal (M.cutOut Z z).joint (T : Set (Fin n)) x =
      marginal M.joint (T : Set (Fin n)) x := by
  simp only [marginal_coe]
  refine sum_congr rfl fun v hv => ?_
  simp only [mem_filter, mem_univ, true_and] at hv
  exact joint_cutOut_eq_of_agree M Z z v (fun j hj => (hv j (hTZ hj)).trans (hx j hj))

/-- The `cutOut` table at `j ∉ X` in a mutilated network: `Z`-parents read at `x`. -/
private theorem cpt_cutOut_mutilate {α : Type*} {n : ℕ} [Fintype α] [Nonempty α] (b : BayesNet α n)
    (X Z : Finset (Fin n)) (x : Fin n → α) (j : Fin n) (hjX : j ∉ X)
    (w : Fin n → α) :
    ((b.mutilateSet X x).cutOut Z x).cpt j (fun j' => w (Fin.castLE j.2.le j')) =
      b.cpt j (fun i : b.pa j => if _ : Fin.castLE j.2.le i.1 ∈ Z then x (Fin.castLE j.2.le i.1)
        else w (Fin.castLE j.2.le i.1)) := by
  simp only [cutOut, mutilateSet, dif_neg hjX]

/-- The `cutOut` table at `j ∈ X` in a mutilated network is the point mass. -/
private theorem cpt_cutOut_mutilate_mem {α : Type*} {n : ℕ} [Fintype α] [Nonempty α]
    (b : BayesNet α n)
    (X Z : Finset (Fin n)) (x : Fin n → α) (j : Fin n) (hjX : j ∈ X)
    (u : ((b.mutilateSet X x).cutOut Z x).pa j → α) :
    ((b.mutilateSet X x).cutOut Z x).cpt j u = Convexity.StdSimplex.single (x j) := by
  simp only [cutOut, mutilateSet, dif_pos hjX]

/-- Summing the `Z`-coordinates against fixed tables gives `1`. -/
private theorem fiber_sum_eq_one {α : Type*} [Fintype α] [DecidableEq α] {n : ℕ}
    (Z : Finset (Fin n))
    (D : Fin n → Convexity.StdSimplex ℝ α) :
    ∑ p ∈ Z.pi (fun _ => (Finset.univ : Finset α)),
      ∏ x ∈ Z.attach, (D x.1).weights (p x.1 x.2) = 1 := by
  have htot : ∀ j ∈ Z, (∑ a ∈ (Finset.univ : Finset α), (D j).weights a) = 1 :=
    fun j _ => Convexity.StdSimplex.total_of_fintype (D j)
  have hps := Finset.prod_sum Z (fun _ => (Finset.univ : Finset α))
    (fun j a => (D j).weights a)
  have hprod : (∏ j ∈ Z, ∑ a ∈ (Finset.univ : Finset α), (D j).weights a) = 1 :=
    Finset.prod_eq_one htot
  calc ∑ p ∈ Z.pi (fun _ => (Finset.univ : Finset α)),
          ∏ x ∈ Z.attach, (D x.1).weights (p x.1 x.2)
      = (∏ j ∈ Z, ∑ a ∈ (Finset.univ : Finset α), (D j).weights a) := hps.symm
    _ = 1 := hprod

/-- Absorption of the intervened set in a `cutOut` network: under `do(X)`, further fixing `X`
does not change the marginal, since the `X`-nodes keep their point-mass tables. -/
private theorem marginal_cutOut_mutilate_absorb {α : Type*} {n : ℕ} [Fintype α] [DecidableEq α]
    [Nonempty α] (b : BayesNet α n) (X Z : Finset (Fin n)) (x : Fin n → α)
    (S : Finset (Fin n)) :
    marginal ((b.mutilateSet X x).cutOut Z x).joint ((S ∪ X : Finset (Fin n)) : Set (Fin n)) x =
      marginal ((b.mutilateSet X x).cutOut Z x).joint (S : Set (Fin n)) x := by
  classical
  simp only [marginal_coe]
  symm
  rw [← sum_filter_of_ne (p := fun x' => ∀ j ∈ X, x' j = x j), filter_filter]
  · refine sum_congr (filter_congr fun x' _ => ?_) fun _ _ => rfl
    simp only [mem_union]
    constructor
    · rintro ⟨h1, h2⟩ i (hi | hi)
      · exact h1 i hi
      · exact h2 i hi
    · intro h
      exact ⟨fun i hi => h i (Or.inl hi), fun j hj => h j (Or.inr hj)⟩
  · intro x' _ hx j hj
    by_contra hne
    apply hx
    rw [joint_eq_prod]
    refine prod_eq_zero (mem_univ j) ?_
    have hcpt : ((b.mutilateSet X x).cutOut Z x).cpt j (fun i => x' (Fin.castLE j.2.le i)) =
        Convexity.StdSimplex.single (x j) :=
      cpt_cutOut_mutilate_mem b X Z x j hj _
    rw [hcpt]
    simp [Convexity.StdSimplex.single, hne]

/-- The fiber sum over `(Z → α)`: summing a product of per-node weights over all `Z`-values
gives `1`, since each table sums to `1`. `F` agrees with the fiber coordinate on `Z`. -/
private theorem fiber_sum_univ {α : Type*} {n : ℕ} [Fintype α] [DecidableEq α] [Nonempty α]
    (Z : Finset (Fin n)) (D : Fin n → Convexity.StdSimplex ℝ α)
    (F : (Z → α) → Fin n → α) (hF : ∀ δ j (hj : j ∈ Z), F δ j = δ ⟨j, hj⟩) :
    ∑ δ ∈ (univ : Finset (Z → α)), ∏ j ∈ Z, (D j).weights (F δ j) = 1 := by
  classical
  revert hF; revert F; revert D
  induction Z using Finset.induction_on with
  | empty =>
    intro D F hF
    have hU : (univ : Finset ((∅ : Finset (Fin n)) → α)) = {fun _ => Classical.arbitrary α} := by
      ext δ
      simp only [mem_univ, mem_singleton]
      exact ⟨fun _ => funext fun z => (notMem_empty z.1 z.2).elim, fun _ => trivial⟩
    rw [hU, Finset.sum_singleton]
    show ∏ j ∈ (∅ : Finset (Fin n)), (D j).weights (F (fun _ => Classical.arbitrary α) j) = 1
    exact Finset.prod_empty
  | insert z Z' hz ih =>
    intro D F hF
    set e' : α × (Z' → α) → (↥(insert z Z') → α) :=
      fun p w => if h : w.1 = z then p.1 else p.2 ⟨w.1, (mem_insert.1 w.2).resolve_left h⟩ with he'
    have he'_pos : ∀ p w (h : w.1 = z), e' p w = p.1 := fun p w h => dif_pos h
    have he'_neg : ∀ p w (h : w.1 ≠ z),
        e' p w = p.2 ⟨w.1, (mem_insert.1 w.2).resolve_left h⟩ :=
      fun p w h => dif_neg h
    have himg' : (univ : Finset (↥(insert z Z') → α)) =
        (univ : Finset (α × (Z' → α))).image e' := by
      ext δ
      simp only [mem_image]
      constructor
      · intro _
        refine ⟨(δ ⟨z, mem_insert_self z Z'⟩, fun w : Z' => δ ⟨w.1, mem_insert_of_mem w.2⟩),
          mem_univ _, ?_⟩
        funext w
        by_cases h : w.1 = z
        · have hwz : w = ⟨z, mem_insert_self z Z'⟩ := Subtype.ext h
          rw [he'_pos _ _ h]
          show δ ⟨z, mem_insert_self z Z'⟩ = δ w
          rw [hwz]
        · exact (he'_neg _ _ h).trans rfl
      · intro _
        exact mem_univ δ
    have hinj' : ∀ p₁ ∈ (univ : Finset (α × (Z' → α))), ∀ p₂ ∈ (univ : Finset (α × (Z' → α))),
        e' p₁ = e' p₂ → p₁ = p₂ := by
      intro p₁ _ p₂ _ h
      obtain ⟨a₁, d₁⟩ := p₁; obtain ⟨a₂, d₂⟩ := p₂
      have h1 : a₁ = a₂ := by
        have hcon := congrFun h ⟨z, mem_insert_self z Z'⟩
        rw [he'_pos _ ⟨z, mem_insert_self z Z'⟩ rfl,
          he'_pos _ ⟨z, mem_insert_self z Z'⟩ rfl] at hcon
        exact hcon
      have h2 : d₁ = d₂ := by
        funext w
        have hne : w.1 ≠ z := fun he => hz (he ▸ w.2)
        have hcon := congrFun h ⟨w.1, mem_insert_of_mem w.2⟩
        rw [he'_neg _ _ hne, he'_neg _ _ hne] at hcon
        exact hcon
      rw [h1, h2]
    rw [himg', Finset.sum_image hinj']
    simp only [Fintype.sum_prod_type]
    have hsplit2 : ∀ a d, ∏ j ∈ insert z Z', (D j).weights (F (e' (a, d)) j) =
        (D z).weights a * ∏ j ∈ Z', (D j).weights (F (e' (a, d)) j) := by
      intro a d
      simp only [prod_insert hz]
      congr 1
      congr 1
      rw [hF _ _ (mem_insert_self z Z')]
      exact he'_pos (a, d) ⟨z, mem_insert_self z Z'⟩ rfl
    have hF' : ∀ a d j (hj : j ∈ Z'), (fun d j => F (e' (a, d)) j) d j = d ⟨j, hj⟩ := by
      intro a d j hj
      show F (e' (a, d)) j = d ⟨j, hj⟩
      rw [hF _ _ (mem_insert_of_mem hj)]
      have hne : j ≠ z := fun he => hz (he ▸ hj)
      exact (he'_neg _ _ hne).trans rfl
    have hIH : ∀ a, ∑ d ∈ univ, ∏ j ∈ Z', (D j).weights (F (e' (a, d)) j) = 1 :=
      fun a => ih D (fun d j => F (e' (a, d)) j) (hF' a)
    simp only [hsplit2, ← mul_sum, hIH, mul_one]
    exact Convexity.StdSimplex.total_of_fintype (D z)

/-- Summing out the `Z`-coordinates of the `cutOut` joint gives the `do(X ∪ Z)` marginal on
sets disjoint from `Z`: the `Z`-factors sum to `1` and the rest match the intervened tables. -/
private theorem marginal_cutOut_eq_mutilate {α : Type*} {n : ℕ} [Fintype α] [DecidableEq α]
    [Nonempty α] (b : BayesNet α n) {X Z : Finset (Fin n)} (x : Fin n → α)
    (hXZ : Disjoint X Z) {S : Finset (Fin n)} (hSZ : Disjoint S Z) :
    marginal ((b.mutilateSet X x).cutOut Z x).joint (S : Set (Fin n)) x =
      marginal (b.mutilateSet (X ∪ Z) x).joint (S : Set (Fin n)) x := by
  classical
  rw [← marginal_cutOut_mutilate_absorb b X Z x S]
  rw [← marginal_mutilateSet_union_absorb b (X ∪ Z) x S (fun _ _ => rfl)]
  simp only [marginal_coe]
  set M : BayesNet α n := b.mutilateSet X x with hM
  set N : BayesNet α n := M.cutOut Z x with hN
  set P : BayesNet α n := b.mutilateSet (X ∪ Z) x with hP
  set g : (Fin n → α) → (Fin n → α) := fun v j => if j ∈ Z then x j else v j with hg
  have hg_pos : ∀ v j (hj : j ∈ Z), g v j = x j := fun v j hj => dif_pos hj
  have hg_neg : ∀ v j (hj : j ∉ Z), g v j = v j := fun v j hj => dif_neg hj
  have hSXZ : ∀ j ∈ S ∪ X, j ∉ Z := fun j hj hJZ => (mem_union.1 hj).elim
    (fun hjS => disjoint_left.1 hSZ hjS hJZ) (fun hjX => disjoint_left.1 hXZ hjX hJZ)
  have hmemSX : ∀ j ∈ S ∪ X, j ∈ S ∪ (X ∪ Z) := fun j hj => (mem_union.1 hj).elim
    (fun hjS => mem_union_left _ hjS) (fun hjX => mem_union_right _ (mem_union_left _ hjX))
  have himg : (univ.filter (fun v : Fin n → α => ∀ i ∈ S ∪ X, v i = x i)).image g =
      univ.filter (fun v₀ : Fin n → α => ∀ i ∈ S ∪ (X ∪ Z), v₀ i = x i) := by
    ext v₀
    simp only [mem_image, mem_filter]
    constructor
    · rintro ⟨v, ⟨-, hv⟩, rfl⟩
      refine ⟨mem_univ _, ?_⟩
      intro j hj
      by_cases hjZ : j ∈ Z
      · rw [hg_pos _ _ hjZ]
      · rw [hg_neg _ _ hjZ]
        exact hv j ((mem_union.1 hj).elim (fun hjS => mem_union_left _ hjS)
          (fun hjXZ => (mem_union.1 hjXZ).elim (fun hjX => mem_union_right _ hjX)
            (fun hjZ' => absurd hjZ' hjZ)))
    · intro hmem
      obtain ⟨-, hag⟩ := hmem
      refine ⟨v₀, ⟨mem_univ _, fun j hj => hag j (hmemSX j hj)⟩, ?_⟩
      funext j
      by_cases hjZ : j ∈ Z
      · rw [hg_pos _ _ hjZ]
        exact (hag j (mem_union_right _ (mem_union_right _ hjZ))).symm
      · rw [hg_neg _ _ hjZ]
  have hmaps : ∀ v ∈ univ.filter (fun v : Fin n → α => ∀ i ∈ S ∪ X, v i = x i),
      g v ∈ univ.filter (fun v₀ : Fin n → α => ∀ i ∈ S ∪ (X ∪ Z), v₀ i = x i) := by
    intro v hv
    rw [← himg]
    exact Finset.mem_image_of_mem g hv
  rw [← Finset.sum_fiberwise_of_maps_to hmaps N.joint]
  refine sum_congr rfl fun v₀ hv₀ => ?_
  have hv₀agree : ∀ i ∈ S ∪ (X ∪ Z), v₀ i = x i := (mem_filter.1 hv₀).2
  have hv₀SX : ∀ j ∈ S ∪ X, v₀ j = x j := fun j hj => hv₀agree j (hmemSX j hj)
  have hv₀Z : ∀ j ∈ Z, v₀ j = x j :=
    fun j hjZ => hv₀agree j (mem_union_right _ (mem_union_right _ hjZ))
  set e : (Z → α) → (Fin n → α) := fun δ j => if h : j ∈ Z then δ ⟨j, h⟩ else v₀ j with he
  have he_pos : ∀ δ j (hj : j ∈ Z), e δ j = δ ⟨j, hj⟩ := fun δ j hj => dif_pos hj
  have he_neg : ∀ δ j (hj : j ∉ Z), e δ j = v₀ j := fun δ j hj => dif_neg hj
  simp only [filter_filter]
  have hfibeq : univ.filter (fun v : Fin n → α => (∀ i ∈ S ∪ X, v i = x i) ∧ g v = v₀) =
      univ.image e := by
    ext v
    simp only [mem_filter, mem_image]
    constructor
    · rintro ⟨-, hag, hpr⟩
      refine ⟨fun z : Z => v z.1, mem_univ _, ?_⟩
      funext j
      by_cases hjZ : j ∈ Z
      · exact (he_pos (fun z : Z => v z.1) j hjZ).trans rfl
      · rw [he_neg (fun z : Z => v z.1) j hjZ]
        have hprj : v j = v₀ j := by
          rw [← hg_neg v j hjZ]
          exact congrFun hpr j
        exact hprj.symm
    · rintro ⟨δ, _, rfl⟩
      refine ⟨mem_univ _, ?_, ?_⟩
      · intro j hjSX
        rw [he_neg _ _ (hSXZ j hjSX)]
        exact hv₀SX j hjSX
      · funext j
        by_cases hjZ : j ∈ Z
        · rw [hg_pos _ _ hjZ]
          exact (hv₀Z j hjZ).symm
        · rw [hg_neg _ _ hjZ, he_neg _ _ hjZ]
  have hinj : ∀ d₁ ∈ (univ : Finset (Z → α)), ∀ d₂ ∈ (univ : Finset (Z → α)),
      e d₁ = e d₂ → d₁ = d₂ := by
    intro δ₁ _ δ₂ _ h
    funext z
    have h12 := congrFun h z.1
    rw [he_pos _ _ z.2, he_pos _ _ z.2] at h12
    exact h12
  rw [hfibeq, Finset.sum_image hinj]
  conv_lhs => arg 2; ext x; rw [N.joint_eq_prod (e x)]
  have hpaE : ∀ δ k, (fun j : N.pa k => (e δ) (Fin.castLE k.2.le j)) = N.paVal k v₀ := by
    intro δ k
    funext i
    have hflt : i.1 ∈ (M.pa k).filter (fun i => Fin.castLE k.2.le i ∉ Z) := i.2
    have hmem : Fin.castLE k.2.le i.1 ∉ Z := (mem_filter.1 hflt).2
    show (e δ) (Fin.castLE k.2.le i.1) = v₀ (Fin.castLE k.2.le i.1)
    rw [he_neg _ _ hmem]
  have hsum : (∑ δ ∈ univ, ∏ k, (N.cpt k
      (fun j : N.pa k => (e δ) (Fin.castLE k.2.le j))).weights ((e δ) k)) =
      (∑ δ ∈ univ, ∏ k, (N.cpt k (N.paVal k v₀)).weights ((e δ) k)) :=
    Finset.sum_congr rfl fun δ _ => Finset.prod_congr rfl fun k _ => by rw [hpaE δ k]
  rw [hsum]
  have hunion : Z ∪ (univ \ Z) = univ := by
    ext j
    simp only [mem_union, mem_sdiff, mem_univ, true_and, iff_true_intro (em (j ∈ Z))]
  have hdisj : Disjoint Z (univ \ Z) :=
    disjoint_left.2 fun j hjZ hjSD => (mem_sdiff.1 hjSD).2 hjZ
  have hsplit : ∀ K : Fin n → ℝ, (∏ k ∈ univ, K k) =
      (∏ k ∈ Z, K k) * (∏ k ∈ univ \ Z, K k) := by
    intro K
    conv_lhs => rw [← hunion]
    rw [prod_union hdisj]
  simp only [hsplit]
  have hnonZ : ∀ δ k (hk : k ∉ Z),
      (N.cpt k (N.paVal k v₀)).weights ((e δ) k) =
        (N.cpt k (N.paVal k v₀)).weights (v₀ k) := fun δ k hk => by rw [he_neg δ k hk]
  have hδfree : ∀ δ, (∏ k ∈ Z, (N.cpt k (N.paVal k v₀)).weights ((e δ) k)) *
      (∏ k ∈ univ \ Z, (N.cpt k (N.paVal k v₀)).weights ((e δ) k)) =
      (∏ k ∈ Z, (N.cpt k (N.paVal k v₀)).weights ((e δ) k)) *
      (∏ k ∈ univ \ Z, (N.cpt k (N.paVal k v₀)).weights (v₀ k)) := by
    intro δ
    congr 1
    exact prod_congr rfl fun k hk => hnonZ δ k (mem_sdiff.1 hk).2
  simp only [hδfree]
  rw [← sum_mul]
  have hfib : ∑ δ ∈ univ, ∏ k ∈ Z, (N.cpt k (N.paVal k v₀)).weights ((e δ) k) = 1 :=
    fiber_sum_univ Z (fun k => N.cpt k (N.paVal k v₀)) e (fun δ k hk => he_pos δ k hk)
  rw [hfib, one_mul]
  have htable : ∀ k (hk : k ∉ X ∪ Z),
      N.cpt k (N.paVal k v₀) = b.cpt k (b.paVal k v₀) := by
    intro k hkXZ
    have hkX : k ∉ X := fun hX => hkXZ (mem_union_left _ hX)
    have hpa : N.paVal k v₀ = (fun j' : N.pa k => v₀ (Fin.castLE k.2.le j')) := rfl
    have hN' : N.cpt k (fun j' : N.pa k => v₀ (Fin.castLE k.2.le j')) =
        b.cpt k (fun i => if _ : Fin.castLE k.2.le i.1 ∈ Z then x (Fin.castLE k.2.le i.1)
          else v₀ (Fin.castLE k.2.le i.1)) :=
      cpt_cutOut_mutilate b X Z x k hkX v₀
    have hfun : (fun i => if _ : Fin.castLE k.2.le i.1 ∈ Z then x (Fin.castLE k.2.le i.1)
          else v₀ (Fin.castLE k.2.le i.1)) = b.paVal k v₀ := by
      funext i
      by_cases h : Fin.castLE k.2.le i.1 ∈ Z
      · simp only [dif_pos h]; exact (hv₀Z _ h).symm
      · simp only [dif_neg h]; exact rfl
    rw [hpa, hN', hfun]
  have hFG : ∀ k (hk : k ∉ X ∪ Z),
      (N.cpt k (N.paVal k v₀)).weights (v₀ k) =
        (b.cpt k (b.paVal k v₀)).weights (v₀ k) := fun k hk => by rw [htable k hk]
  have hNC : (∏ k ∈ univ \ Z, (N.cpt k (N.paVal k v₀)).weights (v₀ k)) =
      ∏ k ∈ univ.filter (fun k => k ∉ X ∪ Z),
        (N.cpt k (N.paVal k v₀)).weights (v₀ k) := by
    symm
    refine Finset.prod_subset ?_ ?_
    · intro k hk
      exact mem_sdiff.2 ⟨mem_univ k, fun hZ => (mem_filter.1 hk).2 (mem_union_right _ hZ)⟩
    · intro k hkUD hnf
      have hkXZ : k ∈ X ∪ Z := by
        by_contra hC
        exact hnf (mem_filter.2 ⟨mem_univ k, hC⟩)
      have hkX : k ∈ X := (mem_union.1 hkXZ).resolve_right (mem_sdiff.1 hkUD).2
      have hcpt1 : N.cpt k (N.paVal k v₀) = Convexity.StdSimplex.single (x k) :=
        cpt_cutOut_mutilate_mem b X Z x k hkX _
      rw [hcpt1]
      have hag : v₀ k = x k := hv₀SX k (mem_union_right _ hkX)
      rw [hag]
      simp [Convexity.StdSimplex.single]
  have hPJ : P.joint v₀ = ∏ j, (if j ∈ X ∪ Z then (if v₀ j = x j then 1 else 0)
      else (b.cpt j (b.paVal j v₀)).weights (v₀ j)) :=
    joint_mutilateSet b (X ∪ Z) x v₀
  have hPside : P.joint v₀ = ∏ k ∈ univ.filter (fun k => k ∉ X ∪ Z),
      (b.cpt k (b.paVal k v₀)).weights (v₀ k) := by
    rw [hPJ]
    have hsubP : univ.filter (fun k => k ∉ X ∪ Z) ⊆ univ := subset_univ _
    have hfP : ∀ j ∈ univ, j ∉ univ.filter (fun k => k ∉ X ∪ Z) →
        (if j ∈ X ∪ Z then (if v₀ j = x j then 1 else 0)
          else (b.cpt j (b.paVal j v₀)).weights (v₀ j)) = 1 := by
      intro j _ hnf
      have hjXZ : j ∈ X ∪ Z := by
        by_contra hC
        exact hnf (mem_filter.2 ⟨mem_univ j, hC⟩)
      have hag : v₀ j = x j := hv₀agree j (mem_union_right _ hjXZ)
      simp only [if_pos hjXZ, if_pos hag]
    rw [(Finset.prod_subset hsubP hfP).symm]
    refine prod_congr rfl fun j hj => ?_
    rw [if_neg (mem_filter.1 hj).2]
  have hNZ : (∏ k ∈ univ \ Z, (N.cpt k (N.paVal k v₀)).weights (v₀ k)) = P.joint v₀ := by
    rw [hNC]
    exact (prod_congr rfl fun k hk => hFG k (mem_filter.1 hk).2).trans hPside.symm
  exact hNZ

/-- The arrows of `b.cutOut Z z` are those of `b` not leaving `Z`. -/
theorem edge_cutOut_iff {α : Type*} {n : ℕ} (b : BayesNet α n) (Z : Finset (Fin n))
    (z : Fin n → α) {i j : Fin n} :
    (b.cutOut Z z).Edge i j ↔ b.Edge i j ∧ i ∉ Z := by
  have hcast : ∀ h : i.val < j.val, Fin.castLE j.2.le (⟨i.val, h⟩ : Fin j) = i :=
    fun h => Fin.ext rfl
  simp only [Edge, cutOut, Finset.mem_filter]
  constructor
  · rintro ⟨h, hmem, hnot⟩
    have hnot' : Fin.castLE j.2.le (⟨i.val, h⟩ : Fin j) ∉ Z := hnot
    rw [hcast h] at hnot'
    exact ⟨⟨h, hmem⟩, hnot'⟩
  · rintro ⟨⟨h, hmem⟩, hiZ⟩
    refine ⟨h, hmem, ?_⟩
    show Fin.castLE j.2.le (⟨i.val, h⟩ : Fin j) ∉ Z
    rw [hcast h]
    exact hiZ

/-- **Rule 1 of the do-calculus** (insertion/deletion of observations; Pearl 1995, Theorem 3;
Pearl 2009, Theorem 3.4.1): if `Y` and `Z` are d-separated by `X ∪ W` in `G_{\bar X}` (the
graph of `b.mutilateSet X x`), then `P(y | do(x), z, w) = P(y | do(x), w)`, wherever both
conditional probabilities are defined. All values are read off the single assignment `x`. -/
theorem doCalculus_rule1 {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α] {n : ℕ}
    (b : BayesNet α n) {X Y Z W : Finset (Fin n)} (x : Fin n → α)
    (hXY : Disjoint X Y) (hXZ : Disjoint X Z) (hXW : Disjoint X W) (hYZ : Disjoint Y Z)
    (hYW : Disjoint Y W) (hZW : Disjoint Z W)
    (hd : (b.mutilateSet X x).DSeparated (Y : Set (Fin n)) (Z : Set (Fin n))
      ((X ∪ W : Finset (Fin n)) : Set (Fin n)))
    (hzw : marginal (b.mutilateSet X x).joint ((Z ∪ W : Finset (Fin n)) : Set (Fin n)) x ≠ 0)
    (hw : marginal (b.mutilateSet X x).joint (W : Set (Fin n)) x ≠ 0) :
    marginal (b.mutilateSet X x).joint ((Y ∪ Z ∪ W : Finset (Fin n)) : Set (Fin n)) x /
        marginal (b.mutilateSet X x).joint ((Z ∪ W : Finset (Fin n)) : Set (Fin n)) x =
      marginal (b.mutilateSet X x).joint ((Y ∪ W : Finset (Fin n)) : Set (Fin n)) x /
        marginal (b.mutilateSet X x).joint (W : Set (Fin n)) x := by
  have hCI : CondIndep (b.mutilateSet X x).joint (Y : Set (Fin n)) (Z : Set (Fin n))
      ((X ∪ W : Finset (Fin n)) : Set (Fin n)) :=
    (b.mutilateSet X x).condIndep_of_dSeparated_finset hd
  have habs : ∀ S : Finset (Fin n),
      marginal (b.mutilateSet X x).joint ((S ∪ X : Finset (Fin n)) : Set (Fin n)) x =
        marginal (b.mutilateSet X x).joint (S : Set (Fin n)) x :=
    fun S => marginal_mutilateSet_union_absorb b X x S (fun _ _ => rfl)
  exact condRatio_of_condIndep hCI habs hzw hw

/-- **Rule 2 of the do-calculus** (action/observation exchange; Pearl 1995, Theorem 3; Pearl
2009, Theorem 3.4.1): if `Y` and `Z` are d-separated by `X ∪ W` in `G_{\bar X \underline Z}`
(the graph of `(b.mutilateSet X x).cutOut Z x`), then
`P(y | do(x), do(z), w) = P(y | do(x), z, w)`, wherever both conditional probabilities are
defined. -/
theorem doCalculus_rule2 {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α] {n : ℕ}
    (b : BayesNet α n) {X Y Z W : Finset (Fin n)} (x : Fin n → α)
    (hXY : Disjoint X Y) (hXZ : Disjoint X Z) (hXW : Disjoint X W) (hYZ : Disjoint Y Z)
    (hYW : Disjoint Y W) (hZW : Disjoint Z W)
    (hd : ((b.mutilateSet X x).cutOut Z x).DSeparated (Y : Set (Fin n)) (Z : Set (Fin n))
      ((X ∪ W : Finset (Fin n)) : Set (Fin n)))
    (hw : marginal (b.mutilateSet (X ∪ Z) x).joint (W : Set (Fin n)) x ≠ 0)
    (hzw : marginal (b.mutilateSet X x).joint ((Z ∪ W : Finset (Fin n)) : Set (Fin n)) x ≠ 0) :
    marginal (b.mutilateSet (X ∪ Z) x).joint ((Y ∪ W : Finset (Fin n)) : Set (Fin n)) x /
        marginal (b.mutilateSet (X ∪ Z) x).joint (W : Set (Fin n)) x =
      marginal (b.mutilateSet X x).joint ((Y ∪ Z ∪ W : Finset (Fin n)) : Set (Fin n)) x /
        marginal (b.mutilateSet X x).joint ((Z ∪ W : Finset (Fin n)) : Set (Fin n)) x := by
  classical
  set M : BayesNet α n := b.mutilateSet X x with hM
  set N : BayesNet α n := M.cutOut Z x with hN
  set P : BayesNet α n := b.mutilateSet (X ∪ Z) x with hP
  have hCI : CondIndep N.joint (Y : Set (Fin n)) (Z : Set (Fin n))
      ((X ∪ W : Finset (Fin n)) : Set (Fin n)) :=
    N.condIndep_of_dSeparated_finset hd
  have habs : ∀ S : Finset (Fin n),
      marginal N.joint ((S ∪ X : Finset (Fin n)) : Set (Fin n)) x =
        marginal N.joint (S : Set (Fin n)) x :=
    fun S => marginal_cutOut_mutilate_absorb b X Z x S
  have hYWZ : Disjoint (Y ∪ W) Z :=
    disjoint_left.2 fun a ha haZ => (mem_union.1 ha).elim
      (fun haY => disjoint_left.1 hYZ haY haZ) (fun haW => disjoint_left.1 hZW haZ haW)
  have c1 : marginal N.joint ((Y ∪ Z ∪ W : Finset (Fin n)) : Set (Fin n)) x =
      marginal M.joint ((Y ∪ Z ∪ W : Finset (Fin n)) : Set (Fin n)) x :=
    margCutOut_eq_of_superset M Z x (Y ∪ Z ∪ W)
      (fun j hj => mem_union_left _ (mem_union_right _ hj)) x (fun _ _ => rfl)
  have c2 : marginal N.joint ((Z ∪ W : Finset (Fin n)) : Set (Fin n)) x =
      marginal M.joint ((Z ∪ W : Finset (Fin n)) : Set (Fin n)) x :=
    margCutOut_eq_of_superset M Z x (Z ∪ W)
      (fun j hj => mem_union_left _ hj) x (fun _ _ => rfl)
  have c3 : marginal N.joint ((Y ∪ W : Finset (Fin n)) : Set (Fin n)) x =
      marginal P.joint ((Y ∪ W : Finset (Fin n)) : Set (Fin n)) x :=
    marginal_cutOut_eq_mutilate b x hXZ hYWZ
  have c4 : marginal N.joint (W : Set (Fin n)) x =
      marginal P.joint (W : Set (Fin n)) x :=
    marginal_cutOut_eq_mutilate b x hXZ hZW.symm
  have hzw' : marginal N.joint ((Z ∪ W : Finset (Fin n)) : Set (Fin n)) x ≠ 0 := by
    rw [c2]; exact hzw
  have hw' : marginal N.joint (W : Set (Fin n)) x ≠ 0 := by
    rw [c4]; exact hw
  rw [← c3, ← c4, ← c1, ← c2]
  exact (condRatio_of_condIndep hCI habs hzw' hw').symm

/-! ### Rule 3 helpers -/

/-- A strengthened copy of the private lemma `exists_isChain_of_reflTransGen` of
`CausalAdjustment.lean`: every node after the first has an incoming `r`-edge and is reachable
from `a`. -/
private lemma exists_isChain_of_reflTransGen_r3 {n : ℕ} {r : Fin n → Fin n → Prop}
    {a c : Fin n} (h : Relation.ReflTransGen r a c) :
    ∃ l : List (Fin n), (a :: l).IsChain r ∧ (a :: l).getLast? = some c ∧
      ∀ y ∈ l, (∃ u, r u y) ∧ Relation.ReflTransGen r a y := by
  induction h with
  | refl => exact ⟨[], .singleton _, rfl, fun y hy => by cases hy⟩
  | @tail b' c' hab hbc ih =>
    obtain ⟨l, h1, h2, h3⟩ := ih
    refine ⟨l ++ [c'], ?_, ?_, ?_⟩
    · rw [← List.cons_append]
      refine h1.append (.singleton _) fun x hx y hy => ?_
      rw [h2] at hx
      simp only [Option.mem_def, Option.some.injEq, List.head?_cons] at hx hy
      subst hx hy
      exact hbc
    · rw [show a :: (l ++ [c']) = (a :: l) ++ [c'] from rfl, List.getLast?_append]
      simp
    · intro y hy
      rcases List.mem_append.1 hy with hy | hy
      · exact h3 y hy
      · rw [List.mem_singleton] at hy
        exact ⟨⟨b', hy ▸ hbc⟩, hy ▸ hab.tail hbc⟩

/-- A directed path whose nodes after the first avoid `C` is a path not blocked by `C`. -/
private lemma exists_path_not_blocked_r3 {α : Type*} {n : ℕ} (B : BayesNet α n)
    {C : Set (Fin n)} {z t : Fin n} (h : B.IsDescendant z t)
    (hC : ∀ d, B.IsDescendant z d → d ≠ z → d ∉ C) :
    ∃ p, B.IsPath z t p ∧ ¬B.PathBlocked C p := by
  obtain ⟨l, hchain, hlast, hreach⟩ := exists_isChain_of_reflTransGen_r3 h
  have hlt : (z :: l).IsChain (· < ·) := hchain.imp fun u v huv => Fin.lt_def.2 huv.1
  have hnd : (z :: l).Nodup := (List.isChain_iff_pairwise.1 hlt).imp ne_of_lt
  refine ⟨z :: l, ⟨hnd, hchain.imp (fun _ _ e => Or.inl e), rfl, hlast⟩, ?_⟩
  rintro ⟨i, hi, hb⟩
  rcases hb with ⟨e1, e2, -⟩ | ⟨-, hm⟩
  · have hch := List.isChain_iff_getElem.1 hchain (i + 1) (by omega)
    exact absurd (e2.1.trans hch.1) (lt_irrefl _)
  · have hmem : (z :: l)[i + 1]'(by omega) ∈ l := by
      have hall : (z :: l)[i + 1]'(by omega) ∈ z :: l :=
        List.mem_iff_getElem.2 ⟨i + 1, by omega, rfl⟩
      rcases List.mem_cons.1 hall with heq | hmem
      · have h0 : (z :: l)[0]'(by simp) = z := rfl
        have hcon : (0 : ℕ) = i + 1 := hnd.getElem_inj_iff.1 (h0.trans heq.symm)
        omega
      · exact hmem
    obtain ⟨-, hdesc⟩ := hreach _ hmem
    have hne : (z :: l)[i + 1]'(by omega) ≠ z := by
      intro heq
      have h0 : (z :: l)[0]'(by simp) = z := rfl
      have hcon : (0 : ℕ) = i + 1 := hnd.getElem_inj_iff.1 (h0.trans heq.symm)
      omega
    exact (hC _ hdesc hne) hm

/-- Step 1 of rule 3: no node of `ZW` is an ancestor, in `G_{bar X}`, of a node of `Y ∪ W`. -/
private lemma not_isDescendant_rule3_r3 {α : Type*} [Nonempty α] {n : ℕ} (b : BayesNet α n)
    {X Y Z W ZW : Finset (Fin n)} (x : Fin n → α)
    (hZWdef : ∀ z, z ∈ ZW ↔ z ∈ Z ∧ ∀ w ∈ W, ¬(b.mutilateSet X x).IsDescendant z w)
    (hd : (b.mutilateSet (X ∪ ZW) x).DSeparated (Y : Set (Fin n)) (Z : Set (Fin n))
      ((X ∪ W : Finset (Fin n)) : Set (Fin n))) :
    ∀ z ∈ ZW, ∀ t ∈ Y ∪ W, ¬(b.mutilateSet X x).IsDescendant z t := by
  have key : ∀ z ∈ ZW, ∀ c, (b.mutilateSet X x).IsDescendant z c →
      ∃ z' ∈ ZW, (b.mutilateSet (X ∪ ZW) x).IsDescendant z' c := by
    intro z hz c hdesc
    unfold IsDescendant at hdesc
    induction hdesc with
    | refl => exact ⟨z, hz, .refl⟩
    | @tail m c _ e ih =>
      by_cases hc : c ∈ ZW
      · exact ⟨c, hc, .refl⟩
      · obtain ⟨z', hz', hM⟩ := ih
        have he : b.Edge m c ∧ c ∉ X := (b.edge_mutilateSet_iff X x).1 e
        have hcX : c ∉ X ∪ ZW := by
          intro hcon
          rcases mem_union.1 hcon with hX | hZW
          · exact he.2 hX
          · exact hc hZW
        exact ⟨z', hz', Relation.ReflTransGen.tail hM
          ((b.edge_mutilateSet_iff (X ∪ ZW) x).2 ⟨he.1, hcX⟩)⟩
  intro z hz t ht hdesc
  rcases mem_union.1 ht with htY | htW
  · obtain ⟨z', hz', hM⟩ := key z hz t hdesc
    have hz'Z : z' ∈ Z := ((hZWdef z').1 hz').1
    have hz'W : ∀ w ∈ W, ¬(b.mutilateSet X x).IsDescendant z' w :=
      ((hZWdef z').1 hz').2
    have hC : ∀ d, (b.mutilateSet (X ∪ ZW) x).IsDescendant z' d → d ≠ z' →
        d ∉ ((X ∪ W : Finset (Fin n)) : Set (Fin n)) := by
      intro d hdescM hne
      rcases Relation.ReflTransGen.cases_tail hdescM with hzz | ⟨u, -, e⟩
      · exact absurd hzz hne
      · have hdXW : d ∉ X ∪ ZW := ((b.edge_mutilateSet_iff (X ∪ ZW) x).1 e).2
        have hdX : d ∉ X := fun hX => hdXW (mem_union_left ZW hX)
        have hdW : d ∉ W := by
          intro hdW
          have hmono : (b.mutilateSet (X ∪ ZW) x).Edge ≤ (b.mutilateSet X x).Edge := by
            intro u v huv
            have huv' := (b.edge_mutilateSet_iff (X ∪ ZW) x).1 huv
            exact (b.edge_mutilateSet_iff X x).2 ⟨huv'.1,
              fun hvX => huv'.2 (mem_union_left ZW hvX)⟩
          have hG : (b.mutilateSet X x).IsDescendant z' d :=
            Relation.ReflTransGen.mono hmono _ _ hdescM
          exact hz'W d hdW hG
        simp [hdX, hdW]
    obtain ⟨p, hpath, hnblock⟩ :=
      exists_path_not_blocked_r3 (b.mutilateSet (X ∪ ZW) x) hM hC
    exact hnblock (DSeparated.symm _ hd z' (mem_coe.2 hz'Z) t (mem_coe.2 htY) p hpath)
  · exact ((hZWdef z).1 hz).2 t htW hdesc

/-- Copy of the private lemma `marginal_eq_of_tables` of `CausalAdjustment.lean`. -/
private lemma marginal_eq_of_tables_r3 {α : Type*} [Nonempty α] [Fintype α] {n : ℕ}
    (b b' : BayesNet α n) {N : Finset (Fin n)} (hN : b.IsAncestral N)
    (hN' : b'.IsAncestral N)
    (htab : ∀ j ∈ N, ∀ x, (b.cpt j (b.paVal j x)).weights (x j) =
      (b'.cpt j (b'.paVal j x)).weights (x j))
    {S : Finset (Fin n)} (hS : S ⊆ N) (x' : Fin n → α) :
    marginal b.joint ↑S x' = marginal b'.joint ↑S x' := by
  classical
  rw [marginal_joint_eq_ancProd b hN hS, marginal_joint_eq_ancProd b' hN' hS]
  congr 1
  funext x
  refine prod_congr rfl fun j _ => ?_
  split_ifs with hj
  · exact htab j hj x
  · rfl

/-- Intervening on `T` does not change the law of a set `S` containing no descendant of `T`. -/
private lemma marginal_mutilateSet_of_not_isDescendant_r3 {α : Type*} [Nonempty α]
    [Fintype α] {n : ℕ} (B : BayesNet α n) (T S : Finset (Fin n)) (w : Fin n → α)
    (hS : ∀ t ∈ T, ∀ s ∈ S, ¬B.IsDescendant t s) (x' : Fin n → α) :
    marginal (B.mutilateSet T w).joint ↑S x' = marginal B.joint ↑S x' := by
  classical
  set N := univ.filter (fun j => ∀ t ∈ T, ¬B.IsDescendant t j) with hNdef
  have hN : B.IsAncestral N := by
    intro i j hE hj
    simp only [hNdef, mem_filter, mem_univ, true_and] at hj ⊢
    intro t ht hdesc
    exact hj t ht (Relation.ReflTransGen.tail hdesc hE)
  have hN' : (B.mutilateSet T w).IsAncestral N := by
    intro i j hE hj
    refine hN ?_ hj
    exact ((B.edge_mutilateSet_iff T w).1 hE).1
  refine marginal_eq_of_tables_r3 (B.mutilateSet T w) B hN' hN (fun j hj x => ?_)
    (fun s hs => mem_filter.2 ⟨mem_univ _, fun t ht => hS t ht s hs⟩) x'
  have hjT : j ∉ T := by
    intro hjT
    have hj' : ∀ t ∈ T, ¬B.IsDescendant t j := (mem_filter.1 hj).2
    exact hj' j hjT Relation.ReflTransGen.refl
  simp only [mutilateSet, hjT, dite_false]
  rfl

/-- Two interventions with the same values compose. -/
private lemma joint_mutilateSet_mutilateSet_r3 {α : Type*} [Nonempty α] {n : ℕ}
    (B : BayesNet α n) (A A' : Finset (Fin n)) (w : Fin n → α) :
    ((B.mutilateSet A w).mutilateSet A' w).joint = (B.mutilateSet (A ∪ A') w).joint := by
  classical
  funext v
  rw [joint_mutilateSet, joint_mutilateSet]
  refine Finset.prod_congr rfl fun j _ => ?_
  by_cases hj' : j ∈ A'
  · have hmem : j ∈ A ∪ A' := mem_union_right A hj'
    rw [ite_eq_left hj', ite_eq_left hmem]
  · by_cases hj : j ∈ A
    · have hmem : j ∈ A ∪ A' := mem_union_left A' hj
      rw [ite_eq_right hj', ite_eq_left hmem]
      simp only [mutilateSet, hj, dite_true]
      rw [Convexity.StdSimplex.weights_single]
      by_cases hvv : v j = w j
      · simp [hvv]
      · simp [hvv]
    · have hmem : j ∉ A ∪ A' := by simp [hj, hj']
      rw [ite_eq_right hj', ite_eq_right hmem]
      simp only [mutilateSet, hj, dite_false]
      rfl

/-- A list of nonzero elements of `Fin (n + 1)` is the image of a list under `Fin.succ`. -/
private lemma exists_eq_map_succ_r3 {n : ℕ} (l : List (Fin (n + 1))) (h : ∀ v ∈ l, v ≠ 0) :
    ∃ L : List (Fin n), l = L.map Fin.succ := by
  induction l with
  | nil => exact ⟨[], rfl⟩
  | cons v l ih =>
    have hv : v ≠ 0 := h v List.mem_cons_self
    obtain ⟨y, rfl⟩ := Fin.exists_succ_eq.2 hv
    have hl : ∀ w ∈ l, w ≠ 0 := fun w hw => h w (List.mem_cons_of_mem _ hw)
    obtain ⟨L, rfl⟩ := ih hl
    exact ⟨y :: L, rfl⟩

/-- Prior of the intervention switch: weight `1/2` on `a` and weight `1/2` on `c`. -/
private noncomputable def switchPrior_r3 {α : Type*} (a c : α) :
    Convexity.StdSimplex ℝ α :=
  Convexity.StdSimplex.duple a c (s := 1 / 2) (t := 1 / 2) (by norm_num) (by norm_num)
    (by norm_num)

private lemma switchPrior_r3_weights_left_pos {α : Type*} (a c : α) :
    0 < (switchPrior_r3 a c).weights a := by
  unfold switchPrior_r3
  rw [Convexity.StdSimplex.weights_duple, Finsupp.add_apply, Finsupp.single_eq_same]
  by_cases h : c = a
  · subst h
    rw [Finsupp.single_eq_same]
    norm_num
  · rw [Finsupp.single_eq_of_ne (Ne.symm h)]
    norm_num

private lemma switchPrior_r3_weights_right_pos {α : Type*} (a c : α) :
    0 < (switchPrior_r3 a c).weights c := by
  unfold switchPrior_r3
  rw [Convexity.StdSimplex.weights_duple, Finsupp.add_apply, Finsupp.single_eq_same]
  by_cases h : a = c
  · subst h
    rw [Finsupp.single_eq_same]
    norm_num
  · rw [Finsupp.single_eq_of_ne (Ne.symm h)]
    norm_num

/-- Parents in the switch network on `n + 1` nodes: node `0` is the switch (no parents); node
`j.succ` has the parents of `j` in `B` shifted by one, plus node `0` when `j ∈ T`. -/
private def switchPa_r3 {α : Type*} {n : ℕ} (B : BayesNet α n) (T : Finset (Fin n)) :
    (k : Fin (n + 1)) → Finset (Fin k) :=
  Fin.cases (motive := fun k : Fin (n + 1) => Finset (Fin k)) ∅
    (fun j => (B.pa j).map (Fin.succEmb j.val) ∪
      (if j ∈ T then {⟨0, by rw [Fin.val_succ]; exact Nat.zero_lt_succ _⟩} else ∅))

/-- A parent of `j` in `B`, shifted by one, is a parent of `j.succ` in the switch network. -/
private lemma switchPa_r3_mem_succ {α : Type*} {n : ℕ} (B : BayesNet α n)
    (T : Finset (Fin n)) (j : Fin n) (i : B.pa j) :
    Fin.succ i.1 ∈ switchPa_r3 B T j.succ := by
  simp only [switchPa_r3, Fin.cases_succ]
  refine Finset.mem_union_left _ ?_
  have h1 := Finset.mem_map_of_mem (Fin.succEmb j.val) i.2
  rwa [Fin.coe_succEmb] at h1

/-- Node `0` is a parent of `j.succ` in the switch network when `j ∈ T`. -/
private lemma switchPa_r3_mem_zero {α : Type*} {n : ℕ} (B : BayesNet α n)
    (T : Finset (Fin n)) (j : Fin n) (hj : j ∈ T) (h0 : 0 < j.succ.val) :
    (⟨0, h0⟩ : Fin j.succ) ∈ switchPa_r3 B T j.succ := by
  simp only [switchPa_r3, Fin.cases_succ]
  rw [ite_eq_left hj]
  exact Finset.mem_union_right _ (Finset.mem_singleton_self _)

/-- The switch network: node `0` has table `switchPrior_r3 a c`; node `j.succ` with `j ∈ T` has
the point mass at `x j` when node `0` equals `a` and the table of `j` in `B` otherwise; every
other node `j.succ` has the table of `j` in `B`. -/
private noncomputable def switchNet_r3 {α : Type*} [DecidableEq α] {n : ℕ} (B : BayesNet α n)
    (T : Finset (Fin n)) (x : Fin n → α) (a c : α) : BayesNet α (n + 1) where
  pa := switchPa_r3 B T
  cpt := Fin.cases (motive := fun k : Fin (n + 1) =>
      (switchPa_r3 B T k → α) → Convexity.StdSimplex ℝ α)
    (fun _ => switchPrior_r3 a c)
    (fun j u =>
      if hj : j ∈ T then
        if u ⟨⟨0, by rw [Fin.val_succ]; exact Nat.zero_lt_succ _⟩,
          switchPa_r3_mem_zero B T j hj _⟩ = a then Convexity.StdSimplex.single (x j)
        else B.cpt j (fun i => u ⟨Fin.succ i.1, switchPa_r3_mem_succ B T j i⟩)
      else B.cpt j (fun i => u ⟨Fin.succ i.1, switchPa_r3_mem_succ B T j i⟩))

private lemma switchNet_r3_factor_zero {α : Type*} [DecidableEq α] {n : ℕ} (B : BayesNet α n)
    (T : Finset (Fin n)) (x : Fin n → α) (a c : α) (v : Fin (n + 1) → α) :
    ((switchNet_r3 B T x a c).cpt 0 fun i => v (Fin.castLE (0 : Fin (n + 1)).2.le i)).weights
        (v 0) = (switchPrior_r3 a c).weights (v 0) := by
  simp only [switchNet_r3, Fin.cases_zero]

private lemma switchNet_r3_factor_succ {α : Type*} [DecidableEq α] [Nonempty α] {n : ℕ}
    (B : BayesNet α n) (T : Finset (Fin n)) (x : Fin n → α) (a c : α) (v : Fin (n + 1) → α)
    (j : Fin n) :
    ((switchNet_r3 B T x a c).cpt j.succ fun i => v (Fin.castLE j.succ.2.le i)).weights
        (v j.succ) =
      if j ∈ T ∧ v 0 = a then (if v j.succ = x j then 1 else 0)
      else (B.cpt j (B.paVal j (Fin.tail v))).weights (v j.succ) := by
  simp only [switchNet_r3, Fin.cases_succ]
  have hcast0 : ∀ h0 : 0 < j.succ.val,
      Fin.castLE j.succ.2.le (⟨0, h0⟩ : Fin j.succ) = 0 := by
    intro h0
    rw [Fin.ext_iff]
    show (0 : ℕ) = _
    exact (Fin.val_zero _).symm
  simp only [hcast0]
  have hfun : (fun i : B.pa j => v (Fin.castLE j.succ.2.le (i.1).succ)) =
      B.paVal j (Fin.tail v) := by
    funext i
    show v _ = v _
    rfl
  by_cases hj : j ∈ T
  · by_cases hva : v 0 = a
    · simp only [hj, hva, dite_true, ite_true, true_and]
      rw [Convexity.StdSimplex.weights_single]
      by_cases hvv : v j.succ = x j
      · simp [hvv]
      · simp [hvv]
    · simp only [hj, hva, dite_true, ite_false, true_and]
      rw [hfun]
  · simp only [hj, dite_false, false_and, ite_false]
    rw [hfun]

private lemma switchNet_r3_edge_succ_succ {α : Type*} [DecidableEq α] {n : ℕ}
    (B : BayesNet α n) (T : Finset (Fin n)) (x : Fin n → α) (a c : α) {i j : Fin n} :
    (switchNet_r3 B T x a c).Edge i.succ j.succ ↔ B.Edge i j := by
  simp only [switchNet_r3, Edge, switchPa_r3, Fin.cases_succ]
  constructor
  · rintro ⟨h, hmem⟩
    rw [Fin.val_succ, Fin.val_succ] at h
    rcases Finset.mem_union.1 hmem with hmap | hzero
    · rw [Finset.mem_map] at hmap
      obtain ⟨e', he'mem, he'eq⟩ := hmap
      have hval : e'.val + 1 = i.val + 1 := by
        have hcc := congrArg Fin.val he'eq
        simpa [Fin.coe_succEmb, Fin.val_succ] using hcc
      have hval' : e'.val = i.val := by omega
      have hei : e' = ⟨i.val, by omega⟩ := Fin.ext hval'
      rw [hei] at he'mem
      exact ⟨by omega, he'mem⟩
    · by_cases hjT : j ∈ T
      · rw [ite_eq_left hjT, Finset.mem_singleton] at hzero
        have hcc := congrArg Fin.val hzero
        simp [Fin.val_succ] at hcc
      · rw [ite_eq_right hjT] at hzero
        exact absurd hzero (Finset.notMem_empty _)
  · rintro ⟨h, hmem⟩
    have h' : i.succ.val < j.succ.val := by rw [Fin.val_succ, Fin.val_succ]; omega
    refine ⟨h', Finset.mem_union_left _ ?_⟩
    rw [Finset.mem_map]
    exact ⟨⟨i.val, h⟩, hmem, by rw [Fin.coe_succEmb]; rfl⟩

private lemma switchNet_r3_edge_zero_succ {α : Type*} [DecidableEq α] {n : ℕ}
    (B : BayesNet α n) (T : Finset (Fin n)) (x : Fin n → α) (a c : α) {j : Fin n} :
    (switchNet_r3 B T x a c).Edge 0 j.succ ↔ j ∈ T := by
  simp only [switchNet_r3, Edge, switchPa_r3, Fin.cases_succ]
  constructor
  · rintro ⟨h, hmem⟩
    rcases Finset.mem_union.1 hmem with hmap | hzero
    · rw [Finset.mem_map] at hmap
      obtain ⟨e', -, he'eq⟩ := hmap
      have hcc := congrArg Fin.val he'eq
      simp [Fin.coe_succEmb, Fin.val_succ, Fin.val_zero] at hcc
    · by_cases hjT : j ∈ T
      · exact hjT
      · rw [ite_eq_right hjT] at hzero
        exact absurd hzero (Finset.notMem_empty _)
  · intro hjT
    have h1 : (0 : Fin (n + 1)).val = 0 := Fin.val_zero _
    have h' : (0 : Fin (n + 1)).val < j.succ.val := by
      have h2 : j.succ.val = j.val + 1 := Fin.val_succ j
      omega
    refine ⟨h', Finset.mem_union_right _ ?_⟩
    rw [ite_eq_left hjT, Finset.mem_singleton]
    exact Fin.ext (by rw [h1])

private lemma switchNet_r3_not_edge_zero {α : Type*} [DecidableEq α] {n : ℕ}
    (B : BayesNet α n) (T : Finset (Fin n)) (x : Fin n → α) (a c : α) (i : Fin (n + 1)) :
    ¬(switchNet_r3 B T x a c).Edge i 0 := by
  simp only [switchNet_r3, Edge, switchPa_r3, Fin.cases_zero]
  rintro ⟨h, hmem⟩
  exact absurd hmem (Finset.notMem_empty _)

private lemma switchNet_r3_isDescendant_succ {α : Type*} [DecidableEq α] {n : ℕ}
    (B : BayesNet α n) (T : Finset (Fin n)) (x : Fin n → α) (a c : α) {i : Fin n}
    {d : Fin (n + 1)} (h : (switchNet_r3 B T x a c).IsDescendant i.succ d) :
    ∃ d₀ : Fin n, d = d₀.succ ∧ B.IsDescendant i d₀ := by
  unfold IsDescendant at h
  induction h with
  | refl => exact ⟨i, rfl, Relation.ReflTransGen.refl⟩
  | @tail m d' _ e ih =>
    obtain ⟨m₀, rfl, hm⟩ := ih
    by_cases hd0 : d' = 0
    · subst hd0
      exact absurd e (switchNet_r3_not_edge_zero B T x a c _)
    · obtain ⟨d₀, rfl⟩ := Fin.exists_succ_eq.2 hd0
      exact ⟨d₀, rfl,
        Relation.ReflTransGen.tail hm ((switchNet_r3_edge_succ_succ B T x a c).1 e)⟩

private lemma switchNet_r3_adj_succ_succ {α : Type*} [DecidableEq α] {n : ℕ}
    (B : BayesNet α n) (T : Finset (Fin n)) (x : Fin n → α) (a c : α) {i j : Fin n} :
    (switchNet_r3 B T x a c).Adj i.succ j.succ ↔ B.Adj i j := by
  unfold Adj
  rw [switchNet_r3_edge_succ_succ, switchNet_r3_edge_succ_succ]

private lemma switchNet_r3_isPath_map {α : Type*} [DecidableEq α] {n : ℕ}
    (B : BayesNet α n) (T : Finset (Fin n)) (x : Fin n → α) (a c : α) {t y : Fin n}
    {L : List (Fin n)} (hp : (switchNet_r3 B T x a c).IsPath t.succ y.succ (L.map Fin.succ)) :
    B.IsPath t y L := by
  obtain ⟨hnd, hch, hh, hl⟩ := hp
  have hndL : L.Nodup := List.Nodup.of_map Fin.succ hnd
  have hchL : L.IsChain B.Adj := by
    rw [List.isChain_iff_getElem] at hch ⊢
    intro i hi
    have hi' : i + 1 < (L.map Fin.succ).length := by
      rw [List.length_map]
      exact hi
    have hN := hch i hi'
    simp only [List.getElem_map] at hN
    exact (switchNet_r3_adj_succ_succ B T x a c).1 hN
  have hhL : L.head? = some t := by
    rw [List.head?_map] at hh
    match hL : L.head? with
    | none =>
      simp only [hL, Option.map_none] at hh
      simp at hh
    | some v =>
      simp only [hL, Option.map_some] at hh
      have hhF := Option.some.inj hh
      have hval := congrArg Fin.val hhF
      simp only [Fin.val_succ] at hval
      have heq : v = t := Fin.ext (by omega)
      rw [heq]
  have hlL : L.getLast? = some y := by
    rw [List.getLast?_map] at hl
    match hG : L.getLast? with
    | none =>
      simp only [hG, Option.map_none] at hl
      simp at hl
    | some v =>
      simp only [hG, Option.map_some] at hl
      have hlF := Option.some.inj hl
      have hval := congrArg Fin.val hlF
      simp only [Fin.val_succ] at hval
      have heq : v = y := Fin.ext (by omega)
      rw [heq]
  exact ⟨hndL, hchL, hhL, hlL⟩

private lemma switchNet_r3_blockedAt_succ {α : Type*} [DecidableEq α] {n : ℕ}
    (B : BayesNet α n) (T C : Finset (Fin n)) (x : Fin n → α) (a c : α) {u m w : Fin n}
    (h : B.BlockedAt (C : Set (Fin n)) u m w) :
    (switchNet_r3 B T x a c).BlockedAt
      ((C.map (Fin.succEmb n) : Finset (Fin (n + 1))) : Set (Fin (n + 1))) u.succ m.succ
      w.succ := by
  rcases h with ⟨e1, e2, hdesc⟩ | ⟨hcol, hmem⟩
  · refine Or.inl ⟨(switchNet_r3_edge_succ_succ B T x a c).2 e1,
      (switchNet_r3_edge_succ_succ B T x a c).2 e2, ?_⟩
    intro d hd hmemC
    rw [Finset.mem_coe] at hmemC
    obtain ⟨d₀, rfl, hd₀⟩ := switchNet_r3_isDescendant_succ B T x a c hd
    rw [Finset.mem_map] at hmemC
    obtain ⟨a₀, haC, heq⟩ := hmemC
    rw [Fin.coe_succEmb] at heq
    have hval := congrArg Fin.val heq
    simp only [Fin.val_succ] at hval
    have haeq : a₀ = d₀ := Fin.ext (by omega)
    subst haeq
    exact hdesc a₀ hd₀ (Finset.mem_coe.2 haC)
  · refine Or.inr ⟨?_, ?_⟩
    · intro hcon
      apply hcol
      constructor
      · exact (switchNet_r3_edge_succ_succ B T x a c).1 hcon.1
      · exact (switchNet_r3_edge_succ_succ B T x a c).1 hcon.2
    · rw [Finset.mem_coe, Finset.mem_map]
      exact ⟨m, Finset.mem_coe.1 hmem, by rw [Fin.coe_succEmb]⟩

private lemma switchNet_r3_dSeparated {α : Type*} [DecidableEq α] {n : ℕ}
    (B : BayesNet α n) {T Y C : Finset (Fin n)} (x : Fin n → α) (a c : α)
    (hd : B.DSeparated (T : Set (Fin n)) (Y : Set (Fin n)) (C : Set (Fin n))) :
    (switchNet_r3 B T x a c).DSeparated (({0} : Finset (Fin (n + 1))) : Set (Fin (n + 1)))
      ((Y.map (Fin.succEmb n) : Finset (Fin (n + 1))) : Set (Fin (n + 1)))
      ((C.map (Fin.succEmb n) : Finset (Fin (n + 1))) : Set (Fin (n + 1))) := by
  intro x0 hx0 y0 hy0 p hp
  rw [Finset.mem_coe, Finset.mem_singleton] at hx0
  subst hx0
  rw [Finset.mem_coe, Finset.mem_map] at hy0
  obtain ⟨y, hyY, hyEq⟩ := hy0
  rw [Fin.coe_succEmb] at hyEq
  subst hyEq
  obtain ⟨hnd, hch, hh, hl⟩ := hp
  cases p with
  | nil =>
    simp at hh
  | cons hd tl =>
    simp only [List.head?_cons, Option.some.injEq] at hh
    subst hh
    have h0not : (0 : Fin (n + 1)) ∉ tl := (List.nodup_cons.1 hnd).1
    have hne : ∀ v ∈ tl, v ≠ 0 := fun v hv heq => h0not (heq ▸ hv)
    obtain ⟨L, rfl⟩ := exists_eq_map_succ_r3 tl hne
    cases L with
    | nil =>
      simp at hl
      exact absurd hl.symm (Fin.succ_ne_zero _)
    | cons t L' =>
      simp only [List.map_cons] at hnd hch hl
      obtain ⟨hadj, hchRest⟩ := List.isChain_cons_cons.1 hch
      have htT : t ∈ T := by
        unfold Adj at hadj
        rcases hadj with h01 | h10
        · exact (switchNet_r3_edge_zero_succ B T x a c).1 h01
        · exact absurd h10 (switchNet_r3_not_edge_zero B T x a c _)
      have hndRest : (t.succ :: L'.map Fin.succ).Nodup := (List.nodup_cons.1 hnd).2
      have hlRest : (t.succ :: L'.map Fin.succ).getLast? = some y.succ := by
        rwa [List.getLast?_cons_cons] at hl
      have hpN : (switchNet_r3 B T x a c).IsPath t.succ y.succ ((t :: L').map Fin.succ) :=
        ⟨by simpa [List.map_cons] using hndRest, by simpa [List.map_cons] using hchRest,
          rfl, by simpa [List.map_cons] using hlRest⟩
      have hB : B.IsPath t y (t :: L') := switchNet_r3_isPath_map B T x a c hpN
      obtain ⟨i, hi, hb⟩ := hd t (Finset.mem_coe.2 htT) y (Finset.mem_coe.2 hyY) (t :: L') hB
      refine ⟨i + 1, by simp [List.length_map] at hi ⊢; omega, ?_⟩
      simp only [List.getElem_cons_succ, List.getElem_map]
      exact switchNet_r3_blockedAt_succ B T C x a c hb

private lemma switchNet_r3_joint_cons {α : Type*} [DecidableEq α] [Nonempty α] {n : ℕ}
    (B : BayesNet α n) (T : Finset (Fin n)) (x : Fin n → α) (a c : α) (f : α)
    (v : Fin n → α) :
    (switchNet_r3 B T x a c).joint (Fin.cons f v) =
      (switchPrior_r3 a c).weights f *
        (if f = a then (B.mutilateSet T x).joint v else B.joint v) := by
  rw [joint_eq_prod, Fin.prod_univ_succ, switchNet_r3_factor_zero, Fin.cons_zero]
  have hfac : ∀ j : Fin n,
      ((switchNet_r3 B T x a c).cpt j.succ fun i =>
          (Fin.cons f v : Fin (n + 1) → α) (Fin.castLE j.succ.2.le i)).weights
        ((Fin.cons f v : Fin (n + 1) → α) j.succ) =
        if j ∈ T ∧ f = a then (if v j = x j then 1 else 0)
        else (B.cpt j (B.paVal j v)).weights (v j) := by
    intro j
    have h := switchNet_r3_factor_succ B T x a c (Fin.cons f v) j
    rwa [Fin.cons_zero, Fin.cons_succ, Fin.tail_cons] at h
  simp only [hfac]
  by_cases hf : f = a
  · have hif : (if f = a then (B.mutilateSet T x).joint v else B.joint v) =
        (B.mutilateSet T x).joint v := by simp [hf]
    rw [hif]
    congr 1
    rw [joint_mutilateSet]
    refine Finset.prod_congr rfl fun j _ => ?_
    simp [hf]
  · have hif : (if f = a then (B.mutilateSet T x).joint v else B.joint v) = B.joint v := by
      simp [hf]
    rw [hif]
    congr 1
    rw [joint_eq_prod]
    refine Finset.prod_congr rfl fun j _ => ?_
    have hpa : B.paVal j v = (fun (j_1 : B.pa j) => v (Fin.castLE j.2.le j_1)) := rfl
    rw [ite_eq_right (fun h => hf h.2), hpa]

private lemma switchNet_r3_marginal_cons {α : Type*} [DecidableEq α] [Nonempty α] [Fintype α]
    {n : ℕ} (B : BayesNet α n) (T : Finset (Fin n)) (x : Fin n → α) (a c : α)
    (S : Finset (Fin n)) (f : α) (v : Fin n → α) :
    marginal (switchNet_r3 B T x a c).joint
        ((insert 0 (S.map (Fin.succEmb n)) : Finset (Fin (n + 1))) : Set (Fin (n + 1)))
        (Fin.cons f v) =
      (switchPrior_r3 a c).weights f *
        (if f = a then marginal (B.mutilateSet T x).joint ↑S v
          else marginal B.joint ↑S v) := by
  classical
  simp only [marginal_coe]
  by_cases hf : f = a
  · rw [ite_eq_left hf]
    rw [Finset.mul_sum]
    refine (Finset.sum_nbij' (Fin.cons f) Fin.tail ?_ ?_ ?_ ?_ ?_).symm
    · intro w' hw'
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw' ⊢
      intro i hi
      rcases Finset.mem_insert.1 hi with rfl | hiMap
      · simp [Fin.cons_zero]
      · rw [Finset.mem_map] at hiMap
        obtain ⟨j, hjS, hjEq⟩ := hiMap
        subst hjEq
        rw [Fin.coe_succEmb, Fin.cons_succ, Fin.cons_succ]
        exact hw' j hjS
    · intro w hw
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw ⊢
      intro i hiS
      have hmem : (Fin.succEmb n) i ∈ insert 0 (S.map (Fin.succEmb n)) :=
        Finset.mem_insert_of_mem (Finset.mem_map_of_mem _ hiS)
      have hwS := hw _ hmem
      rw [Fin.coe_succEmb] at hwS
      rw [Fin.cons_succ] at hwS
      exact hwS
    · intro w' _
      simp [Fin.tail_cons]
    · intro w hw
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw
      have hw0 := hw 0 (Finset.mem_insert_self 0 _)
      rw [Fin.cons_zero] at hw0
      have htail := Fin.cons_self_tail w
      rw [hw0] at htail
      exact htail
    · intro w' _
      rw [switchNet_r3_joint_cons]
      simp [hf]
  · rw [ite_eq_right hf]
    rw [Finset.mul_sum]
    refine (Finset.sum_nbij' (Fin.cons f) Fin.tail ?_ ?_ ?_ ?_ ?_).symm
    · intro w' hw'
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw' ⊢
      intro i hi
      rcases Finset.mem_insert.1 hi with rfl | hiMap
      · simp [Fin.cons_zero]
      · rw [Finset.mem_map] at hiMap
        obtain ⟨j, hjS, hjEq⟩ := hiMap
        subst hjEq
        rw [Fin.coe_succEmb, Fin.cons_succ, Fin.cons_succ]
        exact hw' j hjS
    · intro w hw
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw ⊢
      intro i hiS
      have hmem : (Fin.succEmb n) i ∈ insert 0 (S.map (Fin.succEmb n)) :=
        Finset.mem_insert_of_mem (Finset.mem_map_of_mem _ hiS)
      have hwS := hw _ hmem
      rw [Fin.coe_succEmb] at hwS
      rw [Fin.cons_succ] at hwS
      exact hwS
    · intro w' _
      simp [Fin.tail_cons]
    · intro w hw
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw
      have hw0 := hw 0 (Finset.mem_insert_self 0 _)
      rw [Fin.cons_zero] at hw0
      have htail := Fin.cons_self_tail w
      rw [hw0] at htail
      exact htail
    · intro w' _
      rw [switchNet_r3_joint_cons]
      simp [hf]

/-- A marginal over mapped nodes does not see the switch value. -/
private lemma switch_marginal_cons_eq_r3 {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
    {n : ℕ} (B : BayesNet α n) (T S : Finset (Fin n)) (x : Fin n → α) (a c : α) (f g : α) :
    marginal (switchNet_r3 B T x a c).joint ↑(S.map (Fin.succEmb n)) (Fin.cons f x) =
      marginal (switchNet_r3 B T x a c).joint ↑(S.map (Fin.succEmb n)) (Fin.cons g x) := by
  apply marginal_congr_of_eqOn
  intro i hi
  rw [Finset.mem_map] at hi
  obtain ⟨j, _, hjEq⟩ := hi
  subst hjEq
  rw [Fin.coe_succEmb, Fin.cons_succ, Fin.cons_succ]

/-- The switch-network conditional independence, expanded at `Fin.cons a x`. -/
private lemma condIndep_switch_cons_a_r3 {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
    {n : ℕ} (B : BayesNet α n) {T Y C : Finset (Fin n)} (x : Fin n → α) (a c : α)
    (hCI : CondIndep (switchNet_r3 B T x a c).joint
      (({0} : Finset (Fin (n + 1))) : Set (Fin (n + 1)))
      ((Y.map (Fin.succEmb n) : Finset (Fin (n + 1))) : Set (Fin (n + 1)))
      ((C.map (Fin.succEmb n) : Finset (Fin (n + 1))) : Set (Fin (n + 1)))) :
    ((switchPrior_r3 a c).weights a * marginal (B.mutilateSet T x).joint ↑(Y ∪ C) x) *
          marginal (switchNet_r3 B T x a c).joint ↑(C.map (Fin.succEmb n)) (Fin.cons a x) =
        ((switchPrior_r3 a c).weights a * marginal (B.mutilateSet T x).joint ↑C x) *
          marginal (switchNet_r3 B T x a c).joint ↑((Y ∪ C).map (Fin.succEmb n))
            (Fin.cons a x) := by
  have h := (condIndep_coe_iff.1 hCI) (Fin.cons a x)
  have e3 : (Y.map (Fin.succEmb n) ∪ C.map (Fin.succEmb n) : Finset (Fin (n + 1))) =
      (Y ∪ C).map (Fin.succEmb n) := by simp [Finset.map_union]
  have e2 : (({0} : Finset (Fin (n + 1))) ∪ C.map (Fin.succEmb n)) =
      insert 0 (C.map (Fin.succEmb n)) := by exact (Finset.insert_eq 0 _).symm
  have e1 : (({0} : Finset (Fin (n + 1))) ∪ Y.map (Fin.succEmb n) ∪ C.map (Fin.succEmb n)) =
      insert 0 ((Y ∪ C).map (Fin.succEmb n)) := by
    rw [Finset.insert_eq, Finset.map_union, Finset.union_assoc]
  rw [e1, e2, e3] at h
  simp only [switchNet_r3_marginal_cons] at h
  rw [ite_eq_left True.intro, ite_eq_left True.intro] at h
  exact h

/-- The switch-network conditional independence, expanded at `Fin.cons c x`. -/
private lemma condIndep_switch_cons_c_r3 {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
    {n : ℕ} (B : BayesNet α n) {T Y C : Finset (Fin n)} (x : Fin n → α) (a c : α)
    (hca : c ≠ a)
    (hCI : CondIndep (switchNet_r3 B T x a c).joint
      (({0} : Finset (Fin (n + 1))) : Set (Fin (n + 1)))
      ((Y.map (Fin.succEmb n) : Finset (Fin (n + 1))) : Set (Fin (n + 1)))
      ((C.map (Fin.succEmb n) : Finset (Fin (n + 1))) : Set (Fin (n + 1)))) :
    ((switchPrior_r3 a c).weights c * marginal B.joint ↑(Y ∪ C) x) *
          marginal (switchNet_r3 B T x a c).joint ↑(C.map (Fin.succEmb n)) (Fin.cons a x) =
        ((switchPrior_r3 a c).weights c * marginal B.joint ↑C x) *
          marginal (switchNet_r3 B T x a c).joint ↑((Y ∪ C).map (Fin.succEmb n))
            (Fin.cons a x) := by
  have h := (condIndep_coe_iff.1 hCI) (Fin.cons c x)
  have e3 : (Y.map (Fin.succEmb n) ∪ C.map (Fin.succEmb n) : Finset (Fin (n + 1))) =
      (Y ∪ C).map (Fin.succEmb n) := by simp [Finset.map_union]
  have e2 : (({0} : Finset (Fin (n + 1))) ∪ C.map (Fin.succEmb n)) =
      insert 0 (C.map (Fin.succEmb n)) := by exact (Finset.insert_eq 0 _).symm
  have e1 : (({0} : Finset (Fin (n + 1))) ∪ Y.map (Fin.succEmb n) ∪ C.map (Fin.succEmb n)) =
      insert 0 ((Y ∪ C).map (Fin.succEmb n)) := by
    rw [Finset.insert_eq, Finset.map_union, Finset.union_assoc]
  rw [e1, e2, e3] at h
  simp only [switchNet_r3_marginal_cons] at h
  rw [ite_eq_right hca, ite_eq_right hca] at h
  have hT0 := switch_marginal_cons_eq_r3 B T C x a c a c
  have hU0 := switch_marginal_cons_eq_r3 B T (Y ∪ C) x a c a c
  rw [← hT0, ← hU0] at h
  exact h

/-- Lower bound at `Fin.cons a x`: the switch mass on `a` times the intervened marginal. -/
private lemma switch_marginal_le_a_r3 {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
    {n : ℕ} (B : BayesNet α n) {T C : Finset (Fin n)} (x : Fin n → α) (a c : α) :
    (switchPrior_r3 a c).weights a * marginal (B.mutilateSet T x).joint ↑C x ≤
      marginal (switchNet_r3 B T x a c).joint ↑(C.map (Fin.succEmb n)) (Fin.cons a x) := by
  have hpN : ∀ v, 0 ≤ (switchNet_r3 B T x a c).joint v :=
    fun v => (switchNet_r3 B T x a c).toChain.joint_nonneg _ v
  have hsub : (↑(C.map (Fin.succEmb n)) : Set (Fin (n + 1))) ⊆
      (↑(insert 0 (C.map (Fin.succEmb n))) : Set (Fin (n + 1))) := by
    intro y hy
    simp only [Finset.mem_coe] at hy ⊢
    exact Finset.mem_insert_of_mem hy
  have hanti := marginal_anti hpN hsub (Fin.cons a x)
  simp only [switchNet_r3_marginal_cons] at hanti
  rw [ite_eq_left True.intro] at hanti
  exact hanti

/-- Lower bound at `Fin.cons c x`, transported to `Fin.cons a x`. -/
private lemma switch_marginal_le_c_r3 {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
    {n : ℕ} (B : BayesNet α n) {T C : Finset (Fin n)} (x : Fin n → α) (a c : α)
    (hca : c ≠ a) :
    (switchPrior_r3 a c).weights c * marginal B.joint ↑C x ≤
      marginal (switchNet_r3 B T x a c).joint ↑(C.map (Fin.succEmb n)) (Fin.cons a x) := by
  have hpN : ∀ v, 0 ≤ (switchNet_r3 B T x a c).joint v :=
    fun v => (switchNet_r3 B T x a c).toChain.joint_nonneg _ v
  have hsub : (↑(C.map (Fin.succEmb n)) : Set (Fin (n + 1))) ⊆
      (↑(insert 0 (C.map (Fin.succEmb n))) : Set (Fin (n + 1))) := by
    intro y hy
    simp only [Finset.mem_coe] at hy ⊢
    exact Finset.mem_insert_of_mem hy
  have hanti := marginal_anti hpN hsub (Fin.cons c x)
  simp only [switchNet_r3_marginal_cons] at hanti
  rw [ite_eq_right hca] at hanti
  have hT0 := switch_marginal_cons_eq_r3 B T C x a c a c
  rw [← hT0] at hanti
  exact hanti

/-- Pure algebra closing the core identity from the two expanded equations. -/
private lemma rule3_core_algebra_r3 (wa wc DYC DC BYC BC T0 U0 : ℝ)
    (hwa : 0 < wa) (hwc : 0 < wc) (hDC0 : 0 ≤ DC) (hBC0 : 0 ≤ BC)
    (hCIa : (wa * DYC) * T0 = (wa * DC) * U0)
    (hCIc : (wc * BYC) * T0 = (wc * BC) * U0)
    (hle_a : wa * DC ≤ T0) (hle_c : wc * BC ≤ T0) :
    DYC * BC = BYC * DC := by
  by_cases hT0 : T0 = 0
  · have h1 : wa * DC = 0 :=
      le_antisymm (hle_a.trans_eq hT0) (mul_nonneg (le_of_lt hwa) hDC0)
    have h2 : wc * BC = 0 :=
      le_antisymm (hle_c.trans_eq hT0) (mul_nonneg (le_of_lt hwc) hBC0)
    have hDC : DC = 0 := (mul_eq_zero.1 h1).resolve_left (ne_of_gt hwa)
    have hBC : BC = 0 := (mul_eq_zero.1 h2).resolve_left (ne_of_gt hwc)
    simp [hBC, hDC]
  · have hwa0 : wa ≠ 0 := ne_of_gt hwa
    have hwc0 : wc ≠ 0 := ne_of_gt hwc
    have hmul0 : wa * wc * T0 ≠ 0 := mul_ne_zero (mul_ne_zero hwa0 hwc0) hT0
    have hzero : (DYC * BC - BYC * DC) * (wa * wc * T0) = 0 := by
      linear_combination (wc * BC) * hCIa - (wa * DC) * hCIc
    have hsub : DYC * BC - BYC * DC = 0 :=
      (mul_eq_zero.1 hzero).resolve_right hmul0
    exact sub_eq_zero.1 hsub

/-- Core of rule 3, with no positivity hypothesis: if `T` and `Y` are d-separated by `C` in
`B`, then `P(y, c | do(t)) P(c) = P(y, c) P(c | do(t))` at the values of `x`. -/
private lemma marginal_mutilateSet_mul_of_dSeparated_r3 {α : Type*} [Fintype α]
    [DecidableEq α] [Nonempty α] {n : ℕ} (B : BayesNet α n) {T Y C : Finset (Fin n)}
    (x : Fin n → α)
    (hd : B.DSeparated (T : Set (Fin n)) (Y : Set (Fin n)) (C : Set (Fin n))) :
    marginal (B.mutilateSet T x).joint ↑(Y ∪ C) x * marginal B.joint ↑C x =
      marginal B.joint ↑(Y ∪ C) x * marginal (B.mutilateSet T x).joint ↑C x := by
  classical
  rcases subsingleton_or_nontrivial α with hsub | hnon
  · have hfull : ∀ (P : (Fin n → α) → ℝ) (S : Finset (Fin n)),
        marginal P ↑S x = ∑ y, P y := by
      intro P S
      unfold marginal
      congr 1
      ext y
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact iff_true_intro fun v _ => hsub.elim _ _
    rw [hfull, hfull, hfull, hfull]
    exact mul_comm _ _
  · haveI := hnon
    obtain ⟨a, c, hac⟩ := exists_pair_ne α
    have hca : c ≠ a := Ne.symm hac
    have hdN : (switchNet_r3 B T x a c).DSeparated
        (({0} : Finset (Fin (n + 1))) : Set (Fin (n + 1)))
        ((Y.map (Fin.succEmb n) : Finset (Fin (n + 1))) : Set (Fin (n + 1)))
        ((C.map (Fin.succEmb n) : Finset (Fin (n + 1))) : Set (Fin (n + 1))) :=
      switchNet_r3_dSeparated B x a c hd
    have hCI := (switchNet_r3 B T x a c).condIndep_of_dSeparated_finset hdN
    have e1 := condIndep_switch_cons_a_r3 B x a c hCI
    have e2 := condIndep_switch_cons_c_r3 B x a c hca hCI
    have l1 := switch_marginal_le_a_r3 (T := T) (C := C) B x a c
    have l2 := switch_marginal_le_c_r3 (T := T) (C := C) B x a c hca
    have hwa : 0 < (switchPrior_r3 a c).weights a := switchPrior_r3_weights_left_pos a c
    have hwc : 0 < (switchPrior_r3 a c).weights c := switchPrior_r3_weights_right_pos a c
    have hDC0 : 0 ≤ marginal (B.mutilateSet T x).joint ↑C x :=
      marginal_nonneg (fun v => (B.mutilateSet T x).toChain.joint_nonneg n v) _ _
    have hBC0 : 0 ≤ marginal B.joint ↑C x :=
      marginal_nonneg (fun v => B.toChain.joint_nonneg n v) _ _
    exact rule3_core_algebra_r3 _ _ _ _ _ _ _ _ hwa hwc hDC0 hBC0 e1 e2 l1 l2

/-- The Finset identity behind the `Y ∪ W` absorption facts. -/
private lemma finset_Y_XW_r3 {n : ℕ} (X Y W : Finset (Fin n)) :
    Y ∪ (X ∪ W) = (Y ∪ W) ∪ X := by
  ext i
  simp only [Finset.mem_union]
  constructor
  · rintro (hy | hx | hw)
    · exact Or.inl (Or.inl hy)
    · exact Or.inr hx
    · exact Or.inl (Or.inr hw)
  · rintro ((hy | hw) | hx)
    · exact Or.inl hy
    · exact Or.inr (Or.inr hw)
    · exact Or.inr (Or.inl hx)

/-- Absorption for a subset of the intervened set. -/
private lemma marginal_mutilateSet_absorb_subset_r3 {α : Type*} [Fintype α] [Nonempty α]
    {n : ℕ} (b : BayesNet α n) (V S A : Finset (Fin n)) (x : Fin n → α) (hAV : A ⊆ V) :
    marginal (b.mutilateSet V x).joint ↑(S ∪ A) x =
      marginal (b.mutilateSet V x).joint ↑S x := by
  have hunion : S ∪ A ∪ V = S ∪ V := by
    ext i
    simp only [Finset.mem_union]
    constructor
    · rintro ((hs | ha) | hv)
      · exact Or.inl hs
      · exact Or.inr (hAV ha)
      · exact Or.inr hv
    · rintro (hs | hv)
      · exact Or.inl (Or.inl hs)
      · exact Or.inr hv
  have h1 := marginal_mutilateSet_union_absorb b V x (S ∪ A) (fun _ _ => rfl)
  rw [hunion] at h1
  have h2 := marginal_mutilateSet_union_absorb b V x S (fun _ _ => rfl)
  rw [← h1]
  exact h2

private lemma absorb_PXZ_YW_r3 {α : Type*} [Fintype α] [Nonempty α] {n : ℕ}
    (b : BayesNet α n) {X Y Z W : Finset (Fin n)} (x : Fin n → α) :
    marginal (b.mutilateSet (X ∪ Z) x).joint ↑(Y ∪ (X ∪ W)) x =
      marginal (b.mutilateSet (X ∪ Z) x).joint ↑(Y ∪ W) x := by
  rw [finset_Y_XW_r3]
  exact marginal_mutilateSet_absorb_subset_r3 b (X ∪ Z) (Y ∪ W) X x Finset.subset_union_left

private lemma absorb_PXZ_W_r3 {α : Type*} [Fintype α] [Nonempty α] {n : ℕ}
    (b : BayesNet α n) {X Z W : Finset (Fin n)} (x : Fin n → α) :
    marginal (b.mutilateSet (X ∪ Z) x).joint ↑(X ∪ W) x =
      marginal (b.mutilateSet (X ∪ Z) x).joint ↑W x := by
  rw [Finset.union_comm X W]
  exact marginal_mutilateSet_absorb_subset_r3 b (X ∪ Z) W X x Finset.subset_union_left

private lemma absorb_M_YW_r3 {α : Type*} [Fintype α] [Nonempty α] {n : ℕ}
    (b : BayesNet α n) {X Y W ZW : Finset (Fin n)} (x : Fin n → α) :
    marginal (b.mutilateSet (X ∪ ZW) x).joint ↑(Y ∪ (X ∪ W)) x =
      marginal (b.mutilateSet (X ∪ ZW) x).joint ↑(Y ∪ W) x := by
  rw [finset_Y_XW_r3]
  exact marginal_mutilateSet_absorb_subset_r3 b (X ∪ ZW) (Y ∪ W) X x Finset.subset_union_left

private lemma absorb_M_W_r3 {α : Type*} [Fintype α] [Nonempty α] {n : ℕ}
    (b : BayesNet α n) {X W ZW : Finset (Fin n)} (x : Fin n → α) :
    marginal (b.mutilateSet (X ∪ ZW) x).joint ↑(X ∪ W) x =
      marginal (b.mutilateSet (X ∪ ZW) x).joint ↑W x := by
  rw [Finset.union_comm X W]
  exact marginal_mutilateSet_absorb_subset_r3 b (X ∪ ZW) W X x Finset.subset_union_left

/-- **Rule 3 of the do-calculus** (insertion/deletion of actions; Pearl 1995, Theorem 3; Pearl
2009, Theorem 3.4.1): let `ZW` be the nodes of `Z` that are not ancestors of any node of `W`
in `G_{\bar X}` (Pearl's `Z(W)`). If `Y` and `Z` are d-separated by `X ∪ W` in
`G_{\bar X \overline{Z(W)}}` (the graph of `b.mutilateSet (X ∪ ZW) x`), then
`P(y | do(x), do(z), w) = P(y | do(x), w)`, wherever both conditional probabilities are
defined. -/
theorem doCalculus_rule3 {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α] {n : ℕ}
    (b : BayesNet α n) {X Y Z W : Finset (Fin n)} (x : Fin n → α)
    (hXY : Disjoint X Y) (hXZ : Disjoint X Z) (hXW : Disjoint X W) (hYZ : Disjoint Y Z)
    (hYW : Disjoint Y W) (hZW : Disjoint Z W) (ZW : Finset (Fin n))
    (hZWdef : ∀ z, z ∈ ZW ↔ z ∈ Z ∧ ∀ w ∈ W, ¬(b.mutilateSet X x).IsDescendant z w)
    (hd : (b.mutilateSet (X ∪ ZW) x).DSeparated (Y : Set (Fin n)) (Z : Set (Fin n))
      ((X ∪ W : Finset (Fin n)) : Set (Fin n)))
    (hwz : marginal (b.mutilateSet (X ∪ Z) x).joint (W : Set (Fin n)) x ≠ 0)
    (hw : marginal (b.mutilateSet X x).joint (W : Set (Fin n)) x ≠ 0) :
    marginal (b.mutilateSet (X ∪ Z) x).joint ((Y ∪ W : Finset (Fin n)) : Set (Fin n)) x /
        marginal (b.mutilateSet (X ∪ Z) x).joint (W : Set (Fin n)) x =
      marginal (b.mutilateSet X x).joint ((Y ∪ W : Finset (Fin n)) : Set (Fin n)) x /
        marginal (b.mutilateSet X x).joint (W : Set (Fin n)) x := by
  classical
  have hZWsub : ZW ⊆ Z := fun z hz => ((hZWdef z).1 hz).1
  have hunion : (X ∪ ZW) ∪ Z.filter (fun z => z ∉ ZW) = X ∪ Z := by
    ext i
    simp only [Finset.mem_union, Finset.mem_filter]
    constructor
    · rintro ((hx | hzw) | ⟨hz, -⟩)
      · exact Or.inl hx
      · exact Or.inr (hZWsub hzw)
      · exact Or.inr hz
    · rintro (hx | hz)
      · exact Or.inl (Or.inl hx)
      · by_cases hzw : i ∈ ZW
        · exact Or.inl (Or.inr hzw)
        · exact Or.inr ⟨hz, hzw⟩
  have hjoint : ((b.mutilateSet (X ∪ ZW) x).mutilateSet (Z.filter fun z => z ∉ ZW) x).joint =
      (b.mutilateSet (X ∪ Z) x).joint := by
    rw [joint_mutilateSet_mutilateSet_r3, hunion]
  have hStep1 := not_isDescendant_rule3_r3 b x hZWdef hd
  have hEq : ((b.mutilateSet X x).mutilateSet ZW x).joint =
      (b.mutilateSet (X ∪ ZW) x).joint :=
    joint_mutilateSet_mutilateSet_r3 b X ZW x
  have hMYW : marginal (b.mutilateSet (X ∪ ZW) x).joint ↑(Y ∪ W) x =
      marginal (b.mutilateSet X x).joint ↑(Y ∪ W) x := by
    rw [← hEq]
    exact marginal_mutilateSet_of_not_isDescendant_r3 (b.mutilateSet X x) ZW (Y ∪ W) x hStep1 x
  have hMW : marginal (b.mutilateSet (X ∪ ZW) x).joint ↑W x =
      marginal (b.mutilateSet X x).joint ↑W x := by
    rw [← hEq]
    apply marginal_mutilateSet_of_not_isDescendant_r3
    intro t ht s hs
    exact hStep1 t ht s (Finset.mem_union_right Y hs)
  have hZA : Z.filter (fun z => z ∉ ZW) ⊆ Z := Finset.filter_subset _ _
  have hdZA : (b.mutilateSet (X ∪ ZW) x).DSeparated ↑(Z.filter fun z => z ∉ ZW) ↑Y ↑(X ∪ W) := by
    intro z hz y hy p hp
    have hzZ : z ∈ (Z : Set (Fin n)) := Finset.coe_subset.2 hZA hz
    exact (DSeparated.symm _ hd) z hzZ y hy p hp
  have hcore := marginal_mutilateSet_mul_of_dSeparated_r3 (b.mutilateSet (X ∪ ZW) x) x hdZA
  rw [hjoint] at hcore
  rw [absorb_PXZ_YW_r3 b x, absorb_PXZ_W_r3 b x, absorb_M_YW_r3 b x, absorb_M_W_r3 b x] at hcore
  rw [hMYW, hMW] at hcore
  rw [div_eq_div_iff hwz hw]
  exact hcore

end BayesNet

end Cslib.MachineLearning.GraphicalModels

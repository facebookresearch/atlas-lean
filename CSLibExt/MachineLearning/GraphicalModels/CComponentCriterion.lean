/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.MachineLearning.GraphicalModels.CComponentFactorization
public import CSLibExt.MachineLearning.GraphicalModels.Identifiability
public import Mathlib.Data.Finset.Sort

/-!
# The single-intervention criterion of Tian and Pearl

For a Bayesian network with a set `L` of latent nodes, let `G` be its latent projection onto the
observed nodes `O`, let `x ∈ O`, and let `S^x` be the c-component of `x`. Among networks in
which no latent node is a descendant of an observed node and whose observed law is strictly
positive, the causal effect of `x` on the other observed nodes, `Q[O ∖ {x}]`
(`BayesNet.qFactor`), is identified from the observed law whenever no bidirected path connects
`x` to any of its children, and then

`Q[O ∖ {x}](v) = P(v) / Q[S^x](v) * Σ_x Q[S^x](v)`,

where `Q[S^x]` is computed from the observed law along any topological order of `G` (Tian and
Pearl 2002, Theorem 3 and eq. (43)). Only this sufficient direction is formalized.

## Main definitions

* `ADMG.NoBidirPathToChild G x`: no child of `x` lies in the c-component of `x`.
* `ADMG.cComponentFinset G x`: the c-component of `x` as a vertex set, an element of
  `ADMG.cComponents`.
* `qOfLaw σ S P`: the product over `S` of the conditional ratios of a law `P` along an order
  `σ`.
* `tianFormula G σ x P`: the right-hand side of eq. (43) as a function of the observed law `P`.
* `BayesNet.obsOrder L`: the increasing enumeration of the observed nodes.
* `BayesNet.tianClass L G`: the networks in which no latent node is a descendant of an observed
  node, whose latent projection is `G` and whose observed law is strictly positive.

## Main results

* `BayesNet.qFactor_erase_eq`, `BayesNet.qFactor_erase_eq_prod`,
  `BayesNet.qFactor_erase_mul_qFactor_cComponent`: eqs. (42), (44) and (45) without division,
  for every network.
* `BayesNet.qFactor_erase_eq_div`, `BayesNet.qFactor_erase_eq_tianFormula`: eq. (43).
* `BayesNet.identifiedOn_qFactor_erase`, `BayesNet.identifiedOn_marginal_qFactor_erase`: the
  criterion, for the effect on all other observed nodes and for its marginals `P_x(y)`.
* `BayesNet.latentProjection_dir_iff_edge`: when no latent node is a descendant of an observed
  node, the arrows of the latent projection are the arrows of the network.
* `BayesNet.qFactor_erase_eq_marginal_intervene`: `Q[O ∖ {x}]` is a marginal of the network
  after the intervention `do(x = v x)`.

The bow graph, where the condition fails and the effect is not identified, is in the test file.

## References

* J. Tian and J. Pearl, *A General Identification Condition for Causal Effects*, Proceedings of
  the Eighteenth National Conference on Artificial Intelligence (AAAI-02), AAAI Press (2002),
  567–573.
-/

@[expose] public section

namespace Cslib.MachineLearning.GraphicalModels

open Finset MetaMathlibExt.FiniteWeight

namespace ADMG

variable {V : Type*} (G : ADMG V)

/-- The graph condition of the single-intervention criterion: no bidirected path connects `x`
to any of its children, that is, no child of `x` lies in the c-component of `x` (Tian and
Pearl 2002, Theorem 3). -/
def NoBidirPathToChild (x : V) : Prop :=
  ∀ w, G.dir x w → w ∉ G.cComponent x

open scoped Classical in
/-- The c-component of `x` as a vertex set: the set that `ADMG.cComponents` collects for the
root `x`. Every element of `ADMG.cComponents` has this form (`ADMG.mem_cComponents_iff`), and
`cComponentFinset_mem_cComponents` is the converse. -/
noncomputable def cComponentFinset [Fintype V] (x : V) : Finset V :=
  Finset.univ.filter (· ∈ G.cComponent x)

/-- The c-component of `x` is a c-component of `G`. -/
theorem cComponentFinset_mem_cComponents [Fintype V] [DecidableEq V] (x : V) :
    G.cComponentFinset x ∈ G.cComponents := by
  rw [mem_cComponents_iff]
  exact ⟨x, rfl⟩

end ADMG

section Functional

variable {V α : Type*} [Fintype V] [DecidableEq V] [Fintype α]

/-- The Q-factor of a vertex set `S` computed from a law `P` along an order `σ`: the product
over `i ∈ S` of `P(v_i, v_{<i}) / P(v_{<i})`, where `v_{<i}` is `v` on the vertices before `i`
in `σ` (Tian and Pearl 2002, eq. (29)). For a c-component `S` of a latent projection, a
topological order `σ` of the projection and a strictly positive observed law, this product is
the right-hand side of `BayesNet.qFactor_eq_prod_cond`, so it equals `BayesNet.qFactor`. -/
noncomputable def qOfLaw (σ : V ≃ Fin (Fintype.card V)) (S : Finset V) (P : (V → α) → ℝ)
    (v : V → α) : ℝ :=
  ∏ i ∈ S, marginal P ↑({i} ∪ univ.filter fun u => σ u < σ i) v /
    marginal P ↑(univ.filter fun u => σ u < σ i) v

/-- The identification formula of the single-intervention criterion as a function of the
observed law `P` (Tian and Pearl 2002, eq. (43)): `P(v) / Q(v) * Σ_x Q(v)`, where `Q` is
`qOfLaw` of the c-component of `x` and the sum ranges over the values of `x`, the other
coordinates of `v` fixed. -/
noncomputable def tianFormula (G : ADMG V) (σ : V ≃ Fin (Fintype.card V)) (x : V)
    (P : (V → α) → ℝ) (v : V → α) : ℝ :=
  P v / qOfLaw σ (G.cComponentFinset x) P v *
    marginal (qOfLaw σ (G.cComponentFinset x) P) (↑({x} : Finset V))ᶜ v

end Functional

namespace BayesNet

variable {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α] {n : ℕ}
  (b : BayesNet α n) (L : Finset (Fin n))

omit [Fintype α] [DecidableEq α] [Nonempty α] in
/-- If no latent node is a descendant of an observed node (the semi-Markovian convention of
Tian and Pearl 2002, p. 568), the arrows of the latent projection are the arrows of the network
between observed nodes. So the projection is the causal graph of the source on the observed
nodes, and `ADMG.NoBidirPathToChild` speaks of the children of `x` in the network. -/
theorem latentProjection_dir_iff_edge (hSM : b.NoObservedAncestorOfLatent L)
    (u w : {i : Fin n // i ∉ L}) :
    (b.latentProjection L).dir u w ↔ b.Edge (u : Fin n) (w : Fin n) := by
  constructor
  · intro hdir
    have hlat : b.LatentPath L (u : Fin n) (w : Fin n) :=
      (latentProjection_dir_iff b L u w).mp hdir
    obtain ⟨m, hseg, hedge⟩ := hlat
    rcases Relation.ReflTransGen.cases_tail hseg with rfl | ⟨p, hup, hpm⟩
    · exact hedge
    · have hmL : m ∈ L := hpm.2
      have hseg' : Relation.ReflTransGen (fun x y => b.Edge x y ∧ y ∈ L) (u : Fin n) m :=
        hup.tail hpm
      have hdesc : b.IsDescendant (u : Fin n) m := reflTransGen_r_edges b L hseg'
      exact absurd hdesc (hSM m hmL (u : Fin n) u.2)
  · intro hedge
    exact (latentProjection_dir_iff b L u w).mpr (latentPath_of_edge_direct b L _ _ hedge)

/-- The increasing enumeration of the observed nodes. -/
noncomputable def obsOrder : {i : Fin n // i ∉ L} ≃ Fin (Fintype.card {i : Fin n // i ∉ L}) :=
  (Fintype.orderIsoFinOfCardEq {i : Fin n // i ∉ L} rfl).symm.toEquiv

omit [Fintype α] [DecidableEq α] [Nonempty α] in
/-- The increasing enumeration of the observed nodes is a topological order of the latent
projection of every network with latent set `L`. -/
theorem obsOrder_topological :
    ∀ ⦃u w⦄, (b.latentProjection L).dir u w → obsOrder L u < obsOrder L w := by
  intro u w h
  have hlat : b.LatentPath L (u : Fin n) (w : Fin n) := (latentProjection_dir_iff b L u w).mp h
  have hlt : (u : Fin n) < (w : Fin n) := LatentPath.lt b L hlat
  have huv : u < w := hlt
  exact (OrderIso.lt_iff_lt (Fintype.orderIsoFinOfCardEq {i : Fin n // i ∉ L} rfl).symm).mpr huv

private theorem crit_aux_compl_erase_univ {V : Type*} [Fintype V] [DecidableEq V] (x : V) :
    (univ.erase x)ᶜ = {x} := by
  ext y
  constructor
  · intro hy
    rw [Finset.mem_compl, Finset.mem_erase] at hy
    rw [Finset.mem_singleton]
    by_contra h
    exact hy ⟨h, Finset.mem_univ y⟩
  · intro hy
    rw [Finset.mem_singleton] at hy
    subst hy
    rw [Finset.mem_compl, Finset.mem_erase]
    exact fun ⟨h, _⟩ => h rfl

private theorem crit_aux_extendObs_obs {α : Type*} {n : ℕ} [Nonempty α] (L : Finset (Fin n))
    (v : {i : Fin n // i ∉ L} → α) (x : {i : Fin n // i ∉ L}) :
    extendObs L v (↑x) = v x := by
  unfold extendObs
  rw [dite_eq_right x.2]

private theorem crit_aux_joint_mutilate_intervene {α : Type*} {n : ℕ} [Nonempty α] [DecidableEq α]
    (b : BayesNet α n) (L : Finset (Fin n)) (x : {i : Fin n // i ∉ L})
    (v : {i : Fin n // i ∉ L} → α) (y : Fin n → α) :
    (b.mutilateSet ({((x : Fin n))}) (extendObs L v)).joint y
      = (b.intervene (x : Fin n) (v x)).joint y := by
  rw [joint_mutilateSet, joint_intervene]
  have hext : (extendObs L v) (↑x) = v x := crit_aux_extendObs_obs L v x
  have hmem : (↑x) ∈ ({((x : Fin n))} : Finset (Fin n)) := Finset.mem_singleton_self _
  have hFerase : (∏ j ∈ univ.erase (↑x), (if j ∈ ({((x : Fin n))} : Finset (Fin n)) then (if y j = (extendObs L v) j then (1:ℝ) else 0) else (b.cpt j (b.paVal j y)).weights (y j))) = ∏ j ∈ univ.erase (↑x), (b.cpt j (b.paVal j y)).weights (y j) := by
    apply Finset.prod_congr rfl
    intro j hj
    have hne : j ≠ (↑x) := Finset.ne_of_mem_erase hj
    have hnot : j ∉ ({((x : Fin n))} : Finset (Fin n)) := by simp [Finset.mem_singleton, hne]
    simp only [hnot, ite_false]
  rw [← Finset.mul_prod_erase univ _ (Finset.mem_univ (↑x : Fin n))]
  show ((if (↑x) ∈ ({((x : Fin n))} : Finset (Fin n)) then (if y (↑x) = (extendObs L v) (↑x) then (1:ℝ) else 0) else (b.cpt (↑x) (b.paVal (↑x) y)).weights (y (↑x))) * ∏ j ∈ univ.erase (↑x), (if j ∈ ({((x : Fin n))} : Finset (Fin n)) then (if y j = (extendObs L v) j then (1:ℝ) else 0) else (b.cpt j (b.paVal j y)).weights (y j))) = (if y (↑x) = v x then ∏ j ∈ univ.erase (↑x), (b.cpt j (b.paVal j y)).weights (y j) else 0)
  simp only [hmem, ite_true, hext, hFerase]
  by_cases h : y (↑x) = v x <;> simp [h]

/-- `Q[O ∖ {x}](v)` is the probability of the values of `v` on the observed nodes other than `x`
after the intervention `do(x = v x)` (`BayesNet.intervene`): the Q-factor of the observed nodes
other than `x` is the causal effect of `x` on them. -/
theorem qFactor_erase_eq_marginal_intervene (x : {i : Fin n // i ∉ L})
    (v : {i : Fin n // i ∉ L} → α) :
    b.qFactor L (univ.erase x) v =
      marginal (b.intervene (x : Fin n) (v x)).joint
        ↑((univ.erase x).map (Function.Embedding.subtype _)) (extendObs L v) := by
  unfold qFactor
  have hcompl : ((univ.erase x)ᶜ).map (Function.Embedding.subtype _) = {((x : Fin n))} := by
    rw [crit_aux_compl_erase_univ]
    simp only [Finset.map_singleton, Function.Embedding.subtype_apply]
  rw [hcompl]
  have hJ : (b.mutilateSet ({((x : Fin n))}) (extendObs L v)).joint
      = (b.intervene (x : Fin n) (v x)).joint :=
    funext fun y => crit_aux_joint_mutilate_intervene b L x v y
  rw [hJ]

/-- Under the graph condition, the effect of `x` on the other observed nodes factors without
division: `Q[O ∖ {x}](v) = (Σ_x Q[S^x])(v) * Q[O ∖ S^x](v)`, where `S^x` is the c-component of
`x` and the sum ranges over the values of `x` (Tian and Pearl 2002, eqs. (42) and (44)). No
positivity or semi-Markovian hypothesis is needed. -/
theorem qFactor_erase_eq {x : {i : Fin n // i ∉ L}}
    (hx : (b.latentProjection L).NoBidirPathToChild x) (v : {i : Fin n // i ∉ L} → α) :
    b.qFactor L (univ.erase x) v =
      marginal (b.qFactor L ((b.latentProjection L).cComponentFinset x))
          (↑({x} : Finset {i : Fin n // i ∉ L}))ᶜ v *
        b.qFactor L (univ \ (b.latentProjection L).cComponentFinset x) v := by
  classical
  have hxS : x ∈ (b.latentProjection L).cComponentFinset x := by
    have hreach : (b.latentProjection L).bidir.Reachable x x := SimpleGraph.Reachable.refl x
    have hmem : x ∈ (b.latentProjection L).cComponent x :=
      (ADMG.mem_cComponent_iff _).mpr hreach
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ x, hmem⟩
  have hTH : ((b.latentProjection L).cComponentFinset x).erase x ⊆ univ.erase x := by
    intro u hu
    simp only [Finset.mem_erase] at hu ⊢
    exact ⟨hu.1, Finset.mem_univ u⟩
  have hS : (b.latentProjection L).cComponentFinset x ∈ (b.latentProjection L).cComponents :=
    ADMG.cComponentFinset_mem_cComponents (b.latentProjection L) x
  have hsep0 := cComponent_no_adj_compl b L hS
  have hsep : ∀ u ∈ ((b.latentProjection L).cComponentFinset x).erase x,
      ∀ w ∈ (univ.erase x) \ (((b.latentProjection L).cComponentFinset x).erase x),
      ¬ (b.latentProjection L).bidir.Adj u w := by
    intro u hu w hw
    simp only [Finset.mem_sdiff, Finset.mem_erase] at hw
    obtain ⟨⟨hwx, -⟩, hwS⟩ := hw
    exact hsep0 u (Finset.mem_erase.mp hu).2 w
      (Finset.mem_sdiff.mpr ⟨Finset.mem_univ w, fun h => hwS ⟨hwx, h⟩⟩)
  have hmul := qFactor_eq_mul_of_not_adj b L hTH hsep v
  have hsdiff : (univ.erase x) \ (((b.latentProjection L).cComponentFinset x).erase x)
      = univ \ (b.latentProjection L).cComponentFinset x := by
    ext u
    simp only [Finset.mem_sdiff, Finset.mem_erase, Finset.mem_univ, true_and, and_true]
    constructor
    · rintro ⟨hux, h⟩ hSu
      exact h ⟨hux, hSu⟩
    · intro huS
      by_cases hux : u = x
      · rw [hux] at huS ⊢
        exact absurd hxS huS
      · exact ⟨hux, fun h => huS h.2⟩
  have hAH : ((b.latentProjection L).cComponentFinset x).erase x
      ⊆ (b.latentProjection L).cComponentFinset x :=
    fun u hu => (Finset.mem_erase.mp hu).2
  have hanc : ∀ ⦃u w⦄, (b.latentProjection L).dir u w →
      u ∈ (b.latentProjection L).cComponentFinset x →
      w ∈ (((b.latentProjection L).cComponentFinset x).erase x) →
      u ∈ (((b.latentProjection L).cComponentFinset x).erase x) := by
    intro u w hdir huS hwS
    simp only [Finset.mem_erase] at hwS ⊢
    refine ⟨?_, huS⟩
    intro heq
    rw [heq] at hdir
    exact hx w hdir (Finset.mem_filter.mp hwS.2).2
  have hancestral := marginal_qFactor_of_ancestral b L hAH hanc v
  have hsdiff2 : (b.latentProjection L).cComponentFinset x
      \ (((b.latentProjection L).cComponentFinset x).erase x) = {x} := by
    ext u
    simp only [Finset.mem_sdiff, Finset.mem_erase, Finset.mem_singleton]
    constructor
    · rintro ⟨huS, h⟩
      by_contra hux
      exact h ⟨hux, huS⟩
    · intro heq
      rw [heq]
      exact ⟨hxS, fun h => h.1 rfl⟩
  rw [hsdiff] at hmul
  rw [hsdiff2] at hancestral
  rw [hmul, ← hancestral]

/-- `qFactor_erase_eq` with `Q[O ∖ S^x]` written as the product of the Q-factors of the other
c-components (Tian and Pearl 2002, eq. (42)). -/
theorem qFactor_erase_eq_prod {x : {i : Fin n // i ∉ L}}
    (hx : (b.latentProjection L).NoBidirPathToChild x) (v : {i : Fin n // i ∉ L} → α) :
    b.qFactor L (univ.erase x) v =
      marginal (b.qFactor L ((b.latentProjection L).cComponentFinset x))
          (↑({x} : Finset {i : Fin n // i ∉ L}))ᶜ v *
        ∏ S ∈ (b.latentProjection L).cComponents.erase
            ((b.latentProjection L).cComponentFinset x), b.qFactor L S v := by
  classical
  have hN5 := qFactor_erase_eq b L hx v
  have hS : (b.latentProjection L).cComponentFinset x ∈ (b.latentProjection L).cComponents :=
    ADMG.cComponentFinset_mem_cComponents (b.latentProjection L) x
  have hshare : ∀ {T T' : Finset {i : Fin n // i ∉ L}},
      T ∈ (b.latentProjection L).cComponents → T' ∈ (b.latentProjection L).cComponents →
      (∃ u, u ∈ T ∧ u ∈ T') → T = T' := by
    intro T T' hT hT' ⟨u, huT, huT'⟩
    obtain ⟨a, ha⟩ := (ADMG.mem_cComponents_iff (b.latentProjection L)).mp hT
    obtain ⟨c, hc⟩ := (ADMG.mem_cComponents_iff (b.latentProjection L)).mp hT'
    have hu1 : u ∈ Finset.univ.filter (· ∈ (b.latentProjection L).cComponent a) := by
      rw [ha]; exact huT
    have hu2 : u ∈ Finset.univ.filter (· ∈ (b.latentProjection L).cComponent c) := by
      rw [hc]; exact huT'
    have hfac := ADMG.filter_cComponent_eq_of_shared (b.latentProjection L) hu1 hu2
    rw [ha, hc] at hfac
    exact hfac
  have hdisj : (((b.latentProjection L).cComponents.erase
      ((b.latentProjection L).cComponentFinset x)) : Set (Finset {i : Fin n // i ∉ L})).PairwiseDisjoint id := by
    intro T hT T' hT' hne
    simp only [Finset.mem_coe, Finset.mem_erase] at hT hT'
    show Disjoint T T'
    refine Finset.disjoint_left.mpr ?_
    intro u huT huT'
    exact hne (hshare hT.2 hT'.2 ⟨u, huT, huT'⟩)
  have hcov : ((b.latentProjection L).cComponents.erase
      ((b.latentProjection L).cComponentFinset x)).biUnion id =
      univ \ (b.latentProjection L).cComponentFinset x := by
    ext u
    simp only [Finset.mem_biUnion, Finset.mem_erase, Finset.mem_sdiff, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨T, ⟨hneT, hTc⟩, huT⟩ huS
      exact hneT (hshare hTc hS ⟨u, huT, huS⟩)
    · intro huS
      have huu : u ∈ (b.latentProjection L).cComponentFinset u := by
        have hreach : (b.latentProjection L).bidir.Reachable u u := SimpleGraph.Reachable.refl u
        have hmem : u ∈ (b.latentProjection L).cComponent u :=
          (ADMG.mem_cComponent_iff _).mpr hreach
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ u, hmem⟩
      refine ⟨(b.latentProjection L).cComponentFinset u,
        ⟨?_, ADMG.cComponentFinset_mem_cComponents (b.latentProjection L) u⟩, huu⟩
      intro heq
      rw [heq] at huu
      exact huS huu
  have hsep : ∀ T ∈ (b.latentProjection L).cComponents.erase
      ((b.latentProjection L).cComponentFinset x),
      ∀ T' ∈ (b.latentProjection L).cComponents.erase
      ((b.latentProjection L).cComponentFinset x),
      T ≠ T' → ∀ u ∈ T, ∀ w ∈ T', ¬ (b.latentProjection L).bidir.Adj u w := by
    intro T hT T' hT' hne u huT w hwT'
    simp only [Finset.mem_erase] at hT hT'
    refine (cComponent_no_adj_compl b L hT.2 u huT) w
      (Finset.mem_sdiff.mpr ⟨Finset.mem_univ w, ?_⟩)
    intro hwT
    exact hne (hshare hT.2 hT'.2 ⟨w, hwT, hwT'⟩)
  have hprod := qFactor_eq_prod_of_not_adj b L
    ((b.latentProjection L).cComponents.erase ((b.latentProjection L).cComponentFinset x))
    hdisj hcov hsep v
  rw [hN5, hprod]

/-- Under the graph condition, `Q[O ∖ {x}](v) * Q[S^x](v) = (Σ_x Q[S^x])(v) * P(v)`: eq. (45)
of Tian and Pearl (2002) without division, for every network. -/
theorem qFactor_erase_mul_qFactor_cComponent {x : {i : Fin n // i ∉ L}}
    (hx : (b.latentProjection L).NoBidirPathToChild x) (v : {i : Fin n // i ∉ L} → α) :
    b.qFactor L (univ.erase x) v * b.qFactor L ((b.latentProjection L).cComponentFinset x) v =
      marginal (b.qFactor L ((b.latentProjection L).cComponentFinset x))
          (↑({x} : Finset {i : Fin n // i ∉ L}))ᶜ v * b.observedLaw L v := by
  have hS : (b.latentProjection L).cComponentFinset x ∈ (b.latentProjection L).cComponents :=
    ADMG.cComponentFinset_mem_cComponents (b.latentProjection L) x
  have hsep := cComponent_no_adj_compl b L hS
  have hmul := qFactor_eq_mul_of_not_adj b L (Finset.subset_univ _) hsep v
  have huniv := congrFun (qFactor_univ b L) v
  have herase := qFactor_erase_eq b L hx v
  rw [herase, ← huniv, hmul]
  ring

/-- Under the graph condition, at every `v` with `P(v) > 0`,
`Q[O ∖ {x}](v) = P(v) / Q[S^x](v) * (Σ_x Q[S^x])(v)` (Tian and Pearl 2002, eq. (43)). -/
theorem qFactor_erase_eq_div {x : {i : Fin n // i ∉ L}}
    (hx : (b.latentProjection L).NoBidirPathToChild x) {v : {i : Fin n // i ∉ L} → α}
    (hv : 0 < b.observedLaw L v) :
    b.qFactor L (univ.erase x) v =
      b.observedLaw L v / b.qFactor L ((b.latentProjection L).cComponentFinset x) v *
        marginal (b.qFactor L ((b.latentProjection L).cComponentFinset x))
          (↑({x} : Finset {i : Fin n // i ∉ L}))ᶜ v := by
  have hQpos := qFactor_pos b L hv ((b.latentProjection L).cComponentFinset x)
  have hne : b.qFactor L ((b.latentProjection L).cComponentFinset x) v ≠ 0 :=
    ne_of_gt hQpos
  have hN7 := qFactor_erase_mul_qFactor_cComponent b L hx v
  have hdiv : b.qFactor L (univ.erase x) v =
      (marginal (b.qFactor L ((b.latentProjection L).cComponentFinset x))
          (↑({x} : Finset {i : Fin n // i ∉ L}))ᶜ v * b.observedLaw L v) /
        b.qFactor L ((b.latentProjection L).cComponentFinset x) v :=
    (eq_div_iff hne).mpr hN7
  rw [hdiv]
  ring

/-- **The single-intervention criterion, formula form** (Tian and Pearl 2002, Theorem 3,
sufficient direction, and eq. (43)): under the graph condition and a strictly positive observed
law, the effect of `x` on the other observed nodes is `tianFormula` of the observed law, for
every topological order `σ` of the latent projection. The formula depends only on the observed
law, the projection, `σ` and `x`. -/
theorem qFactor_erase_eq_tianFormula {x : {i : Fin n // i ∉ L}}
    (hx : (b.latentProjection L).NoBidirPathToChild x)
    (σ : {i : Fin n // i ∉ L} ≃ Fin (Fintype.card {i : Fin n // i ∉ L}))
    (hσ : ∀ ⦃u w⦄, (b.latentProjection L).dir u w → σ u < σ w)
    (hpos : ∀ v, 0 < b.observedLaw L v) :
    b.qFactor L (univ.erase x) = tianFormula (b.latentProjection L) σ x (b.observedLaw L) := by
  funext v
  have hS : (b.latentProjection L).cComponentFinset x ∈ (b.latentProjection L).cComponents :=
    ADMG.cComponentFinset_mem_cComponents (b.latentProjection L) x
  have hQeq : b.qFactor L ((b.latentProjection L).cComponentFinset x) =
      qOfLaw σ ((b.latentProjection L).cComponentFinset x) (b.observedLaw L) := by
    funext w
    exact qFactor_eq_prod_cond b L σ hσ hS (hpos w)
  have hN8 := qFactor_erase_eq_div b L hx (hpos v)
  rw [hQeq] at hN8
  exact hN8

/-- The networks of the identification problem for a graph `G` on the observed nodes (Tian and
Pearl 2002, Definition 1): no latent node is a descendant of an observed node (the source's
semi-Markovian convention, p. 568), the latent projection is `G`, and the observed law is
strictly positive. -/
def tianClass (G : ADMG {i : Fin n // i ∉ L}) : Set (BayesNet α n) :=
  {b | b.NoObservedAncestorOfLatent L ∧ b.latentProjection L = G ∧ ∀ v, 0 < b.observedLaw L v}

/-- **The single-intervention criterion** (Tian and Pearl 2002, Theorem 3, sufficient
direction): if no bidirected path connects `x` to any of its children in `G`, the effect of `x`
on the other observed nodes is identified from the observed law on `tianClass L G`. -/
theorem identifiedOn_qFactor_erase {G : ADMG {i : Fin n // i ∉ L}} {x : {i : Fin n // i ∉ L}}
    (hx : G.NoBidirPathToChild x) :
    IdentifiedOn (tianClass (α := α) L G) (fun b : BayesNet α n => b.observedLaw L)
      (fun b => b.qFactor L (univ.erase x)) := by
  refine IdentifiedOn.of_eq_comp (tianFormula G (obsOrder L) x) ?_
  intro b hb
  obtain ⟨-, hproj, hpos⟩ := hb
  subst hproj
  exact qFactor_erase_eq_tianFormula b L hx (obsOrder L) (obsOrder_topological b L) hpos

/-- For every set `Y` of observed nodes, `P_x(y)` is identified under the same condition: the
marginal on `Y` of the effect of `do(x = v x)`, with `x` itself kept at the intervention value
(Tian and Pearl 2002, p. 572). -/
theorem identifiedOn_marginal_qFactor_erase {G : ADMG {i : Fin n // i ∉ L}}
    {x : {i : Fin n // i ∉ L}} (hx : G.NoBidirPathToChild x) (Y : Finset {i : Fin n // i ∉ L}) :
    IdentifiedOn (tianClass (α := α) L G) (fun b : BayesNet α n => b.observedLaw L)
      (fun b => marginal (b.qFactor L (univ.erase x)) ↑(insert x Y)) := by
  intro b hb b' hb' hobs
  have hQ : b.qFactor L (univ.erase x) = b'.qFactor L (univ.erase x) :=
    identifiedOn_qFactor_erase L hx b hb b' hb' hobs
  show marginal (b.qFactor L (univ.erase x)) ↑(insert x Y) =
    marginal (b'.qFactor L (univ.erase x)) ↑(insert x Y)
  rw [hQ]

end BayesNet

end Cslib.MachineLearning.GraphicalModels

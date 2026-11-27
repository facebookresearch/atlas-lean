/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.MachineLearning.GraphicalModels.IdentificationSoundness
public import CSLibExtTest.MachineLearning.GraphicalModels.CComponentCriterionTests
public import CSLibExtTest.MachineLearning.GraphicalModels.CausalAdjustmentTests
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FinCases

/-!
# Tests for the soundness of the ID algorithm

* Line 1, for every network: with nothing intervened, `ADMG.ID` returns the observed marginal,
  and that marginal is the effect of the empty intervention (`ID_empty`,
  `observed_marginal_eq_doMarginal_empty`).
* The chain `X → Y` with no latent node (`chainNet`): its observed law is strictly positive, so
  the positivity hypothesis of `BayesNet.ID_sound` is satisfiable; `ADMG.ID` reaches line 6 and
  returns `P(y | x)`; conditioning on `X` equals intervening on `X`; and
  `P_{X = 1}(Y = 1) = 3 / 4`, computed from the surgery definition alone, so the soundness
  instance could have failed; and the effect of `do(X)` on `Y` is the Q-factor of `{Y}`
  (`chain_doMarginal_eq_qFactor`).
* The front-door network `U → X → M → Y`, `U → Y` of the adjustment tests (`fdNet`), with the
  confounder `U` latent: its latent projection is `X → M → Y`, `X ↔ Y`, its observed law is
  strictly positive, and `ADMG.ID` succeeds for `P_x(y)` (line 4 on the c-components `{M}` and
  `{Y}` of `G[{M, Y}]`, then lines 2 and 6 for `{M}` and lines 7, 2 and 1 for `{Y}`). By
  `BayesNet.ID_sound` the returned expression evaluates on the observed law to
  `P_{X = 1}(Y = 1) = 17 / 32`, the value computed from the network's tables by the surgery
  definition alone (`fd_doMarginal_true`, `fd_ID_eval_true`).
* The bow graph `X → Y`, `X ↔ Y` with a latent common cause (the bow arc graph of Shpitser and
  Pearl, AAAI 2006, Theorem 1): `ADMG.ID` fails at line 5 with the pair `(O, O ∖ {X})`, so
  `BayesNet.ID_sound` has no instance there. Nothing is claimed about failure outputs; the
  non-identification of this one query is the separate test
  `LatentConfounding.not_identifiedOn_bow`.
-/

@[expose] public section

namespace Cslib.MachineLearning.IdentificationSoundnessTests

open Cslib.MachineLearning.GraphicalModels Finset MetaMathlibExt.FiniteWeight

/-! ### Line 1, for every network -/

section Empty

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- With nothing intervened, `ID` returns the marginal of the observed law (line 1). -/
theorem ID_empty (G : ADMG V) (σ : V ≃ Fin (Fintype.card V)) (Y : Finset V) :
    G.ID σ Y ∅ = .ok (.sum (univ \ Y) .obs) := by
  unfold ADMG.ID ADMG.idRec
  simp

end Empty

/-- Soundness through line 1, for every network: the observed marginal is the effect of the
empty intervention (the base case `x = ∅` of Shpitser and Pearl, AAAI 2006, Theorem 5). -/
theorem observed_marginal_eq_doMarginal_empty {α : Type*} [Fintype α] [DecidableEq α]
    [Nonempty α] {n : ℕ} (b : BayesNet α n) (L : Finset (Fin n)) (Y : Finset {i : Fin n // i ∉ L})
    (v : {i : Fin n // i ∉ L} → α) :
    marginal (b.observedLaw L) (↑(univ \ Y))ᶜ v = b.doMarginal L ∅ Y v := by
  rw [BayesNet.doMarginal_eq_marginal_qFactor, Finset.sdiff_empty, BayesNet.qFactor_univ]

/-! ### The chain `X → Y` -/

/-- A Bernoulli law on `Bool`, `true` with probability `p` (the criterion tests' private helper,
restated). -/
noncomputable def bern (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) : Convexity.StdSimplex ℝ Bool where
  weights := Finsupp.equivFunOnFinite.symm (fun b => if b then p else 1 - p)
  nonneg := by
    intro b
    simp only [Finsupp.coe_zero, Pi.zero_apply]
    cases b <;> simp_all
  total := by
    rw [Finsupp.sum_fintype _ _ fun _ => rfl]
    simp

/-- The chain `X → Y` on `Fin 2` (`X = 0`, `Y = 1`) with no latent node: `X` is fair,
`P(Y = 1 | X = 1) = 3 / 4` and `P(Y = 1 | X = 0) = 1 / 4`. -/
noncomputable def chainNet : BayesNet Bool 2 where
  pa := fun _ => Finset.univ
  cpt := fun k z =>
    match k with
    | ⟨0, _⟩ => bern (1 / 2) (by norm_num) (by norm_num)
    | ⟨1, _⟩ =>
      if z ⟨0, Finset.mem_univ 0⟩ then bern (3 / 4) (by norm_num) (by norm_num)
      else bern (1 / 4) (by norm_num) (by norm_num)
    | ⟨m + 2, h⟩ => False.elim (by omega)

/-- The observed nodes of the chain: all of them. -/
abbrev CObs : Type := {i : Fin 2 // i ∉ (∅ : Finset (Fin 2))}

/-- The node `X = 0`. -/
def cX : CObs := ⟨0, by simp⟩

/-- The node `Y = 1`. -/
def cY : CObs := ⟨1, by simp⟩

/-- Every observed node of the chain is `X` or `Y`. -/
theorem cObs_cases : ∀ u : CObs, u = cX ∨ u = cY := by
  decide

/-- The nodes `X` and `Y` differ. -/
theorem cX_ne_cY : cX ≠ cY := by
  decide

/-- The latent projection of the chain has the arrow `X → Y`. -/
theorem chain_dir : (chainNet.latentProjection ∅).dir cX cY := by
  rw [BayesNet.latentProjection_dir_iff]
  apply BayesNet.latentPath_of_edge_direct
  exact ⟨by decide, Finset.mem_univ _⟩

/-- With no latent node, the latent projection of the chain has no bidirected edge. -/
theorem chain_not_bidir (u w : CObs) : ¬ (chainNet.latentProjection ∅).bidir.Adj u w := by
  rw [BayesNet.latentProjection_bidir_adj_iff]
  rintro ⟨-, t, ht, _, _⟩
  simp at ht

/-- With no bidirected edge, the c-component of `u` inside any vertex set lies in `{u}`. -/
theorem chain_compIn_subset (D : Finset CObs) (u : CObs) :
    (chainNet.latentProjection ∅).compIn D u ⊆ {u} := by
  have hno : ∀ a b : CObs, ¬ ((chainNet.latentProjection ∅).induce ↑D).bidir.Adj a b := by
    intro a b hadj
    rcases hadj.2 with h | h
    · exact chain_not_bidir a b h.2.2
    · exact chain_not_bidir b a h.2.2
  intro w hw
  simp only [ADMG.compIn, Finset.mem_filter, Finset.mem_singleton] at hw ⊢
  rw [ADMG.mem_cComponent_iff] at hw
  have hreach := hw.2
  rcases hreach with rfl | ⟨hadj, _⟩
  · rfl
  · exact absurd hadj (hno _ _)

/-- The table of `X`: a fair coin. -/
theorem chainNet_cpt_zero (z : chainNet.pa 0 → Bool) :
    chainNet.cpt 0 z = bern (1 / 2) (by norm_num) (by norm_num) := by
  rfl

/-- The table of `Y` given the value of `X`. -/
theorem chainNet_cpt_one (z : chainNet.pa 1 → Bool) :
    chainNet.cpt 1 z = if z ⟨⟨0, by decide⟩, Finset.mem_univ _⟩ then
      bern (3 / 4) (by norm_num) (by norm_num) else bern (1 / 4) (by norm_num) (by norm_num) := by
  rfl

/-- Every table entry of the chain is positive. -/
theorem chainNet_cpt_pos (k : Fin 2) (z : chainNet.pa k → Bool) (b : Bool) :
    0 < (chainNet.cpt k z).weights b := by
  have hk : k.val = 0 ∨ k.val = 1 := by have hlt := k.isLt; omega
  rcases hk with hk | hk
  · have hk0 : k = 0 := Fin.ext hk
    subst hk0
    rw [chainNet_cpt_zero]
    cases b <;> simp [bern]
    norm_num
  · have hk1 : k = 1 := Fin.ext hk
    subst hk1
    rw [chainNet_cpt_one]
    split <;> cases b <;> simp [bern] <;> norm_num

/-- The chain network has a strictly positive observed law, so the positivity hypothesis of
`BayesNet.ID_sound` is satisfiable. -/
theorem chainNet_observedLaw_pos : ∀ v, 0 < chainNet.observedLaw (∅ : Finset (Fin 2)) v := by
  intro v
  simp only [BayesNet.observedLaw]
  have hU : ((∅ : Finset (Fin 2))ᶜ : Finset (Fin 2)) = Finset.univ := Finset.compl_empty
  rw [hU, Finset.coe_univ, marginal_univ, BayesNet.joint_eq_prod, Fin.prod_univ_two]
  exact mul_pos (chainNet_cpt_pos _ _ _) (chainNet_cpt_pos _ _ _)

/-- `ID` on the chain's projection passes lines 1–5 (none of their guards holds) and returns
`P(y | x)` at line 6. -/
theorem chain_ID :
    (chainNet.latentProjection ∅).ID (BayesNet.obsOrder (∅ : Finset (Fin 2))) {cY} {cX} =
      .ok (.sum ((univ \ {cX}) \ {cY})
        (ADMG.condChain (BayesNet.obsOrder (∅ : Finset (Fin 2))) univ (univ \ {cX}) .obs)) := by
  have hAnc : (chainNet.latentProjection ∅).ancIn univ {cY} = univ := by
    rw [Finset.eq_univ_iff_forall]
    intro u
    simp only [ADMG.ancIn, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_singleton]
    rcases cObs_cases u with rfl | rfl
    · exact ⟨cY, rfl, Relation.ReflTransGen.single
        ⟨Finset.mem_univ _, Finset.mem_univ _, chain_dir⟩⟩
    · exact ⟨cY, rfl, Relation.ReflTransGen.refl⟩
  have hYX : ¬ cY = cX := fun h => cX_ne_cY h.symm
  have hCut : (chainNet.latentProjection ∅).ancCut univ {cX} {cY} = univ := by
    rw [Finset.eq_univ_iff_forall]
    intro u
    simp only [ADMG.ancCut, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_singleton]
    rcases cObs_cases u with rfl | rfl
    · exact ⟨cY, rfl, Relation.ReflTransGen.single
        ⟨⟨Finset.mem_univ _, Finset.mem_univ _, chain_dir⟩, hYX⟩⟩
    · exact ⟨cY, rfl, Relation.ReflTransGen.refl⟩
  have hDX : (univ : Finset CObs) \ {cX} = {cY} := by
    ext w
    simp only [Finset.mem_sdiff, Finset.mem_univ, Finset.mem_singleton, true_and]
    constructor
    · intro hw
      rcases cObs_cases w with rfl | rfl
      · exact absurd rfl hw
      · rfl
    · rintro rfl
      exact fun h => cX_ne_cY h.symm
  have hCompY : (chainNet.latentProjection ∅).compIn {cY} cY = {cY} := by
    apply subset_antisymm (chain_compIn_subset _ _)
    intro w hw
    rw [Finset.mem_singleton] at hw
    subst hw
    exact ADMG.compIn_self_mem _ (Finset.mem_singleton_self _)
  have hCompYU : (chainNet.latentProjection ∅).compIn univ cY = {cY} := by
    apply subset_antisymm (chain_compIn_subset _ _)
    intro w hw
    rw [Finset.mem_singleton] at hw
    subst hw
    exact ADMG.compIn_self_mem _ (Finset.mem_univ _)
  have hUnivNe : ∀ v : CObs, (chainNet.latentProjection ∅).compIn univ v ≠ univ := by
    intro v hcon
    have hsub := chain_compIn_subset univ v
    rw [hcon] at hsub
    rcases cObs_cases v with rfl | rfl
    · have hmem : cY ∈ ({cX} : Finset CObs) := hsub (Finset.mem_univ cY)
      rw [Finset.mem_singleton] at hmem
      exact cX_ne_cY hmem.symm
    · have hmem : cX ∈ ({cY} : Finset CObs) := hsub (Finset.mem_univ cX)
      rw [Finset.mem_singleton] at hmem
      exact cX_ne_cY hmem
  have g1 : ({cX} : Finset CObs) ≠ ∅ := by simp
  have g2 : ¬ ((chainNet.latentProjection ∅).ancIn univ {cY} ≠ univ) := by simp [hAnc]
  have g3 : ¬ ((((univ : Finset CObs) \ {cX}) \
      (chainNet.latentProjection ∅).ancCut univ {cX} {cY}).Nonempty) := by
    rw [hCut]
    rintro ⟨x, hx⟩
    simp at hx
  have g4 : ((univ : Finset CObs) \ {cX}) ∈
      (chainNet.latentProjection ∅).cComponentsIn ((univ : Finset CObs) \ {cX}) := by
    rw [hDX]
    simp only [ADMG.cComponentsIn, Finset.mem_image, Finset.mem_singleton]
    exact ⟨cY, rfl, hCompY⟩
  have g4n : ¬ (((univ : Finset CObs) \ {cX}) ∉
      (chainNet.latentProjection ∅).cComponentsIn ((univ : Finset CObs) \ {cX})) :=
    fun h => h g4
  have g5 : (univ : Finset CObs) ∉ (chainNet.latentProjection ∅).cComponentsIn univ := by
    simp only [ADMG.cComponentsIn, Finset.mem_image, Finset.mem_univ, true_and]
    rintro ⟨v, hcon⟩
    exact hUnivNe v hcon
  have g6 : ((univ : Finset CObs) \ {cX}) ∈
      (chainNet.latentProjection ∅).cComponentsIn univ := by
    rw [hDX]
    simp only [ADMG.cComponentsIn, Finset.mem_image, Finset.mem_univ, true_and]
    exact ⟨cY, hCompYU⟩
  unfold ADMG.ID ADMG.idRec
  rw [ite_eq_right g1, dite_eq_right g2, dite_eq_right g3, dite_eq_right g4n,
    dite_eq_right g5, ite_eq_left g6]

/-- Soundness on the chain: conditioning on `X` equals intervening on `X`,
`P(x, y) / P(x) = P_x(y)`. -/
theorem chain_cond_eq_doMarginal (v : CObs → Bool) :
    chainNet.observedLaw ∅ v / marginal (chainNet.observedLaw ∅) ↑({cX} : Finset CObs) v =
      chainNet.doMarginal ∅ {cX} {cY} v := by
  have hXY : Disjoint ({cX} : Finset CObs) {cY} := by
    rw [Finset.disjoint_singleton]
    exact cX_ne_cY
  have hID := BayesNet.ID_sound chainNet (∅ : Finset (Fin 2))
    (hσ := BayesNet.obsOrder_topological chainNet ∅)
    (hpos := chainNet_observedLaw_pos) (hXY := hXY) (h := chain_ID) v
  rw [← hID]
  have hS : ((univ \ {cX}) \ {cY} : Finset CObs) = ∅ := by
    rw [Finset.eq_empty_iff_forall_notMem]
    intro w hw
    simp only [Finset.mem_sdiff, Finset.mem_univ, Finset.mem_singleton, true_and] at hw
    rcases cObs_cases w with rfl | rfl
    · exact hw.1 rfl
    · exact hw.2 rfl
  simp only [IdExpr.eval, hS, Finset.coe_empty, Set.compl_empty, marginal_univ]
  rw [ADMG.condChain_eval]
  have hDX : ((univ : Finset CObs) \ {cX}) = {cY} := by
    ext w
    simp only [Finset.mem_sdiff, Finset.mem_univ, Finset.mem_singleton, true_and]
    constructor
    · intro hw
      rcases cObs_cases w with rfl | rfl
      · exact absurd rfl hw
      · rfl
    · rintro rfl
      exact fun h => cX_ne_cY h.symm
  rw [hDX, Finset.prod_singleton]
  have htop : BayesNet.obsOrder (∅ : Finset (Fin 2)) cX < BayesNet.obsOrder ∅ cY :=
    BayesNet.obsOrder_topological chainNet ∅ chain_dir
  have hFilt : (univ.filter fun u : CObs =>
      BayesNet.obsOrder (∅ : Finset (Fin 2)) u < BayesNet.obsOrder ∅ cY) = {cX} := by
    ext u
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    rcases cObs_cases u with rfl | rfl
    · simp [htop]
    · simp [show cY ≠ cX from fun h => cX_ne_cY h.symm]
  rw [hFilt]
  have hYX : ({cY} ∪ {cX} : Finset CObs) = univ := by
    ext w
    simp only [Finset.mem_union, Finset.mem_singleton, Finset.mem_univ, iff_true]
    rcases cObs_cases w with rfl | rfl
    · exact Or.inr rfl
    · exact Or.inl rfl
  have hNum : (↑(({cY} ∪ {cX} : Finset CObs)) ∪ (↑(univ : Finset CObs))ᶜ : Set CObs) =
      Set.univ := by
    rw [hYX, Finset.coe_univ, Set.compl_univ, Set.union_empty]
  have hDen : (↑({cX} : Finset CObs) ∪ (↑(univ : Finset CObs))ᶜ : Set CObs) =
      ↑({cX} : Finset CObs) := by
    rw [Finset.coe_univ, Set.compl_univ, Set.union_empty]
  rw [hNum, hDen, marginal_univ, IdExpr.eval]

private theorem ids_aux_bern_true (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (bern p hp0 hp1).weights true = p := by
  simp [bern, Finsupp.equivFunOnFinite_symm_apply_apply]

private theorem ids_aux_extendObs_empty (i : Fin 2) :
    extendObs (∅ : Finset (Fin 2)) (fun _ => true) i = true := by
  simp [extendObs]

/-- A value computed from the surgery definition alone, so that the soundness instance on the
chain could have failed: `P_{X = 1}(Y = 1) = 3 / 4`. -/
theorem chain_doMarginal_true : chainNet.doMarginal ∅ {cX} {cY} (fun _ => true) = 3 / 4 := by
  have h0mem : (0 : Fin 2) ∈ ({cX} : Finset CObs).map (Function.Embedding.subtype _) :=
    Finset.mem_map.mpr ⟨cX, Finset.mem_singleton_self cX, rfl⟩
  have h1nmem : (1 : Fin 2) ∉ ({cX} : Finset CObs).map (Function.Embedding.subtype _) := by
    decide
  have h1mem : (1 : Fin 2) ∈ (↑(({cY} : Finset CObs).map (Function.Embedding.subtype _)) :
      Set (Fin 2)) := by
    rw [Finset.mem_coe, Finset.mem_map]
    exact ⟨cY, Finset.mem_singleton_self cY, rfl⟩
  unfold BayesNet.doMarginal MetaMathlibExt.FiniteWeight.marginal
  refine (Finset.sum_eq_single (fun _ => true) ?hzero ?hni).trans ?hval
  · intro b hb hne
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb
    have hb1 : b 1 = true := by
      have h := hb 1 h1mem
      rwa [ids_aux_extendObs_empty] at h
    have hb0 : b 0 = false := by
      cases h0 : b 0
      · rfl
      · exfalso
        apply hne
        funext i
        fin_cases i
        · simpa [Fin.mk_zero] using h0
        · simpa [Fin.mk_one] using hb1
    have hne' : b 0 ≠ extendObs (∅ : Finset (Fin 2)) (fun _ => true) 0 := by
      simp [hb0, ids_aux_extendObs_empty]
    rw [BayesNet.joint_mutilateSet, Fin.prod_univ_two, ite_eq_left h0mem, ite_eq_right hne',
      zero_mul]
  · intro hcon
    exfalso
    apply hcon
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    intro v _
    exact (ids_aux_extendObs_empty v).symm
  · rw [BayesNet.joint_mutilateSet, Fin.prod_univ_two, ite_eq_left h0mem]
    have hw0 : (fun _ => true) (0 : Fin 2) = extendObs (∅ : Finset (Fin 2)) (fun _ => true) 0 := by
      rw [ids_aux_extendObs_empty]
    rw [ite_eq_left hw0, ite_eq_right h1nmem, one_mul, chainNet_cpt_one]
    have hz : chainNet.paVal 1 (fun _ => true) ⟨⟨0, by decide⟩, Finset.mem_univ _⟩ = true := rfl
    rw [ite_eq_left hz]
    exact ids_aux_bern_true _ (by norm_num) (by norm_num)

/-- `BayesNet.doMarginal_eq_marginal_qFactor` with a nonempty intervention: on the chain, the
effect of `do(X)` on `Y` is the Q-factor of `{Y}`, since `(O ∖ {X}) ∖ {Y}` is empty. -/
theorem chain_doMarginal_eq_qFactor (v : CObs → Bool) :
    chainNet.doMarginal ∅ {cX} {cY} v = chainNet.qFactor ∅ {cY} v := by
  have hDX : ((univ : Finset CObs) \ {cX}) = {cY} := by
    ext w
    simp only [Finset.mem_sdiff, Finset.mem_univ, Finset.mem_singleton, true_and]
    constructor
    · intro hw
      rcases cObs_cases w with rfl | rfl
      · exact absurd rfl hw
      · rfl
    · rintro rfl
      exact fun h => cX_ne_cY h.symm
  rw [BayesNet.doMarginal_eq_marginal_qFactor, hDX, Finset.sdiff_self, Finset.coe_empty,
    Set.compl_empty, marginal_univ]

/-! ### A successful run with a latent confounder: the front-door graph -/

section FrontDoor

open Cslib.MachineLearning.CausalAdjustmentTests

/-- The observed nodes of the front-door network `fdNet` (`U → X → M → Y`, `U → Y`, nodes
`0, 1, 2, 3`) when the confounder `U = 0` is latent. -/
abbrev FObs : Type := {i : Fin 4 // i ∉ ({0} : Finset (Fin 4))}

/-- The treatment `X = 1`. -/
def fX : FObs := ⟨1, by decide⟩

/-- The mediator `M = 2`. -/
def fM : FObs := ⟨2, by decide⟩

/-- The outcome `Y = 3`. -/
def fY : FObs := ⟨3, by decide⟩

/-- Every observed node of the front-door network is `X`, `M` or `Y`. -/
theorem fObs_cases : ∀ u : FObs, u = fX ∨ u = fM ∨ u = fY := by
  decide

local notation "fdG" => fdNet.latentProjection ({0} : Finset (Fin 4))

local notation "fdσ" => BayesNet.obsOrder ({0} : Finset (Fin 4))

/-- With `U = 0` latent, a latent path of `fdNet` is an edge: `U` has no parent, so no path
passes through it. -/
theorem fd_latentPath_iff (u w : Fin 4) : fdNet.LatentPath {0} u w ↔ fdNet.Edge u w := by
  constructor
  · rintro ⟨m, hseg, hedge⟩
    rcases Relation.ReflTransGen.cases_tail hseg with rfl | ⟨c, -, hcm, hm⟩
    · exact hedge
    · rw [Finset.mem_singleton] at hm
      subst hm
      exact absurd (fdNet.edge_lt hcm) (Fin.not_lt_zero c)
  · exact fdNet.latentPath_of_edge_direct {0} u w

/-- The directed edges of the latent projection are `X → M` and `M → Y`. -/
theorem fd_dir_iff (u w : FObs) :
    (fdG).dir u w ↔ (u = fX ∧ w = fM) ∨ (u = fM ∧ w = fY) := by
  rw [BayesNet.latentProjection_dir_iff, fd_latentPath_iff, fd_edge]
  rcases fObs_cases u with rfl | rfl | rfl <;> rcases fObs_cases w with rfl | rfl | rfl <;> decide

/-- The only bidirected edge of the latent projection is `X ↔ Y`, from the latent `U`. -/
theorem fd_bidir_iff (u w : FObs) :
    (fdG).bidir.Adj u w ↔ (u = fX ∧ w = fY) ∨ (u = fY ∧ w = fX) := by
  rw [BayesNet.latentProjection_bidir_adj_iff]
  simp only [Finset.mem_singleton, exists_eq_left, fd_latentPath_iff, fd_edge]
  rcases fObs_cases u with rfl | rfl | rfl <;> rcases fObs_cases w with rfl | rfl | rfl <;> decide

/-- A bidirected edge of the subgraph induced on `D` joins `X` and `Y`, both in `D`. -/
theorem fd_induce_adj {D : Finset FObs} {a b : FObs} (h : ((fdG).induce ↑D).bidir.Adj a b) :
    fX ∈ D ∧ fY ∈ D ∧ ((a = fX ∧ b = fY) ∨ (a = fY ∧ b = fX)) := by
  have hEq : ((fdG).induce ↑D).bidir = SimpleGraph.fromRel fun u w =>
      u ∈ (↑D : Set FObs) ∧ w ∈ (↑D : Set FObs) ∧ (fdG).bidir.Adj u w := rfl
  rw [hEq, SimpleGraph.fromRel_adj] at h
  rcases h.2 with ⟨ha, hb, hab⟩ | ⟨hb, ha, hba⟩
  · rcases (fd_bidir_iff a b).mp hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨ha, hb, Or.inl ⟨rfl, rfl⟩⟩
    · exact ⟨hb, ha, Or.inr ⟨rfl, rfl⟩⟩
  · rcases (fd_bidir_iff b a).mp hba with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨hb, ha, Or.inr ⟨rfl, rfl⟩⟩
    · exact ⟨ha, hb, Or.inl ⟨rfl, rfl⟩⟩

/-- Inside a vertex set that misses `X` or `Y`, bidirected reachability is equality. -/
theorem fd_reachable_eq {D : Finset FObs} (hD : fX ∉ D ∨ fY ∉ D) {a b : FObs}
    (h : ((fdG).induce ↑D).bidir.Reachable a b) : a = b := by
  rcases h with ⟨_ | ⟨hadj, _⟩⟩
  · rfl
  · obtain ⟨hX, hY, -⟩ := fd_induce_adj hadj
    rcases hD with h | h
    · exact absurd hX h
    · exact absurd hY h

/-- `M` is isolated in the bidirected part of every induced subgraph. -/
theorem fd_reachable_m {D : Finset FObs} {a : FObs} (h : ((fdG).induce ↑D).bidir.Reachable a fM) :
    a = fM := by
  rw [SimpleGraph.reachable_iff_reflTransGen] at h
  rcases Relation.ReflTransGen.cases_tail h with h' | ⟨c, -, hc⟩
  · exact h'.symm
  · obtain ⟨-, -, h''⟩ := fd_induce_adj hc
    rcases h'' with ⟨-, h⟩ | ⟨-, h⟩ <;> exact absurd h (by decide)

/-- Inside a vertex set that misses `X` or `Y`, the c-component of a vertex is itself. -/
theorem fd_compIn_singleton {D : Finset FObs} (hD : fX ∉ D ∨ fY ∉ D) {u : FObs} (hu : u ∈ D) :
    (fdG).compIn D u = {u} := by
  ext w
  simp only [ADMG.compIn, Finset.mem_filter, Finset.mem_singleton, ADMG.mem_cComponent_iff]
  constructor
  · rintro ⟨-, hr⟩
    exact (fd_reachable_eq hD hr).symm
  · rintro rfl
    exact ⟨hu, SimpleGraph.Reachable.refl _⟩

/-- In the whole projection, `X` and `Y` form one c-component. -/
theorem fd_compIn_univ_xy {u : FObs} (hu : u = fX ∨ u = fY) :
    (fdG).compIn univ u = {fX, fY} := by
  have hadj : ((fdG).induce ↑(univ : Finset FObs)).bidir.Adj fX fY := by
    have hEq : ((fdG).induce ↑(univ : Finset FObs)).bidir = SimpleGraph.fromRel fun u w =>
        u ∈ (↑(univ : Finset FObs) : Set FObs) ∧ w ∈ (↑(univ : Finset FObs) : Set FObs) ∧
          (fdG).bidir.Adj u w := rfl
    rw [hEq, SimpleGraph.fromRel_adj]
    exact ⟨by decide, Or.inl ⟨by simp, by simp, (fd_bidir_iff _ _).mpr (Or.inl ⟨rfl, rfl⟩)⟩⟩
  ext w
  simp only [ADMG.compIn, Finset.mem_filter, Finset.mem_univ, true_and, ADMG.mem_cComponent_iff,
    Finset.mem_insert, Finset.mem_singleton]
  constructor
  · intro hr
    rcases fObs_cases w with rfl | rfl | rfl
    · exact Or.inl rfl
    · have := fd_reachable_m hr
      rcases hu with rfl | rfl <;> exact absurd this (by decide)
    · exact Or.inr rfl
  · rintro (rfl | rfl) <;> rcases hu with rfl | rfl
    · exact SimpleGraph.Reachable.refl _
    · exact hadj.symm.reachable
    · exact hadj.reachable
    · exact SimpleGraph.Reachable.refl _

/-- In the whole projection, `M` is a c-component on its own. -/
theorem fd_compIn_univ_m : (fdG).compIn univ fM = {fM} := by
  ext w
  simp only [ADMG.compIn, Finset.mem_filter, Finset.mem_univ, true_and, ADMG.mem_cComponent_iff,
    Finset.mem_singleton]
  constructor
  · intro hr
    exact fd_reachable_m hr.symm
  · rintro rfl
    exact SimpleGraph.Reachable.refl _

/-- One step of the directed part of an induced subgraph. -/
theorem fd_induce_dir {D : Finset FObs} {a b : FObs} :
    ((fdG).induce ↑D).dir a b ↔ a ∈ D ∧ b ∈ D ∧ (fdG).dir a b :=
  Iff.rfl

/-- Every observed node is an ancestor of `Y`. -/
theorem fd_ancIn_univ_y : (fdG).ancIn univ {fY} = univ := by
  rw [Finset.eq_univ_iff_forall]
  intro u
  simp only [ADMG.ancIn, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton,
    exists_eq_left]
  have hXM : ((fdG).induce ↑(univ : Finset FObs)).dir fX fM :=
    fd_induce_dir.mpr ⟨mem_univ _, mem_univ _, (fd_dir_iff _ _).mpr (Or.inl ⟨rfl, rfl⟩)⟩
  have hMY : ((fdG).induce ↑(univ : Finset FObs)).dir fM fY :=
    fd_induce_dir.mpr ⟨mem_univ _, mem_univ _, (fd_dir_iff _ _).mpr (Or.inr ⟨rfl, rfl⟩)⟩
  rcases fObs_cases u with rfl | rfl | rfl
  · exact Relation.ReflTransGen.head hXM (Relation.ReflTransGen.single hMY)
  · exact Relation.ReflTransGen.single hMY
  · exact Relation.ReflTransGen.refl

/-- With the arrows into `X` deleted, every observed node is still an ancestor of `Y`. -/
theorem fd_ancCut_univ : (fdG).ancCut univ {fX} {fY} = univ := by
  rw [Finset.eq_univ_iff_forall]
  intro u
  simp only [ADMG.ancCut, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton,
    exists_eq_left]
  have hXM : ((fdG).induce ↑(univ : Finset FObs)).dir fX fM ∧ ¬ fM = fX :=
    ⟨fd_induce_dir.mpr ⟨mem_univ _, mem_univ _, (fd_dir_iff _ _).mpr (Or.inl ⟨rfl, rfl⟩)⟩,
      by decide⟩
  have hMY : ((fdG).induce ↑(univ : Finset FObs)).dir fM fY ∧ ¬ fY = fX :=
    ⟨fd_induce_dir.mpr ⟨mem_univ _, mem_univ _, (fd_dir_iff _ _).mpr (Or.inr ⟨rfl, rfl⟩)⟩,
      by decide⟩
  rcases fObs_cases u with rfl | rfl | rfl
  · exact Relation.ReflTransGen.head hXM (Relation.ReflTransGen.single hMY)
  · exact Relation.ReflTransGen.single hMY
  · exact Relation.ReflTransGen.refl

/-- The ancestors of `M` are `X` and `M`. -/
theorem fd_ancIn_univ_m : (fdG).ancIn univ {fM} = {fX, fM} := by
  ext u
  simp only [ADMG.ancIn, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton,
    exists_eq_left, Finset.mem_insert]
  rcases fObs_cases u with rfl | rfl | rfl
  · exact iff_of_true (Relation.ReflTransGen.single (fd_induce_dir.mpr
      ⟨mem_univ _, mem_univ _, (fd_dir_iff _ _).mpr (Or.inl ⟨rfl, rfl⟩)⟩)) (Or.inl rfl)
  · exact iff_of_true Relation.ReflTransGen.refl (Or.inr rfl)
  · refine iff_of_false ?_ (by decide)
    intro h
    rcases Relation.ReflTransGen.cases_head h with h' | ⟨c, hc, -⟩
    · exact absurd h' (by decide)
    · rcases (fd_dir_iff _ _).mp (fd_induce_dir.mp hc).2.2 with ⟨h', -⟩ | ⟨h', -⟩ <;>
        exact absurd h' (by decide)

/-- Inside `{X, M}`, both nodes are ancestors of `M`. -/
theorem fd_ancIn_xm : (fdG).ancIn {fX, fM} {fM} = {fX, fM} := by
  ext u
  simp only [ADMG.ancIn, Finset.mem_filter, Finset.mem_singleton, exists_eq_left,
    Finset.mem_insert]
  rcases fObs_cases u with rfl | rfl | rfl
  · exact iff_of_true ⟨Or.inl rfl, Relation.ReflTransGen.single (fd_induce_dir.mpr
      ⟨by decide, by decide, (fd_dir_iff _ _).mpr (Or.inl ⟨rfl, rfl⟩)⟩)⟩ (Or.inl rfl)
  · exact iff_of_true ⟨Or.inr rfl, Relation.ReflTransGen.refl⟩ (Or.inr rfl)
  · exact iff_of_false (fun h => absurd h.1 (by decide)) (by decide)

/-- Inside `{X, Y}`, the only ancestor of `Y` is `Y`: the path `X → M → Y` leaves the set. -/
theorem fd_ancIn_xy : (fdG).ancIn {fX, fY} {fY} = {fY} := by
  ext u
  simp only [ADMG.ancIn, Finset.mem_filter, Finset.mem_singleton, exists_eq_left,
    Finset.mem_insert]
  rcases fObs_cases u with rfl | rfl | rfl
  · refine iff_of_false ?_ (by decide)
    rintro ⟨-, h⟩
    rcases Relation.ReflTransGen.cases_head h with h' | ⟨c, hc, -⟩
    · exact absurd h' (by decide)
    · obtain ⟨-, hcD, hdir⟩ := fd_induce_dir.mp hc
      rcases (fd_dir_iff _ _).mp hdir with ⟨-, rfl⟩ | ⟨h', -⟩
      · exact absurd hcD (by decide)
      · exact absurd h' (by decide)
  · exact iff_of_false (fun h => absurd h.1 (by decide)) (by decide)
  · exact iff_of_true ⟨Or.inr rfl, Relation.ReflTransGen.refl⟩ rfl

/-- The recursive call of line 4 for the c-component `{M}` of `G[{M, Y}]`: line 2 restricts to
the ancestors `{X, M}` of `M`, and line 6 returns a conditional. -/
theorem fd_idRec_m : ∃ e, (fdG).idRec fdσ {fM} (univ \ {fM}) univ .obs = .ok e := by
  rw [show (univ : Finset FObs) \ {fM} = {fX, fY} by decide]
  have hA : (fdG).ancIn univ {fM} ≠ univ := by rw [fd_ancIn_univ_m]; decide
  rw [ADMG.idRec.eq_def, ite_eq_right (by decide), dite_eq_left hA, fd_ancIn_univ_m,
    show ({fX, fY} ∩ {fX, fM} : Finset FObs) = {fX} by decide]
  have hA' : ¬ (fdG).ancIn {fX, fM} {fM} ≠ {fX, fM} := not_not.mpr fd_ancIn_xm
  have hW : ¬ (({fX, fM} \ {fX}) \ (fdG).ancCut {fX, fM} {fX} {fM}).Nonempty := by
    have hmem : fM ∈ (fdG).ancCut {fX, fM} {fX} {fM} := by
      simp only [ADMG.ancCut, Finset.mem_filter, Finset.mem_singleton, exists_eq_left]
      exact ⟨by decide, Relation.ReflTransGen.refl⟩
    rw [show ({fX, fM} \ {fX} : Finset FObs) = {fM} by decide,
      Finset.sdiff_eq_empty_iff_subset.mpr (Finset.singleton_subset_iff.mpr hmem)]
    exact Finset.not_nonempty_empty
  have hT : ¬ (({fX, fM} : Finset FObs) \ {fX} ∉ (fdG).cComponentsIn ({fX, fM} \ {fX})) := by
    rw [not_not, show ({fX, fM} \ {fX} : Finset FObs) = {fM} by decide]
    simp only [ADMG.cComponentsIn, Finset.mem_image, Finset.mem_singleton, exists_eq_left]
    exact fd_compIn_singleton (Or.inl (by decide)) (Finset.mem_singleton_self _)
  have hD : ¬ ({fX, fM} : Finset FObs) ∈ (fdG).cComponentsIn {fX, fM} := by
    simp only [ADMG.cComponentsIn, Finset.mem_image, not_exists, not_and]
    intro v hv
    rw [fd_compIn_singleton (Or.inr (by decide)) hv]
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl <;> decide
  have h6 : ({fX, fM} : Finset FObs) \ {fX} ∈ (fdG).cComponentsIn {fX, fM} := by
    rw [show ({fX, fM} \ {fX} : Finset FObs) = {fM} by decide]
    simp only [ADMG.cComponentsIn, Finset.mem_image]
    exact ⟨fM, by decide, fd_compIn_singleton (Or.inr (by decide)) (by decide)⟩
  rw [ADMG.idRec.eq_def, ite_eq_right (by decide), dite_eq_right hA', dite_eq_right hW,
    dite_eq_right hT, dite_eq_right hD, ite_eq_left h6]
  exact ⟨_, rfl⟩

/-- The recursive call of line 4 for the c-component `{Y}` of `G[{M, Y}]`: line 7 moves to the
c-component `{X, Y}` of `Y`, line 2 restricts to `{Y}`, and line 1 returns a marginal. -/
theorem fd_idRec_y : ∃ e, (fdG).idRec fdσ {fY} (univ \ {fY}) univ .obs = .ok e := by
  rw [show (univ : Finset FObs) \ {fY} = {fX, fM} by decide]
  have hUXM : (univ : Finset FObs) \ {fX, fM} = {fY} := by decide
  have hW : ¬ ((univ \ {fX, fM}) \ (fdG).ancCut univ {fX, fM} {fY}).Nonempty := by
    have hmem : fY ∈ (fdG).ancCut univ {fX, fM} {fY} := by
      simp only [ADMG.ancCut, Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_singleton, exists_eq_left]
      exact Relation.ReflTransGen.refl
    rw [hUXM, Finset.sdiff_eq_empty_iff_subset.mpr (Finset.singleton_subset_iff.mpr hmem)]
    exact Finset.not_nonempty_empty
  have hT : ¬ ((univ : Finset FObs) \ {fX, fM} ∉ (fdG).cComponentsIn (univ \ {fX, fM})) := by
    rw [not_not, hUXM]
    simp only [ADMG.cComponentsIn, Finset.mem_image, Finset.mem_singleton, exists_eq_left]
    exact fd_compIn_singleton (Or.inl (by decide)) (Finset.mem_singleton_self _)
  have hcomp : ∀ v : FObs, (fdG).compIn univ v = {fX, fY} ∨ (fdG).compIn univ v = {fM} := by
    intro v
    rcases fObs_cases v with rfl | rfl | rfl
    · exact Or.inl (fd_compIn_univ_xy (Or.inl rfl))
    · exact Or.inr fd_compIn_univ_m
    · exact Or.inl (fd_compIn_univ_xy (Or.inr rfl))
  have hD : ¬ (univ : Finset FObs) ∈ (fdG).cComponentsIn univ := by
    simp only [ADMG.cComponentsIn, Finset.mem_image, not_exists, not_and]
    intro v _
    rcases hcomp v with h | h <;> rw [h] <;> decide
  have h6 : ¬ (univ : Finset FObs) \ {fX, fM} ∈ (fdG).cComponentsIn univ := by
    rw [hUXM]
    simp only [ADMG.cComponentsIn, Finset.mem_image, not_exists, not_and]
    intro v _
    rcases hcomp v with h | h <;> rw [h] <;> decide
  have key : ∀ h : ((univ : Finset FObs) \ {fX, fM}).Nonempty, ∃ e,
      (fdG).idRec fdσ {fY} ({fX, fM} ∩ (fdG).compIn univ h.choose) ((fdG).compIn univ h.choose)
        (ADMG.condChain fdσ univ ((fdG).compIn univ h.choose) .obs) = .ok e := by
    intro h
    have hc : h.choose = fY :=
      Finset.mem_singleton.mp ((Finset.ext_iff.mp hUXM _).mp h.choose_spec)
    rw [hc, fd_compIn_univ_xy (Or.inr rfl),
      show ({fX, fM} ∩ {fX, fY} : Finset FObs) = {fX} by decide]
    have hA : (fdG).ancIn {fX, fY} {fY} ≠ {fX, fY} := by rw [fd_ancIn_xy]; decide
    rw [ADMG.idRec.eq_def, ite_eq_right (by decide), dite_eq_left hA, fd_ancIn_xy,
      show ({fX} ∩ {fY} : Finset FObs) = ∅ by decide, ADMG.idRec.eq_def, ite_eq_left rfl]
    exact ⟨_, rfl⟩
  rw [ADMG.idRec.eq_def, ite_eq_right (by decide), dite_eq_right (not_not.mpr fd_ancIn_univ_y),
    dite_eq_right hW, dite_eq_right hT, dite_eq_right hD, ite_eq_right h6]
  exact key _

/-- **ID succeeds with a latent confounder.** On the latent projection of the front-door network
with `U` latent (`X → M → Y`, `X ↔ Y`), `ID` for `P_x(y)` takes line 4 on the c-components `{M}`
and `{Y}` of `G[{M, Y}]`, and both recursive calls return expressions. -/
theorem fd_ID_ok : ∃ e, (fdG).ID fdσ {fY} {fX} = .ok e := by
  have hUX : (univ : Finset FObs) \ {fX} = {fM, fY} := by decide
  have hW : ¬ ((univ \ {fX}) \ (fdG).ancCut univ {fX} {fY}).Nonempty := by
    rw [fd_ancCut_univ, Finset.sdiff_eq_empty_iff_subset.mpr (Finset.subset_univ _)]
    exact Finset.not_nonempty_empty
  have hT : (univ : Finset FObs) \ {fX} ∉ (fdG).cComponentsIn (univ \ {fX}) := by
    rw [hUX]
    simp only [ADMG.cComponentsIn, Finset.mem_image, not_exists, not_and]
    intro v hv
    rw [fd_compIn_singleton (Or.inl (by decide)) hv]
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl <;> decide
  unfold ADMG.ID
  rw [ADMG.idRec.eq_def, ite_eq_right (by decide), dite_eq_right (not_not.mpr fd_ancIn_univ_y),
    dite_eq_right hW, dite_eq_left hT]
  have hmap : ∃ es, ((fdG).cComponentsIn (univ \ {fX})).toList.attach.mapM
      (fun S : {S // S ∈ ((fdG).cComponentsIn (univ \ {fX})).toList} =>
        (fdG).idRec fdσ S.1 (univ \ S.1) univ .obs) = .ok es := by
    refine List.exists_mapM_eq_ok_iff.mpr fun ⟨T, hTmem⟩ _ => ?_
    have hS : T ∈ (fdG).cComponentsIn (univ \ {fX}) := Finset.mem_toList.mp hTmem
    rw [hUX] at hS
    simp only [ADMG.cComponentsIn, Finset.mem_image] at hS
    obtain ⟨v, hv, hvS⟩ := hS
    rw [fd_compIn_singleton (Or.inl (by decide)) hv] at hvS
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv
    change ∃ e, (fdG).idRec fdσ T (univ \ T) univ .obs = .ok e
    rw [← hvS]
    rcases hv with rfl | rfl
    · exact fd_idRec_m
    · exact fd_idRec_y
  obtain ⟨es, hes⟩ := hmap
  exact ⟨_, by rw [hes]; rfl⟩

/-- The observed law of the front-door network, `U` summed out, is strictly positive. -/
theorem fd_observedLaw_pos (v : FObs → Bool) : 0 < fdNet.observedLaw {0} v := by
  unfold BayesNet.observedLaw MetaMathlibExt.FiniteWeight.marginal
  refine Finset.sum_pos (fun z _ => fd_joint_pos z) ⟨extendObs {0} v, ?_⟩
  simp

/-- The effect computed from the surgery definition alone: in the front-door network,
`P_{X = 1}(Y = 1) = Σ_u Σ_m P(u) P(m | X = 1) P(Y = 1 | u, m) = 17 / 32`. -/
theorem fd_doMarginal_true : fdNet.doMarginal {0} {fX} {fY} (fun _ => true) = 17 / 32 := by
  have hX : ({fX} : Finset FObs).map (Function.Embedding.subtype _) = {1} := by decide
  have hY : ({fY} : Finset FObs).map (Function.Embedding.subtype _) = {3} := by decide
  have he1 : extendObs ({0} : Finset (Fin 4)) (fun _ : FObs => true) 1 = true := by
    simp [extendObs]
  have he3 : extendObs ({0} : Finset (Fin 4)) (fun _ : FObs => true) 3 = true := by
    simp [extendObs]
  let g : Bool × Bool → (Fin 4 → Bool) := fun p => ![p.1, true, p.2, true]
  unfold BayesNet.doMarginal MetaMathlibExt.FiniteWeight.marginal
  rw [hX, hY]
  refine ((Finset.sum_subset (s₁ := univ.image g) ?_ ?_).symm).trans ?_
  · intro z hz
    obtain ⟨p, -, rfl⟩ := Finset.mem_image.mp hz
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.coe_singleton,
      Set.mem_singleton_iff, forall_eq, he3]
    rfl
  · intro z hzF hzn
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.coe_singleton,
      Set.mem_singleton_iff, forall_eq, he3] at hzF
    rw [BayesNet.joint_mutilateSet]
    refine Finset.prod_eq_zero (Finset.mem_univ 1) ?_
    rw [ite_eq_left (Finset.mem_singleton_self 1), he1]
    refine ite_eq_right fun h1 => hzn (Finset.mem_image.mpr ⟨(z 0, z 2), Finset.mem_univ _, ?_⟩)
    funext i
    fin_cases i
    · rfl
    · exact h1.symm
    · rfl
    · exact hzF.symm
  · rw [Finset.sum_image fun p _ q _ h => Prod.ext (congrFun h 0) (congrFun h 2),
      Fintype.sum_prod_type, Fintype.sum_bool, Fintype.sum_bool, Fintype.sum_bool]
    simp (config := {decide := true}) only [BayesNet.joint_mutilateSet, Fin.prod_univ_four, g,
      ite_true, ite_false, mul_one]
    simp (config := {decide := true}) [fdNet, coin_true, coin_false]
    norm_num

/-- **Soundness of ID with a latent confounder.** In the front-door network with the confounder
`U` latent, `ID` returns an expression for the effect of `do(X)` on `Y`, and that expression,
evaluated against the observed law (`U` summed out), gives `P_{X = 1}(Y = 1) = 17 / 32`, the
value `fd_doMarginal_true` computes from the network's tables. -/
theorem fd_ID_eval_true : ∃ e, (fdG).ID fdσ {fY} {fX} = .ok e ∧
    e.eval (fdNet.observedLaw {0}) (fun _ => true) = 17 / 32 := by
  obtain ⟨e, he⟩ := fd_ID_ok
  refine ⟨e, he, ?_⟩
  rw [BayesNet.ID_sound fdNet {0} (BayesNet.obsOrder_topological fdNet {0}) fd_observedLaw_pos
    (Finset.disjoint_singleton.mpr (by decide)) he, fd_doMarginal_true]

end FrontDoor

section Bow

open Cslib.MachineLearning.GraphicalModels.LatentConfounding

private theorem ids_aux_obs_cases (u : Obs) : u = xNode ∨ u = yNode := by
  obtain ⟨i, hi⟩ := u
  have h0 : i ≠ 0 := fun hcon => hi (by simp [hcon])
  have hfin : i = 1 ∨ i = 2 := by
    fin_cases i
    · simp at h0
    · left
      decide
    · right
      decide
  rcases hfin with h1 | h2
  · left
    apply Subtype.ext
    simpa [xNode] using h1
  · right
    apply Subtype.ext
    simpa [yNode] using h2

/-! ### Failure on the bow graph -/

/-- On the bow graph `X → Y`, `X ↔ Y` (`U = 0` latent; the bow arc graph of Shpitser and Pearl,
AAAI 2006, Theorem 1), `ID` for `P_x(y)` passes lines 1–4 (none of their guards holds) and fails
at line 5 with the pair `(O, O ∖ {X})`. -/
theorem bow_ID_eq_error :
    bow.ID (BayesNet.obsOrder ({0} : Finset (Fin 3))) {yNode} {xNode} =
      .error (univ, univ \ {xNode}) := by
  have hxy : yNode ≠ xNode := by decide
  have hAnc : bow.ancIn Finset.univ {yNode} = Finset.univ := by
    apply Finset.eq_univ_of_forall
    intro u
    simp only [ADMG.ancIn, Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨yNode, Finset.mem_singleton_self yNode, ?_⟩
    rcases ids_aux_obs_cases u with rfl | rfl
    · exact Relation.ReflTransGen.single ⟨Finset.mem_univ _, Finset.mem_univ _, rfl, rfl⟩
    · exact Relation.ReflTransGen.refl
  have hCut : bow.ancCut Finset.univ {xNode} {yNode} = Finset.univ := by
    apply Finset.eq_univ_of_forall
    intro u
    simp only [ADMG.ancCut, Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨yNode, Finset.mem_singleton_self yNode, ?_⟩
    rcases ids_aux_obs_cases u with rfl | rfl
    · refine Relation.ReflTransGen.single ⟨⟨Finset.mem_univ _, Finset.mem_univ _, rfl, rfl⟩, ?_⟩
      simp [hxy]
    · exact Relation.ReflTransGen.refl
  have hDX : (Finset.univ \ {xNode} : Finset Obs) = {yNode} := by
    ext w
    simp only [Finset.mem_sdiff, Finset.mem_univ, Finset.mem_singleton, true_and]
    rcases ids_aux_obs_cases w with rfl | rfl
    · simp [Ne.symm hxy]
    · simp [hxy]
  have hcomp : bow.compIn {yNode} yNode = {yNode} := by
    apply Finset.eq_singleton_iff_unique_mem.mpr
    constructor
    · exact bow.compIn_self_mem (Finset.mem_singleton_self yNode)
    · intro x hx
      exact Finset.mem_singleton.mp (bow.compIn_subset _ _ hx)
  have hTmem : (Finset.univ \ {xNode}) ∈ bow.cComponentsIn (Finset.univ \ {xNode}) := by
    rw [hDX]
    simp only [ADMG.cComponentsIn, Finset.mem_image]
    exact ⟨yNode, Finset.mem_singleton_self yNode, hcomp⟩
  have hTside : ¬(Finset.univ \ {xNode} ∉ bow.cComponentsIn (Finset.univ \ {xNode})) :=
    fun hcon => hcon hTmem
  have hadj : ∀ u w : Obs, u ≠ w → (bow.induce (↑(Finset.univ : Finset Obs))).bidir.Adj u w := by
    intro u w hne
    simp only [ADMG.induce, SimpleGraph.fromRel_adj]
    refine ⟨hne, Or.inl ⟨Finset.mem_univ _, Finset.mem_univ _, ?_⟩⟩
    exact (SimpleGraph.top_adj u w).mpr hne
  have hcompU : ∀ v : Obs, bow.compIn Finset.univ v = Finset.univ := by
    intro v
    apply Finset.eq_univ_of_forall
    intro w
    simp only [ADMG.compIn, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [ADMG.mem_cComponent_iff]
    rcases ids_aux_obs_cases v with rfl | rfl <;> rcases ids_aux_obs_cases w with rfl | rfl
    · exact SimpleGraph.Reachable.refl _
    · exact SimpleGraph.Adj.reachable (hadj _ _ (Ne.symm hxy))
    · exact SimpleGraph.Adj.reachable (hadj _ _ hxy)
    · exact SimpleGraph.Reachable.refl _
  have hDside : (Finset.univ : Finset Obs) ∈ bow.cComponentsIn Finset.univ := by
    simp only [ADMG.cComponentsIn, Finset.mem_image]
    exact ⟨xNode, Finset.mem_univ xNode, hcompU xNode⟩
  have hXside : ¬({xNode} : Finset Obs) = ∅ := by simp
  have hAside : ¬(bow.ancIn Finset.univ {yNode} ≠ Finset.univ) := by simp [hAnc]
  have hWside :
      ¬(((Finset.univ \ {xNode}) \ bow.ancCut Finset.univ {xNode} {yNode}).Nonempty) := by
    have hempty : ((Finset.univ \ {xNode}) \ Finset.univ : Finset Obs) = ∅ :=
      Finset.sdiff_eq_empty_iff_subset.mpr (Finset.subset_univ _)
    rw [hCut, hempty]
    exact Finset.not_nonempty_empty
  unfold ADMG.ID ADMG.idRec
  rw [ite_eq_right hXside, dite_eq_right hAside, dite_eq_right hWside, dite_eq_right hTside,
    dite_eq_left hDside]

/-- So `BayesNet.ID_sound` has no instance for this query: no expression is returned. Nothing is
claimed about `.error` outputs (completeness through hedges is not formalized); the
non-identification of this particular query is the separate test
`LatentConfounding.not_identifiedOn_bow`. -/
theorem bow_ID_ne_ok (e : IdExpr Obs) :
    bow.ID (BayesNet.obsOrder ({0} : Finset (Fin 3))) {yNode} {xNode} ≠ .ok e := by
  rw [bow_ID_eq_error]
  intro h
  cases h

end Bow

end Cslib.MachineLearning.IdentificationSoundnessTests

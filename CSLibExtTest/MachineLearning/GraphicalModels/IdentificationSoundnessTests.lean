/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.MachineLearning.GraphicalModels.IdentificationSoundness
public import CSLibExtTest.MachineLearning.GraphicalModels.CComponentCriterionTests
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
  instance could have failed.
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
    [Nonempty α] {n : ℕ} (b : BayesNet α n) (L : Finset (Fin n))
    {σ : {i : Fin n // i ∉ L} ≃ Fin (Fintype.card {i : Fin n // i ∉ L})}
    (hσ : ∀ ⦃u w⦄, (b.latentProjection L).dir u w → σ u < σ w)
    (hpos : ∀ v, 0 < b.observedLaw L v) (Y : Finset {i : Fin n // i ∉ L})
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
    cases b <;> simp [bern] <;> norm_num
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

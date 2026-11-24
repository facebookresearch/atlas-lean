/-
Copyright (c) 2026 Adam Kiezun. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Adam Kiezun
-/

module

public import CSLibExt.MachineLearning.GraphicalModels.LatentProjection
public import MathlibExt.Probability.FiniteWeight
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# Factorization of the observed law over c-components

For a Bayesian network with a set `L` of latent (unobserved) nodes, Tian and
Pearl (AAAI 2002) factor the observed law over the c-components of the latent
projection: `P(v) = ∏ S ∈ C(G), Q[S](v)`, where the Q-factors
`Q[S](v) = P_{v∖s}(s)` are interventional laws of the network. This file
defines the observed law `BayesNet.observedLaw` and the Q-factor
`BayesNet.qFactor`, using the c-components `ADMG.cComponents` as vertex
sets from `LatentProjection`, and proves the factorization together with the prefix identity that recovers each
Q-factor from the observed law along a topological order (in division-free
form for every `v`, and as a product of conditional ratios when `P(v) > 0`).
The factorization and prefix identities need no semi-Markovian hypothesis;
they subsume TP02's statements under its p. 568 hypothesis, recorded here
as `BayesNet.NoObservedAncestorOfLatent`.

## References

* J. Tian and J. Pearl, *A General Identification Condition for Causal
  Effects*, Proceedings of the Eighteenth National Conference on Artificial
  Intelligence (AAAI-02), AAAI Press (2002), 567–573. Cited as TP02.
* J. Tian and J. Pearl, *On the Identification of Causal Effects*, UCLA
  Cognitive Systems Laboratory, Technical Report R-290-L (2003). Cited as TR.
-/

@[expose] public section

namespace Cslib.MachineLearning.GraphicalModels.BayesNet

open Finset

variable {α : Type*} {n : ℕ} [Nonempty α] (b : BayesNet α n)

end Cslib.MachineLearning.GraphicalModels.BayesNet

namespace Cslib.MachineLearning.GraphicalModels

variable {α : Type*} {n : ℕ}

/-- An observed assignment extended to all nodes; latent coordinates are arbitrary. -/
noncomputable def extendObs [Nonempty α] (L : Finset (Fin n)) (v : {i : Fin n // i ∉ L} → α) :
    Fin n → α :=
  fun i => if h : i ∈ L then Classical.arbitrary α else v ⟨i, h⟩

variable [Fintype α] [Nonempty α]

/-- The observed law `P(v) = Σ_u P(v, u)` (TP02 eq. (4)). -/
noncomputable def BayesNet.observedLaw (b : BayesNet α n) (L : Finset (Fin n)) :
    ({i : Fin n // i ∉ L} → α) → ℝ :=
  fun v => MetaMathlibExt.FiniteWeight.marginal b.joint ↑(Lᶜ) (extendObs L v)

/-- `Q[S](v) = P_{v∖s}(s)` (TP02 eq. (28), TR eq. (55)): the probability of the values `v` on
`S` after `do(V ∖ S = v ∖ s)` on the observed nodes outside `S`; latents are not intervened. -/
noncomputable def BayesNet.qFactor (b : BayesNet α n) (L : Finset (Fin n))
    (S : Finset {i : Fin n // i ∉ L}) (v : {i : Fin n // i ∉ L} → α) : ℝ :=
  MetaMathlibExt.FiniteWeight.marginal
    (b.mutilateSet ((Sᶜ).map (Function.Embedding.subtype _)) (extendObs L v)).joint
    ↑(S.map (Function.Embedding.subtype _)) (extendObs L v)

end Cslib.MachineLearning.GraphicalModels

namespace Cslib.MachineLearning.GraphicalModels.BayesNet
open Finset MetaMathlibExt.FiniteWeight
variable {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α] {n : ℕ}
  (b : BayesNet α n) (L : Finset (Fin n))

/-- No latent node is a descendant of an observed node. This is TP02's
hypothesis verbatim (AAAI-02, p. 568, right column): "Assuming that no U
variable is a descendant of any V variable (called a semi-Markovian
model)". The companion technical report TR (R-290-L, p. 6) uses
"semi-Markovian" for a different, stronger normal form: "each unobserved
variable is a root node with exactly two observed children". The
descriptive name here keeps the two source conventions apart; no theorem
below takes this predicate as a hypothesis. -/
def NoObservedAncestorOfLatent : Prop := ∀ u ∈ L, ∀ w ∉ L, ¬ b.IsDescendant w u

/-- The Q-factor as a truncated product (TP02 (26), TR (55)), summed over the latent
coordinates with the observed coordinates fixed at `v`. -/
theorem qFactor_eq_sum_prod (S : Finset {i : Fin n // i ∉ L}) (v : {i : Fin n // i ∉ L} → α) :
    b.qFactor L S v = ∑ y with ∀ i : {i : Fin n // i ∉ L}, y i = v i,
      ∏ j ∈ L ∪ S.map (Function.Embedding.subtype _), (b.cpt j (b.paVal j y)).weights (y j) := by
  classical
  have hext : ∀ a : {i : Fin n // i ∉ L}, extendObs L v ↑a = v a := by
    intro a
    unfold extendObs
    simp only [dite_eq_right a.2]
  have hW : ∀ j : Fin n, j ∈ (Sᶜ).map (Function.Embedding.subtype _) ↔
      ∃ a : {i : Fin n // i ∉ L}, a ∉ S ∧ ↑a = j := by
    intro j
    simp only [Finset.mem_map, Finset.mem_compl]
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact ⟨a, ha, rfl⟩
    · rintro ⟨a, ha, rfl⟩
      exact ⟨a, ha, rfl⟩
  have hSmap : ∀ j : Fin n, j ∈ S.map (Function.Embedding.subtype _) ↔
      ∃ a ∈ S, ↑a = j := by
    intro j
    simp only [Finset.mem_map]
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact ⟨a, ha, rfl⟩
    · rintro ⟨a, ha, rfl⟩
      exact ⟨a, ha, rfl⟩
  have hWL : ∀ j ∈ (Sᶜ).map (Function.Embedding.subtype _), j ∉ L := by
    intro j hj
    rw [hW] at hj
    obtain ⟨a, _, rfl⟩ := hj
    exact a.2
  have hWS : ∀ j ∈ (Sᶜ).map (Function.Embedding.subtype _),
      j ∉ S.map (Function.Embedding.subtype _) := by
    intro j hjW hjS
    rw [hW] at hjW
    rw [hSmap] at hjS
    obtain ⟨a, haS, rfl⟩ := hjW
    obtain ⟨a', ha'S, hval⟩ := hjS
    rw [Subtype.ext hval] at ha'S
    exact haS ha'S
  have hPonW : ∀ y : Fin n → α, (∀ i : {i : Fin n // i ∉ L}, y i = v i) →
      ∀ j ∈ (Sᶜ).map (Function.Embedding.subtype _), y j = extendObs L v j := by
    intro y hyP j hjW
    rw [hW] at hjW
    obtain ⟨a, _, rfl⟩ := hjW
    rw [hext a]
    exact hyP a
  have hQofP : ∀ y : Fin n → α, (∀ i : {i : Fin n // i ∉ L}, y i = v i) →
      ∀ j ∈ (↑(S.map (Function.Embedding.subtype _)) : Set (Fin n)),
        y j = extendObs L v j := by
    intro y hyP j hj
    rw [Finset.mem_coe, hSmap] at hj
    obtain ⟨a, _, rfl⟩ := hj
    rw [hext a]
    exact hyP a
  have hvan : ∀ y : Fin n → α,
      (∀ j ∈ (↑(S.map (Function.Embedding.subtype _)) : Set (Fin n)),
        y j = extendObs L v j) →
      ¬ (∀ i : {i : Fin n // i ∉ L}, y i = v i) →
      (b.mutilateSet ((Sᶜ).map (Function.Embedding.subtype _)) (extendObs L v)).joint y = 0 := by
    intro y hyQ hynP
    rw [not_forall] at hynP
    obtain ⟨a, ha⟩ := hynP
    by_cases haS : a ∈ S
    · have hjS : (↑a : Fin n) ∈ S.map (Function.Embedding.subtype _) := by
        rw [hSmap]
        exact ⟨a, haS, rfl⟩
      have hmem : (↑a : Fin n) ∈ (↑(S.map (Function.Embedding.subtype _)) : Set (Fin n)) :=
        Finset.mem_coe.mpr hjS
      have hQ := hyQ _ hmem
      rw [hext a] at hQ
      exact absurd hQ ha
    · have hjW : (↑a : Fin n) ∈ (Sᶜ).map (Function.Embedding.subtype _) := by
        rw [hW]
        exact ⟨a, haS, rfl⟩
      have hne : y ↑a ≠ extendObs L v ↑a := by
        rw [hext a]
        exact ha
      rw [joint_mutilateSet]
      refine Finset.prod_eq_zero (i := (↑a : Fin n)) (Finset.mem_univ _) ?_
      simp only [ite_eq_left hjW, ite_eq_right hne]
  have hval : ∀ y : Fin n → α, (∀ i : {i : Fin n // i ∉ L}, y i = v i) →
      (b.mutilateSet ((Sᶜ).map (Function.Embedding.subtype _)) (extendObs L v)).joint y =
      ∏ j ∈ L ∪ S.map (Function.Embedding.subtype _),
        (b.cpt j (b.paVal j y)).weights (y j) := by
    intro y hyP
    rw [joint_mutilateSet]
    refine (Finset.prod_subset (s₁ := L ∪ S.map (Function.Embedding.subtype _))
      (Finset.subset_univ _) (fun j _ hjn => ?_)).symm.trans ?_
    · simp only [Finset.mem_union, not_or] at hjn
      obtain ⟨hjL, hjS⟩ := hjn
      have hjW : j ∈ (Sᶜ).map (Function.Embedding.subtype _) := by
        rw [hW]
        refine ⟨⟨j, hjL⟩, ?_, rfl⟩
        intro haS
        apply hjS
        rw [hSmap]
        exact ⟨⟨j, hjL⟩, haS, rfl⟩
      have hyw : y j = extendObs L v j := hPonW y hyP j hjW
      simp only [ite_eq_left hjW, ite_eq_left hyw]
    · refine Finset.prod_congr rfl (fun j hj => ?_)
      have hjnW : j ∉ (Sᶜ).map (Function.Embedding.subtype _) := by
        intro hjW
        simp only [Finset.mem_union] at hj
        exact hj.elim (hWL j hjW) (hWS j hjW)
      simp only [ite_eq_right hjnW]
  unfold qFactor marginal
  refine (Finset.sum_subset (s₁ := univ.filter
    fun y : Fin n → α => ∀ i : {i : Fin n // i ∉ L}, y i = v i) ?hsub ?hvan).symm.trans ?_
  · intro y hy
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
    exact hQofP y hy
  · intro y hyQ hynP
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hyQ hynP
    exact hvan y hyQ hynP
  · refine Finset.sum_congr rfl (fun y hy => ?_)
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy
    exact hval y hy

theorem qFactor_univ : b.qFactor L univ = b.observedLaw L := by  -- TR p. 19
  funext v
  unfold qFactor observedLaw
  rw [Finset.compl_univ, Finset.map_empty, joint_mutilateSet_empty]
  congr 1
  ext i
  simp only [Finset.mem_coe, Finset.mem_map, Finset.mem_univ, true_and, Finset.mem_compl]
  constructor
  · rintro ⟨a, rfl⟩
    exact a.2
  · intro h
    exact ⟨⟨i, h⟩, rfl⟩
theorem qFactor_empty (v : {i : Fin n // i ∉ L} → α) : b.qFactor L ∅ v = 1 := by  -- TR p. 19
  have h : ∀ (p : (Fin n → α) → ℝ) (x : Fin n → α), marginal p ∅ x = ∑ y, p y := by
    intro p x
    unfold marginal
    simp
  unfold qFactor
  rw [Finset.map_empty, Finset.coe_empty, h]
  exact (b.mutilateSet _ _).sum_joint
theorem qFactor_nonneg (S : Finset {i : Fin n // i ∉ L}) (v : {i : Fin n // i ∉ L} → α) :
    0 ≤ b.qFactor L S v := by
  unfold qFactor
  apply marginal_nonneg
  intro x
  exact (b.mutilateSet _ _).toChain.joint_nonneg n x
theorem qFactor_pos {v : {i : Fin n // i ∉ L} → α} (hv : 0 < b.observedLaw L v)
    (S : Finset {i : Fin n // i ∉ L}) :
    0 < b.qFactor L S v := by
  classical
  have hnn : ∀ (T : Finset (Fin n)) (y : Fin n → α),
      0 ≤ ∏ j ∈ T, (b.cpt j (b.paVal j y)).weights (y j) := fun T y =>
    Finset.prod_nonneg fun j _ => (b.cpt j (b.paVal j y)).nonneg _
  have hT0S := b.qFactor_eq_sum_prod L S v
  have hT0U := b.qFactor_eq_sum_prod L univ v
  have huniv := congrFun (b.qFactor_univ L) v
  rw [← huniv, hT0U] at hv
  rw [hT0S]
  obtain ⟨y0, hy0mem, hy0pos⟩ :=
    (Finset.sum_pos_iff_of_nonneg (fun y _ => hnn _ y)).mp hv
  have hsub : L ∪ S.map (Function.Embedding.subtype _) ⊆
      L ∪ Finset.univ.map (Function.Embedding.subtype _) :=
    Finset.union_subset_union (fun x hx => hx)
      (Finset.map_subset_map.mpr (Finset.subset_univ _))
  have hfac : ∀ j ∈ L ∪ S.map (Function.Embedding.subtype _),
      0 < (b.cpt j (b.paVal j y0)).weights (y0 j) := by
    intro j hj
    by_contra hle
    rw [not_lt] at hle
    have h0 : (b.cpt j (b.paVal j y0)).weights (y0 j) = 0 :=
      le_antisymm hle ((b.cpt j (b.paVal j y0)).nonneg _)
    have hz : (∏ j ∈ L ∪ Finset.univ.map (Function.Embedding.subtype _),
        (b.cpt j (b.paVal j y0)).weights (y0 j)) = 0 :=
      Finset.prod_eq_zero (hsub hj) h0
    exact absurd hz (ne_of_gt hy0pos)
  have hy0posS : 0 < ∏ j ∈ L ∪ S.map (Function.Embedding.subtype _),
      (b.cpt j (b.paVal j y0)).weights (y0 j) :=
    Finset.prod_pos hfac
  have hle : (∏ j ∈ L ∪ S.map (Function.Embedding.subtype _),
      (b.cpt j (b.paVal j y0)).weights (y0 j)) ≤
      ∑ y with ∀ i : {i : Fin n // i ∉ L}, y i = v i,
        ∏ j ∈ L ∪ S.map (Function.Embedding.subtype _),
          (b.cpt j (b.paVal j y)).weights (y j) :=
    Finset.single_le_sum (fun y _ => hnn _ y) hy0mem
  exact lt_of_lt_of_le hy0posS hle

open scoped Classical in
/-- The latents that reach `H` along a latent path. -/
noncomputable def latentsInto (H : Finset {i : Fin n // i ∉ L}) : Finset (Fin n) :=
  L.filter fun l => ∃ u ∈ H, b.LatentPath L l (u : Fin n)

/-- Summing the factors over the assignments that agree with `x` off `B` is 1. -/
theorem sum_prod_cpt_filter_eq_one (B : Finset (Fin n)) (x : Fin n → α) :
    ∑ y with ∀ j ∉ B, y j = x j, ∏ j ∈ B, (b.cpt j (b.paVal j y)).weights (y j) = 1 := by
  classical
  have hJ : ∀ y : Fin n → α, (∀ j ∉ B, y j = x j) →
      (b.mutilateSet Bᶜ x).joint y = ∏ j ∈ B, (b.cpt j (b.paVal j y)).weights (y j) := by
    intro y hy
    rw [joint_mutilateSet]
    refine (Finset.prod_subset (s₁ := B) (Finset.subset_univ _) (fun j _ hjB => ?_)).symm.trans ?_
    · have hjC : j ∈ Bᶜ := Finset.mem_compl.mpr hjB
      rw [ite_eq_left hjC, ite_eq_left (hy j hjB)]
    · refine Finset.prod_congr rfl fun j hjB => ?_
      have hjC : j ∉ Bᶜ := fun h => (Finset.mem_compl.mp h) hjB
      rw [ite_eq_right hjC]
  have hJ0 : ∀ y : Fin n → α, ¬ (∀ j ∉ B, y j = x j) →
      (b.mutilateSet Bᶜ x).joint y = 0 := by
    intro y hy
    have hex : ∃ j ∉ B, y j ≠ x j := by
      by_contra hcon
      apply hy
      intro j hjB
      by_contra hne
      exact hcon ⟨j, hjB, hne⟩
    obtain ⟨j, hjB, hne⟩ := hex
    rw [joint_mutilateSet]
    refine Finset.prod_eq_zero (i := j) (Finset.mem_univ _) ?_
    have hjC : j ∈ Bᶜ := Finset.mem_compl.mpr hjB
    rw [ite_eq_left hjC, ite_eq_right hne]
  calc ∑ y with ∀ j ∉ B, y j = x j, ∏ j ∈ B, (b.cpt j (b.paVal j y)).weights (y j)
        = ∑ y with ∀ j ∉ B, y j = x j, (b.mutilateSet Bᶜ x).joint y := by
          refine Finset.sum_congr rfl fun y hy => ?_
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy
          exact (hJ y hy).symm
      _ = ∑ y, (b.mutilateSet Bᶜ x).joint y := by
          refine Finset.sum_subset (Finset.filter_subset _ _) fun y _ hy => ?_
          exact hJ0 y (fun hP => hy (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hP⟩))
      _ = 1 := (b.mutilateSet Bᶜ x).sum_joint

omit [Fintype α] [DecidableEq α] [Nonempty α] in
/-- The factor product over `B` depends only on `B` and the parents of `B`. -/
theorem dependsOn_prod_cpt (B : Finset (Fin n)) :
    DependsOn (fun y : Fin n → α => ∏ j ∈ B, (b.cpt j (b.paVal j y)).weights (y j))
      (↑B ∪ {u : Fin n | ∃ j ∈ B, ∃ p : b.pa j, Fin.castLE j.2.le p = u}) := by
  intro x y hxy
  refine Finset.prod_congr rfl fun j hjB => ?_
  have hj : x j = y j := hxy j (Or.inl (Finset.mem_coe.mpr hjB))
  have hpa : b.paVal j x = b.paVal j y := by
    funext p
    show x (Fin.castLE j.2.le p) = y (Fin.castLE j.2.le p)
    exact hxy _ (Or.inr ⟨j, hjB, p, rfl⟩)
  rw [hpa, hj]

omit [Fintype α] [DecidableEq α] [Nonempty α] in
/-- Latent parents of `latentsInto H` and `H` stay in `latentsInto H`. -/
theorem mem_latentsInto_of_edge_mem (H : Finset {i : Fin n // i ∉ L}) (l j : Fin n)
    (hj : j ∈ b.latentsInto L H ∪ H.map (Function.Embedding.subtype _)) (hl : l ∈ L)
    (h : b.Edge l j) : l ∈ b.latentsInto L H := by
  simp only [latentsInto, Finset.mem_filter, Finset.mem_union] at hj ⊢
  refine ⟨hl, ?_⟩
  rcases hj with ⟨hjL, u, huH, hpath⟩ | hjmap
  · exact ⟨u, huH, b.latentPath_of_edge_latentPath L _ _ _ h hjL hpath⟩
  · rw [Finset.mem_map] at hjmap
    obtain ⟨a, haH, rfl⟩ := hjmap
    exact ⟨a, haH, b.latentPath_of_edge_direct L _ _ h⟩

omit [Fintype α] [DecidableEq α] [Nonempty α] in
/-- With no bidirected edge across the split, the two latent sets are disjoint. -/
theorem disjoint_latentsInto_sdiff (H T : Finset {i : Fin n // i ∉ L}) (_hTH : T ⊆ H)
    (hsep : ∀ u ∈ T, ∀ w ∈ H \ T, ¬ (b.latentProjection L).bidir.Adj u w) :
    Disjoint (b.latentsInto L T) (b.latentsInto L (H \ T)) := by
  rw [Finset.disjoint_left]
  intro l hlT hlHT
  simp only [latentsInto, Finset.mem_filter] at hlT hlHT
  obtain ⟨hlL, u, huT, hlu⟩ := hlT
  obtain ⟨-, w, hwHT, hlw⟩ := hlHT
  have hwT : w ∉ T := (Finset.mem_sdiff.mp hwHT).2
  have hne : u ≠ w := by
    rintro rfl
    exact hwT huT
  exact hsep u huT w hwHT ((b.latentProjection_bidir_adj_iff L u w).mpr ⟨hne, l, hlL, hlu, hlw⟩)

omit [Fintype α] [DecidableEq α] [Nonempty α] in
/-- `latentsInto` distributes over the split. -/
theorem latentsInto_union_sdiff (H T : Finset {i : Fin n // i ∉ L}) (hTH : T ⊆ H) :
    b.latentsInto L H = b.latentsInto L T ∪ b.latentsInto L (H \ T) := by
  ext l
  simp only [latentsInto, Finset.mem_filter, Finset.mem_union]
  constructor
  · rintro ⟨hlL, u, huH, hlu⟩
    by_cases huT : u ∈ T
    · exact Or.inl ⟨hlL, u, huT, hlu⟩
    · exact Or.inr ⟨hlL, u, Finset.mem_sdiff.mpr ⟨huH, huT⟩, hlu⟩
  · rintro (⟨hlL, u, huT, hlu⟩ | ⟨hlL, u, huHT, hlu⟩)
    · exact ⟨hlL, u, hTH huT, hlu⟩
    · exact ⟨hlL, u, (Finset.mem_sdiff.mp huHT).1, hlu⟩

omit [Fintype α] [DecidableEq α] [Nonempty α] in
/-- Latent parents of the truncated index set stay in `latentsInto H`. -/
theorem latentParent_mem_latentsInto (H : Finset {i : Fin n // i ∉ L}) (j u : Fin n)
    (hj : j ∈ b.latentsInto L H ∪ H.map (Function.Embedding.subtype _))
    (hpu : ∃ p : b.pa j, Fin.castLE j.2.le p = u) (huL : u ∈ L) :
    u ∈ b.latentsInto L H := by
  obtain ⟨⟨p, hp⟩, hpu⟩ := hpu
  have hval : p.val = u.val := congrArg Fin.val hpu
  have hlt : u.val < j.val := by
    rw [← hval]
    exact p.2
  have heq : (⟨u.val, hlt⟩ : Fin j) = p := Fin.ext hval.symm
  have hmem : (⟨u.val, hlt⟩ : Fin j) ∈ b.pa j := by
    rw [heq]
    exact hp
  exact b.mem_latentsInto_of_edge_mem L H u j hj huL ⟨hlt, hmem⟩

/-- Truncated-product form over the latents that reach `H`: only the
`latentsInto H` coordinates are summed; every other coordinate is fixed at `extendObs L v`. -/
theorem qFactor_eq_sum_prod_latentsInto (H : Finset {i : Fin n // i ∉ L})
(v : {i : Fin n // i ∉ L} → α) :
b.qFactor L H v = ∑ y with ∀ j ∉ b.latentsInto L H, y j = extendObs L v j,
∏ j ∈ b.latentsInto L H ∪ H.map (Function.Embedding.subtype _),
(b.cpt j (b.paVal j y)).weights (y j) := by
  classical
  have hext : ∀ a : {i : Fin n // i ∉ L}, extendObs L v ↑a = v a := by
    intro a
    unfold extendObs
    simp only [dite_eq_right a.2]
  have hLHsub : b.latentsInto L H ⊆ L := by
    intro l hl
    simp only [latentsInto, Finset.mem_filter] at hl
    exact hl.1
  have hHMcap : ∀ j ∈ H.map (Function.Embedding.subtype _), j ∉ L := by
    intro j hj
    simp only [Finset.mem_map] at hj
    obtain ⟨a, -, rfl⟩ := hj
    exact a.2
  have hsplit : L ∪ H.map (Function.Embedding.subtype _) =
      (b.latentsInto L H ∪ H.map (Function.Embedding.subtype _)) ∪
        (L \ b.latentsInto L H) := by
    ext j
    simp only [Finset.mem_union, Finset.mem_sdiff]
    constructor
    · rintro (hjL | hjM)
      · by_cases hjLH : j ∈ b.latentsInto L H
        · exact Or.inl (Or.inl hjLH)
        · exact Or.inr ⟨hjL, hjLH⟩
      · exact Or.inl (Or.inr hjM)
    · rintro ((hjLH | hjM) | ⟨hjL, -⟩)
      · exact Or.inl (hLHsub hjLH)
      · exact Or.inr hjM
      · exact Or.inl hjL
  have hdisj : Disjoint (b.latentsInto L H ∪ H.map (Function.Embedding.subtype _))
      (L \ b.latentsInto L H) := by
    rw [Finset.disjoint_left]
    intro j hj1 hj2
    simp only [Finset.mem_union, Finset.mem_sdiff] at hj1 hj2
    rcases hj1 with hjLH | hjM
    · exact hj2.2 hjLH
    · exact hHMcap j hjM hj2.1
  have hprod : ∀ y : Fin n → α,
      ∏ j ∈ L ∪ H.map (Function.Embedding.subtype _), (b.cpt j (b.paVal j y)).weights (y j) =
        (∏ j ∈ b.latentsInto L H ∪ H.map (Function.Embedding.subtype _),
          (b.cpt j (b.paVal j y)).weights (y j)) *
        ∏ j ∈ L \ b.latentsInto L H, (b.cpt j (b.paVal j y)).weights (y j) := by
    intro y
    rw [hsplit, Finset.prod_union hdisj]
  have hmaps : ∀ y ∈ univ.filter
      (fun y : Fin n → α => ∀ i : {i : Fin n // i ∉ L}, y i = v i),
      (fun y j => if j ∈ L \ b.latentsInto L H then extendObs L v j else y j) y ∈
        univ.filter (fun y : Fin n → α => ∀ j ∉ b.latentsInto L H, y j = extendObs L v j) := by
    intro y hy
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
    intro j hjLH
    show (if j ∈ L \ b.latentsInto L H then extendObs L v j else y j) = extendObs L v j
    by_cases hjB : j ∈ L \ b.latentsInto L H
    · rw [ite_eq_left hjB]
    · rw [ite_eq_right hjB]
      have hjL : j ∉ L := fun hjL => hjB (Finset.mem_sdiff.mpr ⟨hjL, hjLH⟩)
      exact (hy ⟨j, hjL⟩).trans (hext ⟨j, hjL⟩).symm
  have hinner : ∀ z ∈ univ.filter
      (fun y : Fin n → α => ∀ j ∉ b.latentsInto L H, y j = extendObs L v j),
      (∑ w ∈ (univ.filter (fun y : Fin n → α => ∀ i : {i : Fin n // i ∉ L}, y i = v i)).filter
        (fun w => (fun y j => if j ∈ L \ b.latentsInto L H then extendObs L v j else y j) w = z),
        ∏ j ∈ L ∪ H.map (Function.Embedding.subtype _),
          (b.cpt j (b.paVal j w)).weights (w j)) =
      ∏ j ∈ b.latentsInto L H ∪ H.map (Function.Embedding.subtype _),
        (b.cpt j (b.paVal j z)).weights (z j) := by
    intro z hz
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz
    have hset : (univ.filter (fun y : Fin n → α => ∀ i : {i : Fin n // i ∉ L}, y i = v i)).filter
          (fun w => (fun y j => if j ∈ L \ b.latentsInto L H then extendObs L v j else y j) w = z) =
          univ.filter (fun w : Fin n → α => ∀ j ∉ L \ b.latentsInto L H, w j = z j) := by
      ext w
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨-, hφz⟩ j hjB
        have h : (if j ∈ L \ b.latentsInto L H then extendObs L v j else w j) = z j :=
          congrFun hφz j
        rw [ite_eq_right hjB] at h
        exact h
      · intro hw
        refine ⟨?_, ?_⟩
        · intro i
          have hiB : (↑i : Fin n) ∉ L \ b.latentsInto L H :=
            fun hcon => i.2 (Finset.sdiff_subset hcon)
          have hiLH : (↑i : Fin n) ∉ b.latentsInto L H := fun h => i.2 (hLHsub h)
          rw [hw _ hiB, hz _ hiLH]
          exact hext i
        · funext j
          show (if j ∈ L \ b.latentsInto L H then extendObs L v j else w j) = z j
          by_cases hjB : j ∈ L \ b.latentsInto L H
          · rw [ite_eq_left hjB]
            exact (hz j (Finset.mem_sdiff.mp hjB).2).symm
          · rw [ite_eq_right hjB]
            exact hw j hjB
    rw [hset]
    have hFw : ∀ w : Fin n → α, (∀ j ∉ L \ b.latentsInto L H, w j = z j) →
        (∏ j ∈ b.latentsInto L H ∪ H.map (Function.Embedding.subtype _),
          (b.cpt j (b.paVal j w)).weights (w j)) =
        ∏ j ∈ b.latentsInto L H ∪ H.map (Function.Embedding.subtype _),
          (b.cpt j (b.paVal j z)).weights (z j) := by
      intro w hw
      have hdep := b.dependsOn_prod_cpt
        (b.latentsInto L H ∪ H.map (Function.Embedding.subtype _))
      refine hdep (fun u hu => ?_)
      simp only [Set.mem_union, Finset.mem_coe, Set.mem_ofPred_eq] at hu
      rcases hu with hu | ⟨j, hj, p, hpu⟩
      · have huB : u ∉ L \ b.latentsInto L H := by
          intro hcon
          obtain ⟨huL, huLH⟩ := Finset.mem_sdiff.mp hcon
          simp only [Finset.mem_union] at hu
          rcases hu with huLH' | huM
          · exact huLH huLH'
          · exact hHMcap u huM huL
        exact hw u huB
      · by_cases huL : u ∈ L
        · have huLH : u ∈ b.latentsInto L H :=
            b.latentParent_mem_latentsInto L H j u hj ⟨p, hpu⟩ huL
          have huB : u ∉ L \ b.latentsInto L H :=
            fun hcon => (Finset.mem_sdiff.mp hcon).2 huLH
          exact hw u huB
        · have huB : u ∉ L \ b.latentsInto L H := fun hcon => huL (Finset.sdiff_subset hcon)
          exact hw u huB
    calc (∑ w ∈ univ.filter (fun w : Fin n → α => ∀ j ∉ L \ b.latentsInto L H, w j = z j),
            ∏ j ∈ L ∪ H.map (Function.Embedding.subtype _),
              (b.cpt j (b.paVal j w)).weights (w j))
        = ∑ w ∈ univ.filter (fun w : Fin n → α => ∀ j ∉ L \ b.latentsInto L H, w j = z j),
            (∏ j ∈ b.latentsInto L H ∪ H.map (Function.Embedding.subtype _),
              (b.cpt j (b.paVal j w)).weights (w j)) *
            ∏ j ∈ L \ b.latentsInto L H, (b.cpt j (b.paVal j w)).weights (w j) :=
          Finset.sum_congr rfl (fun w _ => hprod w)
      _ = ∑ w ∈ univ.filter (fun w : Fin n → α => ∀ j ∉ L \ b.latentsInto L H, w j = z j),
            (∏ j ∈ b.latentsInto L H ∪ H.map (Function.Embedding.subtype _),
              (b.cpt j (b.paVal j z)).weights (z j)) *
            ∏ j ∈ L \ b.latentsInto L H, (b.cpt j (b.paVal j w)).weights (w j) := by
          refine Finset.sum_congr rfl (fun w hmem => ?_)
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hmem
          rw [hFw w hmem]
      _ = (∏ j ∈ b.latentsInto L H ∪ H.map (Function.Embedding.subtype _),
              (b.cpt j (b.paVal j z)).weights (z j)) *
            ∑ w ∈ univ.filter (fun w : Fin n → α => ∀ j ∉ L \ b.latentsInto L H, w j = z j),
              ∏ j ∈ L \ b.latentsInto L H, (b.cpt j (b.paVal j w)).weights (w j) :=
          (Finset.mul_sum _ _ _).symm
      _ = ∏ j ∈ b.latentsInto L H ∪ H.map (Function.Embedding.subtype _),
            (b.cpt j (b.paVal j z)).weights (z j) := by
          rw [b.sum_prod_cpt_filter_eq_one (L \ b.latentsInto L H) z, mul_one]
  calc b.qFactor L H v
      = ∑ y ∈ univ.filter (fun y : Fin n → α => ∀ i : {i : Fin n // i ∉ L}, y i = v i),
          ∏ j ∈ L ∪ H.map (Function.Embedding.subtype _),
            (b.cpt j (b.paVal j y)).weights (y j) := b.qFactor_eq_sum_prod L H v
    _ = ∑ z ∈ univ.filter (fun y : Fin n → α => ∀ j ∉ b.latentsInto L H, y j = extendObs L v j),
          ∑ w ∈ (univ.filter (fun y : Fin n → α => ∀ i : {i : Fin n // i ∉ L}, y i = v i)).filter
            (fun w => (fun y j => if j ∈ L \ b.latentsInto L H then extendObs L v j else y j) w = z),
          ∏ j ∈ L ∪ H.map (Function.Embedding.subtype _),
            (b.cpt j (b.paVal j w)).weights (w j) :=
        (Finset.sum_fiberwise_of_maps_to hmaps _).symm
    _ = ∑ z ∈ univ.filter (fun y : Fin n → α => ∀ j ∉ b.latentsInto L H, y j = extendObs L v j),
          ∏ j ∈ b.latentsInto L H ∪ H.map (Function.Embedding.subtype _),
            (b.cpt j (b.paVal j z)).weights (z j) :=
        Finset.sum_congr rfl (fun z hz => hinner z hz)
    _ = ∑ y with ∀ j ∉ b.latentsInto L H, y j = extendObs L v j,
          ∏ j ∈ b.latentsInto L H ∪ H.map (Function.Embedding.subtype _),
            (b.cpt j (b.paVal j y)).weights (y j) := rfl

/-- G0, TR Lemma 4(i) for a split with no bidirected edge across it. -/
theorem qFactor_eq_mul_of_not_adj {H T : Finset {i : Fin n // i ∉ L}} (hTH : T ⊆ H)
    (hsep : ∀ u ∈ T, ∀ w ∈ H \ T, ¬ (b.latentProjection L).bidir.Adj u w)
    (v : {i : Fin n // i ∉ L} → α) :
    b.qFactor L H v = b.qFactor L T v * b.qFactor L (H \ T) v := by
  classical
  have hTUR : T ∪ H \ T = H := Finset.union_sdiff_of_subset hTH
  have hLH : b.latentsInto L H = b.latentsInto L T ∪ b.latentsInto L (H \ T) :=
    b.latentsInto_union_sdiff L H T hTH
  have hdisjL : Disjoint (b.latentsInto L T) (b.latentsInto L (H \ T)) :=
    b.disjoint_latentsInto_sdiff L H T hTH hsep
  have hLTsub : b.latentsInto L T ⊆ b.latentsInto L H := by
    rw [hLH]
    exact Finset.subset_union_left
  have hLRsub : b.latentsInto L (H \ T) ⊆ b.latentsInto L H := by
    rw [hLH]
    exact Finset.subset_union_right
  have hLHsubL : b.latentsInto L H ⊆ L := by
    intro l hl
    simp only [latentsInto, Finset.mem_filter] at hl
    exact hl.1
  have hmapH : H.map (Function.Embedding.subtype _) =
      T.map (Function.Embedding.subtype _) ∪ (H \ T).map (Function.Embedding.subtype _) := by
    conv_lhs => rw [← hTUR]
    rw [Finset.map_union]
  have hI : b.latentsInto L H ∪ H.map (Function.Embedding.subtype _) =
      (b.latentsInto L T ∪ T.map (Function.Embedding.subtype _)) ∪
        (b.latentsInto L (H \ T) ∪ (H \ T).map (Function.Embedding.subtype _)) := by
    rw [hLH, hmapH]
    ext j
    simp only [Finset.mem_union]
    tauto
  have hdisjI : Disjoint (b.latentsInto L T ∪ T.map (Function.Embedding.subtype _))
      (b.latentsInto L (H \ T) ∪ (H \ T).map (Function.Embedding.subtype _)) := by
    rw [Finset.disjoint_left]
    intro j hj1 hj2
    simp only [Finset.mem_union] at hj1 hj2
    rcases hj1 with hjLT | hjTM
    · rcases hj2 with hjLR | hjRM
      · exact Finset.disjoint_left.mp hdisjL hjLT hjLR
      · rw [Finset.mem_map] at hjRM
        obtain ⟨a, -, rfl⟩ := hjRM
        exact a.2 (hLHsubL (hLTsub hjLT))
    · rw [Finset.mem_map] at hjTM
      obtain ⟨a, haT, rfl⟩ := hjTM
      rcases hj2 with hjLR | hjRM
      · exact a.2 (hLHsubL (hLRsub hjLR))
      · rw [Finset.mem_map] at hjRM
        obtain ⟨a', ha'R, hval⟩ := hjRM
        have heq : a = a' := Subtype.ext hval.symm
        subst heq
        exact (Finset.mem_sdiff.mp ha'R).2 haT
  have hF : ∀ y : Fin n → α,
      (∏ j ∈ b.latentsInto L H ∪ H.map (Function.Embedding.subtype _),
        (b.cpt j (b.paVal j y)).weights (y j)) =
      (∏ j ∈ b.latentsInto L T ∪ T.map (Function.Embedding.subtype _),
        (b.cpt j (b.paVal j y)).weights (y j)) *
      ∏ j ∈ b.latentsInto L (H \ T) ∪ (H \ T).map (Function.Embedding.subtype _),
        (b.cpt j (b.paVal j y)).weights (y j) := by
    intro y
    rw [hI, Finset.prod_union hdisjI]
  have hf : DependsOn (fun y : Fin n → α => ∏ j ∈ b.latentsInto L T ∪
      T.map (Function.Embedding.subtype _), (b.cpt j (b.paVal j y)).weights (y j))
      ((↑(b.latentsInto L T) ∪ ↑((b.latentsInto L H)ᶜ)) : Set (Fin n)) := by
    have hdep := b.dependsOn_prod_cpt
      (b.latentsInto L T ∪ T.map (Function.Embedding.subtype _))
    intro x y hxy
    refine hdep (fun u hu => ?_)
    simp only [Set.mem_union, Finset.mem_coe, Set.mem_ofPred_eq] at hu
    rcases hu with hu | ⟨j, hj, p, hpu⟩
    · simp only [Finset.mem_union, Finset.mem_map] at hu
      rcases hu with huLT | ⟨a, -, rfl⟩
      · exact hxy u (Or.inl (Finset.mem_coe.mpr huLT))
      · exact hxy _ (Or.inr (Finset.mem_coe.mpr
          (Finset.mem_compl.mpr (fun hcon => a.2 (hLHsubL hcon)))))
    · by_cases huL : u ∈ L
      · have huLT : u ∈ b.latentsInto L T :=
          b.latentParent_mem_latentsInto L T j u hj ⟨p, hpu⟩ huL
        exact hxy u (Or.inl (Finset.mem_coe.mpr huLT))
      · exact hxy u (Or.inr (Finset.mem_coe.mpr
          (Finset.mem_compl.mpr (fun hcon => huL (hLHsubL hcon)))))
  have hg : DependsOn (fun y : Fin n → α => ∏ j ∈ b.latentsInto L (H \ T) ∪
      (H \ T).map (Function.Embedding.subtype _), (b.cpt j (b.paVal j y)).weights (y j))
      ((↑(b.latentsInto L (H \ T)) ∪ ↑((b.latentsInto L H)ᶜ)) : Set (Fin n)) := by
    have hdep := b.dependsOn_prod_cpt
      (b.latentsInto L (H \ T) ∪ (H \ T).map (Function.Embedding.subtype _))
    intro x y hxy
    refine hdep (fun u hu => ?_)
    simp only [Set.mem_union, Finset.mem_coe, Set.mem_ofPred_eq] at hu
    rcases hu with hu | ⟨j, hj, p, hpu⟩
    · simp only [Finset.mem_union, Finset.mem_map] at hu
      rcases hu with huLR | ⟨a, -, rfl⟩
      · exact hxy u (Or.inl (Finset.mem_coe.mpr huLR))
      · exact hxy _ (Or.inr (Finset.mem_coe.mpr
          (Finset.mem_compl.mpr (fun hcon => a.2 (hLHsubL hcon)))))
    · by_cases huL : u ∈ L
      · have huLR : u ∈ b.latentsInto L (H \ T) :=
          b.latentParent_mem_latentsInto L (H \ T) j u hj ⟨p, hpu⟩ huL
        exact hxy u (Or.inl (Finset.mem_coe.mpr huLR))
      · exact hxy u (Or.inr (Finset.mem_coe.mpr
          (Finset.mem_compl.mpr (fun hcon => huL (hLHsubL hcon)))))
  have hPQ : ∀ v : Fin n, v ∈ ((↑(b.latentsInto L T) ∪ ↑((b.latentsInto L H)ᶜ)) : Set (Fin n)) ∨
      v ∈ ((↑(b.latentsInto L (H \ T)) ∪ ↑((b.latentsInto L H)ᶜ)) : Set (Fin n)) := by
    intro v
    by_cases hv : v ∈ b.latentsInto L H
    · rw [hLH, Finset.mem_union] at hv
      rcases hv with hvT | hvR
      · exact Or.inl (Or.inl (Finset.mem_coe.mpr hvT))
      · exact Or.inr (Or.inl (Finset.mem_coe.mpr hvR))
    · exact Or.inl (Or.inr (Finset.mem_coe.mpr (Finset.mem_compl.mpr hv)))
  have hU : ((↑(b.latentsInto L T) ∪ ↑((b.latentsInto L H)ᶜ)) : Set (Fin n)) ∩
      ((↑(b.latentsInto L (H \ T)) ∪ ↑((b.latentsInto L H)ᶜ)) : Set (Fin n)) ⊆ ↑((b.latentsInto L H)ᶜ) := by
    intro v hv
    simp only [Set.mem_inter_iff, Set.mem_union] at hv
    obtain ⟨hvP, hvQ⟩ := hv
    rcases hvP with hvT | hvC
    · rcases hvQ with hvR | hvC'
      · exact False.elim (Finset.disjoint_left.mp hdisjL (Finset.mem_coe.mp hvT)
          (Finset.mem_coe.mp hvR))
      · exact hvC'
    · exact hvC
  have hmul := marginal_mul hf hg hPQ hU (extendObs L v)
  have bH : marginal ((fun y : Fin n → α => ∏ j ∈ b.latentsInto L T ∪
        T.map (Function.Embedding.subtype _), (b.cpt j (b.paVal j y)).weights (y j)) *
        (fun y : Fin n → α => ∏ j ∈ b.latentsInto L (H \ T) ∪
        (H \ T).map (Function.Embedding.subtype _), (b.cpt j (b.paVal j y)).weights (y j)))
      ↑((b.latentsInto L H)ᶜ) (extendObs L v) =
      ∑ y with ∀ j ∉ b.latentsInto L H, y j = extendObs L v j,
        ∏ j ∈ b.latentsInto L H ∪ H.map (Function.Embedding.subtype _),
          (b.cpt j (b.paVal j y)).weights (y j) := by
    unfold marginal
    refine Finset.sum_congr ?_ (fun y _ => ?_)
    · ext y
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · intro h j hj
        exact h j (Finset.mem_coe.mpr (Finset.mem_compl.mpr hj))
      · intro h v hv
        exact h v (Finset.mem_compl.mp (Finset.mem_coe.mp hv))
    · rw [Pi.mul_apply]
      exact (hF y).symm
  have bT : marginal (fun y : Fin n → α => ∏ j ∈ b.latentsInto L T ∪
        T.map (Function.Embedding.subtype _), (b.cpt j (b.paVal j y)).weights (y j))
      (↑((b.latentsInto L H)ᶜ) ∪ ((↑(b.latentsInto L T) ∪ ↑((b.latentsInto L H)ᶜ)) : Set (Fin n))ᶜ)
      (extendObs L v) =
      ∑ y with ∀ j ∉ b.latentsInto L T, y j = extendObs L v j,
        ∏ j ∈ b.latentsInto L T ∪ T.map (Function.Embedding.subtype _),
          (b.cpt j (b.paVal j y)).weights (y j) := by
    unfold marginal
    refine Finset.sum_congr ?_ (fun y _ => rfl)
    ext y
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro h j hj
      by_cases hjH : j ∈ b.latentsInto L H
      · refine h j (Or.inr ?_)
        rw [Set.mem_compl_iff]
        intro hcon
        simp only [Set.mem_union, Finset.mem_coe, Finset.mem_compl] at hcon
        rcases hcon with hcon | hcon
        · exact hj hcon
        · exact hcon hjH
      · exact h j (Or.inl (Finset.mem_coe.mpr (Finset.mem_compl.mpr hjH)))
    · intro h v hv
      rcases hv with hv | hv
      · apply h v
        intro hvT
        exact Finset.mem_compl.mp (Finset.mem_coe.mp hv) (hLTsub hvT)
      · apply h v
        intro hvT
        rw [Set.mem_compl_iff] at hv
        exact hv (Or.inl (Finset.mem_coe.mpr hvT))
  have bR : marginal (fun y : Fin n → α => ∏ j ∈ b.latentsInto L (H \ T) ∪
        (H \ T).map (Function.Embedding.subtype _), (b.cpt j (b.paVal j y)).weights (y j))
      (↑((b.latentsInto L H)ᶜ) ∪ ((↑(b.latentsInto L (H \ T)) ∪ ↑((b.latentsInto L H)ᶜ)) : Set (Fin n))ᶜ)
      (extendObs L v) =
      ∑ y with ∀ j ∉ b.latentsInto L (H \ T), y j = extendObs L v j,
        ∏ j ∈ b.latentsInto L (H \ T) ∪ (H \ T).map (Function.Embedding.subtype _),
          (b.cpt j (b.paVal j y)).weights (y j) := by
    unfold marginal
    refine Finset.sum_congr ?_ (fun y _ => rfl)
    ext y
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro h j hj
      by_cases hjH : j ∈ b.latentsInto L H
      · refine h j (Or.inr ?_)
        rw [Set.mem_compl_iff]
        intro hcon
        simp only [Set.mem_union, Finset.mem_coe, Finset.mem_compl] at hcon
        rcases hcon with hcon | hcon
        · exact hj hcon
        · exact hcon hjH
      · exact h j (Or.inl (Finset.mem_coe.mpr (Finset.mem_compl.mpr hjH)))
    · intro h v hv
      rcases hv with hv | hv
      · apply h v
        intro hvR
        exact Finset.mem_compl.mp (Finset.mem_coe.mp hv) (hLRsub hvR)
      · apply h v
        intro hvR
        rw [Set.mem_compl_iff] at hv
        exact hv (Or.inl (Finset.mem_coe.mpr hvR))
  have hH := b.qFactor_eq_sum_prod_latentsInto L H v
  have hTT := b.qFactor_eq_sum_prod_latentsInto L T v
  have hR := b.qFactor_eq_sum_prod_latentsInto L (H \ T) v
  rw [hH, hTT, hR, ← bH, ← bT, ← bR]
  exact hmul

/-- G0 for a partition of `H` into blocks with no bidirected edge between blocks (TR (70)). -/
theorem qFactor_eq_prod_of_not_adj {H : Finset {i : Fin n // i ∉ L}}
    (𝒯 : Finset (Finset {i : Fin n // i ∉ L}))
    (hdisj : (𝒯 : Set (Finset {i : Fin n // i ∉ L})).PairwiseDisjoint id)
    (hcov : 𝒯.biUnion id = H)
    (hsep : ∀ T ∈ 𝒯, ∀ T' ∈ 𝒯, T ≠ T' → ∀ u ∈ T, ∀ w ∈ T',
      ¬ (b.latentProjection L).bidir.Adj u w) (v : {i : Fin n // i ∉ L} → α) :
    b.qFactor L H v = ∏ T ∈ 𝒯, b.qFactor L T v := by
  classical
  revert H hdisj hcov hsep v
  induction 𝒯 using Finset.induction with
  | empty =>
    intro H hdisj hcov hsep v
    rw [Finset.biUnion_empty] at hcov
    subst hcov
    rw [b.qFactor_empty L v, Finset.prod_empty]
  | insert T 𝒯' hTmem ih =>
    intro H hdisj hcov hsep v
    have hbi : (insert T 𝒯').biUnion id = T ∪ 𝒯'.biUnion id := Finset.biUnion_insert
    have hH : H = T ∪ 𝒯'.biUnion id := by
      rw [← hcov, hbi]
    have hsubT : T ⊆ H := by
      rw [hH]
      exact Finset.subset_union_left
    have hTR : Disjoint T (𝒯'.biUnion id) := by
      rw [Finset.disjoint_biUnion_right]
      intro T' hT'
      have hne : T ≠ T' := by
        rintro rfl
        exact hTmem hT'
      exact hdisj (Finset.mem_coe.mpr (Finset.mem_insert_self T 𝒯'))
        (Finset.mem_coe.mpr (Finset.mem_insert_of_mem hT')) hne
    have hHT : H \ T = 𝒯'.biUnion id := by
      rw [hH]
      ext w
      simp only [Finset.mem_union, Finset.mem_sdiff]
      constructor
      · rintro ⟨hwT | hwR, hwT'⟩
        · exact absurd hwT hwT'
        · exact hwR
      · intro hwR
        refine ⟨Or.inr hwR, ?_⟩
        intro hwT
        exact Finset.disjoint_left.mp hTR hwT hwR
    have hsepT : ∀ u ∈ T, ∀ w ∈ H \ T, ¬ (b.latentProjection L).bidir.Adj u w := by
      intro u huT w hwHT
      rw [Finset.mem_sdiff] at hwHT
      obtain ⟨hwH, hwT⟩ := hwHT
      rw [hH, Finset.mem_union] at hwH
      rcases hwH with hwT' | hwR
      · exact absurd hwT' hwT
      · rw [Finset.mem_biUnion] at hwR
        obtain ⟨T', hT'𝒯, hwT'⟩ := hwR
        have hne : T ≠ T' := by
          rintro rfl
          exact hTmem hT'𝒯
        exact hsep T (Finset.mem_insert_self T 𝒯') T' (Finset.mem_insert_of_mem hT'𝒯)
          hne u huT w hwT'
    have hbin := b.qFactor_eq_mul_of_not_adj L hsubT hsepT v
    have hdisj' : (𝒯' : Set (Finset {i : Fin n // i ∉ L})).PairwiseDisjoint id := by
      intro x hx y hy hne
      exact hdisj (Finset.mem_coe.mpr (Finset.mem_insert_of_mem (Finset.mem_coe.mp hx)))
        (Finset.mem_coe.mpr (Finset.mem_insert_of_mem (Finset.mem_coe.mp hy))) hne
    have hsep' : ∀ T1 ∈ 𝒯', ∀ T2 ∈ 𝒯', T1 ≠ T2 → ∀ u ∈ T1, ∀ w ∈ T2,
        ¬ (b.latentProjection L).bidir.Adj u w := by
      intro T1 h1 T2 h2 hne u hu w hw
      exact hsep T1 (Finset.mem_insert_of_mem h1) T2 (Finset.mem_insert_of_mem h2)
        hne u hu w hw
    have ih' := ih hdisj' rfl hsep' v
    rw [hbin, hHT, ih', Finset.prod_insert hTmem]

omit [Fintype α] [DecidableEq α] [Nonempty α] in
/-- `latentsInto` is monotone. -/
theorem latentsInto_mono {H A : Finset {i : Fin n // i ∉ L}} (hAH : A ⊆ H) :
    b.latentsInto L A ⊆ b.latentsInto L H := by
  intro l hl
  simp only [latentsInto, Finset.mem_filter] at hl ⊢
  obtain ⟨hlL, u, huA, hlu⟩ := hl
  exact ⟨hlL, u, hAH huA, hlu⟩

/-- L3, TR Lemma 3 (69): no projection edge from `H ∖ A` into `A`. -/
theorem marginal_qFactor_of_ancestral {H A : Finset {i : Fin n // i ∉ L}} (hAH : A ⊆ H)
    (hanc : ∀ ⦃u w⦄, (b.latentProjection L).dir u w → u ∈ H → w ∈ A → u ∈ A)
    (v : {i : Fin n // i ∉ L} → α) :
    marginal (b.qFactor L H) (↑(H \ A))ᶜ v = b.qFactor L A v := by
  classical
  have hAsubH : b.latentsInto L A ⊆ b.latentsInto L H := b.latentsInto_mono L hAH
  have hLHsubL : b.latentsInto L H ⊆ L := by
    intro l hl
    simp only [latentsInto, Finset.mem_filter] at hl
    exact hl.1
  have hLAsubL : b.latentsInto L A ⊆ L := fun l hl => hLHsubL (hAsubH hl)
  have hAMcap : ∀ j ∈ A.map (Function.Embedding.subtype _), j ∉ L := by
    intro j hj
    simp only [Finset.mem_map] at hj
    obtain ⟨a, -, rfl⟩ := hj
    exact a.2
  have hHMAcap : ∀ j ∈ (H \ A).map (Function.Embedding.subtype _), j ∉ L := by
    intro j hj
    simp only [Finset.mem_map] at hj
    obtain ⟨a, -, rfl⟩ := hj
    exact a.2
  set B : Finset (Fin n) :=
    (H \ A).map (Function.Embedding.subtype _) ∪ (b.latentsInto L H \ b.latentsInto L A) with hBdef
  have hmapH : H.map (Function.Embedding.subtype _) =
      A.map (Function.Embedding.subtype _) ∪ (H \ A).map (Function.Embedding.subtype _) := by
    conv_lhs => rw [← Finset.union_sdiff_of_subset hAH]
    rw [Finset.map_union]
  have hlatH : b.latentsInto L H =
      b.latentsInto L A ∪ (b.latentsInto L H \ b.latentsInto L A) :=
    (Finset.union_sdiff_of_subset hAsubH).symm
  have hIdxUnion : b.latentsInto L H ∪ H.map (Function.Embedding.subtype _) =
      (b.latentsInto L A ∪ A.map (Function.Embedding.subtype _)) ∪ B := by
    rw [hlatH, hmapH, hBdef]
    ext j
    simp only [Finset.mem_union]
    tauto
  have hIdxDisj : Disjoint (b.latentsInto L A ∪ A.map (Function.Embedding.subtype _)) B := by
    rw [hBdef, Finset.disjoint_left]
    intro j hj1 hj2
    simp only [Finset.mem_union, Finset.mem_sdiff] at hj1 hj2
    rcases hj1 with hjLA | hjAM
    · rcases hj2 with hjHM | ⟨hjLH, hjLA'⟩
      · exact hHMAcap j hjHM (hLAsubL hjLA)
      · exact hjLA' hjLA
    · rcases hj2 with hjHM | ⟨hjLH, -⟩
      · simp only [Finset.mem_map] at hjAM hjHM
        obtain ⟨a, haA, rfl⟩ := hjAM
        obtain ⟨a', ha'HA, hval⟩ := hjHM
        have heq : a = a' := Subtype.ext hval.symm
        subst heq
        exact (Finset.mem_sdiff.mp ha'HA).2 haA
      · exact hAMcap _ hjAM (hLHsubL hjLH)
  have hProdSplit : ∀ y : Fin n → α,
      (∏ j ∈ b.latentsInto L H ∪ H.map (Function.Embedding.subtype _),
        (b.cpt j (b.paVal j y)).weights (y j)) =
      (∏ j ∈ b.latentsInto L A ∪ A.map (Function.Embedding.subtype _),
        (b.cpt j (b.paVal j y)).weights (y j)) *
      ∏ j ∈ B, (b.cpt j (b.paVal j y)).weights (y j) := by
    intro y
    rw [hIdxUnion, Finset.prod_union hIdxDisj]
  have hParNotB : ∀ j ∈ b.latentsInto L A ∪ A.map (Function.Embedding.subtype _),
      ∀ u : Fin n, (∃ p : b.pa j, Fin.castLE j.2.le p = u) → u ∉ B := by
    intro j hj u hpu
    by_cases huL : u ∈ L
    · have huLA := b.latentParent_mem_latentsInto L A j u hj hpu huL
      intro huB
      rw [hBdef] at huB
      simp only [Finset.mem_union, Finset.mem_sdiff] at huB
      rcases huB with huHM | ⟨_, huLA'⟩
      · exact hHMAcap u huHM (hLAsubL huLA)
      · exact huLA' huLA
    · obtain ⟨⟨p, hp⟩, hpu'⟩ := hpu
      have hval : p.val = u.val := congrArg Fin.val hpu'
      have hlt : u.val < j.val := by
        rw [← hval]
        exact p.2
      have heq : (⟨u.val, hlt⟩ : Fin j) = p := Fin.ext hval.symm
      have hmem : (⟨u.val, hlt⟩ : Fin j) ∈ b.pa j := by
        rw [heq]
        exact hp
      have hedge : b.Edge u j := ⟨hlt, hmem⟩
      intro huB
      rw [hBdef] at huB
      simp only [Finset.mem_union] at huB
      have huHM : u ∈ (H \ A).map (Function.Embedding.subtype _) := by
        rcases huB with huHM | huLat
        · exact huHM
        · exfalso
          exact huL (hLHsubL (Finset.mem_sdiff.mp huLat |>.1))
      simp only [Finset.mem_map] at huHM
      obtain ⟨a, haHA, hvalAu⟩ := huHM
      obtain ⟨haH, haA⟩ := Finset.mem_sdiff.mp haHA
      simp only [Finset.mem_union] at hj
      rcases hj with hjLA | hjAM
      · simp only [latentsInto, Finset.mem_filter] at hjLA
        obtain ⟨hjL, a0, ha0A, hjpath⟩ := hjLA
        have hpath : b.LatentPath L u ↑a0 :=
          b.latentPath_of_edge_latentPath L u j ↑a0 hedge hjL hjpath
        have hdir : (b.latentProjection L).dir ⟨u, huL⟩ a0 :=
          (b.latentProjection_dir_iff L _ _).mpr hpath
        have heqU : (⟨u, huL⟩ : {i : Fin n // i ∉ L}) = a := Subtype.ext hvalAu.symm
        have huH : (⟨u, huL⟩ : {i : Fin n // i ∉ L}) ∈ H := by
          rw [heqU]
          exact haH
        have huA : (⟨u, huL⟩ : {i : Fin n // i ∉ L}) ∈ A := hanc hdir huH ha0A
        rw [heqU] at huA
        exact haA huA
      · simp only [Finset.mem_map] at hjAM
        obtain ⟨a0, ha0A, hval0⟩ := hjAM
        have hpath : b.LatentPath L u j := b.latentPath_of_edge_direct L u j hedge
        rw [← hval0] at hpath
        have hdir : (b.latentProjection L).dir ⟨u, huL⟩ a0 :=
          (b.latentProjection_dir_iff L _ _).mpr hpath
        have heqU : (⟨u, huL⟩ : {i : Fin n // i ∉ L}) = a := Subtype.ext hvalAu.symm
        have huH : (⟨u, huL⟩ : {i : Fin n // i ∉ L}) ∈ H := by
          rw [heqU]
          exact haH
        have huA : (⟨u, huL⟩ : {i : Fin n // i ∉ L}) ∈ A := hanc hdir huH ha0A
        rw [heqU] at huA
        exact haA huA
  have hDepEq : ∀ z w : Fin n → α, (∀ j ∉ B, z j = w j) →
      (∏ j ∈ b.latentsInto L A ∪ A.map (Function.Embedding.subtype _),
        (b.cpt j (b.paVal j z)).weights (z j)) =
      ∏ j ∈ b.latentsInto L A ∪ A.map (Function.Embedding.subtype _),
        (b.cpt j (b.paVal j w)).weights (w j) := by
    intro z w hzw
    have hdep := b.dependsOn_prod_cpt
      (b.latentsInto L A ∪ A.map (Function.Embedding.subtype _))
    refine hdep (fun u hu => ?_)
    simp only [Set.mem_union, Finset.mem_coe, Set.mem_ofPred_eq] at hu
    rcases hu with hu | ⟨j, hj, p, hpu⟩
    · have huB : u ∉ B := fun hcon =>
        Finset.disjoint_left.mp hIdxDisj hu hcon
      exact hzw u huB
    · have huB : u ∉ B := hParNotB j hj u ⟨p, hpu⟩
      exact hzw u huB
  have hextV : ∀ a : {i : Fin n // i ∉ L}, extendObs L v ↑a = v a := by
    intro a
    unfold extendObs
    simp only [dite_eq_right a.2]
  have hLHS : marginal (b.qFactor L H) (↑(H \ A))ᶜ v =
      ∑ y with ∀ a ∉ H \ A, y a = v a, b.qFactor L H y := by
    unfold marginal
    refine Finset.sum_congr ?_ (fun y _ => rfl)
    ext y
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro h a haHA
      apply h a
      rw [Set.mem_compl_iff]
      intro hcon
      exact haHA (Finset.mem_coe.mp hcon)
    · intro h a haCompl
      apply h a
      intro haHA
      exact (Set.mem_compl_iff _ _).mp haCompl (Finset.mem_coe.mpr haHA)
  have hT0A := b.qFactor_eq_sum_prod_latentsInto L A v
  have hExtLat : ∀ (y1 y2 : {i : Fin n // i ∉ L} → α) (j : Fin n) (hjL : j ∈ L),
      extendObs L y1 j = extendObs L y2 j := by
    intro y1 y2 j hjL
    unfold extendObs
    simp only [dite_eq_left hjL]
  have hExtObs : ∀ (y : {i : Fin n // i ∉ L} → α) (j : Fin n) (hjL : j ∉ L),
      extendObs L y j = y ⟨j, hjL⟩ := by
    intro y j hjL
    unfold extendObs
    simp only [dite_eq_right hjL]
  have hMapMem : ∀ (j : Fin n) (hjL : j ∉ L),
      (j ∈ (H \ A).map (Function.Embedding.subtype _) ↔ ⟨j, hjL⟩ ∈ H \ A) := by
    intro j hjL
    constructor
    · intro hj
      simp only [Finset.mem_map] at hj
      obtain ⟨a, haHA, hval⟩ := hj
      have heq : (⟨j, hjL⟩ : {i : Fin n // i ∉ L}) = a := Subtype.ext hval.symm
      rw [heq]
      exact haHA
    · intro haHA
      simp only [Finset.mem_map]
      exact ⟨⟨j, hjL⟩, haHA, rfl⟩
  have hDouble : marginal (b.qFactor L H) (↑(H \ A))ᶜ v =
      ∑ y with ∀ a ∉ H \ A, y a = v a,
        ∑ z with ∀ j ∉ b.latentsInto L H, z j = extendObs L y j,
          ∏ j ∈ b.latentsInto L H ∪ H.map (Function.Embedding.subtype _),
            (b.cpt j (b.paVal j z)).weights (z j) := by
    rw [hLHS]
    refine Finset.sum_congr rfl (fun y _ => ?_)
    rw [b.qFactor_eq_sum_prod_latentsInto L H y]
  have hSigma : (∑ y with ∀ a ∉ H \ A, y a = v a,
        ∑ z with ∀ j ∉ b.latentsInto L H, z j = extendObs L y j,
          ∏ j ∈ b.latentsInto L H ∪ H.map (Function.Embedding.subtype _),
            (b.cpt j (b.paVal j z)).weights (z j)) =
      ∑ p ∈ (univ.filter (fun y : {i : Fin n // i ∉ L} → α => ∀ a ∉ H \ A, y a = v a)).sigma
        (fun y => univ.filter (fun z : Fin n → α => ∀ j ∉ b.latentsInto L H, z j = extendObs L y j)),
        ∏ j ∈ b.latentsInto L H ∪ H.map (Function.Embedding.subtype _),
          (b.cpt j (b.paVal j p.2)).weights (p.2 j) :=
    (Finset.sum_sigma _ _ (fun p : Σ _ : ({i : Fin n // i ∉ L} → α), Fin n → α =>
      ∏ j ∈ b.latentsInto L H ∪ H.map (Function.Embedding.subtype _),
        (b.cpt j (b.paVal j p.2)).weights (p.2 j))).symm
  have hBij : (∑ p ∈ (univ.filter (fun y : {i : Fin n // i ∉ L} → α => ∀ a ∉ H \ A, y a = v a)).sigma
        (fun y => univ.filter (fun z : Fin n → α => ∀ j ∉ b.latentsInto L H, z j = extendObs L y j)),
        ∏ j ∈ b.latentsInto L H ∪ H.map (Function.Embedding.subtype _),
          (b.cpt j (b.paVal j p.2)).weights (p.2 j)) =
      ∑ z with ∀ j ∉ b.latentsInto L H ∪ (H \ A).map (Function.Embedding.subtype _),
        z j = extendObs L v j,
        ∏ j ∈ b.latentsInto L H ∪ H.map (Function.Embedding.subtype _),
          (b.cpt j (b.paVal j z)).weights (z j) := by
    refine Finset.sum_nbij'
      (fun p : Σ _ : ({i : Fin n // i ∉ L} → α), Fin n → α => p.2)
      (fun z : Fin n → α => ⟨fun a : {i : Fin n // i ∉ L} => if a ∈ H \ A then z ↑a else v a, z⟩)
      ?_ ?_ ?_ ?_ ?_
    · intro p hp
      simp only [Finset.mem_sigma, Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
      obtain ⟨hp1, hp2⟩ := hp
      intro j hj
      simp only [Finset.mem_union] at hj
      have hjLH : j ∉ b.latentsInto L H := fun h => hj (Or.inl h)
      have hjHM : j ∉ (H \ A).map (Function.Embedding.subtype _) := fun h => hj (Or.inr h)
      have hz : p.2 j = extendObs L p.1 j := hp2 j hjLH
      rw [hz]
      by_cases hjL : j ∈ L
      · exact hExtLat p.1 v j hjL
      · have haHA : (⟨j, hjL⟩ : {i : Fin n // i ∉ L}) ∉ H \ A :=
          fun h => hjHM ((hMapMem j hjL).mpr h)
        have hy : p.1 ⟨j, hjL⟩ = v ⟨j, hjL⟩ := hp1 _ haHA
        rw [hExtObs p.1 j hjL, hExtObs v j hjL, hy]
    · intro z hz
      simp only [Finset.mem_sigma, Finset.mem_filter, Finset.mem_univ, true_and] at hz ⊢
      constructor
      · intro a haHA
        simp only [haHA, ↓reduceIte]
      · intro j hjLH
        by_cases hjL : j ∈ L
        · have hjHM : j ∉ (H \ A).map (Function.Embedding.subtype _) :=
            fun h => hHMAcap j h hjL
          have hjU : j ∉ b.latentsInto L H ∪ (H \ A).map (Function.Embedding.subtype _) := by
            simp only [Finset.mem_union]
            exact fun h => h.elim hjLH hjHM
          have hzz : z j = extendObs L v j := hz j hjU
          rw [hzz]
          exact (hExtLat _ v j hjL).symm
        · rw [hExtObs _ j hjL]
          by_cases haHA : (⟨j, hjL⟩ : {i : Fin n // i ∉ L}) ∈ H \ A
          · simp only [haHA, ↓reduceIte]
          · simp only [haHA, ↓reduceIte]
            have hjHM : j ∉ (H \ A).map (Function.Embedding.subtype _) :=
              fun h => haHA ((hMapMem j hjL).mp h)
            have hjU : j ∉ b.latentsInto L H ∪ (H \ A).map (Function.Embedding.subtype _) := by
              simp only [Finset.mem_union]
              exact fun h => h.elim hjLH hjHM
            have hzz : z j = extendObs L v j := hz j hjU
            rw [hzz, hExtObs v j hjL]
    · intro p hp
      simp only [Finset.mem_sigma, Finset.mem_filter, Finset.mem_univ, true_and] at hp
      obtain ⟨hp1, hp2⟩ := hp
      obtain ⟨y, z⟩ := p
      simp only at hp1 hp2 ⊢
      have hy : (fun a : {i : Fin n // i ∉ L} => if a ∈ H \ A then z ↑a else v a) = y := by
        funext a
        by_cases haHA : a ∈ H \ A
        · simp only [haHA, ↓reduceIte]
          have hjLH : (↑a : Fin n) ∉ b.latentsInto L H := fun h => a.2 (hLHsubL h)
          have hzz : z ↑a = extendObs L y ↑a := hp2 _ hjLH
          have hext : extendObs L y ↑a = y a := by
            unfold extendObs
            simp only [dite_eq_right a.2]
          rw [hzz, hext]
        · simp only [haHA, ↓reduceIte]
          exact (hp1 a haHA).symm
      simp only [hy]
    · intro z _
      rfl
    · intro p _
      rfl
  have hPsiMaps : ∀ z ∈ univ.filter
      (fun z : Fin n → α => ∀ j ∉ b.latentsInto L H ∪ (H \ A).map (Function.Embedding.subtype _),
        z j = extendObs L v j),
      (fun z j => if j ∈ B then extendObs L v j else z j) z ∈
        univ.filter (fun w : Fin n → α => ∀ j ∉ b.latentsInto L A, w j = extendObs L v j) := by
    intro z hz
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz ⊢
    intro j hjLA
    show (if j ∈ B then extendObs L v j else z j) = extendObs L v j
    by_cases hjB : j ∈ B
    · rw [ite_eq_left hjB]
    · rw [ite_eq_right hjB]
      have hjHM : j ∉ (H \ A).map (Function.Embedding.subtype _) := by
        intro hcon
        apply hjB
        rw [hBdef]
        simp only [Finset.mem_union]
        exact Or.inl hcon
      have hjLH : j ∉ b.latentsInto L H := by
        intro hcon
        apply hjB
        rw [hBdef]
        simp only [Finset.mem_union]
        exact Or.inr (Finset.mem_sdiff.mpr ⟨hcon, hjLA⟩)
      have hjU : j ∉ b.latentsInto L H ∪ (H \ A).map (Function.Embedding.subtype _) := by
        simp only [Finset.mem_union]
        exact fun h => h.elim hjLH hjHM
      exact hz j hjU
  have hFiberSet : ∀ w ∈ univ.filter
      (fun w : Fin n → α => ∀ j ∉ b.latentsInto L A, w j = extendObs L v j),
      (univ.filter (fun z : Fin n → α => ∀ j ∉ b.latentsInto L H ∪
        (H \ A).map (Function.Embedding.subtype _), z j = extendObs L v j)).filter
        (fun z => (fun z j => if j ∈ B then extendObs L v j else z j) z = w) =
      univ.filter (fun z : Fin n → α => ∀ j ∉ B, z j = w j) := by
    intro w hw
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw
    ext z
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨-, hψ⟩ j hjB
      have h : (if j ∈ B then extendObs L v j else z j) = w j := congrFun hψ j
      rw [ite_eq_right hjB] at h
      exact h
    · intro hwz
      constructor
      · intro j hjU
        simp only [Finset.mem_union] at hjU
        have hjLH : j ∉ b.latentsInto L H := fun h => hjU (Or.inl h)
        have hjHM : j ∉ (H \ A).map (Function.Embedding.subtype _) := fun h => hjU (Or.inr h)
        have hjLA : j ∉ b.latentsInto L A := fun h => hjLH (hAsubH h)
        have hwj : w j = extendObs L v j := hw j hjLA
        have hjB : j ∉ B := by
          rw [hBdef]
          simp only [Finset.mem_union, Finset.mem_sdiff]
          exact fun h => h.elim hjHM (fun hsd => hjLH hsd.1)
        rw [hwz j hjB, hwj]
      · funext j
        show (if j ∈ B then extendObs L v j else z j) = w j
        by_cases hjB : j ∈ B
        · rw [ite_eq_left hjB]
          have hjLA : j ∉ b.latentsInto L A := by
            intro hcon
            exact Finset.disjoint_left.mp hIdxDisj (Finset.mem_union_left _ hcon) hjB
          exact (hw j hjLA).symm
        · rw [ite_eq_right hjB]
          exact hwz j hjB
  have hInner : ∀ w ∈ univ.filter
      (fun w : Fin n → α => ∀ j ∉ b.latentsInto L A, w j = extendObs L v j),
      (∑ z ∈ (univ.filter (fun z : Fin n → α => ∀ j ∉ b.latentsInto L H ∪
        (H \ A).map (Function.Embedding.subtype _), z j = extendObs L v j)).filter
        (fun z => (fun z j => if j ∈ B then extendObs L v j else z j) z = w),
        ∏ j ∈ b.latentsInto L H ∪ H.map (Function.Embedding.subtype _),
          (b.cpt j (b.paVal j z)).weights (z j)) =
      ∏ j ∈ b.latentsInto L A ∪ A.map (Function.Embedding.subtype _),
        (b.cpt j (b.paVal j w)).weights (w j) := by
    intro w hw
    rw [hFiberSet w hw]
    calc (∑ z ∈ univ.filter (fun z : Fin n → α => ∀ j ∉ B, z j = w j),
            ∏ j ∈ b.latentsInto L H ∪ H.map (Function.Embedding.subtype _),
              (b.cpt j (b.paVal j z)).weights (z j))
        = ∑ z ∈ univ.filter (fun z : Fin n → α => ∀ j ∉ B, z j = w j),
            (∏ j ∈ b.latentsInto L A ∪ A.map (Function.Embedding.subtype _),
              (b.cpt j (b.paVal j z)).weights (z j)) *
            ∏ j ∈ B, (b.cpt j (b.paVal j z)).weights (z j) :=
          Finset.sum_congr rfl (fun z _ => hProdSplit z)
      _ = ∑ z ∈ univ.filter (fun z : Fin n → α => ∀ j ∉ B, z j = w j),
            (∏ j ∈ b.latentsInto L A ∪ A.map (Function.Embedding.subtype _),
              (b.cpt j (b.paVal j w)).weights (w j)) *
            ∏ j ∈ B, (b.cpt j (b.paVal j z)).weights (z j) := by
          refine Finset.sum_congr rfl (fun z hmem => ?_)
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hmem
          rw [hDepEq z w hmem]
      _ = (∏ j ∈ b.latentsInto L A ∪ A.map (Function.Embedding.subtype _),
              (b.cpt j (b.paVal j w)).weights (w j)) *
            ∑ z ∈ univ.filter (fun z : Fin n → α => ∀ j ∉ B, z j = w j),
              ∏ j ∈ B, (b.cpt j (b.paVal j z)).weights (z j) :=
          (Finset.mul_sum _ _ _).symm
      _ = ∏ j ∈ b.latentsInto L A ∪ A.map (Function.Embedding.subtype _),
            (b.cpt j (b.paVal j w)).weights (w j) := by
          rw [b.sum_prod_cpt_filter_eq_one B w, mul_one]
  have hZtoW : (∑ z with ∀ j ∉ b.latentsInto L H ∪ (H \ A).map (Function.Embedding.subtype _),
        z j = extendObs L v j,
        ∏ j ∈ b.latentsInto L H ∪ H.map (Function.Embedding.subtype _),
          (b.cpt j (b.paVal j z)).weights (z j)) =
      ∑ w with ∀ j ∉ b.latentsInto L A, w j = extendObs L v j,
        ∏ j ∈ b.latentsInto L A ∪ A.map (Function.Embedding.subtype _),
          (b.cpt j (b.paVal j w)).weights (w j) := by
    calc (∑ z ∈ univ.filter (fun z : Fin n → α => ∀ j ∉ b.latentsInto L H ∪
          (H \ A).map (Function.Embedding.subtype _), z j = extendObs L v j),
            ∏ j ∈ b.latentsInto L H ∪ H.map (Function.Embedding.subtype _),
              (b.cpt j (b.paVal j z)).weights (z j))
        = ∑ w ∈ univ.filter (fun w : Fin n → α => ∀ j ∉ b.latentsInto L A, w j = extendObs L v j),
            ∑ z ∈ (univ.filter (fun z : Fin n → α => ∀ j ∉ b.latentsInto L H ∪
              (H \ A).map (Function.Embedding.subtype _), z j = extendObs L v j)).filter
              (fun z => (fun z j => if j ∈ B then extendObs L v j else z j) z = w),
              ∏ j ∈ b.latentsInto L H ∪ H.map (Function.Embedding.subtype _),
                (b.cpt j (b.paVal j z)).weights (z j) :=
          (Finset.sum_fiberwise_of_maps_to hPsiMaps _).symm
      _ = ∑ w ∈ univ.filter (fun w : Fin n → α => ∀ j ∉ b.latentsInto L A, w j = extendObs L v j),
            ∏ j ∈ b.latentsInto L A ∪ A.map (Function.Embedding.subtype _),
              (b.cpt j (b.paVal j w)).weights (w j) :=
          Finset.sum_congr rfl (fun w hw => hInner w hw)
  calc marginal (b.qFactor L H) (↑(H \ A))ᶜ v
      = (∑ y with ∀ a ∉ H \ A, y a = v a,
          ∑ z with ∀ j ∉ b.latentsInto L H, z j = extendObs L y j,
            ∏ j ∈ b.latentsInto L H ∪ H.map (Function.Embedding.subtype _),
              (b.cpt j (b.paVal j z)).weights (z j)) := hDouble
    _ = (∑ p ∈ (univ.filter (fun y : {i : Fin n // i ∉ L} → α => ∀ a ∉ H \ A, y a = v a)).sigma
          (fun y => univ.filter (fun z : Fin n → α => ∀ j ∉ b.latentsInto L H, z j = extendObs L y j)),
          ∏ j ∈ b.latentsInto L H ∪ H.map (Function.Embedding.subtype _),
            (b.cpt j (b.paVal j p.2)).weights (p.2 j)) := hSigma
    _ = (∑ z with ∀ j ∉ b.latentsInto L H ∪ (H \ A).map (Function.Embedding.subtype _),
          z j = extendObs L v j,
          ∏ j ∈ b.latentsInto L H ∪ H.map (Function.Embedding.subtype _),
            (b.cpt j (b.paVal j z)).weights (z j)) := hBij
    _ = (∑ w with ∀ j ∉ b.latentsInto L A, w j = extendObs L v j,
          ∏ j ∈ b.latentsInto L A ∪ A.map (Function.Embedding.subtype _),
            (b.cpt j (b.paVal j w)).weights (w j)) := hZtoW
    _ = b.qFactor L A v := hT0A.symm

/-- Prefix induction for L4: the claim with `H` replaced by its `σ`-prefix below `m`. -/
theorem qFactor_mul_prod_qFactor_pred_aux {H : Finset {i : Fin n // i ∉ L}}
    (σ : {i : Fin n // i ∉ L} ≃ Fin (Fintype.card {i : Fin n // i ∉ L}))
    (v : {i : Fin n // i ∉ L} → α) (m : ℕ) (T : Finset {i : Fin n // i ∉ L})
    (hTHm : T ⊆ H.filter fun u => (σ u).val < m)
    (hsep : ∀ u ∈ T, ∀ w ∈ (H.filter fun u => (σ u).val < m) \ T,
      ¬ (b.latentProjection L).bidir.Adj u w) :
    b.qFactor L T v * ∏ i ∈ T, b.qFactor L (H.filter fun u => σ u < σ i) v =
      ∏ i ∈ T, b.qFactor L ({i} ∪ H.filter fun u => σ u < σ i) v := by
  classical
  induction m generalizing T with
  | zero =>
    have hT : T = ∅ := by
      ext u
      simp only [Finset.notMem_empty]
      constructor
      · intro huT
        have h2 := (Finset.mem_filter.mp (hTHm huT)).2
        exact absurd h2 (Nat.not_lt_zero _)
      · intro h
        exact h.elim
    subst hT
    rw [b.qFactor_empty L v, Finset.prod_empty, Finset.prod_empty, mul_one]
  | succ m IH =>
    by_cases hex : ∃ i ∈ T, (σ i).val = m
    · obtain ⟨i, hiT, hival⟩ := hex
      have hiH : i ∈ H := (Finset.mem_filter.mp (hTHm hiT)).1
      have huniq : ∀ u : {i : Fin n // i ∉ L}, (σ u).val = m → u = i := by
        intro u hu
        apply σ.injective
        apply Fin.ext
        omega
      have hi_not_Hm : i ∉ H.filter fun u => (σ u).val < m := by
        intro h
        have h2 := (Finset.mem_filter.mp h).2
        omega
      have hHm1 : H.filter (fun u => (σ u).val < m + 1)
          = insert i (H.filter fun u => (σ u).val < m) := by
        ext u
        simp only [Finset.mem_filter, Finset.mem_insert]
        constructor
        · rintro ⟨huH, hlt⟩
          by_cases heq : u = i
          · exact Or.inl heq
          · right
            refine ⟨huH, ?_⟩
            by_cases hvm : (σ u).val = m
            · exact absurd (huniq u hvm) heq
            · omega
        · rintro (rfl | ⟨huH, hlt⟩)
          · exact ⟨hiH, by omega⟩
          · exact ⟨huH, by omega⟩
      have hpred_i : H.filter (fun u => σ u < σ i)
          = H.filter fun u => (σ u).val < m := by
        ext u
        simp only [Finset.mem_filter]
        constructor
        · rintro ⟨huH, hlt⟩
          refine ⟨huH, ?_⟩
          have hlt' : (σ u).val < (σ i).val := Fin.lt_def.mp hlt
          omega
        · rintro ⟨huH, hlt⟩
          refine ⟨huH, ?_⟩
          have hlt' : (σ u).val < (σ i).val := by omega
          exact Fin.lt_def.mpr hlt'
      have hunion_i : ({i} ∪ H.filter (fun u => σ u < σ i))
          = H.filter fun u => (σ u).val < m + 1 := by
        rw [hpred_i, hHm1, Finset.insert_eq]
      have hR : H.filter (fun u => (σ u).val < m + 1) \ T
          = H.filter (fun u => (σ u).val < m) \ (T \ {i}) := by
        rw [hHm1]
        ext u
        simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]
        constructor
        · rintro ⟨rfl | huHm, huT⟩
          · exact absurd hiT huT
          · exact ⟨huHm, fun h => huT h.1⟩
        · rintro ⟨huHm, h⟩
          refine ⟨Or.inr huHm, ?_⟩
          intro huT
          by_cases heq : u = i
          · subst heq
            exact absurd huHm hi_not_Hm
          · exact h ⟨huT, heq⟩
      have hsub' : T \ {i} ⊆ H.filter fun u => (σ u).val < m := by
        intro u hu
        simp only [Finset.mem_sdiff, Finset.mem_singleton] at hu
        obtain ⟨huT, hne⟩ := hu
        have hum := hTHm huT
        simp only [Finset.mem_filter] at hum ⊢
        refine ⟨hum.1, ?_⟩
        have hne' : (σ u).val ≠ m := fun hvm => hne (huniq u hvm)
        omega
      have hsep' : ∀ u ∈ T \ {i},
          ∀ w ∈ H.filter (fun u => (σ u).val < m) \ (T \ {i}),
          ¬ (b.latentProjection L).bidir.Adj u w := by
        intro u huT' w hw
        rw [← hR] at hw
        exact hsep u (Finset.mem_sdiff.mp huT').1 w hw
      have hG0top := b.qFactor_eq_mul_of_not_adj L hTHm hsep v
      have hG0bot := b.qFactor_eq_mul_of_not_adj L hsub' hsep' v
      have hIH := IH (T \ {i}) hsub' hsep'
      have hsplitL : ∏ j ∈ T, b.qFactor L (H.filter fun u => σ u < σ j) v
          = b.qFactor L (H.filter fun u => σ u < σ i) v
            * ∏ j ∈ T \ {i}, b.qFactor L (H.filter fun u => σ u < σ j) v :=
        Finset.prod_eq_mul_prod_sdiff_singleton i _ (fun h => absurd hiT h)
      have hsplitR : ∏ j ∈ T, b.qFactor L ({j} ∪ H.filter fun u => σ u < σ j) v
          = b.qFactor L ({i} ∪ H.filter fun u => σ u < σ i) v
            * ∏ j ∈ T \ {i}, b.qFactor L ({j} ∪ H.filter fun u => σ u < σ j) v :=
        Finset.prod_eq_mul_prod_sdiff_singleton i _ (fun h => absurd hiT h)
      rw [hsplitL, hsplitR, hunion_i, hpred_i, hG0bot, hG0top, hR, ← hIH]
      ring
    · have hsub : T ⊆ H.filter fun u => (σ u).val < m := by
        intro u huT
        have hu := hTHm huT
        simp only [Finset.mem_filter] at hu ⊢
        refine ⟨hu.1, ?_⟩
        have hne : (σ u).val ≠ m := fun h => hex ⟨u, huT, h⟩
        omega
      have hsep0 : ∀ u ∈ T, ∀ w ∈ (H.filter fun u => (σ u).val < m) \ T,
          ¬ (b.latentProjection L).bidir.Adj u w := by
        intro u huT w hw
        have hw' : w ∈ (H.filter fun u => (σ u).val < m + 1) \ T := by
          simp only [Finset.mem_sdiff, Finset.mem_filter] at hw ⊢
          exact ⟨⟨hw.1.1, by omega⟩, hw.2⟩
        exact hsep u huT w hw'
      exact IH T hsub hsep0

/-- L4, TR Lemma 4(ii) (71) without division; any order, no topological hypothesis. -/
theorem qFactor_mul_prod_qFactor_pred {H T : Finset {i : Fin n // i ∉ L}} (hTH : T ⊆ H)
    (hsep : ∀ u ∈ T, ∀ w ∈ H \ T, ¬ (b.latentProjection L).bidir.Adj u w)
    (σ : {i : Fin n // i ∉ L} ≃ Fin (Fintype.card {i : Fin n // i ∉ L}))
    (v : {i : Fin n // i ∉ L} → α) :
    b.qFactor L T v * ∏ i ∈ T, b.qFactor L (H.filter fun u => σ u < σ i) v =
      ∏ i ∈ T, b.qFactor L ({i} ∪ H.filter fun u => σ u < σ i) v := by
  classical
  have hcard : H.filter (fun u => (σ u).val < Fintype.card {i : Fin n // i ∉ L}) = H := by
    apply Finset.filter_true_of_mem
    intro u _
    exact Fin.is_lt _
  have hsub : T ⊆ H.filter fun u => (σ u).val < Fintype.card {i : Fin n // i ∉ L} := by
    rw [hcard]
    exact hTH
  have hsep' : ∀ u ∈ T,
      ∀ w ∈ (H.filter fun u => (σ u).val < Fintype.card {i : Fin n // i ∉ L}) \ T,
      ¬ (b.latentProjection L).bidir.Adj u w := by
    rw [hcard]
    exact hsep
  exact b.qFactor_mul_prod_qFactor_pred_aux L σ v _ T hsub hsep'

/-- The factorization of the observed law over c-components (TP02 (27)-(28), TR (35),
(56)), for every `v` with no positivity hypothesis. No semi-Markovian
hypothesis is needed, so this subsumes TP02's semi-Markovian statement. -/
theorem observedLaw_eq_prod_qFactor (v : {i : Fin n // i ∉ L} → α) :
    b.observedLaw L v = ∏ S ∈ (b.latentProjection L).cComponents, b.qFactor L S v := by
  classical
  have hmem : ∀ S : Finset {i : Fin n // i ∉ L},
      S ∈ (b.latentProjection L).cComponents →
      ∃ v, Finset.univ.filter (· ∈ (b.latentProjection L).cComponent v) = S :=
    fun S hS => (ADMG.mem_cComponents_iff _).mp hS
  have hdisj : ((b.latentProjection L).cComponents :
      Set (Finset {i : Fin n // i ∉ L})).PairwiseDisjoint id := by
    intro S hS T hT hne
    obtain ⟨v, rfl⟩ := hmem S (Finset.mem_coe.mp hS)
    obtain ⟨w, rfl⟩ := hmem T (Finset.mem_coe.mp hT)
    show Disjoint _ _
    rw [Finset.disjoint_left]
    intro x hxv hxw
    exact hne (ADMG.filter_cComponent_eq_of_shared _ hxv hxw)
  have hcov : ((b.latentProjection L).cComponents).biUnion id = Finset.univ := by
    ext x
    rw [Finset.mem_biUnion]
    constructor
    · rintro ⟨S, -, -⟩
      exact Finset.mem_univ x
    · intro _
      refine ⟨Finset.univ.filter (· ∈ (b.latentProjection L).cComponent x), ?_, ?_⟩
      · exact (ADMG.mem_cComponents_iff _).mpr ⟨x, rfl⟩
      · show x ∈ Finset.univ.filter (· ∈ (b.latentProjection L).cComponent x)
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, ADMG.mem_cComponent_iff]
        exact SimpleGraph.Reachable.refl x
  have hsep : ∀ T ∈ (b.latentProjection L).cComponents, ∀ T' ∈ (b.latentProjection L).cComponents,
      T ≠ T' → ∀ u ∈ T, ∀ w ∈ T', ¬ (b.latentProjection L).bidir.Adj u w := by
    intro T hT T' hT' hne u huT w hwT' hadj
    obtain ⟨v, rfl⟩ := hmem T hT
    obtain ⟨w', rfl⟩ := hmem T' hT'
    apply hne
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      ADMG.mem_cComponent_iff] at huT hwT'
    exact ADMG.filter_cComponent_eq_of_reachable _ (huT.trans (hadj.reachable.trans hwT'.symm))
  have hG0 := b.qFactor_eq_prod_of_not_adj L (b.latentProjection L).cComponents
    hdisj hcov hsep v
  have huniv := congrFun (b.qFactor_univ L) v
  exact huniv.symm.trans hG0

/-- No bidirected edge runs from a c-component to its complement. -/
theorem cComponent_no_adj_compl {S : Finset {i : Fin n // i ∉ L}}
    (hS : S ∈ (b.latentProjection L).cComponents) :
    ∀ u ∈ S, ∀ w ∈ univ \ S, ¬ (b.latentProjection L).bidir.Adj u w := by
  classical
  obtain ⟨v, rfl⟩ := (ADMG.mem_cComponents_iff _).mp hS
  intro u hu w hw hadj
  simp only [Finset.mem_sdiff, Finset.mem_univ, true_and] at hw
  have hwmem : w ∈ Finset.univ.filter (· ∈ (b.latentProjection L).cComponent w) := by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, ADMG.mem_cComponent_iff]
    exact SimpleGraph.Reachable.refl w
  simp only [Finset.mem_filter, Finset.mem_univ, true_and,
    ADMG.mem_cComponent_iff] at hu
  have hrw : (b.latentProjection L).bidir.Reachable w w := by
    have h := hwmem
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      ADMG.mem_cComponent_iff] at h
    exact h
  have heq := ADMG.filter_cComponent_eq_of_reachable (b.latentProjection L)
    (hu.trans (hadj.reachable.trans hrw.symm))
  rw [heq] at hw
  exact hw hwmem

/-- The observed marginal on predecessors is the `qFactor` on predecessors. -/
theorem marginal_pred_eq_qFactor
    (σ : {i : Fin n // i ∉ L} ≃ Fin (Fintype.card {i : Fin n // i ∉ L}))
    (hσ : ∀ ⦃u w⦄, (b.latentProjection L).dir u w → σ u < σ w)
    (i : {i : Fin n // i ∉ L}) (v : {i : Fin n // i ∉ L} → α) :
    marginal (b.observedLaw L) ↑(univ.filter fun u => σ u < σ i) v =
      b.qFactor L (univ.filter fun u => σ u < σ i) v := by
  classical
  have hset : ((↑(univ \ (univ.filter fun u => σ u < σ i)))ᶜ :
      Set {i : Fin n // i ∉ L}) = ↑(univ.filter fun u => σ u < σ i) := by
    ext x
    simp only [Set.mem_compl_iff, Finset.mem_coe, Finset.mem_sdiff, Finset.mem_univ,
      true_and, not_not]
  have hanc : ∀ ⦃u w⦄, (b.latentProjection L).dir u w → u ∈ univ →
      w ∈ univ.filter (fun u => σ u < σ i) →
      u ∈ univ.filter fun u => σ u < σ i := by
    intro u w hdir _ hw
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw ⊢
    exact lt_trans (hσ hdir) hw
  have h := b.marginal_qFactor_of_ancestral L (Finset.subset_univ _) hanc v
  rw [hset, b.qFactor_univ L] at h
  exact h

/-- The observed marginal on a vertex plus predecessors is the `qFactor` there. -/
theorem marginal_insert_pred_eq_qFactor
    (σ : {i : Fin n // i ∉ L} ≃ Fin (Fintype.card {i : Fin n // i ∉ L}))
    (hσ : ∀ ⦃u w⦄, (b.latentProjection L).dir u w → σ u < σ w)
    (i : {i : Fin n // i ∉ L}) (v : {i : Fin n // i ∉ L} → α) :
    marginal (b.observedLaw L) ↑({i} ∪ univ.filter fun u => σ u < σ i) v =
      b.qFactor L ({i} ∪ univ.filter fun u => σ u < σ i) v := by
  classical
  have hset : ((↑(univ \ ({i} ∪ univ.filter fun u => σ u < σ i)))ᶜ :
      Set {i : Fin n // i ∉ L}) = ↑({i} ∪ univ.filter fun u => σ u < σ i) := by
    ext x
    simp only [Set.mem_compl_iff, Finset.mem_coe, Finset.mem_sdiff, Finset.mem_univ,
      true_and, not_not]
  have hanc : ∀ ⦃u w⦄, (b.latentProjection L).dir u w → u ∈ univ →
      w ∈ {i} ∪ univ.filter (fun u => σ u < σ i) →
      u ∈ {i} ∪ univ.filter fun u => σ u < σ i := by
    intro u w hdir _ hw
    simp only [Finset.mem_union, Finset.mem_singleton, Finset.mem_filter,
      Finset.mem_univ, true_and] at hw ⊢
    rcases hw with rfl | hlt
    · exact Or.inr (hσ hdir)
    · exact Or.inr (lt_trans (hσ hdir) hlt)
  have h := b.marginal_qFactor_of_ancestral L (Finset.subset_univ _) hanc v
  rw [hset, b.qFactor_univ L] at h
  exact h

/-- T2, TP02 Lemma 1(i) without division; `σ` any topological order of the projection.
No semi-Markovian hypothesis is needed, so this subsumes the source's
semi-Markovian statement. -/
theorem qFactor_mul_prod_marginal_pred
    (σ : {i : Fin n // i ∉ L} ≃ Fin (Fintype.card {i : Fin n // i ∉ L}))
    (hσ : ∀ ⦃u w⦄, (b.latentProjection L).dir u w → σ u < σ w)
    {S : Finset {i : Fin n // i ∉ L}} (hS : S ∈ (b.latentProjection L).cComponents)
    (v : {i : Fin n // i ∉ L} → α) :
    b.qFactor L S v * ∏ i ∈ S, marginal (b.observedLaw L) ↑(univ.filter fun u => σ u < σ i) v =
      ∏ i ∈ S, marginal (b.observedLaw L) ↑({i} ∪ univ.filter fun u => σ u < σ i) v := by
  classical
  have hsep := b.cComponent_no_adj_compl L hS
  have hL4 := b.qFactor_mul_prod_qFactor_pred L (H := univ) (T := S)
    (Finset.subset_univ S) hsep σ v
  have e1 : ∏ i ∈ S, marginal (b.observedLaw L) ↑(univ.filter fun u => σ u < σ i) v =
      ∏ i ∈ S, b.qFactor L (univ.filter fun u => σ u < σ i) v :=
    Finset.prod_congr rfl fun i _ => b.marginal_pred_eq_qFactor L σ hσ i v
  have e2 : ∏ i ∈ S, marginal (b.observedLaw L) ↑({i} ∪ univ.filter fun u => σ u < σ i) v =
      ∏ i ∈ S, b.qFactor L ({i} ∪ univ.filter fun u => σ u < σ i) v :=
    Finset.prod_congr rfl fun i _ => b.marginal_insert_pred_eq_qFactor L σ hσ i v
  rw [e1, e2]
  exact hL4

/-- The prefix identity in ratio form, TP02 eq. (29). No semi-Markovian
hypothesis is needed, so this subsumes the source's semi-Markovian statement. -/
theorem qFactor_eq_prod_cond
    (σ : {i : Fin n // i ∉ L} ≃ Fin (Fintype.card {i : Fin n // i ∉ L}))
    (hσ : ∀ ⦃u w⦄, (b.latentProjection L).dir u w → σ u < σ w)
    {S : Finset {i : Fin n // i ∉ L}} (hS : S ∈ (b.latentProjection L).cComponents)
    {v : {i : Fin n // i ∉ L} → α} (hv : 0 < b.observedLaw L v) :
    b.qFactor L S v = ∏ i ∈ S,
      marginal (b.observedLaw L) ↑({i} ∪ univ.filter fun u => σ u < σ i) v /
        marginal (b.observedLaw L) ↑(univ.filter fun u => σ u < σ i) v := by
  classical
  have hT2 := b.qFactor_mul_prod_marginal_pred L σ hσ hS v
  have hpos : ∀ i ∈ S,
      0 < marginal (b.observedLaw L) ↑(univ.filter fun u => σ u < σ i) v := by
    intro i _
    rw [b.marginal_pred_eq_qFactor L σ hσ i v]
    exact b.qFactor_pos L hv _
  have hden : (∏ i ∈ S, marginal (b.observedLaw L) ↑(univ.filter fun u => σ u < σ i) v) ≠ 0 :=
    ne_of_gt (Finset.prod_pos hpos)
  rw [Finset.prod_div_distrib, eq_div_iff hden]
  exact hT2

end Cslib.MachineLearning.GraphicalModels.BayesNet

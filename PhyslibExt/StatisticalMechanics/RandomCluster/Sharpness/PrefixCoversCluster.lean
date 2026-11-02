/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.StatisticalMechanics.RandomCluster.Sharpness.ReachDomination

/-!
# Prefixes of the order covering the incident cluster

When does the part of the order before an edge contain every edge of the cluster that meets the
frontier, and the existence of cluster orders for which it does.

## i. Overview

`PrefixCoversCluster σ endU endV B e` is reduced to the all-open configuration
(`prefixCoversCluster_iff_top`). Ordering the edges incident to the top cluster first
(`clusterOrder_exists`) makes it hold for frontier edges, and it gives `frontierConn_clusterOrder`.
It cannot hold for every edge once two edges are incident to the top cluster:
`not_forall_prefixCoversCluster` is a Lean-checked refutation. Part of the revealment bounds for the
OSSS covariance lower bound: the revealment of an edge is bounded by the probability that it is
connected to the frontier of the exploration.

## ii. Key results

- `prefixCoversCluster_frontier`: frontier edges are covered under a cluster order.
- `frontierConn_clusterOrder`: `FrontierConn` under a cluster order.
- `not_forall_prefixCoversCluster`: the covering property fails for some edge.

## iii. Table of contents

- A. Monotonicity of connection
- B. The all-open configuration
- C. Cluster orders

## iv. References

* H. Duminil-Copin, A. Raoufi, V. Tassion, *Sharp phase transition for the random-cluster and Potts
  models via decision trees*, Ann. of Math. 189 (2019).
-/

@[expose] public section

open scoped BigOperators
open MeasureTheory


namespace StatMech

namespace OSSS

namespace PrefixCoversClose

open OSSS.Coding
open StatMech.OSSS
open StatMech.OSSS.RevealmentConstruction
open StatMech.OSSS.ReachBoxCrossing
open StatMech.OSSS.ReachDomination
open StatMech.Lattice

variable {E : Type*} [Fintype E] [DecidableEq E]
variable {V : Type*} [DecidableEq V]

/-! ## A. Monotonicity of connection -/

omit [Fintype E] [DecidableEq E] [DecidableEq V] in
lemma reachOpen_mono {endU endV : E → V} {X w : ConfigSpace E}
    (hle : ∀ e, X e = true → w e = true) {x y : V}
    (h : ReachOpen endU endV X x y) : ReachOpen endU endV w x y := by
  induction h with
  | refl x => exact ReachOpen.refl x
  | step e hopen hpair _ ih => exact ReachOpen.step e (hle e hopen) hpair ih

omit [Fintype E] [DecidableEq E] [DecidableEq V] in
lemma connOpenSet_mono {endU endV : E → V} {X w : ConfigSpace E} {B : Set V}
    (hle : ∀ e, X e = true → w e = true) {x : V}
    (h : ConnOpenSet endU endV X x B) : ConnOpenSet endU endV w x B := by
  obtain ⟨b, hbB, hreach⟩ := h
  exact ⟨b, hbB, reachOpen_mono hle hreach⟩

omit [Fintype E] [DecidableEq E] [DecidableEq V] in
lemma incidentCluster_mono {endU endV : E → V} {X w : ConfigSpace E} {B : Set V}
    (hle : ∀ e, X e = true → w e = true) {e' : E}
    (h : IncidentCluster endU endV X B e') : IncidentCluster endU endV w B e' := by
  rcases h with hU | hV
  · exact Or.inl (connOpenSet_mono hle hU)
  · exact Or.inr (connOpenSet_mono hle hV)

/-! ## B. The all-open configuration -/

/-- The configuration with every edge open. -/
def topCfg (E : Type*) : ConfigSpace E := fun _ => true

omit [Fintype E] [DecidableEq E] [DecidableEq V] in
lemma le_topCfg {endU endV : E → V} {X : ConfigSpace E} {B : Set V} {e' : E}
    (h : IncidentCluster endU endV X B e') : IncidentCluster endU endV (topCfg E) B e' :=
  incidentCluster_mono (fun _ _ => rfl) h

/-- The edge `e'` is incident to the cluster of `B` in the all-open configuration. -/
def TopIncident (endU endV : E → V) (B : Set V) (e' : E) : Prop :=
  IncidentCluster endU endV (topCfg E) B e'

omit [DecidableEq V] [Fintype E] in
lemma prefixCoversCluster_iff_top {n : ℕ} (σ : Fin n ≃ E) (endU endV : E → V)
    (B : Set V) (e : E) :
    PrefixCoversCluster σ endU endV B e ↔
      ∀ e' : E, e' ≠ e → TopIncident endU endV B e' →
        e' ∈ prefixSet (σ : Fin n → E) (σ.symm e : ℕ) := by
  constructor
  · intro hcover e' he' htop
    exact hcover (topCfg E) e' he' htop
  · intro htopcov X e' he' hincid
    exact htopcov e' he' (le_topCfg hincid)

omit [DecidableEq V] [Fintype E] in
lemma prefixCoversCluster_of_topIncident_subset {n : ℕ} (σ : Fin n ≃ E)
    (endU endV : E → V) (B : Set V) (e : E)
    (hsub : ∀ e' : E, e' ≠ e → TopIncident endU endV B e' →
        e' ∈ prefixSet (σ : Fin n → E) (σ.symm e : ℕ)) :
    PrefixCoversCluster σ endU endV B e :=
  (prefixCoversCluster_iff_top σ endU endV B e).mpr hsub

omit [DecidableEq V] [Fintype E] in
lemma prefixCoversCluster_of_pos_lt {n : ℕ} (σ : Fin n ≃ E) (endU endV : E → V)
    (B : Set V) (e : E)
    (hpos : ∀ e' : E, e' ≠ e → TopIncident endU endV B e' →
        (σ.symm e' : ℕ) < (σ.symm e : ℕ)) :
    PrefixCoversCluster σ endU endV B e := by
  refine prefixCoversCluster_of_topIncident_subset σ endU endV B e (fun e' he' htop => ?_)
  rw [mem_prefixSet_iff]
  exact ⟨σ.symm e', hpos e' he' htop, by simp⟩

/-! ## C. Cluster orders -/

omit [DecidableEq E] in
lemma clusterOrder_exists (p : E → Prop) [DecidablePred p]
    (n : ℕ) (hn : Fintype.card E = n) :
    ∃ σ : Fin n ≃ E,
      ∀ e' : E, (p e' ↔ (σ.symm e' : ℕ) < (Finset.univ.filter p).card) := by
  classical
  set m := (Finset.univ.filter p).card with hm
  set mc := (Finset.univ.filter (fun a => ¬ p a)).card with hmc
  have hcardp : Fintype.card {a // p a} = m := by rw [Fintype.card_subtype]
  have hcardc : Fintype.card {a // ¬ p a} = mc := by rw [Fintype.card_subtype]
  set epm : {a // p a} ≃ Fin m := Fintype.equivFinOfCardEq hcardp with hepm
  set epc : {a // ¬ p a} ≃ Fin mc := Fintype.equivFinOfCardEq hcardc with hepc
  have hsum : m + mc = n := by
    rw [hm, hmc, Finset.card_filter_add_card_filter_not, Finset.card_univ, hn]
  set σ0 : E ≃ Fin n :=
    (Equiv.sumCompl p).symm.trans
      ((epm.sumCongr epc).trans (finSumFinEquiv.trans (finCongr hsum))) with hσ0
  refine ⟨σ0.symm, ?_⟩
  intro e'
  change p e' ↔ ((σ0 e' : Fin n) : ℕ) < m
  by_cases hp' : p e'
  · have he : (Equiv.sumCompl p).symm e' = Sum.inl ⟨e', hp'⟩ :=
      Equiv.sumCompl_symm_apply_of_pos hp'
    simp only [hp', true_iff, hσ0, Equiv.trans_apply, he, Equiv.sumCongr_apply, Sum.map_inl,
      finSumFinEquiv_apply_left, finCongr_apply, Fin.val_cast, Fin.val_castAdd]
    exact (epm ⟨e', hp'⟩).2
  · have he : (Equiv.sumCompl p).symm e' = Sum.inr ⟨e', hp'⟩ :=
      Equiv.sumCompl_symm_apply_of_neg hp'
    simp only [hp', false_iff, not_lt, hσ0, Equiv.trans_apply, he, Equiv.sumCongr_apply,
      Sum.map_inr, finSumFinEquiv_apply_right, finCongr_apply, Fin.val_cast, Fin.val_natAdd]
    exact Nat.le_add_right m _

open Classical in
omit [DecidableEq V] in
lemma prefixCoversCluster_clusterOrder {n : ℕ} (σ : Fin n ≃ E)
    (endU endV : E → V) (B : Set V)
    (hσ : ∀ e' : E, (TopIncident endU endV B e' ↔
        (σ.symm e' : ℕ) < (Finset.univ.filter (TopIncident endU endV B)).card))
    (e : E)
    (he : (Finset.univ.filter (TopIncident endU endV B)).card - 1 ≤ (σ.symm e : ℕ)) :
    PrefixCoversCluster σ endU endV B e := by
  refine prefixCoversCluster_of_pos_lt σ endU endV B e (fun e' hne htop => ?_)
  have hlt : (σ.symm e' : ℕ) < (Finset.univ.filter (TopIncident endU endV B)).card :=
    (hσ e').mp htop
  have hne' : (σ.symm e' : ℕ) ≠ (σ.symm e : ℕ) := by
    intro h; exact hne (σ.symm.injective (Fin.ext h))
  omega

open Classical in
omit [DecidableEq V] in
lemma prefixCoversCluster_frontier (endU endV : E → V) (B : Set V) (n : ℕ)
    (hn : Fintype.card E = n)
    (hne : (Finset.univ.filter (TopIncident endU endV B)).Nonempty) :
    ∃ (σ : Fin n ≃ E) (e : E), TopIncident endU endV B e ∧
        PrefixCoversCluster σ endU endV B e := by
  classical
  obtain ⟨σ, hσ⟩ := clusterOrder_exists (TopIncident endU endV B) n hn
  have hm1 : 1 ≤ (Finset.univ.filter (TopIncident endU endV B)).card :=
    Finset.Nonempty.card_pos hne
  have hmn : (Finset.univ.filter (TopIncident endU endV B)).card ≤ n := by
    rw [← hn, ← Finset.card_univ]; exact Finset.card_filter_le _ _
  set e : E := σ ⟨(Finset.univ.filter (TopIncident endU endV B)).card - 1, by omega⟩ with hedef
  have hsymm : (σ.symm e : ℕ) = (Finset.univ.filter (TopIncident endU endV B)).card - 1 := by
    rw [hedef, Equiv.symm_apply_apply]
  have htop : TopIncident endU endV B e := by
    rw [hσ e, hsymm]; omega
  exact ⟨σ, e, htop, prefixCoversCluster_clusterOrder σ endU endV B hσ e (by rw [hsymm])⟩

open Classical in
omit [DecidableEq V] in
lemma frontierConn_clusterOrder (endU endV : E → V) (B C : Set V) (n : ℕ)
    (hn : Fintype.card E = n)
    (hne : (Finset.univ.filter (TopIncident endU endV B)).Nonempty) :
    ∃ (σ : Fin n ≃ E) (e : E), TopIncident endU endV B e ∧
        FrontierConn σ (indicatorConn endU endV B C) endU endV B e := by
  obtain ⟨σ, e, htop, hpcc⟩ := prefixCoversCluster_frontier endU endV B n hn hne
  exact ⟨σ, e, htop, frontierConn_of_clusterMeasurable σ endU endV B e
    (clusterMeasurable_indicatorConn endU endV B C) hpcc⟩

open Classical in
omit [DecidableEq V] in
/-- The covering property fails for some edge. -/
theorem not_forall_prefixCoversCluster {n : ℕ} (σ : Fin n ≃ E) (endU endV : E → V)
    (B : Set V) (h2 : 2 ≤ (Finset.univ.filter (TopIncident endU endV B)).card) :
    ¬ (∀ e : E, PrefixCoversCluster σ endU endV B e) := by
  classical
  intro hall
  set S : Finset E := Finset.univ.filter (TopIncident endU endV B) with hS
  have hSne : S.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨e0, he0S, he0min⟩ := S.exists_min_image (fun e => (σ.symm e : ℕ)) hSne
  have hpcc := (prefixCoversCluster_iff_top σ endU endV B e0).mp (hall e0)
  have hex : ∃ e1 ∈ S, e1 ≠ e0 := by
    by_contra hcon
    have hcon' : ∀ x ∈ S, x = e0 := by
      intro x hx; by_contra hxne; exact hcon ⟨x, hx, hxne⟩
    have hsub : S ⊆ {e0} := fun x hx => Finset.mem_singleton.mpr (hcon' x hx)
    have := Finset.card_le_card hsub
    simp only [Finset.card_singleton] at this
    omega
  obtain ⟨e1, he1S, hne⟩ := hex
  have hin : e1 ∈ prefixSet (σ : Fin n → E) (σ.symm e0 : ℕ) :=
    hpcc e1 hne (Finset.mem_filter.mp he1S).2
  rw [mem_prefixSet_iff] at hin
  obtain ⟨s, hs, hseq⟩ := hin
  have hlt : (σ.symm e1 : ℕ) < (σ.symm e0 : ℕ) := by
    have hse : σ.symm e1 = s := by rw [← hseq, Equiv.symm_apply_apply]
    rw [hse]; exact hs
  exact absurd hlt (not_lt.mpr (he0min e1 he1S))

omit [Fintype E] in
lemma incidentCluster_of_queried_crossTree (endU endV : E → V) (o : V) (B C : Set V)
    (l : List E) (disc₀ : Finset V) (hdisc₀ : ∀ x ∈ disc₀, x ∈ B) (ω : ConfigSpace E) (i : E)
    (hi : i ∈ (crossTree endU endV o C l disc₀).queried ω) :
    IncidentCluster endU endV ω B i :=
  queried_crossTree_imp endU endV o B C l disc₀ hdisc₀ ω i hi

end PrefixCoversClose

end OSSS

end StatMech

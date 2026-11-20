/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/













































import Mathlib
import Code.Sharpness.Switching
import Code.Sharpness.RandomCurrent
import Code.Sharpness.CurrentRep
import Code.Sharpness.TwoReplica

open Finset BigOperators
open scoped symmDiff Classical

set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

namespace StatMech
namespace Sharpness
namespace FluxEdgeCopy



variable {E : Type*} [Fintype E] [DecidableEq E] {β : E → Type*}
  [∀ e, Fintype (β e)] [∀ e, DecidableEq (β e)]





noncomputable def sigmaFinsetEquivPi : Finset (Σ e : E, β e) ≃ Π e : E, Finset (β e) where
  toFun S := fun e => (univ : Finset (β e)).filter (fun b => (⟨e, b⟩ : Σ e, β e) ∈ S)
  invFun f := univ.filter (fun i : Σ e, β e => i.2 ∈ f i.1)
  left_inv := by intro S; ext i; obtain ⟨e, b⟩ := i; simp
  right_inv := by intro f; ext e b; simp

@[simp] theorem sigmaFinsetEquivPi_apply_card (S : Finset (Σ e : E, β e)) (e : E) :
    #(sigmaFinsetEquivPi S e) = #(S.filter (fun i : Σ e, β e => i.1 = e)) := by
  
  rw [show sigmaFinsetEquivPi S e
        = (univ : Finset (β e)).filter (fun b => (⟨e, b⟩ : Σ e, β e) ∈ S) from rfl]
  
  apply Finset.card_bij (fun b _ => (⟨e, b⟩ : Σ e, β e))
  · intro b hb
    simp only [mem_filter, mem_univ, true_and] at hb
    simp only [mem_filter, hb, true_and]
  · intro b₁ _ b₂ _ h
    simpa using h
  · intro i hi
    simp only [mem_filter] at hi
    obtain ⟨hS, he⟩ := hi
    subst he
    refine ⟨i.2, ?_, ?_⟩
    · simp only [mem_filter, mem_univ, true_and]; exact hS
    · rfl






theorem pi_card_profile_count (k : E → ℕ) :
    #(univ.filter (fun f : Π e : E, Finset (β e) => (fun e => #(f e)) = k))
      = ∏ e : E, (Fintype.card (β e)).choose (k e) := by
  have hset : (univ.filter (fun f : Π e : E, Finset (β e) => (fun e => #(f e)) = k))
      = Fintype.piFinset (fun e => (univ : Finset (β e)).powersetCard (k e)) := by
    ext f
    simp only [mem_filter, mem_univ, true_and, Fintype.mem_piFinset, mem_powersetCard,
      Finset.subset_univ, true_and]
    constructor
    · intro h e; exact congrFun h e
    · intro h; funext e; exact h e
  rw [hset, Fintype.card_piFinset]
  exact Finset.prod_congr rfl (fun e _ => by rw [card_powersetCard, card_univ])





theorem pi_reindex_profile {M : Type*} [AddCommMonoid M] (Φ : (E → ℕ) → M) :
    (∑ f : (Π e : E, Finset (β e)), Φ (fun e => #(f e)))
      = ∑ k ∈ (univ.image (fun f : Π e : E, Finset (β e) => fun e => #(f e))),
          (∏ e : E, (Fintype.card (β e)).choose (k e)) • Φ k := by
  rw [Finset.sum_comp (fun k : E → ℕ => Φ k) (fun f : Π e : E, Finset (β e) => fun e => #(f e))]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  congr 1
  exact pi_card_profile_count k










open StatMech.Sharpness (ofEdgeFun)
open StatMech.Sharpness.RandomCurrent (degK adjStep connK)

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]




abbrev Copy (m : ↥G.edgeFinset → ℕ) : Type _ := Σ e : ↥G.edgeFinset, Fin (m e)



def endsM (m : ↥G.edgeFinset → ℕ) : Copy G m → Sym2 V := fun i => i.1.1




noncomputable def profileFlux (m : ↥G.edgeFinset → ℕ) (S : Finset (Copy G m)) :
    ↥G.edgeFinset → ℕ :=
  fun e => #(S.filter (fun i : Copy G m => i.1 = e))

omit [DecidableEq V] in

theorem edge_mem {a b : V} (hadj : G.Adj a b) : s(a, b) ∈ G.edgeFinset :=
  SimpleGraph.mem_edgeFinset.mpr ((SimpleGraph.mem_edgeSet G).mpr hadj)

omit [DecidableEq V] in



theorem endsM_not_isDiag (m : ↥G.edgeFinset → ℕ) (i : Copy G m) : ¬ (endsM G m i).IsDiag := by
  unfold endsM
  have hi : i.1.1 ∈ G.edgeFinset := i.1.2
  rw [SimpleGraph.mem_edgeFinset] at hi
  exact fun hdiag => G.not_isDiag_of_mem_edgeSet hi hdiag




theorem degK_eq_incidentFlux (m : ↥G.edgeFinset → ℕ) (S : Finset (Copy G m)) (x : V) :
    degK (endsM G m) S x = incidentFlux G (ofEdgeFun G (profileFlux G m S)) x := by
  unfold degK endsM
  rw [Finset.card_eq_sum_card_fiberwise
    (f := fun i : Copy G m => i.1) (t := (univ : Finset ↥G.edgeFinset))
    (by intro i _; exact mem_univ _)]
  have hRHS : incidentFlux G (ofEdgeFun G (profileFlux G m S)) x
        = ∑ e : ↥G.edgeFinset,
            (if x ∈ e.1 then (ofEdgeFun G (profileFlux G m S)) e.1 else 0) := by
    unfold incidentFlux
    rw [Finset.sum_filter,
      ← Finset.sum_attach G.edgeFinset
        (fun e => if x ∈ e then (ofEdgeFun G (profileFlux G m S)) e else 0)]
    rfl
  rw [hRHS]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  by_cases hxb : x ∈ b.1
  · rw [if_pos hxb,
      show (ofEdgeFun G (profileFlux G m S)) b.1 = profileFlux G m S b from by
        unfold ofEdgeFun; rw [dif_pos b.2]]
    unfold profileFlux
    congr 1
    ext a
    simp only [mem_filter]
    constructor
    · rintro ⟨ha1, hab⟩; exact ⟨ha1.1, hab⟩
    · rintro ⟨haS, hab⟩; exact ⟨⟨haS, by rw [hab]; exact hxb⟩, hab⟩
  · rw [if_neg hxb, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    rintro a ha hab
    simp only [mem_filter] at ha
    rw [hab] at ha
    exact hxb ha.2




theorem sources_eq (m : ↥G.edgeFinset → ℕ) (S : Finset (Copy G m)) :
    RandomCurrent.sources (endsM G m) S = sources G (ofEdgeFun G (profileFlux G m S)) := by
  ext x
  rw [RandomCurrent.mem_sources, mem_sources, degK_eq_incidentFlux]



theorem adjStep_iff (m : ↥G.edgeFinset → ℕ) (S : Finset (Copy G m)) (a b : V) :
    adjStep (endsM G m) S a b
      ↔ (currentSubgraph G (ofEdgeFun G (profileFlux G m S))).Adj a b := by
  unfold adjStep endsM
  rw [currentSubgraph_adj]
  constructor
  · rintro ⟨i, hi, ha, hb, hne⟩
    have hedge : i.1.1 = s(a, b) := (Sym2.mem_and_mem_iff hne).mp ⟨ha, hb⟩
    have hadj : G.Adj a b := by
      have hm : i.1.1 ∈ G.edgeFinset := i.1.2
      rw [hedge, SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at hm
      exact hm
    refine ⟨hadj, ?_⟩
    rw [show (ofEdgeFun G (profileFlux G m S)) s(a, b)
          = profileFlux G m S ⟨s(a, b), edge_mem G hadj⟩ from by
      unfold ofEdgeFun; rw [dif_pos (edge_mem G hadj)]]
    unfold profileFlux
    rw [Nat.one_le_iff_ne_zero, ← Nat.pos_iff_ne_zero, Finset.card_pos]
    exact ⟨i, by simp only [mem_filter]; exact ⟨hi, Subtype.ext hedge⟩⟩
  · rintro ⟨hadj, hpos⟩
    rw [show (ofEdgeFun G (profileFlux G m S)) s(a, b)
          = profileFlux G m S ⟨s(a, b), edge_mem G hadj⟩ from by
      unfold ofEdgeFun; rw [dif_pos (edge_mem G hadj)]] at hpos
    unfold profileFlux at hpos
    rw [Nat.one_le_iff_ne_zero, ← Nat.pos_iff_ne_zero, Finset.card_pos] at hpos
    obtain ⟨i, hi⟩ := hpos
    simp only [mem_filter] at hi
    refine ⟨i, hi.1, ?_, ?_, G.ne_of_adj hadj⟩
    · rw [hi.2]; exact Sym2.mem_mk_left a b
    · rw [hi.2]; exact Sym2.mem_mk_right a b





theorem connK_iff (m : ↥G.edgeFinset → ℕ) (S : Finset (Copy G m)) (a b : V) :
    connK (endsM G m) S a b ↔ CurrentConnected G (ofEdgeFun G (profileFlux G m S)) a b := by
  unfold connK CurrentConnected
  rw [SimpleGraph.reachable_iff_reflTransGen]
  constructor
  · intro h
    refine Relation.ReflTransGen.mono ?_ h
    intro a b hstep; exact (adjStep_iff G m S a b).mp hstep
  · intro h
    refine Relation.ReflTransGen.mono ?_ h
    intro a b hstep; exact (adjStep_iff G m S a b).mpr hstep




theorem fiber_card (m : ↥G.edgeFinset → ℕ) (e : ↥G.edgeFinset) :
    #((univ : Finset (Copy G m)).filter (fun i : Copy G m => i.1 = e)) = m e := by
  rw [show ((univ : Finset (Copy G m)).filter (fun i : Copy G m => i.1 = e))
        = (univ : Finset (Fin (m e))).image (fun j => (⟨e, j⟩ : Copy G m)) from ?_]
  · rw [Finset.card_image_of_injective, card_univ, Fintype.card_fin]
    intro j₁ j₂ h; simpa using h
  · ext i; simp only [mem_filter, mem_univ, true_and, mem_image]
    exact ⟨fun he => he ▸ ⟨i.2, rfl⟩, fun ⟨j, hj⟩ => hj ▸ rfl⟩


theorem profileFlux_le (m : ↥G.edgeFinset → ℕ) (S : Finset (Copy G m)) :
    profileFlux G m S ≤ m := by
  intro e; unfold profileFlux; rw [← fiber_card G m e]
  exact Finset.card_le_card (fun i hi => by
    simp only [mem_filter, mem_univ, true_and] at hi ⊢; exact hi.2)




theorem profileFlux_compl (m : ↥G.edgeFinset → ℕ) (S : Finset (Copy G m)) :
    profileFlux G m (univ \ S) = fun e => m e - profileFlux G m S e := by
  funext e
  unfold profileFlux
  rw [← fiber_card G m e]
  have hsub : (S.filter (fun i : Copy G m => i.1 = e))
      ⊆ (univ.filter (fun i : Copy G m => i.1 = e)) := by
    intro i hi; simp only [mem_filter, mem_univ, true_and] at hi ⊢; exact hi.2
  rw [show ((univ \ S).filter (fun i : Copy G m => i.1 = e))
        = (univ.filter (fun i : Copy G m => i.1 = e)) \ (S.filter (fun i : Copy G m => i.1 = e))
      from by ext i; simp only [mem_filter, mem_sdiff, mem_univ, true_and]; tauto,
    Finset.card_sdiff_of_subset hsub, fiber_card]


theorem fin_filter_lt_card (n k : ℕ) (h : k ≤ n) :
    #((univ : Finset (Fin n)).filter (fun j => j.val < k)) = k := by
  rw [show ((univ : Finset (Fin n)).filter (fun j => j.val < k))
        = (univ : Finset (Fin k)).image (fun j => (⟨j.val, by omega⟩ : Fin n)) from ?_]
  · rw [Finset.card_image_of_injective, card_univ, Fintype.card_fin]
    intro a b hab; ext; simpa using hab
  · ext j; simp only [mem_filter, mem_univ, true_and, mem_image]
    exact ⟨fun hj => ⟨⟨j.val, hj⟩, by ext; rfl⟩, fun ⟨a, ha⟩ => ha ▸ a.2⟩




theorem profileFlux_surj (m : ↥G.edgeFinset → ℕ) (K : ↥G.edgeFinset → ℕ) (hK : K ≤ m) :
    profileFlux G m (univ.filter (fun i : Copy G m => i.2.val < K i.1)) = K := by
  funext e
  unfold profileFlux
  rw [show (univ.filter (fun i : Copy G m => i.2.val < K i.1)).filter (fun i : Copy G m => i.1 = e)
        = ((univ : Finset (Fin (m e))).filter (fun j => j.val < K e)).image
            (fun j => (⟨e, j⟩ : Copy G m)) from ?_]
  · rw [Finset.card_image_of_injective _ (by intro j₁ j₂ h; simpa using h)]
    exact fin_filter_lt_card (m e) (K e) (hK e)
  · ext i
    simp only [mem_filter, mem_univ, true_and, mem_image]
    exact ⟨fun ⟨hlt, he⟩ => he ▸ ⟨i.2, hlt, rfl⟩, fun ⟨j, hj, he⟩ => he ▸ ⟨hj, rfl⟩⟩




theorem preimage_count (m : ↥G.edgeFinset → ℕ) (K : ↥G.edgeFinset → ℕ) :
    #(univ.filter (fun S : Finset (Copy G m) => profileFlux G m S = K))
      = ∏ e : ↥G.edgeFinset, (m e).choose (K e) := by
  have hprof : ∀ S : Finset (Copy G m), profileFlux G m S = fun e => #(sigmaFinsetEquivPi S e) := by
    intro S; funext e; rw [sigmaFinsetEquivPi_apply_card]; rfl
  have hbij : #(univ.filter (fun S : Finset (Copy G m) => profileFlux G m S = K))
      = #(univ.filter (fun f : Π e : ↥G.edgeFinset, Finset (Fin (m e)) =>
          (fun e => #(f e)) = K)) := by
    apply Finset.card_bij (fun S _ => sigmaFinsetEquivPi S)
    · intro S hS; simp only [mem_filter, mem_univ, true_and] at hS ⊢; rw [← hS, hprof]
    · intro S₁ _ S₂ _ h; exact sigmaFinsetEquivPi.injective h
    · intro f hf
      refine ⟨sigmaFinsetEquivPi.symm f, ?_, by rw [Equiv.apply_symm_apply]⟩
      simp only [mem_filter, mem_univ, true_and] at hf ⊢
      rw [hprof, Equiv.apply_symm_apply]; exact hf
  rw [hbij, pi_card_profile_count]
  exact Finset.prod_congr rfl (fun e _ => by rw [Fintype.card_fin])














theorem flux_edgecopy_bridge {M : Type*} [AddCommMonoid M]
    (m : ↥G.edgeFinset → ℕ) (Θ : (↥G.edgeFinset → ℕ) → M) :
    (∑ K : {p : ↥G.edgeFinset → ℕ // p ≤ m},
        (∏ e : ↥G.edgeFinset, (m e).choose (K.1 e)) • Θ K.1)
      = ∑ S : Finset (Copy G m), Θ (profileFlux G m S) := by
  classical
  
  rw [Finset.sum_comp (fun K : {p : ↥G.edgeFinset → ℕ // p ≤ m} => Θ K.1)
      (fun S : Finset (Copy G m) =>
        (⟨profileFlux G m S, profileFlux_le G m S⟩ : {p : ↥G.edgeFinset → ℕ // p ≤ m}))]
  
  
  have himg : (univ.image (fun S : Finset (Copy G m) =>
        (⟨profileFlux G m S, profileFlux_le G m S⟩ : {p : ↥G.edgeFinset → ℕ // p ≤ m})))
      = univ := by
    apply Finset.eq_univ_of_forall
    intro K
    rw [mem_image]
    refine ⟨univ.filter (fun i : Copy G m => i.2.val < K.1 i.1), mem_univ _, ?_⟩
    exact Subtype.ext (profileFlux_surj G m K.1 K.2)
  rw [himg]
  refine Finset.sum_congr rfl (fun K _ => ?_)
  
  rw [show #({S ∈ univ | (fun S : Finset (Copy G m) =>
        (⟨profileFlux G m S, profileFlux_le G m S⟩ : {p : ↥G.edgeFinset → ℕ // p ≤ m})) S = K})
        = #(univ.filter (fun S : Finset (Copy G m) => profileFlux G m S = K.1)) from ?_]
  · rw [preimage_count]
  · congr 1
    apply Finset.filter_congr
    intro S _
    rw [Subtype.ext_iff]





















theorem sourcePair_superposition_bridge (β : ℝ) (J : Sym2 V → ℝ) (A B : Finset V)
    (m : ↥G.edgeFinset → ℕ) :
    (∑ K : {p : ↥G.edgeFinset → ℕ // p ≤ m},
        (if sources G (ofEdgeFun G K.1) = A then weight G β J (ofEdgeFun G K.1) else 0)
          * (if sources G (ofEdgeFun G (fun e => m e - K.1 e)) = B
                then weight G β J (ofEdgeFun G (fun e => m e - K.1 e)) else 0))
      = (∑ S : Finset (Copy G m),
          (if RandomCurrent.sources (endsM G m) S = A then (1 : ℝ) else 0)
            * (if RandomCurrent.sources (endsM G m) (univ \ S) = B then 1 else 0))
        * weight G β J (ofEdgeFun G m) := by
  classical
  have hstep1 : ∀ K : {p : ↥G.edgeFinset → ℕ // p ≤ m},
      (if sources G (ofEdgeFun G K.1) = A then weight G β J (ofEdgeFun G K.1) else 0)
          * (if sources G (ofEdgeFun G (fun e => m e - K.1 e)) = B
                then weight G β J (ofEdgeFun G (fun e => m e - K.1 e)) else 0)
        = (∏ e : ↥G.edgeFinset, (m e).choose (K.1 e))
          • ((if sources G (ofEdgeFun G K.1) = A then (1 : ℝ) else 0)
              * (if sources G (ofEdgeFun G (fun e => m e - K.1 e)) = B then 1 else 0)
              * weight G β J (ofEdgeFun G m)) := by
    intro K
    rw [nsmul_eq_mul, Nat.cast_prod]
    by_cases hA : sources G (ofEdgeFun G K.1) = A <;>
      by_cases hB : sources G (ofEdgeFun G (fun e => m e - K.1 e)) = B
    · rw [if_pos hA, if_pos hB, if_pos hA, if_pos hB, weight_split_eq_binom G β J m K.1 K.2]
      rw [show (∏ e ∈ G.edgeFinset, (Nat.choose ((ofEdgeFun G m) e) ((ofEdgeFun G K.1) e) : ℝ))
            = (∏ e : ↥G.edgeFinset, ((m e).choose (K.1 e) : ℝ)) from by
        rw [← Finset.prod_attach G.edgeFinset
          (fun e => (Nat.choose ((ofEdgeFun G m) e) ((ofEdgeFun G K.1) e) : ℝ))]
        refine Finset.prod_congr rfl (fun e _ => ?_)
        unfold ofEdgeFun; rw [dif_pos e.2, dif_pos e.2]]
      ring
    · rw [if_neg hB]; simp [hB]
    · rw [if_neg hA]; simp [hA]
    · rw [if_neg hA]; simp [hA]
  simp_rw [hstep1]
  rw [flux_edgecopy_bridge G m (fun k =>
    (if sources G (ofEdgeFun G k) = A then (1 : ℝ) else 0)
      * (if sources G (ofEdgeFun G (fun e => m e - k e)) = B then 1 else 0)
      * weight G β J (ofEdgeFun G m))]
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl (fun S _ => ?_)
  rw [sources_eq, show (fun e => m e - profileFlux G m S e) = profileFlux G m (univ \ S) from
    (profileFlux_compl G m S).symm, sources_eq]
















theorem sourcePairSum_eq_edgecopy (β : ℝ) (J : Sym2 V → ℝ) (A B : Finset V) :
    sourcePairSum G β J A B
      = ∑' m : ↥G.edgeFinset → ℕ,
          (∑ S : Finset (Copy G m),
            (if RandomCurrent.sources (endsM G m) S = A then (1 : ℝ) else 0)
              * (if RandomCurrent.sources (endsM G m) (univ \ S) = B then 1 else 0))
          * weight G β J (ofEdgeFun G m) := by
  rw [sourcePairSum_eq_superposition]
  refine tsum_congr (fun m => ?_)
  exact sourcePair_superposition_bridge G β J A B m












theorem profileFlux_univ (m : ↥G.edgeFinset → ℕ) :
    profileFlux G m (univ : Finset (Copy G m)) = m := by
  funext e; unfold profileFlux; exact fiber_card G m e




theorem connK_univ_iff (m : ↥G.edgeFinset → ℕ) (u v : V) :
    RandomCurrent.connK (endsM G m) univ u v ↔ CurrentConnected G (ofEdgeFun G m) u v := by
  rw [connK_iff, profileFlux_univ]





theorem sourcePair_superposition_bridge_connK (β : ℝ) (J : Sym2 V → ℝ) (A B : Finset V)
    (m : ↥G.edgeFinset → ℕ) (u v : V) :
    (∑ K : {p : ↥G.edgeFinset → ℕ // p ≤ m},
        (if sources G (ofEdgeFun G K.1) = A then weight G β J (ofEdgeFun G K.1) else 0)
          * (if sources G (ofEdgeFun G (fun e => m e - K.1 e)) = B
                then weight G β J (ofEdgeFun G (fun e => m e - K.1 e)) else 0)
          * (if CurrentConnected G (ofEdgeFun G m) u v then (1 : ℝ) else 0))
      = (∑ S : Finset (Copy G m),
          (if RandomCurrent.sources (endsM G m) S = A then (1 : ℝ) else 0)
            * (if RandomCurrent.sources (endsM G m) (univ \ S) = B then 1 else 0)
            * (if RandomCurrent.connK (endsM G m) univ u v then 1 else 0))
        * weight G β J (ofEdgeFun G m) := by
  classical
  rw [show (if RandomCurrent.connK (endsM G m) univ u v then (1 : ℝ) else 0)
        = (if CurrentConnected G (ofEdgeFun G m) u v then (1 : ℝ) else 0) from by
    by_cases h : CurrentConnected G (ofEdgeFun G m) u v <;> simp [connK_univ_iff, h]]
  by_cases hC : CurrentConnected G (ofEdgeFun G m) u v
  · simp only [hC, if_true, mul_one]
    exact sourcePair_superposition_bridge G β J A B m
  · simp only [hC, if_false, mul_zero, Finset.sum_const_zero, zero_mul]







theorem sourcePair_superposition_bridge_disconn (β : ℝ) (J : Sym2 V → ℝ) (A B : Finset V)
    (m : ↥G.edgeFinset → ℕ) (u v : V) :
    (∑ K : {p : ↥G.edgeFinset → ℕ // p ≤ m},
        (if sources G (ofEdgeFun G K.1) = A then weight G β J (ofEdgeFun G K.1) else 0)
          * (if sources G (ofEdgeFun G (fun e => m e - K.1 e)) = B
                then weight G β J (ofEdgeFun G (fun e => m e - K.1 e)) else 0)
          * (if ¬ CurrentConnected G (ofEdgeFun G m) u v then (1 : ℝ) else 0))
      = (∑ S : Finset (Copy G m),
          (if RandomCurrent.sources (endsM G m) S = A then (1 : ℝ) else 0)
            * (if RandomCurrent.sources (endsM G m) (univ \ S) = B then 1 else 0)
            * (if ¬ RandomCurrent.connK (endsM G m) univ u v then 1 else 0))
        * weight G β J (ofEdgeFun G m) := by
  classical
  rw [show (if ¬ RandomCurrent.connK (endsM G m) univ u v then (1 : ℝ) else 0)
        = (if ¬ CurrentConnected G (ofEdgeFun G m) u v then (1 : ℝ) else 0) from by
    by_cases h : CurrentConnected G (ofEdgeFun G m) u v <;> simp [connK_univ_iff, h]]
  by_cases hC : CurrentConnected G (ofEdgeFun G m) u v
  · simp only [hC, not_true_eq_false, if_false, mul_zero, Finset.sum_const_zero, zero_mul]
  · simp only [hC, not_false_eq_true, if_true, mul_one]
    exact sourcePair_superposition_bridge G β J A B m













noncomputable def sourcePairDisconnSum (β : ℝ) (J : Sym2 V → ℝ) (A B : Finset V) (u v : V) : ℝ :=
  ∑' pq : (↥G.edgeFinset → ℕ) × (↥G.edgeFinset → ℕ),
    ((if sources G (ofEdgeFun G pq.1) = A then weight G β J (ofEdgeFun G pq.1) else 0)
        * (if sources G (ofEdgeFun G pq.2) = B then weight G β J (ofEdgeFun G pq.2) else 0))
      * (if ¬ CurrentConnected G (ofEdgeFun G (fun e => pq.1 e + pq.2 e)) u v then 1 else 0)





theorem sourcePairSum_conv_factor (β : ℝ) (J : Sym2 V → ℝ) (A B : Finset V)
    (W : (↥G.edgeFinset → ℕ) → ℝ) (hWb : ∀ m, |W m| ≤ 1) :
    (∑' pq : (↥G.edgeFinset → ℕ) × (↥G.edgeFinset → ℕ),
        ((if sources G (ofEdgeFun G pq.1) = A then weight G β J (ofEdgeFun G pq.1) else 0)
            * (if sources G (ofEdgeFun G pq.2) = B then weight G β J (ofEdgeFun G pq.2) else 0))
          * W (fun e => pq.1 e + pq.2 e))
      = ∑' m : ↥G.edgeFinset → ℕ,
          (∑ K : {p : ↥G.edgeFinset → ℕ // p ≤ m},
            ((if sources G (ofEdgeFun G K.1) = A then weight G β J (ofEdgeFun G K.1) else 0)
              * (if sources G (ofEdgeFun G (fun e => m e - K.1 e)) = B
                    then weight G β J (ofEdgeFun G (fun e => m e - K.1 e)) else 0)))
            * W m := by
  set f : (↥G.edgeFinset → ℕ) → ℝ :=
    fun p => if sources G (ofEdgeFun G p) = A then weight G β J (ofEdgeFun G p) else 0 with hf
  set g : (↥G.edgeFinset → ℕ) → ℝ :=
    fun q => if sources G (ofEdgeFun G q) = B then weight G β J (ofEdgeFun G q) else 0 with hg
  have hfg_norm : Summable
      (fun z : (↥G.edgeFinset → ℕ) × (↥G.edgeFinset → ℕ) => ‖f z.1 * g z.2‖) := by
    apply ((summable_norm_currentSum_summand G β J A).mul_of_nonneg
      (summable_norm_currentSum_summand G β J B)
      (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)).congr
    intro z; rw [norm_mul]
  have hsummand : Summable (fun z : (↥G.edgeFinset → ℕ) × (↥G.edgeFinset → ℕ) =>
      (f z.1 * g z.2) * W (fun e => z.1 e + z.2 e)) := by
    apply Summable.of_norm
    apply hfg_norm.of_nonneg_of_le (fun _ => norm_nonneg _) (fun z => ?_)
    rw [norm_mul]
    calc ‖f z.1 * g z.2‖ * ‖W (fun e => z.1 e + z.2 e)‖
        ≤ ‖f z.1 * g z.2‖ * 1 := by
          apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
          rw [Real.norm_eq_abs]; exact hWb _
      _ = ‖f z.1 * g z.2‖ := mul_one _
  set F : (Σ m : (↥G.edgeFinset → ℕ), {p : ↥G.edgeFinset → ℕ // p ≤ m}) → ℝ :=
    fun s => (f s.2.1 * g (fun e => s.1 e - s.2.1 e)) * W s.1 with hF
  have hcomp : ∀ z : (↥G.edgeFinset → ℕ) × (↥G.edgeFinset → ℕ),
      (f z.1 * g z.2) * W (fun e => z.1 e + z.2 e) = F (pairEquivSigma z) := by
    rintro ⟨p, q⟩
    simp only [hF, pairEquivSigma, Equiv.coe_fn_mk]
    have hsub : (fun e => (p e + q e) - p e) = q := by ext e; simp
    rw [hsub]
  have hsumF : Summable F := by
    rw [← (pairEquivSigma (E := ↥G.edgeFinset)).summable_iff]
    exact hsummand.congr (fun z => hcomp z)
  rw [tsum_congr hcomp, (pairEquivSigma (E := ↥G.edgeFinset)).tsum_eq F,
    Summable.tsum_sigma hsumF]
  refine tsum_congr (fun m => ?_)
  rw [tsum_fintype, Finset.sum_mul]
















theorem sourcePairDisconnSum_eq_edgecopy (β : ℝ) (J : Sym2 V → ℝ) (A B : Finset V) (u v : V) :
    sourcePairDisconnSum G β J A B u v
      = ∑' m : ↥G.edgeFinset → ℕ,
          (∑ S : Finset (Copy G m),
            (if RandomCurrent.sources (endsM G m) S = A then (1 : ℝ) else 0)
              * (if RandomCurrent.sources (endsM G m) (univ \ S) = B then 1 else 0)
              * (if ¬ RandomCurrent.connK (endsM G m) univ u v then 1 else 0))
          * weight G β J (ofEdgeFun G m) := by
  unfold sourcePairDisconnSum
  rw [sourcePairSum_conv_factor G β J A B
    (fun m => if ¬ CurrentConnected G (ofEdgeFun G m) u v then 1 else 0)
    (fun m => by by_cases h : CurrentConnected G (ofEdgeFun G m) u v <;> simp [h])]
  refine tsum_congr (fun m => ?_)
  rw [Finset.sum_mul]
  exact sourcePair_superposition_bridge_disconn G β J A B m u v

end FluxEdgeCopy
end Sharpness
end StatMech

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

















































import Mathlib
import Code.Walls.gc40count

open Finset BigOperators SimpleGraph
open scoped symmDiff
open Classical

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.longLine false
set_option linter.style.openClassical false
set_option linter.style.setOption false
set_option linter.unusedDecidableInType false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1600000

namespace StatMech.Walls

open StatMech StatMech.Ising StatMech.Sharpness
open StatMech.Walls.Gc5EqGap StatMech.Walls.GhcEqGap
open StatMech.Sharpness.FluxEdgeCopy
open StatMech.Sharpness.FieldGhostDict
open StatMech.Sharpness.RandomCurrent (sources connK degK compOf switching_card
  exists_conn_set sources_symmDiff path_exists mem_sources)

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]










section AbstractPi

variable {E : Type*} [Fintype E] [DecidableEq E] {γ : E → Type*}
  [∀ e, Fintype (γ e)] [∀ e, DecidableEq (γ e)]



theorem gc41_mem_sigmaFinsetEquivPi (S : Finset (Σ e : E, γ e)) (e : E) (b : γ e) :
    b ∈ sigmaFinsetEquivPi S e ↔ (⟨e, b⟩ : Σ e, γ e) ∈ S := by
  rw [show sigmaFinsetEquivPi S e
        = (univ : Finset (γ e)).filter (fun b => (⟨e, b⟩ : Σ e, γ e) ∈ S) from rfl]
  simp only [Finset.mem_filter, mem_univ, true_and]




noncomputable def gc41_pairSigmaEquivPi :
    (Finset (Σ e : E, γ e) × Finset (Σ e : E, γ e)) ≃ (Π e : E, Finset (γ e) × Finset (γ e)) where
  toFun p := fun e => (sigmaFinsetEquivPi p.1 e, sigmaFinsetEquivPi p.2 e)
  invFun f := (sigmaFinsetEquivPi.symm (fun e => (f e).1), sigmaFinsetEquivPi.symm (fun e => (f e).2))
  left_inv p := by
    obtain ⟨S₁, S₂⟩ := p
    simp only [Prod.mk.injEq]
    constructor <;> · rw [← Equiv.eq_symm_apply]; rfl
  right_inv f := by funext e; simp only [Equiv.apply_symm_apply]



theorem gc41_disj_fiberwise (S₁ S₂ : Finset (Σ e : E, γ e)) :
    S₂ ⊆ univ \ S₁ ↔ ∀ e, sigmaFinsetEquivPi S₂ e ⊆ univ \ sigmaFinsetEquivPi S₁ e := by
  constructor
  · intro h e b hb
    rw [gc41_mem_sigmaFinsetEquivPi] at hb
    have := h hb
    simp only [Finset.mem_sdiff, mem_univ, true_and] at this ⊢
    rw [gc41_mem_sigmaFinsetEquivPi]; exact this
  · intro h i hi
    obtain ⟨e, b⟩ := i
    have hmem : b ∈ sigmaFinsetEquivPi S₂ e := by rw [gc41_mem_sigmaFinsetEquivPi]; exact hi
    have := h e hmem
    simp only [Finset.mem_sdiff, mem_univ, true_and] at this ⊢
    rw [gc41_mem_sigmaFinsetEquivPi] at this; exact this




theorem gc41_perFiber_count (α : Type*) [Fintype α] [DecidableEq α] (n k1 k2 : ℕ)
    (h : Fintype.card α = n) :
    #((univ : Finset (Finset α × Finset α)).filter
        (fun p => p.2 ⊆ univ \ p.1 ∧ #p.1 = k1 ∧ #p.2 = k2))
      = n.choose k1 * (n - k1).choose k2 := by
  rw [Finset.card_eq_sum_card_fiberwise (f := fun p : Finset α × Finset α => p.1)
    (t := (univ : Finset α).powersetCard k1)
    (by
      intro p hp
      simp only [Finset.mem_coe, mem_filter, mem_univ, true_and] at hp
      simp only [mem_coe, mem_powersetCard]
      exact ⟨subset_univ _, hp.2.1⟩)]
  have hinner : ∀ A ∈ (univ : Finset α).powersetCard k1,
      #(((univ : Finset (Finset α × Finset α)).filter
          (fun p => p.2 ⊆ univ \ p.1 ∧ #p.1 = k1 ∧ #p.2 = k2)).filter (fun p => p.1 = A))
        = (n - k1).choose k2 := by
    intro A hA
    rw [mem_powersetCard] at hA
    rw [show (((univ : Finset (Finset α × Finset α)).filter
          (fun p => p.2 ⊆ univ \ p.1 ∧ #p.1 = k1 ∧ #p.2 = k2)).filter (fun p => p.1 = A))
        = ((univ \ A).powersetCard k2).image (fun B => (A, B)) from ?_]
    · rw [card_image_of_injective _ (by intro B1 B2 hB; simpa using hB)]
      rw [card_powersetCard]
      congr 1
      rw [card_univ_diff, h, hA.2]
    · ext ⟨A', B'⟩
      simp only [mem_filter, mem_univ, true_and, mem_image, mem_powersetCard]
      constructor
      · rintro ⟨⟨hsub, _, hB⟩, hA'⟩
        subst hA'
        exact ⟨B', ⟨hsub, hB⟩, rfl⟩
      · rintro ⟨B, ⟨hsub, hB⟩, heq⟩
        rw [Prod.mk.injEq] at heq
        obtain ⟨rfl, rfl⟩ := heq
        exact ⟨⟨hsub, hA.2, hB⟩, rfl⟩
  rw [Finset.sum_congr rfl hinner]
  rw [Finset.sum_const, card_powersetCard, card_univ, h, smul_eq_mul]




theorem gc41_pi_pair_profile_count (K₁ K₂ : E → ℕ) :
    #((univ : Finset (Finset (Σ e : E, γ e) × Finset (Σ e : E, γ e))).filter
        (fun p => p.2 ⊆ univ \ p.1
          ∧ (fun e => #(sigmaFinsetEquivPi p.1 e)) = K₁
          ∧ (fun e => #(sigmaFinsetEquivPi p.2 e)) = K₂))
      = ∏ e : E, ((Fintype.card (γ e)).choose (K₁ e) * (Fintype.card (γ e) - K₁ e).choose (K₂ e)) := by
  rw [show ((univ : Finset (Finset (Σ e : E, γ e) × Finset (Σ e : E, γ e))).filter
        (fun p => p.2 ⊆ univ \ p.1
          ∧ (fun e => #(sigmaFinsetEquivPi p.1 e)) = K₁
          ∧ (fun e => #(sigmaFinsetEquivPi p.2 e)) = K₂))
      = (Fintype.piFinset (fun e => (univ : Finset (Finset (γ e) × Finset (γ e))).filter
          (fun q => q.2 ⊆ univ \ q.1 ∧ #q.1 = K₁ e ∧ #q.2 = K₂ e))).image gc41_pairSigmaEquivPi.symm
      from ?_]
  · rw [card_image_of_injective _ gc41_pairSigmaEquivPi.symm.injective, Fintype.card_piFinset]
    refine Finset.prod_congr rfl (fun e _ => ?_)
    exact gc41_perFiber_count (γ e) (Fintype.card (γ e)) (K₁ e) (K₂ e) rfl
  · ext ⟨S₁, S₂⟩
    simp only [Finset.mem_filter, mem_univ, true_and, mem_image, Fintype.mem_piFinset]
    constructor
    · rintro ⟨hdisj, hp1, hp2⟩
      refine ⟨gc41_pairSigmaEquivPi (S₁, S₂), ?_, ?_⟩
      · intro e
        simp only [gc41_pairSigmaEquivPi, Equiv.coe_fn_mk, Finset.mem_filter, mem_univ, true_and]
        exact ⟨(gc41_disj_fiberwise S₁ S₂).mp hdisj e, congrFun hp1 e, congrFun hp2 e⟩
      · rw [Equiv.symm_apply_apply]
    · rintro ⟨f, hf, heq⟩
      have hS1 : S₁ = (gc41_pairSigmaEquivPi.symm f).1 := (congrArg Prod.fst heq).symm
      have hS2 : S₂ = (gc41_pairSigmaEquivPi.symm f).2 := (congrArg Prod.snd heq).symm
      subst hS1 hS2
      have hval1 : ∀ e, sigmaFinsetEquivPi (gc41_pairSigmaEquivPi.symm f).1 e = (f e).1 := by
        intro e
        show sigmaFinsetEquivPi (sigmaFinsetEquivPi.symm (fun e => (f e).1)) e = (f e).1
        rw [Equiv.apply_symm_apply]
      have hval2 : ∀ e, sigmaFinsetEquivPi (gc41_pairSigmaEquivPi.symm f).2 e = (f e).2 := by
        intro e
        show sigmaFinsetEquivPi (sigmaFinsetEquivPi.symm (fun e => (f e).2)) e = (f e).2
        rw [Equiv.apply_symm_apply]
      refine ⟨?_, ?_, ?_⟩
      · rw [gc41_disj_fiberwise]
        intro e
        have := hf e
        simp only [Finset.mem_filter, mem_univ, true_and] at this
        rw [hval1 e, hval2 e]; exact this.1
      · funext e
        have := hf e
        simp only [Finset.mem_filter, mem_univ, true_and] at this
        show #(sigmaFinsetEquivPi (gc41_pairSigmaEquivPi.symm f).1 e) = K₁ e
        rw [hval1 e]; exact this.2.1
      · funext e
        have := hf e
        simp only [Finset.mem_filter, mem_univ, true_and] at this
        show #(sigmaFinsetEquivPi (gc41_pairSigmaEquivPi.symm f).2 e) = K₂ e
        rw [hval2 e]; exact this.2.2

end AbstractPi





theorem gc41_pair_profile_count (m : ↥G.edgeFinset → ℕ) (K₁ K₂ : ↥G.edgeFinset → ℕ) :
    #((univ : Finset (Finset (Copy G m) × Finset (Copy G m))).filter
        (fun p => p.2 ⊆ univ \ p.1
          ∧ profileFlux G m p.1 = K₁ ∧ profileFlux G m p.2 = K₂))
      = ∏ e : ↥G.edgeFinset, ((m e).choose (K₁ e) * (m e - K₁ e).choose (K₂ e)) := by
  have hprof : ∀ (S : Finset (Copy G m)),
      profileFlux G m S = fun e => #(sigmaFinsetEquivPi S e) := by
    intro S; funext e; rw [sigmaFinsetEquivPi_apply_card]; rfl
  rw [show ((univ : Finset (Finset (Copy G m) × Finset (Copy G m))).filter
        (fun p => p.2 ⊆ univ \ p.1
          ∧ profileFlux G m p.1 = K₁ ∧ profileFlux G m p.2 = K₂))
      = ((univ : Finset (Finset (Copy G m) × Finset (Copy G m))).filter
        (fun p => p.2 ⊆ univ \ p.1
          ∧ (fun e => #(sigmaFinsetEquivPi p.1 e)) = K₁
          ∧ (fun e => #(sigmaFinsetEquivPi p.2 e)) = K₂)) from by
    apply Finset.filter_congr
    intro p _
    rw [hprof p.1, hprof p.2]]
  rw [gc41_pi_pair_profile_count K₁ K₂]
  exact Finset.prod_congr rfl (fun e _ => by rw [Fintype.card_fin])




theorem gc41_pairProfile_le (m : ↥G.edgeFinset → ℕ) (S₁ S₂ : Finset (Copy G m))
    (hdisj : S₂ ⊆ univ \ S₁) :
    ∀ e, profileFlux G m S₁ e + profileFlux G m S₂ e ≤ m e := by
  intro e
  have hd : Disjoint (S₁.filter (fun i : Copy G m => i.1 = e))
      (S₂.filter (fun i : Copy G m => i.1 = e)) := by
    rw [Finset.disjoint_left]
    intro i hi1 hi2
    simp only [mem_filter] at hi1 hi2
    have := hdisj hi2.1
    rw [mem_sdiff] at this
    exact this.2 hi1.1
  unfold profileFlux
  rw [← Finset.card_union_of_disjoint hd, ← fiber_card G m e]
  apply Finset.card_le_card
  intro i hi
  rw [mem_union, mem_filter, mem_filter] at hi
  simp only [mem_filter, mem_univ, true_and]
  rcases hi with ⟨_, he⟩ | ⟨_, he⟩ <;> exact he


theorem gc41_fin_filter_range_card (n a b : ℕ) (h : a + b ≤ n) :
    #((univ : Finset (Fin n)).filter (fun j => a ≤ j.val ∧ j.val < a + b)) = b := by
  rw [show ((univ : Finset (Fin n)).filter (fun j => a ≤ j.val ∧ j.val < a + b))
        = (Finset.Ico a (a + b)).attachFin (by intro k hk; rw [mem_Ico] at hk; omega) from ?_]
  · rw [Finset.card_attachFin, Nat.card_Ico]; omega
  · ext j
    simp only [mem_filter, mem_univ, true_and, Finset.mem_attachFin, mem_Ico]



theorem gc41_profile_range (m : ↥G.edgeFinset → ℕ) (K₁ K₂ : ↥G.edgeFinset → ℕ)
    (hK : ∀ e, K₁ e + K₂ e ≤ m e) :
    profileFlux G m (univ.filter (fun i : FluxEdgeCopy.Copy G m =>
        K₁ i.1 ≤ i.2.val ∧ i.2.val < K₁ i.1 + K₂ i.1))
      = K₂ := by
  funext e
  unfold profileFlux
  rw [show (univ.filter (fun i : FluxEdgeCopy.Copy G m =>
            K₁ i.1 ≤ i.2.val ∧ i.2.val < K₁ i.1 + K₂ i.1)).filter
          (fun i : FluxEdgeCopy.Copy G m => i.1 = e)
        = ((univ : Finset (Fin (m e))).filter (fun j => K₁ e ≤ j.val ∧ j.val < K₁ e + K₂ e)).image
            (fun j => (⟨e, j⟩ : FluxEdgeCopy.Copy G m)) from ?_]
  · rw [Finset.card_image_of_injective _ (by intro j₁ j₂ h; simpa using h)]
    exact gc41_fin_filter_range_card (m e) (K₁ e) (K₂ e) (hK e)
  · ext i
    simp only [mem_filter, mem_univ, true_and, mem_image]
    constructor
    · rintro ⟨⟨hlo, hhi⟩, he⟩; subst he; exact ⟨i.2, ⟨hlo, hhi⟩, rfl⟩
    · rintro ⟨j, ⟨hlo, hhi⟩, he⟩; subst he; exact ⟨⟨hlo, hhi⟩, rfl⟩












theorem gc41_pair_edgecopy_bridge {M : Type*} [AddCommMonoid M]
    (m : ↥G.edgeFinset → ℕ)
    (Θ : (↥G.edgeFinset → ℕ) → (↥G.edgeFinset → ℕ) → M) :
    (∑ K : {pq : (↥G.edgeFinset → ℕ) × (↥G.edgeFinset → ℕ) // ∀ e, pq.1 e + pq.2 e ≤ m e},
        (∏ e : ↥G.edgeFinset, ((m e).choose (K.1.1 e) * (m e - K.1.1 e).choose (K.1.2 e)))
          • Θ K.1.1 K.1.2)
      = ∑ p ∈ (univ : Finset (Finset (Copy G m) × Finset (Copy G m))).filter
          (fun p => p.2 ⊆ univ \ p.1),
          Θ (profileFlux G m p.1) (profileFlux G m p.2) := by
  classical
  set T := {pq : (↥G.edgeFinset → ℕ) × (↥G.edgeFinset → ℕ) // ∀ e, pq.1 e + pq.2 e ≤ m e} with hT
  set g : Finset (Copy G m) × Finset (Copy G m) → T := fun p =>
    if hp : p.2 ⊆ univ \ p.1
    then ⟨(profileFlux G m p.1, profileFlux G m p.2), gc41_pairProfile_le G m p.1 p.2 hp⟩
    else ⟨(fun _ => 0, fun _ => 0), fun e => by simp⟩ with hg
  have hΘ : ∀ p ∈ (univ : Finset (Finset (Copy G m) × Finset (Copy G m))).filter
        (fun p => p.2 ⊆ univ \ p.1),
      Θ (profileFlux G m p.1) (profileFlux G m p.2) = (fun K : T => Θ K.1.1 K.1.2) (g p) := by
    intro p hp
    simp only [mem_filter, mem_univ, true_and] at hp
    simp only [hg, hp, dif_pos]
  rw [Finset.sum_congr rfl hΘ, Finset.sum_comp (fun K : T => Θ K.1.1 K.1.2) g]
  
  have himg : (((univ : Finset (Finset (Copy G m) × Finset (Copy G m))).filter
        (fun p => p.2 ⊆ univ \ p.1)).image g) = univ := by
    apply Finset.eq_univ_of_forall
    intro K
    rw [mem_image]
    refine ⟨(univ.filter (fun i : FluxEdgeCopy.Copy G m => i.2.val < K.1.1 i.1),
             univ.filter (fun i : FluxEdgeCopy.Copy G m =>
                K.1.1 i.1 ≤ i.2.val ∧ i.2.val < K.1.1 i.1 + K.1.2 i.1)),
           ?_, ?_⟩
    · simp only [mem_filter, mem_univ, true_and]
      intro i hi
      simp only [mem_filter, mem_univ, true_and] at hi
      rw [mem_sdiff]
      refine ⟨mem_univ _, ?_⟩
      simp only [mem_filter, mem_univ, true_and]
      omega
    · have hdisj : (univ.filter (fun i : FluxEdgeCopy.Copy G m => K.1.1 i.1 ≤ i.2.val
              ∧ i.2.val < K.1.1 i.1 + K.1.2 i.1)) ⊆ univ \
            (univ.filter (fun i : FluxEdgeCopy.Copy G m => i.2.val < K.1.1 i.1)) := by
        intro i hi
        simp only [mem_filter, mem_univ, true_and] at hi
        rw [mem_sdiff]
        refine ⟨mem_univ _, ?_⟩
        simp only [mem_filter, mem_univ, true_and]
        omega
      have hK1le : K.1.1 ≤ m := by
        intro e; exact le_trans (Nat.le_add_right _ _) (K.2 e)
      simp only [hg, hdisj, dif_pos]
      rw [Subtype.ext_iff, Prod.ext_iff]
      refine ⟨?_, ?_⟩
      · exact profileFlux_surj G m K.1.1 hK1le
      · exact gc41_profile_range G m K.1.1 K.1.2 K.2
  rw [himg]
  refine Finset.sum_congr rfl (fun K _ => ?_)
  rw [show #(((univ : Finset (Finset (Copy G m) × Finset (Copy G m))).filter
        (fun p => p.2 ⊆ univ \ p.1)).filter (fun p => g p = K))
      = #((univ : Finset (Finset (Copy G m) × Finset (Copy G m))).filter
        (fun p => p.2 ⊆ univ \ p.1
          ∧ profileFlux G m p.1 = K.1.1 ∧ profileFlux G m p.2 = K.1.2)) from ?_]
  · rw [gc41_pair_profile_count G m K.1.1 K.1.2]
  · congr 1
    ext p
    simp only [mem_filter, mem_univ, true_and]
    constructor
    · rintro ⟨hp, hgp⟩
      simp only [hg, hp, dif_pos] at hgp
      rw [Subtype.ext_iff, Prod.ext_iff] at hgp
      exact ⟨hp, hgp.1, hgp.2⟩
    · rintro ⟨hp, h1, h2⟩
      refine ⟨hp, ?_⟩
      simp only [hg, hp, dif_pos]
      rw [Subtype.ext_iff, Prod.ext_iff]
      exact ⟨h1, h2⟩




















theorem gc41_tpsum_eq_pairCount (β : ℝ) (J : Sym2 V → ℝ) (m : ↥G.edgeFinset → ℕ) (A B : Finset V) :
    gc15_tpsum G β J m A B
      = (#((univ : Finset (Finset (Copy G m) × Finset (Copy G m))).filter
          (fun p => p.2 ⊆ univ \ p.1
            ∧ RandomCurrent.sources (endsM G m) p.1 = A
            ∧ RandomCurrent.sources (endsM G m) p.2 = B)) : ℝ)
        * weight G β J (ofEdgeFun G m) := by
  unfold gc15_tpsum
  have hstep : ∀ K : {pq : (↥G.edgeFinset → ℕ) × (↥G.edgeFinset → ℕ) // ∀ e, pq.1 e + pq.2 e ≤ m e},
      (if sources G (ofEdgeFun G K.1.1) = A then weight G β J (ofEdgeFun G K.1.1) else 0)
        * (if sources G (ofEdgeFun G K.1.2) = B then weight G β J (ofEdgeFun G K.1.2) else 0)
        * weight G β J (ofEdgeFun G (fun e => m e - K.1.1 e - K.1.2 e))
      = (∏ e : ↥G.edgeFinset, ((m e).choose (K.1.1 e) * (m e - K.1.1 e).choose (K.1.2 e)))
        • ((if sources G (ofEdgeFun G K.1.1) = A then (1:ℝ) else 0)
            * (if sources G (ofEdgeFun G K.1.2) = B then 1 else 0)
            * weight G β J (ofEdgeFun G m)) := by
    intro K
    rw [nsmul_eq_mul, Nat.cast_prod]
    by_cases hA : sources G (ofEdgeFun G K.1.1) = A
    · by_cases hB : sources G (ofEdgeFun G K.1.2) = B
      · have hprod : (∏ e ∈ G.edgeFinset, ((Nat.choose ((ofEdgeFun G m) e) ((ofEdgeFun G K.1.1) e) : ℝ)
                  * (Nat.choose ((ofEdgeFun G m) e - (ofEdgeFun G K.1.1) e) ((ofEdgeFun G K.1.2) e) : ℝ)))
              = (∏ e : ↥G.edgeFinset, ((m e).choose (K.1.1 e) * (m e - K.1.1 e).choose (K.1.2 e) : ℝ)) := by
          rw [← Finset.prod_attach G.edgeFinset
            (fun e => ((Nat.choose ((ofEdgeFun G m) e) ((ofEdgeFun G K.1.1) e) : ℝ)
                * (Nat.choose ((ofEdgeFun G m) e - (ofEdgeFun G K.1.1) e) ((ofEdgeFun G K.1.2) e) : ℝ)))]
          refine Finset.prod_congr rfl (fun e _ => ?_)
          simp only [ofEdgeFun, e.2, dif_pos]
        rw [if_pos hA, if_pos hB, if_pos hA, if_pos hB,
          weight_split₃_eq_binom G β J m K.1.1 K.1.2 K.2, hprod]
        push_cast; ring
      · rw [if_neg hB]; simp [hB]
    · rw [if_neg hA]; simp [hA]
  simp_rw [hstep]
  rw [gc41_pair_edgecopy_bridge G m (fun K₁ K₂ =>
    (if sources G (ofEdgeFun G K₁) = A then (1:ℝ) else 0)
      * (if sources G (ofEdgeFun G K₂) = B then 1 else 0)
      * weight G β J (ofEdgeFun G m))]
  rw [Finset.card_filter, Finset.sum_filter]
  push_cast
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  rw [← FluxEdgeCopy.sources_eq, ← FluxEdgeCopy.sources_eq]
  by_cases hd : p.2 ⊆ univ \ p.1 <;>
    by_cases hA : RandomCurrent.sources (endsM G m) p.1 = A <;>
    by_cases hB : RandomCurrent.sources (endsM G m) p.2 = B <;>
    simp [hd, hA, hB]











theorem gc41_sd_third {W : Type*} [DecidableEq W] (o x y g : W)
    (hox : o ≠ x) (hoy : o ≠ y) (hog : o ≠ g) (hxy : x ≠ y) (hxg : x ≠ g) (hyg : y ≠ g) :
    ({o, x, y, g} : Finset W) ∆ {o, g} ∆ {x, g} = ({y, g} : Finset W) := by
  ext a
  simp only [Finset.mem_symmDiff, Finset.mem_insert, Finset.mem_singleton]
  by_cases h1 : a = o <;> by_cases h2 : a = x <;> by_cases h3 : a = y <;> by_cases h4 : a = g <;>
    subst_vars <;> simp_all





theorem gc41_pairCount_eq_NR {ι W : Type*} [DecidableEq ι] [Fintype ι] [DecidableEq W] [Fintype W]
    (ends : ι → Sym2 W) {o x y g : W}
    (hox : o ≠ x) (hoy : o ≠ y) (hog : o ≠ g) (hxy : x ≠ y) (hxg : x ≠ g) (hyg : y ≠ g)
    (huniv : sources ends (univ : Finset ι) = ({o, x, y, g} : Finset W)) :
    #((univ : Finset (Finset ι × Finset ι)).filter
        (fun p => p.2 ⊆ univ \ p.1
          ∧ sources ends p.1 = ({o, g} : Finset W)
          ∧ sources ends p.2 = ({x, g} : Finset W)))
      = gc40_NR ends o x y g := by
  unfold gc40_NR
  congr 1
  apply Finset.filter_congr
  intro p _
  constructor
  · rintro ⟨hd, h1, h2⟩
    refine ⟨hd, h1, h2, ?_⟩
    have hcompl : (univ \ p.1) \ p.2 = (univ \ p.1) ∆ p.2 := (symmDiff_of_ge hd).symm
    rw [hcompl, sources_symmDiff, gc40_sources_compl, huniv, h1, h2,
      gc41_sd_third o x y g hox hoy hog hxy hxg hyg]
  · rintro ⟨hd, h1, h2, _⟩; exact ⟨hd, h1, h2⟩




theorem gc41_NR_eq_zero {ι W : Type*} [DecidableEq ι] [Fintype ι] [DecidableEq W] [Fintype W]
    (ends : ι → Sym2 W) {o x y g : W}
    (hox : o ≠ x) (hoy : o ≠ y) (hog : o ≠ g) (hxy : x ≠ y) (hxg : x ≠ g) (hyg : y ≠ g)
    (huniv : sources ends (univ : Finset ι) ≠ ({o, x, y, g} : Finset W)) :
    gc40_NR ends o x y g = 0 := by
  unfold gc40_NR
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  rintro ⟨S₁, S₂⟩ hmem
  simp only [mem_univ, forall_true_left]
  rintro ⟨hd, h1, h2, h3⟩
  apply huniv
  have e1 : sources ends (univ \ S₁) = sources ends univ ∆ sources ends S₁ := gc40_sources_compl ends S₁
  have hcompl : (univ \ S₁) \ S₂ = (univ \ S₁) ∆ S₂ := (symmDiff_of_ge hd).symm
  have e2 : sources ends ((univ \ S₁) \ S₂) = sources ends (univ \ S₁) ∆ sources ends S₂ := by
    rw [hcompl, sources_symmDiff]
  rw [e1, h1] at e2
  rw [h2, h3] at e2
  rw [Finset.ext_iff] at e2 ⊢
  intro a
  have ea := e2 a
  simp only [Finset.mem_symmDiff, Finset.mem_insert, Finset.mem_singleton] at ea ⊢
  by_cases h1' : a = o <;> by_cases h2' : a = x <;> by_cases h3' : a = y <;> by_cases h4' : a = g <;>
    subst_vars <;> simp_all










theorem gc41_csTriple_eq_NRsum (β h : ℝ) (o x y : V) (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y) :
    gc39_csTriple G β h o x y
      = ∑' m : ↥(withGhost G).edgeFinset → ℕ,
          (gc40_NR (endsM (withGhost G) m) (some o) (some x) (some y) none : ℝ)
            * weight (withGhost G) β (ghostCoupling h β (fun _ => 1)) (ofEdgeFun (withGhost G) m) := by
  set J' := ghostCoupling h β (fun _ => 1) with hJ'
  set W := withGhost G with hW
  unfold gc39_csTriple
  rw [← sourceTripleSum_eq_mul W β J' ({some o, none}) ({some x, none}) ({some y, none})]
  rw [gc15_sourceTripleSum_eq_tFiber W β J' ({some o, none}) ({some x, none}) ({some y, none})]
  refine tsum_congr (fun m => ?_)
  unfold gc15_tFiber
  rw [gc15_sd4 (some o) (some x) (some y) none (by simp [hox]) (by simp [hoy]) (by simp)
    (by simp [hxy]) (by simp) (by simp)]
  have huniv : RandomCurrent.sources (endsM W m) univ
      = Sharpness.sources W (ofEdgeFun W m) := by
    rw [FluxEdgeCopy.sources_eq, FluxEdgeCopy.profileFlux_univ]
  by_cases hm : Sharpness.sources W (ofEdgeFun W m)
      = ({some o, some x, some y, none} : Finset (Option V))
  · rw [if_pos hm, gc41_tpsum_eq_pairCount W β J' m ({some o, none}) ({some x, none})]
    rw [gc41_pairCount_eq_NR (endsM W m) (o := some o) (x := some x) (y := some y) (g := none)
        (by simp [hox]) (by simp [hoy]) (by simp) (by simp [hxy]) (by simp) (by simp)
        (by rw [huniv]; exact hm)]
  · rw [if_neg hm]
    rw [gc41_NR_eq_zero (endsM W m) (o := some o) (x := some x) (y := some y) (g := none)
        (by simp [hox]) (by simp [hoy]) (by simp) (by simp [hxy]) (by simp) (by simp)
        (by rw [huniv]; exact hm)]
    simp















noncomputable def gc41_allConnTripleSum (β : ℝ) (J : Sym2 V → ℝ) (A : Finset V) (o x y g : V) : ℝ :=
  ∑' z : (↥G.edgeFinset → ℕ) × (↥G.edgeFinset → ℕ) × (↥G.edgeFinset → ℕ),
    ((if sources G (ofEdgeFun G z.1) = A then weight G β J (ofEdgeFun G z.1) else 0)
      * (if sources G (ofEdgeFun G z.2.1) = (∅ : Finset V) then weight G β J (ofEdgeFun G z.2.1) else 0)
      * (if sources G (ofEdgeFun G z.2.2) = (∅ : Finset V) then weight G β J (ofEdgeFun G z.2.2) else 0))
      * (if CurrentConnected G (ofEdgeFun G (fun e => z.1 e + z.2.1 e)) o x
            ∧ CurrentConnected G (ofEdgeFun G (fun e => z.1 e + z.2.1 e)) o y
            ∧ CurrentConnected G (ofEdgeFun G (fun e => z.1 e + z.2.1 e)) o g then 1 else 0)




theorem gc41_allConnTripleSum_eq (β : ℝ) (J : Sym2 V → ℝ) (A : Finset V) (o x y g : V) :
    gc41_allConnTripleSum G β J A o x y g
      = gc38_sourcePairAllConnSum G β J A o x y g * currentSum G β J ∅ := by
  unfold gc41_allConnTripleSum gc38_sourcePairAllConnSum currentSum
  set fA : (↥G.edgeFinset → ℕ) → ℝ :=
    fun p => if sources G (ofEdgeFun G p) = A then weight G β J (ofEdgeFun G p) else 0 with hfA
  set fE : (↥G.edgeFinset → ℕ) → ℝ :=
    fun p => if sources G (ofEdgeFun G p) = (∅ : Finset V) then weight G β J (ofEdgeFun G p) else 0
    with hfE
  set gate : (↥G.edgeFinset → ℕ) × (↥G.edgeFinset → ℕ) → ℝ :=
    fun pq : (↥G.edgeFinset → ℕ) × (↥G.edgeFinset → ℕ) =>
      (if CurrentConnected G (ofEdgeFun G (fun e => pq.1 e + pq.2 e)) o x
            ∧ CurrentConnected G (ofEdgeFun G (fun e => pq.1 e + pq.2 e)) o y
            ∧ CurrentConnected G (ofEdgeFun G (fun e => pq.1 e + pq.2 e)) o g then 1 else 0) with hgate
  set P : (↥G.edgeFinset → ℕ) × (↥G.edgeFinset → ℕ) → ℝ :=
    fun pq : (↥G.edgeFinset → ℕ) × (↥G.edgeFinset → ℕ) => (fA pq.1 * fE pq.2) * gate pq with hP
  have hPnorm : Summable
      (fun pq : (↥G.edgeFinset → ℕ) × (↥G.edgeFinset → ℕ) => ‖fA pq.1 * fE pq.2‖) := by
    apply ((summable_norm_currentSum_summand G β J A).mul_of_nonneg
      (summable_norm_currentSum_summand G β J ∅) (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)).congr
    intro pq; rw [norm_mul]
  have hgateb : ∀ pq, ‖gate pq‖ ≤ 1 := by
    intro pq; rw [hgate]; simp only
    by_cases hc : CurrentConnected G (ofEdgeFun G (fun e => pq.1 e + pq.2 e)) o x
        ∧ CurrentConnected G (ofEdgeFun G (fun e => pq.1 e + pq.2 e)) o y
        ∧ CurrentConnected G (ofEdgeFun G (fun e => pq.1 e + pq.2 e)) o g
    · rw [if_pos hc]; simp
    · rw [if_neg hc]; simp
  have hPsum : Summable P := by
    apply Summable.of_norm
    apply hPnorm.of_nonneg_of_le (fun _ => norm_nonneg _) (fun pq => ?_)
    rw [hP]; simp only; rw [norm_mul]
    calc ‖fA pq.1 * fE pq.2‖ * ‖gate pq‖ ≤ ‖fA pq.1 * fE pq.2‖ * 1 :=
          mul_le_mul_of_nonneg_left (hgateb pq) (norm_nonneg _)
      _ = ‖fA pq.1 * fE pq.2‖ := mul_one _
  have hEsum : Summable fE := (summable_norm_currentSum_summand G β J ∅).of_norm
  rw [show (fun z : (↥G.edgeFinset → ℕ) × (↥G.edgeFinset → ℕ) × (↥G.edgeFinset → ℕ) =>
        (fA z.1 * fE z.2.1 * fE z.2.2) * gate (z.1, z.2.1))
      = (fun z => (fun pq : ((↥G.edgeFinset → ℕ) × (↥G.edgeFinset → ℕ)) × (↥G.edgeFinset → ℕ) =>
            P pq.1 * fE pq.2) ((Equiv.prodAssoc _ _ _).symm z)) from by
    funext z; simp only [Equiv.prodAssoc, Equiv.coe_fn_symm_mk, hP]; ring]
  rw [(Equiv.prodAssoc (↥G.edgeFinset → ℕ) (↥G.edgeFinset → ℕ) (↥G.edgeFinset → ℕ)).symm.tsum_eq
      (fun pq => P pq.1 * fE pq.2)]
  rw [Summable.tsum_mul_tsum hPsum hEsum
    (summable_mul_of_summable_norm hPsum.norm hEsum.norm)]





theorem gc41_gatedTriple_superposition (β : ℝ) (J : Sym2 V → ℝ) (A B C : Finset V)
    (Wg : (↥G.edgeFinset → ℕ) → ℝ) (hWb : ∀ p, |Wg p| ≤ 1) :
    (∑' z : (↥G.edgeFinset → ℕ) × (↥G.edgeFinset → ℕ) × (↥G.edgeFinset → ℕ),
        ((if sources G (ofEdgeFun G z.1) = A then weight G β J (ofEdgeFun G z.1) else 0)
          * (if sources G (ofEdgeFun G z.2.1) = B then weight G β J (ofEdgeFun G z.2.1) else 0)
          * (if sources G (ofEdgeFun G z.2.2) = C then weight G β J (ofEdgeFun G z.2.2) else 0))
          * Wg (fun e => z.1 e + z.2.1 e))
      = ∑' m : ↥G.edgeFinset → ℕ,
          (∑ K : {pq : (↥G.edgeFinset → ℕ) × (↥G.edgeFinset → ℕ) // ∀ e, pq.1 e + pq.2 e ≤ m e},
            (if sources G (ofEdgeFun G K.1.1) = A then weight G β J (ofEdgeFun G K.1.1) else 0)
            * (if sources G (ofEdgeFun G K.1.2) = B then weight G β J (ofEdgeFun G K.1.2) else 0)
            * (if sources G (ofEdgeFun G (fun e => m e - K.1.1 e - K.1.2 e)) = C
                  then weight G β J (ofEdgeFun G (fun e => m e - K.1.1 e - K.1.2 e)) else 0)
            * Wg (fun e => K.1.1 e + K.1.2 e)) := by
  set f : (↥G.edgeFinset → ℕ) → ℝ :=
    fun p => if sources G (ofEdgeFun G p) = A then weight G β J (ofEdgeFun G p) else 0 with hf
  set g : (↥G.edgeFinset → ℕ) → ℝ :=
    fun p => if sources G (ofEdgeFun G p) = B then weight G β J (ofEdgeFun G p) else 0 with hg
  set k : (↥G.edgeFinset → ℕ) → ℝ :=
    fun p => if sources G (ofEdgeFun G p) = C then weight G β J (ofEdgeFun G p) else 0 with hk
  set F : (Σ m : (↥G.edgeFinset → ℕ),
      {pq : (↥G.edgeFinset → ℕ) × (↥G.edgeFinset → ℕ) // ∀ e, pq.1 e + pq.2 e ≤ m e}) → ℝ :=
    fun s => f s.2.1.1 * g s.2.1.2 * k (fun e => s.1 e - s.2.1.1 e - s.2.1.2 e)
      * Wg (fun e => s.2.1.1 e + s.2.1.2 e) with hF
  have hgknorm : Summable (fun w : (↥G.edgeFinset → ℕ) × (↥G.edgeFinset → ℕ) => ‖g w.1 * k w.2‖) := by
    apply ((summable_norm_currentSum_summand G β J B).mul_of_nonneg
      (summable_norm_currentSum_summand G β J C)
      (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)).congr
    intro w; rw [norm_mul]
  have hABC := summable_mul_of_summable_norm (summable_norm_currentSum_summand G β J A) hgknorm
  have htriple : Summable (fun z : (↥G.edgeFinset → ℕ) × (↥G.edgeFinset → ℕ) × (↥G.edgeFinset → ℕ) =>
      f z.1 * g z.2.1 * k z.2.2) := by
    have heq : (fun z : (↥G.edgeFinset → ℕ) × (↥G.edgeFinset → ℕ) × (↥G.edgeFinset → ℕ) =>
        f z.1 * g z.2.1 * k z.2.2)
        = (fun z : (↥G.edgeFinset → ℕ) × (↥G.edgeFinset → ℕ) × (↥G.edgeFinset → ℕ) =>
        f z.1 * (g z.2.1 * k z.2.2)) := by funext z; rw [mul_assoc]
    rw [heq]; exact hABC
  have htripleG : Summable (fun z : (↥G.edgeFinset → ℕ) × (↥G.edgeFinset → ℕ) × (↥G.edgeFinset → ℕ) =>
      (f z.1 * g z.2.1 * k z.2.2) * Wg (fun e => z.1 e + z.2.1 e)) := by
    apply Summable.of_norm
    apply (htriple.norm).of_nonneg_of_le (fun _ => norm_nonneg _) (fun z => ?_)
    rw [norm_mul]
    calc ‖f z.1 * g z.2.1 * k z.2.2‖ * ‖Wg (fun e => z.1 e + z.2.1 e)‖
        ≤ ‖f z.1 * g z.2.1 * k z.2.2‖ * 1 := by
          apply mul_le_mul_of_nonneg_left _ (norm_nonneg _); rw [Real.norm_eq_abs]; exact hWb _
      _ = ‖f z.1 * g z.2.1 * k z.2.2‖ := mul_one _
  have hcomp : ∀ z : (↥G.edgeFinset → ℕ) × (↥G.edgeFinset → ℕ) × (↥G.edgeFinset → ℕ),
      (f z.1 * g z.2.1 * k z.2.2) * Wg (fun e => z.1 e + z.2.1 e) = F (tripleEquivSigma z) := by
    rintro ⟨p, q, r⟩
    simp only [hF, tripleEquivSigma, Equiv.coe_fn_mk]
    have hsub : (fun e => p e + q e + r e - p e - q e) = r := by ext e; omega
    rw [hsub]
  have hsumF : Summable F := by
    rw [← (tripleEquivSigma (E := ↥G.edgeFinset)).summable_iff]
    exact htripleG.congr (fun z => hcomp z)
  rw [tsum_congr hcomp, (tripleEquivSigma (E := ↥G.edgeFinset)).tsum_eq F,
    Summable.tsum_sigma hsumF]
  refine tsum_congr (fun m => ?_)
  rw [tsum_fintype]



theorem gc41_profileFlux_union (m : ↥G.edgeFinset → ℕ) (S₁ S₂ : Finset (Copy G m))
    (hd : S₂ ⊆ univ \ S₁) :
    profileFlux G m (S₁ ∪ S₂) = fun e => profileFlux G m S₁ e + profileFlux G m S₂ e := by
  funext e
  unfold profileFlux
  have hdd : Disjoint (S₁.filter (fun i : Copy G m => i.1 = e))
      (S₂.filter (fun i : Copy G m => i.1 = e)) := by
    rw [Finset.disjoint_left]; intro i hi1 hi2
    simp only [mem_filter] at hi1 hi2
    have := hd hi2.1; rw [mem_sdiff] at this; exact this.2 hi1.1
  rw [← Finset.card_union_of_disjoint hdd]
  congr 1
  ext i; simp only [mem_filter, mem_union]; tauto







theorem gc41_allConnSplit_eq_NL (β : ℝ) (J : Sym2 V → ℝ) (m : ↥G.edgeFinset → ℕ) (o x y g : V) :
    (∑ K : {pq : (↥G.edgeFinset → ℕ) × (↥G.edgeFinset → ℕ) // ∀ e, pq.1 e + pq.2 e ≤ m e},
      (if sources G (ofEdgeFun G K.1.1) = ({o, x, y, g} : Finset V)
          then weight G β J (ofEdgeFun G K.1.1) else 0)
      * (if sources G (ofEdgeFun G K.1.2) = (∅ : Finset V) then weight G β J (ofEdgeFun G K.1.2) else 0)
      * (if sources G (ofEdgeFun G (fun e => m e - K.1.1 e - K.1.2 e)) = (∅ : Finset V)
            then weight G β J (ofEdgeFun G (fun e => m e - K.1.1 e - K.1.2 e)) else 0)
      * (if CurrentConnected G (ofEdgeFun G (fun e => K.1.1 e + K.1.2 e)) o x
            ∧ CurrentConnected G (ofEdgeFun G (fun e => K.1.1 e + K.1.2 e)) o y
            ∧ CurrentConnected G (ofEdgeFun G (fun e => K.1.1 e + K.1.2 e)) o g then 1 else 0))
      = (gc40_NL (endsM G m) o x y g : ℝ) * weight G β J (ofEdgeFun G m) := by
  have hstep : ∀ K : {pq : (↥G.edgeFinset → ℕ) × (↥G.edgeFinset → ℕ) // ∀ e, pq.1 e + pq.2 e ≤ m e},
      (if sources G (ofEdgeFun G K.1.1) = ({o, x, y, g} : Finset V)
          then weight G β J (ofEdgeFun G K.1.1) else 0)
      * (if sources G (ofEdgeFun G K.1.2) = (∅ : Finset V) then weight G β J (ofEdgeFun G K.1.2) else 0)
      * (if sources G (ofEdgeFun G (fun e => m e - K.1.1 e - K.1.2 e)) = (∅ : Finset V)
            then weight G β J (ofEdgeFun G (fun e => m e - K.1.1 e - K.1.2 e)) else 0)
      * (if CurrentConnected G (ofEdgeFun G (fun e => K.1.1 e + K.1.2 e)) o x
            ∧ CurrentConnected G (ofEdgeFun G (fun e => K.1.1 e + K.1.2 e)) o y
            ∧ CurrentConnected G (ofEdgeFun G (fun e => K.1.1 e + K.1.2 e)) o g then 1 else 0)
      = (∏ e : ↥G.edgeFinset, ((m e).choose (K.1.1 e) * (m e - K.1.1 e).choose (K.1.2 e)))
        • ((if sources G (ofEdgeFun G K.1.1) = ({o, x, y, g} : Finset V) then (1 : ℝ) else 0)
            * (if sources G (ofEdgeFun G K.1.2) = (∅ : Finset V) then 1 else 0)
            * (if sources G (ofEdgeFun G (fun e => m e - K.1.1 e - K.1.2 e)) = (∅ : Finset V) then 1 else 0)
            * (if CurrentConnected G (ofEdgeFun G (fun e => K.1.1 e + K.1.2 e)) o x
                  ∧ CurrentConnected G (ofEdgeFun G (fun e => K.1.1 e + K.1.2 e)) o y
                  ∧ CurrentConnected G (ofEdgeFun G (fun e => K.1.1 e + K.1.2 e)) o g then 1 else 0)
            * weight G β J (ofEdgeFun G m)) := by
    intro K
    rw [nsmul_eq_mul, Nat.cast_prod]
    by_cases hA : sources G (ofEdgeFun G K.1.1) = ({o, x, y, g} : Finset V)
    · by_cases hB : sources G (ofEdgeFun G K.1.2) = (∅ : Finset V)
      · by_cases hC : sources G (ofEdgeFun G (fun e => m e - K.1.1 e - K.1.2 e)) = (∅ : Finset V)
        · have hprod : (∏ e ∈ G.edgeFinset, ((Nat.choose ((ofEdgeFun G m) e) ((ofEdgeFun G K.1.1) e) : ℝ)
                    * (Nat.choose ((ofEdgeFun G m) e - (ofEdgeFun G K.1.1) e) ((ofEdgeFun G K.1.2) e) : ℝ)))
                = (∏ e : ↥G.edgeFinset, ((m e).choose (K.1.1 e) * (m e - K.1.1 e).choose (K.1.2 e) : ℝ)) := by
            rw [← Finset.prod_attach G.edgeFinset
              (fun e => ((Nat.choose ((ofEdgeFun G m) e) ((ofEdgeFun G K.1.1) e) : ℝ)
                  * (Nat.choose ((ofEdgeFun G m) e - (ofEdgeFun G K.1.1) e) ((ofEdgeFun G K.1.2) e) : ℝ)))]
            refine Finset.prod_congr rfl (fun e _ => ?_)
            simp only [ofEdgeFun, e.2, dif_pos]
          rw [if_pos hA, if_pos hB, if_pos hC, if_pos hA, if_pos hB, if_pos hC,
            weight_split₃_eq_binom G β J m K.1.1 K.1.2 K.2, hprod]
          push_cast; ring
        · rw [if_neg hC]; simp [hC]
      · rw [if_neg hB]; simp [hB]
    · rw [if_neg hA]; simp [hA]
  simp_rw [hstep]
  rw [gc41_pair_edgecopy_bridge G m (fun K₁ K₂ =>
    (if sources G (ofEdgeFun G K₁) = ({o, x, y, g} : Finset V) then (1 : ℝ) else 0)
      * (if sources G (ofEdgeFun G K₂) = (∅ : Finset V) then 1 else 0)
      * (if sources G (ofEdgeFun G (fun e => m e - K₁ e - K₂ e)) = (∅ : Finset V) then 1 else 0)
      * (if CurrentConnected G (ofEdgeFun G (fun e => K₁ e + K₂ e)) o x
            ∧ CurrentConnected G (ofEdgeFun G (fun e => K₁ e + K₂ e)) o y
            ∧ CurrentConnected G (ofEdgeFun G (fun e => K₁ e + K₂ e)) o g then 1 else 0)
      * weight G β J (ofEdgeFun G m))]
  rw [Finset.sum_filter]
  unfold gc40_NL
  rw [Finset.card_filter]
  push_cast
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  by_cases hd : p.2 ⊆ univ \ p.1
  · rw [if_pos hd]
    have hcompl : profileFlux G m ((univ \ p.1) \ p.2)
        = fun e => m e - profileFlux G m p.1 e - profileFlux G m p.2 e := by
      rw [show (univ \ p.1) \ p.2 = univ \ (p.1 ∪ p.2) from by
        ext i; simp only [mem_sdiff, mem_union, mem_univ, true_and]; tauto]
      rw [FluxEdgeCopy.profileFlux_compl, gc41_profileFlux_union G m p.1 p.2 hd]
      funext e; rw [Nat.sub_add_eq]
    rw [show (fun e => m e - profileFlux G m p.1 e - profileFlux G m p.2 e)
          = profileFlux G m ((univ \ p.1) \ p.2) from hcompl.symm]
    rw [← FluxEdgeCopy.sources_eq, ← FluxEdgeCopy.sources_eq, ← FluxEdgeCopy.sources_eq]
    rw [show (fun e => profileFlux G m p.1 e + profileFlux G m p.2 e)
          = profileFlux G m (p.1 ∪ p.2) from (gc41_profileFlux_union G m p.1 p.2 hd).symm]
    rw [← FluxEdgeCopy.connK_iff, ← FluxEdgeCopy.connK_iff, ← FluxEdgeCopy.connK_iff]
    by_cases h1 : RandomCurrent.sources (endsM G m) p.1 = ({o, x, y, g} : Finset V) <;>
      by_cases h2 : RandomCurrent.sources (endsM G m) p.2 = (∅ : Finset V) <;>
      by_cases h3 : RandomCurrent.sources (endsM G m) ((univ \ p.1) \ p.2) = (∅ : Finset V) <;>
      by_cases h4 : RandomCurrent.connK (endsM G m) (p.1 ∪ p.2) o x
          ∧ RandomCurrent.connK (endsM G m) (p.1 ∪ p.2) o y
          ∧ RandomCurrent.connK (endsM G m) (p.1 ∪ p.2) o g <;>
      simp [hd, h1, h2, h3, h4]
  · rw [if_neg hd, if_neg (fun h => hd h.1), zero_mul]









theorem gc41_Z0allConn_eq_NLsum (β h : ℝ) (o x y : V) :
    gc15_Z0 G β h * gc39_allConnSum G β h o x y
      = ∑' m : ↥(withGhost G).edgeFinset → ℕ,
          (gc40_NL (endsM (withGhost G) m) (some o) (some x) (some y) none : ℝ)
            * weight (withGhost G) β (ghostCoupling h β (fun _ => 1)) (ofEdgeFun (withGhost G) m) := by
  set J' := ghostCoupling h β (fun _ => 1) with hJ'
  set W := withGhost G with hW
  unfold gc15_Z0 gc39_allConnSum
  rw [mul_comm, ← gc41_allConnTripleSum_eq W β J' ({some o, some x, some y, none})
    (some o) (some x) (some y) none]
  unfold gc41_allConnTripleSum
  rw [gc41_gatedTriple_superposition W β J' ({some o, some x, some y, none}) ∅ ∅
    (fun p => if CurrentConnected W (ofEdgeFun W p) (some o) (some x)
        ∧ CurrentConnected W (ofEdgeFun W p) (some o) (some y)
        ∧ CurrentConnected W (ofEdgeFun W p) (some o) none then 1 else 0)
    (fun p => by
      by_cases hc : CurrentConnected W (ofEdgeFun W p) (some o) (some x)
          ∧ CurrentConnected W (ofEdgeFun W p) (some o) (some y)
          ∧ CurrentConnected W (ofEdgeFun W p) (some o) none <;> simp [hc])]
  refine tsum_congr (fun m => ?_)
  rw [← gc41_allConnSplit_eq_NL W β J' m (some o) (some x) (some y) none]

























theorem gc41_NR_eq_tFiber (β h : ℝ) (o x y : V) (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y)
    (m : ↥(withGhost G).edgeFinset → ℕ) :
    (gc40_NR (endsM (withGhost G) m) (some o) (some x) (some y) none : ℝ)
        * weight (withGhost G) β (ghostCoupling h β (fun _ => 1)) (ofEdgeFun (withGhost G) m)
      = gc15_tFiber (withGhost G) β (ghostCoupling h β (fun _ => 1))
          ({some o, none}) ({some x, none}) ({some y, none}) m := by
  set J' := ghostCoupling h β (fun _ => 1) with hJ'
  set W := withGhost G with hW
  unfold gc15_tFiber
  rw [gc15_sd4 (some o) (some x) (some y) none (by simp [hox]) (by simp [hoy]) (by simp)
    (by simp [hxy]) (by simp) (by simp)]
  have huniv : RandomCurrent.sources (endsM W m) univ
      = Sharpness.sources W (ofEdgeFun W m) := by
    rw [FluxEdgeCopy.sources_eq, FluxEdgeCopy.profileFlux_univ]
  by_cases hm : Sharpness.sources W (ofEdgeFun W m)
      = ({some o, some x, some y, none} : Finset (Option V))
  · rw [if_pos hm, gc41_tpsum_eq_pairCount W β J' m ({some o, none}) ({some x, none})]
    rw [gc41_pairCount_eq_NR (endsM W m) (o := some o) (x := some x) (y := some y) (g := none)
        (by simp [hox]) (by simp [hoy]) (by simp) (by simp [hxy]) (by simp) (by simp)
        (by rw [huniv]; exact hm)]
  · rw [if_neg hm]
    rw [gc41_NR_eq_zero (endsM W m) (o := some o) (x := some x) (y := some y) (g := none)
        (by simp [hox]) (by simp [hoy]) (by simp) (by simp [hxy]) (by simp) (by simp)
        (by rw [huniv]; exact hm)]
    simp



theorem gc41_NL_le_pairCount {ι W : Type*} [DecidableEq ι] [Fintype ι] [DecidableEq W] [Fintype W]
    (ends : ι → Sym2 W) (o x y g : W) :
    gc40_NL ends o x y g
      ≤ #((univ : Finset (Finset ι × Finset ι)).filter
          (fun p => p.2 ⊆ univ \ p.1
            ∧ sources ends p.1 = ({o, x, y, g} : Finset W)
            ∧ sources ends p.2 = (∅ : Finset W))) := by
  unfold gc40_NL
  apply Finset.card_le_card
  intro p hp
  rw [Finset.mem_filter] at hp ⊢
  exact ⟨hp.1, hp.2.1, hp.2.2.1, hp.2.2.2.1⟩




theorem gc41_NL_eq_zero {ι W : Type*} [DecidableEq ι] [Fintype ι] [DecidableEq W] [Fintype W]
    (ends : ι → Sym2 W) {o x y g : W}
    (huniv : sources ends (univ : Finset ι) ≠ ({o, x, y, g} : Finset W)) :
    gc40_NL ends o x y g = 0 := by
  unfold gc40_NL
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  rintro ⟨S₁, S₂⟩ hmem
  simp only [mem_univ, forall_true_left]
  rintro ⟨hd, h1, h2, h3, _⟩
  apply huniv
  have e1 : sources ends (univ \ S₁) = sources ends univ ∆ sources ends S₁ := gc40_sources_compl ends S₁
  have hcompl : (univ \ S₁) \ S₂ = (univ \ S₁) ∆ S₂ := (symmDiff_of_ge hd).symm
  have e2 : sources ends ((univ \ S₁) \ S₂) = sources ends (univ \ S₁) ∆ sources ends S₂ := by
    rw [hcompl, sources_symmDiff]
  rw [e1, h1] at e2
  rw [h2, h3] at e2
  rw [Finset.ext_iff] at e2 ⊢
  intro a
  have ea := e2 a
  simp only [Finset.mem_symmDiff, Finset.mem_insert, Finset.mem_singleton] at ea ⊢
  by_cases h1' : a = o <;> by_cases h2' : a = x <;> by_cases h3' : a = y <;> by_cases h4' : a = g <;>
    subst_vars <;> simp_all





theorem gc41_NLweight_le_tFiber (β h : ℝ) (hβ : 0 ≤ β) (hh : 0 ≤ h) (o x y : V)
    (m : ↥(withGhost G).edgeFinset → ℕ) :
    (gc40_NL (endsM (withGhost G) m) (some o) (some x) (some y) none : ℝ)
        * weight (withGhost G) β (ghostCoupling h β (fun _ => 1)) (ofEdgeFun (withGhost G) m)
      ≤ gc15_tFiber (withGhost G) β (ghostCoupling h β (fun _ => 1))
          ({some o, some x, some y, none}) ∅ ∅ m := by
  set J' := ghostCoupling h β (fun _ => 1) with hJ'
  set W := withGhost G with hW
  have hJnn : ∀ e, (0 : ℝ) ≤ J' e := gc6_ghostCoupling_nonneg (V := V) β h hh
  have hw : 0 ≤ weight W β J' (ofEdgeFun W m) := acw_weight_nonneg W β J' hβ hJnn _
  have huniv : RandomCurrent.sources (endsM W m) univ
      = Sharpness.sources W (ofEdgeFun W m) := by
    rw [FluxEdgeCopy.sources_eq, FluxEdgeCopy.profileFlux_univ]
  unfold gc15_tFiber
  have hsd : ({some o, some x, some y, none} : Finset (Option V)) ∆ ∅ ∆ ∅
      = ({some o, some x, some y, none} : Finset (Option V)) := by simp
  by_cases hm : Sharpness.sources W (ofEdgeFun W m)
      = ({some o, some x, some y, none} : Finset (Option V))
  · rw [hsd, if_pos hm]
    rw [gc41_tpsum_eq_pairCount W β J' m ({some o, some x, some y, none}) ∅]
    apply mul_le_mul_of_nonneg_right _ hw
    exact_mod_cast gc41_NL_le_pairCount (endsM W m) (some o) (some x) (some y) none
  · rw [hsd, if_neg hm]
    rw [gc41_NL_eq_zero (endsM W m) (o := some o) (x := some x) (y := some y) (g := none)
        (by rw [huniv]; exact hm)]
    simp



theorem gc41_NLweight_nonneg (β h : ℝ) (hβ : 0 ≤ β) (hh : 0 ≤ h) (o x y : V)
    (m : ↥(withGhost G).edgeFinset → ℕ) :
    0 ≤ (gc40_NL (endsM (withGhost G) m) (some o) (some x) (some y) none : ℝ)
        * weight (withGhost G) β (ghostCoupling h β (fun _ => 1)) (ofEdgeFun (withGhost G) m) := by
  set J' := ghostCoupling h β (fun _ => 1) with hJ'
  set W := withGhost G with hW
  have hJnn : ∀ e, (0 : ℝ) ≤ J' e := gc6_ghostCoupling_nonneg (V := V) β h hh
  have hw : 0 ≤ weight W β J' (ofEdgeFun W m) := acw_weight_nonneg W β J' hβ hJnn _
  exact mul_nonneg (by positivity) hw

theorem gc41_improvedBound_of_countIneq (β h : ℝ) (hβ : 0 ≤ β) (hh : 0 ≤ h) (o x y : V)
    (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y)
    (hcnt : ∀ m : ↥(withGhost G).edgeFinset → ℕ,
      gc39_ThreeColouringCountIneq (endsM (withGhost G) m) (some o) (some x) (some y) none) :
    gc39_ThreeReplicaImprovedBound G β h o x y := by
  set J' := ghostCoupling h β (fun _ => 1) with hJ'
  set W := withGhost G with hW
  have hJnn : ∀ e, (0 : ℝ) ≤ J' e := gc6_ghostCoupling_nonneg (V := V) β h hh
  unfold gc39_ThreeReplicaImprovedBound
  rw [gc41_csTriple_eq_NRsum G β h o x y hox hoy hxy, gc41_Z0allConn_eq_NLsum G β h o x y]
  
  have hle : ∀ m : ↥W.edgeFinset → ℕ,
      (gc40_NR (endsM W m) (some o) (some x) (some y) none : ℝ) * weight W β J' (ofEdgeFun W m)
        ≤ (gc40_NL (endsM W m) (some o) (some x) (some y) none : ℝ) * weight W β J' (ofEdgeFun W m) := by
    intro m
    have hw : 0 ≤ weight W β J' (ofEdgeFun W m) := acw_weight_nonneg W β J' hβ hJnn _
    have hNR : gc40_NR (endsM W m) (some o) (some x) (some y) none
        ≤ gc40_NL (endsM W m) (some o) (some x) (some y) none :=
      (gc40_countIneq_iff (endsM W m) (some o) (some x) (some y) none).mp (hcnt m)
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hNR) hw
  
  have hsumNL : Summable (fun m : ↥W.edgeFinset → ℕ =>
      (gc40_NL (endsM W m) (some o) (some x) (some y) none : ℝ) * weight W β J' (ofEdgeFun W m)) :=
    Summable.of_nonneg_of_le
      (fun m => gc41_NLweight_nonneg G β h hβ hh o x y m)
      (fun m => gc41_NLweight_le_tFiber G β h hβ hh o x y m)
      (gc15_summable_tFiber W β J' ({some o, some x, some y, none}) ∅ ∅)
  
  have hsumNR : Summable (fun m : ↥W.edgeFinset → ℕ =>
      (gc40_NR (endsM W m) (some o) (some x) (some y) none : ℝ) * weight W β J' (ofEdgeFun W m)) :=
    (gc15_summable_tFiber W β J' ({some o, none}) ({some x, none}) ({some y, none})).congr
      (fun m => (gc41_NR_eq_tFiber G β h o x y hox hoy hxy m).symm)
  
  exact hsumNR.tsum_le_tsum hle hsumNL

end StatMech.Walls

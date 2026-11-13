/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/





































































import Mathlib
import Code.Sharpness.RandomCurrent
import Code.Sharpness.ClaimIsing
import Code.Sharpness.CurrentRep
import Code.Sharpness.TwoReplica

open SimpleGraph Finset
open scoped BigOperators symmDiff

set_option linter.unusedSectionVars false
set_option maxHeartbeats 4000000

namespace StatMech

namespace Sharpness

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]









theorem reach_restrictCompl_le (m : Current V) (S : Finset V) {u v : V}
    (hr : (currentSubgraph G (restrictTo m Sᶜ)).Reachable u v) :
    (currentSubgraph G m).Reachable u v := by
  refine hr.mono ?_
  intro x y h
  refine ⟨h.1, ?_⟩
  have hxy := h.2
  simp only [restrictTo_apply] at hxy
  by_cases hc : edgeInside Sᶜ s(x, y)
  · rw [if_pos hc] at hxy; exact hxy
  · rw [if_neg hc] at hxy; omega





theorem reach_forward (m : Current V) (S : Finset V) (hn : NoCrossing G m S) (u v : V)
    (hu : u ∉ S) (hr : (currentSubgraph G m).Reachable u v) :
    (currentSubgraph G (restrictTo m Sᶜ)).Reachable u v ∧ v ∉ S := by
  obtain ⟨w⟩ := hr
  induction w with
  | nil => exact ⟨Reachable.refl _, hu⟩
  | @cons a b c hadj rest ih =>
    have ha : a ∉ S := hu
    have hab_adj : G.Adj a b := hadj.1
    have hab_pos : 1 ≤ m s(a, b) := hadj.2
    have he : s(a, b) ∈ G.edgeFinset := by rw [mem_edgeFinset]; exact hab_adj
    rcases hn _ he hab_pos with hins | hinc
    · exact absurd (hins a (by rw [Sym2.mem_iff]; left; rfl)) ha
    · have hbnotS : b ∉ S := by
        have hbc := hinc b (by rw [Sym2.mem_iff]; right; rfl)
        rw [Finset.mem_compl] at hbc; exact hbc
      obtain ⟨hrest, hvnotS⟩ := ih hbnotS
      refine ⟨Reachable.trans ?_ hrest, hvnotS⟩
      refine Adj.reachable ⟨hab_adj, ?_⟩
      simp only [restrictTo_apply]; rw [if_pos hinc]; exact hab_pos



theorem currentConnected_iff_compl (m : Current V) (S : Finset V) (hn : NoCrossing G m S)
    (u v : V) (hu : u ∉ S) :
    CurrentConnected G m u v ↔ CurrentConnected G (restrictTo m Sᶜ) u v :=
  ⟨fun h => (reach_forward G m S hn u v hu h).1, fun h => reach_restrictCompl_le G m S h⟩



theorem not_currentConnected_in_S (m : Current V) (S : Finset V) (hn : NoCrossing G m S)
    (g : V) (hg : g ∉ S) (v : V) (hv : v ∈ S) :
    ¬ CurrentConnected G m g v := fun h => (reach_forward G m S hn g v hg h).2 hv






noncomputable def couplingIn (J : Sym2 V → ℝ) (S : Finset V) : Sym2 V → ℝ :=
  fun e => if edgeInside S e then J e else 0


def isIn (S : Finset V) : (↥G.edgeFinset) → Prop := fun i => edgeInside S (i : Sym2 V)

instance (S : Finset V) : DecidablePred (isIn G S) := fun i => by unfold isIn; infer_instance


noncomputable def aFull (S : Finset V) (a : {i : ↥G.edgeFinset // isIn G S i} → ℕ) :
    ↥G.edgeFinset → ℕ := fun i => if h : isIn G S i then a ⟨i, h⟩ else 0


noncomputable def bFull (S : Finset V) (b : {i : ↥G.edgeFinset // ¬ isIn G S i} → ℕ) :
    ↥G.edgeFinset → ℕ := fun i => if h : isIn G S i then 0 else b ⟨i, h⟩


noncomputable def reEdge (S : Finset V)
    (ab : ({i : ↥G.edgeFinset // isIn G S i} → ℕ) × ({i : ↥G.edgeFinset // ¬ isIn G S i} → ℕ)) :
    ↥G.edgeFinset → ℕ := (Equiv.piEquivPiSubtypeProd (isIn G S) (fun _ => ℕ)).symm ab

theorem aFull_notIn (S : Finset V) (a) (i : ↥G.edgeFinset) (hi : ¬ isIn G S i) :
    aFull G S a i = 0 := by unfold aFull; rw [dif_neg hi]

theorem reEdge_apply (S : Finset V) (ab) (i : ↥G.edgeFinset) :
    reEdge G S ab i = if h : isIn G S i then ab.1 ⟨i, h⟩ else ab.2 ⟨i, h⟩ := by
  unfold reEdge; simp [Equiv.piEquivPiSubtypeProd]

theorem reEdge_zero_right (S : Finset V) (a) : reEdge G S (a, fun _ => 0) = aFull G S a := by
  funext i; rw [reEdge_apply]; unfold aFull; by_cases h : isIn G S i <;> simp [h]

theorem reEdge_eq_add (S : Finset V) (a b) (i : ↥G.edgeFinset) :
    reEdge G S (a, b) i = aFull G S a i + bFull G S b i := by
  rw [reEdge_apply]; unfold aFull bFull; by_cases h : isIn G S i <;> simp [h]


theorem ofEdgeFun_reEdge_add (S : Finset V) (a b) :
    (fun e => (ofEdgeFun G (aFull G S a)) e + (ofEdgeFun G (bFull G S b)) e)
      = ofEdgeFun G (reEdge G S (a, b)) := by
  funext e; unfold ofEdgeFun
  by_cases h : e ∈ G.edgeFinset
  · rw [dif_pos h, dif_pos h, dif_pos h, reEdge_eq_add]
  · rw [dif_neg h, dif_neg h, dif_neg h]


theorem aFull_bFull_disjoint (S : Finset V) (a b) (e : Sym2 V) :
    (ofEdgeFun G (aFull G S a)) e = 0 ∨ (ofEdgeFun G (bFull G S b)) e = 0 := by
  unfold ofEdgeFun
  by_cases h : e ∈ G.edgeFinset
  · rw [dif_pos h, dif_pos h]; unfold aFull bFull
    by_cases hi : isIn G S ⟨e, h⟩
    · right; rw [dif_pos hi]
    · left; rw [dif_neg hi]
  · left; rw [dif_neg h]






theorem weight_reEdge_split (β : ℝ) (J : Sym2 V → ℝ) (S : Finset V) (a b) :
    weight G β J (ofEdgeFun G (reEdge G S (a, b)))
      = weight G β J (ofEdgeFun G (aFull G S a)) * weight G β J (ofEdgeFun G (bFull G S b)) := by
  rw [← ofEdgeFun_reEdge_add]
  unfold weight
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl (fun e _ => ?_)
  have key : ∀ (x : ℝ) (p q : ℕ), p = 0 ∨ q = 0 →
      x ^ (p + q) / (Nat.factorial (p + q)) = x ^ p / (Nat.factorial p) * (x ^ q / (Nat.factorial q)) := by
    intro x p q hpq; rcases hpq with h | h <;> subst h <;> simp
  exact key (β * J e) _ _ (aFull_bFull_disjoint G S a b e)



theorem sources_reEdge_split (S : Finset V) (a b) :
    sources G (ofEdgeFun G (reEdge G S (a, b)))
      = sources G (ofEdgeFun G (aFull G S a)) ∆ sources G (ofEdgeFun G (bFull G S b)) := by
  rw [← ofEdgeFun_reEdge_add, sources_add]



theorem incidentFlux_aFull_zero (S : Finset V) (a) {v : V} (hv : v ∉ S) :
    incidentFlux G (ofEdgeFun G (aFull G S a)) v = 0 := by
  unfold incidentFlux
  apply Finset.sum_eq_zero
  intro e he
  rw [Finset.mem_filter] at he
  obtain ⟨hee, hve⟩ := he
  rw [SimpleGraph.mem_edgeFinset] at hee
  unfold ofEdgeFun aFull
  by_cases h : e ∈ G.edgeFinset
  · rw [dif_pos h]
    by_cases hi : isIn G S ⟨e, h⟩
    · exact absurd (hi v hve) hv
    · rw [dif_neg hi]
  · exact absurd (SimpleGraph.mem_edgeFinset.mpr hee) h


theorem sources_aFull_subset (S : Finset V) (a) :
    sources G (ofEdgeFun G (aFull G S a)) ⊆ S := by
  intro v hv
  rw [mem_sources] at hv
  by_contra hvS
  rw [incidentFlux_aFull_zero G S a hvS] at hv
  exact (Nat.not_odd_iff_even.mpr ⟨0, rfl⟩) hv



theorem incidentFlux_bFull_zero_of_noCross (S : Finset V) (b)
    (hcross : ∀ i : ↥G.edgeFinset, 1 ≤ bFull G S b i → edgeInside Sᶜ (i : Sym2 V))
    {v : V} (hv : v ∈ S) :
    incidentFlux G (ofEdgeFun G (bFull G S b)) v = 0 := by
  unfold incidentFlux
  apply Finset.sum_eq_zero
  intro e he
  rw [Finset.mem_filter] at he
  obtain ⟨hee, hve⟩ := he
  rw [SimpleGraph.mem_edgeFinset] at hee
  unfold ofEdgeFun
  by_cases h : e ∈ G.edgeFinset
  · rw [dif_pos h]
    by_cases hpos : 1 ≤ bFull G S b ⟨e, h⟩
    · have hvc := (hcross ⟨e, h⟩ hpos) v hve
      rw [Finset.mem_compl] at hvc; exact absurd hv hvc
    · omega
  · exact absurd (SimpleGraph.mem_edgeFinset.mpr hee) h



theorem sources_bFull_subset_compl (S : Finset V) (b)
    (hcross : ∀ i : ↥G.edgeFinset, 1 ≤ bFull G S b i → edgeInside Sᶜ (i : Sym2 V)) :
    sources G (ofEdgeFun G (bFull G S b)) ⊆ Sᶜ := by
  intro v hv
  rw [mem_sources] at hv
  rw [Finset.mem_compl]
  intro hvS
  rw [incidentFlux_bFull_zero_of_noCross G S b hcross hvS] at hv
  exact (Nat.not_odd_iff_even.mpr ⟨0, rfl⟩) hv





theorem weight_couplingIn_aFull (β : ℝ) (J : Sym2 V → ℝ) (S : Finset V) (a) :
    weight G β (couplingIn J S) (ofEdgeFun G (aFull G S a))
      = weight G β J (ofEdgeFun G (aFull G S a)) := by
  rw [weight_ofEdgeFun, weight_ofEdgeFun]
  refine Finset.prod_congr rfl (fun e _ => ?_)
  unfold couplingIn
  by_cases hi : edgeInside S e.1
  · rw [if_pos hi]
  · rw [if_neg hi, aFull_notIn G S a e (by unfold isIn; exact hi)]; simp



theorem weight_reEdge_eq_zero (β : ℝ) (J : Sym2 V → ℝ) (S : Finset V) (a)
    (b : {i : ↥G.edgeFinset // ¬ isIn G S i} → ℕ)
    (j : {i : ↥G.edgeFinset // ¬ isIn G S i}) (hj : 1 ≤ b j) :
    weight G β (couplingIn J S) (ofEdgeFun G (reEdge G S (a, b))) = 0 := by
  rw [weight_ofEdgeFun]
  apply Finset.prod_eq_zero (Finset.mem_univ j.1)
  have hcoup : couplingIn J S j.1.1 = 0 := if_neg j.2
  rw [hcoup, mul_zero]
  have hpos : 1 ≤ reEdge G S (a, b) j.1 := by rw [reEdge_apply, dif_neg j.2]; convert hj
  rw [zero_pow (by omega), zero_div]




theorem currentSum_couplingIn_eq (β : ℝ) (J : Sym2 V → ℝ) (S : Finset V) (A : Finset V) :
    currentSum G β (couplingIn J S) A
      = ∑' a : {i : ↥G.edgeFinset // isIn G S i} → ℕ,
          (if sources G (ofEdgeFun G (aFull G S a)) = A
            then weight G β J (ofEdgeFun G (aFull G S a)) else 0) := by
  unfold currentSum
  rw [← (Equiv.piEquivPiSubtypeProd (isIn G S) (fun _ => ℕ)).symm.tsum_eq]
  rw [Summable.tsum_prod ?_]
  · refine tsum_congr (fun a => ?_)
    rw [tsum_eq_single (fun _ => 0) ?_]
    · show (if sources G (ofEdgeFun G (reEdge G S (a, fun _ => 0))) = A
              then weight G β (couplingIn J S) (ofEdgeFun G (reEdge G S (a, fun _ => 0))) else 0) = _
      rw [reEdge_zero_right]
      by_cases hA : sources G (ofEdgeFun G (aFull G S a)) = A
      · rw [if_pos hA, if_pos hA, weight_couplingIn_aFull]
      · rw [if_neg hA, if_neg hA]
    · intro b hb
      have hex : ∃ j, 1 ≤ b j := by
        by_contra hc; push Not at hc
        exact hb (funext (fun j => by have := hc j; omega))
      obtain ⟨j, hj⟩ := hex
      show (if sources G (ofEdgeFun G (reEdge G S (a, b))) = A
              then weight G β (couplingIn J S) (ofEdgeFun G (reEdge G S (a, b))) else 0) = 0
      rw [weight_reEdge_eq_zero G β J S a b j hj]; simp
  · have hsum := (summable_norm_currentSum_summand G β (couplingIn J S) A).of_norm
    rw [← (Equiv.piEquivPiSubtypeProd (isIn G S) (fun _ => ℕ)).symm.summable_iff
      (f := fun m => if sources G (ofEdgeFun G m) = A then weight G β (couplingIn J S) (ofEdgeFun G m)
        else 0)] at hsum
    exact hsum



theorem aFull_injective (S : Finset V) : Function.Injective (aFull G S) := by
  intro a a' h; funext i
  have hh := congrFun h i.1
  unfold aFull at hh; rw [dif_pos i.2, dif_pos i.2] at hh; convert hh

theorem bFull_injective (S : Finset V) : Function.Injective (bFull G S) := by
  intro b b' h; funext i
  have hh := congrFun h i.1
  unfold bFull at hh; rw [dif_neg i.2, dif_neg i.2] at hh; convert hh



theorem summable_norm_weight_aFull (β : ℝ) (J : Sym2 V → ℝ) (S : Finset V) :
    Summable (fun a : {i : ↥G.edgeFinset // isIn G S i} → ℕ =>
      ‖weight G β J (ofEdgeFun G (aFull G S a))‖) :=
  (summable_norm_weight_ofEdgeFun G β J).comp_injective (aFull_injective G S)


theorem summable_norm_weight_bFull (β : ℝ) (J : Sym2 V → ℝ) (S : Finset V) :
    Summable (fun b : {i : ↥G.edgeFinset // ¬ isIn G S i} → ℕ =>
      ‖weight G β J (ofEdgeFun G (bFull G S b))‖) :=
  (summable_norm_weight_ofEdgeFun G β J).comp_injective (bFull_injective G S)

















theorem summand_factor (β : ℝ) (J : Sym2 V → ℝ) (S : Finset V) (P : Current V → Prop)
    [DecidablePred P]
    (H1 : ∀ m, P m → NoCrossing G m S)
    (H2 : ∀ m m' : Current V, (∀ i ∈ G.edgeFinset, ¬ edgeInside S i → m i = m' i) → (P m ↔ P m'))
    (A : Finset V) (hAS : A ⊆ S)
    (a : {i : ↥G.edgeFinset // isIn G S i} → ℕ) (b : {i : ↥G.edgeFinset // ¬ isIn G S i} → ℕ)
    (n₂ : ↥G.edgeFinset → ℕ) :
    (if sources G (ofEdgeFun G (reEdge G S (a, b))) = A then
        weight G β J (ofEdgeFun G (reEdge G S (a, b))) else 0)
      * (if sources G (ofEdgeFun G n₂) = ∅ then weight G β J (ofEdgeFun G n₂) else 0)
      * (if P (fun e => ofEdgeFun G (reEdge G S (a, b)) e + ofEdgeFun G n₂ e) then 1 else 0)
    = (if sources G (ofEdgeFun G (aFull G S a)) = A then
        weight G β J (ofEdgeFun G (aFull G S a)) else 0)
      * ((if sources G (ofEdgeFun G (bFull G S b)) = ∅ then weight G β J (ofEdgeFun G (bFull G S b)) else 0)
        * (if sources G (ofEdgeFun G n₂) = ∅ then weight G β J (ofEdgeFun G n₂) else 0)
        * (if P (fun e => ofEdgeFun G (bFull G S b) e + ofEdgeFun G n₂ e) then 1 else 0)) := by
  
  have hP : P (fun e => ofEdgeFun G (reEdge G S (a, b)) e + ofEdgeFun G n₂ e)
      ↔ P (fun e => ofEdgeFun G (bFull G S b) e + ofEdgeFun G n₂ e) := by
    apply H2
    intro i _ hi
    
    have : ofEdgeFun G (reEdge G S (a, b)) i = ofEdgeFun G (bFull G S b) i := by
      unfold ofEdgeFun
      by_cases h : i ∈ G.edgeFinset
      · rw [dif_pos h, dif_pos h, reEdge_eq_add, aFull, dif_neg (by unfold isIn; exact hi), zero_add]
      · rw [dif_neg h, dif_neg h]
    rw [this]
  by_cases hev : P (fun e => ofEdgeFun G (bFull G S b) e + ofEdgeFun G n₂ e)
  · 
    rw [if_pos hev, if_pos (hP.mpr hev), mul_one, mul_one]
    
    have hncross : NoCrossing G (fun e => ofEdgeFun G (reEdge G S (a, b)) e + ofEdgeFun G n₂ e) S :=
      H1 _ (hP.mpr (hev))
    
    have hcross : ∀ i : ↥G.edgeFinset, 1 ≤ bFull G S b i → edgeInside Sᶜ (i : Sym2 V) := by
      intro i hipos
      have he : (i : Sym2 V) ∈ G.edgeFinset := i.2
      have hsuper : 1 ≤ (fun e => ofEdgeFun G (reEdge G S (a, b)) e + ofEdgeFun G n₂ e) i.1 := by
        have hge : bFull G S b i ≤ ofEdgeFun G (reEdge G S (a, b)) i.1 := by
          rw [show ofEdgeFun G (reEdge G S (a, b)) i.1 = reEdge G S (a, b) i from by
            unfold ofEdgeFun; rw [dif_pos i.2]]
          rw [reEdge_eq_add]; omega
        simp only; omega
      rcases hncross _ he hsuper with hi | hi
      · 
        exfalso
        have hni : ¬ isIn G S i := by
          intro hii; unfold bFull at hipos; rw [dif_pos hii] at hipos; omega
        exact hni hi
      · exact hi
    
    have haS : sources G (ofEdgeFun G (aFull G S a)) ⊆ S := sources_aFull_subset G S a
    have hbSc : sources G (ofEdgeFun G (bFull G S b)) ⊆ Sᶜ := sources_bFull_subset_compl G S b hcross
    
    have hdisj : Disjoint (sources G (ofEdgeFun G (aFull G S a)))
        (sources G (ofEdgeFun G (bFull G S b))) := by
      refine Finset.disjoint_left.mpr (fun v hva hvb => ?_)
      exact (Finset.mem_compl.mp (hbSc hvb)) (haS hva)
    
    rw [sources_reEdge_split]
    by_cases hcon : sources G (ofEdgeFun G (aFull G S a)) ∆ sources G (ofEdgeFun G (bFull G S b))
        = A
    · 
      have hunion : sources G (ofEdgeFun G (aFull G S a)) ∪ sources G (ofEdgeFun G (bFull G S b))
          = A := by
        rw [← hcon, ← (symmDiff_eq_union_iff _ _).mpr hdisj]
      have hbempty : sources G (ofEdgeFun G (bFull G S b)) = ∅ := by
        rw [Finset.eq_empty_iff_forall_notMem]
        intro v hvb
        have hvScompl : v ∈ Sᶜ := hbSc hvb
        have hvA : v ∈ A := by rw [← hunion]; exact Finset.mem_union_right _ hvb
        exact (Finset.mem_compl.mp hvScompl) (hAS hvA)
      have haval : sources G (ofEdgeFun G (aFull G S a)) = A := by
        rw [← hunion, hbempty, Finset.union_empty]
      rw [if_pos hcon, if_pos haval, if_pos hbempty, weight_reEdge_split]; ring
    · 
      rw [if_neg hcon]
      by_cases haval : sources G (ofEdgeFun G (aFull G S a)) = A
      · by_cases hbempty : sources G (ofEdgeFun G (bFull G S b)) = ∅
        · exfalso; apply hcon; rw [haval, hbempty]; simp
        · rw [if_neg hbempty]; ring
      · rw [if_neg haval]; ring
  · 
    rw [if_neg hev, if_neg (fun h => hev (hP.mp h))]
    ring




noncomputable def contextSummand (β : ℝ) (J : Sym2 V → ℝ) (S : Finset V) (P : Current V → Prop)
    [DecidablePred P]
    (bn : ({i : ↥G.edgeFinset // ¬ isIn G S i} → ℕ) × (↥G.edgeFinset → ℕ)) : ℝ :=
  (if sources G (ofEdgeFun G (bFull G S bn.1)) = ∅ then weight G β J (ofEdgeFun G (bFull G S bn.1)) else 0)
    * (if sources G (ofEdgeFun G bn.2) = ∅ then weight G β J (ofEdgeFun G bn.2) else 0)
    * (if P (fun e => ofEdgeFun G (bFull G S bn.1) e + ofEdgeFun G bn.2 e) then 1 else 0)



noncomputable def factorSummand (β : ℝ) (J : Sym2 V → ℝ) (S : Finset V) (A : Finset V)
    (a : {i : ↥G.edgeFinset // isIn G S i} → ℕ) : ℝ :=
  if sources G (ofEdgeFun G (aFull G S a)) = A then weight G β J (ofEdgeFun G (aFull G S a)) else 0


theorem norm_factorSummand_le (β : ℝ) (J : Sym2 V → ℝ) (S : Finset V) (A : Finset V)
    (a : {i : ↥G.edgeFinset // isIn G S i} → ℕ) :
    ‖factorSummand G β J S A a‖ ≤ ‖weight G β J (ofEdgeFun G (aFull G S a))‖ := by
  unfold factorSummand
  by_cases h : sources G (ofEdgeFun G (aFull G S a)) = A
  · rw [if_pos h]
  · rw [if_neg h, norm_zero]; positivity


theorem summable_factorSummand (β : ℝ) (J : Sym2 V → ℝ) (S : Finset V) (A : Finset V) :
    Summable (factorSummand G β J S A) :=
  Summable.of_norm ((summable_norm_weight_aFull G β J S).of_nonneg_of_le (fun _ => norm_nonneg _)
    (norm_factorSummand_le G β J S A))



theorem norm_triple_le (w₁ w₂ : ℝ) (P₁ P₂ P₃ : Prop) [Decidable P₁] [Decidable P₂] [Decidable P₃] :
    ‖(if P₁ then w₁ else 0) * (if P₂ then w₂ else 0) * (if P₃ then (1 : ℝ) else 0)‖
      ≤ ‖w₁‖ * ‖w₂‖ := by
  rw [norm_mul, norm_mul]
  have h1 : ‖(if P₁ then w₁ else 0)‖ ≤ ‖w₁‖ := by by_cases h : P₁ <;> simp [h]
  have h2 : ‖(if P₂ then w₂ else 0)‖ ≤ ‖w₂‖ := by by_cases h : P₂ <;> simp [h]
  have h3 : ‖(if P₃ then (1 : ℝ) else 0)‖ ≤ 1 := by by_cases h : P₃ <;> simp [h]
  calc ‖if P₁ then w₁ else 0‖ * ‖if P₂ then w₂ else 0‖ * ‖if P₃ then (1 : ℝ) else 0‖
      ≤ ‖w₁‖ * ‖w₂‖ * 1 :=
        mul_le_mul (mul_le_mul h1 h2 (norm_nonneg _) (norm_nonneg _)) h3 (norm_nonneg _) (by positivity)
    _ = ‖w₁‖ * ‖w₂‖ := by ring


theorem norm_contextSummand_le (β : ℝ) (J : Sym2 V → ℝ) (S : Finset V) (P : Current V → Prop)
    [DecidablePred P]
    (bn : ({i : ↥G.edgeFinset // ¬ isIn G S i} → ℕ) × (↥G.edgeFinset → ℕ)) :
    ‖contextSummand G β J S P bn‖
      ≤ ‖weight G β J (ofEdgeFun G (bFull G S bn.1))‖ * ‖weight G β J (ofEdgeFun G bn.2)‖ :=
  norm_triple_le _ _ _ _ _



theorem summable_contextSummand (β : ℝ) (J : Sym2 V → ℝ) (S : Finset V) (P : Current V → Prop)
    [DecidablePred P] :
    Summable (contextSummand G β J S P) := by
  have hdom : Summable (fun bn : ({i : ↥G.edgeFinset // ¬ isIn G S i} → ℕ) × (↥G.edgeFinset → ℕ) =>
      ‖weight G β J (ofEdgeFun G (bFull G S bn.1))‖ * ‖weight G β J (ofEdgeFun G bn.2)‖) :=
    Summable.mul_of_nonneg (summable_norm_weight_bFull G β J S)
      (summable_norm_weight_ofEdgeFun G β J) (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)
  exact Summable.of_norm (hdom.of_nonneg_of_le (fun _ => norm_nonneg _)
    (norm_contextSummand_le G β J S P))


theorem summable_factor_context (β : ℝ) (J : Sym2 V → ℝ) (S : Finset V) (A : Finset V)
    (P : Current V → Prop) [DecidablePred P] :
    Summable (fun abn : ({i : ↥G.edgeFinset // isIn G S i} → ℕ) ×
        (({i : ↥G.edgeFinset // ¬ isIn G S i} → ℕ) × (↥G.edgeFinset → ℕ)) =>
      factorSummand G β J S A abn.1 * contextSummand G β J S P abn.2) := by
  have hfn : Summable (fun a => ‖factorSummand G β J S A a‖) :=
    (summable_norm_weight_aFull G β J S).of_nonneg_of_le (fun _ => norm_nonneg _)
      (norm_factorSummand_le G β J S A)
  have hgn : Summable (fun bn => ‖contextSummand G β J S P bn‖) := by
    have hdom : Summable (fun bn : ({i : ↥G.edgeFinset // ¬ isIn G S i} → ℕ) × (↥G.edgeFinset → ℕ) =>
        ‖weight G β J (ofEdgeFun G (bFull G S bn.1))‖ * ‖weight G β J (ofEdgeFun G bn.2)‖) :=
      Summable.mul_of_nonneg (summable_norm_weight_bFull G β J S)
        (summable_norm_weight_ofEdgeFun G β J) (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)
    exact hdom.of_nonneg_of_le (fun _ => norm_nonneg _) (norm_contextSummand_le G β J S P)
  exact summable_mul_of_summable_norm hfn hgn






theorem claim2_pairSum_factor (β : ℝ) (J : Sym2 V → ℝ) (S : Finset V) (P : Current V → Prop)
    [DecidablePred P]
    (H1 : ∀ m, P m → NoCrossing G m S)
    (H2 : ∀ m m' : Current V, (∀ i ∈ G.edgeFinset, ¬ edgeInside S i → m i = m' i) → (P m ↔ P m'))
    (A : Finset V) (hAS : A ⊆ S) :
    (∑' pq : (↥G.edgeFinset → ℕ) × (↥G.edgeFinset → ℕ),
        (if sources G (ofEdgeFun G pq.1) = A then weight G β J (ofEdgeFun G pq.1) else 0)
          * (if sources G (ofEdgeFun G pq.2) = ∅ then weight G β J (ofEdgeFun G pq.2) else 0)
          * (if P (fun e => ofEdgeFun G pq.1 e + ofEdgeFun G pq.2 e) then 1 else 0))
    = currentSum G β (couplingIn J S) A
      * (∑' bn : ({i : ↥G.edgeFinset // ¬ isIn G S i} → ℕ) × (↥G.edgeFinset → ℕ),
          contextSummand G β J S P bn) := by
  
  set E := Equiv.piEquivPiSubtypeProd (isIn G S) (fun _ : ↥G.edgeFinset => ℕ)
  set E' := E.prodCongr (Equiv.refl (↥G.edgeFinset → ℕ))
  
  rw [← E'.symm.tsum_eq]
  
  have hsummand : ∀ pq : (({i : ↥G.edgeFinset // isIn G S i} → ℕ)
        × ({i : ↥G.edgeFinset // ¬ isIn G S i} → ℕ)) × (↥G.edgeFinset → ℕ),
      ((if sources G (ofEdgeFun G (E'.symm pq).1) = A then weight G β J (ofEdgeFun G (E'.symm pq).1) else 0)
          * (if sources G (ofEdgeFun G (E'.symm pq).2) = ∅ then weight G β J (ofEdgeFun G (E'.symm pq).2) else 0)
          * (if P (fun e => ofEdgeFun G (E'.symm pq).1 e + ofEdgeFun G (E'.symm pq).2 e) then 1 else 0))
        = factorSummand G β J S A pq.1.1 * contextSummand G β J S P (pq.1.2, pq.2) := by
    rintro ⟨⟨a, b⟩, n₂⟩
    have heq : E'.symm ((a, b), n₂) = (reEdge G S (a, b), n₂) := rfl
    rw [heq]
    unfold factorSummand contextSummand
    exact summand_factor G β J S P H1 H2 A hAS a b n₂
  rw [tsum_congr hsummand]
  
  rw [show (∑' pq : (({i : ↥G.edgeFinset // isIn G S i} → ℕ)
            × ({i : ↥G.edgeFinset // ¬ isIn G S i} → ℕ)) × (↥G.edgeFinset → ℕ),
          factorSummand G β J S A pq.1.1 * contextSummand G β J S P (pq.1.2, pq.2))
        = ∑' pq, (fun abn => factorSummand G β J S A abn.1 * contextSummand G β J S P abn.2)
            (Equiv.prodAssoc _ _ _ pq) from rfl]
  rw [(Equiv.prodAssoc _ _ _).tsum_eq (fun abn => factorSummand G β J S A abn.1
      * contextSummand G β J S P abn.2)]
  rw [← Summable.tsum_mul_tsum (summable_factorSummand G β J S A) (summable_contextSummand G β J S P)
      (summable_factor_context G β J S A P)]
  rw [currentSum_couplingIn_eq]
  rfl









theorem claim2_abstract (β : ℝ) (J : Sym2 V → ℝ) (S : Finset V) (P : Current V → Prop)
    [DecidablePred P]
    (H1 : ∀ m, P m → NoCrossing G m S)
    (H2 : ∀ m m' : Current V, (∀ i ∈ G.edgeFinset, ¬ edgeInside S i → m i = m' i) → (P m ↔ P m'))
    (zero x : V) (h0 : zero ∈ S) (hx : x ∈ S)
    (hZ : currentSum G β (couplingIn J S) ∅ ≠ 0) :
    (∑' pq : (↥G.edgeFinset → ℕ) × (↥G.edgeFinset → ℕ),
        (if sources G (ofEdgeFun G pq.1) = {zero, x} then weight G β J (ofEdgeFun G pq.1) else 0)
          * (if sources G (ofEdgeFun G pq.2) = ∅ then weight G β J (ofEdgeFun G pq.2) else 0)
          * (if P (fun e => ofEdgeFun G pq.1 e + ofEdgeFun G pq.2 e) then 1 else 0))
    = expectationJ G β (couplingIn J S) {zero, x}
      * (∑' pq : (↥G.edgeFinset → ℕ) × (↥G.edgeFinset → ℕ),
          (if sources G (ofEdgeFun G pq.1) = ∅ then weight G β J (ofEdgeFun G pq.1) else 0)
            * (if sources G (ofEdgeFun G pq.2) = ∅ then weight G β J (ofEdgeFun G pq.2) else 0)
            * (if P (fun e => ofEdgeFun G pq.1 e + ofEdgeFun G pq.2 e) then 1 else 0)) := by
  have h0x : ({zero, x} : Finset V) ⊆ S := by
    intro v hv; rw [Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl
    · exact h0
    · exact hx
  rw [claim2_pairSum_factor G β J S P H1 H2 {zero, x} h0x,
    claim2_pairSum_factor G β J S P H1 H2 ∅ (Finset.empty_subset _)]
  
  rw [current_representation]
  rw [div_mul_eq_mul_div, mul_div_assoc,
    mul_comm (currentSum G β (couplingIn J S) ∅), mul_div_assoc, div_self hZ, mul_one]







open Classical in

noncomputable def notConnComp (m : Current V) (g : V) : Finset V :=
  Finset.univ.filter (fun v => ¬ CurrentConnected G m g v)

theorem mem_notConnComp {m : Current V} {g v : V} :
    v ∈ notConnComp G m g ↔ ¬ CurrentConnected G m g v := by
  classical simp [notConnComp]





theorem noCrossing_of_event (m : Current V) (S : Finset V) (g : V) (_hg : g ∉ S)
    (hev : notConnComp G m g = S) : NoCrossing G m S := by
  intro e he hpos
  obtain ⟨⟨u, v⟩, huv⟩ := e.exists_rep
  subst huv
  have hadj : G.Adj u v := by rw [mem_edgeFinset, mem_edgeSet] at he; exact he
  by_cases hu : u ∈ S <;> by_cases hv : v ∈ S
  · left; intro w hw; rw [Sym2.mem_iff] at hw; rcases hw with rfl | rfl <;> assumption
  · 
    exfalso
    have hconn_uv : CurrentConnected G m u v := Adj.reachable ⟨hadj, hpos⟩
    have hvconn : CurrentConnected G m g v := by
      by_contra hc; exact hv (hev ▸ (mem_notConnComp G).mpr hc)
    have huconn : CurrentConnected G m g u := SimpleGraph.Reachable.trans hvconn hconn_uv.symm
    exact ((mem_notConnComp G).not.mpr (not_not.mpr huconn)) (hev ▸ hu)
  · 
    exfalso
    have hconn_uv : CurrentConnected G m v u :=
      Adj.reachable ⟨hadj.symm, by rwa [Sym2.eq_swap]⟩
    have huconn : CurrentConnected G m g u := by
      by_contra hc; exact hu (hev ▸ (mem_notConnComp G).mpr hc)
    have hvconn : CurrentConnected G m g v := SimpleGraph.Reachable.trans huconn hconn_uv.symm
    exact ((mem_notConnComp G).not.mpr (not_not.mpr hvconn)) (hev ▸ hv)
  · right; intro w hw; rw [Finset.mem_compl]; rw [Sym2.mem_iff] at hw
    rcases hw with rfl | rfl <;> assumption



theorem currentSubgraph_restrictCompl_congr (m m' : Current V) (S : Finset V)
    (hagree : ∀ i ∈ G.edgeFinset, ¬ edgeInside S i → m i = m' i) :
    currentSubgraph G (restrictTo m Sᶜ) = currentSubgraph G (restrictTo m' Sᶜ) := by
  ext u v
  simp only [currentSubgraph_adj, restrictTo_apply]
  constructor <;> rintro ⟨hadj, hpos⟩ <;> refine ⟨hadj, ?_⟩ <;>
    by_cases hc : edgeInside Sᶜ s(u, v)
  · rw [if_pos hc] at hpos ⊢
    have he : s(u, v) ∈ G.edgeFinset := by rw [mem_edgeFinset, mem_edgeSet]; exact hadj
    rw [← hagree _ he (fun hi => not_edgeInside_compl_of_edgeInside S _ hi hc)]; exact hpos
  · rw [if_neg hc] at hpos; omega
  · rw [if_pos hc] at hpos ⊢
    have he : s(u, v) ∈ G.edgeFinset := by rw [mem_edgeFinset, mem_edgeSet]; exact hadj
    rw [hagree _ he (fun hi => not_edgeInside_compl_of_edgeInside S _ hi hc)]; exact hpos
  · rw [if_neg hc] at hpos; omega


theorem noCrossing_congr (m m' : Current V) (S : Finset V) (hnm : NoCrossing G m S)
    (hagree : ∀ i ∈ G.edgeFinset, ¬ edgeInside S i → m i = m' i) :
    NoCrossing G m' S := by
  intro e he hpos
  by_cases hi : edgeInside S e
  · exact Or.inl hi
  · have hmpos : 1 ≤ m e := by rw [hagree e he hi]; exact hpos
    rcases hnm e he hmpos with h | h
    · exact absurd h hi
    · exact Or.inr h





theorem notConnComp_congr (m m' : Current V) (S : Finset V) (g : V) (hg : g ∉ S)
    (hev : notConnComp G m g = S)
    (hagree : ∀ i ∈ G.edgeFinset, ¬ edgeInside S i → m i = m' i) :
    notConnComp G m' g = S := by
  have hnm : NoCrossing G m S := noCrossing_of_event G m S g hg hev
  have hnm' : NoCrossing G m' S := noCrossing_congr G m m' S hnm hagree
  have hsub := currentSubgraph_restrictCompl_congr G m m' S hagree
  rw [← hev]
  ext v
  rw [mem_notConnComp, mem_notConnComp]
  by_cases hv : v ∈ S
  · constructor <;> intro _
    · exact not_currentConnected_in_S G m S hnm g hg v (hev ▸ hv)
    · exact not_currentConnected_in_S G m' S hnm' g hg v (hev ▸ hv)
  · rw [currentConnected_iff_compl G m' S hnm' g v hg,
      currentConnected_iff_compl G m S hnm g v hg]
    unfold CurrentConnected
    rw [hsub]















theorem claim2_ising (β : ℝ) (J : Sym2 V → ℝ) (S : Finset V) (g : V) (hg : g ∉ S)
    (zero x : V) (h0 : zero ∈ S) (hx : x ∈ S)
    (hZ : currentSum G β (couplingIn J S) ∅ ≠ 0) :
    (∑' pq : (↥G.edgeFinset → ℕ) × (↥G.edgeFinset → ℕ),
        (if sources G (ofEdgeFun G pq.1) = {zero, x} then weight G β J (ofEdgeFun G pq.1) else 0)
          * (if sources G (ofEdgeFun G pq.2) = ∅ then weight G β J (ofEdgeFun G pq.2) else 0)
          * (if notConnComp G (fun e => ofEdgeFun G pq.1 e + ofEdgeFun G pq.2 e) g = S
              then 1 else 0))
    = expectationJ G β (couplingIn J S) {zero, x}
      * (∑' pq : (↥G.edgeFinset → ℕ) × (↥G.edgeFinset → ℕ),
          (if sources G (ofEdgeFun G pq.1) = ∅ then weight G β J (ofEdgeFun G pq.1) else 0)
            * (if sources G (ofEdgeFun G pq.2) = ∅ then weight G β J (ofEdgeFun G pq.2) else 0)
            * (if notConnComp G (fun e => ofEdgeFun G pq.1 e + ofEdgeFun G pq.2 e) g = S
                then 1 else 0)) := by
  classical
  exact claim2_abstract G β J S (fun m => notConnComp G m g = S)
    (fun m hm => noCrossing_of_event G m S g hg hm)
    (fun m m' hagree => ⟨fun hm => notConnComp_congr G m m' S g hg hm hagree,
      fun hm' => notConnComp_congr G m' m S g hg hm' (fun i hi hni => (hagree i hi hni).symm)⟩)
    zero x h0 hx hZ

end Sharpness

end StatMech

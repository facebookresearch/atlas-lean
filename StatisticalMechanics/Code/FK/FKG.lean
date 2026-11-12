/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/































import Code.FK.RandomCluster
import Code.Inequalities.FKG

open scoped BigOperators
open SimpleGraph Finset




set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

namespace StatMech

namespace FK

variable {V : Type*} [Fintype V] [DecidableEq V]








omit [Fintype V] in




theorem reachable_sup_edge_iff {G : SimpleGraph V} (x y a b : V) :
    (G ⊔ edge x y).Reachable a b ↔
      G.Reachable a b ∨ (G.Reachable a x ∧ G.Reachable y b)
        ∨ (G.Reachable a y ∧ G.Reachable x b) := by
  constructor
  · rintro ⟨w⟩
    induction w with
    | nil => exact Or.inl (Reachable.refl _)
    | @cons u v c h p ih =>
      rcases (SimpleGraph.sup_adj _ _ _ _).mp h with hG | he
      · have hr : G.Reachable u v := hG.reachable
        rcases ih with h1 | ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact Or.inl (hr.trans h1)
        · exact Or.inr (Or.inl ⟨hr.trans h1, h2⟩)
        · exact Or.inr (Or.inr ⟨hr.trans h1, h2⟩)
      · rcases ((edge_adj x y u v).mp he).1 with ⟨hu, hv⟩ | ⟨hu, hv⟩
        · subst hu; subst hv
          rcases ih with h1 | ⟨h1, h2⟩ | ⟨h1, h2⟩
          · exact Or.inr (Or.inl ⟨Reachable.refl _, h1⟩)
          · exact Or.inl (h1.symm.trans h2)
          · exact Or.inl h2
        · subst hu; subst hv
          rcases ih with h1 | ⟨h1, h2⟩ | ⟨h1, h2⟩
          · exact Or.inr (Or.inr ⟨Reachable.refl _, h1⟩)
          · exact Or.inl h2
          · exact Or.inl (h1.symm.trans h2)
  · have hGsubR : ∀ {s t : V}, G.Reachable s t → (G ⊔ edge x y).Reachable s t :=
      fun hr => hr.mono le_sup_left
    have hedge : (G ⊔ edge x y).Reachable x y := by
      by_cases hxy : x = y
      · subst hxy; exact Reachable.refl x
      · exact Adj.reachable (by
          rw [SimpleGraph.sup_adj]
          exact Or.inr ((edge_adj x y x y).mpr ⟨Or.inl ⟨rfl, rfl⟩, hxy⟩))
    rintro (h | ⟨h1, h2⟩ | ⟨h1, h2⟩)
    · exact hGsubR h
    · exact (hGsubR h1).trans (hedge.trans (hGsubR h2))
    · exact (hGsubR h1).trans (hedge.symm.trans (hGsubR h2))






theorem card_connectedComponent_le_sup_edge (G : SimpleGraph V) (x y : V) :
    Nat.card G.ConnectedComponent ≤ Nat.card (G ⊔ edge x y).ConnectedComponent + 1 := by
  classical
  set H := G ⊔ edge x y with hH
  let g : G.ConnectedComponent → H.ConnectedComponent :=
    fun c => c.lift (fun v => H.connectedComponentMk v)
      (fun v w p _hp => ConnectedComponent.sound (p.reachable.mono le_sup_left))
  have hg_mk : ∀ v, g (G.connectedComponentMk v) = H.connectedComponentMk v := fun _ => rfl
  let cy : G.ConnectedComponent := G.connectedComponentMk y
  let f : G.ConnectedComponent → H.ConnectedComponent ⊕ Unit :=
    fun c => if c = cy ∧ G.connectedComponentMk x ≠ cy then Sum.inr () else Sum.inl (g c)
  have hfinj : Function.Injective f := by
    intro c d hcd
    induction c using ConnectedComponent.ind with | h vc =>
    induction d using ConnectedComponent.ind with | h vd =>
    simp only [f] at hcd
    by_cases hcx : G.connectedComponentMk x = cy
    · simp only [hcx, ne_eq, not_true_eq_false, and_false, if_false] at hcd
      have hgg : g (G.connectedComponentMk vc) = g (G.connectedComponentMk vd) := Sum.inl.inj hcd
      rw [hg_mk, hg_mk] at hgg
      have hreach : H.Reachable vc vd := ConnectedComponent.exact hgg
      rw [hH, reachable_sup_edge_iff] at hreach
      rcases hreach with hr | ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact ConnectedComponent.sound hr
      · exact ConnectedComponent.sound (h1.trans ((ConnectedComponent.exact hcx).trans h2))
      · exact ConnectedComponent.sound (h1.trans ((ConnectedComponent.exact hcx).symm.trans h2))
    · have hxne : G.connectedComponentMk x ≠ cy := hcx
      simp only [hxne, ne_eq, not_false_eq_true, and_true] at hcd
      by_cases hvc : G.connectedComponentMk vc = cy <;>
        by_cases hvd : G.connectedComponentMk vd = cy
      · rw [hvc, hvd]
      · rw [if_pos hvc, if_neg hvd] at hcd; exact absurd hcd (by simp)
      · rw [if_neg hvc, if_pos hvd] at hcd; exact absurd hcd (by simp)
      · rw [if_neg hvc, if_neg hvd] at hcd
        have hgg : g (G.connectedComponentMk vc) = g (G.connectedComponentMk vd) := Sum.inl.inj hcd
        rw [hg_mk, hg_mk] at hgg
        have hreach : H.Reachable vc vd := ConnectedComponent.exact hgg
        rw [hH, reachable_sup_edge_iff] at hreach
        rcases hreach with hr | ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact ConnectedComponent.sound hr
        · exact absurd (ConnectedComponent.sound h2.symm) hvd
        · exact absurd (ConnectedComponent.sound h1) hvc
  calc Nat.card G.ConnectedComponent
      ≤ Nat.card (H.ConnectedComponent ⊕ Unit) := Nat.card_le_card_of_injective f hfinj
    _ = Nat.card H.ConnectedComponent + 1 := by rw [Nat.card_sum]; simp

omit [Fintype V] [DecidableEq V] in


theorem card_connectedComponent_sup_edge_le [Finite V] (G : SimpleGraph V) (x y : V) :
    Nat.card (G ⊔ edge x y).ConnectedComponent ≤ Nat.card G.ConnectedComponent :=
  ConnectedComponent.card_le_card_of_le le_sup_left

omit [Fintype V] in



theorem card_connectedComponent_sup_edge_of_reachable {G : SimpleGraph V} {x y : V}
    (hxy : G.Reachable x y) :
    Nat.card (G ⊔ edge x y).ConnectedComponent = Nat.card G.ConnectedComponent := by
  classical
  have hreq : (G ⊔ edge x y).Reachable = G.Reachable := by
    funext a b
    apply propext
    rw [reachable_sup_edge_iff]
    constructor
    · rintro (h | ⟨h1, h2⟩ | ⟨h1, h2⟩)
      · exact h
      · exact h1.trans (hxy.trans h2)
      · exact h1.trans (hxy.symm.trans h2)
    · exact Or.inl
  apply Nat.card_eq_of_bijective
    (fun c => c.lift (fun v => G.connectedComponentMk v) (fun v w p _hp =>
      ConnectedComponent.sound (by rw [← hreq]; exact p.reachable)))
  refine ⟨?_, ?_⟩
  · intro c d hcd
    induction c using ConnectedComponent.ind with | h vc =>
    induction d using ConnectedComponent.ind with | h vd =>
    simp only [ConnectedComponent.lift_mk] at hcd
    have : G.Reachable vc vd := ConnectedComponent.exact hcd
    rw [← hreq] at this
    exact ConnectedComponent.sound this
  · intro c
    induction c using ConnectedComponent.ind with | h v =>
    exact ⟨(G ⊔ edge x y).connectedComponentMk v, rfl⟩

omit [Fintype V] in



theorem card_connectedComponent_sup_edge_lt [Finite V] {G : SimpleGraph V} {x y : V}
    (hxy : ¬ G.Reachable x y) :
    Nat.card (G ⊔ edge x y).ConnectedComponent < Nat.card G.ConnectedComponent := by
  classical
  set H := G ⊔ edge x y with hH
  let g : G.ConnectedComponent → H.ConnectedComponent :=
    fun c => c.lift (fun v => H.connectedComponentMk v)
      (fun v w p _hp => ConnectedComponent.sound (p.reachable.mono le_sup_left))
  have hg_mk : ∀ v, g (G.connectedComponentMk v) = H.connectedComponentMk v := fun _ => rfl
  have hsurj : Function.Surjective g := by
    intro c
    induction c using ConnectedComponent.ind with | h v =>
    exact ⟨G.connectedComponentMk v, rfl⟩
  have hxy_ne : G.connectedComponentMk x ≠ G.connectedComponentMk y := by
    rw [ne_eq, ConnectedComponent.eq]; exact hxy
  have hgeq : g (G.connectedComponentMk x) = g (G.connectedComponentMk y) := by
    rw [hg_mk, hg_mk]
    apply ConnectedComponent.sound
    rw [hH, reachable_sup_edge_iff]
    exact Or.inr (Or.inl ⟨Reachable.refl x, Reachable.refl y⟩)
  have hnotinj : ¬ Function.Injective g := fun hinj => hxy_ne (hinj hgeq)
  by_contra hle
  rw [not_lt] at hle
  have hcard_le : Nat.card H.ConnectedComponent ≤ Nat.card G.ConnectedComponent :=
    Nat.card_le_card_of_surjective g hsurj
  have heq : Nat.card H.ConnectedComponent = Nat.card G.ConnectedComponent :=
    le_antisymm hcard_le hle
  have hbij : Function.Bijective g :=
    (Nat.bijective_iff_surjective_and_card g).mpr ⟨hsurj, heq.symm⟩
  exact hnotinj hbij.1





theorem card_connectedComponent_marginal_edge [Finite V] {A B : SimpleGraph V}
    (hAB : A ≤ B) (x y : V) :
    Nat.card (A ⊔ edge x y).ConnectedComponent + Nat.card B.ConnectedComponent
      ≤ Nat.card A.ConnectedComponent + Nat.card (B ⊔ edge x y).ConnectedComponent := by
  by_cases hBr : B.Reachable x y
  · rw [card_connectedComponent_sup_edge_of_reachable hBr]
    have := card_connectedComponent_sup_edge_le A x y
    omega
  · have hAr : ¬ A.Reachable x y := fun h => hBr (h.mono hAB)
    have hAdrop := card_connectedComponent_sup_edge_lt hAr
    have hAlow := card_connectedComponent_le_sup_edge A x y
    have hBlow := card_connectedComponent_le_sup_edge B x y
    omega




theorem card_connectedComponent_marginal_finset [Finite V] (S : Finset (Sym2 V)) :
    ∀ (A B : SimpleGraph V), A ≤ B →
      Nat.card (A ⊔ fromEdgeSet (↑S)).ConnectedComponent + Nat.card B.ConnectedComponent
        ≤ Nat.card A.ConnectedComponent
            + Nat.card (B ⊔ fromEdgeSet (↑S)).ConnectedComponent := by
  classical
  induction S using Finset.induction with
  | empty =>
    intro A B _hAB
    simp only [Finset.coe_empty, fromEdgeSet_empty, sup_bot_eq, le_refl]
  | insert e S _he ih =>
    intro A B hAB
    have key : ∀ G : SimpleGraph V,
        G ⊔ fromEdgeSet (↑(insert e S)) = (G ⊔ fromEdgeSet (↑S)) ⊔ fromEdgeSet {e} := by
      intro G
      rw [Finset.coe_insert, Set.insert_eq, fromEdgeSet_union, sup_comm (fromEdgeSet {e}),
        ← sup_assoc]
    rw [key A, key B]
    obtain ⟨x, y, hxy⟩ : ∃ x y : V, fromEdgeSet ({e} : Set (Sym2 V)) = edge x y := by
      induction e using Sym2.ind with | _ x y => exact ⟨x, y, by rw [edge]⟩
    rw [hxy]
    have hA'B' : A ⊔ fromEdgeSet (↑S) ≤ B ⊔ fromEdgeSet (↑S) := sup_le_sup_right hAB _
    have hm := card_connectedComponent_marginal_edge hA'B' x y
    have hih := ih A B hAB
    omega




theorem card_connectedComponent_marginal {A B : SimpleGraph V} (hAB : A ≤ B)
    (K : SimpleGraph V) [DecidableRel K.Adj] :
    Nat.card (A ⊔ K).ConnectedComponent + Nat.card B.ConnectedComponent
      ≤ Nat.card A.ConnectedComponent + Nat.card (B ⊔ K).ConnectedComponent := by
  classical
  have hK : fromEdgeSet (↑K.edgeFinset) = K := by rw [coe_edgeFinset, fromEdgeSet_edgeSet]
  have h := card_connectedComponent_marginal_finset K.edgeFinset A B hAB
  rw [hK] at h
  exact h





theorem card_connectedComponent_submodular (G₁ G₂ : SimpleGraph V)
    [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] :
    Nat.card G₁.ConnectedComponent + Nat.card G₂.ConnectedComponent
      ≤ Nat.card (G₁ ⊔ G₂).ConnectedComponent + Nat.card (G₁ ⊓ G₂).ConnectedComponent := by
  have h := card_connectedComponent_marginal (inf_le_right (a := G₁) (b := G₂)) G₁
  rw [show (G₁ ⊓ G₂) ⊔ G₁ = G₁ by rw [sup_comm, sup_inf_self]] at h
  rw [show G₂ ⊔ G₁ = G₁ ⊔ G₂ by rw [sup_comm]] at h
  omega



variable (G : SimpleGraph V) [DecidableRel G.Adj]

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in


theorem openSub_sup (a b : ConfigSpace (Sym2 V)) :
    openSub G (a ⊔ b) = openSub G a ⊔ openSub G b := by
  ext x y
  simp only [openSub_adj, SimpleGraph.sup_adj]
  change (G.Adj x y ∧ (a s(x, y) || b s(x, y)) = true) ↔ _
  rw [Bool.or_eq_true]
  tauto

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in


theorem openSub_inf (a b : ConfigSpace (Sym2 V)) :
    openSub G (a ⊓ b) = openSub G a ⊓ openSub G b := by
  ext x y
  simp only [openSub_adj, SimpleGraph.inf_adj]
  change (G.Adj x y ∧ (a s(x, y) && b s(x, y)) = true) ↔ _
  rw [Bool.and_eq_true]
  tauto





theorem numClusters_supermodular (a b : ConfigSpace (Sym2 V)) :
    numClusters G a + numClusters G b
      ≤ numClusters G (a ⊔ b) + numClusters G (a ⊓ b) := by
  classical
  have h := card_connectedComponent_submodular (openSub G a) (openSub G b)
  rw [← openSub_sup G a b, ← openSub_inf G a b] at h
  simpa only [numClusters, Nat.card_eq_fintype_card] using h



omit [DecidableEq V] in




theorem edgeProduct_logModular (p : ℝ) (a b : ConfigSpace (Sym2 V)) :
    edgeProduct G p a * edgeProduct G p b
      = edgeProduct G p (a ⊔ b) * edgeProduct G p (a ⊓ b) := by
  unfold edgeProduct
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl (fun e _ => ?_)
  have hcoord : ∀ x y : Bool,
      (if x then p else 1 - p) * (if y then p else 1 - p)
        = (if (x || y) then p else 1 - p) * (if (x && y) then p else 1 - p) := by
    intro x y
    cases x <;> cases y <;>
      simp only [Bool.or_self, Bool.or_false, Bool.or_true, Bool.and_self, Bool.and_false,
        Bool.and_true, if_true, mul_comm]
  have hsup : (a ⊔ b) e = (a e || b e) := rfl
  have hinf : (a ⊓ b) e = (a e && b e) := rfl
  rw [hsup, hinf]
  exact hcoord (a e) (b e)





theorem fkWeight_logSupermodular {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    (a b : ConfigSpace (Sym2 V)) :
    fkWeight G p q a * fkWeight G p q b
      ≤ fkWeight G p q (a ⊔ b) * fkWeight G p q (a ⊓ b) := by
  
  have hcluster :
      q ^ numClusters G a * q ^ numClusters G b
        ≤ q ^ numClusters G (a ⊔ b) * q ^ numClusters G (a ⊓ b) := by
    rw [← pow_add, ← pow_add]
    exact pow_le_pow_right₀ hq (numClusters_supermodular G a b)
  
  have hedge := edgeProduct_logModular G p a b
  
  have hea := (edgeProduct_pos G hp hp1 a).le
  have heb := (edgeProduct_pos G hp hp1 b).le
  have hq0 : (0 : ℝ) ≤ q := le_trans zero_le_one hq
  have hpowa : (0 : ℝ) ≤ q ^ numClusters G a := pow_nonneg hq0 _
  have hpowb : (0 : ℝ) ≤ q ^ numClusters G b := pow_nonneg hq0 _
  
  have hLHS : fkWeight G p q a * fkWeight G p q b
      = (edgeProduct G p a * edgeProduct G p b)
          * (q ^ numClusters G a * q ^ numClusters G b) := by
    unfold fkWeight; ring
  have hRHS : fkWeight G p q (a ⊔ b) * fkWeight G p q (a ⊓ b)
      = (edgeProduct G p (a ⊔ b) * edgeProduct G p (a ⊓ b))
          * (q ^ numClusters G (a ⊔ b) * q ^ numClusters G (a ⊓ b)) := by
    unfold fkWeight; ring
  rw [hLHS, hRHS, hedge]
  
  have hprod_nonneg : (0 : ℝ) ≤ edgeProduct G p (a ⊔ b) * edgeProduct G p (a ⊓ b) :=
    mul_nonneg (edgeProduct_pos G hp hp1 _).le (edgeProduct_pos G hp hp1 _).le
  exact mul_le_mul_of_nonneg_left hcluster hprod_nonneg






theorem fkProb_FKGLatticeCondition {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q) :
    FKGLatticeCondition (fun ω => fkProb G p q ω) := by
  have hq0 : 0 < q := lt_of_lt_of_le zero_lt_one hq
  have hZpos : 0 < fkZ G p q := fkZ_pos G hp hp1 hq0
  intro a b
  simp only [fkProb]
  rw [div_mul_div_comm, div_mul_div_comm]
  exact (div_le_div_iff_of_pos_right (mul_pos hZpos hZpos)).mpr
    (fkWeight_logSupermodular G hp hp1 hq a b)





theorem fkProb_positively_associated {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    {f g : ConfigSpace (Sym2 V) → ℝ} (hf : Monotone f) (hg : Monotone g) :
    (∑ ω, fkProb G p q ω * f ω) * (∑ ω, fkProb G p q ω * g ω)
      ≤ ∑ ω, fkProb G p q ω * (f ω * g ω) := by
  have hq0 : 0 < q := lt_of_lt_of_le zero_lt_one hq
  exact fkg_inequality
    (fun ω => fkProb_nonneg G hp hp1 hq0 ω)
    (fkProb_sum_eq_one G hp hp1 hq0)
    (fkProb_FKGLatticeCondition G hp hp1 hq) hf hg




theorem fkProb_positively_associated_events {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    {A B : Set (ConfigSpace (Sym2 V))} (hA : IsIncreasing A) (hB : IsIncreasing B) :
    (∑ ω, fkProb G p q ω * A.indicator (fun _ => (1 : ℝ)) ω)
        * (∑ ω, fkProb G p q ω * B.indicator (fun _ => (1 : ℝ)) ω)
      ≤ ∑ ω, fkProb G p q ω * (A ∩ B).indicator (fun _ => (1 : ℝ)) ω := by
  have hq0 : 0 < q := lt_of_lt_of_le zero_lt_one hq
  exact fkg_inequality_events
    (fun ω => fkProb_nonneg G hp hp1 hq0 ω)
    (fkProb_sum_eq_one G hp hp1 hq0)
    (fkProb_FKGLatticeCondition G hp hp1 hq) hA hB

end FK

end StatMech

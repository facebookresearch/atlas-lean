/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/















































































import Mathlib
import Code.FK.RandomCluster
import Code.FK.Tilt
import Code.FK.FeketeLimit

open scoped BigOperators
open SimpleGraph Filter Topology

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

namespace StatMech

namespace FK







section Reach
variable {V W : Type*} (G : SimpleGraph V) (H : SimpleGraph W)


theorem fsm_reach_inl_inl (a b : V) :
    (G ⊕g H).Reachable (Sum.inl a) (Sum.inl b) ↔ G.Reachable a b := by
  constructor
  · intro h
    rw [reachable_eq_reflTransGen] at h ⊢
    have key : ∀ x, Relation.ReflTransGen (G ⊕g H).Adj (Sum.inl a) x →
        ∃ a', x = Sum.inl a' ∧ Relation.ReflTransGen G.Adj a a' := by
      intro x hx
      induction hx with
      | refl => exact ⟨a, rfl, Relation.ReflTransGen.refl⟩
      | @tail y z hprev hadj ih =>
        obtain ⟨a', rfl, hra'⟩ := ih
        match z, hadj with
        | Sum.inl c', hadj => exact ⟨c', rfl, hra'.tail (by simpa using hadj)⟩
        | Sum.inr c', hadj => simp at hadj
    obtain ⟨a', haeq, hra'⟩ := key (Sum.inl b) h
    cases haeq; exact hra'
  · rintro ⟨p⟩; exact ⟨p.map Embedding.sumInl.toHom⟩


theorem fsm_reach_inr_inr (a b : W) :
    (G ⊕g H).Reachable (Sum.inr a) (Sum.inr b) ↔ H.Reachable a b := by
  constructor
  · intro h
    rw [reachable_eq_reflTransGen] at h ⊢
    have key : ∀ x, Relation.ReflTransGen (G ⊕g H).Adj (Sum.inr a) x →
        ∃ a', x = Sum.inr a' ∧ Relation.ReflTransGen H.Adj a a' := by
      intro x hx
      induction hx with
      | refl => exact ⟨a, rfl, Relation.ReflTransGen.refl⟩
      | @tail y z hprev hadj ih =>
        obtain ⟨a', rfl, hra'⟩ := ih
        match z, hadj with
        | Sum.inr c', hadj => exact ⟨c', rfl, hra'.tail (by simpa using hadj)⟩
        | Sum.inl c', hadj => simp at hadj
    obtain ⟨a', haeq, hra'⟩ := key (Sum.inr b) h
    cases haeq; exact hra'
  · rintro ⟨p⟩; exact ⟨p.map Embedding.sumInr.toHom⟩


theorem fsm_not_reach_inl_inr (a : V) (b : W) :
    ¬ (G ⊕g H).Reachable (Sum.inl a) (Sum.inr b) := by
  intro h
  rw [reachable_eq_reflTransGen] at h
  have key : ∀ x, Relation.ReflTransGen (G ⊕g H).Adj (Sum.inl a) x → ∃ a', x = Sum.inl a' := by
    intro x hx
    induction hx with
    | refl => exact ⟨a, rfl⟩
    | @tail y z hprev hadj ih =>
      obtain ⟨a', rfl⟩ := ih
      match z, hadj with
      | Sum.inl c', hadj => exact ⟨c', rfl⟩
      | Sum.inr c', hadj => simp at hadj
  obtain ⟨a', haeq⟩ := key (Sum.inr b) h
  exact Sum.inr_ne_inl haeq

end Reach





section CC
variable {V W : Type*} (G : SimpleGraph V) (H : SimpleGraph W)



noncomputable def fsm_ccToSum :
    (G ⊕g H).ConnectedComponent → G.ConnectedComponent ⊕ H.ConnectedComponent :=
  Quot.lift
    (fun x => Sum.elim (fun a => Sum.inl (G.connectedComponentMk a))
                       (fun b => Sum.inr (H.connectedComponentMk b)) x)
    (by
      intro x y hxy
      match x, y, hxy with
      | Sum.inl a, Sum.inl b, hxy =>
        simp only [Sum.elim_inl]; congr 1
        exact ConnectedComponent.sound ((fsm_reach_inl_inl G H a b).mp hxy)
      | Sum.inr a, Sum.inr b, hxy =>
        simp only [Sum.elim_inr]; congr 1
        exact ConnectedComponent.sound ((fsm_reach_inr_inr G H a b).mp hxy)
      | Sum.inl a, Sum.inr b, hxy => exact absurd hxy (fsm_not_reach_inl_inr G H a b)
      | Sum.inr a, Sum.inl b, hxy => exact absurd hxy.symm (fsm_not_reach_inl_inr G H b a))



noncomputable def fsm_sumToCC :
    G.ConnectedComponent ⊕ H.ConnectedComponent → (G ⊕g H).ConnectedComponent :=
  Sum.elim (ConnectedComponent.map Embedding.sumInl.toHom)
           (ConnectedComponent.map Embedding.sumInr.toHom)


noncomputable def fsm_ccSumEquiv :
    (G ⊕g H).ConnectedComponent ≃ G.ConnectedComponent ⊕ H.ConnectedComponent where
  toFun := fsm_ccToSum G H
  invFun := fsm_sumToCC G H
  left_inv := by
    refine ConnectedComponent.ind ?_; rintro (a | b) <;> rfl
  right_inv := by
    rintro (c | c)
    · induction c using ConnectedComponent.ind with | _ a => rfl
    · induction c using ConnectedComponent.ind with | _ b => rfl

end CC






instance fsm_instDecidableSumAdj {V W : Type*} (G : SimpleGraph V) (H : SimpleGraph W)
    [DecidableRel G.Adj] [DecidableRel H.Adj] : DecidableRel (G ⊕g H).Adj := by
  intro x y
  match x, y with
  | Sum.inl a, Sum.inl b => exact (by simpa using inferInstanceAs (Decidable (G.Adj a b)))
  | Sum.inr c, Sum.inr d => exact (by simpa using inferInstanceAs (Decidable (H.Adj c d)))
  | Sum.inl a, Sum.inr d => exact (by simp; infer_instance)
  | Sum.inr c, Sum.inl b => exact (by simp; infer_instance)



section Edges
variable {V W : Type*} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]
  (G : SimpleGraph V) (H : SimpleGraph W) [DecidableRel G.Adj] [DecidableRel H.Adj]


theorem fsm_edgeSet_sum :
    (G ⊕g H).edgeSet =
      (Sym2.map Sum.inl '' G.edgeSet) ∪ (Sym2.map Sum.inr '' H.edgeSet) := by
  ext e
  induction e using Sym2.ind with
  | _ x y =>
    simp only [mem_edgeSet, Set.mem_union, Set.mem_image]
    match x, y with
    | Sum.inl a, Sum.inl b =>
      constructor
      · intro h
        exact Or.inl ⟨s(a,b), by simpa [mem_edgeSet] using h, by simp⟩
      · rintro (⟨z, hz, hmap⟩ | ⟨z, hz, hmap⟩)
        · induction z using Sym2.ind with
          | _ c d =>
            simp only [Sym2.map_mk] at hmap
            rw [mem_edgeSet] at hz
            rw [Sym2.eq_iff] at hmap
            rcases hmap with ⟨hc, hd⟩ | ⟨hc, hd⟩
            · cases hc; cases hd; simpa [mem_edgeSet] using hz
            · cases hc; cases hd; simpa [SimpleGraph.sum_adj] using hz.symm
        · exfalso
          induction z using Sym2.ind with
          | _ c d => simp only [Sym2.map_mk, Sym2.eq_iff] at hmap; tauto
    | Sum.inr a, Sum.inr b =>
      constructor
      · intro h
        exact Or.inr ⟨s(a,b), by simpa [mem_edgeSet] using h, by simp⟩
      · rintro (⟨z, hz, hmap⟩ | ⟨z, hz, hmap⟩)
        · exfalso
          induction z using Sym2.ind with
          | _ c d => simp only [Sym2.map_mk, Sym2.eq_iff] at hmap; tauto
        · induction z using Sym2.ind with
          | _ c d =>
            simp only [Sym2.map_mk] at hmap
            rw [mem_edgeSet] at hz
            rw [Sym2.eq_iff] at hmap
            rcases hmap with ⟨hc, hd⟩ | ⟨hc, hd⟩
            · cases hc; cases hd; simpa [mem_edgeSet] using hz
            · cases hc; cases hd; simpa [SimpleGraph.sum_adj] using hz.symm
    | Sum.inl a, Sum.inr b =>
      simp only [SimpleGraph.sum_adj]
      constructor
      · intro h; exact absurd h (by simp)
      · rintro (⟨z, hz, hmap⟩ | ⟨z, hz, hmap⟩) <;>
          (induction z using Sym2.ind with
           | _ c d => simp only [Sym2.map_mk, Sym2.eq_iff] at hmap; tauto)
    | Sum.inr a, Sum.inl b =>
      simp only [SimpleGraph.sum_adj]
      constructor
      · intro h; exact absurd h (by simp)
      · rintro (⟨z, hz, hmap⟩ | ⟨z, hz, hmap⟩) <;>
          (induction z using Sym2.ind with
           | _ c d => simp only [Sym2.map_mk, Sym2.eq_iff] at hmap; tauto)


theorem fsm_edgeFinset_sum :
    (G ⊕g H).edgeFinset =
      (G.edgeFinset.image (Sym2.map Sum.inl)) ∪ (H.edgeFinset.image (Sym2.map Sum.inr)) := by
  ext e
  simp only [mem_edgeFinset, Finset.mem_union, Finset.mem_image, mem_edgeFinset]
  have he : e ∈ (G ⊕g H).edgeSet ↔
      (∃ z ∈ G.edgeSet, Sym2.map Sum.inl z = e) ∨ (∃ z ∈ H.edgeSet, Sym2.map Sum.inr z = e) := by
    rw [fsm_edgeSet_sum]; simp [Set.mem_image]
  rw [he]

theorem fsm_map_inl_injective : Function.Injective (Sym2.map (Sum.inl : V → V ⊕ W)) :=
  Sym2.map.injective Sum.inl_injective

theorem fsm_map_inr_injective : Function.Injective (Sym2.map (Sum.inr : W → V ⊕ W)) :=
  Sym2.map.injective Sum.inr_injective


theorem fsm_images_disjoint :
    Disjoint (G.edgeFinset.image (Sym2.map (Sum.inl : V → V ⊕ W)))
             (H.edgeFinset.image (Sym2.map (Sum.inr : W → V ⊕ W))) := by
  rw [Finset.disjoint_left]
  rintro e he1 he2
  rw [Finset.mem_image] at he1 he2
  obtain ⟨z1, _, rfl⟩ := he1
  obtain ⟨z2, _, hz2⟩ := he2
  induction z1 using Sym2.ind with
  | _ a b =>
    induction z2 using Sym2.ind with
    | _ c d => simp only [Sym2.map_mk, Sym2.eq_iff] at hz2; tauto

end Edges



section Combine
variable {V W : Type*}




noncomputable def fsm_combine (σ : Sym2 V → Bool) (τ : Sym2 W → Bool) :
    Sym2 (V ⊕ W) → Bool :=
  Sym2.lift ⟨fun x y =>
    match x, y with
    | Sum.inl a, Sum.inl b => σ s(a, b)
    | Sum.inr c, Sum.inr d => τ s(c, d)
    | _, _ => false,
    by
      intro x y
      match x, y with
      | Sum.inl a, Sum.inl b => simp [Sym2.eq_swap]
      | Sum.inr c, Sum.inr d => simp [Sym2.eq_swap]
      | Sum.inl a, Sum.inr d => rfl
      | Sum.inr c, Sum.inl b => rfl⟩

@[simp] theorem fsm_combine_inl (σ : Sym2 V → Bool) (τ : Sym2 W → Bool) (a b : V) :
    fsm_combine σ τ s(Sum.inl a, Sum.inl b) = σ s(a, b) := rfl

@[simp] theorem fsm_combine_inr (σ : Sym2 V → Bool) (τ : Sym2 W → Bool) (a b : W) :
    fsm_combine σ τ s(Sum.inr a, Sum.inr b) = τ s(a, b) := rfl

theorem fsm_combine_map_inl (σ : Sym2 V → Bool) (τ : Sym2 W → Bool) (e : Sym2 V) :
    fsm_combine σ τ (Sym2.map Sum.inl e) = σ e := by
  induction e using Sym2.ind with | _ a b => simp [Sym2.map_mk]

theorem fsm_combine_map_inr (σ : Sym2 V → Bool) (τ : Sym2 W → Bool) (e : Sym2 W) :
    fsm_combine σ τ (Sym2.map Sum.inr e) = τ e := by
  induction e using Sym2.ind with | _ a b => simp [Sym2.map_mk]



theorem fsm_combine_injective :
    Function.Injective fun p : (Sym2 V → Bool) × (Sym2 W → Bool) => fsm_combine p.1 p.2 := by
  rintro ⟨σ₁, τ₁⟩ ⟨σ₂, τ₂⟩ h
  simp only at h
  ext1
  · funext e; show σ₁ e = σ₂ e
    rw [← fsm_combine_map_inl σ₁ τ₁ e, ← fsm_combine_map_inl σ₂ τ₂ e, h]
  · funext e; show τ₁ e = τ₂ e
    rw [← fsm_combine_map_inr σ₁ τ₁ e, ← fsm_combine_map_inr σ₂ τ₂ e, h]

end Combine



section Weight
variable {V W : Type*} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]
  (G : SimpleGraph V) (H : SimpleGraph W) [DecidableRel G.Adj] [DecidableRel H.Adj]


theorem fsm_edgeProduct_combine (p : ℝ) (σ : Sym2 V → Bool) (τ : Sym2 W → Bool) :
    edgeProduct (G ⊕g H) p (fsm_combine σ τ) = edgeProduct G p σ * edgeProduct H p τ := by
  unfold edgeProduct
  rw [fsm_edgeFinset_sum, Finset.prod_union (fsm_images_disjoint G H)]
  congr 1
  · rw [Finset.prod_image (fun x _ y _ h => fsm_map_inl_injective h)]
    exact Finset.prod_congr rfl fun e _ => by rw [fsm_combine_map_inl]
  · rw [Finset.prod_image (fun x _ y _ h => fsm_map_inr_injective h)]
    exact Finset.prod_congr rfl fun e _ => by rw [fsm_combine_map_inr]



theorem fsm_openSub_combine (σ : Sym2 V → Bool) (τ : Sym2 W → Bool) :
    openSub (G ⊕g H) (fsm_combine σ τ) = (openSub G σ) ⊕g (openSub H τ) := by
  ext x y
  match x, y with
  | Sum.inl a, Sum.inl b => simp only [openSub_adj, SimpleGraph.sum_adj, fsm_combine_inl]
  | Sum.inr c, Sum.inr d => simp only [openSub_adj, SimpleGraph.sum_adj, fsm_combine_inr]
  | Sum.inl a, Sum.inr d => simp [openSub_adj, SimpleGraph.sum_adj]
  | Sum.inr c, Sum.inl b => simp [openSub_adj, SimpleGraph.sum_adj]


theorem fsm_numClusters_combine (σ : Sym2 V → Bool) (τ : Sym2 W → Bool) :
    numClusters (G ⊕g H) (fsm_combine σ τ)
      = numClusters G σ + numClusters H τ := by
  classical
  unfold numClusters
  
  rw [Nat.card_eq_fintype_card.symm, Nat.card_eq_fintype_card.symm, Nat.card_eq_fintype_card.symm]
  rw [show (openSub (G ⊕g H) (fsm_combine σ τ)) = (openSub G σ) ⊕g (openSub H τ) from
        fsm_openSub_combine G H σ τ]
  rw [Nat.card_congr (fsm_ccSumEquiv (openSub G σ) (openSub H τ)), Nat.card_sum]


theorem fsm_fkWeight_combine (p q : ℝ) (σ : Sym2 V → Bool) (τ : Sym2 W → Bool) :
    fkWeight (G ⊕g H) p q (fsm_combine σ τ) = fkWeight G p q σ * fkWeight H p q τ := by
  unfold fkWeight
  rw [fsm_edgeProduct_combine G H p σ τ, fsm_numClusters_combine G H σ τ, pow_add]
  ring

end Weight



section Super
variable {V W : Type*} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]
  (G : SimpleGraph V) (H : SimpleGraph W) [DecidableRel G.Adj] [DecidableRel H.Adj]

















theorem fsm_fkZ_sum_ge {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) :
    fkZ G p q * fkZ H p q ≤ fkZ (G ⊕g H) p q := by
  classical
  
  have hprod : fkZ G p q * fkZ H p q
      = ∑ στ : (Sym2 V → Bool) × (Sym2 W → Bool),
          fkWeight (G ⊕g H) p q (fsm_combine στ.1 στ.2) := by
    unfold fkZ
    rw [Fintype.sum_mul_sum, Fintype.sum_prod_type]
    exact Finset.sum_congr rfl fun σ _ => Finset.sum_congr rfl fun τ _ =>
      (fsm_fkWeight_combine G H p q σ τ).symm
  rw [hprod]
  
  have himg : (∑ στ : (Sym2 V → Bool) × (Sym2 W → Bool),
          fkWeight (G ⊕g H) p q (fsm_combine στ.1 στ.2))
      = ∑ ω ∈ Finset.univ.image (fun στ : (Sym2 V → Bool) × (Sym2 W → Bool) =>
            fsm_combine στ.1 στ.2), fkWeight (G ⊕g H) p q ω := by
    rw [Finset.sum_image]
    intro a _ b _ h
    exact fsm_combine_injective h
  rw [himg]
  
  refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) ?_
  intro ω _ _
  exact fkWeight_nonneg (G ⊕g H) hp hp1 hq ω




theorem fsm_neglog_sum_le {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) :
    - Real.log (fkZ (G ⊕g H) p q)
      ≤ - Real.log (fkZ G p q) + - Real.log (fkZ H p q) := by
  have hZG : 0 < fkZ G p q := fkZ_pos G hp hp1 hq
  have hZH : 0 < fkZ H p q := fkZ_pos H hp hp1 hq
  have hge : fkZ G p q * fkZ H p q ≤ fkZ (G ⊕g H) p q := fsm_fkZ_sum_ge G H hp hp1 hq
  have hlog : Real.log (fkZ G p q) + Real.log (fkZ H p q)
      ≤ Real.log (fkZ (G ⊕g H) p q) := by
    rw [← Real.log_mul hZG.ne' hZH.ne']
    exact Real.log_le_log (mul_pos hZG hZH) hge
  linarith

end Super







section Iso
variable {V W : Type*} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]
  (G : SimpleGraph V) (H : SimpleGraph W) [DecidableRel G.Adj] [DecidableRel H.Adj]


def fsm_sym2Congr (φ : V ≃ W) : Sym2 V ≃ Sym2 W where
  toFun := Sym2.map φ
  invFun := Sym2.map φ.symm
  left_inv z := by induction z using Sym2.ind with | _ a b => simp [Sym2.map_mk]
  right_inv z := by induction z using Sym2.ind with | _ a b => simp [Sym2.map_mk]



noncomputable def fsm_openSubIso (φ : G ≃g H) (ω : Sym2 W → Bool) :
    openSub G (fun e => ω (Sym2.map φ.toEquiv e)) ≃g openSub H ω where
  toEquiv := φ.toEquiv
  map_rel_iff' := by
    intro a b
    simp only [openSub_adj, Sym2.map_mk]
    exact and_congr φ.map_rel_iff Iff.rfl


theorem fsm_numClusters_iso (φ : G ≃g H) (ω : Sym2 W → Bool) :
    numClusters G (fun e => ω (Sym2.map φ.toEquiv e)) = numClusters H ω := by
  unfold numClusters
  exact Fintype.card_congr (SimpleGraph.Iso.connectedComponentEquiv (fsm_openSubIso G H φ ω))


theorem fsm_edgeProduct_iso (φ : G ≃g H) (p : ℝ) (ω : Sym2 W → Bool) :
    edgeProduct G p (fun e => ω (Sym2.map φ.toEquiv e)) = edgeProduct H p ω := by
  classical
  unfold edgeProduct
  
  have himg : G.edgeFinset.image (Sym2.map φ.toEquiv) = H.edgeFinset := by
    ext e
    simp only [Finset.mem_image, mem_edgeFinset]
    constructor
    · rintro ⟨z, hz, rfl⟩
      induction z using Sym2.ind with
      | _ a b =>
        rw [mem_edgeSet] at hz
        rw [Sym2.map_mk, mem_edgeSet]; exact φ.map_rel_iff.mpr hz
    · intro he
      refine ⟨Sym2.map φ.toEquiv.symm e, ?_, ?_⟩
      · induction e using Sym2.ind with
        | _ a b =>
          rw [mem_edgeSet] at he
          rw [Sym2.map_mk, mem_edgeSet]
          have := φ.symm.map_rel_iff.mpr (show H.Adj a b from he)
          simpa using this
      · induction e using Sym2.ind with
        | _ a b =>
          simp only [Sym2.map_mk, Sym2.eq_iff]
          exact Or.inl ⟨RelIso.apply_symm_apply φ a, RelIso.apply_symm_apply φ b⟩
  calc ∏ e ∈ G.edgeFinset, (if ω (Sym2.map φ.toEquiv e) then p else 1 - p)
      = ∏ e ∈ G.edgeFinset.image (Sym2.map φ.toEquiv), (if ω e then p else 1 - p) := by
        rw [Finset.prod_image
          (fun x _ y _ h => Sym2.map.injective φ.toEquiv.injective h)]
    _ = ∏ e ∈ H.edgeFinset, (if ω e then p else 1 - p) := by rw [himg]


theorem fsm_fkZ_iso (φ : G ≃g H) (p q : ℝ) :
    fkZ G p q = fkZ H p q := by
  classical
  unfold fkZ
  
  refine Fintype.sum_equiv
    (Equiv.arrowCongr (fsm_sym2Congr φ.toEquiv) (Equiv.refl Bool))
    (fun ω => fkWeight G p q ω) (fun ω => fkWeight H p q ω) ?_
  intro ωV
  
  have hpb : (Equiv.arrowCongr (fsm_sym2Congr φ.toEquiv) (Equiv.refl Bool)) ωV
      = fun w => ωV (Sym2.map φ.symm.toEquiv w) := by
    funext w
    simp only [Equiv.arrowCongr_apply, Equiv.coe_refl, id_eq, Function.comp,
      fsm_sym2Congr, Equiv.coe_fn_symm_mk]
    rfl
  rw [hpb]
  show fkWeight G p q ωV = fkWeight H p q (fun w => ωV (Sym2.map φ.symm.toEquiv w))
  unfold fkWeight
  rw [fsm_edgeProduct_iso H G φ.symm p ωV, fsm_numClusters_iso H G φ.symm ωV]

end Iso








section Fekete
variable {V : ℕ → Type*} [∀ n, Fintype (V n)] [∀ n, DecidableEq (V n)]
  (Gn : ∀ n, SimpleGraph (V n)) [∀ n, DecidableRel (Gn n).Adj]














theorem fsm_subadditive_neglog_fkZ {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (hjux : ∀ m n, Gn (m + n) ≃g Gn m ⊕g Gn n) :
    Subadditive (fun n => - Real.log (fkZ (Gn n) p q)) := by
  intro m n
  simp only
  rw [fsm_fkZ_iso (Gn (m + n)) (Gn m ⊕g Gn n) (hjux m n) p q]
  exact fsm_neglog_sum_le (Gn m) (Gn n) hp hp1 hq






















theorem fsm_fekete_limit (q : ℝ) (hq : 0 < q)
    (hE : ∀ n, 0 < (Gn n).edgeFinset.card)
    (hjux : ∀ m n, Gn (m + n) ≃g Gn m ⊕g Gn n)
    (hbdd : ∀ t, BddBelow (Set.range fun n =>
      (- Real.log (fkZ (Gn n) (fsc_logistic t) q)) / n))
    (c : ℝ → ℝ) (hc : ∀ t, c t ≠ 0)
    (he : ∀ t, Tendsto (fun n => ((Gn n).edgeFinset.card : ℝ) / n) atTop (𝓝 (c t))) :
    ∃ g : ℝ → ℝ,
      (∀ t, Tendsto (fun n => ivp2_tiltFreeEnergy (Gn n) q t) atTop (𝓝 (g t)))
        ∧ ConvexOn ℝ Set.univ g := by
  have hsuper : ∀ t, Subadditive (fun n => - Real.log (fkZ (Gn n) (fsc_logistic t) q)) :=
    fun t => fsm_subadditive_neglog_fkZ Gn (fsc_logistic_pos t) (fsc_logistic_lt_one t) hq
      hjux
  exact fkl_fekete_limit Gn q hq hE hsuper hbdd c hc he

end Fekete











theorem fsm_juxtaposition_satisfiable (m n : ℕ) :
    Nonempty ((⊥ : SimpleGraph (Fin (m + n))) ≃g
      (⊥ : SimpleGraph (Fin m)) ⊕g (⊥ : SimpleGraph (Fin n))) := by
  refine ⟨⟨finSumFinEquiv.symm, ?_⟩⟩
  intro a b
  
  simp only [SimpleGraph.bot_adj]
  constructor
  · intro h
    
    match finSumFinEquiv.symm a, finSumFinEquiv.symm b, h with
    | Sum.inl _, Sum.inl _, h => simp only [SimpleGraph.sum_adj, SimpleGraph.bot_adj] at h
    | Sum.inr _, Sum.inr _, h => simp only [SimpleGraph.sum_adj, SimpleGraph.bot_adj] at h
    | Sum.inl _, Sum.inr _, h => simp only [SimpleGraph.sum_adj] at h
    | Sum.inr _, Sum.inl _, h => simp only [SimpleGraph.sum_adj] at h
  · intro h; exact h.elim

end FK

end StatMech

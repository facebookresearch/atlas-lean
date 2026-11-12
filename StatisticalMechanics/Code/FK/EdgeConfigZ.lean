/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
























































import Mathlib
import Code.FK.RandomCluster
import Code.FK.SuperMultiplicative
import Code.FK.FKInterfaceSubadd
import Code.FK.QuadrantPartition
import Code.FK.CenteredFreeEnergy
import Code.FK.BoxFeketePerVolume

open scoped BigOperators
open SimpleGraph Filter Topology Set

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.style.openClassical false
set_option linter.style.setOption false
set_option linter.style.longLine false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1000000

namespace StatMech

namespace FK

open StatMech.Lattice



section Weight
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

omit [DecidableEq V] in


theorem ecz_openSub_eq_of_edges (ω₁ ω₂ : ConfigSpace (Sym2 V))
    (h : ∀ e ∈ G.edgeFinset, ω₁ e = ω₂ e) :
    openSub G ω₁ = openSub G ω₂ := by
  apply SimpleGraph.ext; ext x y; simp only [openSub_adj]
  constructor
  · rintro ⟨hadj, hop⟩
    exact ⟨hadj, by rw [← h s(x,y) (by rw [mem_edgeFinset]; exact hadj)]; exact hop⟩
  · rintro ⟨hadj, hop⟩
    exact ⟨hadj, by rw [h s(x,y) (by rw [mem_edgeFinset]; exact hadj)]; exact hop⟩


theorem ecz_numClusters_eq_of_edges (ω₁ ω₂ : ConfigSpace (Sym2 V))
    (h : ∀ e ∈ G.edgeFinset, ω₁ e = ω₂ e) :
    numClusters G ω₁ = numClusters G ω₂ := by
  unfold numClusters
  exact Fintype.card_congr (by rw [ecz_openSub_eq_of_edges G ω₁ ω₂ h])



theorem ecz_fkWeight_eq_of_edges (p q : ℝ) (ω₁ ω₂ : ConfigSpace (Sym2 V))
    (h : ∀ e ∈ G.edgeFinset, ω₁ e = ω₂ e) :
    fkWeight G p q ω₁ = fkWeight G p q ω₂ := by
  unfold fkWeight
  rw [ecz_numClusters_eq_of_edges G ω₁ ω₂ h]
  congr 1
  unfold edgeProduct
  exact Finset.prod_congr rfl (fun e he => by rw [h e he])

end Weight



section EdgeZ
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]



def ecz_ClosedOff : Type _ :=
  {ω : ConfigSpace (Sym2 V) // ∀ e, e ∉ G.edgeFinset → ω e = false}

noncomputable instance ecz_instFintype : Fintype (ecz_ClosedOff G) := by
  unfold ecz_ClosedOff; infer_instance

instance ecz_instNonempty : Nonempty (ecz_ClosedOff G) :=
  ⟨⟨fun _ => false, fun _ _ => rfl⟩⟩




noncomputable def ecz_fkZEdge (p q : ℝ) : ℝ :=
  ∑ ω : ecz_ClosedOff G, fkWeight G p q ω.val



noncomputable def ecz_NE : ℕ :=
  (Finset.univ.filter (fun e : Sym2 V => e ∉ G.edgeFinset)).card

theorem ecz_NE_eq : ecz_NE G = Fintype.card (Sym2 V) - G.edgeFinset.card := by
  unfold ecz_NE
  rw [Finset.filter_not, Finset.card_univ_diff]
  congr 1
  rw [Finset.filter_mem_eq_inter, Finset.univ_inter]



theorem ecz_fkZEdge_pos {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) :
    0 < ecz_fkZEdge G p q :=
  Finset.sum_pos (fun ω _ => fkWeight_pos G hp hp1 hq ω.val) Finset.univ_nonempty

theorem ecz_fkZEdge_ne_zero {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) :
    ecz_fkZEdge G p q ≠ 0 :=
  (ecz_fkZEdge_pos G hp hp1 hq).ne'





theorem ecz_factorization (p q : ℝ) :
    fkZ G p q = 2 ^ ecz_NE G * ecz_fkZEdge G p q := by
  classical
  set P : Sym2 V → Prop := fun e => e ∈ G.edgeFinset with hP
  rw [fkZ, ← Equiv.sum_comp (Equiv.piEquivPiSubtypeProd P (fun _ => Bool)).symm
        (fun ω => fkWeight G p q ω), Fintype.sum_prod_type]
  rw [ecz_fkZEdge]
  have hcard : (Fintype.card ({e // ¬ P e} → Bool))
      = 2 ^ (Finset.univ.filter (fun e : Sym2 V => e ∉ G.edgeFinset)).card := by
    rw [Fintype.card_fun, Fintype.card_bool, Fintype.card_subtype]
  have key : ∀ η : ({e // P e} → Bool),
      (∑ ξ : ({e // ¬ P e} → Bool),
        fkWeight G p q ((Equiv.piEquivPiSubtypeProd P (fun _ => Bool)).symm (η, ξ)))
      = 2 ^ ecz_NE G
          * fkWeight G p q ((Equiv.piEquivPiSubtypeProd P (fun _ => Bool)).symm (η, fun _ => false)) := by
    intro η
    rw [Finset.sum_congr rfl (fun ξ _ => ?_)]
    · rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcard, ecz_NE]; push_cast; ring
    · apply ecz_fkWeight_eq_of_edges
      intro e he
      rw [Equiv.piEquivPiSubtypeProd_symm_apply, Equiv.piEquivPiSubtypeProd_symm_apply,
        dif_pos he, dif_pos he]
  rw [Finset.sum_congr rfl (fun η _ => key η), ← Finset.mul_sum]
  congr 1
  symm
  refine Finset.sum_nbij'
    (i := fun ω : ecz_ClosedOff G => (fun e : {e // P e} => ω.val e.val))
    (j := fun η : ({e // P e} → Bool) =>
      (⟨(Equiv.piEquivPiSubtypeProd P (fun _ => Bool)).symm (η, fun _ => false), by
        intro e he
        rw [Equiv.piEquivPiSubtypeProd_symm_apply, dif_neg he]⟩ : ecz_ClosedOff G))
    (fun ω _ => Finset.mem_univ _) (fun η _ => Finset.mem_univ _) ?_ ?_ ?_
  · intro ω _
    apply Subtype.ext
    ext e
    by_cases he : P e
    · simp only; rw [Equiv.piEquivPiSubtypeProd_symm_apply]; simp [he]
    · simp only; rw [Equiv.piEquivPiSubtypeProd_symm_apply, dif_neg he]
      exact (ω.2 e he).symm
  · intro η _
    ext e
    simp only
    rw [Equiv.piEquivPiSubtypeProd_symm_apply]; simp [e.2]
  · intro ω _
    apply ecz_fkWeight_eq_of_edges
    intro e he
    rw [Equiv.piEquivPiSubtypeProd_symm_apply, dif_pos he]



theorem ecz_fkZEdge_eq_div (p q : ℝ) :
    ecz_fkZEdge G p q = fkZ G p q / 2 ^ ecz_NE G := by
  rw [ecz_factorization G p q]
  have : (2 : ℝ) ^ ecz_NE G ≠ 0 := by positivity
  field_simp

end EdgeZ



section Iso
variable {V W : Type*} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]
  {G : SimpleGraph V} {H : SimpleGraph W} [DecidableRel G.Adj] [DecidableRel H.Adj]



theorem ecz_NE_iso (φ : G ≃g H) : ecz_NE G = ecz_NE H := by
  rw [ecz_NE_eq, ecz_NE_eq, Fintype.card_congr (fsm_sym2Congr φ.toEquiv), φ.card_edgeFinset_eq]



theorem ecz_fkZEdge_iso (φ : G ≃g H) (p q : ℝ) :
    ecz_fkZEdge G p q = ecz_fkZEdge H p q := by
  have hZ : fkZ G p q = fkZ H p q := fsm_fkZ_iso G H φ p q
  rw [ecz_fkZEdge_eq_div, ecz_fkZEdge_eq_div, ecz_NE_iso φ, hZ]

end Iso











section Interface
variable {V W : Type*} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]
  {G : SimpleGraph V} {H : SimpleGraph W} [DecidableRel G.Adj] [DecidableRel H.Adj]
  {K : SimpleGraph (V ⊕ W)} [DecidableRel K.Adj]





theorem ecz_combine_closedOff (hci : fis_CrossInterface G H K)
    (σ : ecz_ClosedOff G) (τ : ecz_ClosedOff H) (e : Sym2 (V ⊕ W)) (he : e ∉ K.edgeFinset) :
    fsm_combine σ.val τ.val e = false := by
  induction e using Sym2.ind with
  | _ x y =>
    rw [mem_edgeFinset, mem_edgeSet] at he
    match x, y with
    | Sum.inl a, Sum.inl b =>
      show σ.val s(a, b) = false
      apply σ.2
      rw [mem_edgeFinset, mem_edgeSet]
      intro hG
      exact he (hci.le (show (G ⊕g H).Adj (Sum.inl a) (Sum.inl b) from hG))
    | Sum.inr c, Sum.inr d =>
      show τ.val s(c, d) = false
      apply τ.2
      rw [mem_edgeFinset, mem_edgeSet]
      intro hH
      exact he (hci.le (show (G ⊕g H).Adj (Sum.inr c) (Sum.inr d) from hH))
    | Sum.inl a, Sum.inr d => rfl
    | Sum.inr c, Sum.inl b => rfl










theorem ecz_fkZEdge_interface_ge (hci : fis_CrossInterface G H K) {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) :
    (1 - p) ^ (fis_interface G H K).card * (ecz_fkZEdge G p q * ecz_fkZEdge H p q)
      ≤ ecz_fkZEdge K p q := by
  classical
  let glue : ecz_ClosedOff G → ecz_ClosedOff H → ecz_ClosedOff K :=
    fun σ τ => ⟨fsm_combine σ.val τ.val, ecz_combine_closedOff hci σ τ⟩
  have hprod : (1 - p) ^ (fis_interface G H K).card * (ecz_fkZEdge G p q * ecz_fkZEdge H p q)
      = ∑ στ : ecz_ClosedOff G × ecz_ClosedOff H, fkWeight K p q (glue στ.1 στ.2).val := by
    rw [ecz_fkZEdge, ecz_fkZEdge, Fintype.sum_mul_sum, Finset.mul_sum, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun τ _ => ?_
    show _ = fkWeight K p q (fsm_combine σ.val τ.val)
    rw [fis_fkWeight_combine hci p q σ.val τ.val]
  rw [hprod]
  have hinj : Function.Injective
      (fun στ : ecz_ClosedOff G × ecz_ClosedOff H => glue στ.1 στ.2) := by
    rintro ⟨σ₁, τ₁⟩ ⟨σ₂, τ₂⟩ h
    have heq : fsm_combine σ₁.val τ₁.val = fsm_combine σ₂.val τ₂.val := congrArg Subtype.val h
    have h2 : ((σ₁.val, τ₁.val) : (Sym2 V → Bool) × (Sym2 W → Bool)) = (σ₂.val, τ₂.val) :=
      fsm_combine_injective heq
    rw [Prod.mk.injEq] at h2
    exact Prod.ext (Subtype.ext h2.1) (Subtype.ext h2.2)
  rw [ecz_fkZEdge,
    show (∑ στ : ecz_ClosedOff G × ecz_ClosedOff H, fkWeight K p q (glue στ.1 στ.2).val)
        = ∑ ω ∈ Finset.univ.image (fun στ : ecz_ClosedOff G × ecz_ClosedOff H => glue στ.1 στ.2),
            fkWeight K p q ω.val from by
      rw [Finset.sum_image]; intro a _ b _ h; exact hinj h]
  refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) ?_
  intro ω _ _
  exact fkWeight_nonneg K hp hp1 hq ω.val




theorem ecz_neglog_interface_le (hci : fis_CrossInterface G H K) {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) :
    - Real.log (ecz_fkZEdge K p q)
      ≤ - Real.log (ecz_fkZEdge G p q) + - Real.log (ecz_fkZEdge H p q)
        - (fis_interface G H K).card * Real.log (1 - p) := by
  have hZG : 0 < ecz_fkZEdge G p q := ecz_fkZEdge_pos G hp hp1 hq
  have hZH : 0 < ecz_fkZEdge H p q := ecz_fkZEdge_pos H hp hp1 hq
  have hZK : 0 < ecz_fkZEdge K p q := ecz_fkZEdge_pos K hp hp1 hq
  have h1mp : (0:ℝ) < 1 - p := by linarith
  have hge : (1 - p) ^ (fis_interface G H K).card * (ecz_fkZEdge G p q * ecz_fkZEdge H p q)
      ≤ ecz_fkZEdge K p q := ecz_fkZEdge_interface_ge hci hp hp1 hq
  have hpos : 0 < (1 - p) ^ (fis_interface G H K).card * (ecz_fkZEdge G p q * ecz_fkZEdge H p q) :=
    mul_pos (pow_pos h1mp _) (mul_pos hZG hZH)
  have hlog : Real.log ((1 - p) ^ (fis_interface G H K).card
        * (ecz_fkZEdge G p q * ecz_fkZEdge H p q))
      ≤ Real.log (ecz_fkZEdge K p q) := Real.log_le_log hpos hge
  rw [Real.log_mul (by positivity) (by positivity), Real.log_mul hZG.ne' hZH.ne',
    Real.log_pow] at hlog
  push_cast at hlog ⊢
  linarith

end Interface








section AllClosed
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]


theorem ecz_fkZEdge_ge_allClosed {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq1 : 1 ≤ q) :
    (1 - p) ^ G.edgeFinset.card ≤ ecz_fkZEdge G p q := by
  have hterm : (1 - p) ^ G.edgeFinset.card ≤ fkWeight G p q (fun _ => false) := by
    unfold fkWeight edgeProduct
    have hep : (∏ e ∈ G.edgeFinset, (if (fun (_ : Sym2 V) => false) e then p else 1 - p))
        = (1 - p) ^ G.edgeFinset.card := by
      rw [show (∏ e ∈ G.edgeFinset, (if (fun (_ : Sym2 V) => false) e then p else 1 - p))
            = ∏ _e ∈ G.edgeFinset, (1 - p) from Finset.prod_congr rfl (fun e _ => by simp),
        Finset.prod_const]
    rw [hep]
    have hqk : (1 : ℝ) ≤ q ^ numClusters G (fun _ => false) := one_le_pow₀ hq1
    nlinarith [pow_nonneg (by linarith : (0 : ℝ) ≤ 1 - p) G.edgeFinset.card]
  calc (1 - p) ^ G.edgeFinset.card ≤ fkWeight G p q (fun _ => false) := hterm
    _ = fkWeight G p q (⟨fun _ => false, fun _ _ => rfl⟩ : ecz_ClosedOff G).val := rfl
    _ ≤ ecz_fkZEdge G p q := by
        unfold ecz_fkZEdge
        exact Finset.single_le_sum (f := fun ω : ecz_ClosedOff G => fkWeight G p q ω.val)
          (fun ω _ => fkWeight_nonneg G hp hp1 (by linarith) ω.val) (Finset.mem_univ _)


theorem ecz_neglogZEdge_le_edges {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq1 : 1 ≤ q) :
    -Real.log (ecz_fkZEdge G p q) ≤ (G.edgeFinset.card : ℝ) * (-Real.log (1 - p)) := by
  have h1mp : (0 : ℝ) < 1 - p := by linarith
  have hge := ecz_fkZEdge_ge_allClosed G hp hp1 hq1
  have hpow : (0 : ℝ) < (1 - p) ^ G.edgeFinset.card := pow_pos h1mp _
  have hZ : 0 < ecz_fkZEdge G p q := ecz_fkZEdge_pos G hp hp1 (by linarith)
  have hlog : Real.log ((1 - p) ^ G.edgeFinset.card) ≤ Real.log (ecz_fkZEdge G p q) :=
    Real.log_le_log hpow hge
  rw [Real.log_pow] at hlog
  push_cast at hlog ⊢
  nlinarith [hlog]

end AllClosed









section PartitionPeel
variable {U : Type*} [Fintype U] [DecidableEq U] (K₀ : SimpleGraph U) [DecidableRel K₀.Adj]





theorem ecz_neglog_partition_le (P : U → Prop) [DecidablePred P] {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) :
    -Real.log (ecz_fkZEdge K₀ p q)
      ≤ -Real.log (ecz_fkZEdge (agl_left K₀ P) p q)
        + -Real.log (ecz_fkZEdge (agl_right K₀ P) p q)
        - (agl_interfaceCard K₀ P : ℝ) * Real.log (1 - p) := by
  have hiso : ecz_fkZEdge K₀ p q = ecz_fkZEdge (agl_glueGraph K₀ P) p q :=
    ecz_fkZEdge_iso (agl_iso K₀ P) p q
  rw [hiso]
  exact ecz_neglog_interface_le (agl_partitionCrossInterface K₀ P) hp hp1 hq


noncomputable def ecz_uu {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (p q : ℝ) : ℝ := -Real.log (ecz_fkZEdge G p q)

section Peel
variable {T : Type*} [DecidableEq T] (tag : U → T)



theorem ecz_left_eq (τ : T) (S : Finset T) (hτ : τ ∉ S) (p q : ℝ) :
    ecz_fkZEdge (agl_left (qp_restG K₀ tag (insert τ S)) (fun x => tag x.1 = τ)) p q
      = ecz_fkZEdge (qp_blkG K₀ tag τ) p q := by
  show ecz_fkZEdge (((K₀.comap (Subtype.val : {x // tag x ∈ insert τ S} → U)).comap
    (Subtype.val : {x // tag x.1 = τ} → _))) p q
      = ecz_fkZEdge (K₀.comap (Subtype.val : {x // tag x = τ} → U)) p q
  refine ecz_fkZEdge_iso (qp_comapComapIso K₀ _ _ _ ?_ Subtype.val_injective ?_) p q
  · intro a b h; apply Subtype.ext; apply Subtype.ext; exact h
  · ext u; constructor
    · rintro ⟨v, rfl⟩; exact ⟨⟨v.1, v.2⟩, rfl⟩
    · rintro ⟨v, rfl⟩
      exact ⟨⟨⟨v.1, by rw [v.2]; exact Finset.mem_insert_self τ S⟩, v.2⟩, rfl⟩



theorem ecz_right_eq (τ : T) (S : Finset T) (hτ : τ ∉ S) (p q : ℝ) :
    ecz_fkZEdge (agl_right (qp_restG K₀ tag (insert τ S)) (fun x => tag x.1 = τ)) p q
      = ecz_fkZEdge (qp_restG K₀ tag S) p q := by
  show ecz_fkZEdge (((K₀.comap (Subtype.val : {x // tag x ∈ insert τ S} → U)).comap
    (Subtype.val : {x // ¬ (tag x.1 = τ)} → _))) p q
      = ecz_fkZEdge (K₀.comap (Subtype.val : {x // tag x ∈ S} → U)) p q
  refine ecz_fkZEdge_iso (qp_comapComapIso K₀ _ _ _ ?_ Subtype.val_injective ?_) p q
  · intro a b h; apply Subtype.ext; apply Subtype.ext; exact h
  · ext u; constructor
    · rintro ⟨v, rfl⟩
      have hv := v.1.2; have hne := v.2; rw [Finset.mem_insert] at hv
      rcases hv with h | h
      · exact absurd h hne
      · exact ⟨⟨v.1.1, h⟩, rfl⟩
    · rintro ⟨v, rfl⟩
      exact ⟨⟨⟨v.1, Finset.mem_insert_of_mem v.2⟩, fun hc => hτ (hc ▸ v.2)⟩, rfl⟩



theorem ecz_left_edge_card (τ : T) (S : Finset T) (hτ : τ ∉ S) :
    (agl_left (qp_restG K₀ tag (insert τ S)) (fun x => tag x.1 = τ)).edgeFinset.card
      = (qp_blkG K₀ tag τ).edgeFinset.card := by
  show (((K₀.comap (Subtype.val : {x // tag x ∈ insert τ S} → U)).comap
    (Subtype.val : {x // tag x.1 = τ} → _))).edgeFinset.card
      = (K₀.comap (Subtype.val : {x // tag x = τ} → U)).edgeFinset.card
  refine (qp_comapComapIso K₀ _ _ _ ?_ Subtype.val_injective ?_).card_edgeFinset_eq
  · intro a b h; apply Subtype.ext; apply Subtype.ext; exact h
  · ext u; constructor
    · rintro ⟨v, rfl⟩; exact ⟨⟨v.1, v.2⟩, rfl⟩
    · rintro ⟨v, rfl⟩
      exact ⟨⟨⟨v.1, by rw [v.2]; exact Finset.mem_insert_self τ S⟩, v.2⟩, rfl⟩



theorem ecz_right_edge_card (τ : T) (S : Finset T) (hτ : τ ∉ S) :
    (agl_right (qp_restG K₀ tag (insert τ S)) (fun x => tag x.1 = τ)).edgeFinset.card
      = (qp_restG K₀ tag S).edgeFinset.card := by
  show (((K₀.comap (Subtype.val : {x // tag x ∈ insert τ S} → U)).comap
    (Subtype.val : {x // ¬ (tag x.1 = τ)} → _))).edgeFinset.card
      = (K₀.comap (Subtype.val : {x // tag x ∈ S} → U)).edgeFinset.card
  refine (qp_comapComapIso K₀ _ _ _ ?_ Subtype.val_injective ?_).card_edgeFinset_eq
  · intro a b h; apply Subtype.ext; apply Subtype.ext; exact h
  · ext u; constructor
    · rintro ⟨v, rfl⟩
      have hv := v.1.2; have hne := v.2; rw [Finset.mem_insert] at hv
      rcases hv with h | h
      · exact absurd h hne
      · exact ⟨⟨v.1.1, h⟩, rfl⟩
    · rintro ⟨v, rfl⟩
      exact ⟨⟨⟨v.1, Finset.mem_insert_of_mem v.2⟩, fun hc => hτ (hc ▸ v.2)⟩, rfl⟩



theorem ecz_fkZEdge_empty {V : Type*} [Fintype V] [DecidableEq V] [IsEmpty V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (p q : ℝ) : ecz_fkZEdge G p q = 1 := by
  have hZ : fkZ G p q = 1 := qp_fkZ_empty G p q
  have hNE : ecz_NE G = 0 := by
    rw [ecz_NE_eq]
    have : Fintype.card (Sym2 V) = 0 := by
      rw [Fintype.card_eq_zero_iff]
      exact ⟨fun e => e.recOnSubsingleton (fun x => isEmptyElim x)⟩
    omega
  rw [ecz_fkZEdge_eq_div, hZ, hNE, pow_zero, div_one]








theorem ecz_peel_le (p q : ℝ) (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) :
    ∀ S : Finset T, ∃ I : ℕ,
      ecz_uu (qp_restG K₀ tag S) p q
          ≤ (∑ τ ∈ S, ecz_uu (qp_blkG K₀ tag τ) p q) + (I : ℝ) * (-Real.log (1 - p))
        ∧ I ≤ ∑ τ ∈ S, (qp_straddleEdges K₀ (fun u => tag u = τ)).card := by
  intro S
  induction S using Finset.induction with
  | empty =>
    refine ⟨0, ?_, by simp⟩
    simp only [Finset.sum_empty, Nat.cast_zero, zero_mul, add_zero]
    haveI : IsEmpty {x : U // tag x ∈ (∅ : Finset T)} := ⟨fun x => by simpa using x.2⟩
    rw [ecz_uu, ecz_fkZEdge_empty, Real.log_one, neg_zero]
  | @insert τ S hτ ih =>
    obtain ⟨I0, hI0le, hI0bd⟩ := ih
    have hpart := ecz_neglog_partition_le (qp_restG K₀ tag (insert τ S))
      (fun x => tag x.1 = τ) hp hp1 hq
    rw [show -Real.log (ecz_fkZEdge (agl_left (qp_restG K₀ tag (insert τ S))
            (fun x => tag x.1 = τ)) p q)
        = ecz_uu (qp_blkG K₀ tag τ) p q from by rw [ecz_uu, ecz_left_eq K₀ tag τ S hτ]] at hpart
    rw [show -Real.log (ecz_fkZEdge (agl_right (qp_restG K₀ tag (insert τ S))
            (fun x => tag x.1 = τ)) p q)
        = ecz_uu (qp_restG K₀ tag S) p q from by rw [ecz_uu, ecz_right_eq K₀ tag τ S hτ]] at hpart
    set Istep := agl_interfaceCard (qp_restG K₀ tag (insert τ S)) (fun x => tag x.1 = τ)
      with hIstep
    refine ⟨Istep + I0, ?_, ?_⟩
    · rw [Finset.sum_insert hτ]; push_cast
      have huu : ecz_uu (qp_restG K₀ tag (insert τ S)) p q
          ≤ ecz_uu (qp_blkG K₀ tag τ) p q + ecz_uu (qp_restG K₀ tag S) p q
            - (Istep : ℝ) * Real.log (1 - p) := by rw [ecz_uu]; exact hpart
      calc ecz_uu (qp_restG K₀ tag (insert τ S)) p q
          ≤ ecz_uu (qp_blkG K₀ tag τ) p q + ecz_uu (qp_restG K₀ tag S) p q
              - (Istep : ℝ) * Real.log (1 - p) := huu
        _ ≤ ecz_uu (qp_blkG K₀ tag τ) p q
              + ((∑ σ ∈ S, ecz_uu (qp_blkG K₀ tag σ) p q) + (I0 : ℝ) * (-Real.log (1 - p)))
              - (Istep : ℝ) * Real.log (1 - p) := by linarith [hI0le]
        _ = (ecz_uu (qp_blkG K₀ tag τ) p q + ∑ σ ∈ S, ecz_uu (qp_blkG K₀ tag σ) p q)
              + ((Istep : ℝ) + (I0 : ℝ)) * (-Real.log (1 - p)) := by ring
    · rw [Finset.sum_insert hτ]
      have hIstepbd : Istep ≤ (qp_straddleEdges K₀ (fun u => tag u = τ)).card :=
        le_trans (qp_interface_le_straddle (qp_restG K₀ tag (insert τ S)) (fun x => tag x.1 = τ))
          (qp_restG_straddle_le K₀ tag τ S)
      omega

end Peel

end PartitionPeel










section BoxDoubling


noncomputable def ecz_u (d : ℕ) (t : ℝ) (n : ℕ) : ℝ :=
  -Real.log (ecz_fkZEdge (boxGraph d n) (fsc_logistic t) 2)



theorem ecz_block_fkZEdge (d K : ℕ) (s : Fin d → Bool) (p q : ℝ) :
    ecz_fkZEdge (qp_blkG (boxGraph d (2 * K + 1)) (qp_boxTag d K) (some s)) p q
      = ecz_fkZEdge (boxGraph d K) p q := by
  have key : ecz_fkZEdge (agl_left (boxGraph d (2 * K + 1)) (fun x => qp_boxTag d K x = some s)) p q
      = ecz_fkZEdge (boxGraph d K) p q :=
    (ecz_fkZEdge_iso
      (agl_leftBlockIso (2 * K + 1) K (fun x => qp_boxTag d K x = some s)
        (qp_vshift d K s) (qp_quadφ d K s)
        (by intro y
            show (((qp_quadφ d K s y).1 : boxVerts d (2 * K + 1)) : Site d)
                = (y : Site d) + qp_vshift d K s
            funext i; rfl)) p q).symm
  convert key using 2




theorem ecz_box_neglog_doubling (d K : ℕ) (t : ℝ) :
    ecz_u d t (2 * K + 1) ≤ (2 : ℝ) ^ d * ecz_u d t K
      + ((2 * d * (qp_Jset d K).card + (2 ^ d + 1) * (2 * d * (qp_Jset d K).card) : ℕ) : ℝ)
          * (-Real.log (1 - fsc_logistic t)) := by
  set p := fsc_logistic t with hp
  have hp0 : (0 : ℝ) < p := fsc_logistic_pos t
  have hp1 : p < 1 := fsc_logistic_lt_one t
  set c := -Real.log (1 - p) with hc
  have hc0 : 0 ≤ c := by rw [hc, neg_nonneg]; exact Real.log_nonpos (by linarith) (by linarith)
  obtain ⟨I, hIle, hIbd⟩ :=
    ecz_peel_le (boxGraph d (2 * K + 1)) (qp_boxTag d K) p 2 hp0 hp1 (by norm_num) Finset.univ
  have hrest : ecz_uu (qp_restG (boxGraph d (2 * K + 1)) (qp_boxTag d K) Finset.univ) p 2
      = ecz_u d t (2 * K + 1) := by
    rw [ecz_uu, ecz_u, ecz_fkZEdge_iso (qp_restGUnivIso d K) p 2]
  have hblksum : (∑ τ ∈ (Finset.univ : Finset (Option (Fin d → Bool))),
        ecz_uu (qp_blkG (boxGraph d (2 * K + 1)) (qp_boxTag d K) τ) p 2)
      = ecz_uu (qp_blkG (boxGraph d (2 * K + 1)) (qp_boxTag d K) none) p 2
        + (2 : ℝ) ^ d * ecz_u d t K := by
    rw [show (∑ τ ∈ (Finset.univ : Finset (Option (Fin d → Bool))),
            ecz_uu (qp_blkG (boxGraph d (2 * K + 1)) (qp_boxTag d K) τ) p 2)
          = ∑ τ : Option (Fin d → Bool),
              ecz_uu (qp_blkG (boxGraph d (2 * K + 1)) (qp_boxTag d K) τ) p 2 from rfl,
      Fintype.sum_option]
    congr 1
    have heach : ∀ s : Fin d → Bool,
        ecz_uu (qp_blkG (boxGraph d (2 * K + 1)) (qp_boxTag d K) (some s)) p 2 = ecz_u d t K :=
      fun s => by rw [ecz_uu, ecz_block_fkZEdge]; rfl
    rw [Finset.sum_congr rfl (fun s _ => heach s), Finset.sum_const, Finset.card_univ,
      show Fintype.card (Fin d → Bool) = 2 ^ d from by simp [Fintype.card_fun, Fintype.card_bool],
      nsmul_eq_mul]
    push_cast; ring
  have hnone : ecz_uu (qp_blkG (boxGraph d (2 * K + 1)) (qp_boxTag d K) none) p 2
      ≤ ((2 * d * (qp_Jset d K).card : ℕ) : ℝ) * c := by
    rw [ecz_uu]
    calc -Real.log (ecz_fkZEdge (qp_blkG (boxGraph d (2 * K + 1)) (qp_boxTag d K) none) p 2)
        ≤ ((qp_blkG (boxGraph d (2 * K + 1)) (qp_boxTag d K) none).edgeFinset.card : ℝ) * c :=
          ecz_neglogZEdge_le_edges _ hp0 hp1 (by norm_num)
      _ ≤ ((2 * d * (qp_Jset d K).card : ℕ) : ℝ) * c := by
          apply mul_le_mul_of_nonneg_right _ hc0
          exact_mod_cast qp_blkNone_edge_le d K
  have hIbound : (I : ℝ) ≤ ((2 ^ d + 1) * (2 * d * (qp_Jset d K).card) : ℕ) := by
    have h2 : (∑ τ ∈ (Finset.univ : Finset (Option (Fin d → Bool))),
          (qp_straddleEdges (boxGraph d (2 * K + 1)) (fun u => qp_boxTag d K u = τ)).card)
        ≤ ∑ _τ ∈ (Finset.univ : Finset (Option (Fin d → Bool))), 2 * d * (qp_Jset d K).card :=
      Finset.sum_le_sum (fun τ _ => qp_straddle_card_le_all d K τ)
    have h3 : (∑ _τ ∈ (Finset.univ : Finset (Option (Fin d → Bool))), 2 * d * (qp_Jset d K).card)
        = (2 ^ d + 1) * (2 * d * (qp_Jset d K).card) := by
      rw [Finset.sum_const, Finset.card_univ, smul_eq_mul]
      congr 1
      rw [show Fintype.card (Option (Fin d → Bool)) = Fintype.card (Fin d → Bool) + 1 from
          Fintype.card_option,
        show Fintype.card (Fin d → Bool) = 2 ^ d from by simp [Fintype.card_fun, Fintype.card_bool]]
    calc (I : ℝ) ≤ ((∑ τ ∈ (Finset.univ : Finset (Option (Fin d → Bool))),
            (qp_straddleEdges (boxGraph d (2 * K + 1)) (fun u => qp_boxTag d K u = τ)).card : ℕ) : ℝ) := by
          exact_mod_cast hIbd
      _ ≤ (((2 ^ d + 1) * (2 * d * (qp_Jset d K).card) : ℕ) : ℝ) := by
          exact_mod_cast le_trans h2 (le_of_eq h3)
  rw [hrest, hblksum] at hIle
  push_cast at hIle hnone hIbound ⊢
  nlinarith [hIle, hnone, hIbound, hc0, mul_le_mul_of_nonneg_right hIbound hc0]

end BoxDoubling









section EdgeFreeEnergy
variable {d : ℕ}


noncomputable def ecz_edgeFreeEnergy (d : ℕ) (t : ℝ) (n : ℕ) : ℝ :=
  -(ecz_u d t n / ((boxGraph d n).edgeFinset.card : ℝ)) + Real.log (1 + Real.exp t)



theorem ecz_ivp2_eq_edgeFE (t : ℝ) (n : ℕ) (hE : 0 < (boxGraph d n).edgeFinset.card) :
    ivp2_tiltFreeEnergy (boxGraph d n) 2 t
      = (ecz_NE (boxGraph d n) : ℝ) / ((boxGraph d n).edgeFinset.card : ℝ) * Real.log 2
        + ecz_edgeFreeEnergy d t n := by
  unfold ivp2_tiltFreeEnergy ecz_edgeFreeEnergy ecz_u
  set p := fsc_logistic t
  have hp0 : (0:ℝ) < p := fsc_logistic_pos t
  have hp1 : p < 1 := fsc_logistic_lt_one t
  have hfact : fkZ (boxGraph d n) p 2 = 2 ^ ecz_NE (boxGraph d n) * ecz_fkZEdge (boxGraph d n) p 2 :=
    ecz_factorization (boxGraph d n) p 2
  have hZE : 0 < ecz_fkZEdge (boxGraph d n) p 2 := ecz_fkZEdge_pos _ hp0 hp1 (by norm_num)
  have h2 : (0:ℝ) < (2:ℝ) ^ ecz_NE (boxGraph d n) := by positivity
  rw [hfact, Real.log_mul h2.ne' hZE.ne', Real.log_pow]
  have hEne : ((boxGraph d n).edgeFinset.card : ℝ) ≠ 0 := by exact_mod_cast hE.ne'
  field_simp
  ring



theorem ecz_centered_eq_cfe (t : ℝ) (n : ℕ) (hE : 0 < (boxGraph d n).edgeFinset.card) :
    cfe_centered (boxGraph d n) 2 t = ecz_edgeFreeEnergy d t n - ecz_edgeFreeEnergy d 0 n := by
  unfold cfe_centered
  rw [ecz_ivp2_eq_edgeFE t n hE, ecz_ivp2_eq_edgeFE 0 n hE]
  ring


theorem ecz_edgeFE_eq (t : ℝ) (n : ℕ) :
    ecz_edgeFreeEnergy d t n = -(ecz_u d t n / agl_E d n) + Real.log (1 + Real.exp t) := by
  rfl

end EdgeFreeEnergy







section AdditiveDoubling
variable {d : ℕ}




def ecz_AdditiveDoublingBound (d : ℕ) (t : ℝ) : Prop :=
  ∃ (I : ℕ → ℝ),
    (∀ j, 0 ≤ I j)
    ∧ Summable (fun j => I j / agl_E d (agl_K (j + 1)))
    ∧ (∀ j, ecz_u d t (agl_K (j + 1))
        ≤ (2 : ℝ) ^ d * ecz_u d t (agl_K j) + I j * (-Real.log (1 - fsc_logistic t)))
    ∧ (∀ j, |(2 : ℝ) ^ d * agl_E d (agl_K j) - agl_E d (agl_K (j + 1))| ≤ I j)





theorem ecz_additiveDoublingBound (d : ℕ) (hd : 1 ≤ d) (t : ℝ) :
    ecz_AdditiveDoublingBound d t := by
  set c := -Real.log (1 - fsc_logistic t) with hc
  have hp0 : (0 : ℝ) < fsc_logistic t := fsc_logistic_pos t
  have hp1 : fsc_logistic t < 1 := fsc_logistic_lt_one t
  have hc0 : 0 ≤ c := by rw [hc, neg_nonneg]; exact Real.log_nonpos (by linarith) (by linarith)
  set N : ℕ → ℝ := fun j => ((2 * d * (qp_Jset d (agl_K j)).card
    + (2 ^ d + 1) * (2 * d * (qp_Jset d (agl_K j)).card) : ℕ) : ℝ) with hN
  set G : ℕ → ℝ := fun j => agl_E d (agl_K (j + 1)) - (2 : ℝ) ^ d * agl_E d (agl_K j) with hG
  have hKsucc : ∀ j, agl_K (j + 1) = 2 * agl_K j + 1 := agl_K_succ
  have hGnn : ∀ j, 0 ≤ G j := by
    intro j; rw [hG]; simp only
    have h := qp_edge_le d (agl_K j) hd
    rw [show agl_E d (agl_K (j + 1)) = agl_E d (2 * agl_K j + 1) from by rw [agl_K_succ]]
    rw [agl_E, agl_E]; linarith [h]
  set I : ℕ → ℝ := fun j => N j + G j with hI
  have hInn : ∀ j, 0 ≤ I j := by
    intro j; rw [hI]; have : 0 ≤ N j := Nat.cast_nonneg _; linarith [hGnn j]
  refine ⟨I, hInn, ?_, ?_, ?_⟩
  · apply qp_summable_ratio d hd I _ hInn
    intro j
    have hNb : N j ≤ ((2 ^ d + 2) * (2 * d * d) : ℝ) * (4 * (agl_K j : ℝ) + 3) ^ (d - 1) := by
      simp only [hN]
      have hJ : (qp_Jset d (agl_K j)).card ≤ d * (2 * (2 * agl_K j + 1) + 1) ^ (d - 1) :=
        qp_Jset_card_le d (agl_K j) hd
      rw [show (2 * d * (qp_Jset d (agl_K j)).card + (2 ^ d + 1) * (2 * d * (qp_Jset d (agl_K j)).card))
            = (2 ^ d + 2) * (2 * d * (qp_Jset d (agl_K j)).card) from by ring]
      push_cast
      have hbase : (2 * (2 * (agl_K j : ℝ) + 1) + 1) = 4 * (agl_K j : ℝ) + 3 := by ring
      have hJR : ((qp_Jset d (agl_K j)).card : ℝ)
          ≤ (d : ℝ) * (4 * (agl_K j : ℝ) + 3) ^ (d - 1) := by
        calc ((qp_Jset d (agl_K j)).card : ℝ)
            ≤ ((d * (2 * (2 * agl_K j + 1) + 1) ^ (d - 1) : ℕ) : ℝ) := by exact_mod_cast hJ
          _ = (d : ℝ) * (2 * (2 * (agl_K j : ℝ) + 1) + 1) ^ (d - 1) := by push_cast; ring
          _ = (d : ℝ) * (4 * (agl_K j : ℝ) + 3) ^ (d - 1) := by rw [hbase]
      calc ((2 : ℝ) ^ d + 2) * (2 * d * ((qp_Jset d (agl_K j)).card : ℝ))
          ≤ ((2 : ℝ) ^ d + 2) * (2 * d * ((d : ℝ) * (4 * (agl_K j : ℝ) + 3) ^ (d - 1))) := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            apply mul_le_mul_of_nonneg_left hJR (by positivity)
        _ = ((2 : ℝ) ^ d + 2) * (2 * d * d) * (4 * (agl_K j : ℝ) + 3) ^ (d - 1) := by ring
    have hGb : G j ≤ ((d : ℝ) * (d + 2)) * (4 * (agl_K j : ℝ) + 3) ^ (d - 1) := by
      rw [hG]; simp only
      rw [show agl_E d (agl_K (j + 1)) = agl_E d (2 * agl_K j + 1) from by rw [agl_K_succ]]
      have h := qp_edge_gap_le d (agl_K j) hd
      rw [agl_E, agl_E]; linarith [h]
    rw [hI]; linarith [hNb, hGb]
  · intro j
    have hdbl := ecz_box_neglog_doubling d (agl_K j) t
    rw [show ecz_u d t (agl_K (j + 1)) = ecz_u d t (2 * agl_K j + 1) from by rw [agl_K_succ]]
    have hge : N j * c ≤ I j * c := by
      rw [hI]; apply mul_le_mul_of_nonneg_right _ hc0; linarith [hGnn j]
    calc ecz_u d t (2 * agl_K j + 1)
        ≤ (2 : ℝ) ^ d * ecz_u d t (agl_K j) + N j * c := hdbl
      _ ≤ (2 : ℝ) ^ d * ecz_u d t (agl_K j) + I j * c := by linarith
  · intro j
    have hGval : G j = agl_E d (agl_K (j + 1)) - (2 : ℝ) ^ d * agl_E d (agl_K j) := rfl
    rw [abs_of_nonpos (by have := hGnn j; rw [hGval] at this; linarith)]
    rw [hI]; have hNn : 0 ≤ N j := Nat.cast_nonneg _
    have hGeq : -((2 : ℝ) ^ d * agl_E d (agl_K j) - agl_E d (agl_K (j + 1))) = G j := by
      rw [hGval]; ring
    rw [hGeq]; linarith

end AdditiveDoubling









section Boundedness
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]


theorem ecz_numClusters_le (ω : ConfigSpace (Sym2 V)) : numClusters G ω ≤ Fintype.card V := by
  unfold numClusters
  apply Fintype.card_le_of_surjective (openSub G ω).connectedComponentMk
  intro c
  induction c using SimpleGraph.ConnectedComponent.ind with
  | _ v => exact ⟨v, rfl⟩



theorem ecz_fkWeight_le {p : ℝ} (hp : 0 < p) (hp1 : p < 1) (ω : ConfigSpace (Sym2 V)) :
    fkWeight G p 2 ω ≤ 2 ^ Fintype.card V := by
  unfold fkWeight
  have hep : edgeProduct G p ω ≤ 1 := by
    unfold edgeProduct
    apply Finset.prod_le_one
    · intro e _; split <;> [exact hp.le; linarith]
    · intro e _; split <;> [exact hp1.le; linarith]
  have hq : (2:ℝ) ^ numClusters G ω ≤ 2 ^ Fintype.card V :=
    pow_le_pow_right₀ (by norm_num) (ecz_numClusters_le G ω)
  calc edgeProduct G p ω * 2 ^ numClusters G ω
      ≤ 1 * 2 ^ Fintype.card V := by
        exact mul_le_mul hep hq (by positivity) (by norm_num)
    _ = 2 ^ Fintype.card V := by ring


theorem ecz_closedOff_card : Fintype.card (ecz_ClosedOff G) = 2 ^ G.edgeFinset.card := by
  classical
  rw [show (2:ℕ) ^ G.edgeFinset.card = Fintype.card (G.edgeFinset → Bool) from by
    rw [Fintype.card_fun, Fintype.card_bool, Fintype.card_coe]]
  apply Fintype.card_congr
  refine ⟨fun ω e => ω.val e.val,
    fun η => ⟨fun e => if h : e ∈ G.edgeFinset then η ⟨e, h⟩ else false,
      fun e he => by simp only [dif_neg he]⟩, ?_, ?_⟩
  · intro ω; apply Subtype.ext; funext e
    by_cases he : e ∈ G.edgeFinset
    · simp only [dif_pos he]
    · simp only [dif_neg he]; exact (ω.2 e he).symm
  · intro η; funext e; simp only [dif_pos e.2]


theorem ecz_fkZEdge_le {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    ecz_fkZEdge G p 2 ≤ (2 : ℝ) ^ G.edgeFinset.card * 2 ^ Fintype.card V := by
  unfold ecz_fkZEdge
  calc ∑ ω : ecz_ClosedOff G, fkWeight G p 2 ω.val
      ≤ ∑ ω : ecz_ClosedOff G, (2:ℝ) ^ Fintype.card V :=
        Finset.sum_le_sum (fun ω _ => ecz_fkWeight_le G hp hp1 ω.val)
    _ = (Fintype.card (ecz_ClosedOff G) : ℝ) * 2 ^ Fintype.card V := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ = (2 : ℝ) ^ G.edgeFinset.card * 2 ^ Fintype.card V := by
        rw [ecz_closedOff_card G]; push_cast; ring

end Boundedness



section BoxBounds







theorem ecz_box_edge_pos (d : ℕ) (hd : 1 ≤ d) {n : ℕ} (hn : 1 ≤ n) :
    0 < (boxGraph d n).edgeFinset.card := by
  rw [EdgeCount.boxGraph_edgeCard d n hd]
  have hdp : 0 < d := hd
  have hnp : 0 < 2 * n := by omega
  have hpow : 0 < (2 * n + 1) ^ (d - 1) := pow_pos (by omega) _
  positivity


theorem ecz_boxVerts_card (d n : ℕ) : Fintype.card (boxVerts d n) = (2 * n + 1) ^ d := by
  rw [← boxSV_card_boxF d n]
  apply Fintype.card_of_subtype (boxSV_boxF d n)
  intro x
  rw [boxSV_mem_boxF]
  show (∀ i, x i ∈ Finset.Icc (-(n:ℤ)) n) ↔ x ∈ box d n
  rw [mem_box]
  refine forall_congr' (fun i => ?_)
  rw [Finset.mem_Icc]
  constructor
  · intro ⟨h1, h2⟩; omega
  · intro h; constructor <;> omega



theorem ecz_boxVerts_le_edges (d n : ℕ) (hd : 1 ≤ d) (hn : 1 ≤ n) :
    Fintype.card (boxVerts d n) ≤ 2 * (boxGraph d n).edgeFinset.card := by
  rw [ecz_boxVerts_card, EdgeCount.boxGraph_edgeCard d n hd]
  have hd1 : (2 * n + 1) ^ d = (2 * n + 1) * (2 * n + 1) ^ (d - 1) := by
    rw [← pow_succ']; congr 1; omega
  rw [hd1]
  calc (2 * n + 1) * (2 * n + 1) ^ (d - 1)
      ≤ (2 * (d * (2 * n))) * (2 * n + 1) ^ (d - 1) := by
        apply Nat.mul_le_mul_right
        nlinarith [hd, hn]
    _ = 2 * (d * (2 * n * (2 * n + 1) ^ (d - 1))) := by ring





theorem ecz_edgeFE_le_const (d n : ℕ) (hd : 1 ≤ d) (hn : 1 ≤ n) (s : ℝ)
    (hE : 0 < (boxGraph d n).edgeFinset.card) :
    ecz_edgeFreeEnergy d s n ≤ 3 * Real.log 2 + Real.log (1 + Real.exp s) := by
  unfold ecz_edgeFreeEnergy ecz_u
  set E := (boxGraph d n).edgeFinset.card with hEdef
  set V := Fintype.card (boxVerts d n) with hVdef
  set p := fsc_logistic s
  have hp0 : (0:ℝ) < p := fsc_logistic_pos s
  have hp1 : p < 1 := fsc_logistic_lt_one s
  have hEr : (0:ℝ) < (E:ℝ) := by exact_mod_cast hE
  have hZpos : 0 < ecz_fkZEdge (boxGraph d n) p 2 := ecz_fkZEdge_pos _ hp0 hp1 (by norm_num)
  have hub : ecz_fkZEdge (boxGraph d n) p 2 ≤ (2:ℝ)^E * 2^V := ecz_fkZEdge_le _ hp0 hp1
  have hlog : Real.log (ecz_fkZEdge (boxGraph d n) p 2) ≤ ((E:ℝ) + V) * Real.log 2 := by
    calc Real.log (ecz_fkZEdge (boxGraph d n) p 2)
        ≤ Real.log ((2:ℝ)^E * 2^V) := Real.log_le_log hZpos hub
      _ = (E:ℝ) * Real.log 2 + V * Real.log 2 := by
          rw [Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow]
      _ = ((E:ℝ) + V) * Real.log 2 := by ring
  have hVle : (V:ℝ) ≤ 2 * E := by exact_mod_cast ecz_boxVerts_le_edges d n hd hn
  have hlog2 : (0:ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hkey : -(-Real.log (ecz_fkZEdge (boxGraph d n) p 2) / (E:ℝ)) ≤ 3 * Real.log 2 := by
    rw [neg_div, neg_neg, div_le_iff₀ hEr]
    calc Real.log (ecz_fkZEdge (boxGraph d n) p 2) ≤ ((E:ℝ) + V) * Real.log 2 := hlog
      _ ≤ ((E:ℝ) + 2 * E) * Real.log 2 := by
          apply mul_le_mul_of_nonneg_right _ hlog2; linarith
      _ = 3 * Real.log 2 * E := by ring
  linarith

end BoxBounds














section BoxNesting
variable {d : ℕ}



def ecz_subBoxPred (d a n : ℕ) : boxVerts d n → Prop := fun x => (x : Site d) ∈ box d a

instance ecz_subBoxPred_decidable (d a n : ℕ) : DecidablePred (ecz_subBoxPred d a n) := by
  intro x; unfold ecz_subBoxPred box; infer_instance



noncomputable def ecz_subBoxIso (a n : ℕ) (hle : a ≤ n) :
    boxGraph d a ≃g agl_left (boxGraph d n) (ecz_subBoxPred d a n) := by
  classical
  have hsub : box d a ⊆ box d n := box_mono d hle
  refine agl_leftBlockIso n a (ecz_subBoxPred d a n) 0 ?_ ?_
  · exact {
      toFun := fun y => ⟨⟨(y : Site d), hsub y.2⟩, y.2⟩
      invFun := fun z => ⟨(z.1 : Site d), z.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  · intro y
    show ((⟨(y : Site d), hsub y.2⟩ : boxVerts d n) : Site d) = (y : Site d) + 0
    simp











theorem ecz_box_nesting_le (a n : ℕ) (hle : a ≤ n) (t : ℝ) :
    ecz_u d t n ≤ ecz_u d t a
      + ((agl_interfaceCard (boxGraph d n) (ecz_subBoxPred d a n)
          + ((agl_right (boxGraph d n) (ecz_subBoxPred d a n)).edgeFinset.card : ℝ)))
          * (-Real.log (1 - fsc_logistic t)) := by
  classical
  set p := fsc_logistic t with hp
  have hp0 : (0 : ℝ) < p := fsc_logistic_pos t
  have hp1 : p < 1 := fsc_logistic_lt_one t
  set c := -Real.log (1 - p) with hc
  have hc0 : 0 ≤ c := by rw [hc, neg_nonneg]; exact Real.log_nonpos (by linarith) (by linarith)
  set P : boxVerts d n → Prop := ecz_subBoxPred d a n with hP
  have hpart := ecz_neglog_partition_le (boxGraph d n) P hp0 hp1 (by norm_num : (0:ℝ) < 2)
  have hleft : ecz_fkZEdge (agl_left (boxGraph d n) P) p 2 = ecz_fkZEdge (boxGraph d a) p 2 :=
    (ecz_fkZEdge_iso (ecz_subBoxIso a n hle) p 2).symm
  have hright : -Real.log (ecz_fkZEdge (agl_right (boxGraph d n) P) p 2)
      ≤ ((agl_right (boxGraph d n) P).edgeFinset.card : ℝ) * c :=
    ecz_neglogZEdge_le_edges _ hp0 hp1 (by norm_num)
  rw [ecz_u, ecz_u]
  rw [show -Real.log (ecz_fkZEdge (agl_left (boxGraph d n) P) p 2)
        = -Real.log (ecz_fkZEdge (boxGraph d a) p 2) from by rw [hleft]] at hpart
  have hkey : -Real.log (ecz_fkZEdge (boxGraph d n) p 2)
      ≤ -Real.log (ecz_fkZEdge (boxGraph d a) p 2)
        + ((agl_right (boxGraph d n) P).edgeFinset.card : ℝ) * c
        + (agl_interfaceCard (boxGraph d n) P : ℝ) * c := by
    have hceq : -(agl_interfaceCard (boxGraph d n) P : ℝ) * Real.log (1 - p)
        = (agl_interfaceCard (boxGraph d n) P : ℝ) * c := by rw [hc]; ring
    nlinarith [hpart, hright, hceq]
  calc -Real.log (ecz_fkZEdge (boxGraph d n) p 2)
      ≤ _ := hkey
    _ = -Real.log (ecz_fkZEdge (boxGraph d a) p 2)
        + ((agl_interfaceCard (boxGraph d n) P : ℝ)
            + ((agl_right (boxGraph d n) P).edgeFinset.card : ℝ)) * c := by ring



theorem ecz_sum_edgeFinset_card {V W : Type*} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]
    (G : SimpleGraph V) (H : SimpleGraph W) [DecidableRel G.Adj] [DecidableRel H.Adj] :
    (G ⊕g H).edgeFinset.card = G.edgeFinset.card + H.edgeFinset.card := by
  classical
  have hkey : (G ⊕g H).edgeFinset
      = G.edgeFinset.image (Sym2.map Sum.inl) ∪ H.edgeFinset.image (Sym2.map Sum.inr) := by
    ext e
    induction e using Sym2.ind with
    | _ x y =>
      simp only [Finset.mem_union, Finset.mem_image, mem_edgeFinset, mem_edgeSet]
      match x, y with
      | Sum.inl a, Sum.inl b =>
        constructor
        · intro h
          refine Or.inl ⟨s(a, b), ?_, by simp [Sym2.map_mk]⟩
          rw [mem_edgeSet]; rw [SimpleGraph.sum_adj] at h; exact h
        · rintro (⟨f, hf, hfe⟩ | ⟨f, hf, hfe⟩)
          · induction f using Sym2.ind with
            | _ p q =>
              rw [mem_edgeSet] at hf
              simp only [Sym2.map_mk] at hfe
              rcases Sym2.eq_iff.mp hfe with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
                (simp only [Sum.inl.injEq] at h1 h2; subst h1; subst h2)
              · rw [SimpleGraph.sum_adj]; exact hf
              · rw [SimpleGraph.sum_adj]; exact hf.symm
          · induction f using Sym2.ind with
            | _ p q => simp only [Sym2.map_mk] at hfe; exact absurd hfe (by simp)
      | Sum.inr c, Sum.inr e2 =>
        constructor
        · intro h
          refine Or.inr ⟨s(c, e2), ?_, by simp [Sym2.map_mk]⟩
          rw [mem_edgeSet]; rw [SimpleGraph.sum_adj] at h; exact h
        · rintro (⟨f, hf, hfe⟩ | ⟨f, hf, hfe⟩)
          · induction f using Sym2.ind with
            | _ p q => simp only [Sym2.map_mk] at hfe; exact absurd hfe (by simp)
          · induction f using Sym2.ind with
            | _ p q =>
              rw [mem_edgeSet] at hf
              simp only [Sym2.map_mk] at hfe
              rcases Sym2.eq_iff.mp hfe with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
                (simp only [Sum.inr.injEq] at h1 h2; subst h1; subst h2)
              · rw [SimpleGraph.sum_adj]; exact hf
              · rw [SimpleGraph.sum_adj]; exact hf.symm
      | Sum.inl a, Sum.inr d =>
        constructor
        · intro h; rw [SimpleGraph.sum_adj] at h; exact absurd h not_false
        · rintro (⟨f, hf, hfe⟩ | ⟨f, hf, hfe⟩) <;>
          · induction f using Sym2.ind with
            | _ p q => simp only [Sym2.map_mk] at hfe; exact absurd hfe (by simp)
      | Sum.inr c, Sum.inl b =>
        constructor
        · intro h; rw [SimpleGraph.sum_adj] at h; exact absurd h not_false
        · rintro (⟨f, hf, hfe⟩ | ⟨f, hf, hfe⟩) <;>
          · induction f using Sym2.ind with
            | _ p q => simp only [Sym2.map_mk] at hfe; exact absurd hfe (by simp)
  have hinjL : Function.Injective (Sym2.map (Sum.inl : V → V ⊕ W)) :=
    Sym2.map.injective Sum.inl_injective
  have hinjR : Function.Injective (Sym2.map (Sum.inr : W → V ⊕ W)) :=
    Sym2.map.injective Sum.inr_injective
  have hdisj : Disjoint (G.edgeFinset.image (Sym2.map Sum.inl))
      (H.edgeFinset.image (Sym2.map Sum.inr)) := by
    rw [Finset.disjoint_left]
    intro e he1 he2
    simp only [Finset.mem_image, mem_edgeFinset] at he1 he2
    obtain ⟨f1, _, hf1⟩ := he1
    obtain ⟨f2, _, hf2⟩ := he2
    induction f1 using Sym2.ind with
    | _ p q =>
      induction f2 using Sym2.ind with
      | _ r t =>
        simp only [Sym2.map_mk] at hf1 hf2
        rw [← hf2] at hf1
        rcases Sym2.eq_iff.mp hf1 with ⟨h1, _⟩ | ⟨h1, _⟩ <;> exact absurd h1 (by simp)
  calc (G ⊕g H).edgeFinset.card
      = (G.edgeFinset.image (Sym2.map Sum.inl) ∪ H.edgeFinset.image (Sym2.map Sum.inr)).card := by
          rw [hkey]
    _ = (G.edgeFinset.image (Sym2.map Sum.inl)).card
          + (H.edgeFinset.image (Sym2.map Sum.inr)).card := Finset.card_union_of_disjoint hdisj
    _ = G.edgeFinset.card + H.edgeFinset.card := by
          rw [Finset.card_image_of_injective _ hinjL, Finset.card_image_of_injective _ hinjR]





theorem ecz_partition_edge_card {U : Type*} [Fintype U] [DecidableEq U] (K₀ : SimpleGraph U)
    [DecidableRel K₀.Adj] (P : U → Prop) [DecidablePred P] :
    K₀.edgeFinset.card
      = (agl_left K₀ P).edgeFinset.card + (agl_right K₀ P).edgeFinset.card
        + agl_interfaceCard K₀ P := by
  classical
  have hiso : K₀.edgeFinset.card = (agl_glueGraph K₀ P).edgeFinset.card :=
    (agl_iso K₀ P).card_edgeFinset_eq
  have hci := agl_partitionCrossInterface K₀ P
  have heq := fis_edgeFinset_eq hci
  have hdisj : Disjoint ((agl_left K₀ P ⊕g agl_right K₀ P).edgeFinset)
      (fis_interface (agl_left K₀ P) (agl_right K₀ P) (agl_glueGraph K₀ P)) := by
    rw [fis_interface]; exact Finset.disjoint_sdiff
  rw [hiso, heq, Finset.card_union_of_disjoint hdisj, agl_interfaceCard,
    ecz_sum_edgeFinset_card]












section MultiBlock
variable {U : Type*} [Fintype U] [DecidableEq U] (K₀ : SimpleGraph U) [DecidableRel K₀.Adj]
  {T : Type*} [DecidableEq T] (tag : U → T)




theorem ecz_peel_edge_card (τ : T) (S : Finset T) (hτ : τ ∉ S) :
    (qp_restG K₀ tag (insert τ S)).edgeFinset.card
      = (qp_blkG K₀ tag τ).edgeFinset.card + (qp_restG K₀ tag S).edgeFinset.card
        + agl_interfaceCard (qp_restG K₀ tag (insert τ S)) (fun x => tag x.1 = τ) := by
  have hpc := ecz_partition_edge_card (qp_restG K₀ tag (insert τ S)) (fun x => tag x.1 = τ)
  rw [ecz_left_edge_card K₀ tag τ S hτ, ecz_right_edge_card K₀ tag τ S hτ] at hpc
  exact hpc











theorem ecz_multiblock_subadd (p q : ℝ) (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) :
    ∀ S : Finset T,
      ecz_uu (qp_restG K₀ tag S) p q
        ≤ (∑ τ ∈ S, ecz_uu (qp_blkG K₀ tag τ) p q)
          + (((qp_restG K₀ tag S).edgeFinset.card : ℝ)
              - ∑ τ ∈ S, ((qp_blkG K₀ tag τ).edgeFinset.card : ℝ)) * (-Real.log (1 - p)) := by
  intro S
  induction S using Finset.induction with
  | empty =>
    simp only [Finset.sum_empty, sub_zero]
    haveI : IsEmpty {x : U // tag x ∈ (∅ : Finset T)} := ⟨fun x => by simpa using x.2⟩
    have hcard : (qp_restG K₀ tag (∅ : Finset T)).edgeFinset.card = 0 := by
      rw [Finset.card_eq_zero]
      apply Finset.eq_empty_of_forall_notMem
      intro e he; rw [mem_edgeFinset] at he
      induction e using Sym2.ind with | _ x y => exact isEmptyElim x
    rw [ecz_uu, ecz_fkZEdge_empty, Real.log_one, neg_zero, hcard]
    simp
  | @insert τ S hτ ih =>
    have hpart := ecz_neglog_partition_le (qp_restG K₀ tag (insert τ S))
      (fun x => tag x.1 = τ) hp hp1 hq
    rw [show -Real.log (ecz_fkZEdge (agl_left (qp_restG K₀ tag (insert τ S))
            (fun x => tag x.1 = τ)) p q)
        = ecz_uu (qp_blkG K₀ tag τ) p q from by rw [ecz_uu, ecz_left_eq K₀ tag τ S hτ]] at hpart
    rw [show -Real.log (ecz_fkZEdge (agl_right (qp_restG K₀ tag (insert τ S))
            (fun x => tag x.1 = τ)) p q)
        = ecz_uu (qp_restG K₀ tag S) p q from by rw [ecz_uu, ecz_right_eq K₀ tag τ S hτ]] at hpart
    set c := -Real.log (1 - p) with hc
    set Istep := agl_interfaceCard (qp_restG K₀ tag (insert τ S)) (fun x => tag x.1 = τ) with hIstep
    
    have hedge := ecz_peel_edge_card K₀ tag τ S hτ
    have hedgeR : ((qp_restG K₀ tag (insert τ S)).edgeFinset.card : ℝ)
        = ((qp_blkG K₀ tag τ).edgeFinset.card : ℝ) + ((qp_restG K₀ tag S).edgeFinset.card : ℝ)
          + (Istep : ℝ) := by rw [← hIstep] at hedge; exact_mod_cast hedge
    
    have huu : ecz_uu (qp_restG K₀ tag (insert τ S)) p q
        ≤ ecz_uu (qp_blkG K₀ tag τ) p q + ecz_uu (qp_restG K₀ tag S) p q + (Istep : ℝ) * c := by
      have : ecz_uu (qp_restG K₀ tag (insert τ S)) p q
          ≤ ecz_uu (qp_blkG K₀ tag τ) p q + ecz_uu (qp_restG K₀ tag S) p q
            - (Istep : ℝ) * Real.log (1 - p) := by rw [ecz_uu]; exact hpart
      rw [hc]; linarith [this]
    rw [Finset.sum_insert hτ, Finset.sum_insert hτ]
    set A : ℝ := ecz_uu (qp_blkG K₀ tag τ) p q with hA
    set B : ℝ := ∑ σ ∈ S, ecz_uu (qp_blkG K₀ tag σ) p q with hB
    set CardI : ℝ := ((qp_restG K₀ tag (insert τ S)).edgeFinset.card : ℝ) with hCardI
    set CardS : ℝ := ((qp_restG K₀ tag S).edgeFinset.card : ℝ) with hCardS
    set Cblk : ℝ := ((qp_blkG K₀ tag τ).edgeFinset.card : ℝ) with hCblk
    set Csum : ℝ := ∑ σ ∈ S, ((qp_blkG K₀ tag σ).edgeFinset.card : ℝ) with hCsum
    
    have hih : ecz_uu (qp_restG K₀ tag S) p q ≤ B + (CardS - Csum) * c := by rw [hc]; exact ih
    
    have hcoeff : (CardI - (Cblk + Csum)) * c = (Istep : ℝ) * c + (CardS - Csum) * c := by
      rw [hedgeR]; ring
    rw [hcoeff]
    calc ecz_uu (qp_restG K₀ tag (insert τ S)) p q
        ≤ A + ecz_uu (qp_restG K₀ tag S) p q + (Istep : ℝ) * c := huu
      _ ≤ A + (B + (CardS - Csum) * c) + (Istep : ℝ) * c := by linarith [hih]
      _ = A + B + ((Istep : ℝ) * c + (CardS - Csum) * c) := by ring

end MultiBlock








theorem ecz_box_annulus_card (a n : ℕ) (hle : a ≤ n) :
    (agl_interfaceCard (boxGraph d n) (ecz_subBoxPred d a n)
        + (agl_right (boxGraph d n) (ecz_subBoxPred d a n)).edgeFinset.card)
      + (boxGraph d a).edgeFinset.card = (boxGraph d n).edgeFinset.card := by
  classical
  have hpc := ecz_partition_edge_card (boxGraph d n) (ecz_subBoxPred d a n)
  have hleftcard : (agl_left (boxGraph d n) (ecz_subBoxPred d a n)).edgeFinset.card
      = (boxGraph d a).edgeFinset.card := (ecz_subBoxIso a n hle).card_edgeFinset_eq.symm
  rw [hleftcard] at hpc
  omega








theorem ecz_box_nesting_le' (a n : ℕ) (hle : a ≤ n) (t : ℝ) :
    ecz_u d t n ≤ ecz_u d t a
      + (((boxGraph d n).edgeFinset.card : ℝ) - ((boxGraph d a).edgeFinset.card : ℝ))
          * (-Real.log (1 - fsc_logistic t)) := by
  have hnest := ecz_box_nesting_le (d := d) a n hle t
  have hcard := ecz_box_annulus_card (d := d) a n hle
  have hcardR : ((agl_interfaceCard (boxGraph d n) (ecz_subBoxPred d a n) : ℝ)
      + ((agl_right (boxGraph d n) (ecz_subBoxPred d a n)).edgeFinset.card : ℝ))
      = ((boxGraph d n).edgeFinset.card : ℝ) - ((boxGraph d a).edgeFinset.card : ℝ) := by
    have hc : ((agl_interfaceCard (boxGraph d n) (ecz_subBoxPred d a n)
        + (agl_right (boxGraph d n) (ecz_subBoxPred d a n)).edgeFinset.card : ℕ) : ℝ)
        + ((boxGraph d a).edgeFinset.card : ℝ) = ((boxGraph d n).edgeFinset.card : ℝ) := by
      exact_mod_cast congrArg (Nat.cast : ℕ → ℝ) hcard
    push_cast at hc ⊢; linarith
  rw [hcardR] at hnest
  exact hnest









theorem ecz_box_nesting_sandwich (a n b : ℕ) (han : a ≤ n) (hnb : n ≤ b) (t : ℝ) :
    ecz_u d t b
        - ((agl_interfaceCard (boxGraph d b) (ecz_subBoxPred d n b)
            + ((agl_right (boxGraph d b) (ecz_subBoxPred d n b)).edgeFinset.card : ℝ)))
            * (-Real.log (1 - fsc_logistic t))
        ≤ ecz_u d t n
      ∧ ecz_u d t n ≤ ecz_u d t a
        + ((agl_interfaceCard (boxGraph d n) (ecz_subBoxPred d a n)
            + ((agl_right (boxGraph d n) (ecz_subBoxPred d a n)).edgeFinset.card : ℝ)))
            * (-Real.log (1 - fsc_logistic t)) := by
  have hb := ecz_box_nesting_le (d := d) n b hnb t
  have ha := ecz_box_nesting_le (d := d) a n han t
  exact ⟨by linarith [hb], ha⟩







theorem ecz_box_nesting_sandwich' (a n b : ℕ) (han : a ≤ n) (hnb : n ≤ b) (t : ℝ) :
    ecz_u d t b
        - (((boxGraph d b).edgeFinset.card : ℝ) - ((boxGraph d n).edgeFinset.card : ℝ))
            * (-Real.log (1 - fsc_logistic t))
        ≤ ecz_u d t n
      ∧ ecz_u d t n ≤ ecz_u d t a
        + (((boxGraph d n).edgeFinset.card : ℝ) - ((boxGraph d a).edgeFinset.card : ℝ))
            * (-Real.log (1 - fsc_logistic t)) := by
  have hb := ecz_box_nesting_le' (d := d) n b hnb t
  have ha := ecz_box_nesting_le' (d := d) a n han t
  exact ⟨by linarith [hb], ha⟩
























def ecz_PerEdgeDensityConverges (d : ℕ) (s : ℝ) : Prop :=
  ∃ ρ : ℝ, Tendsto (fun n => ecz_u d s n / ((boxGraph d n).edgeFinset.card : ℝ)) atTop (𝓝 ρ)

section VanHove
variable {d : ℕ}



def ecz_T (m n : ℕ) : ℕ := (2 * n + 1) / (2 * m + 1)


theorem ecz_T_mul_le (m n : ℕ) : ecz_T m n * (2 * m + 1) ≤ 2 * n + 1 :=
  Nat.div_mul_le_self _ _



def ecz_center (m n : ℕ) (c : Fin d → Fin (ecz_T m n)) : Site d :=
  fun i => (c i : ℤ) * (2 * m + 1) + (m : ℤ) - (n : ℤ)




theorem ecz_center_mem_box (m n : ℕ) (c : Fin d → Fin (ecz_T m n)) (y : Site d)
    (hy : y ∈ box d m) : (fun i => y i + ecz_center m n c i) ∈ box d n := by
  rw [mem_box]
  intro i
  rw [qp_natAbs_iff]
  have hyi : -(m : ℤ) ≤ y i ∧ y i ≤ m := (qp_natAbs_iff (y i) m).mp (hy i)
  have hci : (c i : ℕ) < ecz_T m n := (c i).2
  have hcT : ((c i : ℤ)) * (2 * m + 1) + (2 * m + 1) ≤ 2 * n + 1 := by
    have h1 : ((c i : ℕ) + 1) * (2 * m + 1) ≤ ecz_T m n * (2 * m + 1) := by
      apply Nat.mul_le_mul_right; omega
    have h2 : ecz_T m n * (2 * m + 1) ≤ 2 * n + 1 := ecz_T_mul_le m n
    have h3 : ((c i : ℕ) + 1) * (2 * m + 1) ≤ 2 * n + 1 := le_trans h1 h2
    have : (((c i : ℕ) + 1) * (2 * m + 1) : ℤ) ≤ ((2 * n + 1 : ℕ) : ℤ) := by exact_mod_cast h3
    push_cast at this ⊢; nlinarith [this]
  have hc0 : (0 : ℤ) ≤ (c i : ℤ) := Int.ofNat_nonneg _
  simp only [ecz_center]
  constructor
  · nlinarith [hyi.1, hc0]
  · nlinarith [hyi.2, hcT]



def ecz_cellIdx (m n : ℕ) (x : Site d) (i : Fin d) : ℕ := ((x i + n).toNat) / (2 * m + 1)




noncomputable def ecz_vanHoveTag (m n : ℕ) (x : boxVerts d n) :
    Option (Fin d → Fin (ecz_T m n)) :=
  if h : ∀ i, ecz_cellIdx m n (x : Site d) i < ecz_T m n then
    some (fun i => ⟨ecz_cellIdx m n (x : Site d) i, h i⟩)
  else none




theorem ecz_vanHoveTag_eq_some_iff (m n : ℕ) (x : boxVerts d n) (c : Fin d → Fin (ecz_T m n)) :
    ecz_vanHoveTag m n x = some c
      ↔ ∀ i, ((x : Site d) i - ecz_center m n c i).natAbs ≤ m := by
  have hxn : ∀ i, 0 ≤ (x : Site d) i + (n : ℤ) := by
    intro i; have := (qp_natAbs_iff ((x : Site d) i) n).mp (x.2 i); linarith [this.1]
  unfold ecz_vanHoveTag
  constructor
  · intro h
    split_ifs at h with hcond
    · intro i
      have hci : (fun i => (⟨ecz_cellIdx m n (x : Site d) i, hcond i⟩ : Fin (ecz_T m n))) = c :=
        Option.some.inj h
      have hidx : ecz_cellIdx m n (x : Site d) i = (c i : ℕ) := by
        have := congrArg (fun f => (f i : ℕ)) hci; simpa using this
      
      rw [ecz_cellIdx] at hidx
      have h2m1 : 0 < 2 * m + 1 := by omega
      have hlow : (c i : ℕ) * (2 * m + 1) ≤ ((x : Site d) i + n).toNat :=
        hidx ▸ Nat.div_mul_le_self _ _
      have hhigh : ((x : Site d) i + n).toNat < ((c i : ℕ) + 1) * (2 * m + 1) := by
        rw [← hidx]
        have hdm := Nat.div_add_mod ((x : Site d) i + n).toNat (2 * m + 1)
        have hmod := Nat.mod_lt ((x : Site d) i + n).toNat h2m1
        nlinarith [hdm, hmod]
      have htoNat : (((x : Site d) i + n).toNat : ℤ) = (x : Site d) i + n :=
        Int.toNat_of_nonneg (hxn i)
      rw [qp_natAbs_iff]
      simp only [ecz_center]
      have hlowZ : ((c i : ℕ) : ℤ) * (2 * m + 1) ≤ (x : Site d) i + n := by
        have : (((c i : ℕ) * (2 * m + 1) : ℕ) : ℤ) ≤ (((x : Site d) i + n).toNat : ℤ) := by
          exact_mod_cast hlow
        rw [htoNat] at this; push_cast at this ⊢; linarith
      have hhighZ : (x : Site d) i + n < ((c i : ℕ) + 1 : ℤ) * (2 * m + 1) := by
        have : (((x : Site d) i + n).toNat : ℤ) < ((((c i : ℕ) + 1) * (2 * m + 1) : ℕ) : ℤ) := by
          exact_mod_cast hhigh
        rw [htoNat] at this; push_cast at this ⊢; linarith
      push_cast at hlowZ hhighZ ⊢
      constructor <;> nlinarith [hlowZ, hhighZ]
  · intro h
    have h2m1 : 0 < 2 * m + 1 := by omega
    
    have hidx : ∀ i, ecz_cellIdx m n (x : Site d) i = (c i : ℕ) := by
      intro i
      have hi := h i
      rw [qp_natAbs_iff] at hi
      simp only [ecz_center] at hi
      have htoNat : (((x : Site d) i + n).toNat : ℤ) = (x : Site d) i + n :=
        Int.toNat_of_nonneg (hxn i)
      
      have hlowZ : ((c i : ℤ)) * (2 * m + 1) ≤ (x : Site d) i + n := by push_cast at hi ⊢; nlinarith [hi.1]
      have hhighZ : (x : Site d) i + n < ((c i : ℤ) + 1) * (2 * m + 1) := by push_cast at hi ⊢; nlinarith [hi.2]
      rw [ecz_cellIdx]
      have hlowN : (c i : ℕ) * (2 * m + 1) ≤ ((x : Site d) i + n).toNat := by
        have : (((c i : ℕ) * (2 * m + 1) : ℕ) : ℤ) ≤ (((x : Site d) i + n).toNat : ℤ) := by
          rw [htoNat]; push_cast; linarith [hlowZ]
        exact_mod_cast this
      have hhighN : ((x : Site d) i + n).toNat < ((c i : ℕ) + 1) * (2 * m + 1) := by
        have : (((x : Site d) i + n).toNat : ℤ) < ((((c i : ℕ) + 1) * (2 * m + 1) : ℕ) : ℤ) := by
          rw [htoNat]; push_cast; linarith [hhighZ]
        exact_mod_cast this
      rw [Nat.div_eq_of_lt_le hlowN hhighN]
    have hcond : ∀ i, ecz_cellIdx m n (x : Site d) i < ecz_T m n := fun i => by
      rw [hidx i]; exact (c i).2
    rw [dif_pos hcond]
    congr 1
    funext i; apply Fin.ext; simpa using hidx i




noncomputable def ecz_cellEquiv (m n : ℕ) (c : Fin d → Fin (ecz_T m n)) :
    boxVerts d m ≃ {x : boxVerts d n // ecz_vanHoveTag m n x = some c} where
  toFun y := ⟨⟨fun i => (y : Site d) i + ecz_center m n c i,
      ecz_center_mem_box m n c (y : Site d) y.2⟩, by
    rw [ecz_vanHoveTag_eq_some_iff]; intro i; simp only [add_sub_cancel_right]
    exact (qp_natAbs_iff ((y : Site d) i) m).mpr ((qp_natAbs_iff ((y : Site d) i) m).mp (y.2 i))⟩
  invFun x := ⟨fun i => ((x : boxVerts d n) : Site d) i - ecz_center m n c i, by
    have h := (ecz_vanHoveTag_eq_some_iff m n x.1 c).mp x.2
    intro i; exact h i⟩
  left_inv y := by apply Subtype.ext; funext i; simp
  right_inv x := by
    apply Subtype.ext; apply Subtype.ext; funext i; simp




noncomputable def ecz_cellBlockIso (m n : ℕ) (c : Fin d → Fin (ecz_T m n)) :
    boxGraph d m ≃g qp_blkG (boxGraph d n) (ecz_vanHoveTag m n) (some c) where
  toEquiv := ecz_cellEquiv m n c
  map_rel_iff' := by
    intro y z
    show (qp_blkG (boxGraph d n) (ecz_vanHoveTag m n) (some c)).Adj
        (ecz_cellEquiv m n c y) (ecz_cellEquiv m n c z) ↔ (boxGraph d m).Adj y z
    unfold qp_blkG boxGraph
    simp only [comap_adj]
    show (hypercubicLattice d).Adj
        (fun i => (y : Site d) i + ecz_center m n c i) (fun i => (z : Site d) i + ecz_center m n c i)
      ↔ (hypercubicLattice d).Adj (y : Site d) (z : Site d)
    exact agl_nn_translate d (ecz_center m n c) (y : Site d) (z : Site d)


theorem ecz_cellBlock_fkZEdge (m n : ℕ) (c : Fin d → Fin (ecz_T m n)) (p q : ℝ) :
    ecz_fkZEdge (qp_blkG (boxGraph d n) (ecz_vanHoveTag m n) (some c)) p q
      = ecz_fkZEdge (boxGraph d m) p q :=
  (ecz_fkZEdge_iso (ecz_cellBlockIso m n c) p q).symm


theorem ecz_cellBlock_edge_card (m n : ℕ) (c : Fin d → Fin (ecz_T m n)) :
    (qp_blkG (boxGraph d n) (ecz_vanHoveTag m n) (some c)).edgeFinset.card
      = (boxGraph d m).edgeFinset.card :=
  ((ecz_cellBlockIso m n c).card_edgeFinset_eq).symm


theorem ecz_cell_card (m n : ℕ) : Fintype.card (Fin d → Fin (ecz_T m n)) = (ecz_T m n) ^ d := by
  rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]



noncomputable def ecz_restUnivIso (m n : ℕ) :
    qp_restG (boxGraph d n) (ecz_vanHoveTag m n) Finset.univ ≃g boxGraph d n where
  toEquiv := Equiv.subtypeUnivEquiv (fun x => Finset.mem_univ (ecz_vanHoveTag m n x))
  map_rel_iff' := by intro a b; rfl











theorem ecz_box_vanHove_subadd (m n : ℕ) (t : ℝ) :
    ecz_u d t n ≤ ((ecz_T m n) ^ d : ℝ) * ecz_u d t m
      + (((boxGraph d n).edgeFinset.card : ℝ)
          - ((ecz_T m n) ^ d : ℝ) * ((boxGraph d m).edgeFinset.card : ℝ))
          * (-Real.log (1 - fsc_logistic t)) := by
  classical
  set p := fsc_logistic t with hp
  have hp0 : (0 : ℝ) < p := fsc_logistic_pos t
  have hp1 : p < 1 := fsc_logistic_lt_one t
  set c := -Real.log (1 - p) with hc
  have hc0 : 0 ≤ c := by rw [hc, neg_nonneg]; exact Real.log_nonpos (by linarith) (by linarith)
  set tag := ecz_vanHoveTag m n with htag
  set K₀ := boxGraph d n with hK₀
  
  have hsub := ecz_multiblock_subadd K₀ tag p 2 hp0 hp1 (by norm_num : (0:ℝ) < 2) Finset.univ
  
  have hrest_u : ecz_uu (qp_restG K₀ tag Finset.univ) p 2 = ecz_u d t n := by
    rw [ecz_uu, ecz_u, hp, ecz_fkZEdge_iso (ecz_restUnivIso m n) p 2]
  have hrest_E : ((qp_restG K₀ tag Finset.univ).edgeFinset.card : ℝ)
      = ((boxGraph d n).edgeFinset.card : ℝ) := by
    rw [(ecz_restUnivIso m n).card_edgeFinset_eq]
  
  have hsplit_u : (∑ τ : Option (Fin d → Fin (ecz_T m n)), ecz_uu (qp_blkG K₀ tag τ) p 2)
      = ecz_uu (qp_blkG K₀ tag none) p 2
        + ((ecz_T m n) ^ d : ℝ) * ecz_u d t m := by
    rw [Fintype.sum_option]
    congr 1
    have heach : ∀ c : Fin d → Fin (ecz_T m n),
        ecz_uu (qp_blkG K₀ tag (some c)) p 2 = ecz_u d t m := fun c => by
      rw [ecz_uu, ecz_u, hp, ecz_cellBlock_fkZEdge m n c]
    rw [Finset.sum_congr rfl (fun c _ => heach c), Finset.sum_const, Finset.card_univ,
      ecz_cell_card, nsmul_eq_mul]
    push_cast; ring
  have hsplit_E : (∑ τ : Option (Fin d → Fin (ecz_T m n)),
        ((qp_blkG K₀ tag τ).edgeFinset.card : ℝ))
      = ((qp_blkG K₀ tag none).edgeFinset.card : ℝ)
        + ((ecz_T m n) ^ d : ℝ) * ((boxGraph d m).edgeFinset.card : ℝ) := by
    rw [Fintype.sum_option]
    congr 1
    have heach : ∀ c : Fin d → Fin (ecz_T m n),
        ((qp_blkG K₀ tag (some c)).edgeFinset.card : ℝ) = ((boxGraph d m).edgeFinset.card : ℝ) :=
      fun c => by rw [ecz_cellBlock_edge_card m n c]
    rw [Finset.sum_congr rfl (fun c _ => heach c), Finset.sum_const, Finset.card_univ,
      ecz_cell_card, nsmul_eq_mul]
    push_cast; ring
  
  have hnone : ecz_uu (qp_blkG K₀ tag none) p 2
      ≤ ((qp_blkG K₀ tag none).edgeFinset.card : ℝ) * c := by
    rw [ecz_uu, hc]; exact ecz_neglogZEdge_le_edges _ hp0 hp1 (by norm_num : (1:ℝ) ≤ 2)
  
  rw [show (∑ τ ∈ (Finset.univ : Finset (Option (Fin d → Fin (ecz_T m n)))),
        ecz_uu (qp_blkG K₀ tag τ) p 2)
      = ∑ τ : Option (Fin d → Fin (ecz_T m n)), ecz_uu (qp_blkG K₀ tag τ) p 2 from rfl] at hsub
  rw [show (∑ τ ∈ (Finset.univ : Finset (Option (Fin d → Fin (ecz_T m n)))),
        ((qp_blkG K₀ tag τ).edgeFinset.card : ℝ))
      = ∑ τ : Option (Fin d → Fin (ecz_T m n)), ((qp_blkG K₀ tag τ).edgeFinset.card : ℝ) from rfl]
    at hsub
  rw [hrest_u, hsplit_u, hrest_E, hsplit_E] at hsub
  
  set uNone : ℝ := ecz_uu (qp_blkG K₀ tag none) p 2 with huNone
  set ENone : ℝ := ((qp_blkG K₀ tag none).edgeFinset.card : ℝ) with hENone
  set Td : ℝ := ((ecz_T m n) ^ d : ℝ) with hTd
  set Um : ℝ := ecz_u d t m with hUm
  set Em : ℝ := ((boxGraph d m).edgeFinset.card : ℝ) with hEm
  set En : ℝ := ((boxGraph d n).edgeFinset.card : ℝ) with hEn
  
  
  
  have hexpand : (En - (ENone + Td * Em)) * c = (En - Td * Em) * c - ENone * c := by ring
  rw [hexpand] at hsub
  linarith [hsub, hnone]











theorem ecz_denom_tendsto_atTop :
    Tendsto (fun n : ℕ => (2 * (n : ℝ) + 1)) atTop atTop := by
  apply Filter.tendsto_atTop_add_const_right
  exact Tendsto.const_mul_atTop (by norm_num) tendsto_natCast_atTop_atTop


theorem ecz_packing_ratio_tendsto (m : ℕ) :
    Tendsto (fun n => ((ecz_T m n : ℝ) * (2 * m + 1)) / (2 * n + 1)) atTop (𝓝 1) := by
  have hupper : ∀ n, ((ecz_T m n : ℝ) * (2 * m + 1)) / (2 * n + 1) ≤ 1 := by
    intro n
    have hden : (0 : ℝ) < 2 * n + 1 := by positivity
    rw [div_le_one hden]
    have : (ecz_T m n * (2 * m + 1) : ℕ) ≤ 2 * n + 1 := ecz_T_mul_le m n
    exact_mod_cast this
  have h0 : Tendsto (fun n : ℕ => (2 * (m : ℝ) + 1) / (2 * n + 1)) atTop (𝓝 0) :=
    (tendsto_const_nhds (x := (2 * (m : ℝ) + 1))).div_atTop ecz_denom_tendsto_atTop
  have hlowfun : Tendsto (fun n : ℕ => 1 - (2 * (m : ℝ) + 1) / (2 * n + 1)) atTop (𝓝 1) := by
    have := h0.const_sub (1 : ℝ); simpa using this
  have hlower : ∀ n : ℕ, 1 - (2 * (m : ℝ) + 1) / (2 * n + 1)
      ≤ ((ecz_T m n : ℝ) * (2 * m + 1)) / (2 * n + 1) := by
    intro n
    have hden : (0 : ℝ) < 2 * n + 1 := by positivity
    
    have hT1 : 2 * n + 1 < (ecz_T m n + 1) * (2 * m + 1) := by
      have hdm := Nat.div_add_mod (2 * n + 1) (2 * m + 1)
      have hmod := Nat.mod_lt (2 * n + 1) (show 0 < 2 * m + 1 by omega)
      rw [ecz_T]; nlinarith [hdm, hmod]
    have hT1R : (2 * (n : ℝ) + 1) < ((ecz_T m n : ℝ) + 1) * (2 * m + 1) := by
      have : ((2 * n + 1 : ℕ) : ℝ) < (((ecz_T m n + 1) * (2 * m + 1) : ℕ) : ℝ) := by
        exact_mod_cast hT1
      push_cast at this ⊢; linarith
    rw [le_div_iff₀ hden, sub_mul, div_mul_cancel₀ _ (ne_of_gt hden)]
    nlinarith [hT1R]
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le hlowfun tendsto_const_nhds hlower hupper


theorem ecz_oddEven_ratio_tendsto :
    Tendsto (fun n : ℕ => (2 * (n : ℝ) + 1) / (2 * n)) atTop (𝓝 1) := by
  have hden : Tendsto (fun n : ℕ => (2 * (n : ℝ))) atTop atTop :=
    Tendsto.const_mul_atTop (by norm_num) tendsto_natCast_atTop_atTop
  have h0 : Tendsto (fun n : ℕ => 1 / (2 * (n : ℝ))) atTop (𝓝 0) :=
    (tendsto_const_nhds (x := (1 : ℝ))).div_atTop hden
  have heq : ∀ n : ℕ, 1 ≤ n → (2 * (n : ℝ) + 1) / (2 * n) = 1 + 1 / (2 * n) := by
    intro n hn
    have hden0 : (0 : ℝ) < 2 * n := by
      have : (1 : ℝ) ≤ n := by exact_mod_cast hn
      positivity
    field_simp
  have hlim : Tendsto (fun n : ℕ => 1 + 1 / (2 * (n : ℝ))) atTop (𝓝 1) := by
    have := h0.const_add (1 : ℝ); simpa using this
  refine (Filter.tendsto_congr' ?_).mpr hlim
  filter_upwards [Filter.eventually_ge_atTop 1] with n hn using (heq n hn)







theorem ecz_bulkFraction_tendsto (hd : 1 ≤ d) (m : ℕ) (hm : 1 ≤ m) :
    Tendsto (fun n => ((ecz_T m n) ^ d : ℝ) * ((boxGraph d m).edgeFinset.card : ℝ)
        / ((boxGraph d n).edgeFinset.card : ℝ)) atTop
      (𝓝 (2 * (m : ℝ) / (2 * m + 1))) := by
  
  have hprod : Tendsto (fun n => (((ecz_T m n : ℝ) * (2 * m + 1)) / (2 * n + 1)) ^ d
        * (2 * (m : ℝ) / (2 * m + 1)) * ((2 * (n : ℝ) + 1) / (2 * n))) atTop
      (𝓝 ((1 : ℝ) ^ d * (2 * (m : ℝ) / (2 * m + 1)) * 1)) := by
    refine ((((ecz_packing_ratio_tendsto m).pow d).mul tendsto_const_nhds).mul
      ecz_oddEven_ratio_tendsto)
  rw [one_pow, one_mul, mul_one] at hprod
  refine (Filter.tendsto_congr' ?_).mp hprod
  
  filter_upwards [Filter.eventually_ge_atTop 1] with n hn
  have hnpos : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hM1 : (0 : ℝ) < 2 * m + 1 := by positivity
  have h2n : (0 : ℝ) < 2 * n := by positivity
  have h2n1 : (0 : ℝ) < 2 * n + 1 := by positivity
  
  obtain ⟨e, rfl⟩ : ∃ e, d = e + 1 := ⟨d - 1, by omega⟩
  
  have hEm : ((boxGraph (e + 1) m).edgeFinset.card : ℝ)
      = ((e : ℝ) + 1) * (2 * m) * (2 * (m : ℝ) + 1) ^ e := by
    rw [EdgeCount.boxGraph_edgeCard (e + 1) m hd]; push_cast; ring_nf
  have hEn : ((boxGraph (e + 1) n).edgeFinset.card : ℝ)
      = ((e : ℝ) + 1) * (2 * n) * (2 * (n : ℝ) + 1) ^ e := by
    rw [EdgeCount.boxGraph_edgeCard (e + 1) n hd]; push_cast; ring_nf
  rw [hEm, hEn, div_pow, mul_pow, pow_succ (2 * (m : ℝ) + 1) e, pow_succ (2 * (n : ℝ) + 1) e]
  have hpowMp : (0 : ℝ) < (2 * (m : ℝ) + 1) ^ e := by positivity
  have hpowNp : (0 : ℝ) < (2 * (n : ℝ) + 1) ^ e := by positivity
  have hepos : (0 : ℝ) < (e : ℝ) + 1 := by positivity
  field_simp












noncomputable def ecz_f (d : ℕ) (s : ℝ) (n : ℕ) : ℝ :=
  ecz_u d s n / ((boxGraph d n).edgeFinset.card : ℝ)




theorem ecz_perEdge_vanHove (m n : ℕ) (s : ℝ)
    (hEn : 0 < (boxGraph d n).edgeFinset.card) (hEm : 0 < (boxGraph d m).edgeFinset.card) :
    ecz_f d s n
      ≤ (((ecz_T m n) ^ d : ℝ) * ((boxGraph d m).edgeFinset.card : ℝ)
            / ((boxGraph d n).edgeFinset.card : ℝ)) * ecz_f d s m
        + (1 - ((ecz_T m n) ^ d : ℝ) * ((boxGraph d m).edgeFinset.card : ℝ)
            / ((boxGraph d n).edgeFinset.card : ℝ)) * (-Real.log (1 - fsc_logistic s)) := by
  set c := -Real.log (1 - fsc_logistic s) with hc
  have hEnR : (0 : ℝ) < ((boxGraph d n).edgeFinset.card : ℝ) := by exact_mod_cast hEn
  have hEmR : (0 : ℝ) < ((boxGraph d m).edgeFinset.card : ℝ) := by exact_mod_cast hEm
  have hsub := ecz_box_vanHove_subadd (d := d) m n s
  rw [← hc] at hsub
  
  rw [ecz_f, ecz_f]
  set En : ℝ := ((boxGraph d n).edgeFinset.card : ℝ) with hEnDef
  set Em : ℝ := ((boxGraph d m).edgeFinset.card : ℝ) with hEmDef
  set Td : ℝ := ((ecz_T m n) ^ d : ℝ) with hTd
  rw [div_le_iff₀ hEnR]
  
  have hEmne : Em ≠ 0 := ne_of_gt hEmR
  have hkey : (Td * Em / En * (ecz_u d s m / Em) + (1 - Td * Em / En) * c) * En
      = Td * ecz_u d s m + (En - Td * Em) * c := by
    field_simp
  calc ecz_u d s n ≤ Td * ecz_u d s m + (En - Td * Em) * c := hsub
    _ = (Td * Em / En * (ecz_u d s m / Em) + (1 - Td * Em / En) * c) * En := hkey.symm







theorem ecz_dyadic_f_tendsto (hd : 1 ≤ d) (s : ℝ)
    (hbox : ∀ j, 0 < (boxGraph d (agl_K j)).edgeFinset.card) :
    ∃ L : ℝ, Tendsto (fun j => ecz_f d s (agl_K j)) atTop (𝓝 L) := by
  classical
  obtain ⟨I, hInn, hIsum, hudbl, hEdge⟩ := ecz_additiveDoublingBound d hd s
  set c : ℝ := -Real.log (1 - fsc_logistic s) with hc
  have hp1 : fsc_logistic s < 1 := fsc_logistic_lt_one s
  have hp0 : (0:ℝ) < fsc_logistic s := fsc_logistic_pos s
  have hc0 : 0 ≤ c := by rw [hc, neg_nonneg]; exact Real.log_nonpos (by linarith) (by linarith)
  have hEpos : ∀ j, 0 < agl_E d (agl_K j) := fun j => by
    unfold agl_E; exact_mod_cast hbox j
  set M : ℝ := 3 * Real.log 2 + c with hM
  have hMc0 : 0 ≤ M + c := by
    rw [hM]; have hl2 : (0:ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num); linarith
  have hIE0 : ∀ j, 0 ≤ I j / agl_E d (agl_K (j + 1)) := fun j =>
    div_nonneg (hInn j) (hEpos (j + 1)).le
  set δ : ℕ → ℝ := fun j => (M + c) * (I j / agl_E d (agl_K (j + 1))) with hδ
  
  have hmono : ∀ j, ecz_edgeFreeEnergy d s (agl_K j) - δ j ≤ ecz_edgeFreeEnergy d s (agl_K (j + 1)) := by
    intro j
    rw [ecz_edgeFE_eq s (agl_K j), ecz_edgeFE_eq s (agl_K (j + 1))]
    have hstep := bxt_perVolume_doubling_step (a := ecz_u d s (agl_K j))
      (A := ecz_u d s (agl_K (j + 1))) (e := agl_E d (agl_K j)) (E := agl_E d (agl_K (j + 1)))
      (K := (2 : ℝ) ^ d) (c := c) (i := I j)
      (hEpos j) (hEpos (j + 1)) hc0 (hInn j) (hudbl j) (hEdge j)
    have hl2 : (0:ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    have hupper : -(ecz_u d s (agl_K j) / agl_E d (agl_K j)) ≤ 3 * Real.log 2 := by
      have h := ecz_edgeFE_le_const d (agl_K j) hd (agl_K_pos j) s (hbox j)
      rw [ecz_edgeFE_eq] at h; linarith
    have hlower : ecz_u d s (agl_K j) / agl_E d (agl_K j) ≤ c := by
      have hEr : (0:ℝ) < agl_E d (agl_K j) := hEpos j
      have hge := ecz_neglogZEdge_le_edges (boxGraph d (agl_K j)) hp0 hp1 (by norm_num : (1:ℝ) ≤ 2)
      rw [div_le_iff₀ hEr]
      show ecz_u d s (agl_K j) ≤ c * agl_E d (agl_K j)
      have : ecz_u d s (agl_K j) ≤ agl_E d (agl_K j) * c := by
        simpa [ecz_u, agl_E, hc] using hge
      linarith [mul_comm (agl_E d (agl_K j)) c, this]
    have huEbd : |ecz_u d s (agl_K j)| / agl_E d (agl_K j) ≤ M := by
      have hquot : |ecz_u d s (agl_K j)| / agl_E d (agl_K j)
          = |ecz_u d s (agl_K j) / agl_E d (agl_K j)| := by
        rw [abs_div, abs_of_pos (hEpos j)]
      rw [hquot, abs_le]
      exact ⟨by rw [hM]; linarith [hupper, hc0], by rw [hM]; linarith [hlower, hl2]⟩
    have hdefle : (|ecz_u d s (agl_K j)| / agl_E d (agl_K j) + c)
        * (I j / agl_E d (agl_K (j + 1))) ≤ δ j := by
      show _ ≤ (M + c) * (I j / agl_E d (agl_K (j + 1)))
      apply mul_le_mul_of_nonneg_right _ (hIE0 j)
      linarith [huEbd]
    have hgoal : -(ecz_u d s (agl_K j) / agl_E d (agl_K j)) - δ j
        ≤ -(ecz_u d s (agl_K (j + 1)) / agl_E d (agl_K (j + 1))) := by linarith [hstep, hdefle]
    linarith
  
  have hbdd : BddAbove (Set.range fun j => ecz_edgeFreeEnergy d s (agl_K j)) := by
    refine ⟨3 * Real.log 2 + Real.log (1 + Real.exp s), ?_⟩
    rintro x ⟨j, rfl⟩
    simp only
    exact ecz_edgeFE_le_const d (agl_K j) hd (agl_K_pos j) s (hbox j)
  
  obtain ⟨L', hL'⟩ := agl_subseq_almost_mono_converges
    (fun n => ecz_edgeFreeEnergy d s n) agl_K δ
    (fun j => mul_nonneg hMc0 (hIE0 j)) (hIsum.mul_left (M + c)) hmono hbdd
  refine ⟨Real.log (1 + Real.exp s) - L', ?_⟩
  have heq : ∀ j, ecz_f d s (agl_K j)
      = Real.log (1 + Real.exp s) - ecz_edgeFreeEnergy d s (agl_K j) := by
    intro j; rw [ecz_f, ecz_edgeFE_eq, agl_E]; ring
  rw [show (fun j => ecz_f d s (agl_K j))
      = (fun j => Real.log (1 + Real.exp s) - ecz_edgeFreeEnergy d s (agl_K j)) from
    funext heq]
  have := (hL'.const_sub (Real.log (1 + Real.exp s)))
  simpa using this




theorem ecz_f_bounds (hd : 1 ≤ d) (s : ℝ) (n : ℕ) (hn : 1 ≤ n)
    (hEn : 0 < (boxGraph d n).edgeFinset.card) :
    -(3 * Real.log 2) ≤ ecz_f d s n ∧ ecz_f d s n ≤ -Real.log (1 - fsc_logistic s) := by
  set c := -Real.log (1 - fsc_logistic s) with hc
  have hp0 : (0:ℝ) < fsc_logistic s := fsc_logistic_pos s
  have hp1 : fsc_logistic s < 1 := fsc_logistic_lt_one s
  have hEnR : (0 : ℝ) < ((boxGraph d n).edgeFinset.card : ℝ) := by exact_mod_cast hEn
  refine ⟨?_, ?_⟩
  · 
    have h := ecz_edgeFE_le_const d n hd hn s hEn
    rw [ecz_edgeFE_eq, agl_E] at h
    rw [ecz_f]
    have hlog1 : (0:ℝ) ≤ Real.log (1 + Real.exp s) :=
      Real.log_nonneg (by have := Real.exp_pos s; linarith)
    linarith
  · 
    have hge := ecz_neglogZEdge_le_edges (boxGraph d n) hp0 hp1 (by norm_num : (1:ℝ) ≤ 2)
    rw [ecz_f, div_le_iff₀ hEnR]
    have : ecz_u d s n ≤ ((boxGraph d n).edgeFinset.card : ℝ) * c := by
      simpa [ecz_u, hc] using hge
    linarith [this, mul_comm ((boxGraph d n).edgeFinset.card : ℝ) c]









theorem ecz_f_lower (hd : 1 ≤ d) (s : ℝ) (n : ℕ) (hn : 1 ≤ n)
    (hbox : ∀ k, 1 ≤ k → 0 < (boxGraph d k).edgeFinset.card) (L : ℝ)
    (hL : Tendsto (fun j => ecz_f d s (agl_K j)) atTop (𝓝 L)) :
    ((2 * (n : ℝ) + 1) / (2 * n)) * L - (-Real.log (1 - fsc_logistic s)) / (2 * n)
      ≤ ecz_f d s n := by
  set c := -Real.log (1 - fsc_logistic s) with hc
  have hp0 : (0:ℝ) < fsc_logistic s := fsc_logistic_pos s
  have hp1 : fsc_logistic s < 1 := fsc_logistic_lt_one s
  have hc0 : 0 ≤ c := by rw [hc, neg_nonneg]; exact Real.log_nonpos (by linarith) (by linarith)
  have hEnR : (0 : ℝ) < ((boxGraph d n).edgeFinset.card : ℝ) := by exact_mod_cast hbox n hn
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have h2n : (0 : ℝ) < 2 * n := by positivity
  
  
  set rfun : ℕ → ℝ := fun j => ((ecz_T n (agl_K j)) ^ d : ℝ)
    * ((boxGraph d n).edgeFinset.card : ℝ) / ((boxGraph d (agl_K j)).edgeFinset.card : ℝ) with hrfun
  have hr_tendsto : Tendsto rfun atTop (𝓝 (2 * (n : ℝ) / (2 * n + 1))) :=
    ecz_bulkFraction_tendsto hd n hn |>.comp agl_K_tendsto_atTop
  
  
  have hr_pos : ∀ j, 0 < ((boxGraph d (agl_K j)).edgeFinset.card : ℝ) := fun j => by
    exact_mod_cast hbox (agl_K j) (agl_K_pos j)
  
  
  have hbound : ∀ j, n ≤ agl_K j →
      ecz_f d s (agl_K j) ≤ rfun j * ecz_f d s n + (1 - rfun j) * c := by
    intro j hj
    have := ecz_perEdge_vanHove (d := d) n (agl_K j) s (hbox (agl_K j) (agl_K_pos j)) (hbox n hn)
    rw [← hc] at this
    simpa [hrfun] using this
  
  have hrinf_pos : (0 : ℝ) < 2 * (n : ℝ) / (2 * n + 1) := by positivity
  
  have hRHS_tendsto : Tendsto (fun j => rfun j * ecz_f d s n + (1 - rfun j) * c) atTop
      (𝓝 ((2 * (n : ℝ) / (2 * n + 1)) * ecz_f d s n
          + (1 - 2 * (n : ℝ) / (2 * n + 1)) * c)) :=
    ((hr_tendsto.mul tendsto_const_nhds).add
      (((tendsto_const_nhds).sub hr_tendsto).mul tendsto_const_nhds))
  
  have hKge : ∀ᶠ j in atTop, n ≤ agl_K j := by
    have := agl_K_tendsto_atTop.eventually_ge_atTop n
    exact this
  have hLle : L ≤ (2 * (n : ℝ) / (2 * n + 1)) * ecz_f d s n + (1 - 2 * (n : ℝ) / (2 * n + 1)) * c := by
    refine le_of_tendsto_of_tendsto hL hRHS_tendsto ?_
    filter_upwards [hKge] with j hj using hbound j hj
  
  set R : ℝ := 2 * (n : ℝ) / (2 * n + 1) with hR
  have hRpos : 0 < R := hrinf_pos
  
  have h2n1 : (0:ℝ) < 2 * (n:ℝ) + 1 := by positivity
  
  have hfn : (L - (1 - R) * c) / R ≤ ecz_f d s n := by
    rw [div_le_iff₀ hRpos]; nlinarith [hLle]
  have hsimp : (L - (1 - R) * c) / R
      = (2 * (n : ℝ) + 1) / (2 * n) * L - c / (2 * n) := by
    rw [hR]; field_simp; ring
  rw [hsimp] at hfn
  linarith [hfn]



noncomputable def ecz_g (d : ℕ) (s : ℝ) (m : ℕ) : ℝ :=
  (2 * (m : ℝ) / (2 * m + 1)) * ecz_f d s m
    + (1 - 2 * (m : ℝ) / (2 * m + 1)) * (-Real.log (1 - fsc_logistic s))



theorem ecz_g_dyadic_tendsto (s : ℝ) (L : ℝ)
    (hL : Tendsto (fun j => ecz_f d s (agl_K j)) atTop (𝓝 L)) :
    Tendsto (fun j => ecz_g d s (agl_K j)) atTop (𝓝 L) := by
  set c := -Real.log (1 - fsc_logistic s) with hc
  
  have hKtop : Tendsto (fun j => (2 * ((agl_K j : ℕ) : ℝ) + 1)) atTop atTop :=
    ecz_denom_tendsto_atTop.comp (by exact_mod_cast agl_K_tendsto_atTop)
  have h0 : Tendsto (fun j => (1 : ℝ) / (2 * ((agl_K j : ℕ) : ℝ) + 1)) atTop (𝓝 0) :=
    (tendsto_const_nhds (x := (1:ℝ))).div_atTop hKtop
  have hR : Tendsto (fun j => 2 * ((agl_K j : ℕ) : ℝ) / (2 * ((agl_K j : ℕ) : ℝ) + 1)) atTop (𝓝 1) := by
    have heq : ∀ j, 2 * ((agl_K j : ℕ) : ℝ) / (2 * ((agl_K j : ℕ) : ℝ) + 1)
        = 1 - 1 / (2 * ((agl_K j : ℕ) : ℝ) + 1) := by
      intro j
      have hpos : (0:ℝ) < 2 * ((agl_K j : ℕ) : ℝ) + 1 := by positivity
      field_simp; ring
    rw [show (fun j => 2 * ((agl_K j : ℕ) : ℝ) / (2 * ((agl_K j : ℕ) : ℝ) + 1))
        = (fun j => 1 - 1 / (2 * ((agl_K j : ℕ) : ℝ) + 1)) from funext heq]
    have := h0.const_sub (1 : ℝ); simpa using this
  have hprod : Tendsto (fun j => ecz_g d s (agl_K j)) atTop
      (𝓝 ((1 : ℝ) * L + (1 - 1) * c)) := by
    have heq : (fun j => ecz_g d s (agl_K j))
        = (fun j => (2 * ((agl_K j : ℕ) : ℝ) / (2 * ((agl_K j : ℕ) : ℝ) + 1)) * ecz_f d s (agl_K j)
          + (1 - 2 * ((agl_K j : ℕ) : ℝ) / (2 * ((agl_K j : ℕ) : ℝ) + 1)) * c) := by
      funext j; rw [ecz_g, hc]
    rw [heq]
    exact ((hR.mul hL).add ((tendsto_const_nhds.sub hR).mul tendsto_const_nhds))
  rw [show (1 : ℝ) * L + (1 - 1) * c = L by ring] at hprod
  exact hprod



theorem ecz_upperSeq_tendsto (hd : 1 ≤ d) (s : ℝ) (m : ℕ) (hm : 1 ≤ m) :
    Tendsto (fun n =>
        (((ecz_T m n) ^ d : ℝ) * ((boxGraph d m).edgeFinset.card : ℝ)
            / ((boxGraph d n).edgeFinset.card : ℝ)) * ecz_f d s m
        + (1 - ((ecz_T m n) ^ d : ℝ) * ((boxGraph d m).edgeFinset.card : ℝ)
            / ((boxGraph d n).edgeFinset.card : ℝ)) * (-Real.log (1 - fsc_logistic s))) atTop
      (𝓝 (ecz_g d s m)) := by
  have hr := ecz_bulkFraction_tendsto (d := d) hd m hm
  rw [ecz_g]
  exact ((hr.mul (tendsto_const_nhds (x := ecz_f d s m))).add
    (((tendsto_const_nhds (x := (1:ℝ))).sub hr).mul
      (tendsto_const_nhds (x := -Real.log (1 - fsc_logistic s)))))








theorem ecz_perEdgeDensityConverges (hd : 1 ≤ d) (s : ℝ)
    (hbox : ∀ n, 1 ≤ n → 0 < (boxGraph d n).edgeFinset.card) :
    ecz_PerEdgeDensityConverges d s := by
  classical
  obtain ⟨L, hL⟩ := ecz_dyadic_f_tendsto (d := d) hd s (fun j => hbox _ (agl_K_pos j))
  set c := -Real.log (1 - fsc_logistic s) with hc
  refine ⟨L, ?_⟩
  show Tendsto (fun n => ecz_u d s n / ((boxGraph d n).edgeFinset.card : ℝ)) atTop (𝓝 L)
  have hfdef : (fun n => ecz_u d s n / ((boxGraph d n).edgeFinset.card : ℝ)) = ecz_f d s := by
    funext n; rfl
  rw [hfdef]
  
  have hgK := ecz_g_dyadic_tendsto (d := d) s L hL
  
  have hℓ_tendsto : Tendsto (fun n : ℕ => ((2 * (n : ℝ) + 1) / (2 * n)) * L - c / (2 * n)) atTop
      (𝓝 L) := by
    have h1 : Tendsto (fun n : ℕ => ((2 * (n : ℝ) + 1) / (2 * n)) * L) atTop (𝓝 (1 * L)) :=
      ecz_oddEven_ratio_tendsto.mul tendsto_const_nhds
    have h2 : Tendsto (fun n : ℕ => c / (2 * (n : ℝ))) atTop (𝓝 0) := by
      have hden : Tendsto (fun n : ℕ => (2 * (n : ℝ))) atTop atTop :=
        Tendsto.const_mul_atTop (by norm_num) tendsto_natCast_atTop_atTop
      exact (tendsto_const_nhds (x := c)).div_atTop hden
    have := h1.sub h2; simpa using this
  
  rw [Metric.tendsto_atTop]
  intro ε hε
  
  obtain ⟨N1, hN1⟩ := (Metric.tendsto_atTop.mp hℓ_tendsto) (ε / 2) (by linarith)
  
  obtain ⟨N0, hN0⟩ := (Metric.tendsto_atTop.mp hgK) (ε / 2) (by linarith)
  set J := N0 with hJ
  have hgJ : ecz_g d s (agl_K J) < L + ε / 2 := by
    have := hN0 J (le_refl _); rw [Real.dist_eq, abs_lt] at this; linarith [this.2]
  
  have hupperseq := ecz_upperSeq_tendsto (d := d) hd s (agl_K J) (agl_K_pos J)
  obtain ⟨N2, hN2⟩ := (Metric.tendsto_atTop.mp hupperseq) (ε / 2) (by linarith)
  refine ⟨max (max N1 N2) 1, fun n hn => ?_⟩
  have hn1 : 1 ≤ n := le_trans (le_max_right _ _) hn
  have hnN1 : N1 ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hn
  have hnN2 : N2 ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hn
  rw [Real.dist_eq, abs_lt]
  constructor
  · 
    have hℓle : ((2 * (n : ℝ) + 1) / (2 * n)) * L - c / (2 * n) ≤ ecz_f d s n := by
      have := ecz_f_lower (d := d) hd s n hn1 hbox L hL; rw [← hc] at this; exact this

    have hℓclose : |((2 * (n : ℝ) + 1) / (2 * n)) * L - c / (2 * n) - L| < ε / 2 := by
      have := hN1 n hnN1; rwa [Real.dist_eq] at this
    rw [abs_lt] at hℓclose; linarith [hℓclose.1, hℓle]
  · 
    have hfle : ecz_f d s n
        ≤ (((ecz_T (agl_K J) n) ^ d : ℝ) * ((boxGraph d (agl_K J)).edgeFinset.card : ℝ)
            / ((boxGraph d n).edgeFinset.card : ℝ)) * ecz_f d s (agl_K J)
          + (1 - ((ecz_T (agl_K J) n) ^ d : ℝ) * ((boxGraph d (agl_K J)).edgeFinset.card : ℝ)
            / ((boxGraph d n).edgeFinset.card : ℝ)) * (-Real.log (1 - fsc_logistic s)) :=
      ecz_perEdge_vanHove (d := d) (agl_K J) n s (hbox n hn1) (hbox (agl_K J) (agl_K_pos J))
    have hclose : |(((ecz_T (agl_K J) n) ^ d : ℝ) * ((boxGraph d (agl_K J)).edgeFinset.card : ℝ)
            / ((boxGraph d n).edgeFinset.card : ℝ)) * ecz_f d s (agl_K J)
          + (1 - ((ecz_T (agl_K J) n) ^ d : ℝ) * ((boxGraph d (agl_K J)).edgeFinset.card : ℝ)
            / ((boxGraph d n).edgeFinset.card : ℝ)) * (-Real.log (1 - fsc_logistic s))
          - ecz_g d s (agl_K J)| < ε / 2 := by
      have := hN2 n hnN2; rwa [Real.dist_eq] at this
    rw [abs_lt] at hclose; linarith [hclose.2, hfle, hgJ]

end VanHove























end BoxNesting












section GenuineN1
variable {d : ℕ}




theorem ecz_freeBulkCollapse_n1 (t : ℝ)
    (hbox1 : ∀ n, 1 ≤ n → 0 < (boxGraph d n).edgeFinset.card)
    (L : ℝ) (hL0 : 0 ≤ L) (hL1 : L ≤ 1)
    (In : (n : ℕ) → Finset (Sym2 (boxVerts d n)))
    (hIE : ∀ n, In n ⊆ (boxGraph d n).edgeFinset)
    (δ : ℕ → ℝ) (hδ0 : ∀ n, 0 ≤ δ n) (hδlim : Tendsto δ atTop (𝓝 0))
    (hin : ∀ n, ∀ e ∈ In n,
      |edgeMargProb (fkProb (boxGraph d n) (fsc_logistic t) 2) e - L| ≤ δ n)
    (hbdy : Tendsto (fun n =>
        (((boxGraph d n).edgeFinset.card - (In n).card : ℝ)) / (boxGraph d n).edgeFinset.card)
      atTop (𝓝 0)) :
    Tendsto (fun n => fpd_avgDensity (boxGraph d n) t) atTop (𝓝 L) := by
  have hp := fsc_logistic_pos t
  have hp1 := fsc_logistic_lt_one t
  
  rw [← tendsto_add_atTop_iff_nat (f := fun n => fpd_avgDensity (boxGraph d n) t) 1]
  have hrepr : (fun n => fpd_avgDensity (boxGraph d (n + 1)) t)
      = fun n => (1 / ((boxGraph d (n + 1)).edgeFinset.card : ℝ))
          * ∑ e ∈ (boxGraph d (n + 1)).edgeFinset,
              edgeMargProb (fkProb (boxGraph d (n + 1)) (fsc_logistic t) 2) e := by
    funext n; exact adc_avgDensity_eq_sum_edgeMarg (boxGraph d (n + 1)) t
  rw [hrepr]
  exact adc_absavg_tendsto
    (ι := fun n => Sym2 (boxVerts d (n + 1)))
    (En := fun n => (boxGraph d (n + 1)).edgeFinset) (fun n => In (n + 1))
    (fn := fun n e => edgeMargProb (fkProb (boxGraph d (n + 1)) (fsc_logistic t) 2) e)
    L (fun n => δ (n + 1)) (fun n => hIE (n + 1))
    (fun n e _ => adc_edgeMargProb_fkProb_nonneg (boxGraph d (n + 1)) hp hp1 (by norm_num) e)
    (fun n e _ => adc_edgeMargProb_fkProb_le_one (boxGraph d (n + 1)) hp hp1 (by norm_num) e)
    hL0 hL1 (fun n => hδ0 (n + 1)) (hδlim.comp (tendsto_add_atTop_nat 1))
    (fun n => hin (n + 1)) (fun n => hbox1 (n + 1) (by omega))
    (hbdy.comp (tendsto_add_atTop_nat 1))



theorem ecz_wiredBulkCollapse_n1 (t : ℝ)
    (hbox1 : ∀ n, 1 ≤ n → 0 < (boxGraph d n).edgeFinset.card)
    (L : ℝ) (hL0 : 0 ≤ L) (hL1 : L ≤ 1)
    (In : (n : ℕ) → Finset (Sym2 (boxVerts d n)))
    (hIE : ∀ n, In n ⊆ (boxGraph d n).edgeFinset)
    (δ : ℕ → ℝ) (hδ0 : ∀ n, 0 ≤ δ n) (hδlim : Tendsto δ atTop (𝓝 0))
    (hin : ∀ n, ∀ e ∈ In n,
      |edgeMargProb (wiredFkProb (boxGraph d n) (boxBoundary d n) (fsc_logistic t) 2) e - L| ≤ δ n)
    (hbdy : Tendsto (fun n =>
        (((boxGraph d n).edgeFinset.card - (In n).card : ℝ)) / (boxGraph d n).edgeFinset.card)
      atTop (𝓝 0)) :
    Tendsto (fun n => wpd_avgWiredDensity (boxGraph d n) (boxBoundary d n) 2 t) atTop (𝓝 L) := by
  have hp := fsc_logistic_pos t
  have hp1 := fsc_logistic_lt_one t
  rw [← tendsto_add_atTop_iff_nat
    (f := fun n => wpd_avgWiredDensity (boxGraph d n) (boxBoundary d n) 2 t) 1]
  have hrepr : (fun n => wpd_avgWiredDensity (boxGraph d (n + 1)) (boxBoundary d (n + 1)) 2 t)
      = fun n => (1 / ((boxGraph d (n + 1)).edgeFinset.card : ℝ))
          * ∑ e ∈ (boxGraph d (n + 1)).edgeFinset,
              edgeMargProb (wiredFkProb (boxGraph d (n + 1)) (boxBoundary d (n + 1))
                (fsc_logistic t) 2) e := by
    funext n; exact ubd_avgWiredDensity_eq_sum (n + 1) t
  rw [hrepr]
  exact adc_absavg_tendsto
    (ι := fun n => Sym2 (boxVerts d (n + 1)))
    (En := fun n => (boxGraph d (n + 1)).edgeFinset) (fun n => In (n + 1))
    (fn := fun n e => edgeMargProb (wiredFkProb (boxGraph d (n + 1)) (boxBoundary d (n + 1))
      (fsc_logistic t) 2) e)
    L (fun n => δ (n + 1)) (fun n => hIE (n + 1))
    (fun n e _ => ubd_edgeMargProb_wiredFkProb_nonneg (boxGraph d (n + 1)) (boxBoundary d (n + 1))
      hp hp1 (by norm_num) e)
    (fun n e _ => ubd_edgeMargProb_wiredFkProb_le_one (boxGraph d (n + 1)) (boxBoundary d (n + 1))
      hp hp1 (by norm_num) e)
    hL0 hL1 (fun n => hδ0 (n + 1)) (hδlim.comp (tendsto_add_atTop_nat 1))
    (fun n => hin (n + 1)) (fun n => hbox1 (n + 1) (by omega))
    (hbdy.comp (tendsto_add_atTop_nat 1))



theorem ecz_genuineFreeCollapse_n1 (hd : 1 ≤ d) (N : ℕ)
    (hbox1 : ∀ n, 1 ≤ n → 0 < (boxGraph d n).edgeFinset.card) :
    fpe2_GenuineFreeCollapse (d := d) N := by
  intro e' he' t
  obtain ⟨In, δ, hIE, hδ0, hδlim, hin, hbdy⟩ :=
    gec_freeBulk_of_sandwich N e' t
      (gec_freeSandwich_of_rotation hd N e' t
        (rot_freeRotationResidue (lt_of_lt_of_le one_pos hd) N e' he' t))
  obtain ⟨hL0, hL1⟩ := ubd_freeEdgeDensity_mem_Icc N e' t
  exact ecz_freeBulkCollapse_n1 t hbox1 _ hL0 hL1 In hIE δ hδ0 hδlim hin hbdy


theorem ecz_genuineWiredCollapse_n1 (hd : 1 ≤ d) (N : ℕ)
    (hbox1 : ∀ n, 1 ≤ n → 0 < (boxGraph d n).edgeFinset.card) :
    fpe2_GenuineWiredCollapse (d := d) N := by
  intro e' he' t
  obtain ⟨In, δ, hIE, hδ0, hδlim, hin, hbdy⟩ :=
    gec_wiredBulk_of_sandwich N e' t
      (gec_wiredSandwich_of_rotation hd N e' t
        (rot_wiredRotationResidue (lt_of_lt_of_le one_pos hd) N e' he' t))
  obtain ⟨hL0, hL1⟩ := ubd_wiredEdgeDensity_mem_Icc N e' t
  exact ecz_wiredBulkCollapse_n1 t hbox1 _ hL0 hL1 In hIE δ hδ0 hδlim hin hbdy





theorem ecz_wiredCentered_tendsto_n1 (hd : 1 ≤ d)
    (hbox1 : ∀ n, 1 ≤ n → 0 < (boxGraph d n).edgeFinset.card)
    {G : ℝ → ℝ} (t : ℝ)
    (hfree : Tendsto (fun n => cfe_centered (boxGraph d n) 2 t) atTop (𝓝 (G t))) :
    Tendsto (fun n => cfe_wiredCentered (boxGraph d n) (boxBoundary d n) 2 t) atTop (𝓝 (G t)) := by
  have hsv := fup_surfaceVolume_tendsto_zero d hd
  
  have hdiff : ∀ s : ℝ, Tendsto (fun n => ivp2_tiltFreeEnergy (boxGraph d n) 2 s
        - wpd_wiredTiltFreeEnergy (boxGraph d n) (boxBoundary d n) 2 s) atTop (𝓝 0) := by
    intro s
    have hbound : ∀ᶠ n in atTop, |ivp2_tiltFreeEnergy (boxGraph d n) 2 s
          - wpd_wiredTiltFreeEnergy (boxGraph d n) (boxBoundary d n) 2 s|
        ≤ ((Finset.univ.filter (boxBoundary d n)).card : ℝ)
            / ((boxGraph d n).edgeFinset.card : ℝ) * Real.log 2 := by
      filter_upwards [eventually_ge_atTop 1] with n hn
      exact wpd_tiltFreeEnergy_sub_le (boxGraph d n) (boxBoundary d n) (by norm_num)
        (hbox1 n hn) s
    have hsvlog : Tendsto (fun n =>
        ((Finset.univ.filter (boxBoundary d n)).card : ℝ) / ((boxGraph d n).edgeFinset.card : ℝ)
          * Real.log 2) atTop (𝓝 0) := by
      have := hsv.mul_const (Real.log 2); simpa using this
    refine (tendsto_zero_iff_abs_tendsto_zero _).mpr ?_
    refine squeeze_zero' (Filter.Eventually.of_forall (fun n => abs_nonneg _)) hbound hsvlog
  have hcdiff : Tendsto (fun n => cfe_centered (boxGraph d n) 2 t
        - cfe_wiredCentered (boxGraph d n) (boxBoundary d n) 2 t) atTop (𝓝 0) := by
    have heq : (fun n => cfe_centered (boxGraph d n) 2 t
          - cfe_wiredCentered (boxGraph d n) (boxBoundary d n) 2 t)
        = (fun n => (ivp2_tiltFreeEnergy (boxGraph d n) 2 t
            - wpd_wiredTiltFreeEnergy (boxGraph d n) (boxBoundary d n) 2 t)
          - (ivp2_tiltFreeEnergy (boxGraph d n) 2 0
            - wpd_wiredTiltFreeEnergy (boxGraph d n) (boxBoundary d n) 2 0)) := by
      funext n; unfold cfe_centered cfe_wiredCentered; ring
    rw [heq]
    have := (hdiff t).sub (hdiff 0); simpa using this
  have hwired : Tendsto (fun n => cfe_centered (boxGraph d n) 2 t
        - (cfe_centered (boxGraph d n) 2 t
          - cfe_wiredCentered (boxGraph d n) (boxBoundary d n) 2 t)) atTop (𝓝 (G t - 0)) :=
    hfree.sub hcdiff
  simpa using hwired





theorem ecz_genuineFreeIsLeftDeriv_n1 (N : ℕ)
    (hbox1 : ∀ n, 1 ≤ n → 0 < (boxGraph d n).edgeFinset.card)
    {G : ℝ → ℝ} (hG : ConvexOn ℝ univ G)
    (hboxfree : ∀ t, Tendsto (fun n => cfe_centered (boxGraph d n) 2 t) atTop (𝓝 (G t)))
    (hcol : fpe2_GenuineFreeCollapse d N) :
    fpe2_GenuineFreeIsLeftDeriv d N G := by
  
  have hshift : ∀ x, Tendsto (fun n => cfe_centered (boxGraph d (n + 1)) 2 x) atTop (𝓝 (G x)) :=
    fun x => (hboxfree x).comp (tendsto_add_atTop_nat 1)
  intro e' he' t
  have hbL : ∀ s, pressureLeftDeriv G s
      ≤ freeEdgeDensity d 2 (edgeIncl d N e') (fsc_logistic s) := by
    intro s
    exact fdd_leftDeriv_le_avgLimit
      (fun n => cfe_centered (boxGraph d (n + 1)) 2) G
      (fun n => fpd_avgDensity (boxGraph d (n + 1)))
      (fun n => cfe_centered_convexOn (boxGraph d (n + 1)) 2 (by norm_num) (hbox1 (n + 1) (by omega)))
      (fun n u => cfe_centered_hasDerivAt (boxGraph d (n + 1)) (hbox1 (n + 1) (by omega)) u)
      hshift s _ hG ((hcol e' he' s).comp (tendsto_add_atTop_nat 1))
  have hbR : ∀ s, freeEdgeDensity d 2 (edgeIncl d N e') (fsc_logistic s)
      ≤ pressureRightDeriv G s := by
    intro s
    exact fdd_avgLimit_le_rightDeriv
      (fun n => cfe_centered (boxGraph d (n + 1)) 2) G
      (fun n => fpd_avgDensity (boxGraph d (n + 1)))
      (fun n => cfe_centered_convexOn (boxGraph d (n + 1)) 2 (by norm_num) (hbox1 (n + 1) (by omega)))
      (fun n u => cfe_centered_hasDerivAt (boxGraph d (n + 1)) (hbox1 (n + 1) (by omega)) u)
      hshift s _ hG ((hcol e' he' s).comp (tendsto_add_atTop_nat 1))
  exact fdd_eq_leftDeriv_of_bracket_leftContinuous hG hbL hbR
    (osc_freeEdgeDensity_left_continuous d N e' t)



theorem ecz_genuineWiredIsRightDeriv_n1 (hd : 1 ≤ d) (N : ℕ)
    (hbox1 : ∀ n, 1 ≤ n → 0 < (boxGraph d n).edgeFinset.card)
    {G : ℝ → ℝ} (hG : ConvexOn ℝ univ G)
    (hboxfree : ∀ t, Tendsto (fun n => cfe_centered (boxGraph d n) 2 t) atTop (𝓝 (G t)))
    (hcolfree : fpe2_GenuineFreeCollapse d N)
    (hcolwired : fpe2_GenuineWiredCollapse d N) :
    fpe2_GenuineWiredIsRightDeriv d N G := by
  have hwiredlim : ∀ x,
      Tendsto (fun n => cfe_wiredCentered (boxGraph d n) (boxBoundary d n) 2 x) atTop (𝓝 (G x)) :=
    fun x => ecz_wiredCentered_tendsto_n1 hd hbox1 x (hboxfree x)
  
  have hshiftF : ∀ x, Tendsto (fun n => cfe_centered (boxGraph d (n + 1)) 2 x) atTop (𝓝 (G x)) :=
    fun x => (hboxfree x).comp (tendsto_add_atTop_nat 1)
  have hshiftW : ∀ x, Tendsto (fun n => cfe_wiredCentered (boxGraph d (n + 1)) (boxBoundary d (n + 1))
      2 x) atTop (𝓝 (G x)) :=
    fun x => (hwiredlim x).comp (tendsto_add_atTop_nat 1)
  intro e' he' t
  have hbL : ∀ s, pressureLeftDeriv G s
      ≤ wiredEdgeDensity d 2 (edgeIncl d N e') (fsc_logistic s) := by
    intro s
    refine (?_ : pressureLeftDeriv G s
        ≤ freeEdgeDensity d 2 (edgeIncl d N e') (fsc_logistic s)).trans
      (freeEdgeDensity_q2_le_wiredEdgeDensity d N e' (fsc_logistic_pos s) (fsc_logistic_lt_one s))
    exact fdd_leftDeriv_le_avgLimit
      (fun n => cfe_centered (boxGraph d (n + 1)) 2) G
      (fun n => fpd_avgDensity (boxGraph d (n + 1)))
      (fun n => cfe_centered_convexOn (boxGraph d (n + 1)) 2 (by norm_num) (hbox1 (n + 1) (by omega)))
      (fun n u => cfe_centered_hasDerivAt (boxGraph d (n + 1)) (hbox1 (n + 1) (by omega)) u)
      hshiftF s _ hG ((hcolfree e' he' s).comp (tendsto_add_atTop_nat 1))
  have hbR : ∀ s, wiredEdgeDensity d 2 (edgeIncl d N e') (fsc_logistic s)
      ≤ pressureRightDeriv G s := by
    intro s
    exact fdd_avgLimit_le_rightDeriv
      (fun n => cfe_wiredCentered (boxGraph d (n + 1)) (boxBoundary d (n + 1)) 2) G
      (fun n => wpd_avgWiredDensity (boxGraph d (n + 1)) (boxBoundary d (n + 1)) 2)
      (fun n => cfe_wiredCentered_convexOn (boxGraph d (n + 1)) (boxBoundary d (n + 1)) 2
        (by norm_num) (hbox1 (n + 1) (by omega)))
      (fun n u => cfe_wiredCentered_hasDerivAt (boxGraph d (n + 1)) (boxBoundary d (n + 1))
        (hbox1 (n + 1) (by omega)) u)
      hshiftW s _ hG ((hcolwired e' he' s).comp (tendsto_add_atTop_nat 1))
  exact fdd_eq_rightDeriv_of_bracket_rightContinuous hG hbL hbR
    (osc_wiredEdgeDensity_right_continuous d N e' t)







theorem ecz_fk_uniqueness_of_centeredData_n1 (hd : 1 ≤ d) (N : ℕ) (eb : Sym2 (boxVerts d N))
    (heb : eb ∈ (boxGraph d N).edgeFinset)
    (hbox1 : ∀ n, 1 ≤ n → 0 < (boxGraph d n).edgeFinset.card)
    {G : ℝ → ℝ} (hG : ConvexOn ℝ univ G)
    (hboxfree : ∀ t, Tendsto (fun n => cfe_centered (boxGraph d n) 2 t) atTop (𝓝 (G t))) :
    {t : ℝ | ∃ A : Set (ConfigSpace (Sym2 (boxVerts d N))), IsIncreasing A ∧
        eventMassProb (fuc_freeMass d N t) A
          ≠ eventMassProb (fuc_wiredMass d N t) A}.Countable :=
  fpe2_fk_uniqueness_of_genuine (lt_of_lt_of_le one_pos hd) N eb heb hG
    (ecz_genuineFreeIsLeftDeriv_n1 N hbox1 hG hboxfree
      (ecz_genuineFreeCollapse_n1 hd N hbox1))
    (ecz_genuineWiredIsRightDeriv_n1 hd N hbox1 hG hboxfree
      (ecz_genuineFreeCollapse_n1 hd N hbox1)
      (ecz_genuineWiredCollapse_n1 hd N hbox1))

end GenuineN1









section Convergence
variable {d : ℕ}






def ecz_BlockOscillation (d : ℕ) (s : ℝ) : Prop :=
  ∃ (bj : ℕ → ℕ) (osc : ℕ → ℝ), Tendsto bj atTop atTop ∧ Tendsto osc atTop (𝓝 0)
    ∧ (∀ n, |ecz_edgeFreeEnergy d s n - ecz_edgeFreeEnergy d s (agl_K (bj n))| ≤ osc (bj n))





theorem ecz_blockOscillation_satisfiable :
    ∃ (g : ℕ → ℝ) (bj : ℕ → ℕ) (osc : ℕ → ℝ), Tendsto bj atTop atTop ∧ Tendsto osc atTop (𝓝 0)
      ∧ (∀ n, |g n - g (agl_K (bj n))| ≤ osc (bj n)) := by
  refine ⟨fun _ => 0, agl_K, fun _ => 0, agl_K_tendsto_atTop, tendsto_const_nhds, ?_⟩
  intro n; simp







theorem ecz_blockOscillation_of_perEdgeDensity (s : ℝ)
    (hρ : ecz_PerEdgeDensityConverges d s) : ecz_BlockOscillation d s := by
  classical
  obtain ⟨ρ, hρ⟩ := hρ
  set B := Real.log (1 + Real.exp s) with hB
  have hg : Tendsto (fun n => ecz_edgeFreeEnergy d s n) atTop (𝓝 (B - ρ)) := by
    have h1 : Tendsto (fun n => -(ecz_u d s n / ((boxGraph d n).edgeFinset.card : ℝ)) + B)
        atTop (𝓝 (-ρ + B)) := (hρ.neg).add_const B
    have heq : (fun n => ecz_edgeFreeEnergy d s n)
        = (fun n => -(ecz_u d s n / ((boxGraph d n).edgeFinset.card : ℝ)) + B) := by
      funext n; rw [ecz_edgeFreeEnergy]
    rw [heq]; convert h1 using 2; ring
  have hgK : Tendsto (fun m => ecz_edgeFreeEnergy d s (agl_K m)) atTop (𝓝 (B - ρ)) :=
    hg.comp agl_K_tendsto_atTop
  refine ⟨id, fun m => |ecz_edgeFreeEnergy d s m - (B - ρ)|
      + |ecz_edgeFreeEnergy d s (agl_K m) - (B - ρ)|, tendsto_id, ?_, ?_⟩
  · have h1 : Tendsto (fun m => |ecz_edgeFreeEnergy d s m - (B - ρ)|) atTop (𝓝 0) := by
      have := (hg.sub_const (B - ρ)).abs; simpa using this
    have h2 : Tendsto (fun m => |ecz_edgeFreeEnergy d s (agl_K m) - (B - ρ)|) atTop (𝓝 0) := by
      have := (hgK.sub_const (B - ρ)).abs; simpa using this
    simpa using h1.add h2
  · intro n
    simp only [id]
    calc |ecz_edgeFreeEnergy d s n - ecz_edgeFreeEnergy d s (agl_K n)|
        = |(ecz_edgeFreeEnergy d s n - (B - ρ)) - (ecz_edgeFreeEnergy d s (agl_K n) - (B - ρ))| := by
            ring_nf
      _ ≤ |ecz_edgeFreeEnergy d s n - (B - ρ)| + |ecz_edgeFreeEnergy d s (agl_K n) - (B - ρ)| :=
            abs_sub _ _





theorem ecz_edgeFE_tendsto (hd : 1 ≤ d) (s : ℝ)
    (hbox : ∀ j, 0 < (boxGraph d (agl_K j)).edgeFinset.card)
    (hosc : ecz_BlockOscillation d s) :
    ∃ L : ℝ, Tendsto (fun n => ecz_edgeFreeEnergy d s n) atTop (𝓝 L) := by
  classical
  obtain ⟨I, hInn, hIsum, hudbl, hEdge⟩ := ecz_additiveDoublingBound d hd s
  obtain ⟨bj, osc, hbj, hosc0, hsand⟩ := hosc
  set c : ℝ := -Real.log (1 - fsc_logistic s) with hc
  have hp1 : fsc_logistic s < 1 := fsc_logistic_lt_one s
  have hp0 : (0:ℝ) < fsc_logistic s := fsc_logistic_pos s
  have hc0 : 0 ≤ c := by
    rw [hc, neg_nonneg]; exact Real.log_nonpos (by linarith) (by linarith)
  have hEpos : ∀ j, 0 < agl_E d (agl_K j) := fun j => by
    unfold agl_E; exact_mod_cast hbox j
  
  
  
  set M : ℝ := 3 * Real.log 2 + c with hM
  have hMc0 : 0 ≤ M + c := by
    rw [hM]; have hl2 : (0:ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num); linarith
  have hIE0 : ∀ j, 0 ≤ I j / agl_E d (agl_K (j + 1)) := fun j =>
    div_nonneg (hInn j) (hEpos (j + 1)).le
  set δ : ℕ → ℝ := fun j => (M + c) * (I j / agl_E d (agl_K (j + 1))) with hδ
  apply agl_perVolume_converges
    (fun n => ecz_edgeFreeEnergy d s n) agl_K δ osc bj
  · intro j; exact mul_nonneg hMc0 (hIE0 j)
  · exact hIsum.mul_left (M + c)
  · 
    intro j
    rw [ecz_edgeFE_eq s (agl_K j), ecz_edgeFE_eq s (agl_K (j + 1))]
    have hstep := bxt_perVolume_doubling_step (a := ecz_u d s (agl_K j))
      (A := ecz_u d s (agl_K (j + 1))) (e := agl_E d (agl_K j)) (E := agl_E d (agl_K (j + 1)))
      (K := (2 : ℝ) ^ d) (c := c) (i := I j)
      (hEpos j) (hEpos (j + 1)) hc0 (hInn j) (hudbl j) (hEdge j)
    
    have hl2 : (0:ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    have hle1 : (1:ℝ) ≤ 1 + Real.exp s := by have := Real.exp_pos s; linarith
    have hlog1 : (0:ℝ) ≤ Real.log (1 + Real.exp s) := Real.log_nonneg hle1
    
    have hupper : -(ecz_u d s (agl_K j) / agl_E d (agl_K j)) ≤ 3 * Real.log 2 := by
      have h := ecz_edgeFE_le_const d (agl_K j) hd (agl_K_pos j) s (hbox j)
      rw [ecz_edgeFE_eq] at h; linarith
    
    have hlower : ecz_u d s (agl_K j) / agl_E d (agl_K j) ≤ c := by
      have hEr : (0:ℝ) < agl_E d (agl_K j) := hEpos j
      have hge := ecz_neglogZEdge_le_edges (boxGraph d (agl_K j)) hp0 hp1 (by norm_num : (1:ℝ) ≤ 2)
      
      rw [div_le_iff₀ hEr]
      show ecz_u d s (agl_K j) ≤ c * agl_E d (agl_K j)
      have : ecz_u d s (agl_K j) ≤ agl_E d (agl_K j) * c := by
        simpa [ecz_u, agl_E, hc] using hge
      linarith [mul_comm (agl_E d (agl_K j)) c, this]
    have huEbd : |ecz_u d s (agl_K j)| / agl_E d (agl_K j) ≤ M := by
      have hquot : |ecz_u d s (agl_K j)| / agl_E d (agl_K j)
          = |ecz_u d s (agl_K j) / agl_E d (agl_K j)| := by
        rw [abs_div, abs_of_pos (hEpos j)]
      rw [hquot, abs_le]
      refine ⟨?_, ?_⟩
      · rw [hM]; linarith [hupper, hc0]
      · rw [hM]; linarith [hlower, hl2]
    have hdefle : (|ecz_u d s (agl_K j)| / agl_E d (agl_K j) + c)
        * (I j / agl_E d (agl_K (j + 1))) ≤ δ j := by
      show _ ≤ (M + c) * (I j / agl_E d (agl_K (j + 1)))
      apply mul_le_mul_of_nonneg_right _ (hIE0 j)
      linarith [huEbd]
    have hgoal : -(ecz_u d s (agl_K j) / agl_E d (agl_K j)) - δ j
        ≤ -(ecz_u d s (agl_K (j + 1)) / agl_E d (agl_K (j + 1))) := by linarith [hstep, hdefle]
    linarith
  · 
    refine ⟨3 * Real.log 2 + Real.log (1 + Real.exp s), ?_⟩
    rintro x ⟨j, rfl⟩
    simp only
    exact ecz_edgeFE_le_const d (agl_K j) hd (agl_K_pos j) s (hbox j)
  · exact hbj
  · exact hosc0
  · exact hsand




theorem ecz_cfe_centered_tendsto (hd : 1 ≤ d) (t : ℝ)
    (hbox : ∀ n, 1 ≤ n → 0 < (boxGraph d n).edgeFinset.card)
    (hosct : ecz_BlockOscillation d t) (hosc0 : ecz_BlockOscillation d 0) :
    ∃ G : ℝ, Tendsto (fun n => cfe_centered (boxGraph d n) 2 t) atTop (𝓝 G) := by
  obtain ⟨Lt, hLt⟩ := ecz_edgeFE_tendsto hd t (fun j => ecz_box_edge_pos d hd (agl_K_pos j)) hosct
  obtain ⟨L0, hL0⟩ := ecz_edgeFE_tendsto hd 0 (fun j => ecz_box_edge_pos d hd (agl_K_pos j)) hosc0
  refine ⟨Lt - L0, ?_⟩
  
  
  refine Tendsto.congr' ?_ (hLt.sub hL0)
  filter_upwards [eventually_ge_atTop 1] with n hn
  exact (ecz_centered_eq_cfe t n (hbox n hn)).symm




theorem ecz_centeredConvergence (hd : 1 ≤ d)
    (hbox : ∀ n, 1 ≤ n → 0 < (boxGraph d n).edgeFinset.card)
    (hosc : ∀ s, ecz_BlockOscillation d s) :
    ∃ G : ℝ → ℝ,
      (∀ t, Tendsto (fun n => cfe_centered (boxGraph d n) 2 t) atTop (𝓝 (G t)))
        ∧ ConvexOn ℝ Set.univ G ∧ G 0 = 0 := by
  classical
  have hconv : ∀ t, ∃ G : ℝ,
      Tendsto (fun n => cfe_centered (boxGraph d n) 2 t) atTop (𝓝 G) :=
    fun t => ecz_cfe_centered_tendsto hd t hbox (hosc t) (hosc 0)
  refine ⟨fun t => (hconv t).choose, fun t => (hconv t).choose_spec, ?_, ?_⟩
  · 
    
    
    refine ivp2_convexOn_of_tendsto (l := (atTop : Filter ℕ))
      (fun n => cfe_centered (boxGraph d (n + 1)) 2) _
      (fun n => cfe_centered_convexOn (boxGraph d (n + 1)) 2 (by norm_num)
        (hbox (n + 1) (by omega))) ?_
    intro t
    exact ((hconv t).choose_spec).comp (tendsto_add_atTop_nat 1)
  · 
    show (hconv 0).choose = 0
    have h0 : Tendsto (fun n => cfe_centered (boxGraph d n) 2 0) atTop (𝓝 ((hconv 0).choose)) :=
      (hconv 0).choose_spec
    have hzero : Tendsto (fun n => cfe_centered (boxGraph d n) 2 0) atTop (𝓝 0) := by
      simp only [cfe_centered_zero]
      exact tendsto_const_nhds
    exact tendsto_nhds_unique h0 hzero












theorem ecz_fk_uniqueness_of_blockOscillation (hd : 1 ≤ d) (N : ℕ) (eb : Sym2 (boxVerts d N))
    (heb : eb ∈ (boxGraph d N).edgeFinset)
    (hEbox : ∀ n, 1 ≤ n → 0 < (boxGraph d n).edgeFinset.card)
    (hosc : ∀ s, ecz_BlockOscillation d s) :
    {t : ℝ | ∃ A : Set (ConfigSpace (Sym2 (boxVerts d N))), IsIncreasing A ∧
        eventMassProb (fuc_freeMass d N t) A
          ≠ eventMassProb (fuc_wiredMass d N t) A}.Countable := by
  obtain ⟨G, hboxfree, hG, _hG0⟩ := ecz_centeredConvergence hd hEbox hosc
  exact ecz_fk_uniqueness_of_centeredData_n1 hd N eb heb hEbox hG hboxfree










theorem ecz_fk_uniqueness_of_perEdgeDensity (hd : 1 ≤ d) (N : ℕ) (eb : Sym2 (boxVerts d N))
    (heb : eb ∈ (boxGraph d N).edgeFinset)
    (hEbox : ∀ n, 1 ≤ n → 0 < (boxGraph d n).edgeFinset.card)
    (hρ : ∀ s, ecz_PerEdgeDensityConverges d s) :
    {t : ℝ | ∃ A : Set (ConfigSpace (Sym2 (boxVerts d N))), IsIncreasing A ∧
        eventMassProb (fuc_freeMass d N t) A
          ≠ eventMassProb (fuc_wiredMass d N t) A}.Countable :=
  ecz_fk_uniqueness_of_blockOscillation hd N eb heb hEbox
    (fun s => ecz_blockOscillation_of_perEdgeDensity s (hρ s))






















theorem ecz_fk_uniqueness (hd : 1 ≤ d) (N : ℕ) (eb : Sym2 (boxVerts d N))
    (heb : eb ∈ (boxGraph d N).edgeFinset) :
    {t : ℝ | ∃ A : Set (ConfigSpace (Sym2 (boxVerts d N))), IsIncreasing A ∧
        eventMassProb (fuc_freeMass d N t) A
          ≠ eventMassProb (fuc_wiredMass d N t) A}.Countable :=
  ecz_fk_uniqueness_of_perEdgeDensity hd N eb heb
    (fun n hn => ecz_box_edge_pos d hd hn)
    (fun s => ecz_perEdgeDensityConverges hd s (fun n hn => ecz_box_edge_pos d hd hn))






example : True := by
  have hne : (boxGraph 2 1).edgeFinset.Nonempty :=
    Finset.card_pos.mp (ecz_box_edge_pos 2 (by norm_num) (by norm_num))
  obtain ⟨eb, heb⟩ := hne
  have _ := ecz_fk_uniqueness (d := 2) (by norm_num) (N := 1) eb heb
  trivial

end Convergence





























































theorem ecz_residue_remark : True := trivial

end FK

end StatMech

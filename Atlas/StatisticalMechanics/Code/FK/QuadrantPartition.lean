/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


















































import Mathlib
import Code.FK.AdditiveGluing
import Code.Lattice.BoxSurfaceVolume
import Code.FK.FKUniqPrimitives

open scoped BigOperators
open SimpleGraph Filter Topology Set MeasureTheory

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



variable {U : Type*} [Fintype U] [DecidableEq U] (K₀ : SimpleGraph U) [DecidableRel K₀.Adj]



noncomputable def qp_comapIsoOfRangeEq {V W : Type*} (f : V → U) (g : W → U)
    (hf : Function.Injective f) (hg : Function.Injective g) (hr : Set.range f = Set.range g) :
    K₀.comap f ≃g K₀.comap g where
  toEquiv :=
    (Equiv.ofInjective f hf).trans ((Equiv.setCongr hr).trans (Equiv.ofInjective g hg).symm)
  map_rel_iff' := by
    intro a b
    simp only [comap_adj, Equiv.trans_apply]
    have key : ∀ z : V,
        g ((Equiv.ofInjective g hg).symm ((Equiv.setCongr hr) ((Equiv.ofInjective f hf) z))) = f z :=
      fun z => by rw [Equiv.apply_ofInjective_symm hg]; rfl
    rw [key a, key b]


theorem qp_fkZ_comap_range {V W : Type*} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]
    (f : V → U) (g : W → U) (hf : Function.Injective f) (hg : Function.Injective g)
    (hr : Set.range f = Set.range g) (p q : ℝ)
    [DecidableRel (K₀.comap f).Adj] [DecidableRel (K₀.comap g).Adj] :
    fkZ (K₀.comap f) p q = fkZ (K₀.comap g) p q :=
  fsm_fkZ_iso _ _ (qp_comapIsoOfRangeEq K₀ f g hf hg hr) p q


theorem qp_comap_comap {V W : Type*} (g : W → U) (f : V → W) :
    (K₀.comap g).comap f = K₀.comap (g ∘ f) := by
  ext a b; simp only [comap_adj, Function.comp]







theorem qp_fkZ_ge_allClosed {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq1 : 1 ≤ q) :
    (1 - p) ^ G.edgeFinset.card ≤ fkZ G p q := by
  have hterm : (1 - p) ^ G.edgeFinset.card ≤ fkWeight G p q (fun _ => false) := by
    unfold fkWeight edgeProduct
    have hep : (∏ e ∈ G.edgeFinset, (if (fun (_ : Sym2 V) => false) e then p else 1 - p))
        = (1 - p) ^ G.edgeFinset.card := by
      have : (∏ e ∈ G.edgeFinset, (if (fun (_ : Sym2 V) => false) e then p else 1 - p))
          = ∏ _e ∈ G.edgeFinset, (1 - p) := Finset.prod_congr rfl (fun e _ => by simp)
      rw [this, Finset.prod_const]
    rw [hep]
    have hqk : (1 : ℝ) ≤ q ^ numClusters G (fun _ => false) := one_le_pow₀ hq1
    nlinarith [pow_nonneg (by linarith : (0 : ℝ) ≤ 1 - p) G.edgeFinset.card]
  calc (1 - p) ^ G.edgeFinset.card ≤ fkWeight G p q (fun _ => false) := hterm
    _ ≤ fkZ G p q := by
        unfold fkZ
        exact Finset.single_le_sum (f := fun ω => fkWeight G p q ω)
          (fun ω _ => fkWeight_nonneg G hp hp1 (by linarith) ω) (Finset.mem_univ _)




theorem qp_neglogZ_le_edges {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq1 : 1 ≤ q) :
    -Real.log (fkZ G p q) ≤ (G.edgeFinset.card : ℝ) * (-Real.log (1 - p)) := by
  have h1mp : (0 : ℝ) < 1 - p := by linarith
  have hge := qp_fkZ_ge_allClosed G hp hp1 hq1
  have hpow : (0 : ℝ) < (1 - p) ^ G.edgeFinset.card := pow_pos h1mp _
  have hZ : 0 < fkZ G p q := fkZ_pos G hp hp1 (by linarith)
  have hlog : Real.log ((1 - p) ^ G.edgeFinset.card) ≤ Real.log (fkZ G p q) :=
    Real.log_le_log hpow hge
  rw [Real.log_pow] at hlog
  push_cast at hlog ⊢
  nlinarith [hlog]











section Peel

variable {T : Type*} [DecidableEq T] (tag : U → T)


noncomputable def qp_restG (S : Finset T) : SimpleGraph {x : U // tag x ∈ S} :=
  K₀.comap Subtype.val

noncomputable def qp_blkG (τ : T) : SimpleGraph {x : U // tag x = τ} := K₀.comap Subtype.val

noncomputable instance (S : Finset T) : DecidableRel (qp_restG K₀ tag S).Adj := Classical.decRel _
noncomputable instance (τ : T) : DecidableRel (qp_blkG K₀ tag τ).Adj := Classical.decRel _



def qp_straddleP (P : U → Prop) [DecidablePred P] : Sym2 U → Prop :=
  Sym2.lift ⟨fun a b => (P a ∧ ¬ P b) ∨ (¬ P a ∧ P b),
    by intro a b; by_cases ha : P a <;> by_cases hb : P b <;> simp [ha, hb]⟩

noncomputable instance (P : U → Prop) [DecidablePred P] : DecidablePred (qp_straddleP P) :=
  fun _ => Classical.dec _



noncomputable def qp_straddleEdges (P : U → Prop) [DecidablePred P] : Finset (Sym2 U) :=
  K₀.edgeFinset.filter (qp_straddleP P)



noncomputable def qp_comapComapIso {V W X : Type*} (g : W → U) (f : V → W) (h : X → U)
    (hgf : Function.Injective (g ∘ f)) (hh : Function.Injective h)
    (hr : Set.range (g ∘ f) = Set.range h) :
    (K₀.comap g).comap f ≃g K₀.comap h where
  toEquiv := (Equiv.ofInjective (g ∘ f) hgf).trans
    ((Equiv.setCongr hr).trans (Equiv.ofInjective h hh).symm)
  map_rel_iff' := by
    intro a b; simp only [comap_adj, Equiv.trans_apply]
    have key : ∀ z : V,
        h ((Equiv.ofInjective h hh).symm ((Equiv.setCongr hr) ((Equiv.ofInjective (g ∘ f) hgf) z)))
          = g (f z) := fun z => by rw [Equiv.apply_ofInjective_symm hh]; rfl
    rw [key a, key b]


theorem qp_fkZ_comapComap {V W X : Type*} [Fintype V] [Fintype X] [DecidableEq V] [DecidableEq X]
    (g : W → U) (f : V → W) (h : X → U) (hgf : Function.Injective (g ∘ f))
    (hh : Function.Injective h) (hr : Set.range (g ∘ f) = Set.range h) (p q : ℝ)
    [DecidableRel ((K₀.comap g).comap f).Adj] [DecidableRel (K₀.comap h).Adj] :
    fkZ ((K₀.comap g).comap f) p q = fkZ (K₀.comap h) p q :=
  fsm_fkZ_iso _ _ (qp_comapComapIso K₀ g f h hgf hh hr) p q


theorem qp_left_eq (τ : T) (S : Finset T) (hτ : τ ∉ S) (p q : ℝ) :
    fkZ (agl_left (qp_restG K₀ tag (insert τ S)) (fun x => tag x.1 = τ)) p q
      = fkZ (qp_blkG K₀ tag τ) p q := by
  show fkZ (((K₀.comap (Subtype.val : {x // tag x ∈ insert τ S} → U)).comap
    (Subtype.val : {x // tag x.1 = τ} → _))) p q
      = fkZ (K₀.comap (Subtype.val : {x // tag x = τ} → U)) p q
  refine qp_fkZ_comapComap K₀ _ _ _ ?_ Subtype.val_injective ?_ p q
  · intro a b h; apply Subtype.ext; apply Subtype.ext; exact h
  · ext u; constructor
    · rintro ⟨v, rfl⟩; exact ⟨⟨v.1, v.2⟩, rfl⟩
    · rintro ⟨v, rfl⟩
      exact ⟨⟨⟨v.1, by rw [v.2]; exact Finset.mem_insert_self τ S⟩, v.2⟩, rfl⟩


theorem qp_right_eq (τ : T) (S : Finset T) (hτ : τ ∉ S) (p q : ℝ) :
    fkZ (agl_right (qp_restG K₀ tag (insert τ S)) (fun x => tag x.1 = τ)) p q
      = fkZ (qp_restG K₀ tag S) p q := by
  show fkZ (((K₀.comap (Subtype.val : {x // tag x ∈ insert τ S} → U)).comap
    (Subtype.val : {x // ¬ (tag x.1 = τ)} → _))) p q
      = fkZ (K₀.comap (Subtype.val : {x // tag x ∈ S} → U)) p q
  refine qp_fkZ_comapComap K₀ _ _ _ ?_ Subtype.val_injective ?_ p q
  · intro a b h; apply Subtype.ext; apply Subtype.ext; exact h
  · ext u; constructor
    · rintro ⟨v, rfl⟩
      have hv := v.1.2; have hne := v.2; rw [Finset.mem_insert] at hv
      rcases hv with h | h
      · exact absurd h hne
      · exact ⟨⟨v.1.1, h⟩, rfl⟩
    · rintro ⟨v, rfl⟩
      exact ⟨⟨⟨v.1, Finset.mem_insert_of_mem v.2⟩, fun hc => hτ (hc ▸ v.2)⟩, rfl⟩


theorem qp_interface_le_straddle (P : U → Prop) [DecidablePred P] :
    agl_interfaceCard K₀ P ≤ (qp_straddleEdges K₀ P).card := by
  unfold agl_interfaceCard fis_interface
  apply Finset.card_le_card_of_injOn (fun e => Sym2.map (agl_sumEquiv P) e)
  · intro e he
    rw [Finset.mem_coe, Finset.mem_sdiff, mem_edgeFinset, mem_edgeFinset] at he
    obtain ⟨hK, hnot⟩ := he
    rw [Finset.mem_coe]
    induction e using Sym2.ind with
    | _ x y =>
      rw [mem_edgeSet, agl_glueGraph_adj] at hK
      rw [qp_straddleEdges, Finset.mem_filter]
      refine ⟨?_, ?_⟩
      · simp only [Sym2.map_pair_eq, mem_edgeFinset, mem_edgeSet]
        match x, y with
        | Sum.inl a, Sum.inl b => simpa only [agl_sumEquiv_inl] using hK
        | Sum.inr c, Sum.inr e => simpa only [agl_sumEquiv_inr] using hK
        | Sum.inl a, Sum.inr e => simpa only [agl_sumEquiv_inl, agl_sumEquiv_inr] using hK
        | Sum.inr c, Sum.inl b => simpa only [agl_sumEquiv_inr, agl_sumEquiv_inl] using hK
      · match x, y with
        | Sum.inl a, Sum.inl b =>
          refine absurd (by rw [mem_edgeSet, SimpleGraph.sum_adj]
                            simpa only [agl_left, comap_adj] using hK) hnot
        | Sum.inr c, Sum.inr e =>
          refine absurd (by rw [mem_edgeSet, SimpleGraph.sum_adj]
                            simpa only [agl_right, comap_adj] using hK) hnot
        | Sum.inl a, Sum.inr e =>
          simp only [Sym2.map_pair_eq, agl_sumEquiv_inl, agl_sumEquiv_inr]
          show qp_straddleP P s((a : U), (e : U))
          rw [qp_straddleP, Sym2.lift_mk]; exact Or.inl ⟨a.2, e.2⟩
        | Sum.inr c, Sum.inl b =>
          simp only [Sym2.map_pair_eq, agl_sumEquiv_inr, agl_sumEquiv_inl]
          show qp_straddleP P s((c : U), (b : U))
          rw [qp_straddleP, Sym2.lift_mk]; exact Or.inr ⟨c.2, b.2⟩
  · intro a _ b _ hab
    exact Sym2.map.injective (Equiv.injective _) hab


theorem qp_restG_straddle_le (τ : T) (S : Finset T) :
    (qp_straddleEdges (qp_restG K₀ tag (insert τ S)) (fun x => tag x.1 = τ)).card
      ≤ (qp_straddleEdges K₀ (fun u => tag u = τ)).card := by
  apply Finset.card_le_card_of_injOn
    (fun e => Sym2.map (Subtype.val : {x // tag x ∈ insert τ S} → U) e)
  · intro e he
    rw [Finset.mem_coe, qp_straddleEdges, Finset.mem_filter] at he
    obtain ⟨hedge, hstr⟩ := he
    rw [Finset.mem_coe, qp_straddleEdges, Finset.mem_filter]
    induction e using Sym2.ind with
    | _ x y =>
      rw [qp_straddleP, Sym2.lift_mk] at hstr
      rw [mem_edgeFinset, mem_edgeSet, qp_restG, comap_adj] at hedge
      refine ⟨?_, ?_⟩
      · simp only [Sym2.map_pair_eq, mem_edgeFinset, mem_edgeSet]; exact hedge
      · simp only [Sym2.map_pair_eq]
        show qp_straddleP (fun u => tag u = τ) s((x : U), (y : U))
        rw [qp_straddleP, Sym2.lift_mk]; exact hstr
  · intro a _ b _ hab
    exact Sym2.map.injective Subtype.val_injective hab


theorem qp_fkZ_empty {V : Type*} [Fintype V] [DecidableEq V] [IsEmpty V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (p q : ℝ) : fkZ G p q = 1 := by
  unfold fkZ
  have : Subsingleton (ConfigSpace (Sym2 V)) := by
    constructor; intro a b; funext e; exact e.recOnSubsingleton (fun x => isEmptyElim x)
  rw [Finset.sum_eq_single (fun _ => false)]
  · unfold fkWeight edgeProduct numClusters
    have he : G.edgeFinset = ∅ := by
      rw [SimpleGraph.edgeFinset_eq_empty]; ext a b
      simp only [SimpleGraph.bot_adj]
      exact ⟨fun _ => isEmptyElim a, fun h => h.elim⟩
    rw [he, Finset.prod_empty, one_mul]
    have hc : Fintype.card (openSub G (fun _ => false)).ConnectedComponent = 0 := by
      rw [Fintype.card_eq_zero_iff]
      exact ⟨fun c => c.recOnSubsingleton (fun x => isEmptyElim x)⟩
    rw [hc, pow_zero]
  · intro b _ hb; exact absurd (Subsingleton.elim b _) hb
  · intro h; exact absurd (Finset.mem_univ _) h


noncomputable def qp_uu {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (p q : ℝ) : ℝ := -Real.log (fkZ G p q)









theorem qp_peel_le (p q : ℝ) (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) :
    ∀ S : Finset T, ∃ I : ℕ,
      qp_uu (qp_restG K₀ tag S) p q
          ≤ (∑ τ ∈ S, qp_uu (qp_blkG K₀ tag τ) p q) + (I : ℝ) * (-Real.log (1 - p))
        ∧ I ≤ ∑ τ ∈ S, (qp_straddleEdges K₀ (fun u => tag u = τ)).card := by
  intro S
  induction S using Finset.induction with
  | empty =>
    refine ⟨0, ?_, by simp⟩
    simp only [Finset.sum_empty, Nat.cast_zero, zero_mul, add_zero]
    haveI : IsEmpty {x : U // tag x ∈ (∅ : Finset T)} := ⟨fun x => by simpa using x.2⟩
    rw [qp_uu, qp_fkZ_empty, Real.log_one, neg_zero]
  | @insert τ S hτ ih =>
    obtain ⟨I0, hI0le, hI0bd⟩ := ih
    have hpart := agl_neglog_partition_le (qp_restG K₀ tag (insert τ S))
      (fun x => tag x.1 = τ) hp hp1 hq
    rw [show -Real.log (fkZ (agl_left (qp_restG K₀ tag (insert τ S)) (fun x => tag x.1 = τ)) p q)
        = qp_uu (qp_blkG K₀ tag τ) p q from by rw [qp_uu, qp_left_eq K₀ tag τ S hτ]] at hpart
    rw [show -Real.log (fkZ (agl_right (qp_restG K₀ tag (insert τ S)) (fun x => tag x.1 = τ)) p q)
        = qp_uu (qp_restG K₀ tag S) p q from by rw [qp_uu, qp_right_eq K₀ tag τ S hτ]] at hpart
    set Istep := agl_interfaceCard (qp_restG K₀ tag (insert τ S)) (fun x => tag x.1 = τ)
      with hIstep
    refine ⟨Istep + I0, ?_, ?_⟩
    · rw [Finset.sum_insert hτ]; push_cast
      have huu : qp_uu (qp_restG K₀ tag (insert τ S)) p q
          ≤ qp_uu (qp_blkG K₀ tag τ) p q + qp_uu (qp_restG K₀ tag S) p q
            - (Istep : ℝ) * Real.log (1 - p) := by rw [qp_uu]; exact hpart
      calc qp_uu (qp_restG K₀ tag (insert τ S)) p q
          ≤ qp_uu (qp_blkG K₀ tag τ) p q + qp_uu (qp_restG K₀ tag S) p q
              - (Istep : ℝ) * Real.log (1 - p) := huu
        _ ≤ qp_uu (qp_blkG K₀ tag τ) p q
              + ((∑ σ ∈ S, qp_uu (qp_blkG K₀ tag σ) p q) + (I0 : ℝ) * (-Real.log (1 - p)))
              - (Istep : ℝ) * Real.log (1 - p) := by linarith [hI0le]
        _ = (qp_uu (qp_blkG K₀ tag τ) p q + ∑ σ ∈ S, qp_uu (qp_blkG K₀ tag σ) p q)
              + ((Istep : ℝ) + (I0 : ℝ)) * (-Real.log (1 - p)) := by ring
    · rw [Finset.sum_insert hτ]
      have hIstepbd : Istep ≤ (qp_straddleEdges K₀ (fun u => tag u = τ)).card :=
        le_trans (qp_interface_le_straddle (qp_restG K₀ tag (insert τ S)) (fun x => tag x.1 = τ))
          (qp_restG_straddle_le K₀ tag τ S)
      omega

end Peel







namespace EdgeCount

noncomputable def edgeAxisI (d n : ℕ) (i : Fin d) : Finset (Site d × Site d) :=
  (boxSV_edgeF d n).filter (fun p => p.1 i ≠ p.2 i)
noncomputable def shiftDom (d n : ℕ) (i : Fin d) (b : ℤ) : Finset (Site d) :=
  (boxSV_boxF d n).filter (fun x => x i + b ∈ Finset.Icc (-(n : ℤ)) n)
noncomputable def shiftMap (d n : ℕ) (i : Fin d) (b : ℤ) (x : Site d) : Site d × Site d :=
  (x, Function.update x i (x i + b))

theorem shift_adj (d n : ℕ) (i : Fin d) (x : Site d) (b : ℤ) (hb : b = 1 ∨ b = -1) :
    (hypercubicLattice d).Adj x (Function.update x i (x i + b)) := by
  classical
  rw [hypercubicLattice_adj, Finset.sum_eq_single i]
  · simp only [Function.update_self]; rcases hb with h|h <;> simp [h]
  · intro c _ hc; rw [Function.update_of_ne hc]; simp
  · intro h; exact absurd (Finset.mem_univ _) h

theorem card_shiftDom (d n : ℕ) (i : Fin d) (b : ℤ) (hb : b = 1 ∨ b = -1) (hd : 1 ≤ d) :
    (shiftDom d n i b).card = (2 * n) * (2 * n + 1) ^ (d - 1) := by
  unfold shiftDom boxSV_boxF
  have heq : ((Fintype.piFinset (fun _ : Fin d => Finset.Icc (-(n : ℤ)) n)).filter
      (fun x => x i + b ∈ Finset.Icc (-(n : ℤ)) n))
      = Fintype.piFinset (fun j : Fin d =>
          if j = i then ((Finset.Icc (-(n : ℤ)) n).filter (fun v => v + b ∈ Finset.Icc (-(n:ℤ)) n))
                   else Finset.Icc (-(n : ℤ)) n) := by
    ext x; rw [Finset.mem_filter, Fintype.mem_piFinset, Fintype.mem_piFinset]
    constructor
    · rintro ⟨h1, h2⟩ j; have hj1 := h1 j; by_cases hj : j = i
      · subst hj; rw [if_pos rfl, Finset.mem_filter]; exact ⟨hj1, h2⟩
      · rw [if_neg hj]; exact hj1
    · intro h; refine ⟨fun j => ?_, ?_⟩
      · have := h j; by_cases hj : j = i
        · subst hj; rw [if_pos rfl, Finset.mem_filter] at this; exact this.1
        · rw [if_neg hj] at this; exact this
      · have := h i; rw [if_pos rfl, Finset.mem_filter] at this; exact this.2
  rw [heq, Fintype.card_piFinset]
  have hcard : ∀ j : Fin d, (if j = i then ((Finset.Icc (-(n : ℤ)) n).filter (fun v => v + b ∈ Finset.Icc (-(n:ℤ)) n))
        else Finset.Icc (-(n : ℤ)) n).card = (if j = i then (2 * n) else (2 * n + 1)) := by
    intro j; by_cases hj : j = i
    · rw [if_pos hj, if_pos hj]
      rcases hb with h | h <;> subst h
      · rw [show ((Finset.Icc (-(n:ℤ)) n).filter (fun v => v + 1 ∈ Finset.Icc (-(n:ℤ)) n))
              = Finset.Icc (-(n:ℤ)) (n-1) from by
            ext v; rw [Finset.mem_filter, Finset.mem_Icc, Finset.mem_Icc, Finset.mem_Icc]; omega,
          Int.card_Icc]; omega
      · rw [show ((Finset.Icc (-(n:ℤ)) n).filter (fun v => v + (-1) ∈ Finset.Icc (-(n:ℤ)) n))
              = Finset.Icc (-(n:ℤ)+1) n from by
            ext v; rw [Finset.mem_filter, Finset.mem_Icc, Finset.mem_Icc, Finset.mem_Icc]; omega,
          Int.card_Icc]; omega
    · rw [if_neg hj, if_neg hj, Int.card_Icc]; omega
  rw [Finset.prod_congr rfl (fun j _ => hcard j),
    ← Finset.mul_prod_erase Finset.univ (fun j => if j = i then (2 * n) else (2 * n + 1))
      (Finset.mem_univ i), if_pos rfl]
  congr 1
  rw [Finset.prod_congr rfl (fun j hj => by rw [if_neg (Finset.ne_of_mem_erase hj)]),
    Finset.prod_const, Finset.card_erase_of_mem (Finset.mem_univ _),
    Finset.card_univ, Fintype.card_fin]

theorem shiftMap_mem (d n : ℕ) (i : Fin d) (b : ℤ) (hb : b = 1 ∨ b = -1) (x : Site d)
    (hx : x ∈ shiftDom d n i b) : shiftMap d n i b x ∈ edgeAxisI d n i := by
  rw [shiftDom, Finset.mem_filter] at hx
  have hxbox : x ∈ boxSV_boxF d n := hx.1
  rw [boxSV_mem_boxF] at hxbox
  rw [edgeAxisI, Finset.mem_filter, shiftMap, boxSV_mem_edgeF]
  refine ⟨⟨by rw [boxSV_mem_boxF]; exact hxbox, ?_, shift_adj d n i x b hb⟩, ?_⟩
  · rw [boxSV_mem_boxF]; intro j; by_cases hj : j = i
    · subst hj; simp only [Function.update_self]; exact hx.2
    · simp only [Function.update_of_ne hj]; exact hxbox j
  · simp only [shiftMap, Function.update_self, ne_eq]; rcases hb with h|h <;> subst h <;> omega

theorem shiftMap_inj (d n : ℕ) (i : Fin d) (b : ℤ) : Function.Injective (shiftMap d n i b) :=
  fun x y h => (Prod.ext_iff.mp h).1

theorem edgeAxisI_eq (d n : ℕ) (i : Fin d) :
    edgeAxisI d n i = (shiftDom d n i 1).image (shiftMap d n i 1)
        ∪ (shiftDom d n i (-1)).image (shiftMap d n i (-1)) := by
  ext p
  rw [Finset.mem_union, Finset.mem_image, Finset.mem_image]
  constructor
  · intro hp
    rw [edgeAxisI, Finset.mem_filter, boxSV_mem_edgeF] at hp
    obtain ⟨⟨h1box, h2box, hadj⟩, hne⟩ := hp
    rw [hypercubicLattice_adj] at hadj
    rw [boxSV_mem_boxF] at h1box h2box
    have hdiff : (p.1 i - p.2 i).natAbs = 1 := by
      have hge : 1 ≤ (p.1 i - p.2 i).natAbs := by
        rcases Nat.eq_zero_or_pos (p.1 i - p.2 i).natAbs with h | h
        · exact absurd (by omega : p.1 i = p.2 i) hne
        · omega
      have hle : (p.1 i - p.2 i).natAbs ≤ ∑ k, (p.1 k - p.2 k).natAbs :=
        Finset.single_le_sum (f := fun k => (p.1 k - p.2 k).natAbs) (fun _ _ => Nat.zero_le _)
          (Finset.mem_univ i)
      omega
    have hother : ∀ j ≠ i, p.1 j = p.2 j := by
      intro j hj; by_contra hc
      have hjge : 1 ≤ (p.1 j - p.2 j).natAbs := by
        rcases Nat.eq_zero_or_pos (p.1 j - p.2 j).natAbs with h | h
        · exact absurd (by omega : p.1 j = p.2 j) hc
        · omega
      have : (p.1 i - p.2 i).natAbs + (p.1 j - p.2 j).natAbs ≤ ∑ k, (p.1 k - p.2 k).natAbs := by
        rw [show (p.1 i - p.2 i).natAbs + (p.1 j - p.2 j).natAbs
              = ∑ k ∈ ({i, j} : Finset (Fin d)), (p.1 k - p.2 k).natAbs from
            (Finset.sum_pair (f := fun k => (p.1 k - p.2 k).natAbs) (Ne.symm hj)).symm]
        exact Finset.sum_le_sum_of_subset (Finset.subset_univ _)
      omega
    have hp2 : p.2 = Function.update p.1 i (p.1 i + (p.2 i - p.1 i)) := by
      funext j; by_cases hj : j = i
      · subst hj; simp only [Function.update_self]; ring
      · simp only [Function.update_of_ne hj]; exact (hother j hj).symm
    have hb : p.2 i - p.1 i = 1 ∨ p.2 i - p.1 i = -1 := by omega
    have hpeq : ∀ b : ℤ, p.2 i - p.1 i = b → p = shiftMap d n i b p.1 := by
      intro b hbv; rw [shiftMap]; apply Prod.ext
      · rfl
      · rw [hp2]; simp only; congr 1; omega
    rcases hb with hb | hb
    · left; refine ⟨p.1, ?_, (hpeq 1 hb).symm⟩
      rw [shiftDom, Finset.mem_filter]
      refine ⟨by rw [boxSV_mem_boxF]; exact h1box, ?_⟩
      have hpval : p.1 i + 1 = p.2 i := by omega
      rw [hpval]; exact h2box i
    · right; refine ⟨p.1, ?_, (hpeq (-1) hb).symm⟩
      rw [shiftDom, Finset.mem_filter]
      refine ⟨by rw [boxSV_mem_boxF]; exact h1box, ?_⟩
      have hpval : p.1 i + (-1) = p.2 i := by omega
      rw [hpval]; exact h2box i
  · rintro (⟨x, hx, rfl⟩ | ⟨x, hx, rfl⟩)
    · exact shiftMap_mem d n i 1 (Or.inl rfl) x hx
    · exact shiftMap_mem d n i (-1) (Or.inr rfl) x hx

theorem fwd_bwd_disjoint (d n : ℕ) (i : Fin d) :
    Disjoint ((shiftDom d n i 1).image (shiftMap d n i 1))
        ((shiftDom d n i (-1)).image (shiftMap d n i (-1))) := by
  rw [Finset.disjoint_left]
  rintro p hp1 hp2
  rw [Finset.mem_image] at hp1 hp2
  obtain ⟨x, hx, rfl⟩ := hp1
  obtain ⟨y, hy, hxy⟩ := hp2
  rw [shiftMap, shiftMap, Prod.ext_iff] at hxy
  obtain ⟨h1, h2⟩ := hxy
  subst h1
  have := congrFun h2 i
  simp only [Function.update_self] at this
  omega

theorem card_edgeAxisI (d n : ℕ) (i : Fin d) (hd : 1 ≤ d) :
    (edgeAxisI d n i).card = 2 * ((2 * n) * (2 * n + 1) ^ (d - 1)) := by
  rw [edgeAxisI_eq, Finset.card_union_of_disjoint (fwd_bwd_disjoint d n i),
    Finset.card_image_of_injective _ (shiftMap_inj d n i 1),
    Finset.card_image_of_injective _ (shiftMap_inj d n i (-1)),
    card_shiftDom d n i 1 (Or.inl rfl) hd, card_shiftDom d n i (-1) (Or.inr rfl) hd]
  ring

theorem edgeF_biUnion (d n : ℕ) :
    (boxSV_edgeF d n) = Finset.univ.biUnion (fun i : Fin d => edgeAxisI d n i) := by
  ext p; rw [Finset.mem_biUnion]
  constructor
  · intro hp
    have hadj := (boxSV_mem_edgeF.mp hp).2.2
    rw [hypercubicLattice_adj] at hadj
    obtain ⟨i, hi⟩ : ∃ i, (p.1 i - p.2 i).natAbs ≠ 0 := by
      by_contra hc; push_neg at hc; simp only [hc] at hadj; simp at hadj
    exact ⟨i, Finset.mem_univ i, by rw [edgeAxisI, Finset.mem_filter]; exact ⟨hp, fun he => hi (by rw [he]; simp)⟩⟩
  · rintro ⟨i, _, hp⟩; rw [edgeAxisI, Finset.mem_filter] at hp; exact hp.1

theorem edgeAxis_disjoint (d n : ℕ) (i j : Fin d) (hij : i ≠ j) :
    Disjoint (edgeAxisI d n i) (edgeAxisI d n j) := by
  rw [Finset.disjoint_left]
  intro p hpi hpj
  rw [edgeAxisI, Finset.mem_filter] at hpi hpj
  have hadj := (boxSV_mem_edgeF.mp hpi.1).2.2
  rw [hypercubicLattice_adj] at hadj
  have hi : 1 ≤ (p.1 i - p.2 i).natAbs := by
    rcases Nat.eq_zero_or_pos (p.1 i - p.2 i).natAbs with h | h
    · exact absurd (by omega : p.1 i = p.2 i) hpi.2
    · omega
  have hj : 1 ≤ (p.1 j - p.2 j).natAbs := by
    rcases Nat.eq_zero_or_pos (p.1 j - p.2 j).natAbs with h | h
    · exact absurd (by omega : p.1 j = p.2 j) hpj.2
    · omega
  have hsum : (p.1 i - p.2 i).natAbs + (p.1 j - p.2 j).natAbs ≤ ∑ k, (p.1 k - p.2 k).natAbs := by
    rw [show (p.1 i - p.2 i).natAbs + (p.1 j - p.2 j).natAbs
          = ∑ k ∈ ({i, j} : Finset (Fin d)), (p.1 k - p.2 k).natAbs from
        (Finset.sum_pair (f := fun k => (p.1 k - p.2 k).natAbs) hij).symm]
    exact Finset.sum_le_sum_of_subset (Finset.subset_univ _)
  omega

theorem edgeCard_eq (d n : ℕ) (hd : 1 ≤ d) :
    boxSV_edgeCard d n = d * (2 * ((2 * n) * (2 * n + 1) ^ (d - 1))) := by
  unfold boxSV_edgeCard
  rw [edgeF_biUnion, Finset.card_biUnion (fun i _ j _ hij => edgeAxis_disjoint d n i j hij),
    Finset.sum_congr rfl (fun i _ => card_edgeAxisI d n i hd),
    Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  ring


theorem boxGraph_edgeCard (d n : ℕ) (hd : 1 ≤ d) :
    (boxGraph d n).edgeFinset.card = d * ((2 * n) * (2 * n + 1) ^ (d - 1)) := by
  have h := fup_edge_card_eq d n
  rw [edgeCard_eq d n hd] at h
  set Z := d * ((2 * n) * (2 * n + 1) ^ (d - 1)) with hZ
  have h2 : d * (2 * ((2 * n) * (2 * n + 1) ^ (d - 1))) = 2 * Z := by rw [hZ]; ring
  rw [h2] at h
  omega

end EdgeCount









section BoxGeom


def qp_vshift (d K : ℕ) (s : Fin d → Bool) : Site d :=
  fun i => if s i then (K + 1 : ℤ) else -(K + 1 : ℤ)

theorem qp_natAbs_iff (x : ℤ) (n : ℕ) : x.natAbs ≤ n ↔ -(n : ℤ) ≤ x ∧ x ≤ n := by
  rw [show x.natAbs ≤ n ↔ |x| ≤ (n : ℤ) from by rw [Int.abs_eq_natAbs]; exact Int.ofNat_le.symm]
  exact abs_le


noncomputable def qp_boxTag (d K : ℕ) (x : boxVerts d (2 * K + 1)) : Option (Fin d → Bool) :=
  if (∃ i, (x : Site d) i = 0) then none else some (fun i => decide (0 < (x : Site d) i))


theorem qp_boxTag_some_iff (d K : ℕ) (x : boxVerts d (2 * K + 1)) (s : Fin d → Bool) :
    qp_boxTag d K x = some s ↔ ∀ i, if s i then (1 ≤ (x : Site d) i ∧ (x : Site d) i ≤ 2 * K + 1)
              else (-(2 * K + 1 : ℤ) ≤ (x : Site d) i ∧ (x : Site d) i ≤ -1) := by
  unfold qp_boxTag
  by_cases hz : ∃ i, (x : Site d) i = 0
  · rw [if_pos hz]
    constructor
    · intro h; exact absurd h (by simp)
    · intro h; obtain ⟨i, hi⟩ := hz
      have hh := h i
      have hb := (qp_natAbs_iff ((x : Site d) i) (2 * K + 1)).mp (by have := x.2 i; push_cast; omega)
      by_cases hs : s i <;> simp only [hs, if_true, Bool.false_eq_true, if_false] at hh <;>
        push_cast at hh <;> omega
  · rw [if_neg hz]
    push_neg at hz
    constructor
    · intro h
      rw [Option.some_inj] at h
      intro i
      have hb := (qp_natAbs_iff ((x : Site d) i) (2 * K + 1)).mp (by have := x.2 i; push_cast; omega)
      have hsi : s i = decide (0 < (x : Site d) i) := by rw [← h]
      by_cases hs : s i <;> simp only [hs] at hsi ⊢ <;>
        simp only [if_true, Bool.false_eq_true, if_false]
      · have hpos : 0 < (x : Site d) i :=
          (decide_eq_true_iff (p := 0 < (x : Site d) i)).mp hsi.symm
        have hnz := hz i; push_cast; omega
      · have hnp : ¬ (0 < (x : Site d) i) :=
          (decide_eq_false_iff_not (p := 0 < (x : Site d) i)).mp hsi.symm
        have hnz := hz i; push_cast; omega
    · intro h
      rw [Option.some_inj]; funext i
      have hh := h i
      by_cases hs : s i <;> simp only [hs, if_true, Bool.false_eq_true, if_false] at hh ⊢
      · exact (decide_eq_true_iff (p := 0 < (x : Site d) i)).mpr (by omega)
      · exact (decide_eq_false_iff_not (p := 0 < (x : Site d) i)).mpr (by push_cast; omega)


noncomputable def qp_quadφ (d K : ℕ) (s : Fin d → Bool) :
    boxVerts d K ≃ {x : boxVerts d (2 * K + 1) // qp_boxTag d K x = some s} where
  toFun y := ⟨⟨fun i => (y : Site d) i + qp_vshift d K s i, by
      intro i; have hy := (qp_natAbs_iff ((y : Site d) i) K).mp (y.2 i)
      rw [qp_natAbs_iff]; simp only [qp_vshift]
      by_cases hs : s i <;> simp only [hs, if_true, Bool.false_eq_true, if_false] <;> omega⟩,
    by rw [qp_boxTag_some_iff]; intro i; have hy := (qp_natAbs_iff ((y : Site d) i) K).mp (y.2 i)
       simp only [qp_vshift]
       by_cases hs : s i <;> simp only [hs, if_true, Bool.false_eq_true, if_false] <;>
         push_cast <;> omega⟩
  invFun x := ⟨fun i => (x.1 : Site d) i - qp_vshift d K s i, by
      intro i
      have hP : (if s i then (1 ≤ (x.1.1 : Site d) i ∧ (x.1.1 : Site d) i ≤ 2 * K + 1)
              else (-(2 * K + 1 : ℤ) ≤ (x.1.1 : Site d) i ∧ (x.1.1 : Site d) i ≤ -1)) :=
        (qp_boxTag_some_iff d K x.1 s).mp x.2 i
      rw [qp_natAbs_iff]; simp only [qp_vshift]
      by_cases hs : s i <;> simp only [hs, if_true, Bool.false_eq_true, if_false] at hP ⊢ <;>
        push_cast <;> omega⟩
  left_inv y := by apply Subtype.ext; funext i; simp
  right_inv x := by apply Subtype.ext; apply Subtype.ext; funext i; simp


theorem qp_block_fkZ (d K : ℕ) (s : Fin d → Bool) (p q : ℝ) :
    fkZ (qp_blkG (boxGraph d (2 * K + 1)) (qp_boxTag d K) (some s)) p q = fkZ (boxGraph d K) p q := by
  have key := agl_left_block_fkZ_eq (2 * K + 1) K (fun x => qp_boxTag d K x = some s)
    (qp_vshift d K s) (qp_quadφ d K s)
    (by intro y
        show (((qp_quadφ d K s y).1 : boxVerts d (2 * K + 1)) : Site d) = (y : Site d) + qp_vshift d K s
        funext i; rfl) p q
  convert key using 2


noncomputable def qp_Jset (d K : ℕ) : Finset (boxVerts d (2 * K + 1)) :=
  Finset.univ.filter (fun x => ∃ i, (x : Site d) i = 0)


noncomputable def qp_Jslab (d K : ℕ) (i : Fin d) : Finset (boxVerts d (2 * K + 1)) :=
  Finset.univ.filter (fun x => (x : Site d) i = 0)

theorem qp_Jset_subset_biUnion (d K : ℕ) :
    qp_Jset d K ⊆ Finset.univ.biUnion (fun i : Fin d => qp_Jslab d K i) := by
  intro x hx
  rw [qp_Jset, Finset.mem_filter] at hx
  obtain ⟨i, hi⟩ := hx.2
  rw [Finset.mem_biUnion]
  exact ⟨i, Finset.mem_univ _, by rw [qp_Jslab, Finset.mem_filter]; exact ⟨Finset.mem_univ _, hi⟩⟩

theorem qp_Jslab_card (d K : ℕ) (hd : 1 ≤ d) (i : Fin d) :
    (qp_Jslab d K i).card ≤ (2 * (2 * K + 1) + 1) ^ (d - 1) := by
  classical
  have hsub : (qp_Jslab d K i).image (Subtype.val : boxVerts d (2 * K + 1) → Site d)
      ⊆ Fintype.piFinset (fun j : Fin d =>
          if j = i then ({0} : Finset ℤ) else Finset.Icc (-(2 * (K : ℤ) + 1)) (2 * K + 1)) := by
    intro y hy
    rw [Finset.mem_image] at hy
    obtain ⟨x, hxJ, rfl⟩ := hy
    rw [qp_Jslab, Finset.mem_filter] at hxJ
    rw [Fintype.mem_piFinset]
    intro j; by_cases hj : j = i
    · subst hj; rw [if_pos rfl, Finset.mem_singleton]; exact hxJ.2
    · rw [if_neg hj, Finset.mem_Icc]
      have hb := x.2 j
      have h2 : |(x : Site d) j| ≤ ((2 * K + 1 : ℕ) : ℤ) := by rw [Int.abs_eq_natAbs]; exact_mod_cast hb
      have := abs_le.mp h2; push_cast at this ⊢; omega
  calc (qp_Jslab d K i).card
      = ((qp_Jslab d K i).image (Subtype.val : boxVerts d (2 * K + 1) → Site d)).card :=
        (Finset.card_image_of_injective _ Subtype.val_injective).symm
    _ ≤ (Fintype.piFinset (fun j : Fin d =>
          if j = i then ({0} : Finset ℤ) else Finset.Icc (-(2 * (K : ℤ) + 1)) (2 * K + 1))).card :=
        Finset.card_le_card hsub
    _ = ∏ j : Fin d, (if j = i then ({0} : Finset ℤ)
          else Finset.Icc (-(2 * (K : ℤ) + 1)) (2 * K + 1)).card := Fintype.card_piFinset _
    _ = (2 * (2 * K + 1) + 1) ^ (d - 1) := by
        rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i), if_pos rfl,
          Finset.card_singleton, one_mul]
        have hicc : ∀ j ∈ Finset.univ.erase i, (if j = i then ({0} : Finset ℤ)
            else Finset.Icc (-(2 * (K : ℤ) + 1)) (2 * K + 1)).card = 2 * (2 * K + 1) + 1 := by
          intro j hj; rw [if_neg (Finset.ne_of_mem_erase hj), Int.card_Icc]; omega
        rw [Finset.prod_congr rfl hicc, Finset.prod_const,
          Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]


theorem qp_Jset_card_le (d K : ℕ) (hd : 1 ≤ d) :
    (qp_Jset d K).card ≤ d * (2 * (2 * K + 1) + 1) ^ (d - 1) := by
  calc (qp_Jset d K).card
      ≤ (Finset.univ.biUnion (fun i : Fin d => qp_Jslab d K i)).card :=
        Finset.card_le_card (qp_Jset_subset_biUnion d K)
    _ ≤ ∑ i : Fin d, (qp_Jslab d K i).card := Finset.card_biUnion_le
    _ ≤ ∑ _i : Fin d, (2 * (2 * K + 1) + 1) ^ (d - 1) :=
        Finset.sum_le_sum (fun i _ => qp_Jslab_card d K hd i)
    _ = d * (2 * (2 * K + 1) + 1) ^ (d - 1) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]


theorem qp_boxGraph_degree_le (d n : ℕ) (v : boxVerts d n) : (boxGraph d n).degree v ≤ 2 * d := by
  rw [← SimpleGraph.card_incidenceFinset_eq_degree]
  calc ((boxGraph d n).incidenceFinset v).card
      ≤ ((hypercubicLattice d).incidenceFinset (v : Site d)).card := by
        apply Finset.card_le_card_of_injOn (fun e => Sym2.map Subtype.val e)
        · intro e he
          rw [Finset.mem_coe, SimpleGraph.mem_incidenceFinset] at he
          obtain ⟨hmem, hv⟩ := he
          rw [Finset.mem_coe, SimpleGraph.mem_incidenceFinset]
          induction e using Sym2.ind with
          | _ a b =>
            rw [mem_edgeSet] at hmem
            have hadj : (hypercubicLattice d).Adj (a : Site d) (b : Site d) := by
              have : (boxGraph d n).Adj a b := hmem
              simpa only [boxGraph, comap_adj] using this
            refine ⟨?_, ?_⟩
            · simp only [Sym2.map_pair_eq, mem_edgeSet]; exact hadj
            · simp only [Sym2.map_pair_eq]
              rcases Sym2.mem_iff.mp hv with rfl | rfl
              · exact Sym2.mem_mk_left _ _
              · exact Sym2.mem_mk_right _ _
        · intro a _ b _ hab; exact Sym2.map.injective Subtype.val_injective hab
    _ = (hypercubicLattice d).degree (v : Site d) := SimpleGraph.card_incidenceFinset_eq_degree _ _
    _ ≤ 2 * d := degree_le d _




theorem qp_straddle_endpoint_in_J (d K : ℕ) (s : Fin d → Bool) (x y : boxVerts d (2 * K + 1))
    (hadj : (boxGraph d (2 * K + 1)).Adj x y) (hx : qp_boxTag d K x = some s)
    (hy : qp_boxTag d K y ≠ some s) : ∃ i, (y : Site d) i = 0 := by
  by_contra hyc
  push_neg at hyc
  have hyt : qp_boxTag d K y = some (fun i => decide (0 < (y : Site d) i)) := by
    unfold qp_boxTag; rw [if_neg (by push_neg; exact hyc)]
  have hxnz : ∀ i, (x : Site d) i ≠ 0 := by
    intro i hi; unfold qp_boxTag at hx
    by_cases hz : ∃ j, (x : Site d) j = 0
    · rw [if_pos hz] at hx; exact absurd hx (by simp)
    · exact hz ⟨i, hi⟩
  have hxt : qp_boxTag d K x = some (fun i => decide (0 < (x : Site d) i)) := by
    unfold qp_boxTag; rw [if_neg (by push_neg; exact hxnz)]
  rw [hxt, Option.some_inj] at hx
  rw [boxGraph, comap_adj, hypercubicLattice_adj] at hadj
  obtain ⟨i, hi⟩ : ∃ i, ((x : Site d) i - (y : Site d) i).natAbs ≠ 0 := by
    by_contra hc; push_neg at hc; simp only [hc] at hadj; simp at hadj
  have hother : ∀ j ≠ i, (x : Site d) j = (y : Site d) j := by
    intro j hj; by_contra hc
    have : ((x : Site d) i - (y : Site d) i).natAbs + ((x : Site d) j - (y : Site d) j).natAbs
        ≤ ∑ k, ((x : Site d) k - (y : Site d) k).natAbs := by
      rw [show ((x : Site d) i - (y : Site d) i).natAbs + ((x : Site d) j - (y : Site d) j).natAbs
            = ∑ k ∈ ({i, j} : Finset (Fin d)), ((x : Site d) k - (y : Site d) k).natAbs from
          (Finset.sum_pair (f := fun k => ((x : Site d) k - (y : Site d) k).natAbs)
            (Ne.symm hj)).symm]
      exact Finset.sum_le_sum_of_subset (Finset.subset_univ _)
    have hjne : 1 ≤ ((x : Site d) j - (y : Site d) j).natAbs := by
      rcases Nat.eq_zero_or_pos ((x : Site d) j - (y : Site d) j).natAbs with h | h
      · exact absurd (by omega : (x : Site d) j = (y : Site d) j) hc
      · omega
    have hine : 1 ≤ ((x : Site d) i - (y : Site d) i).natAbs := Nat.one_le_iff_ne_zero.mpr hi
    omega
  have hsigns : (fun i => decide (0 < (x : Site d) i)) = (fun i => decide (0 < (y : Site d) i)) := by
    funext j; by_cases hj : j = i
    · subst hj
      have hxi := hxnz j; have hyi := hyc j
      have hone : ((x : Site d) j - (y : Site d) j).natAbs = 1 := by
        have heq : ∑ k, ((x : Site d) k - (y : Site d) k).natAbs
            = ((x : Site d) j - (y : Site d) j).natAbs := by
          rw [Finset.sum_eq_single j]
          · intro b _ hb; rw [hother b hb]; simp
          · intro h; exact absurd (Finset.mem_univ _) h
        omega
      have hiff : (0 < (x : Site d) j) ↔ (0 < (y : Site d) j) := by omega
      simp only [hiff]
    · rw [hother j hj]
  rw [hsigns] at hx
  exact hy (hyt.trans (by rw [hx]))


theorem qp_tag_none_iff (d K : ℕ) (x : boxVerts d (2 * K + 1)) :
    qp_boxTag d K x = none ↔ ∃ i, (x : Site d) i = 0 := by
  unfold qp_boxTag
  by_cases hz : ∃ i, (x : Site d) i = 0
  · rw [if_pos hz]; simp [hz]
  · rw [if_neg hz]; simp [hz]


theorem qp_straddle_endpoint_in_J_all (d K : ℕ) (τ : Option (Fin d → Bool))
    (x y : boxVerts d (2 * K + 1)) (hadj : (boxGraph d (2 * K + 1)).Adj x y)
    (hx : qp_boxTag d K x = τ) (hy : qp_boxTag d K y ≠ τ) :
    (∃ i, (x : Site d) i = 0) ∨ (∃ i, (y : Site d) i = 0) := by
  cases τ with
  | none => left; exact (qp_tag_none_iff d K x).mp hx
  | some s => right; exact qp_straddle_endpoint_in_J d K s x y hadj hx hy


theorem qp_straddle_subset_all (d K : ℕ) (τ : Option (Fin d → Bool)) :
    qp_straddleEdges (boxGraph d (2 * K + 1)) (fun x => qp_boxTag d K x = τ)
      ⊆ (qp_Jset d K).biUnion (fun v => (boxGraph d (2 * K + 1)).incidenceFinset v) := by
  intro e he
  rw [qp_straddleEdges, Finset.mem_filter] at he
  obtain ⟨hedge, hstr⟩ := he
  rw [Finset.mem_biUnion]
  rw [mem_edgeFinset] at hedge
  induction e using Sym2.ind with
  | _ x y =>
    rw [qp_straddleP, Sym2.lift_mk] at hstr
    rw [mem_edgeSet] at hedge
    rcases hstr with ⟨hxq, hyq⟩ | ⟨hxq, hyq⟩
    · rcases qp_straddle_endpoint_in_J_all d K τ x y hedge hxq hyq with ⟨i, hi⟩ | ⟨i, hi⟩
      · refine ⟨x, by rw [qp_Jset, Finset.mem_filter]; exact ⟨Finset.mem_univ _, ⟨i, hi⟩⟩, ?_⟩
        rw [SimpleGraph.mem_incidenceFinset]
        exact ⟨by rw [mem_edgeSet]; exact hedge, Sym2.mem_mk_left _ _⟩
      · refine ⟨y, by rw [qp_Jset, Finset.mem_filter]; exact ⟨Finset.mem_univ _, ⟨i, hi⟩⟩, ?_⟩
        rw [SimpleGraph.mem_incidenceFinset]
        exact ⟨by rw [mem_edgeSet]; exact hedge, Sym2.mem_mk_right _ _⟩
    · rcases qp_straddle_endpoint_in_J_all d K τ y x hedge.symm hyq hxq with ⟨i, hi⟩ | ⟨i, hi⟩
      · refine ⟨y, by rw [qp_Jset, Finset.mem_filter]; exact ⟨Finset.mem_univ _, ⟨i, hi⟩⟩, ?_⟩
        rw [SimpleGraph.mem_incidenceFinset]
        exact ⟨by rw [mem_edgeSet]; exact hedge, Sym2.mem_mk_right _ _⟩
      · refine ⟨x, by rw [qp_Jset, Finset.mem_filter]; exact ⟨Finset.mem_univ _, ⟨i, hi⟩⟩, ?_⟩
        rw [SimpleGraph.mem_incidenceFinset]
        exact ⟨by rw [mem_edgeSet]; exact hedge, Sym2.mem_mk_left _ _⟩


theorem qp_straddle_card_le_all (d K : ℕ) (τ : Option (Fin d → Bool)) :
    (qp_straddleEdges (boxGraph d (2 * K + 1)) (fun x => qp_boxTag d K x = τ)).card
      ≤ 2 * d * (qp_Jset d K).card := by
  calc (qp_straddleEdges (boxGraph d (2 * K + 1)) (fun x => qp_boxTag d K x = τ)).card
      ≤ ((qp_Jset d K).biUnion (fun v => (boxGraph d (2 * K + 1)).incidenceFinset v)).card :=
        Finset.card_le_card (qp_straddle_subset_all d K τ)
    _ ≤ ∑ v ∈ qp_Jset d K, ((boxGraph d (2 * K + 1)).incidenceFinset v).card :=
        Finset.card_biUnion_le
    _ = ∑ v ∈ qp_Jset d K, (boxGraph d (2 * K + 1)).degree v :=
        Finset.sum_congr rfl (fun v _ => SimpleGraph.card_incidenceFinset_eq_degree _ v)
    _ ≤ ∑ _v ∈ qp_Jset d K, 2 * d := Finset.sum_le_sum (fun v _ => qp_boxGraph_degree_le _ _ v)
    _ = (qp_Jset d K).card * (2 * d) := by rw [Finset.sum_const, smul_eq_mul]
    _ = 2 * d * (qp_Jset d K).card := by ring


theorem qp_blkNone_edge_le (d K : ℕ) :
    (qp_blkG (boxGraph d (2 * K + 1)) (qp_boxTag d K) none).edgeFinset.card
      ≤ 2 * d * (qp_Jset d K).card := by
  calc (qp_blkG (boxGraph d (2 * K + 1)) (qp_boxTag d K) none).edgeFinset.card
      ≤ ((qp_Jset d K).biUnion (fun v => (boxGraph d (2 * K + 1)).incidenceFinset v)).card := by
        apply Finset.card_le_card_of_injOn
          (fun e => Sym2.map (Subtype.val : {x // qp_boxTag d K x = none} → boxVerts d (2 * K + 1)) e)
        · intro e he
          rw [Finset.mem_coe, mem_edgeFinset] at he
          rw [Finset.mem_coe, Finset.mem_biUnion]
          induction e using Sym2.ind with
          | _ a b =>
            rw [mem_edgeSet, qp_blkG, comap_adj] at he
            have haJ : ∃ i, ((a : boxVerts d (2 * K + 1)) : Site d) i = 0 := by
              have ha := a.2; unfold qp_boxTag at ha
              by_cases hz : ∃ i, ((a : boxVerts d (2 * K + 1)) : Site d) i = 0
              · exact hz
              · rw [if_neg hz] at ha; exact absurd ha (by simp)
            refine ⟨(a : boxVerts d (2 * K + 1)),
              by rw [qp_Jset, Finset.mem_filter]; exact ⟨Finset.mem_univ _, haJ⟩, ?_⟩
            rw [SimpleGraph.mem_incidenceFinset]
            simp only [Sym2.map_pair_eq]
            exact ⟨by rw [mem_edgeSet]; exact he, Sym2.mem_mk_left _ _⟩
        · intro a _ b _ hab; exact Sym2.map.injective Subtype.val_injective hab
    _ ≤ ∑ v ∈ qp_Jset d K, ((boxGraph d (2 * K + 1)).incidenceFinset v).card :=
        Finset.card_biUnion_le
    _ = ∑ v ∈ qp_Jset d K, (boxGraph d (2 * K + 1)).degree v :=
        Finset.sum_congr rfl (fun v _ => SimpleGraph.card_incidenceFinset_eq_degree _ v)
    _ ≤ ∑ _v ∈ qp_Jset d K, 2 * d := Finset.sum_le_sum (fun v _ => qp_boxGraph_degree_le _ _ v)
    _ = (qp_Jset d K).card * (2 * d) := by rw [Finset.sum_const, smul_eq_mul]
    _ = 2 * d * (qp_Jset d K).card := by ring


noncomputable def qp_restGUnivIso (d K : ℕ) :
    qp_restG (boxGraph d (2 * K + 1)) (qp_boxTag d K) Finset.univ ≃g boxGraph d (2 * K + 1) where
  toEquiv := Equiv.subtypeUnivEquiv (fun x => Finset.mem_univ (qp_boxTag d K x))
  map_rel_iff' := by intro a b; rfl

theorem qp_restG_univ_fkZ (d K : ℕ) (p q : ℝ) :
    fkZ (qp_restG (boxGraph d (2 * K + 1)) (qp_boxTag d K) Finset.univ) p q
      = fkZ (boxGraph d (2 * K + 1)) p q :=
  fsm_fkZ_iso _ _ (qp_restGUnivIso d K) p q











theorem qp_box_neglog_doubling (d K : ℕ) (t : ℝ) :
    agl_u d t (2 * K + 1) ≤ (2 : ℝ) ^ d * agl_u d t K
      + ((2 * d * (qp_Jset d K).card + (2 ^ d + 1) * (2 * d * (qp_Jset d K).card) : ℕ) : ℝ)
          * (-Real.log (1 - fsc_logistic t)) := by
  set p := fsc_logistic t with hp
  have hp0 : (0 : ℝ) < p := fsc_logistic_pos t
  have hp1 : p < 1 := fsc_logistic_lt_one t
  set c := -Real.log (1 - p) with hc
  have hc0 : 0 ≤ c := by rw [hc, neg_nonneg]; exact Real.log_nonpos (by linarith) (by linarith)
  obtain ⟨I, hIle, hIbd⟩ :=
    qp_peel_le (boxGraph d (2 * K + 1)) (qp_boxTag d K) p 2 hp0 hp1 (by norm_num) Finset.univ
  have hrest : qp_uu (qp_restG (boxGraph d (2 * K + 1)) (qp_boxTag d K) Finset.univ) p 2
      = agl_u d t (2 * K + 1) := by rw [qp_uu, qp_restG_univ_fkZ]; rfl
  have hblksum : (∑ τ ∈ (Finset.univ : Finset (Option (Fin d → Bool))),
        qp_uu (qp_blkG (boxGraph d (2 * K + 1)) (qp_boxTag d K) τ) p 2)
      = qp_uu (qp_blkG (boxGraph d (2 * K + 1)) (qp_boxTag d K) none) p 2 + (2 : ℝ) ^ d * agl_u d t K := by
    rw [show (∑ τ ∈ (Finset.univ : Finset (Option (Fin d → Bool))),
            qp_uu (qp_blkG (boxGraph d (2 * K + 1)) (qp_boxTag d K) τ) p 2)
          = ∑ τ : Option (Fin d → Bool),
              qp_uu (qp_blkG (boxGraph d (2 * K + 1)) (qp_boxTag d K) τ) p 2 from rfl,
      Fintype.sum_option]
    congr 1
    have heach : ∀ s : Fin d → Bool,
        qp_uu (qp_blkG (boxGraph d (2 * K + 1)) (qp_boxTag d K) (some s)) p 2 = agl_u d t K :=
      fun s => by rw [qp_uu, qp_block_fkZ]; rfl
    rw [Finset.sum_congr rfl (fun s _ => heach s), Finset.sum_const, Finset.card_univ,
      show Fintype.card (Fin d → Bool) = 2 ^ d from by simp [Fintype.card_fun, Fintype.card_bool],
      nsmul_eq_mul]
    push_cast; ring
  have hnone : qp_uu (qp_blkG (boxGraph d (2 * K + 1)) (qp_boxTag d K) none) p 2
      ≤ ((2 * d * (qp_Jset d K).card : ℕ) : ℝ) * c := by
    rw [qp_uu]
    calc -Real.log (fkZ (qp_blkG (boxGraph d (2 * K + 1)) (qp_boxTag d K) none) p 2)
        ≤ ((qp_blkG (boxGraph d (2 * K + 1)) (qp_boxTag d K) none).edgeFinset.card : ℝ) * c :=
          qp_neglogZ_le_edges _ hp0 hp1 (by norm_num)
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




theorem qp_edge_le (d K : ℕ) (hd : 1 ≤ d) :
    (2 : ℝ) ^ d * ((boxGraph d K).edgeFinset.card) ≤ ((boxGraph d (2 * K + 1)).edgeFinset.card) := by
  rw [EdgeCount.boxGraph_edgeCard d K hd, EdgeCount.boxGraph_edgeCard d (2 * K + 1) hd]
  push_cast
  have key : (2 : ℝ) ^ d * (2 * K * (2 * K + 1) ^ (d - 1))
      ≤ (2 * (2 * K + 1)) * (2 * (2 * K + 1) + 1) ^ (d - 1) := by
    have h2d : (2 : ℝ) ^ d = 2 * 2 ^ (d - 1) := by rw [← pow_succ']; congr 1; omega
    rw [h2d, show (2 : ℝ) * 2 ^ (d - 1) * (2 * K * (2 * K + 1) ^ (d - 1))
          = (4 * K) * (2 * (2 * K + 1)) ^ (d - 1) by rw [mul_pow]; ring,
      show (2 : ℝ) * (2 * K + 1) = 4 * K + 2 by ring]
    apply mul_le_mul
    · linarith
    · apply pow_le_pow_left₀ (by positivity); linarith
    · positivity
    · positivity
  nlinarith [key, Nat.cast_nonneg (α := ℝ) d]


theorem qp_edge_gap_le (d K : ℕ) (hd : 1 ≤ d) :
    (((boxGraph d (2 * K + 1)).edgeFinset.card : ℝ)) - (2 : ℝ) ^ d * ((boxGraph d K).edgeFinset.card)
      ≤ (d : ℝ) * (d + 2) * (4 * K + 3) ^ (d - 1) := by
  rw [EdgeCount.boxGraph_edgeCard d K hd, EdgeCount.boxGraph_edgeCard d (2 * K + 1) hd]
  push_cast
  rw [show (2 * (2 * (K : ℝ) + 1) + 1) = 4 * K + 3 by ring,
    show (2 * (2 * (K : ℝ) + 1)) = 4 * K + 2 by ring]
  have h2d : (2 : ℝ) ^ d = 2 * 2 ^ (d - 1) := by rw [← pow_succ']; congr 1; omega
  rw [h2d,
    show (2 : ℝ) * 2 ^ (d - 1) * ((d : ℝ) * (2 * K * (2 * K + 1) ^ (d - 1)))
        = (d : ℝ) * ((4 * K) * (2 * (2 * K + 1)) ^ (d - 1)) by rw [mul_pow]; ring,
    show (2 : ℝ) * (2 * K + 1) = 4 * K + 2 by ring,
    ← mul_sub,
    show (d : ℝ) * (d + 2) * (4 * K + 3) ^ (d - 1) = (d : ℝ) * ((d + 2) * (4 * K + 3) ^ (d - 1)) by ring]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  rw [show (4 * (K : ℝ) + 2) * (4 * K + 3) ^ (d - 1) - (4 * K) * (4 * K + 2) ^ (d - 1)
        = (4 * K + 2) * ((4 * K + 3) ^ (d - 1) - (4 * K + 2) ^ (d - 1)) + 2 * (4 * K + 2) ^ (d - 1)
      by ring]
  have hpow := boxSV_pow_sub_pow_le (4 * (K : ℝ) + 3) (4 * K + 2) (by positivity) (by linarith) (d - 1)
  rw [show (4 * (K : ℝ) + 3) - (4 * K + 2) = 1 by ring, one_mul] at hpow
  have h1 : (4 * (K : ℝ) + 2) * ((4 * K + 3) ^ (d - 1) - (4 * K + 2) ^ (d - 1))
      ≤ (4 * K + 2) * (((d - 1 : ℕ) : ℝ) * (4 * K + 3) ^ (d - 1 - 1)) :=
    mul_le_mul_of_nonneg_left hpow (by positivity)
  have h2 : (4 * (K : ℝ) + 2) * (((d - 1 : ℕ) : ℝ) * (4 * K + 3) ^ (d - 1 - 1))
      ≤ ((d : ℝ) - 1) * (4 * K + 3) ^ (d - 1) := by
    rcases Nat.lt_or_ge d 2 with h | h
    · have hd1 : d = 1 := by omega
      subst hd1; simp
    · have hcast : ((d - 1 : ℕ) : ℝ) = (d : ℝ) - 1 := by rw [Nat.cast_sub (by omega)]; norm_num
      rw [hcast, show (4 * (K : ℝ) + 3) ^ (d - 1) = (4 * K + 3) * (4 * K + 3) ^ (d - 1 - 1) from by
            rw [← pow_succ']; congr 1; omega,
        show (4 * (K : ℝ) + 2) * (((d : ℝ) - 1) * (4 * K + 3) ^ (d - 1 - 1))
            = ((d : ℝ) - 1) * ((4 * K + 2) * (4 * K + 3) ^ (d - 1 - 1)) by ring]
      have hdpos : (0 : ℝ) ≤ (d : ℝ) - 1 := by
        have : (1 : ℝ) ≤ d := by exact_mod_cast (by omega : 1 ≤ d)
        linarith
      apply mul_le_mul_of_nonneg_left _ hdpos
      apply mul_le_mul_of_nonneg_right (by linarith) (by positivity)
  have h3 : (2 : ℝ) * (4 * K + 2) ^ (d - 1) ≤ 2 * (4 * K + 3) ^ (d - 1) := by
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    apply pow_le_pow_left₀ (by positivity); linarith
  calc (4 * (K : ℝ) + 2) * ((4 * K + 3) ^ (d - 1) - (4 * K + 2) ^ (d - 1)) + 2 * (4 * K + 2) ^ (d - 1)
      ≤ (d - 1) * (4 * K + 3) ^ (d - 1) + 2 * (4 * K + 3) ^ (d - 1) := by linarith [le_trans h1 h2, h3]
    _ = (d + 1) * (4 * K + 3) ^ (d - 1) := by ring
    _ ≤ (d + 2) * (4 * K + 3) ^ (d - 1) := by
        apply mul_le_mul_of_nonneg_right (by linarith) (by positivity)

end BoxGeom








theorem qp_edge_lower (d n : ℕ) (hd : 1 ≤ d) :
    (n : ℝ) * (2 * (n : ℝ) + 1) ^ (d - 1) ≤ ((boxGraph d n).edgeFinset.card : ℝ) := by
  have h1 := boxSV_edge_card_lower (d := d) (n := n) hd
  rw [fup_edge_card_eq d n] at h1
  have hnat : n * (2 * n + 1) ^ (d - 1) ≤ (boxGraph d n).edgeFinset.card := by
    have h2 : 2 * (n * (2 * n + 1) ^ (d - 1)) ≤ 2 * (boxGraph d n).edgeFinset.card := by
      rw [show 2 * (n * (2 * n + 1) ^ (d - 1)) = (2 * n) * (2 * n + 1) ^ (d - 1) by ring]; exact h1
    omega
  calc (n : ℝ) * (2 * (n : ℝ) + 1) ^ (d - 1) = ((n * (2 * n + 1) ^ (d - 1) : ℕ) : ℝ) := by
        push_cast; ring
    _ ≤ ((boxGraph d n).edgeFinset.card : ℝ) := by exact_mod_cast hnat




theorem qp_summable_ratio (d : ℕ) (hd : 1 ≤ d) (I : ℕ → ℝ)
    (hIbd : ∀ j, I j ≤ ((2 ^ d + 2) * (2 * d * d) + d * (d + 2) : ℝ) * (4 * (agl_K j : ℝ) + 3) ^ (d - 1))
    (hI0 : ∀ j, 0 ≤ I j) :
    Summable (fun j => I j / agl_E d (agl_K (j + 1))) := by
  set Ctot : ℝ := ((2 ^ d + 2) * (2 * d * d) + d * (d + 2) : ℝ) with hCtot
  have hCtot0 : 0 ≤ Ctot := by rw [hCtot]; positivity
  refine Summable.of_nonneg_of_le (f := fun j => Ctot * (1 / 2 : ℝ) ^ j)
    (fun j => div_nonneg (hI0 j) (by rw [agl_E]; positivity)) ?_
    ((summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left Ctot)
  intro j
  have hKsucc : agl_K (j + 1) = 2 * agl_K j + 1 := agl_K_succ j
  have hKR : (agl_K (j + 1) : ℝ) = 2 * (agl_K j : ℝ) + 1 := by rw [hKsucc]; push_cast; ring
  have hbase : 2 * (agl_K (j + 1) : ℝ) + 1 = 4 * (agl_K j : ℝ) + 3 := by rw [hKR]; ring
  have hElow : (agl_K (j + 1) : ℝ) * (4 * (agl_K j : ℝ) + 3) ^ (d - 1) ≤ agl_E d (agl_K (j + 1)) := by
    have h := qp_edge_lower d (agl_K (j + 1)) hd
    rw [agl_E, ← hbase]; exact h
  have hKj1pos : (0 : ℝ) < (agl_K (j + 1) : ℝ) := by exact_mod_cast agl_K_pos (j + 1)
  have hpowpos : (0 : ℝ) < (4 * (agl_K j : ℝ) + 3) ^ (d - 1) := by positivity
  calc I j / agl_E d (agl_K (j + 1))
      ≤ (Ctot * (4 * (agl_K j : ℝ) + 3) ^ (d - 1))
          / ((agl_K (j + 1) : ℝ) * (4 * (agl_K j : ℝ) + 3) ^ (d - 1)) :=
        div_le_div₀ (by positivity) (hIbd j) (by positivity) hElow
    _ = Ctot / (agl_K (j + 1) : ℝ) := by rw [mul_div_mul_right _ _ (ne_of_gt hpowpos)]
    _ ≤ Ctot * (1 / 2 : ℝ) ^ j := by
        have hKge : (2 : ℝ) ^ j ≤ (agl_K (j + 1) : ℝ) := by
          have hnat : (2 : ℕ) ^ j ≤ agl_K (j + 1) := by
            unfold agl_K
            have h1 : 2 ^ j ≤ 2 ^ (j + 1 + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
            have h2 : 1 ≤ 2 ^ (j + 1 + 1) := Nat.one_le_two_pow
            omega
          exact_mod_cast hnat
        have h2jpos : (0 : ℝ) < (2 : ℝ) ^ j := by positivity
        rw [show (1 / 2 : ℝ) ^ j = ((2 : ℝ) ^ j)⁻¹ from by rw [one_div, inv_pow],
          div_eq_mul_inv]
        apply mul_le_mul_of_nonneg_left _ hCtot0
        rw [inv_le_inv₀ hKj1pos h2jpos]; exact hKge





theorem qp_additiveDoublingBound (d : ℕ) (hd : 1 ≤ d) (t : ℝ) : agl_AdditiveDoublingBound d t := by
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
  · 
    apply qp_summable_ratio d hd I _ hInn
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
  · 
    intro j
    have hdbl := qp_box_neglog_doubling d (agl_K j) t
    rw [show agl_u d t (agl_K (j + 1)) = agl_u d t (2 * agl_K j + 1) from by rw [agl_K_succ]]
    have hge : N j * c ≤ I j * c := by
      rw [hI]; apply mul_le_mul_of_nonneg_right _ hc0; linarith [hGnn j]
    calc agl_u d t (2 * agl_K j + 1)
        ≤ (2 : ℝ) ^ d * agl_u d t (agl_K j) + N j * c := hdbl
      _ ≤ (2 : ℝ) ^ d * agl_u d t (agl_K j) + I j * c := by linarith
  · 
    intro j
    have hGval : G j = agl_E d (agl_K (j + 1)) - (2 : ℝ) ^ d * agl_E d (agl_K j) := rfl
    rw [abs_of_nonpos (by have := hGnn j; rw [hGval] at this; linarith)]
    rw [hI]; have hNn : 0 ≤ N j := Nat.cast_nonneg _
    have hGeq : -((2 : ℝ) ^ d * agl_E d (agl_K j) - agl_E d (agl_K (j + 1))) = G j := by
      rw [hGval]; ring
    rw [hGeq]; linarith




















theorem qp_additiveBoxFeketeData (d : ℕ) (hd : 1 ≤ d) (t : ℝ)
    (hbdd : ∃ M : ℝ, ∀ j, |agl_u d t (agl_K j) / agl_E d (agl_K j)| ≤ M)
    (hosc : ∃ (bj : ℕ → ℕ) (osc : ℕ → ℝ), Tendsto bj atTop atTop ∧ Tendsto osc atTop (𝓝 0)
        ∧ (∀ n, |ivp2_tiltFreeEnergy (boxGraph d n) 2 t
            - ivp2_tiltFreeEnergy (boxGraph d (agl_K (bj n))) 2 t| ≤ osc (bj n))) :
    agl_AdditiveBoxFeketeData d t :=
  ⟨qp_additiveDoublingBound d hd t, hbdd, hosc⟩






theorem qp_fk_uniqueness (d : ℕ) (hd : 1 ≤ d) (N : ℕ) (eb : Sym2 (boxVerts d N))
    (heb : eb ∈ (boxGraph d N).edgeFinset)
    (hEbox : ∀ n, 0 < (boxGraph d n).edgeFinset.card)
    (hbdd : ∀ t, ∃ M : ℝ, ∀ j, |agl_u d t (agl_K j) / agl_E d (agl_K j)| ≤ M)
    (hosc : ∀ t, ∃ (bj : ℕ → ℕ) (osc : ℕ → ℝ), Tendsto bj atTop atTop ∧ Tendsto osc atTop (𝓝 0)
        ∧ (∀ n, |ivp2_tiltFreeEnergy (boxGraph d n) 2 t
            - ivp2_tiltFreeEnergy (boxGraph d (agl_K (bj n))) 2 t| ≤ osc (bj n))) :
    {t : ℝ | ∃ A : Set (ConfigSpace (Sym2 (boxVerts d N))), IsIncreasing A ∧
        eventMassProb (fuc_freeMass d N t) A
          ≠ eventMassProb (fuc_wiredMass d N t) A}.Countable :=
  agl_fk_uniqueness_of_additiveData d hd N eb heb hEbox
    (fun t => qp_additiveBoxFeketeData d hd t (hbdd t) (hosc t))

end FK

end StatMech

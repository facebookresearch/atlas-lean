/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.OSSS.RevealmentConstruction

open scoped BigOperators
open Finset
open StatMech.Lattice

set_option linter.style.longLine false

namespace StatMech
namespace OSSS
namespace TreeComplete

open StatMech.OSSS
open StatMech.OSSS.DecisionTree
open StatMech.OSSS.Revealment
open StatMech.OSSS.RevealmentConstruction
open scoped Classical

variable {E : Type*} [Fintype E] [DecidableEq E]
variable {V : Type*} [DecidableEq V]

omit [Fintype E] [DecidableEq E] in

theorem subset_runState (endU endV : E → V) (ω : ConfigSpace E)
    (l : List E) (disc : Finset V) :
    disc ⊆ runState (geomGuard endU endV) (geomStep endU endV) ω l disc := by
  induction l generalizing disc with
  | nil => simp [runState]
  | cons e rest ih =>
      simp only [runState]
      by_cases hg : geomGuard endU endV disc e = true
      · rw [if_pos hg]
        refine subset_trans ?_ (ih (geomStep endU endV disc e (ω e)))
        unfold geomStep
        by_cases hb : ω e = true
        · rw [if_pos hb]
          exact subset_trans (Finset.subset_insert _ _) (Finset.subset_insert _ _)
        · simp only [Bool.not_eq_true] at hb; rw [hb]; simp
      · rw [if_neg hg]; exact ih disc

omit [Fintype E] [DecidableEq E] in

theorem subset_geomStep (endU endV : E → V) (disc : Finset V) (e : E) (b : Bool) :
    disc ⊆ geomStep endU endV disc e b := by
  unfold geomStep
  cases b with
  | false => simp
  | true => exact subset_trans (Finset.subset_insert _ _) (Finset.subset_insert _ _)

omit [Fintype E] [DecidableEq E] in

theorem runState_mono (endU endV : E → V) (ω : ConfigSpace E)
    (l : List E) {d₁ d₂ : Finset V} (h : d₁ ⊆ d₂) :
    runState (geomGuard endU endV) (geomStep endU endV) ω l d₁
      ⊆ runState (geomGuard endU endV) (geomStep endU endV) ω l d₂ := by
  induction l generalizing d₁ d₂ with
  | nil => simpa [runState] using h
  | cons e rest ih =>
      simp only [runState]
      have hguardmono : geomGuard endU endV d₁ e = true → geomGuard endU endV d₂ e = true := by
        unfold geomGuard
        simp only [decide_eq_true_eq]
        rintro (hU | hV)
        · exact Or.inl (h hU)
        · exact Or.inr (h hV)
      by_cases hg1 : geomGuard endU endV d₁ e = true
      · rw [if_pos hg1, if_pos (hguardmono hg1)]
        apply ih
        unfold geomStep
        by_cases hb : ω e = true
        · rw [if_pos hb, if_pos hb]
          exact Finset.insert_subset_insert _ (Finset.insert_subset_insert _ h)
        · simp only [Bool.not_eq_true] at hb; rw [hb]; simpa using h
      · rw [if_neg hg1]
        by_cases hg2 : geomGuard endU endV d₂ e = true
        · rw [if_pos hg2]
          exact ih (subset_trans h (subset_geomStep endU endV d₂ e (ω e)))
        · rw [if_neg hg2]; exact ih h

omit [Fintype E] [DecidableEq E] in




theorem mem_runState_of_open_edge (endU endV : E → V) (ω : ConfigSpace E)
    (l : List E) (disc : Finset V) (e : E) (he : e ∈ l) (hopen : ω e = true)
    (hend : endU e ∈ disc ∨ endV e ∈ disc) :
    endU e ∈ runState (geomGuard endU endV) (geomStep endU endV) ω l disc
      ∧ endV e ∈ runState (geomGuard endU endV) (geomStep endU endV) ω l disc := by
  induction l generalizing disc with
  | nil => simp at he
  | cons f rest ih =>
      simp only [runState]
      rcases List.mem_cons.mp he with rfl | hmem
      · 
        have hg : geomGuard endU endV disc e = true := by
          unfold geomGuard; simp only [decide_eq_true_eq]; exact hend
        rw [if_pos hg]
        have hstep : geomStep endU endV disc e (ω e) = insert (endU e) (insert (endV e) disc) := by
          unfold geomStep; rw [hopen, if_pos rfl]
        rw [hstep]
        have hsub := subset_runState endU endV ω rest (insert (endU e) (insert (endV e) disc))
        exact ⟨hsub (Finset.mem_insert_self _ _),
               hsub (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))⟩
      · 
        by_cases hg : geomGuard endU endV disc f = true
        · rw [if_pos hg]
          refine ih (geomStep endU endV disc f (ω f)) hmem ?_
          have hsub := subset_geomStep endU endV disc f (ω f)
          rcases hend with hU | hV
          · exact Or.inl (hsub hU)
          · exact Or.inr (hsub hV)
        · rw [if_neg hg]; exact ih disc hmem hend








def endpointsFinset (endU endV : E → V) (l : List E) : Finset V :=
  l.toFinset.image endU ∪ l.toFinset.image endV

omit [Fintype E] in

theorem runState_subset_union (endU endV : E → V) (ω : ConfigSpace E)
    (l : List E) (disc : Finset V) :
    runState (geomGuard endU endV) (geomStep endU endV) ω l disc
      ⊆ disc ∪ endpointsFinset endU endV l := by
  induction l generalizing disc with
  | nil => simp only [runState]; exact Finset.subset_union_left
  | cons e rest ih =>
      simp only [runState]
      by_cases hg : geomGuard endU endV disc e = true
      · rw [if_pos hg]
        refine subset_trans (ih (geomStep endU endV disc e (ω e))) ?_
        intro x hx
        rw [Finset.mem_union] at hx
        rcases hx with hstep | hrest
        · 
          unfold geomStep at hstep
          by_cases hb : ω e = true
          · rw [if_pos hb] at hstep
            rw [Finset.mem_insert, Finset.mem_insert] at hstep
            rcases hstep with rfl | rfl | hd
            · refine Finset.mem_union_right _ ?_
              unfold endpointsFinset
              exact Finset.mem_union_left _ (Finset.mem_image.mpr
                ⟨e, by simp [List.mem_toFinset], rfl⟩)
            · refine Finset.mem_union_right _ ?_
              unfold endpointsFinset
              exact Finset.mem_union_right _ (Finset.mem_image.mpr
                ⟨e, by simp [List.mem_toFinset], rfl⟩)
            · exact Finset.mem_union_left _ hd
          · simp only [Bool.not_eq_true] at hb; rw [hb, if_neg (by decide)] at hstep
            exact Finset.mem_union_left _ hstep
        · 
          refine Finset.mem_union_right _ ?_
          unfold endpointsFinset at hrest ⊢
          rw [Finset.mem_union] at hrest ⊢
          rcases hrest with hu | hv
          · exact Or.inl (by
              rw [Finset.mem_image] at hu ⊢; obtain ⟨a, ha, rfl⟩ := hu
              exact ⟨a, by simp only [List.mem_toFinset, List.mem_cons]; exact Or.inr (List.mem_toFinset.mp ha), rfl⟩)
          · exact Or.inr (by
              rw [Finset.mem_image] at hv ⊢; obtain ⟨a, ha, rfl⟩ := hv
              exact ⟨a, by simp only [List.mem_toFinset, List.mem_cons]; exact Or.inr (List.mem_toFinset.mp ha), rfl⟩)
      · rw [if_neg hg]
        refine subset_trans (ih disc) ?_
        intro x hx
        rw [Finset.mem_union] at hx
        rcases hx with hd | hrest
        · exact Finset.mem_union_left _ hd
        · refine Finset.mem_union_right _ ?_
          unfold endpointsFinset at hrest ⊢
          rw [Finset.mem_union] at hrest ⊢
          rcases hrest with hu | hv
          · exact Or.inl (by
              rw [Finset.mem_image] at hu ⊢; obtain ⟨a, ha, rfl⟩ := hu
              exact ⟨a, by simp only [List.mem_toFinset, List.mem_cons]; exact Or.inr (List.mem_toFinset.mp ha), rfl⟩)
          · exact Or.inr (by
              rw [Finset.mem_image] at hv ⊢; obtain ⟨a, ha, rfl⟩ := hv
              exact ⟨a, by simp only [List.mem_toFinset, List.mem_cons]; exact Or.inr (List.mem_toFinset.mp ha), rfl⟩)









def Saturated (endU endV : E → V) (ω : ConfigSpace E) (l : List E) (D : Finset V) : Prop :=
  ∀ e ∈ l, ω e = true → (endU e ∈ D ∨ endV e ∈ D) → endU e ∈ D ∧ endV e ∈ D

omit [Fintype E] [DecidableEq E] [DecidableEq V] in




theorem mem_of_reachOpen_of_saturated (endU endV : E → V) (ω : ConfigSpace E)
    (l : List E) (D : Finset V) (hsat : Saturated endU endV ω l D)
    (hl : ∀ e, e ∈ l) {x b : V} (h : ReachOpen endU endV ω x b) (hb : b ∈ D) : x ∈ D := by
  induction h with
  | refl x => exact hb
  | step e hopen hxy _ ih =>
      
      have hyD : _ := ih hb
      rcases hxy with ⟨hU, hV⟩ | ⟨hU, hV⟩
      · 
        have : endU e ∈ D ∧ endV e ∈ D :=
          hsat e (hl e) hopen (Or.inr (hV ▸ hyD))
        exact hU ▸ this.1
      · 
        have : endU e ∈ D ∧ endV e ∈ D :=
          hsat e (hl e) hopen (Or.inl (hU ▸ hyD))
        exact hV ▸ this.2

omit [Fintype E] [DecidableEq E] in



theorem saturated_of_fixpoint (endU endV : E → V) (ω : ConfigSpace E)
    (l : List E) (D : Finset V)
    (hfix : runState (geomGuard endU endV) (geomStep endU endV) ω l D = D) :
    Saturated endU endV ω l D := by
  intro e he hopen hend
  have h := mem_runState_of_open_edge endU endV ω l D e he hopen hend
  rw [hfix] at h
  exact h

omit [Fintype E] [DecidableEq E] in

theorem runState_append (endU endV : E → V) (ω : ConfigSpace E)
    (l₁ l₂ : List E) (disc : Finset V) :
    runState (geomGuard endU endV) (geomStep endU endV) ω (l₁ ++ l₂) disc
      = runState (geomGuard endU endV) (geomStep endU endV) ω l₂
          (runState (geomGuard endU endV) (geomStep endU endV) ω l₁ disc) := by
  induction l₁ generalizing disc with
  | nil => simp [runState]
  | cons e rest ih =>
      simp only [List.cons_append, runState]
      by_cases hg : geomGuard endU endV disc e = true
      · rw [if_pos hg, if_pos hg]; exact ih _
      · rw [if_neg hg, if_neg hg]; exact ih _


def repeatList (l : List E) : ℕ → List E
  | 0 => []
  | n + 1 => l ++ repeatList l n

omit [Fintype E] [DecidableEq E] in

theorem runState_repeatList (endU endV : E → V) (ω : ConfigSpace E)
    (l : List E) (n : ℕ) (disc : Finset V) :
    runState (geomGuard endU endV) (geomStep endU endV) ω (repeatList l n) disc
      = (fun D => runState (geomGuard endU endV) (geomStep endU endV) ω l D)^[n] disc := by
  induction n generalizing disc with
  | zero => simp [repeatList, runState]
  | succ k ih =>
      rw [repeatList, runState_append, Function.iterate_succ, Function.comp_apply]
      exact ih _














theorem fixpoint_iterate_card {V : Type*} [DecidableEq V]
    (f : Finset V → Finset V) (U : Finset V)
    (hinfl : ∀ D, D ⊆ f D) (hbound : ∀ D, D ⊆ U → f D ⊆ U)
    (D₀ : Finset V) (hD₀ : D₀ ⊆ U) :
    f (f^[U.card] D₀) = f^[U.card] D₀ := by
  have hiter_sub : ∀ n, f^[n] D₀ ⊆ U := by
    intro n; induction n with
    | zero => simpa using hD₀
    | succ k ih => rw [Function.iterate_succ', Function.comp_apply]; exact hbound _ ih
  have habsorb : ∀ k m, f (f^[k] D₀) = f^[k] D₀ → f^[k + m] D₀ = f^[k] D₀ := by
    intro k m hk
    induction m with
    | zero => rfl
    | succ j ih =>
      have hstep : f^[k + (j + 1)] D₀ = f (f^[k + j] D₀) := by
        rw [show k + (j + 1) = (k + j) + 1 from by ring, Function.iterate_succ',
          Function.comp_apply]
      rw [hstep, ih, hk]
  by_contra hcon
  have hnofix : ∀ k, k ≤ U.card → f (f^[k] D₀) ≠ f^[k] D₀ := by
    intro k hk hfk
    apply hcon
    obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_le hk
    rw [hm, habsorb k m hfk, hfk]
  have hstrict : ∀ k, k < U.card → (f^[k] D₀).card < (f^[k + 1] D₀).card := by
    intro k hk
    have hne := hnofix k (le_of_lt hk)
    have heq : f^[k + 1] D₀ = f (f^[k] D₀) := by
      rw [Function.iterate_succ', Function.comp_apply]
    rw [heq]
    exact Finset.card_lt_card (lt_of_le_of_ne (hinfl _) (fun h => hne h.symm))
  have hge : ∀ k, k ≤ U.card → k ≤ (f^[k] D₀).card := by
    intro k hk; induction k with
    | zero => exact Nat.zero_le _
    | succ j ih =>
        exact Nat.lt_of_le_of_lt (ih (le_of_lt (Nat.lt_of_succ_le hk)))
          (hstrict j (Nat.lt_of_succ_le hk))
  have hne := hnofix U.card le_rfl
  have heq : f^[U.card + 1] D₀ = f (f^[U.card] D₀) := by
    rw [Function.iterate_succ', Function.comp_apply]
  have hstr : (f^[U.card] D₀).card < (f^[U.card + 1] D₀).card := by
    rw [heq]; exact Finset.card_lt_card (lt_of_le_of_ne (hinfl _) (fun h => hne h.symm))
  have h1 : U.card ≤ (f^[U.card] D₀).card := hge _ le_rfl
  have hle : (f^[U.card + 1] D₀).card ≤ U.card := Finset.card_le_card (hiter_sub _)
  omega







omit [Fintype E] in



theorem runState_repeatList_saturated (endU endV : E → V) (ω : ConfigSpace E)
    (l : List E) (disc₀ : Finset V) :
    Saturated endU endV ω l
      (runState (geomGuard endU endV) (geomStep endU endV) ω
        (repeatList l (disc₀ ∪ endpointsFinset endU endV l).card) disc₀) := by
  set U := disc₀ ∪ endpointsFinset endU endV l with hU
  set pass := fun D => runState (geomGuard endU endV) (geomStep endU endV) ω l D with hpass
  have hinfl : ∀ D, D ⊆ pass D := fun D => subset_runState endU endV ω l D
  have hbound : ∀ D, D ⊆ U → pass D ⊆ U := by
    intro D hD
    refine subset_trans (runState_subset_union endU endV ω l D) ?_
    rw [hU]
    intro x hx
    rw [Finset.mem_union] at hx
    rcases hx with hd | hep
    · exact hD hd
    · exact Finset.mem_union_right _ hep
  have hD₀ : disc₀ ⊆ U := Finset.subset_union_left
  have hfix : pass (pass^[U.card] disc₀) = pass^[U.card] disc₀ :=
    fixpoint_iterate_card pass U hinfl hbound disc₀ hD₀
  
  have hrun : runState (geomGuard endU endV) (geomStep endU endV) ω
      (repeatList l U.card) disc₀ = pass^[U.card] disc₀ :=
    runState_repeatList endU endV ω l U.card disc₀
  rw [hrun]
  exact saturated_of_fixpoint endU endV ω l (pass^[U.card] disc₀) hfix








omit [Fintype E] in




theorem mem_runState_repeatList_of_connOpenSet (endU endV : E → V) (ω : ConfigSpace E)
    (l : List E) (hl : ∀ e, e ∈ l) (B : Set V) (disc₀ : Finset V)
    (hBdisc : ∀ b ∈ B, b ∈ disc₀) {o : V} (h : ConnOpenSet endU endV ω o B) :
    o ∈ runState (geomGuard endU endV) (geomStep endU endV) ω
        (repeatList l (disc₀ ∪ endpointsFinset endU endV l).card) disc₀ := by
  obtain ⟨b, hbB, hreach⟩ := h
  set N := (disc₀ ∪ endpointsFinset endU endV l).card with hN
  set D := runState (geomGuard endU endV) (geomStep endU endV) ω (repeatList l N) disc₀ with hD
  have hsat : Saturated endU endV ω l D := runState_repeatList_saturated endU endV ω l disc₀
  
  have hbD : b ∈ D := by
    have hbdisc : b ∈ disc₀ := hBdisc b hbB
    have hsub : disc₀ ⊆ D := by
      rw [hD, runState_repeatList]
      
      have : ∀ k, disc₀ ⊆ (fun D => runState (geomGuard endU endV) (geomStep endU endV) ω l D)^[k] disc₀ := by
        intro k; induction k with
        | zero => simp
        | succ j ih =>
            rw [Function.iterate_succ', Function.comp_apply]
            exact subset_trans ih (subset_runState endU endV ω l _)
      exact this N
    exact hsub hbdisc
  exact mem_of_reachOpen_of_saturated endU endV ω l D hsat hl hreach hbD
















noncomputable def completeTree (endU endV : E → V) (o : V) (l : List E) (disc₀ : Finset V) :
    DecisionTree E :=
  exploreTree endU endV (fun disc => decide (o ∈ disc))
    (repeatList l (disc₀ ∪ endpointsFinset endU endV l).card) disc₀

omit [Fintype E] in









theorem eval_completeTree_iff (endU endV : E → V) (o : V) (B : Set V)
    (l : List E) (hl : ∀ e, e ∈ l) (disc₀ : Finset V)
    (hdisc₀ : ∀ x ∈ disc₀, x ∈ B) (hBdisc : ∀ b ∈ B, b ∈ disc₀) (ω : ConfigSpace E) :
    (completeTree endU endV o l disc₀).eval ω = true ↔ ConnOpenSet endU endV ω o B := by
  constructor
  · intro h
    exact eval_exploreTree_imp_conn endU endV o B _ disc₀ hdisc₀ ω h
  · intro h
    
    unfold completeTree exploreTree
    rw [eval_buildTree]
    simp only [decide_eq_true_eq]
    exact mem_runState_repeatList_of_connOpenSet endU endV ω l hl B disc₀ hBdisc h

omit [Fintype E] in








theorem evalR_completeTree (endU endV : E → V) (o : V) (B : Set V)
    (l : List E) (hl : ∀ e, e ∈ l) (disc₀ : Finset V)
    (hdisc₀ : ∀ x ∈ disc₀, x ∈ B) (hBdisc : ∀ b ∈ B, b ∈ disc₀) (ω : ConfigSpace E)
    [Decidable (ConnOpenSet endU endV ω o B)] :
    (completeTree endU endV o l disc₀).evalR ω
      = if ConnOpenSet endU endV ω o B then (1 : ℝ) else 0 := by
  unfold DecisionTree.evalR
  by_cases hconn : ConnOpenSet endU endV ω o B
  · rw [if_pos ((eval_completeTree_iff endU endV o B l hl disc₀ hdisc₀ hBdisc ω).mpr hconn),
      if_pos hconn]
  · have heval : (completeTree endU endV o l disc₀).eval ω ≠ true :=
      fun h => hconn ((eval_completeTree_iff endU endV o B l hl disc₀ hdisc₀ hBdisc ω).mp h)
    rw [if_neg heval, if_neg hconn]








section Lattice

variable {d : ℕ}

omit [DecidableEq E] in



theorem exists_abstract_open_edge {edge : E → Sym2 (Site d)} {endU endV : E → Site d}
    {ω : ConfigSpace E} (hcoh : ∀ e, edge e = s(endU e, endV e))
    {u v : Site d} (hopen : liftCfg edge ω s(u, v) = true) :
    ∃ e, ω e = true ∧ ((endU e = u ∧ endV e = v) ∨ (endU e = v ∧ endV e = u)) := by
  unfold liftCfg at hopen
  by_cases hex : ∃ e, edge e = s(u, v)
  · rw [dif_pos hex] at hopen
    refine ⟨hex.choose, hopen, ?_⟩
    have hch : edge hex.choose = s(u, v) := hex.choose_spec
    rw [hcoh hex.choose, Sym2.eq_iff] at hch; exact hch
  · rw [dif_neg hex] at hopen; exact absurd hopen (by simp)

omit [DecidableEq E] in




theorem connected_imp_reachOpen {edge : E → Sym2 (Site d)} {endU endV : E → Site d}
    {ω : ConfigSpace E} (hcoh : ∀ e, edge e = s(endU e, endV e))
    {x y : Site d} (h : Connected d (liftCfg edge ω) x y) :
    ReachOpen endU endV ω x y := by
  obtain ⟨w⟩ := h
  induction w with
  | nil => exact ReachOpen.refl _
  | @cons a b c hadj p ih =>
      have hopen : liftCfg edge ω s(a, b) = true := hadj.2
      obtain ⟨e, hωe, hpair⟩ := exists_abstract_open_edge hcoh hopen
      exact ReachOpen.step e hωe hpair ih

omit [DecidableEq E] in


theorem connectedToSet_imp_connOpenSet {edge : E → Sym2 (Site d)} {endU endV : E → Site d}
    (hcoh : ∀ e, edge e = s(endU e, endV e)) {ω : ConfigSpace E} {x : Site d} {B : Set (Site d)}
    (h : ConnectedToSet d (liftCfg edge ω) x B) : ConnOpenSet endU endV ω x B := by
  obtain ⟨b, hbB, hconn⟩ := h
  exact ⟨b, hbB, connected_imp_reachOpen hcoh hconn⟩














theorem evalR_completeTree_connected {edge : E → Sym2 (Site d)}
    (hinj : Function.Injective edge) {endU endV : E → Site d}
    (hcoh : ∀ e, edge e = s(endU e, endV e))
    (hadj : ∀ e, (hypercubicLattice d).Adj (endU e) (endV e))
    (o : Site d) (B : Set (Site d)) (l : List E) (hl : ∀ e, e ∈ l) (disc₀ : Finset (Site d))
    (hdisc₀ : ∀ x ∈ disc₀, x ∈ B) (hBdisc : ∀ b ∈ B, b ∈ disc₀) (ω : ConfigSpace E)
    [Decidable (ConnectedToSet d (liftCfg edge ω) o B)] :
    (completeTree endU endV o l disc₀).evalR ω
      = if ConnectedToSet d (liftCfg edge ω) o B then (1 : ℝ) else 0 := by
  unfold DecisionTree.evalR
  by_cases hconn : ConnectedToSet d (liftCfg edge ω) o B
  · have hopenconn : ConnOpenSet endU endV ω o B := connectedToSet_imp_connOpenSet hcoh hconn
    rw [if_pos ((eval_completeTree_iff endU endV o B l hl disc₀ hdisc₀ hBdisc ω).mpr hopenconn),
      if_pos hconn]
  · have heval : (completeTree endU endV o l disc₀).eval ω ≠ true := by
      intro h
      have hopenconn := (eval_completeTree_iff endU endV o B l hl disc₀ hdisc₀ hBdisc ω).mp h
      exact hconn (connOpenSet_imp_connectedToSet hinj hcoh hadj hopenconn)
    rw [if_neg heval, if_neg hconn]

end Lattice

end TreeComplete
end OSSS
end StatMech

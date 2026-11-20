/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


























































import Code.OSSS.TreeComplete

open scoped BigOperators
open Finset
open StatMech.Lattice

set_option linter.style.longLine false

namespace StatMech
namespace OSSS

open StatMech.OSSS.DecisionTree
open StatMech.OSSS.Revealment
open StatMech.OSSS.RevealmentConstruction
open StatMech.OSSS.TreeComplete
open scoped Classical

variable {E : Type*} [Fintype E] [DecidableEq E]
variable {V : Type*} [DecidableEq V]








omit [Fintype E] [DecidableEq E] [DecidableEq V] in

theorem reachOpen_symm {endU endV : E → V} {ω : ConfigSpace E} {x y : V}
    (h : ReachOpen endU endV ω x y) : ReachOpen endU endV ω y x := by
  induction h with
  | refl x => exact ReachOpen.refl x
  | @step a b c e hopen hpair hrest ih =>
      have hstep : ReachOpen endU endV ω b a := by
        rcases hpair with ⟨hU, hV⟩ | ⟨hU, hV⟩
        · exact ReachOpen.step e hopen (Or.inr ⟨hU, hV⟩) (ReachOpen.refl a)
        · exact ReachOpen.step e hopen (Or.inl ⟨hU, hV⟩) (ReachOpen.refl a)
      exact ih.trans hstep








omit [Fintype E] [DecidableEq E] in

theorem cb_adj_coord_le_one (d : ℕ) (x y : Site d)
    (hadj : (hypercubicLattice d).Adj x y) (i : Fin d) :
    (x i - y i).natAbs ≤ 1 := by
  simp only [hypercubicLattice_adj] at hadj
  calc (x i - y i).natAbs
      ≤ ∑ j : Fin d, (x j - y j).natAbs :=
        Finset.single_le_sum (f := fun j => (x j - y j).natAbs)
          (by intros; positivity) (Finset.mem_univ i)
    _ = 1 := hadj

omit [Fintype E] [DecidableEq E] in


theorem cb_mem_box_of_adj_box_pred (d k : ℕ) (hk : 1 ≤ k) (x y : Site d)
    (hx : x ∈ box d (k - 1)) (hadj : (hypercubicLattice d).Adj x y) : y ∈ box d k := by
  intro i
  have hdiff : (x i - y i).natAbs ≤ 1 := cb_adj_coord_le_one d x y hadj i
  have hxi : (x i).natAbs ≤ k - 1 := hx i
  have htri : (y i).natAbs ≤ (x i).natAbs + (x i - y i).natAbs := by
    have heq : y i = (y i - x i) + x i := by ring
    have hsym : (y i - x i).natAbs = (x i - y i).natAbs := by rw [← Int.natAbs_neg, neg_sub]
    calc (y i).natAbs = ((y i - x i) + x i).natAbs := by rw [← heq]
      _ ≤ (y i - x i).natAbs + (x i).natAbs := Int.natAbs_add_le _ _
      _ = (x i - y i).natAbs + (x i).natAbs := by rw [hsym]
      _ = (x i).natAbs + (x i - y i).natAbs := by ring
  omega

omit [Fintype E] [DecidableEq E] in




theorem reachOpen_crosses {d k : ℕ} (hk : 1 ≤ k) {endU endV : E → Site d}
    {ω : ConfigSpace E} (hadj : ∀ e, (hypercubicLattice d).Adj (endU e) (endV e))
    {o b : Site d} (h : ReachOpen endU endV ω o b)
    (ho : o ∈ box d (k - 1)) (hb : b ∉ box d (k - 1)) :
    ConnOpenSet endU endV ω o (vertexBoundary d k) := by
  induction h with
  | refl x => exact absurd ho hb
  | @step x y z e hopen hxy hrest ih =>
      have hadje : (hypercubicLattice d).Adj x y := by
        rcases hxy with ⟨hU, hV⟩ | ⟨hU, hV⟩
        · rw [← hU, ← hV]; exact hadj e
        · rw [← hU, ← hV]; exact ((hypercubicLattice d).symm (hadj e))
      by_cases hyin : y ∈ box d (k - 1)
      · obtain ⟨w, hw, hreach⟩ := ih hyin hb
        exact ⟨w, hw, ReachOpen.step e hopen hxy hreach⟩
      · have hyboxk : y ∈ box d k := cb_mem_box_of_adj_box_pred d k hk x y ho hadje
        exact ⟨y, ⟨hyboxk, hyin⟩, ReachOpen.step e hopen hxy (ReachOpen.refl y)⟩

omit [Fintype E] [DecidableEq E] in





theorem connOpenSet_boundary_mono {d k n : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n)
    {endU endV : E → Site d} {ω : ConfigSpace E}
    (hadj : ∀ e, (hypercubicLattice d).Adj (endU e) (endV e)) {o : Site d}
    (ho : o ∈ box d (k - 1)) (h : ConnOpenSet endU endV ω o (vertexBoundary d n)) :
    ConnOpenSet endU endV ω o (vertexBoundary d k) := by
  obtain ⟨b, hbn, hreach⟩ := h
  
  have hbnotn1 : b ∉ box d (n - 1) := hbn.2
  have hsub : box d (k - 1) ⊆ box d (n - 1) := box_mono d (by omega)
  have hbnot : b ∉ box d (k - 1) := fun hc => hbnotn1 (hsub hc)
  exact reachOpen_crosses hk hadj hreach ho hbnot

omit [Fintype E] [DecidableEq E] in


theorem cb_not_mem_vertexBoundary {d k n : ℕ} (hkn : k ≤ n) {o : Site d}
    (ho : o ∈ box d (k - 1)) : o ∉ vertexBoundary d n := by
  intro hcon
  have : o ∈ box d (n - 1) := box_mono d (show k - 1 ≤ n - 1 by omega) ho
  exact hcon.2 this










abbrev XState (V : Type*) := Finset V × Finset V




def xbGuard (endU endV : E → V) (s : XState V) (e : E) : Bool :=
  decide (endU e ∈ s.1 ∨ endV e ∈ s.1)



def xbStep (endU endV : E → V) (o : V) (s : XState V) (e : E) (b : Bool) : XState V :=
  let D' := if b then insert (endU e) (insert (endV e) s.1) else s.1
  let D0a := if b ∧ (endU e ∈ s.2 ∨ endV e ∈ s.2)
             then insert (endU e) (insert (endV e) s.2) else s.2
  let D0' := if o ∈ D' then insert o D0a else D0a
  (D', D0')

omit [Fintype E] [DecidableEq E] in

theorem fst_xbStep (endU endV : E → V) (o : V) (s : XState V) (e : E) (b : Bool) :
    (xbStep endU endV o s e b).1 = geomStep endU endV s.1 e b := by
  unfold xbStep geomStep
  by_cases hb : b
  · simp [hb]
  · simp only [Bool.not_eq_true] at hb; simp [hb]

omit [Fintype E] [DecidableEq E] in


theorem snd_xbStep_eq (endU endV : E → V) (o : V) (s : XState V) (e : E) (b : Bool) :
    (xbStep endU endV o s e b).2 =
      (if o ∈ geomStep endU endV s.1 e b then insert o else id)
        (if b = true ∧ (endU e ∈ s.2 ∨ endV e ∈ s.2)
          then insert (endU e) (insert (endV e) s.2) else s.2) := by
  conv_lhs => unfold xbStep
  simp only
  rw [show (if b then insert (endU e) (insert (endV e) s.1) else s.1)
      = geomStep endU endV s.1 e b from by unfold geomStep; rfl]
  by_cases ho : o ∈ geomStep endU endV s.1 e b
  · rw [if_pos ho, if_pos ho]
  · rw [if_neg ho, if_neg ho]; rfl







omit [Fintype E] [DecidableEq E] in


theorem fst_runState_xbStep (endU endV : E → V) (o : V) (ω : ConfigSpace E)
    (l : List E) (s : XState V) :
    (runState (xbGuard endU endV) (xbStep endU endV o) ω l s).1
      = runState (geomGuard endU endV) (geomStep endU endV) ω l s.1 := by
  induction l generalizing s with
  | nil => rfl
  | cons e rest ih =>
      simp only [runState]
      have hguard : xbGuard endU endV s e = geomGuard endU endV s.1 e := rfl
      rw [hguard]
      by_cases hg : geomGuard endU endV s.1 e = true
      · rw [if_pos hg, if_pos hg, ih, fst_xbStep]
      · rw [if_neg hg, if_neg hg, ih]



omit [Fintype E] [DecidableEq E] in

theorem subset_snd_xbStep (endU endV : E → V) (o : V) (s : XState V) (e : E) (b : Bool) :
    s.2 ⊆ (xbStep endU endV o s e b).2 := by
  rw [snd_xbStep_eq]
  by_cases ho : o ∈ geomStep endU endV s.1 e b
  · rw [if_pos ho]
    refine subset_trans ?_ (Finset.subset_insert _ _)
    by_cases hc : b = true ∧ (endU e ∈ s.2 ∨ endV e ∈ s.2)
    · rw [if_pos hc]; exact subset_trans (Finset.subset_insert _ _) (Finset.subset_insert _ _)
    · rw [if_neg hc]
  · rw [if_neg ho]; simp only [id]
    by_cases hc : b = true ∧ (endU e ∈ s.2 ∨ endV e ∈ s.2)
    · rw [if_pos hc]; exact subset_trans (Finset.subset_insert _ _) (Finset.subset_insert _ _)
    · rw [if_neg hc]

omit [Fintype E] [DecidableEq E] in

theorem subset_snd_runState (endU endV : E → V) (o : V) (ω : ConfigSpace E)
    (l : List E) (s : XState V) :
    s.2 ⊆ (runState (xbGuard endU endV) (xbStep endU endV o) ω l s).2 := by
  induction l generalizing s with
  | nil => simp [runState]
  | cons e rest ih =>
      simp only [runState]
      by_cases hg : xbGuard endU endV s e = true
      · rw [if_pos hg]; exact subset_trans (subset_snd_xbStep endU endV o s e (ω e)) (ih _)
      · rw [if_neg hg]; exact ih _

omit [Fintype E] [DecidableEq E] in

theorem snd_sub_fst_xbStep (endU endV : E → V) (o : V) (s : XState V) (e : E) (b : Bool)
    (hs : s.2 ⊆ s.1) :
    (xbStep endU endV o s e b).2 ⊆ (xbStep endU endV o s e b).1 := by
  rw [snd_xbStep_eq, fst_xbStep]
  by_cases ho : o ∈ geomStep endU endV s.1 e b
  · rw [if_pos ho]
    apply Finset.insert_subset ho
    by_cases hc : b = true ∧ (endU e ∈ s.2 ∨ endV e ∈ s.2)
    · rw [if_pos hc]; unfold geomStep; rw [if_pos hc.1]
      exact Finset.insert_subset_insert _ (Finset.insert_subset_insert _ hs)
    · rw [if_neg hc]; exact subset_trans hs (subset_geomStep endU endV s.1 e b)
  · rw [if_neg ho]; simp only [id]
    by_cases hc : b = true ∧ (endU e ∈ s.2 ∨ endV e ∈ s.2)
    · rw [if_pos hc]; unfold geomStep; rw [if_pos hc.1]
      exact Finset.insert_subset_insert _ (Finset.insert_subset_insert _ hs)
    · rw [if_neg hc]; exact subset_trans hs (subset_geomStep endU endV s.1 e b)

omit [Fintype E] [DecidableEq E] in

theorem snd_sub_fst_runState (endU endV : E → V) (o : V) (ω : ConfigSpace E)
    (l : List E) (s : XState V) (hs : s.2 ⊆ s.1) :
    (runState (xbGuard endU endV) (xbStep endU endV o) ω l s).2
      ⊆ (runState (xbGuard endU endV) (xbStep endU endV o) ω l s).1 := by
  induction l generalizing s with
  | nil => simpa [runState] using hs
  | cons e rest ih =>
      simp only [runState]
      by_cases hg : xbGuard endU endV s e = true
      · rw [if_pos hg]; exact ih _ (snd_sub_fst_xbStep endU endV o s e (ω e) hs)
      · rw [if_neg hg]; exact ih s hs



def reach0Inv (endU endV : E → V) (ω : ConfigSpace E) (o : V) (s : XState V) : Prop :=
  ∀ x ∈ s.2, ReachOpen endU endV ω x o

omit [Fintype E] [DecidableEq E] in

theorem reach0Inv_xbStep (endU endV : E → V) (ω : ConfigSpace E) (o : V) (s : XState V) (e : E)
    (hInv : reach0Inv endU endV ω o s) :
    reach0Inv endU endV ω o (xbStep endU endV o s e (ω e)) := by
  intro x hx
  rw [snd_xbStep_eq] at hx
  by_cases ho : o ∈ geomStep endU endV s.1 e (ω e)
  · rw [if_pos ho] at hx
    rw [Finset.mem_insert] at hx
    rcases hx with rfl | hx
    · exact ReachOpen.refl x
    · by_cases hc : (ω e) = true ∧ (endU e ∈ s.2 ∨ endV e ∈ s.2)
      · rw [if_pos hc] at hx
        rw [Finset.mem_insert, Finset.mem_insert] at hx
        obtain ⟨hopen, hend⟩ := hc
        rcases hx with rfl | rfl | hx
        · rcases hend with hU | hV
          · exact hInv _ hU
          · exact ReachOpen.step e hopen (Or.inl ⟨rfl, rfl⟩) (hInv _ hV)
        · rcases hend with hU | hV
          · exact ReachOpen.step e hopen (Or.inr ⟨rfl, rfl⟩) (hInv _ hU)
          · exact hInv _ hV
        · exact hInv _ hx
      · rw [if_neg hc] at hx; exact hInv _ hx
  · rw [if_neg ho] at hx; simp only [id] at hx
    by_cases hc : (ω e) = true ∧ (endU e ∈ s.2 ∨ endV e ∈ s.2)
    · rw [if_pos hc] at hx
      rw [Finset.mem_insert, Finset.mem_insert] at hx
      obtain ⟨hopen, hend⟩ := hc
      rcases hx with rfl | rfl | hx
      · rcases hend with hU | hV
        · exact hInv _ hU
        · exact ReachOpen.step e hopen (Or.inl ⟨rfl, rfl⟩) (hInv _ hV)
      · rcases hend with hU | hV
        · exact ReachOpen.step e hopen (Or.inr ⟨rfl, rfl⟩) (hInv _ hU)
        · exact hInv _ hV
      · exact hInv _ hx
    · rw [if_neg hc] at hx; exact hInv _ hx

omit [Fintype E] [DecidableEq E] in

theorem reach0Inv_runState (endU endV : E → V) (ω : ConfigSpace E) (o : V)
    (l : List E) (s : XState V) (hInv : reach0Inv endU endV ω o s) :
    reach0Inv endU endV ω o (runState (xbGuard endU endV) (xbStep endU endV o) ω l s) := by
  induction l generalizing s with
  | nil => simpa [runState] using hInv
  | cons e rest ih =>
      simp only [runState]
      by_cases hg : xbGuard endU endV s e = true
      · rw [if_pos hg]; exact ih _ (reach0Inv_xbStep endU endV ω o s e hInv)
      · rw [if_neg hg]; exact ih s hInv



def oSeedInv (o : V) (s : XState V) : Prop := o ∈ s.1 → o ∈ s.2

omit [Fintype E] [DecidableEq E] in

theorem oSeedInv_xbStep (endU endV : E → V) (o : V) (s : XState V) (e : E) (b : Bool) :
    oSeedInv o (xbStep endU endV o s e b) := by
  intro ho
  rw [snd_xbStep_eq]
  rw [fst_xbStep] at ho
  rw [if_pos ho]
  exact Finset.mem_insert_self _ _

omit [Fintype E] [DecidableEq E] in

theorem oSeedInv_runState (endU endV : E → V) (o : V) (ω : ConfigSpace E)
    (l : List E) (s : XState V) (hs : oSeedInv o s) :
    oSeedInv o (runState (xbGuard endU endV) (xbStep endU endV o) ω l s) := by
  induction l generalizing s with
  | nil => simpa [runState] using hs
  | cons e rest ih =>
      simp only [runState]
      by_cases hg : xbGuard endU endV s e = true
      · rw [if_pos hg]; exact ih _ (oSeedInv_xbStep endU endV o s e (ω e))
      · rw [if_neg hg]; exact ih s hs








omit [Fintype E] [DecidableEq E] in



theorem mem_snd_runState_of_open_edge (endU endV : E → V) (o : V) (ω : ConfigSpace E)
    (l : List E) (s : XState V) (hs : s.2 ⊆ s.1) (e : E) (he : e ∈ l) (hopen : ω e = true)
    (hend : endU e ∈ s.2 ∨ endV e ∈ s.2) :
    endU e ∈ (runState (xbGuard endU endV) (xbStep endU endV o) ω l s).2
      ∧ endV e ∈ (runState (xbGuard endU endV) (xbStep endU endV o) ω l s).2 := by
  induction l generalizing s with
  | nil => simp at he
  | cons f rest ih =>
      simp only [runState]
      rcases List.mem_cons.mp he with rfl | hmem
      · have hg : xbGuard endU endV s e = true := by
          unfold xbGuard; simp only [decide_eq_true_eq]
          rcases hend with hU | hV
          · exact Or.inl (hs hU)
          · exact Or.inr (hs hV)
        rw [if_pos hg]
        have hboth : endU e ∈ (xbStep endU endV o s e (ω e)).2
            ∧ endV e ∈ (xbStep endU endV o s e (ω e)).2 := by
          rw [snd_xbStep_eq]
          have hc : (ω e) = true ∧ (endU e ∈ s.2 ∨ endV e ∈ s.2) := ⟨hopen, hend⟩
          by_cases ho : o ∈ geomStep endU endV s.1 e (ω e)
          · rw [if_pos ho, if_pos hc]
            exact ⟨Finset.mem_insert_of_mem (Finset.mem_insert_self _ _),
                   Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))⟩
          · rw [if_neg ho]; simp only [id]; rw [if_pos hc]
            exact ⟨Finset.mem_insert_self _ _,
                   Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)⟩
        have hsub := subset_snd_runState endU endV o ω rest (xbStep endU endV o s e (ω e))
        exact ⟨hsub hboth.1, hsub hboth.2⟩
      · by_cases hg : xbGuard endU endV s f = true
        · rw [if_pos hg]
          refine ih (xbStep endU endV o s f (ω f))
            (snd_sub_fst_xbStep endU endV o s f (ω f) hs) hmem ?_
          have hsub := subset_snd_xbStep endU endV o s f (ω f)
          rcases hend with hU | hV
          · exact Or.inl (hsub hU)
          · exact Or.inr (hsub hV)
        · rw [if_neg hg]; exact ih s hs hmem hend

omit [Fintype E] [DecidableEq E] in


theorem snd_saturated_of_fixpoint (endU endV : E → V) (o : V) (ω : ConfigSpace E)
    (l : List E) (s : XState V) (hs : s.2 ⊆ s.1)
    (hfix : runState (xbGuard endU endV) (xbStep endU endV o) ω l s = s) :
    Saturated endU endV ω l s.2 := by
  intro e he hopen hend
  have h := mem_snd_runState_of_open_edge endU endV o ω l s hs e he hopen hend
  rw [hfix] at h
  exact h







omit [Fintype E] [DecidableEq E] [DecidableEq V] in





theorem pairFixpoint_iterate {W : Type*} [DecidableEq W]
    (f : (Finset W × Finset W) → (Finset W × Finset W)) (U : Finset W)
    (hinfl1 : ∀ s, s.1 ⊆ (f s).1) (hinfl2 : ∀ s, s.2 ⊆ (f s).2)
    (hb1 : ∀ s, s.1 ⊆ U → s.2 ⊆ U → (f s).1 ⊆ U)
    (hb2 : ∀ s, s.1 ⊆ U → s.2 ⊆ U → (f s).2 ⊆ U)
    (s₀ : Finset W × Finset W) (h01 : s₀.1 ⊆ U) (h02 : s₀.2 ⊆ U) :
    f (f^[2 * U.card] s₀) = f^[2 * U.card] s₀ := by
  set m : (Finset W × Finset W) → ℕ := fun s => s.1.card + s.2.card with hm
  have hbound : ∀ n, (f^[n] s₀).1 ⊆ U ∧ (f^[n] s₀).2 ⊆ U := by
    intro n; induction n with
    | zero => simpa using ⟨h01, h02⟩
    | succ k ih =>
        rw [Function.iterate_succ', Function.comp_apply]
        exact ⟨hb1 _ ih.1 ih.2, hb2 _ ih.1 ih.2⟩
  have hmle : ∀ n, m (f^[n] s₀) ≤ 2 * U.card := by
    intro n; have h := hbound n
    have h1 := Finset.card_le_card h.1
    have h2 := Finset.card_le_card h.2
    simp only [hm]; omega
  have hminfl : ∀ s, m s ≤ m (f s) := by
    intro s
    have h1 := Finset.card_le_card (hinfl1 s)
    have h2 := Finset.card_le_card (hinfl2 s)
    simp only [hm]; omega
  have hfix_of_m : ∀ s, m (f s) ≤ m s → f s = s := by
    intro s hle
    have h1 := hinfl1 s
    have h2 := hinfl2 s
    have hc1 := Finset.card_le_card h1
    have hc2 := Finset.card_le_card h2
    have hcards : (f s).1.card = s.1.card ∧ (f s).2.card = s.2.card := by
      simp only [hm] at hle; omega
    have e1 : (f s).1 = s.1 := (Finset.eq_of_subset_of_card_le h1 (le_of_eq hcards.1)).symm
    have e2 : (f s).2 = s.2 := (Finset.eq_of_subset_of_card_le h2 (le_of_eq hcards.2)).symm
    exact Prod.ext e1 e2
  have habsorb : ∀ k j, f (f^[k] s₀) = f^[k] s₀ → f^[k + j] s₀ = f^[k] s₀ := by
    intro k j hk; induction j with
    | zero => rfl
    | succ i ih =>
        have hstep : f^[k + (i + 1)] s₀ = f (f^[k + i] s₀) := by
          rw [show k + (i + 1) = (k + i) + 1 from by ring, Function.iterate_succ',
            Function.comp_apply]
        rw [hstep, ih, hk]
  by_contra hcon
  have hnofix : ∀ k, k ≤ 2 * U.card → f (f^[k] s₀) ≠ f^[k] s₀ := by
    intro k hk hfk; apply hcon
    obtain ⟨j, hj⟩ := Nat.exists_eq_add_of_le hk
    rw [hj, habsorb k j hfk, hfk]
  have hstrict : ∀ k, k < 2 * U.card → m (f^[k] s₀) < m (f^[k + 1] s₀) := by
    intro k hk
    have hne := hnofix k (le_of_lt hk)
    have heq : f^[k + 1] s₀ = f (f^[k] s₀) := by rw [Function.iterate_succ', Function.comp_apply]
    rw [heq]
    rcases lt_or_eq_of_le (hminfl (f^[k] s₀)) with h | h
    · exact h
    · exact absurd (hfix_of_m _ (le_of_eq h.symm)) hne
  have hge : ∀ k, k ≤ 2 * U.card → k ≤ m (f^[k] s₀) := by
    intro k hk; induction k with
    | zero => exact Nat.zero_le _
    | succ j ih =>
        exact Nat.lt_of_le_of_lt (ih (le_of_lt (Nat.lt_of_succ_le hk)))
          (hstrict j (Nat.lt_of_succ_le hk))
  have hne := hnofix (2 * U.card) le_rfl
  have heq : f^[2 * U.card + 1] s₀ = f (f^[2 * U.card] s₀) := by
    rw [Function.iterate_succ', Function.comp_apply]
  have hstr : m (f^[2 * U.card] s₀) < m (f^[2 * U.card + 1] s₀) := by
    rw [heq]
    rcases lt_or_eq_of_le (hminfl (f^[2 * U.card] s₀)) with h | h
    · exact h
    · exact absurd (hfix_of_m _ (le_of_eq h.symm)) hne
  have h1 : 2 * U.card ≤ m (f^[2 * U.card] s₀) := hge _ le_rfl
  have hle : m (f^[2 * U.card + 1] s₀) ≤ 2 * U.card := hmle _
  omega










def xbPass (endU endV : E → V) (o : V) (ω : ConfigSpace E) (l : List E) :
    XState V → XState V :=
  fun s => runState (xbGuard endU endV) (xbStep endU endV o) ω l s

omit [Fintype E] [DecidableEq E] in

theorem runState_append_xb (endU endV : E → V) (o : V) (ω : ConfigSpace E)
    (l₁ l₂ : List E) (s : XState V) :
    runState (xbGuard endU endV) (xbStep endU endV o) ω (l₁ ++ l₂) s
      = runState (xbGuard endU endV) (xbStep endU endV o) ω l₂
          (runState (xbGuard endU endV) (xbStep endU endV o) ω l₁ s) := by
  induction l₁ generalizing s with
  | nil => simp [runState]
  | cons e rest ih =>
      simp only [List.cons_append, runState]
      by_cases hg : xbGuard endU endV s e = true
      · rw [if_pos hg, if_pos hg]; exact ih _
      · rw [if_neg hg, if_neg hg]; exact ih _

omit [Fintype E] [DecidableEq E] in

theorem runState_repeatList_xb (endU endV : E → V) (o : V) (ω : ConfigSpace E)
    (l : List E) (n : ℕ) (s : XState V) :
    runState (xbGuard endU endV) (xbStep endU endV o) ω (repeatList l n) s
      = (xbPass endU endV o ω l)^[n] s := by
  induction n generalizing s with
  | zero => simp [repeatList, runState]
  | succ k ih =>
      rw [repeatList, runState_append_xb, Function.iterate_succ, Function.comp_apply]
      exact ih _

omit [Fintype E] in

theorem snd_runState_subset (endU endV : E → V) (o : V) (ω : ConfigSpace E)
    (l : List E) (s : XState V) :
    (runState (xbGuard endU endV) (xbStep endU endV o) ω l s).2
      ⊆ s.2 ∪ endpointsFinset endU endV l ∪ {o} := by
  induction l generalizing s with
  | nil => intro x hx; simp only [runState] at hx; exact Finset.mem_union_left _ (Finset.mem_union_left _ hx)
  | cons e rest ih =>
      simp only [runState]
      by_cases hg : xbGuard endU endV s e = true
      · rw [if_pos hg]
        refine subset_trans (ih (xbStep endU endV o s e (ω e))) ?_
        intro x hx
        
        rw [Finset.mem_union, Finset.mem_union] at hx
        rcases hx with (hstep | hrest) | hocase
        · 
          rw [snd_xbStep_eq] at hstep
          by_cases ho : o ∈ geomStep endU endV s.1 e (ω e)
          · rw [if_pos ho] at hstep
            rw [Finset.mem_insert] at hstep
            rcases hstep with rfl | hstep
            · exact Finset.mem_union_right _ (Finset.mem_singleton_self _)
            · 
              by_cases hc : (ω e) = true ∧ (endU e ∈ s.2 ∨ endV e ∈ s.2)
              · rw [if_pos hc] at hstep
                rw [Finset.mem_insert, Finset.mem_insert] at hstep
                rcases hstep with rfl | rfl | hd
                · refine Finset.mem_union_left _ (Finset.mem_union_right _ ?_)
                  unfold endpointsFinset
                  exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨e, by simp [List.mem_toFinset], rfl⟩)
                · refine Finset.mem_union_left _ (Finset.mem_union_right _ ?_)
                  unfold endpointsFinset
                  exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨e, by simp [List.mem_toFinset], rfl⟩)
                · exact Finset.mem_union_left _ (Finset.mem_union_left _ hd)
              · rw [if_neg hc] at hstep
                exact Finset.mem_union_left _ (Finset.mem_union_left _ hstep)
          · rw [if_neg ho] at hstep; simp only [id] at hstep
            by_cases hc : (ω e) = true ∧ (endU e ∈ s.2 ∨ endV e ∈ s.2)
            · rw [if_pos hc] at hstep
              rw [Finset.mem_insert, Finset.mem_insert] at hstep
              rcases hstep with rfl | rfl | hd
              · refine Finset.mem_union_left _ (Finset.mem_union_right _ ?_)
                unfold endpointsFinset
                exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨e, by simp [List.mem_toFinset], rfl⟩)
              · refine Finset.mem_union_left _ (Finset.mem_union_right _ ?_)
                unfold endpointsFinset
                exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨e, by simp [List.mem_toFinset], rfl⟩)
              · exact Finset.mem_union_left _ (Finset.mem_union_left _ hd)
            · rw [if_neg hc] at hstep
              exact Finset.mem_union_left _ (Finset.mem_union_left _ hstep)
        · 
          refine Finset.mem_union_left _ (Finset.mem_union_right _ ?_)
          unfold endpointsFinset at hrest ⊢
          rw [Finset.mem_union] at hrest ⊢
          rcases hrest with hu | hv
          · exact Or.inl (by rw [Finset.mem_image] at hu ⊢; obtain ⟨a, ha, rfl⟩ := hu
                             exact ⟨a, by simp only [List.mem_toFinset, List.mem_cons]; exact Or.inr (List.mem_toFinset.mp ha), rfl⟩)
          · exact Or.inr (by rw [Finset.mem_image] at hv ⊢; obtain ⟨a, ha, rfl⟩ := hv
                             exact ⟨a, by simp only [List.mem_toFinset, List.mem_cons]; exact Or.inr (List.mem_toFinset.mp ha), rfl⟩)
        · exact Finset.mem_union_right _ hocase
      · rw [if_neg hg]
        refine subset_trans (ih s) ?_
        intro x hx
        rw [Finset.mem_union, Finset.mem_union] at hx
        rcases hx with (hd | hrest) | hocase
        · exact Finset.mem_union_left _ (Finset.mem_union_left _ hd)
        · refine Finset.mem_union_left _ (Finset.mem_union_right _ ?_)
          unfold endpointsFinset at hrest ⊢
          rw [Finset.mem_union] at hrest ⊢
          rcases hrest with hu | hv
          · exact Or.inl (by rw [Finset.mem_image] at hu ⊢; obtain ⟨a, ha, rfl⟩ := hu
                             exact ⟨a, by simp only [List.mem_toFinset, List.mem_cons]; exact Or.inr (List.mem_toFinset.mp ha), rfl⟩)
          · exact Or.inr (by rw [Finset.mem_image] at hv ⊢; obtain ⟨a, ha, rfl⟩ := hv
                             exact ⟨a, by simp only [List.mem_toFinset, List.mem_cons]; exact Or.inr (List.mem_toFinset.mp ha), rfl⟩)
        · exact Finset.mem_union_right _ hocase


def xbUniverse (endU endV : E → V) (o : V) (l : List E) (disc₀ : Finset V) : Finset V :=
  disc₀ ∪ endpointsFinset endU endV l ∪ {o}

omit [Fintype E] in



theorem xbPass_fixpoint (endU endV : E → V) (o : V) (ω : ConfigSpace E)
    (l : List E) (disc₀ : Finset V) :
    xbPass endU endV o ω l
        ((xbPass endU endV o ω l)^[2 * (xbUniverse endU endV o l disc₀).card] (disc₀, ∅))
      = (xbPass endU endV o ω l)^[2 * (xbUniverse endU endV o l disc₀).card] (disc₀, ∅) := by
  set U := xbUniverse endU endV o l disc₀ with hU
  have hinfl1 : ∀ s : XState V, s.1 ⊆ (xbPass endU endV o ω l s).1 := by
    intro s; rw [xbPass, fst_runState_xbStep]; exact subset_runState endU endV ω l s.1
  have hinfl2 : ∀ s : XState V, s.2 ⊆ (xbPass endU endV o ω l s).2 := by
    intro s; exact subset_snd_runState endU endV o ω l s
  have hb1 : ∀ s : XState V, s.1 ⊆ U → s.2 ⊆ U → (xbPass endU endV o ω l s).1 ⊆ U := by
    intro s hs1 _
    rw [xbPass, fst_runState_xbStep]
    refine subset_trans (runState_subset_union endU endV ω l s.1) ?_
    rw [hU, xbUniverse]
    intro x hx; rw [Finset.mem_union] at hx
    rcases hx with hd | hep
    · exact hs1 hd
    · exact Finset.mem_union_left _ (Finset.mem_union_right _ hep)
  have hb2 : ∀ s : XState V, s.1 ⊆ U → s.2 ⊆ U → (xbPass endU endV o ω l s).2 ⊆ U := by
    intro s _ hs2
    rw [xbPass]
    refine subset_trans (snd_runState_subset endU endV o ω l s) ?_
    rw [hU, xbUniverse]
    intro x hx
    rw [Finset.mem_union, Finset.mem_union] at hx
    rcases hx with (hd | hep) | ho
    · exact hs2 hd
    · exact Finset.mem_union_left _ (Finset.mem_union_right _ hep)
    · exact Finset.mem_union_right _ ho
  have h01 : ((disc₀, ∅) : XState V).1 ⊆ U := by
    rw [hU, xbUniverse]; exact subset_trans Finset.subset_union_left Finset.subset_union_left
  have h02 : ((disc₀, ∅) : XState V).2 ⊆ U := by simp
  exact pairFixpoint_iterate (xbPass endU endV o ω l) U hinfl1 hinfl2 hb1 hb2 (disc₀, ∅) h01 h02




def xbCount (endU endV : E → V) (o : V) (l : List E) (disc₀ : Finset V) : ℕ :=
  2 * (xbUniverse endU endV o l disc₀).card






noncomputable def crossTree (endU endV : E → V) (o : V) (C : Set V)
    (l : List E) (disc₀ : Finset V) : DecisionTree E :=
  buildTree (xbGuard endU endV) (xbStep endU endV o)
    (fun s => decide (∃ y ∈ s.2, y ∈ C))
    (repeatList l (xbCount endU endV o l disc₀)) (disc₀, ∅)

omit [Fintype E] in

theorem eval_crossTree (endU endV : E → V) (o : V) (C : Set V)
    (l : List E) (disc₀ : Finset V) (ω : ConfigSpace E) :
    (crossTree endU endV o C l disc₀).eval ω
      = decide (∃ y ∈ ((xbPass endU endV o ω l)^[xbCount endU endV o l disc₀]
          (disc₀, ∅)).2, y ∈ C) := by
  unfold crossTree
  rw [eval_buildTree]
  congr 1
  rw [xbCount]
  exact (runState_repeatList_xb endU endV o ω l _ (disc₀, ∅)).symm ▸ rfl









omit [Fintype E] in







theorem eval_crossTree_iff (endU endV : E → V) (o : V) (B C : Set V)
    (l : List E) (hl : ∀ e, e ∈ l) (disc₀ : Finset V)
    (hBdisc : ∀ b ∈ B, b ∈ disc₀) (hoB : o ∉ disc₀)
    (hcross : ∀ ω, ConnOpenSet endU endV ω o C → ConnOpenSet endU endV ω o B)
    (ω : ConfigSpace E) :
    (crossTree endU endV o C l disc₀).eval ω = true ↔ ConnOpenSet endU endV ω o C := by
  rw [eval_crossTree, decide_eq_true_eq]
  set N := xbCount endU endV o l disc₀ with hN
  set s := (xbPass endU endV o ω l)^[N] (disc₀, ∅) with hs
  have hfix : xbPass endU endV o ω l s = s := xbPass_fixpoint endU endV o ω l disc₀
  have hrun : runState (xbGuard endU endV) (xbStep endU endV o) ω (repeatList l N) (disc₀, ∅) = s := by
    rw [runState_repeatList_xb]
  have hfix1 : runState (geomGuard endU endV) (geomStep endU endV) ω l s.1 = s.1 := by
    have hc := congrArg Prod.fst hfix
    rwa [xbPass, fst_runState_xbStep] at hc
  have hsub : s.2 ⊆ s.1 := by
    rw [← hrun]; exact snd_sub_fst_runState endU endV o ω (repeatList l N) (disc₀, ∅) (by simp)
  constructor
  · rintro ⟨y, hyD0, hyC⟩
    have hr0 : reach0Inv endU endV ω o s := by
      rw [← hrun]
      exact reach0Inv_runState endU endV ω o (repeatList l N) (disc₀, ∅) (by intro x hx; simp at hx)
    exact ⟨y, hyC, reachOpen_symm (hr0 y hyD0)⟩
  · intro hoC
    obtain ⟨b, hbC, hreach⟩ := hoC
    have hoB' : ConnOpenSet endU endV ω o B := hcross ω ⟨b, hbC, hreach⟩
    have hsat1 : Saturated endU endV ω l s.1 := saturated_of_fixpoint endU endV ω l s.1 hfix1
    have hdisc_sub : disc₀ ⊆ s.1 := by
      rw [← hrun, fst_runState_xbStep]
      exact subset_runState endU endV ω (repeatList l N) disc₀
    obtain ⟨bB, hbBB, hreachB⟩ := hoB'
    have hoD : o ∈ s.1 :=
      mem_of_reachOpen_of_saturated endU endV ω l s.1 hsat1 hl hreachB
        (hdisc_sub (hBdisc bB hbBB))
    have hseed : oSeedInv o s := by
      rw [← hrun]
      exact oSeedInv_runState endU endV o ω (repeatList l N) (disc₀, ∅)
        (by intro h; exact absurd (by simpa using h) hoB)
    have hoD0 : o ∈ s.2 := hseed hoD
    have hsat2 : Saturated endU endV ω l s.2 :=
      snd_saturated_of_fixpoint endU endV o ω l s hsub hfix
    have hbD0 : b ∈ s.2 :=
      mem_of_reachOpen_of_saturated endU endV ω l s.2 hsat2 hl (reachOpen_symm hreach) hoD0
    exact ⟨b, hbD0, hbC⟩

omit [Fintype E] in







theorem evalR_crossTree (endU endV : E → V) (o : V) (B C : Set V)
    (l : List E) (hl : ∀ e, e ∈ l) (disc₀ : Finset V)
    (hBdisc : ∀ b ∈ B, b ∈ disc₀) (hoB : o ∉ disc₀)
    (hcross : ∀ ω, ConnOpenSet endU endV ω o C → ConnOpenSet endU endV ω o B)
    (ω : ConfigSpace E) [Decidable (ConnOpenSet endU endV ω o C)] :
    (crossTree endU endV o C l disc₀).evalR ω
      = if ConnOpenSet endU endV ω o C then (1 : ℝ) else 0 := by
  unfold DecisionTree.evalR
  by_cases hconn : ConnOpenSet endU endV ω o C
  · rw [if_pos ((eval_crossTree_iff endU endV o B C l hl disc₀ hBdisc hoB hcross ω).mpr hconn),
      if_pos hconn]
  · have heval : (crossTree endU endV o C l disc₀).eval ω ≠ true :=
      fun h => hconn ((eval_crossTree_iff endU endV o B C l hl disc₀ hBdisc hoB hcross ω).mp h)
    rw [if_neg heval, if_neg hconn]








omit [Fintype E] in



theorem queried_crossTree_imp (endU endV : E → V) (o : V) (B C : Set V)
    (l : List E) (disc₀ : Finset V) (hdisc₀ : ∀ x ∈ disc₀, x ∈ B) (ω : ConfigSpace E) (i : E)
    (hi : i ∈ (crossTree endU endV o C l disc₀).queried ω) :
    ConnOpenSet endU endV ω (endU i) B ∨ ConnOpenSet endU endV ω (endV i) B := by
  
  have hInv0 : geomInv endU endV ω B (disc₀, (∅ : Finset V)).1 :=
    fun x hx => connOpenSet_of_mem (hdisc₀ x hx)
  obtain ⟨τ, hτInv, hτg⟩ := mem_queried_buildTree (guard := xbGuard endU endV)
    (step := xbStep endU endV o)
    (base := fun s => decide (∃ y ∈ s.2, y ∈ C))
    (Inv := fun s => geomInv endU endV ω B s.1) (ω := ω)
    (fun σ e hσ hg => by
      
      have hg1 : geomGuard endU endV σ.1 e = true := hg
      have := geomInv_step endU endV ω B σ.1 e hσ hg1
      rwa [← fst_xbStep endU endV o σ e (ω e)] at this)
    (repeatList l (xbCount endU endV o l disc₀)) (disc₀, ∅) hInv0 i hi
  have hτg' : geomGuard endU endV τ.1 i = true := hτg
  unfold geomGuard at hτg'; simp only [decide_eq_true_eq] at hτg'
  rcases hτg' with hU | hV
  · exact Or.inl (hτInv _ hU)
  · exact Or.inr (hτInv _ hV)







theorem reveal_crossTree_le {ν : E → Bool → ℝ} (hν : IsProbWeight ν)
    (endU endV : E → V) (o : V) (B C : Set V) (l : List E) (disc₀ : Finset V)
    (hdisc₀ : ∀ x ∈ disc₀, x ∈ B) (i : E) :
    reveal ν (crossTree endU endV o C l disc₀) i
      ≤ expect ν (fun ω => if ConnOpenSet endU endV ω (endU i) B then (1 : ℝ) else 0)
        + expect ν (fun ω => if ConnOpenSet endU endV ω (endV i) B then (1 : ℝ) else 0) := by
  have h := revealment_le_of_queried_imp_or hν (crossTree endU endV o C l disc₀) i
    (fun ω => ConnOpenSet endU endV ω (endU i) B)
    (fun ω => ConnOpenSet endU endV ω (endV i) B)
    (fun ω hq => queried_crossTree_imp endU endV o B C l disc₀ hdisc₀ ω i hq)
  rwa [Revealment.revealment] at h











section Lattice

variable {d : ℕ}














theorem evalR_crossTree_connected
    {edge : E → Sym2 (Site d)} (hinj : Function.Injective edge)
    {endU endV : E → Site d} (hcoh : ∀ e, edge e = s(endU e, endV e))
    (hadj : ∀ e, (hypercubicLattice d).Adj (endU e) (endV e))
    (k n : ℕ) (hk : 1 ≤ k) (hkn : k ≤ n)
    (o : Site d) (ho : o ∈ box d (k - 1))
    (l : List E) (hl : ∀ e, e ∈ l) (disc₀ : Finset (Site d))
    (hBdisc : ∀ b ∈ vertexBoundary d k, b ∈ disc₀) (hoB : o ∉ disc₀)
    (ω : ConfigSpace E)
    [Decidable (ConnectedToSet d (liftCfg edge ω) o (vertexBoundary d n))] :
    (crossTree endU endV o (vertexBoundary d n) l disc₀).evalR ω
      = if ConnectedToSet d (liftCfg edge ω) o (vertexBoundary d n) then (1 : ℝ) else 0 := by
  have hcross : ∀ ω', ConnOpenSet endU endV ω' o (vertexBoundary d n)
      → ConnOpenSet endU endV ω' o (vertexBoundary d k) :=
    fun ω' h => connOpenSet_boundary_mono hk hkn hadj ho h
  unfold DecisionTree.evalR
  by_cases hconn : ConnectedToSet d (liftCfg edge ω) o (vertexBoundary d n)
  · have hopenconn : ConnOpenSet endU endV ω o (vertexBoundary d n) :=
      connectedToSet_imp_connOpenSet hcoh hconn
    rw [if_pos ((eval_crossTree_iff endU endV o (vertexBoundary d k) (vertexBoundary d n)
        l hl disc₀ hBdisc hoB hcross ω).mpr hopenconn), if_pos hconn]
  · have heval : (crossTree endU endV o (vertexBoundary d n) l disc₀).eval ω ≠ true := by
      intro h
      have hopenconn := (eval_crossTree_iff endU endV o (vertexBoundary d k) (vertexBoundary d n)
        l hl disc₀ hBdisc hoB hcross ω).mp h
      exact hconn (connOpenSet_imp_connectedToSet hinj hcoh hadj hopenconn)
    rw [if_neg heval, if_neg hconn]












theorem reveal_crossTree_le_connected {ν : E → Bool → ℝ} (hν : IsProbWeight ν)
    {edge : E → Sym2 (Site d)} (hinj : Function.Injective edge)
    {endU endV : E → Site d} (hcoh : ∀ e, edge e = s(endU e, endV e))
    (hadj : ∀ e, (hypercubicLattice d).Adj (endU e) (endV e))
    (o : Site d) (C : Set (Site d)) (k : ℕ) (l : List E) (disc₀ : Finset (Site d))
    (hdisc₀ : ∀ x ∈ disc₀, x ∈ vertexBoundary d k) (i : E) :
    reveal ν (crossTree endU endV o C l disc₀) i
      ≤ expect ν (fun ω => if ConnectedToSet d (liftCfg edge ω) (endU i) (vertexBoundary d k) then (1 : ℝ) else 0)
        + expect ν (fun ω => if ConnectedToSet d (liftCfg edge ω) (endV i) (vertexBoundary d k) then (1 : ℝ) else 0) := by
  refine le_trans
    (reveal_crossTree_le hν endU endV o (vertexBoundary d k) C l disc₀ hdisc₀ i) ?_
  apply add_le_add
  · exact expect_indicator_mono hν _ _
      (fun ω hP => connOpenSet_imp_connectedToSet hinj hcoh hadj hP)
  · exact expect_indicator_mono hν _ _
      (fun ω hP => connOpenSet_imp_connectedToSet hinj hcoh hadj hP)

end Lattice

end OSSS
end StatMech

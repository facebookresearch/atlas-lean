/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/










































import Mathlib
import Code.Lattice.HypercubicLattice
import Code.Lattice.JordanZ2
import Code.Lattice.JordanEnclosure
import Code.Lattice.CrossingParity
import Code.Lattice.WhitneyBridge
import Code.Lattice.WhitneyCorrect
import Code.Lattice.WindingColoring

open SimpleGraph Set

namespace StatMech

namespace Lattice










def jce_nbr (v : Site 2) : Fin 4 → Site 2
  | 0 => ![v 0 + 1, v 1]
  | 1 => ![v 0 - 1, v 1]
  | 2 => ![v 0, v 1 + 1]
  | 3 => ![v 0, v 1 - 1]



noncomputable def jce_degree (E : Set (Sym2 (Site 2))) (v : Site 2) : ℕ := by
  classical
  exact (Finset.univ.filter (fun i : Fin 4 => s(v, jce_nbr v i) ∈ E)).card



def jce_ClosedContour (E : Set (Sym2 (Site 2))) : Prop :=
  ∀ v : Site 2, Even (jce_degree E v)











def jce_horizBelow (a b : ℤ) : Sym2 (Site 2) → Prop := by
  classical
  refine Sym2.lift ⟨fun x y =>
    (x 1 = y 1) ∧ (x 1 ≤ b) ∧ ((x 0 = a ∧ y 0 = a + 1) ∨ (x 0 = a + 1 ∧ y 0 = a)), ?_⟩
  intro x y; simp only [eq_iff_iff]
  constructor <;> (rintro ⟨h1, h2, h3⟩; exact ⟨h1.symm, h1 ▸ h2, by tauto⟩)

@[simp] theorem jce_horizBelow_mk (a b : ℤ) (x y : Site 2) :
    jce_horizBelow a b s(x, y) ↔
      (x 1 = y 1) ∧ (x 1 ≤ b) ∧ ((x 0 = a ∧ y 0 = a + 1) ∨ (x 0 = a + 1 ∧ y 0 = a)) :=
  Iff.rfl

open Classical in



noncomputable def jce_phi (E : Finset (Sym2 (Site 2))) (f : Site 2) : Prop :=
  Odd (E.filter (fun e => jce_horizBelow (f 0) (f 1) e)).card

open Classical in
theorem jce_phi_def (E : Finset (Sym2 (Site 2))) (f : Site 2) :
    jce_phi E f ↔ Odd (E.filter (fun e => jce_horizBelow (f 0) (f 1) e)).card :=
  Iff.rfl








theorem jce_site_eq_iff (x : Site 2) (c d : ℤ) : x = ![c, d] ↔ x 0 = c ∧ x 1 = d := by
  constructor
  · rintro rfl; exact ⟨rfl, rfl⟩
  · rintro ⟨h0, h1⟩; funext i; fin_cases i <;> simp_all



theorem jce_horizBelow_succ (a b : ℤ) (e : Sym2 (Site 2)) :
    jce_horizBelow a (b + 1) e ↔
      (jce_horizBelow a b e ∨ e = s(![a, b + 1], ![a + 1, b + 1])) := by
  induction e with
  | h x y =>
    rw [jce_horizBelow_mk, jce_horizBelow_mk, Sym2.eq_iff, jce_site_eq_iff, jce_site_eq_iff,
      jce_site_eq_iff, jce_site_eq_iff]
    constructor
    · rintro ⟨h1, h2, h3⟩
      rcases lt_or_eq_of_le h2 with hlt | heq
      · exact Or.inl ⟨h1, by omega, h3⟩
      · rcases h3 with ⟨hx, hy⟩ | ⟨hx, hy⟩
        · exact Or.inr (Or.inl ⟨⟨hx, by omega⟩, ⟨hy, by omega⟩⟩)
        · exact Or.inr (Or.inr ⟨⟨hx, by omega⟩, ⟨hy, by omega⟩⟩)
    · rintro (⟨h1, h2, h3⟩ | ⟨⟨hx0, hx1⟩, hy0, hy1⟩ | ⟨⟨hx0, hx1⟩, hy0, hy1⟩)
      · exact ⟨h1, by omega, h3⟩
      · exact ⟨by omega, by omega, Or.inl ⟨hx0, hy0⟩⟩
      · exact ⟨by omega, by omega, Or.inr ⟨hx0, hy0⟩⟩


theorem jce_succEdge_not_below (a b : ℤ) :
    ¬ jce_horizBelow a b s(![a, b + 1], ![a + 1, b + 1]) := by
  rw [jce_horizBelow_mk]; simp only [Matrix.cons_val_zero, Matrix.cons_val_one]; omega

open Classical in



theorem jce_filter_succ_card (E : Finset (Sym2 (Site 2))) (a b : ℤ) :
    (E.filter (fun e => jce_horizBelow a (b + 1) e)).card =
      (E.filter (fun e => jce_horizBelow a b e)).card +
        (if s(![a, b + 1], ![a + 1, b + 1]) ∈ E then 1 else 0) := by
  classical
  set edge := s(![a, b + 1], ![a + 1, b + 1]) with hedge
  have hsub : E.filter (fun e => jce_horizBelow a b e) ⊆
      E.filter (fun e => jce_horizBelow a (b + 1) e) := by
    intro e he
    rw [Finset.mem_filter] at he ⊢
    exact ⟨he.1, (jce_horizBelow_succ a b e).mpr (Or.inl he.2)⟩
  have hdiff : (E.filter (fun e => jce_horizBelow a (b + 1) e)) \
      (E.filter (fun e => jce_horizBelow a b e)) =
      if edge ∈ E then {edge} else ∅ := by
    ext e
    rw [Finset.mem_sdiff, Finset.mem_filter, Finset.mem_filter]
    by_cases hin : edge ∈ E
    · rw [if_pos hin, Finset.mem_singleton]
      constructor
      · rintro ⟨⟨he, hb1⟩, hnb⟩
        rcases (jce_horizBelow_succ a b e).mp hb1 with hb | hb
        · exact absurd ⟨he, hb⟩ hnb
        · exact hb
      · rintro rfl
        exact ⟨⟨hin, (jce_horizBelow_succ a b edge).mpr (Or.inr rfl)⟩,
          fun h => jce_succEdge_not_below a b h.2⟩
    · rw [if_neg hin]
      simp only [Finset.notMem_empty, iff_false]
      rintro ⟨⟨he, hb1⟩, hnb⟩
      rcases (jce_horizBelow_succ a b e).mp hb1 with hb | hb
      · exact hnb ⟨he, hb⟩
      · subst hb; exact hin he
  have hcardeq := Finset.card_sdiff_add_card_eq_card hsub
  rw [hdiff] at hcardeq
  by_cases hin : edge ∈ E
  · rw [if_pos hin, Finset.card_singleton] at hcardeq
    rw [if_pos hin]; omega
  · rw [if_neg hin, Finset.card_empty] at hcardeq
    rw [if_neg hin]; omega




theorem jce_phi_topStep (E : Finset (Sym2 (Site 2))) (a b : ℤ) :
    (s(![a, b + 1], ![a + 1, b + 1]) ∈ E ↔
      (jce_phi E ![a, b] ↔ ¬ jce_phi E ![a, b + 1])) := by
  classical
  rw [jce_phi_def, jce_phi_def]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [jce_filter_succ_card E a b]
  set n := (E.filter (fun e => jce_horizBelow a b e)).card with hn
  by_cases hin : s(![a, b + 1], ![a + 1, b + 1]) ∈ E
  · rw [if_pos hin]
    simp only [hin, Nat.odd_add_one, not_not]
  · rw [if_neg hin]
    simp only [hin, false_iff, add_zero, not_iff]























def jce_HorizStepResidue : Prop :=
  ∀ (E : Finset (Sym2 (Site 2))), jce_ClosedContour (E : Set (Sym2 (Site 2))) →
    ∀ a b : ℤ, (s(![a + 1, b], ![a + 1, b + 1]) ∈ E ↔
      (jce_phi E ![a, b] ↔ ¬ jce_phi E ![a + 1, b]))











open Classical in


noncomputable def jce_Hc (E : Finset (Sym2 (Site 2))) (c b : ℤ) : ℕ :=
  (E.filter (fun e => jce_horizBelow c b e)).card

theorem jce_phi_eq_odd_Hc (E : Finset (Sym2 (Site 2))) (c b : ℤ) :
    jce_phi E ![c, b] ↔ Odd (jce_Hc E c b) := by
  have h0 : (![c, b] : Site 2) 0 = c := rfl
  have h1 : (![c, b] : Site 2) 1 = b := rfl
  rw [jce_phi_def, jce_Hc, h0, h1]

theorem jce_Hc_succ (E : Finset (Sym2 (Site 2))) (c b : ℤ) :
    jce_Hc E c (b + 1) = jce_Hc E c b + (if s(![c, b + 1], ![c + 1, b + 1]) ∈ E then 1 else 0) := by
  rw [jce_Hc, jce_Hc]; exact jce_filter_succ_card E c b




theorem jce_degree_decomp (E : Finset (Sym2 (Site 2))) (a r : ℤ) :
    jce_degree (E : Set (Sym2 (Site 2))) ![a + 1, r] =
      (if s(![a + 1, r], ![a + 1 + 1, r]) ∈ E then 1 else 0)
    + (if s(![a + 1, r], ![a, r]) ∈ E then 1 else 0)
    + (if s(![a + 1, r], ![a + 1, r + 1]) ∈ E then 1 else 0)
    + (if s(![a + 1, r], ![a + 1, r - 1]) ∈ E then 1 else 0) := by
  classical
  unfold jce_degree jce_nbr
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Finset.mem_coe]
  rw [Finset.card_filter, Fin.sum_univ_four]; norm_num



theorem jce_prop_const_of_step (Q : ℤ → Prop) (hstep : ∀ b, Q b ↔ Q (b + 1)) (b0 : ℤ)
    (hb0 : Q b0) : ∀ b, Q b := by
  have key : ∀ k : ℤ, Q (b0 + k) := by
    intro k
    induction k using Int.induction_on with
    | zero => simpa using hb0
    | succ n ih => rw [show b0 + ((n : ℤ) + 1) = (b0 + n) + 1 by ring]; exact (hstep _).mp ih
    | pred n ih =>
        exact (hstep (b0 + (-(n : ℤ) - 1))).mpr
          (by rw [show b0 + (-(n : ℤ) - 1) + 1 = b0 + (-(n : ℤ)) by ring]; exact ih)
  intro b
  have := key (b - b0)
  rwa [show b0 + (b - b0) = b by ring] at this



theorem jce_Q_step (E : Finset (Sym2 (Site 2)))
    (hcc : jce_ClosedContour (E : Set (Sym2 (Site 2)))) (a b : ℤ) :
    ((jce_Hc E a b + jce_Hc E (a + 1) b +
        (if s(![a + 1, b], ![a + 1, b + 1]) ∈ E then 1 else 0)) % 2 = 0) ↔
      ((jce_Hc E a (b + 1) + jce_Hc E (a + 1) (b + 1) +
        (if s(![a + 1, b + 1], ![a + 1, b + 1 + 1]) ∈ E then 1 else 0)) % 2 = 0) := by
  classical
  have hsa := jce_Hc_succ E a b
  have hsa1 := jce_Hc_succ E (a + 1) b
  have hdeg := hcc ![a + 1, b + 1]
  rw [jce_degree_decomp E a (b + 1), Nat.even_iff] at hdeg
  rw [show s(![a + 1, (b : ℤ) + 1], ![a, b + 1]) = s(![a, (b : ℤ) + 1], ![a + 1, b + 1]) from
        Sym2.eq_swap,
      show s(![a + 1, (b : ℤ) + 1], ![a + 1, b + 1 - 1]) = s(![a + 1, b], ![a + 1, b + 1]) by
        rw [show (b : ℤ) + 1 - 1 = b by ring, Sym2.eq_swap]] at hdeg
  rw [hsa, hsa1]
  set p1 := (if s(![a, (b : ℤ) + 1], ![a + 1, b + 1]) ∈ E then 1 else 0)
  set p2 := (if s(![a + 1, (b : ℤ) + 1], ![a + 1 + 1, b + 1]) ∈ E then 1 else 0)
  set p3 := (if s(![a + 1, (b : ℤ) + 1], ![a + 1, b + 1 + 1]) ∈ E then 1 else 0)
  set p4 := (if s(![a + 1, (b : ℤ)], ![a + 1, b + 1]) ∈ E then 1 else 0)
  omega



theorem jce_exists_lowRow (E : Finset (Sym2 (Site 2))) :
    ∃ L : ℤ, ∀ e ∈ E, ∀ x y : Site 2, e = s(x, y) → L ≤ x 1 ∧ L ≤ y 1 := by
  classical
  by_cases hE : E.Nonempty
  · refine ⟨(E.image (fun e => Sym2.lift ⟨fun x y => min (x 1) (y 1), by
      intro x y; simp only; rw [min_comm]⟩ e)).min' (hE.image _), ?_⟩
    intro e he x y hxy
    have hmin : (E.image (fun e => Sym2.lift ⟨fun x y => min (x 1) (y 1), by
        intro x y; simp only; rw [min_comm]⟩ e)).min' (hE.image _) ≤
          Sym2.lift ⟨fun x y => min (x 1) (y 1), by intro x y; simp only; rw [min_comm]⟩ e :=
      Finset.min'_le _ _ (Finset.mem_image_of_mem _ he)
    subst hxy
    simp only [Sym2.lift_mk] at hmin
    exact ⟨le_trans hmin (min_le_left _ _), le_trans hmin (min_le_right _ _)⟩
  · rw [Finset.not_nonempty_iff_eq_empty] at hE
    exact ⟨0, by simp [hE]⟩



theorem jce_Q_base (E : Finset (Sym2 (Site 2))) (a : ℤ) :
    ∃ b0 : ℤ, (jce_Hc E a b0 + jce_Hc E (a + 1) b0 +
      (if s(![a + 1, b0], ![a + 1, b0 + 1]) ∈ E then 1 else 0)) % 2 = 0 := by
  classical
  obtain ⟨L, hL⟩ := jce_exists_lowRow E
  refine ⟨L - 2, ?_⟩
  have hHc0 : ∀ c : ℤ, jce_Hc E c (L - 2) = 0 := by
    intro c
    rw [jce_Hc, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro e he
    induction e with
    | h x y =>
      rw [jce_horizBelow_mk]
      obtain ⟨hx, _⟩ := hL _ he x y rfl
      omega
  have hwall : s(![a + 1, L - 2], ![a + 1, L - 2 + 1]) ∉ E := by
    intro hmem
    obtain ⟨hx, _⟩ := hL _ hmem ![a + 1, L - 2] ![a + 1, L - 2 + 1] rfl
    simp only [Matrix.cons_val_one, Matrix.cons_val_zero] at hx
    omega
  rw [hHc0, hHc0, if_neg hwall]






theorem jce_horizStepResidue_holds : jce_HorizStepResidue := by
  classical
  intro E hcc a b
  obtain ⟨b0, hb0⟩ := jce_Q_base E a
  have hall := jce_prop_const_of_step
    (fun b => (jce_Hc E a b + jce_Hc E (a + 1) b +
      (if s(![a + 1, b], ![a + 1, b + 1]) ∈ E then 1 else 0)) % 2 = 0)
    (fun b => jce_Q_step E hcc a b) b0 hb0 b
  rw [jce_phi_eq_odd_Hc, jce_phi_eq_odd_Hc, Nat.odd_iff, Nat.odd_iff]
  by_cases hw : s(![a + 1, b], ![a + 1, b + 1]) ∈ E
  · rw [if_pos hw] at hall
    simp only [hw, true_iff]
    omega
  · rw [if_neg hw] at hall
    simp only [hw, false_iff, not_iff]
    omega













theorem jce_phi_compat (hres : jce_HorizStepResidue) (E : Finset (Sym2 (Site 2)))
    (hcc : jce_ClosedContour (E : Set (Sym2 (Site 2)))) (a b : Site 2)
    (hab : (hypercubicLattice 2).Adj a b) :
    (sharedPrimalEdge a b ∈ (E : Set (Sym2 (Site 2))) ↔ (jce_phi E a ↔ ¬ jce_phi E b)) := by
  classical
  have hab' := hab
  rw [hypercubicLattice_adj, Fin.sum_univ_two] at hab'
  set a0 := a 0 with ha0; set a1 := a 1 with ha1
  set b0 := b 0 with hb0; set b1 := b 1 with hb1
  have ha : a = ![a0, a1] := by funext i; fin_cases i <;> rfl
  have hb : b = ![b0, b1] := by funext i; fin_cases i <;> rfl
  rw [Finset.mem_coe]
  
  rw [ha, hb]
  clear_value a0 a1 b0 b1
  clear ha hb ha0 ha1 hb0 hb1 hab
  by_cases hc0 : a0 = b0
  · 
    subst hc0
    have hc1 : a1 = b1 + 1 ∨ b1 = a1 + 1 := by omega
    rcases hc1 with h | h
    · 
      subst h
      have key := jce_phi_topStep E a0 b1
      rw [show sharedPrimalEdge ![a0, b1 + 1] ![a0, b1] = s(![a0, b1 + 1], ![a0 + 1, b1 + 1]) by
        rw [show (![a0, b1] : Site 2) = ![a0, (b1 + 1) - 1] by norm_num, sharedPrimalEdge_bottom]
        unfold faceCorner00 faceCorner10; norm_num]
      rw [key]; tauto
    · 
      subst h
      have key := jce_phi_topStep E a0 a1
      rw [show sharedPrimalEdge ![a0, a1] ![a0, a1 + 1] = s(![a0, a1 + 1], ![a0 + 1, a1 + 1]) by
        rw [sharedPrimalEdge_top]; unfold faceCorner01 faceCorner11; norm_num]
      rw [key]
  · 
    have hc1 : a1 = b1 := by omega
    subst hc1
    have hc0' : a0 = b0 + 1 ∨ b0 = a0 + 1 := by omega
    rcases hc0' with h | h
    · 
      subst h
      have key := hres E hcc b0 a1
      rw [show sharedPrimalEdge ![b0 + 1, a1] ![b0, a1] = s(![b0 + 1, a1], ![b0 + 1, a1 + 1]) by
        rw [show (![b0, a1] : Site 2) = ![(b0 + 1) - 1, a1] by norm_num, sharedPrimalEdge_left]
        unfold faceCorner00 faceCorner01; norm_num]
      rw [key]; tauto
    · 
      subst h
      have key := hres E hcc a0 a1
      rw [show sharedPrimalEdge ![a0, a1] ![a0 + 1, a1] = s(![a0 + 1, a1], ![a0 + 1, a1 + 1]) by
        rw [sharedPrimalEdge_right]; unfold faceCorner10 faceCorner11; norm_num]
      rw [key]










def jce_edgeFlip (E : Finset (Sym2 (Site 2))) (a b : Site 2) : Prop :=
  sharedPrimalEdge a b ∈ E


theorem jce_edgeFlip_symm (E : Finset (Sym2 (Site 2))) : wcl_SymmFlip (jce_edgeFlip E) := by
  intro a b hab
  unfold jce_edgeFlip
  rw [sharedPrimalEdge_comm_of_adj hab]



theorem jce_edgeFlip_compat (hres : jce_HorizStepResidue) (E : Finset (Sym2 (Site 2)))
    (hcc : jce_ClosedContour (E : Set (Sym2 (Site 2)))) :
    ∀ a b, (hypercubicLattice 2).Adj a b →
      (jce_edgeFlip E a b ↔ (jce_phi E a ↔ ¬ jce_phi E b)) := by
  intro a b hab
  have := jce_phi_compat hres E hcc a b hab
  rwa [Finset.mem_coe] at this





theorem jce_edgeFlip_closedEven (hres : jce_HorizStepResidue) (E : Finset (Sym2 (Site 2)))
    (hcc : jce_ClosedContour (E : Set (Sym2 (Site 2)))) :
    wcl_ClosedEven (jce_edgeFlip E) :=
  wcl_closedEven_of_compat (jce_edgeFlip E) (jce_phi E) (jce_edgeFlip_compat hres E hcc)














theorem jce_sharedPrimalEdge_inj {a b c d : Site 2} (hab : (hypercubicLattice 2).Adj a b)
    (hcd : (hypercubicLattice 2).Adj c d) :
    (s(a, b) = s(c, d) ↔ sharedPrimalEdge a b = sharedPrimalEdge c d) := by
  constructor
  · intro h; rw [Sym2.eq_iff] at h
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rfl
    · exact sharedPrimalEdge_comm_of_adj hab
  · intro h
    have ha : a = ![a 0, a 1] := by funext i; fin_cases i <;> rfl
    have hb : b = ![b 0, b 1] := by funext i; fin_cases i <;> rfl
    have hc : c = ![c 0, c 1] := by funext i; fin_cases i <;> rfl
    have hd : d = ![d 0, d 1] := by funext i; fin_cases i <;> rfl
    have hab' := hab; have hcd' := hcd
    rw [hypercubicLattice_adj, Fin.sum_univ_two] at hab' hcd'
    rw [ha, hb, hc, hd] at h ⊢
    unfold sharedPrimalEdge at h
    by_cases h1 : a 0 = b 0 <;> by_cases h2 : c 0 = d 0 <;>
      simp only [h1, h2, if_true, if_false, Matrix.cons_val_zero, Matrix.cons_val_one,
        Sym2.eq_iff, whc_site_eq_iff] at h ⊢ <;> omega




theorem jce_cutFlip_eq_edgeFlip (H : SimpleGraph (Site 2)) [Fintype H.edgeSet]
    (f0 g0 : Site 2) (hfg : (hypercubicLattice 2).Adj f0 g0) {a b : Site 2}
    (hab : (hypercubicLattice 2).Adj a b) :
    (wcl_cutFlip H f0 g0 a b ↔
      jce_edgeFlip (insert (sharedPrimalEdge f0 g0) H.edgeSet.toFinset) a b) := by
  unfold wcl_cutFlip whc_isCross jce_edgeFlip
  rw [Finset.mem_insert, Set.mem_toFinset]
  have hsy : sharedPrimalEdge b a = sharedPrimalEdge a b :=
    (sharedPrimalEdge_comm_of_adj hab).symm
  rw [hsy]
  rw [jce_sharedPrimalEdge_inj hab hfg]
  tauto










theorem jce_flipCount_congr (flip flip' : Site 2 → Site 2 → Prop)
    (hagree : ∀ a b, (hypercubicLattice 2).Adj a b → (flip a b ↔ flip' a b))
    {x y : Site 2} (w : (hypercubicLattice 2).Walk x y) :
    wcl_flipCount flip w = wcl_flipCount flip' w := by
  induction w with
  | nil => rw [wcl_flipCount_nil, wcl_flipCount_nil]
  | @cons a b c hab p ih =>
    rw [wcl_flipCount_cons, wcl_flipCount_cons, ih]
    have h1 := hagree a b hab
    have h2 := hagree b a hab.symm
    by_cases hf : flip a b ∨ flip b a
    · rw [if_pos hf, if_pos (by tauto)]
    · rw [if_neg hf, if_neg (by tauto)]


theorem jce_closedEven_congr (flip flip' : Site 2 → Site 2 → Prop)
    (hagree : ∀ a b, (hypercubicLattice 2).Adj a b → (flip a b ↔ flip' a b))
    (hce : wcl_ClosedEven flip') : wcl_ClosedEven flip := by
  intro x w
  rw [jce_flipCount_congr flip flip' hagree w]
  exact hce w






theorem jce_cutFlip_closedEven (hres : jce_HorizStepResidue) (H : SimpleGraph (Site 2))
    [Fintype H.edgeSet] (f0 g0 : Site 2) (hfg : (hypercubicLattice 2).Adj f0 g0)
    (hcc : jce_ClosedContour
      ((insert (sharedPrimalEdge f0 g0) H.edgeSet.toFinset : Finset (Sym2 (Site 2)))
        : Set (Sym2 (Site 2)))) :
    wcl_ClosedEven (wcl_cutFlip H f0 g0) := by
  set E := insert (sharedPrimalEdge f0 g0) H.edgeSet.toFinset with hE
  apply jce_closedEven_congr (wcl_cutFlip H f0 g0) (jce_edgeFlip E)
    (fun a b hab => jce_cutFlip_eq_edgeFlip H f0 g0 hfg hab)
  exact jce_edgeFlip_closedEven hres E hcc







theorem jce_whitney_forward_of_evenDegree (hres : jce_HorizStepResidue) (H : SimpleGraph (Site 2))
    [Fintype H.edgeSet] (p q f0 g0 : Site 2) (hpq : (hypercubicLattice 2).Adj p q)
    (hnpq : s(p, q) ∉ H.edgeSet) (hfg : (hypercubicLattice 2).Adj f0 g0)
    (hshared : sharedPrimalEdge f0 g0 = s(p, q))
    (hcc : jce_ClosedContour
      ((insert (sharedPrimalEdge f0 g0) H.edgeSet.toFinset : Finset (Sym2 (Site 2)))
        : Set (Sym2 (Site 2)))) :
    ¬ ((whb_faceRegion H).deleteEdges {s(f0, g0)}).Reachable f0 g0 :=
  wcl_whitney_forward_of_closedEven H p q f0 g0 hpq hnpq hfg hshared
    (jce_cutFlip_closedEven hres H f0 g0 hfg hcc)












theorem jce_cutFlip_closedEven' (H : SimpleGraph (Site 2)) [Fintype H.edgeSet]
    (f0 g0 : Site 2) (hfg : (hypercubicLattice 2).Adj f0 g0)
    (hcc : jce_ClosedContour
      ((insert (sharedPrimalEdge f0 g0) H.edgeSet.toFinset : Finset (Sym2 (Site 2)))
        : Set (Sym2 (Site 2)))) :
    wcl_ClosedEven (wcl_cutFlip H f0 g0) :=
  jce_cutFlip_closedEven jce_horizStepResidue_holds H f0 g0 hfg hcc








theorem jce_discreteJordanFaithful_of_evenDegree (H : SimpleGraph (Site 2)) [Fintype H.edgeSet]
    (p q f0 g0 : Site 2) (hpq : (hypercubicLattice 2).Adj p q)
    (hnpq : s(p, q) ∉ H.edgeSet) (hfg : (hypercubicLattice 2).Adj f0 g0)
    (hshared : sharedPrimalEdge f0 g0 = s(p, q))
    (hcc : jce_ClosedContour
      ((insert (sharedPrimalEdge f0 g0) H.edgeSet.toFinset : Finset (Sym2 (Site 2)))
        : Set (Sym2 (Site 2)))) :
    ¬ ((whb_faceRegion H).deleteEdges {s(f0, g0)}).Reachable f0 g0 :=
  jce_whitney_forward_of_evenDegree jce_horizStepResidue_holds H p q f0 g0 hpq hnpq hfg hshared hcc
























theorem jce_empty_closedContour :
    jce_ClosedContour ((∅ : Finset (Sym2 (Site 2))) : Set (Sym2 (Site 2))) := by
  classical
  intro v
  unfold jce_degree jce_nbr
  rw [Nat.even_iff, Finset.card_filter, Fin.sum_univ_four]
  simp only [Finset.mem_coe, Finset.notMem_empty, if_false, add_zero]



theorem jce_empty_closedEven :
    wcl_ClosedEven (jce_edgeFlip (∅ : Finset (Sym2 (Site 2)))) :=
  jce_edgeFlip_closedEven jce_horizStepResidue_holds ∅ jce_empty_closedContour







theorem jce_singleEdge_not_closedContour :
    ¬ jce_ClosedContour
      (({s(![(0:ℤ), 0], ![1, 0])} : Finset (Sym2 (Site 2))) : Set (Sym2 (Site 2))) := by
  classical
  intro h
  have hd := h ![(0:ℤ), 0]
  unfold jce_degree jce_nbr at hd
  simp only [Finset.mem_coe, Finset.mem_singleton, Matrix.cons_val_zero,
    Matrix.cons_val_one] at hd
  rw [Nat.even_iff, Finset.card_filter, Fin.sum_univ_four] at hd
  simp only [Sym2.eq_iff, whc_site_eq_iff, Matrix.cons_val_zero, Matrix.cons_val_one] at hd
  norm_num at hd

















def jce_TwoOddReachable : Prop :=
  ∀ (H : SimpleGraph (Site 2)) [SimpleGraph.LocallyFinite H] (p q : Site 2),
    Odd (H.degree p) → Odd (H.degree q) →
    (∀ v, v ≠ p → v ≠ q → Even (H.degree v)) → H.Reachable p q





theorem jce_reachable_of_twoOdd (hodd : jce_TwoOddReachable) (H : SimpleGraph (Site 2))
    [SimpleGraph.LocallyFinite H] (p q : Site 2)
    (hp : Odd (H.degree p)) (hq : Odd (H.degree q))
    (hother : ∀ v, v ≠ p → v ≠ q → Even (H.degree v)) :
    H.Reachable p q :=
  hodd H p q hp hq hother

end Lattice

end StatMech

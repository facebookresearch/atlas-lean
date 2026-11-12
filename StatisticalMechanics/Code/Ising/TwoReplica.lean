/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

















































































import Mathlib

open Finset Classical
open scoped symmDiff BigOperators

set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

namespace StatMech

namespace Ising






abbrev Current (V : Type*) : Type _ := Sym2 V → ℕ

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (E : Finset (Sym2 V))



def incidentFlux (n : Current V) (x : V) : ℕ :=
  ∑ e ∈ E.filter (fun e => x ∈ e), n e



def sources (n : Current V) : Finset V :=
  Finset.univ.filter (fun x => Odd (incidentFlux E n x))

@[simp] lemma mem_sources {n : Current V} {x : V} :
    x ∈ sources E n ↔ Odd (incidentFlux E n x) := by simp [sources]


lemma incidentFlux_add (n m : Current V) (x : V) :
    incidentFlux E (fun e => n e + m e) x
      = incidentFlux E n x + incidentFlux E m x := by
  unfold incidentFlux; rw [← Finset.sum_add_distrib]




lemma sources_add (n m : Current V) :
    sources E (fun e => n e + m e) = sources E n ∆ sources E m := by
  ext x
  simp only [mem_sources, incidentFlux_add, Finset.mem_symmDiff]
  rw [← ZMod.natCast_eq_one_iff_odd, ← ZMod.natCast_eq_one_iff_odd,
    ← ZMod.natCast_eq_one_iff_odd]
  push_cast
  generalize (incidentFlux E n x : ZMod 2) = a
  generalize (incidentFlux E m x : ZMod 2) = b
  revert a b; decide





def adjP (P : Finset (Sym2 V)) (a b : V) : Prop :=
  ∃ e ∈ P, a ∈ e ∧ b ∈ e ∧ a ≠ b


def connP (P : Finset (Sym2 V)) : V → V → Prop :=
  Relation.ReflTransGen (adjP P)

lemma adjP_symm (P : Finset (Sym2 V)) {a b : V} : adjP P a b → adjP P b a := by
  rintro ⟨e, he, ha, hb, hne⟩; exact ⟨e, he, hb, ha, hne.symm⟩

lemma connP_symm (P : Finset (Sym2 V)) {a b : V} : connP P a b → connP P b a := by
  intro h
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hstep ih => exact Relation.ReflTransGen.head (adjP_symm P hstep) ih

lemma connP_mono {P Q : Finset (Sym2 V)} (hPQ : P ⊆ Q) {a b : V} (h : connP P a b) :
    connP Q a b := by
  refine Relation.ReflTransGen.mono ?_ h
  rintro x y ⟨e, he, hx, hy, hne⟩; exact ⟨e, hPQ he, hx, hy, hne⟩



def posEdges (m : Current V) : Finset (Sym2 V) := E.filter (fun e => 1 ≤ m e)


def oddEdges (m : Current V) : Finset (Sym2 V) := E.filter (fun e => Odd (m e))

lemma oddEdges_subset (m : Current V) : oddEdges E m ⊆ E := Finset.filter_subset _ _


lemma oddEdges_subset_posEdges (m : Current V) : oddEdges E m ⊆ posEdges E m := by
  intro e he
  rw [oddEdges, Finset.mem_filter] at he
  rw [posEdges, Finset.mem_filter]
  exact ⟨he.1, he.2.pos⟩




lemma connOdd_imp_connPos (m : Current V) {u v : V}
    (h : connP (oddEdges E m) u v) : connP (posEdges E m) u v :=
  connP_mono (oddEdges_subset_posEdges E m) h





def degP (P : Finset (Sym2 V)) (x : V) : ℕ := #(P.filter (fun e => x ∈ e))



def srcP (P : Finset (Sym2 V)) : Finset V :=
  Finset.univ.filter (fun x => Odd (degP P x))

@[simp] lemma mem_srcP {P : Finset (Sym2 V)} {x : V} :
    x ∈ srcP P ↔ Odd (degP P x) := by simp [srcP]


noncomputable def compOf (P : Finset (Sym2 V)) (u : V) : Finset V :=
  Finset.univ.filter (fun x => connP P u x)

@[simp] lemma mem_compOf {P : Finset (Sym2 V)} {u x : V} :
    x ∈ compOf P u ↔ connP P u x := by simp [compOf]



lemma comp_edge_card_even (P : Finset (Sym2 V)) (hnd : ∀ e ∈ P, ¬ e.IsDiag)
    (u : V) {e : Sym2 V} (he : e ∈ P) :
    Even (#((compOf P u).filter (fun x => x ∈ e))) := by
  obtain ⟨⟨a, b⟩, hab⟩ := e.exists_rep
  have hne : a ≠ b := by
    intro h; subst h; exact hnd e he (hab ▸ Sym2.mk_isDiag_iff.2 rfl)
  have hset : (compOf P u).filter (fun x => x ∈ e)
            = (({a, b} : Finset V)).filter (fun x => x ∈ compOf P u) := by
    ext x
    simp only [Finset.mem_filter, ← hab, Sym2.mem_iff, Finset.mem_insert,
      Finset.mem_singleton]
    tauto
  rw [hset]
  have key : (a ∈ compOf P u) ↔ (b ∈ compOf P u) := by
    constructor
    · intro ha
      rw [mem_compOf] at ha ⊢
      exact ha.tail ⟨e, he, hab ▸ Sym2.mem_mk_left a b, hab ▸ Sym2.mem_mk_right a b, hne⟩
    · intro hb
      rw [mem_compOf] at hb ⊢
      exact hb.tail ⟨e, he, hab ▸ Sym2.mem_mk_right a b, hab ▸ Sym2.mem_mk_left a b, hne.symm⟩
  by_cases ha : a ∈ compOf P u
  · have hb := key.1 ha
    rw [Finset.filter_insert, Finset.filter_singleton, if_pos ha, if_pos hb,
      Finset.card_insert_of_notMem (by simp [hne]), Finset.card_singleton]
    exact ⟨1, rfl⟩
  · have hb : b ∉ compOf P u := fun h => ha (key.2 h)
    rw [Finset.filter_insert, Finset.filter_singleton, if_neg ha, if_neg hb]; simp



lemma sum_deg_comp_eq (P : Finset (Sym2 V)) (u : V) :
    ∑ x ∈ compOf P u, degP P x
      = ∑ e ∈ P, #((compOf P u).filter (fun x => x ∈ e)) := by
  unfold degP; simp only [Finset.card_filter]; rw [Finset.sum_comm]



lemma sum_deg_comp_even (P : Finset (Sym2 V)) (hnd : ∀ e ∈ P, ¬ e.IsDiag) (u : V) :
    Even (∑ x ∈ compOf P u, degP P x) := by
  rw [sum_deg_comp_eq]
  exact Finset.even_sum _ (fun e he => comp_edge_card_even P hnd u he)


lemma even_sum_iff_even_count {α : Type*} (s : Finset α) (f : α → ℕ) :
    Even (∑ x ∈ s, f x) ↔ Even (#(s.filter (fun x => Odd (f x)))) := by
  rw [← ZMod.natCast_eq_zero_iff_even, ← ZMod.natCast_eq_zero_iff_even]
  have key : ((∑ x ∈ s, f x : ℕ) : ZMod 2)
      = ((#(s.filter (fun x => Odd (f x))) : ℕ) : ZMod 2) := by
    push_cast; rw [Finset.card_filter]; push_cast
    refine Finset.sum_congr rfl (fun x _ => ?_)
    rcases Nat.even_or_odd (f x) with h | h
    · rw [if_neg (by simp [Nat.not_odd_iff_even, h]), ZMod.natCast_eq_zero_iff_even.2 h]
    · rw [if_pos h, ZMod.natCast_eq_one_iff_odd.2 h]
  rw [key]





lemma path_exists (P : Finset (Sym2 V)) (hnd : ∀ e ∈ P, ¬ e.IsDiag) (u v : V)
    (hu_odd : Odd (degP P u))
    (hbdry : ∀ x, Odd (degP P x) → x = u ∨ x = v) (huv : u ≠ v) :
    connP P u v := by
  have hsum_even := sum_deg_comp_even P hnd u
  have hu_in : u ∈ compOf P u := by rw [mem_compOf]; exact Relation.ReflTransGen.refl
  by_contra hcon
  have hv_notin : v ∉ compOf P u := by rw [mem_compOf]; exact hcon
  have hoddC : (compOf P u).filter (fun x => Odd (degP P x)) = {u} := by
    ext x; simp only [Finset.mem_filter, Finset.mem_singleton]
    constructor
    · rintro ⟨hxC, hxodd⟩
      rcases hbdry x hxodd with h | h
      · exact h
      · subst h; exact absurd hxC hv_notin
    · rintro rfl; exact ⟨hu_in, hu_odd⟩
  have hcount : Even (#((compOf P u).filter (fun x => Odd (degP P x)))) :=
    (even_sum_iff_even_count _ _).1 hsum_even
  rw [hoddC, Finset.card_singleton] at hcount
  exact (Nat.not_even_iff_odd.2 ⟨0, rfl⟩) hcount




lemma card_filter_zmod {α : Type*} [DecidableEq α] [Fintype α]
    (T : Finset α) (p : α → Prop) [DecidablePred p] :
    ((#(T.filter p) : ℕ) : ZMod 2)
      = ∑ i : α, (if i ∈ T then (1 : ZMod 2) else 0)
          * (if p i then (1 : ZMod 2) else 0) := by
  have step : ∀ i : α,
      (if i ∈ T then (1 : ZMod 2) else 0) * (if p i then (1 : ZMod 2) else 0)
        = (if i ∈ T then (if p i then (1 : ZMod 2) else 0) else 0) := by
    intro i; by_cases hT : i ∈ T <;> simp [hT]
  simp_rw [step]
  rw [← Finset.sum_filter (· ∈ T) (fun i => if p i then (1 : ZMod 2) else 0),
    Finset.filter_mem_eq_inter, Finset.univ_inter, Finset.card_filter]
  push_cast; rfl


lemma odd_degP_symmDiff (S T : Finset (Sym2 V)) (x : V) :
    Odd (degP (S ∆ T) x) ↔ (Odd (degP S x) ≠ Odd (degP T x)) := by
  unfold degP
  rw [← ZMod.natCast_eq_one_iff_odd, ← ZMod.natCast_eq_one_iff_odd,
    ← ZMod.natCast_eq_one_iff_odd, card_filter_zmod, card_filter_zmod, card_filter_zmod]
  have hlin :
      ∑ i : Sym2 V, (if i ∈ S ∆ T then (1 : ZMod 2) else 0)
          * (if x ∈ i then (1 : ZMod 2) else 0)
        = (∑ i : Sym2 V, (if i ∈ S then (1 : ZMod 2) else 0)
            * (if x ∈ i then (1 : ZMod 2) else 0))
          + (∑ i : Sym2 V, (if i ∈ T then (1 : ZMod 2) else 0)
              * (if x ∈ i then (1 : ZMod 2) else 0)) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    have hind : (if i ∈ S ∆ T then (1 : ZMod 2) else 0)
        = (if i ∈ S then (1 : ZMod 2) else 0) + (if i ∈ T then (1 : ZMod 2) else 0) := by
      simp only [Finset.mem_symmDiff]
      by_cases hS : i ∈ S <;> by_cases hT : i ∈ T <;> simp only [hS, hT] <;> decide
    rw [hind]; ring
  rw [hlin]
  generalize (∑ i : Sym2 V, (if i ∈ S then (1 : ZMod 2) else 0)
    * (if x ∈ i then (1 : ZMod 2) else 0)) = a
  generalize (∑ i : Sym2 V, (if i ∈ T then (1 : ZMod 2) else 0)
    * (if x ∈ i then (1 : ZMod 2) else 0)) = b
  revert a b; decide


lemma srcP_symmDiff (S T : Finset (Sym2 V)) :
    srcP (S ∆ T) = srcP S ∆ srcP T := by
  ext x
  simp only [mem_srcP, Finset.mem_symmDiff]
  rw [odd_degP_symmDiff]
  by_cases hS : Odd (degP S x) <;> by_cases hT : Odd (degP T x) <;> simp [hS, hT]



lemma srcP_singleton (e : Sym2 V) (a b : V) (hab : e = s(a, b)) (hne : a ≠ b) :
    srcP ({e} : Finset (Sym2 V)) = {a, b} := by
  have ha : a ∈ e := hab ▸ Sym2.mem_mk_left a b
  have hb : b ∈ e := hab ▸ Sym2.mem_mk_right a b
  ext x
  simp only [mem_srcP, degP, Finset.filter_singleton, Finset.mem_insert, Finset.mem_singleton]
  by_cases hx : x ∈ e
  · rw [if_pos hx, Finset.card_singleton]
    have hxab : x = a ∨ x = b := by rw [hab, Sym2.mem_iff] at hx; exact hx
    simp only [show Odd 1 from ⟨0, rfl⟩, true_iff]; exact hxab
  · rw [if_neg hx, Finset.card_empty]
    have hnot : ¬ (x = a ∨ x = b) := by
      rintro (rfl | rfl)
      · exact hx ha
      · exact hx hb
    simp only [show ¬ Odd 0 from by decide, false_iff]; exact hnot





lemma exists_conn_set (P₀ : Finset (Sym2 V)) {u v : V}
    (hconn : connP P₀ u v) (huv : u ≠ v) :
    ∃ P ⊆ P₀, srcP P = {u, v} := by
  suffices h : ∀ w, connP P₀ u w → ∃ P ⊆ P₀, srcP P = ({u} : Finset V) ∆ {w} by
    obtain ⟨P, hPm, hP⟩ := h v hconn
    refine ⟨P, hPm, ?_⟩
    rw [hP]; ext x
    simp only [Finset.mem_symmDiff, Finset.mem_singleton, Finset.mem_insert]
    constructor
    · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> tauto
    · rintro (rfl | rfl)
      · left; exact ⟨rfl, huv⟩
      · right; exact ⟨rfl, fun h => huv h.symm⟩
  intro w hconnw
  induction hconnw with
  | refl =>
    refine ⟨∅, Finset.empty_subset _, ?_⟩
    rw [symmDiff_self]; ext x; simp [srcP, degP]
  | @tail b c _ hstep ih =>
    obtain ⟨P, hPm, hP⟩ := ih
    obtain ⟨e, he, hb, hc, hbc⟩ := hstep
    refine ⟨P ∆ {e}, ?_, ?_⟩
    · intro x hx
      rw [Finset.mem_symmDiff] at hx
      rcases hx with ⟨h, _⟩ | ⟨h, _⟩
      · exact hPm h
      · rw [Finset.mem_singleton] at h; subst h; exact he
    · rw [srcP_symmDiff, hP]
      obtain ⟨⟨a, a'⟩, haa⟩ := e.exists_rep
      have hbc' : e = s(b, c) := by
        rw [← haa] at hb hc ⊢
        rw [Sym2.mem_iff] at hb hc
        rcases hb with rfl | rfl <;> rcases hc with rfl | rfl <;>
          first | rfl | (exact absurd rfl hbc) | rw [Sym2.eq_swap]
      have hsi : srcP ({e} : Finset (Sym2 V)) = {b, c} := srcP_singleton e b c hbc' hbc
      rw [hsi]
      have hbc'' : ({b, c} : Finset V) = {b} ∆ {c} := by
        ext x
        simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_symmDiff]
        constructor
        · rintro (rfl | rfl)
          · left; exact ⟨rfl, fun h => hbc (by simpa using h)⟩
          · right; exact ⟨rfl, fun h => hbc (by simpa using h.symm)⟩
        · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> tauto
      rw [hbc'', symmDiff_assoc, ← symmDiff_assoc ({b} : Finset V), symmDiff_self, bot_symmDiff]




lemma srcP_oddEdges (m : Current V) : srcP (oddEdges E m) = sources E m := by
  ext x
  simp only [srcP, sources, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [← ZMod.natCast_eq_one_iff_odd, ← ZMod.natCast_eq_one_iff_odd]
  have key : ((degP (oddEdges E m) x : ℕ) : ZMod 2)
      = ((incidentFlux E m x : ℕ) : ZMod 2) := by
    unfold degP oddEdges incidentFlux
    rw [Finset.filter_filter, Finset.card_filter, Finset.sum_filter]
    push_cast
    refine Finset.sum_congr rfl (fun e he => ?_)
    by_cases hx : x ∈ e
    · rw [if_pos hx]
      by_cases ho : Odd (m e)
      · rw [if_pos ⟨ho, hx⟩, ZMod.natCast_eq_one_iff_odd.2 ho]
      · rw [if_neg (fun ⟨h, _⟩ => ho h)]
        rw [Nat.not_odd_iff_even] at ho; rw [ZMod.natCast_eq_zero_iff_even.2 ho]
    · rw [if_neg hx, if_neg (fun ⟨_, h⟩ => hx h)]
  rw [key]







def reflect (m : Current V) (P : Finset (Sym2 V)) (n : Current V) : Current V :=
  fun e => if e ∈ P then m e - n e else n e

@[simp] lemma reflect_apply (m : Current V) (P : Finset (Sym2 V)) (n : Current V) (e : Sym2 V) :
    reflect m P n e = if e ∈ P then m e - n e else n e := rfl


lemma reflect_le (m : Current V) (P : Finset (Sym2 V)) {n : Current V}
    (hn : ∀ e, n e ≤ m e) : ∀ e, reflect m P n e ≤ m e := by
  intro e; unfold reflect
  by_cases h : e ∈ P
  · simp only [if_pos h]; omega
  · simp only [if_neg h]; exact hn e


lemma reflect_involutive (m : Current V) (P : Finset (Sym2 V)) {n : Current V}
    (hn : ∀ e, n e ≤ m e) : reflect m P (reflect m P n) = n := by
  funext e; unfold reflect
  by_cases h : e ∈ P
  · simp only [if_pos h]; have := hn e; omega
  · simp only [if_neg h]






lemma reflect_add_complement (m : Current V) (P : Finset (Sym2 V)) {n : Current V}
    (hn : ∀ e, n e ≤ m e) (e : Sym2 V) :
    reflect m P n e + reflect m P (fun e => m e - n e) e = m e := by
  unfold reflect
  by_cases h : e ∈ P
  · simp only [if_pos h]; have := hn e; omega
  · simp only [if_neg h]; have := hn e; omega




lemma reflect_complement (m : Current V) (P : Finset (Sym2 V)) (n : Current V) :
    (fun e => m e - reflect m P n e) = reflect m P (fun e => m e - n e) := by
  funext e; unfold reflect
  by_cases h : e ∈ P
  · simp only [if_pos h]
  · simp only [if_neg h]





lemma reflect_parity (m : Current V) (P : Finset (Sym2 V)) (n : Current V)
    (hn : ∀ e, n e ≤ m e) (hodd : ∀ e ∈ P, Odd (m e)) (e : Sym2 V) :
    ((reflect m P n e : ℕ) : ZMod 2)
      = (n e : ZMod 2) + (if e ∈ P then 1 else 0) := by
  unfold reflect
  by_cases h : e ∈ P
  · simp only [if_pos h]
    have hle := hn e
    have key : ((n e : ℕ) : ZMod 2) + ((m e - n e : ℕ) : ZMod 2) = (m e : ZMod 2) := by
      rw [← Nat.cast_add, Nat.add_sub_cancel' hle]
    have hm1 : ((m e : ℕ) : ZMod 2) = 1 := by
      rw [ZMod.natCast_eq_one_iff_odd]; exact hodd e h
    rw [hm1] at key
    have heq : ((m e - n e : ℕ) : ZMod 2) = 1 - (n e : ZMod 2) := by
      rw [eq_sub_iff_add_eq, add_comm]; exact key
    rw [heq, sub_eq_add_neg, CharTwo.neg_eq, add_comm]
  · simp only [if_neg h, add_zero]



lemma degP_as_sum (P : Finset (Sym2 V)) (hP : P ⊆ E) (x : V) :
    degP P x = ∑ e ∈ E.filter (fun e => x ∈ e), (if e ∈ P then 1 else 0) := by
  unfold degP
  rw [Finset.card_eq_sum_ones, ← Finset.sum_filter]
  apply Finset.sum_congr _ (fun _ _ => rfl)
  ext e
  simp only [Finset.mem_filter]
  exact ⟨fun ⟨hP', hx⟩ => ⟨⟨hP hP', hx⟩, hP'⟩, fun ⟨⟨_, hx⟩, hP'⟩ => ⟨hP', hx⟩⟩



lemma flux_reflect_parity (m : Current V) (P : Finset (Sym2 V)) (n : Current V)
    (hn : ∀ e, n e ≤ m e) (hP : P ⊆ E) (hodd : ∀ e ∈ P, Odd (m e)) (x : V) :
    ((incidentFlux E (reflect m P n) x : ℕ) : ZMod 2)
      = ((incidentFlux E n x : ℕ) : ZMod 2) + ((degP P x : ℕ) : ZMod 2) := by
  unfold incidentFlux
  rw [degP_as_sum E P hP x]
  push_cast
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun e he => ?_)
  rw [reflect_parity m P n hn hodd e]









lemma sources_reflect (m : Current V) (P : Finset (Sym2 V)) (n : Current V)
    (hn : ∀ e, n e ≤ m e) (hP : P ⊆ E) (hodd : ∀ e ∈ P, Odd (m e)) :
    sources E (reflect m P n) = sources E n ∆ srcP P := by
  ext x
  simp only [mem_sources, mem_srcP, Finset.mem_symmDiff]
  rw [← ZMod.natCast_eq_one_iff_odd, ← ZMod.natCast_eq_one_iff_odd,
    ← ZMod.natCast_eq_one_iff_odd, flux_reflect_parity E m P n hn hP hodd x]
  generalize ((incidentFlux E n x : ℕ) : ZMod 2) = a
  generalize ((degP P x : ℕ) : ZMod 2) = b
  revert a b; decide





lemma reflect_bijOn (m : Current V) (P : Finset (Sym2 V)) (hP : P ⊆ E)
    (hodd : ∀ e ∈ P, Odd (m e)) (A : Finset V) :
    Set.BijOn (reflect m P)
      {n | (∀ e, n e ≤ m e) ∧ sources E n = A}
      {n | (∀ e, n e ≤ m e) ∧ sources E n = A ∆ srcP P} := by
  refine ⟨?_, ?_, ?_⟩
  · rintro n ⟨hle, hA⟩
    exact ⟨reflect_le m P hle, by rw [sources_reflect E m P n hle hP hodd, hA]⟩
  · rintro n₁ ⟨h1, _⟩ n₂ ⟨h2, _⟩ heq
    have e1 := reflect_involutive m P h1
    have e2 := reflect_involutive m P h2
    rw [← e1, ← e2, heq]
  · rintro L ⟨hLle, hLA⟩
    refine ⟨reflect m P L, ⟨reflect_le m P hLle, ?_⟩, reflect_involutive m P hLle⟩
    rw [sources_reflect E m P L hLle hP hodd, hLA, symmDiff_assoc, symmDiff_self, symmDiff_bot]





noncomputable instance instFintypeSplit (m : Current V) :
    Fintype {n : Current V // ∀ e, n e ≤ m e} := by
  classical exact Fintype.ofFinite _







theorem connOdd_of_sources (m : Current V) (hnd : ∀ e ∈ E, ¬ e.IsDiag)
    {u v : V} (huv : u ≠ v) (hsrc : sources E m = {u, v}) :
    connP (oddEdges E m) u v := by
  have hPnd : ∀ e ∈ oddEdges E m, ¬ e.IsDiag := fun e he => hnd e (oddEdges_subset E m he)
  have hbdsrc : srcP (oddEdges E m) = {u, v} := by rw [srcP_oddEdges]; exact hsrc
  refine path_exists (oddEdges E m) hPnd u v ?_ ?_ huv
  · have : u ∈ srcP (oddEdges E m) := by rw [hbdsrc]; simp
    rwa [mem_srcP] at this
  · intro x hx
    have : x ∈ srcP (oddEdges E m) := by rw [mem_srcP]; exact hx
    rw [hbdsrc] at this; simpa using this













theorem ising_switching_lemma (m : Current V)
    {u v : V} (huv : u ≠ v) (hconn : connP (oddEdges E m) u v) (A : Finset V) :
    Nat.card {n : Current V // (∀ e, n e ≤ m e) ∧ sources E n = A ∆ {u, v}}
      = Nat.card {n : Current V // (∀ e, n e ≤ m e) ∧ sources E n = A} := by
  
  obtain ⟨P, hPodd, hPsrc⟩ := exists_conn_set (oddEdges E m) hconn huv
  have hPE : P ⊆ E := hPodd.trans (oddEdges_subset E m)
  have hPoddE : ∀ e ∈ P, Odd (m e) := by
    intro e he
    have := hPodd he; rw [oddEdges, Finset.mem_filter] at this; exact this.2
  
  have hbij := reflect_bijOn E m P hPE hPoddE A
  rw [hPsrc] at hbij
  
  have hcard := Nat.card_congr (hbij.equiv (reflect m P))
  
  have hL : Nat.card {n : Current V // (∀ e, n e ≤ m e) ∧ sources E n = A ∆ {u, v}}
      = Nat.card ({n | (∀ e, n e ≤ m e) ∧ sources E n = A ∆ {u, v}} : Set (Current V)) :=
    Nat.card_congr (Equiv.refl _)
  have hR : Nat.card {n : Current V // (∀ e, n e ≤ m e) ∧ sources E n = A}
      = Nat.card ({n | (∀ e, n e ≤ m e) ∧ sources E n = A} : Set (Current V)) :=
    Nat.card_congr (Equiv.refl _)
  rw [hL, hR, ← hcard]









theorem ising_switching_lemma_pair (n₁ n₂ : Current V)
    {u v : V} (huv : u ≠ v)
    (hconn : connP (oddEdges E (fun e => n₁ e + n₂ e)) u v) (A : Finset V) :
    Nat.card {n : Current V //
        (∀ e, n e ≤ n₁ e + n₂ e) ∧ sources E n = A ∆ {u, v}}
      = Nat.card {n : Current V //
        (∀ e, n e ≤ n₁ e + n₂ e) ∧ sources E n = A} :=
  ising_switching_lemma E (fun e => n₁ e + n₂ e) huv hconn A













theorem ising_switching_sourceless (m : Current V) (hnd : ∀ e ∈ E, ¬ e.IsDiag)
    {u v : V} (huv : u ≠ v) (hsrc : sources E m = {u, v}) :
    Nat.card {n : Current V // (∀ e, n e ≤ m e) ∧ sources E n = {u, v}}
      = Nat.card {n : Current V // (∀ e, n e ≤ m e) ∧ sources E n = ∅} := by
  have hconn := connOdd_of_sources E m hnd huv hsrc
  have h := ising_switching_lemma E m huv hconn ∅
  
  rwa [show (∅ : Finset V) ∆ {u, v} = {u, v} from symmDiff_eq_right.mpr rfl] at h

end Ising

end StatMech

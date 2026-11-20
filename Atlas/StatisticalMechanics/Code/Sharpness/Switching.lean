/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






















































import Mathlib

open Finset BigOperators
open scoped symmDiff
open Classical

set_option linter.unusedSectionVars false

namespace StatMech
namespace Sharpness

namespace RandomCurrent

variable {ι V : Type*} [DecidableEq ι] [DecidableEq V] [Fintype V] [Fintype ι]





def degK (ends : ι → Sym2 V) (T : Finset ι) (x : V) : ℕ :=
  #(T.filter (fun i => x ∈ ends i))


def sources (ends : ι → Sym2 V) (T : Finset ι) : Finset V :=
  (Finset.univ : Finset V).filter (fun x => Odd (degK ends T x))

@[simp] lemma mem_sources {ends : ι → Sym2 V} {T : Finset ι} {x : V} :
    x ∈ sources ends T ↔ Odd (degK ends T x) := by
  simp [sources]


def adjStep (ends : ι → Sym2 V) (K : Finset ι) (a b : V) : Prop :=
  ∃ i ∈ K, a ∈ ends i ∧ b ∈ ends i ∧ a ≠ b



def connK (ends : ι → Sym2 V) (K : Finset ι) : V → V → Prop :=
  Relation.ReflTransGen (adjStep ends K)

lemma adjStep_symm (ends : ι → Sym2 V) (K : Finset ι) {a b : V} :
    adjStep ends K a b → adjStep ends K b a := by
  rintro ⟨i, hi, ha, hb, hne⟩; exact ⟨i, hi, hb, ha, hne.symm⟩

lemma connK_symm (ends : ι → Sym2 V) (K : Finset ι) {a b : V} :
    connK ends K a b → connK ends K b a := by
  intro h
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hstep ih => exact Relation.ReflTransGen.head (adjStep_symm ends K hstep) ih


noncomputable def compOf (ends : ι → Sym2 V) (K : Finset ι) (u : V) : Finset V :=
  (Finset.univ : Finset V).filter (fun x => connK ends K u x)

@[simp] lemma mem_compOf {ends : ι → Sym2 V} {K : Finset ι} {u x : V} :
    x ∈ compOf ends K u ↔ connK ends K u x := by
  simp [compOf]





lemma card_filter_zmod {α : Type*} [DecidableEq α] [Fintype α]
    (T : Finset α) (p : α → Prop) [DecidablePred p] :
    ((#(T.filter p) : ℕ) : ZMod 2)
      = ∑ i : α, (if i ∈ T then (1 : ZMod 2) else 0) * (if p i then (1 : ZMod 2) else 0) := by
  have step : ∀ i : α, (if i ∈ T then (1 : ZMod 2) else 0) * (if p i then (1 : ZMod 2) else 0)
            = (if i ∈ T then (if p i then (1 : ZMod 2) else 0) else 0) := by
    intro i; by_cases hT : i ∈ T <;> simp [hT]
  simp_rw [step]
  rw [← Finset.sum_filter (· ∈ T) (fun i => if p i then (1 : ZMod 2) else 0),
    Finset.filter_mem_eq_inter, Finset.univ_inter, Finset.card_filter]
  push_cast; rfl



lemma odd_degK_symmDiff (ends : ι → Sym2 V) (S T : Finset ι) (x : V) :
    Odd (degK ends (S ∆ T) x) ↔ (Odd (degK ends S x) ≠ Odd (degK ends T x)) := by
  unfold degK
  rw [← ZMod.natCast_eq_one_iff_odd, ← ZMod.natCast_eq_one_iff_odd,
    ← ZMod.natCast_eq_one_iff_odd, card_filter_zmod, card_filter_zmod, card_filter_zmod]
  have hlin :
      ∑ i : ι, (if i ∈ S ∆ T then (1 : ZMod 2) else 0) * (if x ∈ ends i then (1 : ZMod 2) else 0)
        = (∑ i : ι, (if i ∈ S then (1 : ZMod 2) else 0) * (if x ∈ ends i then (1 : ZMod 2) else 0))
          + (∑ i : ι, (if i ∈ T then (1 : ZMod 2) else 0)
              * (if x ∈ ends i then (1 : ZMod 2) else 0)) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    have hind : (if i ∈ S ∆ T then (1 : ZMod 2) else 0)
        = (if i ∈ S then (1 : ZMod 2) else 0) + (if i ∈ T then (1 : ZMod 2) else 0) := by
      simp only [Finset.mem_symmDiff]
      by_cases hS : i ∈ S <;> by_cases hT : i ∈ T <;> simp only [hS, hT] <;> decide
    rw [hind]; ring
  rw [hlin]
  generalize
    (∑ i : ι, (if i ∈ S then (1 : ZMod 2) else 0) * (if x ∈ ends i then (1 : ZMod 2) else 0)) = a
  generalize
    (∑ i : ι, (if i ∈ T then (1 : ZMod 2) else 0) * (if x ∈ ends i then (1 : ZMod 2) else 0)) = b
  revert a b
  decide



lemma sources_symmDiff (ends : ι → Sym2 V) (S T : Finset ι) :
    sources ends (S ∆ T) = sources ends S ∆ sources ends T := by
  ext x
  simp only [mem_sources, Finset.mem_symmDiff]
  rw [odd_degK_symmDiff]
  by_cases hS : Odd (degK ends S x) <;> by_cases hT : Odd (degK ends T x) <;>
    simp [hS, hT]






lemma comp_edge_card_even (ends : ι → Sym2 V) (K : Finset ι)
    (hnd : ∀ i ∈ K, ¬ (ends i).IsDiag) (u : V) {i : ι} (hi : i ∈ K) :
    Even (#((compOf ends K u).filter (fun x => x ∈ ends i))) := by
  obtain ⟨⟨a, b⟩, hab⟩ := (ends i).exists_rep
  have hne : a ≠ b := by
    intro h; subst h; exact hnd i hi (hab ▸ Sym2.mk_isDiag_iff.2 rfl)
  have hset : (compOf ends K u).filter (fun x => x ∈ ends i)
            = (({a, b} : Finset V)).filter (fun x => x ∈ compOf ends K u) := by
    ext x
    simp only [Finset.mem_filter, ← hab, Sym2.mem_iff, Finset.mem_insert, Finset.mem_singleton]
    tauto
  rw [hset]
  have key : (a ∈ compOf ends K u) ↔ (b ∈ compOf ends K u) := by
    constructor
    · intro ha
      rw [mem_compOf] at ha ⊢
      exact ha.tail ⟨i, hi, hab ▸ Sym2.mem_mk_left a b, hab ▸ Sym2.mem_mk_right a b, hne⟩
    · intro hb
      rw [mem_compOf] at hb ⊢
      exact hb.tail ⟨i, hi, hab ▸ Sym2.mem_mk_right a b, hab ▸ Sym2.mem_mk_left a b, hne.symm⟩
  by_cases ha : a ∈ compOf ends K u
  · have hb := key.1 ha
    rw [Finset.filter_insert, Finset.filter_singleton, if_pos ha, if_pos hb,
      Finset.card_insert_of_notMem (by simp [hne]), Finset.card_singleton]
    exact ⟨1, rfl⟩
  · have hb : b ∉ compOf ends K u := fun h => ha (key.2 h)
    rw [Finset.filter_insert, Finset.filter_singleton, if_neg ha, if_neg hb]; simp



lemma sum_deg_comp_eq (ends : ι → Sym2 V) (K : Finset ι) (u : V) :
    ∑ x ∈ compOf ends K u, degK ends K x
      = ∑ i ∈ K, #((compOf ends K u).filter (fun x => x ∈ ends i)) := by
  unfold degK
  simp only [Finset.card_filter]
  rw [Finset.sum_comm]



lemma sum_deg_comp_even (ends : ι → Sym2 V) (K : Finset ι)
    (hnd : ∀ i ∈ K, ¬ (ends i).IsDiag) (u : V) :
    Even (∑ x ∈ compOf ends K u, degK ends K x) := by
  rw [sum_deg_comp_eq]
  exact Finset.even_sum _ (fun i hi => comp_edge_card_even ends K hnd u hi)


lemma even_sum_iff_even_count {α : Type*} (s : Finset α) (f : α → ℕ) :
    Even (∑ x ∈ s, f x) ↔ Even (#(s.filter (fun x => Odd (f x)))) := by
  rw [← ZMod.natCast_eq_zero_iff_even, ← ZMod.natCast_eq_zero_iff_even]
  have key : ((∑ x ∈ s, f x : ℕ) : ZMod 2)
      = ((#(s.filter (fun x => Odd (f x))) : ℕ) : ZMod 2) := by
    push_cast
    rw [Finset.card_filter]
    push_cast
    refine Finset.sum_congr rfl (fun x _ => ?_)
    rcases Nat.even_or_odd (f x) with h | h
    · rw [if_neg (by simp [Nat.not_odd_iff_even, h]), ZMod.natCast_eq_zero_iff_even.2 h]
    · rw [if_pos h, ZMod.natCast_eq_one_iff_odd.2 h]
  rw [key]





lemma path_exists (ends : ι → Sym2 V) (K : Finset ι)
    (hnd : ∀ i ∈ K, ¬ (ends i).IsDiag) (u v : V)
    (hu_odd : Odd (degK ends K u))
    (hbdry : ∀ x, Odd (degK ends K x) → x = u ∨ x = v)
    (huv : u ≠ v) :
    connK ends K u v := by
  have hsum_even := sum_deg_comp_even ends K hnd u
  have hu_in : u ∈ compOf ends K u := by rw [mem_compOf]; exact Relation.ReflTransGen.refl
  by_contra hcon
  have hv_notin : v ∉ compOf ends K u := by rw [mem_compOf]; exact hcon
  have hoddC : (compOf ends K u).filter (fun x => Odd (degK ends K x)) = {u} := by
    ext x; simp only [Finset.mem_filter, Finset.mem_singleton]
    constructor
    · rintro ⟨hxC, hxodd⟩
      rcases hbdry x hxodd with h | h
      · exact h
      · subst h; exact absurd hxC hv_notin
    · rintro rfl; exact ⟨hu_in, hu_odd⟩
  have hcount : Even (#((compOf ends K u).filter (fun x => Odd (degK ends K x)))) :=
    (even_sum_iff_even_count _ _).1 hsum_even
  rw [hoddC, Finset.card_singleton] at hcount
  exact (Nat.not_even_iff_odd.2 ⟨0, rfl⟩) hcount






lemma sources_shift_bijOn (ends : ι → Sym2 V) (m P : Finset ι) (hP : P ⊆ m) (A : Finset V) :
    Set.BijOn (fun K => K ∆ P)
      {K | K ⊆ m ∧ sources ends K = A}
      {K | K ⊆ m ∧ sources ends K = A ∆ sources ends P} := by
  have hsub : ∀ {K : Finset ι}, K ⊆ m → K ∆ P ⊆ m := by
    intro K hK x hx
    rw [Finset.mem_symmDiff] at hx
    rcases hx with ⟨h, _⟩ | ⟨h, _⟩
    · exact hK h
    · exact hP h
  refine ⟨?_, ?_, ?_⟩
  · 
    rintro K ⟨hKm, hKA⟩
    refine ⟨hsub hKm, ?_⟩
    rw [sources_symmDiff, hKA]
  · 
    rintro K₁ ⟨_, _⟩ K₂ ⟨_, _⟩ h
    simp only at h
    have : (K₁ ∆ P) ∆ P = (K₂ ∆ P) ∆ P := by rw [h]
    rwa [symmDiff_symmDiff_cancel_right, symmDiff_symmDiff_cancel_right] at this
  · 
    rintro L ⟨hLm, hLA⟩
    refine ⟨L ∆ P, ⟨hsub hLm, ?_⟩, ?_⟩
    · rw [sources_symmDiff, hLA, symmDiff_assoc, symmDiff_self, symmDiff_bot]
    · simp only; rw [symmDiff_symmDiff_cancel_right]




lemma exists_conn_set (ends : ι → Sym2 V) (m : Finset ι)
    {u v : V} (hconn : connK ends m u v) (huv : u ≠ v) :
    ∃ P ⊆ m, sources ends P = {u, v} := by
  
  suffices h : ∀ w, connK ends m u w → ∃ P ⊆ m, sources ends P = ({u} : Finset V) ∆ {w} by
    obtain ⟨P, hPm, hP⟩ := h v hconn
    refine ⟨P, hPm, ?_⟩
    rw [hP]
    ext x
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
    rw [symmDiff_self]
    ext x; simp [sources, degK]
  | @tail b c _ hstep ih =>
    obtain ⟨P, hPm, hP⟩ := ih
    obtain ⟨i, hi, hb, hc, hbc⟩ := hstep
    refine ⟨P ∆ {i}, ?_, ?_⟩
    · intro x hx
      rw [Finset.mem_symmDiff] at hx
      rcases hx with ⟨h, _⟩ | ⟨h, _⟩
      · exact hPm h
      · rw [Finset.mem_singleton] at h; subst h; exact hi
    · rw [sources_symmDiff, hP]
      have hsi : sources ends {i} = {b, c} := by
        obtain ⟨⟨a, a'⟩, haa⟩ := (ends i).exists_rep
        ext x
        simp only [mem_sources, degK, Finset.filter_singleton, Finset.mem_insert,
          Finset.mem_singleton]
        by_cases hx : x ∈ ends i
        · rw [if_pos hx, Finset.card_singleton]
          have hxbc : x = b ∨ x = c := by
            rw [← haa] at hx hb hc
            rw [Sym2.mem_iff] at hx hb hc
            rcases hx with rfl | rfl <;> rcases hb with rfl | rfl <;> rcases hc with rfl | rfl <;>
              tauto
          simp only [show Odd 1 from ⟨0, rfl⟩, true_iff]; tauto
        · rw [if_neg hx, Finset.card_empty]
          have hxbc : ¬ (x = b ∨ x = c) := by
            rintro (rfl | rfl)
            · exact hx hb
            · exact hx hc
          simp only [show ¬ Odd 0 from by decide, false_iff]; tauto
      rw [hsi]
      have hbc'' : ({b, c} : Finset V) = {b} ∆ {c} := by
        ext x
        simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_symmDiff]
        constructor
        · rintro (rfl | rfl)
          · left; exact ⟨rfl, fun h => hbc (by simpa using h)⟩
          · right; exact ⟨rfl, fun h => hbc (by simpa using h.symm)⟩
        · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> tauto
      rw [hbc'']
      rw [symmDiff_assoc, ← symmDiff_assoc ({b} : Finset V), symmDiff_self, bot_symmDiff]












theorem switching_card (ends : ι → Sym2 V) (m : Finset ι)
    (hnd : ∀ i ∈ m, ¬ (ends i).IsDiag) (A : Finset V) (hm : sources ends m = A)
    {u v : V} (huv : u ≠ v) :
    #(m.powerset.filter (fun K => sources ends K = A ∆ {u, v}))
      = (if connK ends m u v then
          #(m.powerset.filter (fun K => sources ends K = A)) else 0) := by
  by_cases hconn : connK ends m u v
  · rw [if_pos hconn]
    
    obtain ⟨P, hPm, hPsrc⟩ := exists_conn_set ends m hconn huv
    
    have hbij := sources_shift_bijOn ends m P hPm A
    rw [hPsrc] at hbij
    
    have : (m.powerset.filter (fun K => sources ends K = A ∆ {u, v}))
        = (m.powerset.filter (fun K => sources ends K = A)).image (fun K => K ∆ P) := by
      ext K
      simp only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_image]
      constructor
      · intro ⟨hKm, hKsrc⟩
        obtain ⟨L, hL, hLK⟩ := hbij.2.2 ⟨hKm, hKsrc⟩
        exact ⟨L, ⟨hL.1, hL.2⟩, hLK⟩
      · rintro ⟨L, ⟨hLm, hLsrc⟩, rfl⟩
        have := hbij.1 ⟨hLm, hLsrc⟩
        exact ⟨this.1, this.2⟩
    rw [this, Finset.card_image_of_injOn]
    intro K₁ hK₁ K₂ hK₂ h
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_powerset] at hK₁ hK₂
    exact hbij.2.1 ⟨hK₁.1, hK₁.2⟩ ⟨hK₂.1, hK₂.2⟩ h
  · rw [if_neg hconn]
    
    
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    rintro K hKpow hKsrc
    rw [Finset.mem_powerset] at hKpow
    set L := m \ K with hL
    have hLm : L ⊆ m := Finset.sdiff_subset
    
    have hLeq : L = m ∆ K := by
      rw [hL]
      ext x
      simp only [Finset.mem_sdiff, Finset.mem_symmDiff]
      constructor
      · rintro ⟨hm, hk⟩; left; exact ⟨hm, hk⟩
      · rintro (⟨hm, hk⟩ | ⟨hk, hm⟩)
        · exact ⟨hm, hk⟩
        · exact absurd (hKpow hk) hm
    have hLsrc : sources ends L = {u, v} := by
      rw [hLeq, sources_symmDiff, hm, hKsrc]
      
      rw [← symmDiff_assoc, symmDiff_self, bot_symmDiff]
    
    have hu_odd : Odd (degK ends L u) := by
      rw [← mem_sources, hLsrc]; simp
    have hbdry : ∀ x, Odd (degK ends L x) → x = u ∨ x = v := by
      intro x hx
      rw [← mem_sources, hLsrc] at hx
      simpa using hx
    have hconnL : connK ends L u v :=
      path_exists ends L (fun i hi => hnd i (hLm hi)) u v hu_odd hbdry huv
    
    have hmono : connK ends m u v := by
      have hstep : ∀ {a b}, adjStep ends L a b → adjStep ends m a b := by
        rintro a b ⟨i, hi, ha, hb, hne⟩; exact ⟨i, hLm hi, ha, hb, hne⟩
      exact Relation.ReflTransGen.mono (fun a b => hstep) hconnL
    exact hconn hmono











theorem switching_lemma (ends : ι → Sym2 V) (m : Finset ι)
    (hnd : ∀ i ∈ m, ¬ (ends i).IsDiag) (A : Finset V) (hm : sources ends m = A)
    {u v : V} (huv : u ≠ v) (F : Finset ι → ℝ) :
    ∑ _K ∈ m.powerset.filter (fun K => sources ends K = A ∆ {u, v}), F m
      = ∑ _K ∈ m.powerset.filter (fun K => sources ends K = A),
          F m * (if connK ends m u v then 1 else 0) := by
  rw [Finset.sum_const, Finset.sum_const]
  rw [switching_card ends m hnd A hm huv]
  by_cases hconn : connK ends m u v
  · simp [hconn]
  · simp [hconn]

end RandomCurrent

end Sharpness
end StatMech

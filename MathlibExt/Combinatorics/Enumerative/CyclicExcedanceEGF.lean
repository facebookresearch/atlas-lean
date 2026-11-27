/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.RingTheory.PowerSeries.Log
public import MathlibExt.Combinatorics.AssociatedStirlingEulerian

import Mathlib.Data.Nat.Choose.Sum
import Mathlib.GroupTheory.Perm.Cycle.Concrete

/-!
# Excedance generating function for cyclic permutations

We prove the exponential generating function for excedance-weighted single cycles.
Writing each cycle from its largest label gives a word on the remaining labels. Splitting
that word at its maximum yields a recurrence, which determines the derivative of the series.
-/

namespace MetaMathlibExt

open PowerSeries

namespace cyclicExcedanceEGF_eq

open Finset Equiv.Perm

private abbrev Word {α : Type*} [DecidableEq α] (s : Finset α) :=
  {l : List α // l.Nodup ∧ l.toFinset = s}

private noncomputable instance wordFintype {α : Type*} [DecidableEq α] (s : Finset α) :
    Fintype (Word s) :=
  Fintype.ofFinset (p := {l | l.Nodup ∧ l.toFinset = s}) s.toList.permutations.toFinset (by
    intro l
    simp only [List.mem_toFinset, List.mem_permutations]
    exact ⟨fun h ↦ ⟨h.nodup_iff.mpr s.nodup_toList, by ext b; simp [h.mem_iff]⟩,
      fun h ↦ List.perm_of_nodup_nodup_toFinset_eq h.1 s.nodup_toList (by simp [h.2])⟩)

private def edge {α : Type*} [LinearOrder α] (x : ℚ) (a b : α) : ℚ :=
  if a < b then x else 1

-- Multiply the weights along a path, with both endpoints specified.
private def path {α : Type*} [LinearOrder α] (x : ℚ) (a : α) (l : List α) (b : α) : ℚ :=
  match l with
  | [] => edge x a b
  | c :: cs => edge x a c * path x c cs b

private def weight {α : Type*} [LinearOrder α] (x : ℚ) : List α → ℚ
  | [] => 1
  | a :: l => x * (match l with
    | [] => 1
    | b :: bs => edge x a b * (List.zipWith (edge x) (b :: bs) bs).prod)

private lemma path_end_lt {α : Type*} [LinearOrder α] (x : ℚ) (a b : α) (l : List α)
    (ha : a < b) (hl : ∀ c ∈ l, c < b) :
    path x a l b = x * (List.zipWith (edge x) (a :: l) l).prod := by
  induction l generalizing a with
  | nil => simp [path, edge, ha]
  | cons c cs ih =>
    rw [path, ih c (hl _ (by simp)) (fun d hd ↦ hl _ (by simp [hd]))]
    simp only [List.zipWith_cons_cons, List.prod_cons]
    ring

private lemma weight_eq_path {α : Type*} [LinearOrder α] (x : ℚ) (a : α) (l : List α)
    (ha : ∀ c ∈ l, c < a) : weight x l = path x a l a := by
  cases l with
  | nil => simp [weight, path, edge]
  | cons c cs =>
    rw [path, path_end_lt x c a cs (ha _ (by simp)) (fun d hd ↦ ha _ (by simp [hd]))]
    have h := not_lt_of_gt (ha c (by simp))
    cases cs <;> simp [weight, edge, h]

private lemma weight_cons {α : Type*} [LinearOrder α] (x : ℚ) (a : α) (l : List α) :
    weight x (a :: l) = x * (List.zipWith (edge x) (a :: l) l).prod := by
  cases l <;> rfl

private lemma weight_append_max {α : Type*} [LinearOrder α] (x : ℚ)
    (a : α) (l r : List α) (hl : ∀ c ∈ l, c < a) (hr : ∀ c ∈ r, c < a) :
    weight x (l ++ a :: r) = weight x l * (if r = [] then x else 1) * weight x r := by
  cases l with
  | nil =>
    cases r with
    | nil => simp [weight]
    | cons d ds =>
      simp only [List.nil_append, weight_cons, List.cons_ne_nil, ite_false,
        List.zipWith_cons_cons, List.prod_cons]
      rw [show edge x a d = 1 by simp [edge, not_lt_of_gt (hr d (by simp))]]
      simp [weight]
  | cons c cs =>
    -- The edge into the maximum is an ascent and the edge out is not.
    have hzip : ∀ (b : α) (t : List α), b < a → (∀ d ∈ t, d < a) →
        (List.zipWith (edge x) (b :: (t ++ a :: r)) (t ++ a :: r)).prod =
          (List.zipWith (edge x) (b :: t) t).prod * x *
            (List.zipWith (edge x) (a :: r) r).prod := by
      intro b t
      induction t generalizing b with
      | nil => intro hb _; simp [edge, hb]
      | cons d ds ih =>
        intro _ ht
        simp only [List.cons_append, List.zipWith_cons_cons, List.prod_cons]
        rw [ih d (ht _ (by simp)) (fun e he ↦ ht _ (by simp [he]))]
        ring
    simp only [List.cons_append, weight_cons]
    rw [hzip c cs (hl _ (by simp)) (fun d hd ↦ hl _ (by simp [hd]))]
    cases r with
    | nil => simp [weight, mul_assoc]
    | cons d ds => simp [weight_cons, edge, not_lt_of_gt (hr d (by simp)), mul_assoc]


private noncomputable def wordSum {α : Type*} [LinearOrder α] (x : ℚ) (s : Finset α) : ℚ :=
  ∑ l : Word s, weight x l.val

private lemma word_nil_iff {α : Type*} [DecidableEq α] {s : Finset α} (l : Word s) :
    l.val = [] ↔ s = ∅ := by
  calc
    l.val = [] ↔ l.val.toFinset = ∅ := by simp
    _ ↔ s = ∅ := by rw [l.property.2]

private lemma wordSum_empty {α : Type*} [LinearOrder α] (x : ℚ) :
    wordSum x (∅ : Finset α) = 1 := by
  classical
  let : Unique (Word (∅ : Finset α)) :=
    ⟨⟨[], by simp⟩, fun l ↦ Subtype.ext ((word_nil_iff l).mpr rfl)⟩
  rw [wordSum, Fintype.sum_unique]
  rfl

private lemma mem_word {α : Type*} [DecidableEq α] {s : Finset α}
    (l : Word s) (b : α) : b ∈ l.val ↔ b ∈ s := by
  simpa only [l.property.2] using (List.mem_toFinset (l := l.val) (a := b)).symm

private def joinWord {α : Type*} [DecidableEq α] {s : Finset α} {a : α} (ha : a ∉ s) :
    (Σ t : s.powerset, Word t.val × Word (s \ t.val)) → Word (insert a s) := by
  rintro ⟨⟨t, ht⟩, l, r⟩
  have hts := mem_powerset.mp ht
  have hl : ∀ b, b ∈ l.val ↔ b ∈ t := fun b ↦ by
    exact mem_word l b
  have hr : ∀ b, b ∈ r.val ↔ b ∈ s \ t := fun b ↦ by
    exact mem_word r b
  refine ⟨l.val ++ a :: r.val, ?_, ?_⟩
  · rw [List.nodup_append']
    refine ⟨l.property.1, List.nodup_cons.mpr ⟨?_, r.property.1⟩, ?_⟩
    · simpa [hr] using fun h : a ∈ s ∧ a ∉ t ↦ ha h.1
    · intro b hb hbr
      have hbt := (hl b).mp hb
      rcases List.mem_cons.mp hbr with rfl | hbr
      · exact ha (hts hbt)
      · exact (mem_sdiff.mp ((hr b).mp hbr)).2 hbt
  · ext b
    simp only [List.mem_toFinset, List.mem_append, List.mem_cons, hl, hr, mem_sdiff, mem_insert]
    by_cases hbt : b ∈ t
    · simp [hbt, hts hbt]
    · simp [hbt]

private lemma joinWord_bijective {α : Type*} [DecidableEq α]
    {s : Finset α} {a : α} (ha : a ∉ s) : Function.Bijective (joinWord ha) := by
  constructor
  · rintro ⟨⟨t, ht⟩, l, r⟩ ⟨⟨u, hu⟩, l', r'⟩ h
    have hnl : a ∉ l.val := fun h ↦ ha (mem_powerset.mp ht
      ((mem_word l a).mp h))
    have hnr : a ∉ r.val := fun h ↦ ha (mem_sdiff.mp
      ((mem_word r a).mp h)).1
    have h' : l.val ++ a :: r.val = l'.val ++ a :: r'.val := congrArg Subtype.val h
    obtain ⟨hl, _, hr⟩ := (List.append_cons_inj_of_notMem hnl hnr).mp h'
    have htu : t = u := l.property.2.symm.trans ((congrArg List.toFinset hl).trans l'.property.2)
    subst u
    have hll' : l = l' := Subtype.ext hl
    have hrr' : r = r' := Subtype.ext hr
    subst l'
    subst r'
    rfl
  · intro w
    have haw : a ∈ w.val := by
      exact List.mem_toFinset.mp (w.property.2.symm ▸ mem_insert_self _ _)
    obtain ⟨l, r, hlr⟩ := List.append_of_mem haw
    have hn : (l ++ a :: r).Nodup := hlr ▸ w.property.1
    have hset : (l ++ a :: r).toFinset = insert a s := hlr ▸ w.property.2
    rcases List.nodup_append'.mp hn with ⟨hln, hrn, hd⟩
    have hlsub : l.toFinset ⊆ s := by
      intro b hb
      have hh : b ∈ insert a s := by
        rw [← hset]
        simp [List.mem_toFinset.mp hb]
      rcases mem_insert.mp hh with rfl | hbs
      · exact (hd (List.mem_toFinset.mp hb) (by simp)).elim
      · exact hbs
    have hrs : r.toFinset = s \ l.toFinset := by
      ext b
      have hbs : b ∈ s → b ∈ l ∨ b ∈ r := by
        intro hb
        have hb' : b ∈ (l ++ a :: r).toFinset := hset ▸ mem_insert_of_mem hb
        have hba : b ≠ a := fun h ↦ ha (h ▸ hb)
        simpa [hba] using hb'
      rw [mem_sdiff, List.mem_toFinset, List.mem_toFinset]
      constructor
      · intro hb
        have hh : b ∈ (l ++ a :: r).toFinset := by simp [hb]
        have hba : b ≠ a := fun h ↦ (List.nodup_cons.mp hrn).1 (h ▸ hb)
        exact ⟨(mem_insert.mp (hset ▸ hh)).resolve_left hba, fun h ↦ hd h (by simp [hb])⟩
      · rintro ⟨hb, hbl⟩
        exact (hbs hb).resolve_left hbl
    exact ⟨⟨⟨l.toFinset, mem_powerset.mpr hlsub⟩, ⟨l, hln, rfl⟩,
      ⟨r, (List.nodup_cons.mp hrn).2, hrs⟩⟩, Subtype.ext hlr.symm⟩

private lemma wordSum_insert_max {α : Type*} [LinearOrder α] (x : ℚ)
    (s : Finset α) (a : α) (ha : ∀ b ∈ s, b < a) :
    wordSum x (insert a s) =
      ∑ t ∈ s.powerset, wordSum x t * (if s \ t = ∅ then x else 1) *
        wordSum x (s \ t) := by
  classical
  have has : a ∉ s := fun h ↦ lt_irrefl _ (ha _ h)
  let e := Equiv.ofBijective (joinWord has) (joinWord_bijective has)
  rw [wordSum, ← Fintype.sum_equiv e _ _ (fun _ ↦ rfl), Fintype.sum_sigma]
  rw [← Finset.sum_attach s.powerset]
  change ∑ t ∈ s.powerset.attach, _ = _
  apply Finset.sum_congr rfl
  intro t _
  rw [Fintype.sum_prod_type]
  simp only [e, Equiv.ofBijective_apply]
  have hw (l : Word t.val) (r : Word (s \ t.val)) :
      weight x (joinWord has ⟨t, l, r⟩).val =
        weight x l.val * (if s \ t.val = ∅ then x else 1) * weight x r.val := by
    change weight x (l.val ++ a :: r.val) = _
    rw [weight_append_max, if_congr (word_nil_iff r) rfl rfl]
    · intro b hb
      exact ha b (mem_powerset.mp t.property (l.property.2 ▸ List.mem_toFinset.mpr hb))
    · intro b hb
      exact ha b (mem_sdiff.mp (r.property.2 ▸ List.mem_toFinset.mpr hb)).1
  simp only [hw, wordSum, ← Finset.mul_sum, ← Finset.sum_mul]


private noncomputable def wordPolynomial (x : ℚ) (n : ℕ) :=
  wordSum x (univ : Finset (Fin n))

private lemma weight_map {α β : Type*} [LinearOrder α] [LinearOrder β]
    (x : ℚ) (e : α ↪o β) (l : List α) : weight x (l.map e) = weight x l := by
  have hz (a : α) (l : List α) :
      (List.zipWith (edge x) (e a :: l.map e) (l.map e)).prod =
        (List.zipWith (edge x) (a :: l) l).prod := by
    induction l generalizing a with
    | nil => rfl
    | cons b bs ih =>
      simp only [List.map_cons, List.zipWith_cons_cons, List.prod_cons, ih]
      simp [edge, e.lt_iff_lt]
  cases l with
  | nil => rfl
  | cons a l => simp only [List.map_cons, weight_cons, hz]

private lemma wordSum_eq_wordPolynomial {α : Type*} [LinearOrder α] (x : ℚ) (s : Finset α) :
    wordSum x s = wordPolynomial x s.card := by
  let e := s.orderEmbOfFin rfl
  have he (b : α) : b ∈ s ↔ ∃ i, e i = b := by
    change b ∈ (s : Set α) ↔ b ∈ Set.range e
    rw [range_orderEmbOfFin]
  let mapWord : Word (univ : Finset (Fin s.card)) → Word s := fun l ↦
    ⟨l.val.map e, l.property.1.map e.injective, by
      ext b
      simp [List.mem_map, he b, mem_word]⟩
  have hmap : Function.Bijective mapWord := by
    constructor
    · intro l r h
      apply Subtype.ext
      exact List.map_injective_iff.mpr e.injective (congrArg Subtype.val h)
    · intro l
      have lift (a : α) (ha : a ∈ l.val) : ∃ i, e i = a := (he a).mp ((mem_word l a).mp ha)
      let w := l.val.pmap (fun a ha ↦ (lift a ha).choose) (fun _ h ↦ h)
      have hw : w.map e = l.val := by
        rw [List.map_pmap]
        have eq (a : α) (ha : a ∈ l.val) : e (lift a ha).choose = a :=
          (lift a ha).choose_spec
        have hfun : (fun a (h : a ∈ l.val) ↦ e (lift a h).choose) =
            (fun a _ ↦ a) := funext fun a ↦ funext (eq a)
        rw [hfun, List.pmap_eq_map (f := fun a ↦ a)]
        exact List.map_id _
      have hw' : w.toFinset = univ := by
        ext i
        have hei : e i ∈ l.val := (mem_word l _).mpr ((he _).mpr ⟨i, rfl⟩)
        rw [← hw, List.mem_map] at hei
        obtain ⟨j, hj, hij⟩ := hei
        simpa [e.injective hij] using hj
      exact ⟨⟨w, List.Nodup.of_map e (hw.symm ▸ l.property.1), hw'⟩, Subtype.ext hw⟩
  symm
  exact Fintype.sum_equiv (Equiv.ofBijective mapWord hmap) _ _ (fun l ↦ (weight_map x e l.val).symm)

private lemma wordPolynomial_zero (x : ℚ) : wordPolynomial x 0 = 1 := by
  have h : (univ : Finset (Fin 0)) = ∅ := by ext i; exact i.elim0
  rw [wordPolynomial, h, wordSum_empty]

private lemma wordPolynomial_succ (x : ℚ) (n : ℕ) :
    wordPolynomial x (n + 1) = ∑ k ∈ range (n + 1),
      (n.choose k : ℚ) * (wordPolynomial x k * (if n - k = 0 then x else 1) *
        wordPolynomial x (n - k)) := by
  classical
  let s := (univ : Finset (Fin (n + 1))).erase (Fin.last n)
  have hs : s.card = n := by simp [s]
  have huniv : insert (Fin.last n) s = univ := insert_erase (mem_univ _)
  have hmax (b : Fin (n + 1)) (hb : b ∈ s) : b < Fin.last n :=
    lt_of_le_of_ne (Fin.le_last b) (ne_of_mem_erase hb)
  rw [wordPolynomial, ← huniv, wordSum_insert_max x s (Fin.last n) hmax]
  simp only [wordSum_eq_wordPolynomial]
  have hsub (t : Finset (Fin (n + 1))) (ht : t ∈ s.powerset) :
      (s \ t).card = n - t.card := by rw [card_sdiff_of_subset (mem_powerset.mp ht), hs]
  calc
    _ = ∑ t ∈ s.powerset, wordPolynomial x t.card * (if n - t.card = 0 then x else 1) *
          wordPolynomial x (n - t.card) := by
      refine sum_congr rfl (fun t ht ↦ ?_)
      have he : s \ t = ∅ ↔ n - t.card = 0 := by
        calc
          _ ↔ (s \ t).card = 0 := card_eq_zero.symm
          _ ↔ _ := by rw [hsub t ht]
      rw [if_congr he rfl rfl, hsub t ht]
    _ = _ := by
      rw [sum_powerset_apply_card (fun k ↦
        wordPolynomial x k * (if n - k = 0 then x else 1) * wordPolynomial x (n - k)), hs]
      simp only [nsmul_eq_mul]


private abbrev FullCycles (n : ℕ) :=
  {w : Equiv.Perm (Fin n) // ∀ i j : Fin n, w.SameCycle i j}

private def cycleFromWord {n : ℕ} (l : Word (univ.erase (Fin.last n))) : FullCycles (n + 1) := by
  let a := Fin.last n
  have hn : (a :: l.val).Nodup := List.nodup_cons.mpr
    ⟨fun h ↦ notMem_erase _ _ ((mem_word l _).mp h), l.property.1⟩
  have hm (i : Fin (n + 1)) : i ∈ a :: l.val := by
    simp only [List.mem_cons, mem_word, mem_erase, mem_univ, and_true]
    exact eq_or_ne _ _
  exact ⟨(a :: l.val).formPerm, fun i j ↦ hn.isCycleOn_formPerm.2 (hm i) (hm j)⟩

private lemma cycleFromWord_bijective (n : ℕ) :
    Function.Bijective (cycleFromWord (n := n)) := by
  let a := Fin.last n
  cases n with
  | zero =>
    have h : (univ : Finset (Fin 1)).erase (Fin.last 0) = ∅ := by
      ext i
      simp [Subsingleton.elim i (Fin.last 0)]
    constructor
    · intro l r _
      exact Subtype.ext (((word_nil_iff l).2 h).trans ((word_nil_iff r).2 h).symm)
    · intro w
      refine ⟨⟨[], List.nodup_nil, (by simp)⟩, Subtype.ext (Equiv.ext ?_)⟩
      intro i
      exact (Subsingleton.elim (α := Fin 1) _ _)
  | succ n =>
    let a := Fin.last (n + 1)
    have hlen (l : Word (univ.erase a)) : 2 ≤ (a :: l.val).length := by
      have hb : (0 : Fin (n + 2)) ∈ l.val := (mem_word l _).mpr (by simp [a, Fin.ext_iff])
      have hpos := List.length_pos_of_mem hb
      simp only [List.length_cons]; omega
    have hnodup (l : Word (univ.erase a)) : (a :: l.val).Nodup :=
      List.nodup_cons.mpr ⟨fun h ↦ notMem_erase _ _ ((mem_word l _).mp h), l.property.1⟩
    constructor
    · intro l r h
      have hp : (a :: l.val).formPerm = (a :: r.val).formPerm := congrArg Subtype.val h
      have hl : ((a :: l.val).formPerm).toList a = a :: l.val :=
        toList_formPerm_nontrivial _ (hlen l) (hnodup l)
      have hr : ((a :: r.val).formPerm).toList a = a :: r.val :=
        toList_formPerm_nontrivial _ (hlen r) (hnodup r)
      rw [hp, hr] at hl
      exact Subtype.ext (List.cons.inj hl).2.symm
    · intro w
      obtain ⟨hc, hs⟩ := (sameCycle_all_iff_isCycle_support_eq_univ (by omega) w.val).mp w.property
      have ha : a ∈ w.val.support := by simp [hs]
      let L := w.val.toList a
      have hL (i : Fin (n + 2)) : i ∈ L := mem_toList_iff.mpr ⟨w.property a i, ha⟩
      have hhead : L = a :: L.tail := by
        have h := toList_getElem_zero _ _ ha
        cases hh : L with
        | nil => exact (by simpa [hh] using hL a : False).elim
        | cons b l =>
          have hab : b = a := by simpa [L, hh] using h
          simp [hab]
      have hn : (a :: L.tail).Nodup := hhead ▸ nodup_toList _ _
      have hfin : L.tail.toFinset = univ.erase a := by
        ext i
        rw [List.mem_toFinset, mem_erase]
        refine ⟨fun h ↦ ⟨fun hh ↦ (List.nodup_cons.mp hn).1 (hh ▸ h), mem_univ _⟩, ?_⟩
        intro hi
        have h := hL i
        rw [hhead, List.mem_cons] at h
        exact h.resolve_left hi.1
      refine ⟨⟨L.tail, (List.nodup_cons.mp hn).2, hfin⟩, Subtype.ext ?_⟩
      change (a :: L.tail).formPerm = w.val
      rw [← hhead, formPerm_toList, hc.cycleOf_eq (mem_support.mp ha)]

private lemma path_eq_prod {α : Type*} [LinearOrder α]
    (x : ℚ) (a b : α) (l : List α) (f : α → α)
    (h : ∀ (i : ℕ) (hi : i < (a :: l).length),
      f ((a :: l)[i]) = (l ++ [b])[i]'(by simpa using hi)) :
    path x a l b = ((a :: l).map (fun i ↦ edge x i (f i))).prod := by
  induction l generalizing a with
  | nil => simp [path, show f a = b from h 0 (by simp)]
  | cons c cs ih =>
    have h0 : f a = c := h 0 (by simp)
    have ht := ih c (fun i hi ↦ h (i + 1) (by simpa using hi))
    change edge x a c * path x c cs b =
      edge x a (f a) * ((c :: cs).map (fun i ↦ edge x i (f i))).prod
    rw [h0, ht]

private lemma cycleFromWord_weight {n : ℕ} (x : ℚ) (l : Word (univ.erase (Fin.last n))) :
    weight x l.val = x ^ excedanceCount (n + 1) (cycleFromWord l).val := by
  let a := Fin.last n
  let f := (a :: l.val).formPerm
  have hmax (c : Fin (n + 1)) (hc : c ∈ l.val) : c < a :=
    lt_of_le_of_ne (Fin.le_last c) (ne_of_mem_erase ((mem_word l _).mp hc))
  have hn : (a :: l.val).Nodup := List.nodup_cons.mpr
    ⟨fun h ↦ lt_irrefl _ (hmax _ h), l.property.1⟩
  have hset : (a :: l.val).toFinset = univ := by
    rw [List.toFinset_cons, l.property.2, insert_erase (mem_univ _)]
  rw [weight_eq_path x a l.val hmax, path_eq_prod x a a l.val f,
    ← List.prod_toFinset _ hn, hset]
  · change (∏ i : Fin (n + 1), edge x i (f i)) = x ^ excedanceCount (n + 1) f
    simp [edge, Finset.prod_ite, excedanceCount]
  · intro i hi
    by_cases hil : i < l.val.length
    · rw [List.formPerm_apply_lt_getElem _ hn _ (by simpa using hil),
        List.getElem_cons_succ, List.getElem_append_left hil]
    · have he : i = l.val.length := by simp only [List.length_cons] at hi; omega
      subst i
      rw [List.formPerm_apply_getElem_length, List.getElem_append_right (by omega)]
      simp

private lemma circular_sum_succ (x : ℚ) (n : ℕ) :
    (∑ m ∈ range (n + 2), (circularEulerian (n + 1) m : ℚ) * x ^ m) =
      wordPolynomial x n := by
  classical
  let s := univ.filter (fun w : Equiv.Perm (Fin (n + 1)) ↦ ∀ i j, w.SameCycle i j)
  have hcard (m : ℕ) : circularEulerian (n + 1) m =
      (s.filter (fun w ↦ excedanceCount (n + 1) w = m)).card := by
    simp [s, circularEulerian, Finset.filter_filter, and_comm]
  have hr (w : Equiv.Perm (Fin (n + 1))) : excedanceCount (n + 1) w ≤ n + 1 := by
    simpa [excedanceCount] using
      (card_filter_le (s := (univ : Finset (Fin (n + 1)))) (p := fun i ↦ i < w i))
  calc
    _ = ∑ m ∈ range (n + 2), ∑ w ∈ s with excedanceCount (n + 1) w = m,
          x ^ excedanceCount (n + 1) w := by
      refine sum_congr rfl (fun m _ ↦ ?_)
      rw [hcard, ← nsmul_eq_mul, ← sum_const]
      exact sum_congr rfl (fun w hw ↦ by rw [(mem_filter.mp hw).2])
    _ = ∑ w ∈ s, x ^ excedanceCount (n + 1) w :=
      sum_fiberwise_of_maps_to (fun w _ ↦ mem_range.mpr (Nat.lt_succ_of_le (hr w))) _
    _ = ∑ w : FullCycles (n + 1), x ^ excedanceCount (n + 1) w.val := by
      apply Finset.sum_subtype
      simp [s]
    _ = wordSum x (univ.erase (Fin.last n)) := by
      symm
      exact Fintype.sum_equiv (Equiv.ofBijective _ (cycleFromWord_bijective n)) _ _
        (cycleFromWord_weight x)
    _ = wordPolynomial x n := by rw [wordSum_eq_wordPolynomial]; simp


private noncomputable def wordSeries (x : ℚ) : ℚ⟦X⟧ :=
  PowerSeries.mk (fun n ↦ wordPolynomial x n / (n.factorial : ℚ))

private lemma constantCoeff_wordSeries (x : ℚ) : constantCoeff (wordSeries x) = 1 := by
  simp [wordSeries, wordPolynomial_zero]

private lemma coeff_wordSeries_add (x : ℚ) (n : ℕ) :
    coeff n (wordSeries x + C (x - 1)) =
      (if n = 0 then x else 1) * wordPolynomial x n / (n.factorial : ℚ) := by
  cases n <;> simp [wordSeries, wordPolynomial_zero]

private lemma div_factorial_succ_mul (a : ℚ) (n : ℕ) :
    a / ((n + 1).factorial : ℚ) * (n + 1 : ℚ) = a / (n.factorial : ℚ) := by
  rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_succ]
  have hn : (n : ℚ) + 1 ≠ 0 := by positivity
  field_simp

private lemma derivative_wordSeries (x : ℚ) :
    d⁄dX (wordSeries x) = wordSeries x * (wordSeries x + C (x - 1)) := by
  ext n
  rw [coeff_derivative, wordSeries, coeff_mk, div_factorial_succ_mul, ← wordSeries,
    coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, wordPolynomial_succ,
    div_eq_mul_inv, Finset.sum_mul]
  refine sum_congr rfl fun k hk ↦ ?_
  have hkn := Nat.le_of_lt_succ (mem_range.mp hk)
  have hfac : (n.choose k : ℚ) * (k.factorial : ℚ) * ((n - k).factorial : ℚ) =
      (n.factorial : ℚ) := by exact_mod_cast Nat.choose_mul_factorial_mul_factorial hkn
  rw [coeff_wordSeries_add, wordSeries, coeff_mk, ← hfac]
  have hkf : (k.factorial : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hnkf : ((n - k).factorial : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hchoose : (n.choose k : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.choose_ne_zero hkn)
  field_simp

private noncomputable def cycleSeries (x : ℚ) : ℚ⟦X⟧ :=
  PowerSeries.mk (fun n ↦ if n = 0 then 0 else
    (∑ m ∈ Finset.range (n + 1), (circularEulerian n m : ℚ) * x ^ m) / (n.factorial : ℚ))

private lemma derivative_cycleSeries (x : ℚ) : d⁄dX (cycleSeries x) = wordSeries x := by
  ext n
  rw [coeff_derivative, cycleSeries, wordSeries, coeff_mk, coeff_mk, ite_eq_right (by omega),
    circular_sum_succ, div_factorial_succ_mul]

private lemma derivative_rescale_exp (x : ℚ) :
    d⁄dX (rescale x (exp ℚ)) = C x * rescale x (exp ℚ) := by
  ext n
  rw [coeff_derivative, coeff_C_mul, coeff_rescale, coeff_rescale, coeff_exp, coeff_exp,
    Nat.factorial_succ, Nat.cast_mul, Nat.cast_succ, pow_succ]
  have hn : (n.factorial : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hn' : (n : ℚ) + 1 ≠ 0 := by positivity
  simp only [show algebraMap ℚ ℚ = RingHom.id ℚ from rfl, RingHom.id_apply]
  field_simp

private lemma derivative_logOf_mul {f : ℚ⟦X⟧} (hf : constantCoeff f = 1) :
    d⁄dX (logOf f) * f = d⁄dX f := by
  have hsub : HasSubst (f - 1) := .of_constantCoeff_zero' (by simp [hf])
  let subst := substAlgHom hsub (R := ℚ)
  have hm : (d⁄dX (log ℚ)).subst (f - 1) * f = 1 := by
    have h := congrArg subst (derivative_log_mul_one_add_X (A := ℚ))
    change subst (_ * _) = subst 1 at h
    rw [map_mul, map_one, map_add, map_one] at h
    simpa only [subst, coe_substAlgHom, subst_X hsub, add_sub_cancel] using h
  rw [logOf_eq, derivative_subst hsub, map_sub, derivative_one, sub_zero,
    mul_right_comm, hm, one_mul]

private lemma unique_of_derivative (x : ℚ) {f g : ℚ⟦X⟧}
    (hf : d⁄dX f = f * (f + C (x - 1))) (hg : d⁄dX g = g * (g + C (x - 1)))
    (hc : constantCoeff f = constantCoeff g) : f = g := by
  ext n
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    cases n with
    | zero => simpa only [coeff_zero_eq_constantCoeff_apply] using hc
    | succ n =>
      have hcoeff : coeff n (f * (f + C (x - 1))) = coeff n (g * (g + C (x - 1))) := by
        rw [coeff_mul, coeff_mul]
        refine Finset.sum_congr rfl (fun ij hij ↦ ?_)
        have h := Finset.mem_antidiagonal.mp hij
        simp only [map_add, ih ij.1 (by omega), ih ij.2 (by omega)]
      rw [← hf, ← hg, coeff_derivative, coeff_derivative] at hcoeff
      exact (mul_right_cancel₀ (by positivity : (n + 1 : ℚ) ≠ 0) hcoeff)

private lemma derivative_logarithmic_series (x : ℚ) (hx : x ≠ 1) :
    let f := X + logOf (C (x - 1) * (C x * exp ℚ - rescale x (exp ℚ))⁻¹)
    constantCoeff f = 0 ∧
      constantCoeff (d⁄dX f) = 1 ∧
      d⁄dX (d⁄dX f) = d⁄dX f * (d⁄dX f + C (x - 1)) := by
  let E := rescale x (exp ℚ)
  let D := C x * exp ℚ - E
  let U := C (x - 1) * D⁻¹
  let R := E * U
  change constantCoeff (X + logOf U) = 0 ∧ _ ∧ _
  have hE : constantCoeff E = 1 := by
    simp [E, ← coeff_zero_eq_constantCoeff_apply, coeff_rescale]
  have hD : constantCoeff D = x - 1 := by simp [D, hE, constantCoeff_exp]
  have hd : D * D⁻¹ = 1 := PowerSeries.mul_inv_cancel _ (by rwa [hD, sub_ne_zero])
  have hU : constantCoeff U = 1 := by
    simp [U, constantCoeff_inv, hD, sub_ne_zero.mpr hx]
  have dE : d⁄dX E = C x * E := derivative_rescale_exp x
  have dD : d⁄dX D = D - C (x - 1) * E := by
    simp only [D, map_sub, Derivation.leibniz, derivative_C, smul_eq_mul, derivative_exp,
      dE, map_one]
    ring
  have dU : d⁄dX U = U * (R - 1) := by
    have key : D⁻¹ ^ 2 * D = D⁻¹ := by
      calc
        _ = D⁻¹ * (D * D⁻¹) := by ring
        _ = _ := by rw [hd, mul_one]
    simp only [U, R, Derivation.leibniz, derivative_C, smul_eq_mul,
      derivative_inv', dD]
    rw [mul_sub, neg_mul, neg_mul, key]
    ring
  have hderiv : d⁄dX (X + logOf U) = R := by
    rw [map_add, derivative_X]
    have hc : U ≠ 0 := by
      intro h
      simp [h] at hU
    apply mul_right_cancel₀ hc
    rw [add_mul, one_mul, derivative_logOf_mul hU, dU]
    ring
  change constantCoeff (X + logOf U) = 0 ∧ constantCoeff (d⁄dX (X + logOf U)) = 1 ∧ _
  rw [hderiv]
  refine ⟨by simp [constantCoeff_logOf hU], by simp [R, hE, hU], ?_⟩
  simp only [R, Derivation.leibniz, smul_eq_mul, dE, dU, map_sub, map_one]
  ring

end cyclicExcedanceEGF_eq

open cyclicExcedanceEGF_eq in
/-- **Exponential generating function of excedances over cyclic permutations.** Let $x \ne 1$ be
a rational number. For $n \ge 1$ let $C_n(x) = \sum_{m=0}^{n} C_{n,m} x^m$, where the circular
Eulerian number $C_{n,m}$ is the number of permutations $w$ of $\{0, 1, \dots, n-1\}$ whose points
all lie in a single cycle and which have exactly $m$ excedances, that is, points $i$ with
$w(i) > i$. Then, as formal power series in $z$ over $\mathbb{Q}$,
$$\sum_{n \ge 1} C_n(x) \frac{z^n}{n!} = z + \log \frac{x - 1}{x e^z - e^{xz}},$$
where the quotient has constant term $1$ and $\log$ is the formal logarithm of a power series
with constant term $1$.

Source: Pasquale Petrullo and Domenico Senato, *Generalized Eulerian Polynomials with a
Nonnegative Gamma Vector*, Journal of Integer Sequences 27 (2024), Article 24.1.5, Proposition 1
(`jis-2024-24.1.5-prop-1`). -/
public theorem cyclicExcedanceEGF_eq (x : ℚ) (hx : x ≠ 1) :
    PowerSeries.mk (fun n ↦ if n = 0 then 0 else
        (∑ m ∈ Finset.range (n + 1), (circularEulerian n m : ℚ) * x ^ m) / (n.factorial : ℚ)) =
      X + logOf (C (x - 1) * (C x * exp ℚ - rescale x (exp ℚ))⁻¹) := by
  change cycleSeries x = _
  obtain ⟨hc, hc', hd⟩ := derivative_logarithmic_series x hx
  apply derivative.ext
  · rw [derivative_cycleSeries]
    exact unique_of_derivative x (derivative_wordSeries x) hd
      ((constantCoeff_wordSeries x).trans hc'.symm)
  · rw [hc]
    simp [cycleSeries]

end MetaMathlibExt

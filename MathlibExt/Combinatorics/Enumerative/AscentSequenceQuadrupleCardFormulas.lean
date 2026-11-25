/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Data.Set.Card
public import MathlibExt.Combinatorics.Enumerative.AscentSequenceQuadruplePatterns
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.List.GetD
import Mathlib.Data.Set.Finite.List
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Sum formulas for two families of weak ascent sequences

Let $W_n$ be the set of weak ascent sequences of length $n$ avoiding $011$, $100$, $201$ and
$210$. The main result, `quadrupleUSet_quadrupleVSet_card_formulas`, gives the sum formulas of
Callan and Mansour for the numbers of elements of the subsets $U_{n,1}$ and $V_{n,1}$ of $W_n$.

The proof first counts the words of $W_N$ with $k$ descents. Such a word is a block of leading
zeros followed by entries whose descents are isolated. Inserting the value $1$ as a skipped
value, as the first entry after the zeros, as the first descent bottom, or as the first descent
top gives Pascal-type recurrences, so the count is
$\binom{N-1-k}{2k} 2^{N-1-3k} + \binom{N-1-k}{2k-1} 2^{N-3k}$ for $k \ge 1$, and $2^{N-1}$ for
$k = 0$. A word of $U_{n,1}$ is $0\,v\,(c+1)\,c$ with $v \in W_{n-3}$ having a descent and
$c$ the number of weak ascents of $0\,v$; a word of $V_{n,1}$ is $0^s\,v\,(c+1)\,c\,(c+1+j)$
with $v \in W_{n-3-s}$ and $1 \le j \le s$, with $j < s$ when $v$ has no descent. Summing over
the number of descents and the largest entry before the last descent gives the formulas.
-/

namespace MetaMathlibExt

namespace quadrupleUSet_quadrupleVSet_card_formulas

open List

local notation "WA" => weakAscentAvoiders
  ({[0, 1, 1], [1, 0, 0], [2, 0, 1], [2, 1, 0]} : Finset (List ℕ))

/-- A triple `a, b, c` is an occurrence of `011`, or of one of `100`, `201`, `210`. -/
private def Bad (a b c : ℕ) : Prop := (a < b ∧ b = c) ∨ (b < a ∧ c < a)

private def Avoid (w : List ℕ) : Prop := ∀ ⦃a b c : ℕ⦄, [a, b, c] <+ w → ¬ Bad a b c

private theorem contains_triple {w : List ℕ} {x y z : ℕ} :
    ContainsPattern w [x, y, z] ↔ ∃ a b c, [a, b, c] <+ w ∧
      ((a < b ↔ x < y) ∧ (b < a ↔ y < x) ∧ (a < c ↔ x < z) ∧ (c < a ↔ z < x) ∧
        (b < c ↔ y < z) ∧ (c < b ↔ z < y)) := by
  constructor
  · rintro ⟨s, hs, hl, ho⟩
    obtain ⟨a, b, c, rfl⟩ : ∃ a b c, s = [a, b, c] := List.length_eq_three.mp hl
    refine ⟨a, b, c, hs, ?_⟩
    simp only [length_cons, length_nil, Nat.forall_lt_succ_left] at ho
    simpa [List.getD, and_assoc, and_left_comm, and_comm] using ho
  · rintro ⟨a, b, c, hs, ho⟩
    refine ⟨[a, b, c], hs, rfl, ?_⟩
    simp only [length_cons, length_nil, Nat.forall_lt_succ_left]
    simpa [List.getD, and_assoc, and_left_comm, and_comm] using ho

private theorem avoid_iff (w : List ℕ) :
    (∀ p ∈ ({[0, 1, 1], [1, 0, 0], [2, 0, 1], [2, 1, 0]} : Finset (List ℕ)),
      ¬ ContainsPattern w p) ↔ Avoid w := by
  simp only [Finset.mem_insert, Finset.mem_singleton, forall_eq_or_imp, forall_eq,
    contains_triple, Avoid, Bad]
  constructor
  · rintro ⟨h1, h2, h3, h4⟩ a b c hs hbad
    rcases hbad with ⟨hab, rfl⟩ | ⟨hba, hca⟩
    · exact h1 ⟨a, b, b, hs, by omega⟩
    · rcases lt_trichotomy b c with hbc | rfl | hbc
      · exact h3 ⟨a, b, c, hs, by omega⟩
      · exact h2 ⟨a, b, b, hs, by omega⟩
      · exact h4 ⟨a, b, c, hs, by omega⟩
  · intro h
    refine ⟨?_, ?_, ?_, ?_⟩ <;> rintro ⟨a, b, c, hs, ho⟩ <;> exact h hs (by omega)

private theorem mem_WA_iff {w : List ℕ} {n : ℕ} :
    w ∈ WA n ↔ w.length = n ∧ IsWeakAscentSeq w ∧ Avoid w := by
  simp only [weakAscentAvoiders, Set.mem_ofPred_eq, avoid_iff]


local notation "wasc" => wordWeakAscents

/-- Number of descents of a word. -/
private def desc : List ℕ → ℕ
  | [] => 0
  | [_] => 0
  | a :: b :: t => (if b < a then 1 else 0) + desc (b :: t)

private theorem wasc_cons_cons (a b : ℕ) (t : List ℕ) :
    wasc (a :: b :: t) = (if a ≤ b then 1 else 0) + wasc (b :: t) := rfl

private theorem desc_cons_cons (a b : ℕ) (t : List ℕ) :
    desc (a :: b :: t) = (if b < a then 1 else 0) + desc (b :: t) := rfl

private theorem wasc_add_desc : ∀ l : List ℕ, wasc l + desc l = l.length - 1
  | [] => rfl
  | [_] => rfl
  | a :: b :: t => by
    rw [wasc_cons_cons, desc_cons_cons]
    have := wasc_add_desc (b :: t)
    simp only [length_cons] at this ⊢
    split_ifs <;> omega

private theorem wasc_cons_of_le {a : ℕ} {l : List ℕ} (hl : l ≠ []) (h : a ≤ l.head hl) :
    wasc (a :: l) = wasc l + 1 := by
  obtain ⟨b, t, rfl⟩ := List.exists_cons_of_ne_nil hl
  simp only [head_cons] at h
  rw [wasc_cons_cons, ite_eq_left h]; omega

private theorem desc_cons_of_le {a : ℕ} {l : List ℕ} (hl : l ≠ []) (h : a ≤ l.head hl) :
    desc (a :: l) = desc l := by
  obtain ⟨b, t, rfl⟩ := List.exists_cons_of_ne_nil hl
  simp only [head_cons] at h
  rw [desc_cons_cons, ite_eq_right (by omega)]; omega

private theorem wasc_zero_cons {l : List ℕ} (hl : l ≠ []) : wasc (0 :: l) = wasc l + 1 :=
  wasc_cons_of_le hl (Nat.zero_le _)

private theorem desc_zero_cons (l : List ℕ) : desc (0 :: l) = desc l := by
  cases l with
  | nil => rfl
  | cons b t => exact desc_cons_of_le (by simp) (Nat.zero_le _)

private theorem wasc_append_pair : ∀ (l : List ℕ) (y x : ℕ),
    wasc (l ++ [y, x]) = wasc (l ++ [y]) + if y ≤ x then 1 else 0
  | [], y, x => by simp [wordWeakAscents]
  | [a], y, x => by simp [wordWeakAscents]
  | a :: b :: t, y, x => by
    have ih := wasc_append_pair (b :: t) y x
    simp only [cons_append] at ih ⊢
    rw [wasc_cons_cons, wasc_cons_cons, ih]
    omega

private theorem desc_append_pair : ∀ (l : List ℕ) (y x : ℕ),
    desc (l ++ [y, x]) = desc (l ++ [y]) + if x < y then 1 else 0
  | [], y, x => by simp [desc]
  | [a], y, x => by simp [desc]
  | a :: b :: t, y, x => by
    have ih := desc_append_pair (b :: t) y x
    simp only [cons_append] at ih ⊢
    rw [desc_cons_cons, desc_cons_cons, ih]
    omega

/-- `f` preserves the order between any two entries of `l`. -/
private def OrdOn (f : ℕ → ℕ) (l : List ℕ) : Prop := ∀ a ∈ l, ∀ b ∈ l, (f a ≤ f b ↔ a ≤ b)

private theorem OrdOn.mono {f : ℕ → ℕ} {l l' : List ℕ} (h : OrdOn f l) (hs : l' ⊆ l) :
    OrdOn f l' := fun a ha b hb => h a (hs ha) b (hs hb)

private theorem OrdOn.lt_iff {f : ℕ → ℕ} {l : List ℕ} (h : OrdOn f l) {a b : ℕ} (ha : a ∈ l)
    (hb : b ∈ l) : f a < f b ↔ a < b := by
  rw [← not_le, ← not_le, h b hb a ha]

private theorem OrdOn.eq_iff {f : ℕ → ℕ} {l : List ℕ} (h : OrdOn f l) {a b : ℕ} (ha : a ∈ l)
    (hb : b ∈ l) : f a = f b ↔ a = b := by
  rw [le_antisymm_iff, le_antisymm_iff, h a ha b hb, h b hb a ha]

private theorem ordOn_of_strictMono {f : ℕ → ℕ} (hf : StrictMono f) (l : List ℕ) :
    OrdOn f l :=
  fun _ _ _ _ => hf.le_iff_le

private theorem wasc_map {f : ℕ → ℕ} : ∀ {l : List ℕ}, OrdOn f l → wasc (l.map f) = wasc l
  | [], _ => rfl
  | [_], _ => rfl
  | a :: b :: t, h => by
    have ih := wasc_map (l := b :: t) (h.mono (List.subset_cons_self _ _))
    simp only [map_cons] at ih ⊢
    rw [wasc_cons_cons, wasc_cons_cons, ih]
    simp only [h a (by simp) b (by simp)]

private theorem desc_map {f : ℕ → ℕ} : ∀ {l : List ℕ}, OrdOn f l → desc (l.map f) = desc l
  | [], _ => rfl
  | [_], _ => rfl
  | a :: b :: t, h => by
    have ih := desc_map (l := b :: t) (h.mono (List.subset_cons_self _ _))
    simp only [map_cons] at ih ⊢
    rw [desc_cons_cons, desc_cons_cons, ih]
    simp only [h.lt_iff (by simp : b ∈ a :: b :: t) (by simp : a ∈ a :: b :: t)]

private theorem bad_map {f : ℕ → ℕ} {l : List ℕ} (h : OrdOn f l) {a b c : ℕ} (ha : a ∈ l)
    (hb : b ∈ l) (hc : c ∈ l) : Bad (f a) (f b) (f c) ↔ Bad a b c := by
  unfold Bad
  rw [h.lt_iff ha hb, h.eq_iff hb hc, h.lt_iff hb ha, h.lt_iff hc ha]

private theorem avoid_map {f : ℕ → ℕ} {l : List ℕ} (h : OrdOn f l) :
    Avoid (l.map f) ↔ Avoid l := by
  constructor
  · intro hav a b c hs hbad
    have hs' : [f a, f b, f c] <+ l.map f := by simpa using hs.map f
    exact hav hs' ((bad_map h (hs.subset (by simp)) (hs.subset (by simp))
      (hs.subset (by simp))).mpr hbad)
  · intro hav a' b' c' hs hbad
    obtain ⟨l', hl', he⟩ := List.sublist_map_iff.mp hs
    obtain ⟨a, b, c, rfl⟩ : ∃ a b c, l' = [a, b, c] := by
      have : l'.length = 3 := by simpa using (congrArg List.length he).symm
      exact List.length_eq_three.mp this
    simp only [map_cons, map_nil, cons.injEq, and_true] at he
    obtain ⟨rfl, rfl, rfl⟩ := he
    exact hav hl' ((bad_map h (hl'.subset (by simp)) (hl'.subset (by simp))
      (hl'.subset (by simp))).mp hbad)

private theorem Avoid.sublist {u w : List ℕ} (h : Avoid w) (hs : u <+ w) : Avoid u :=
  fun _ _ _ ht => h (ht.trans hs)

/-- Recursive form of the weak ascent bound for the entries of `t`, read after an entry `p`:
the first entry of `t` is at most `b`, and the bound grows by one after each weak ascent. -/
private def BoundR : ℕ → ℕ → List ℕ → Prop
  | _, _, [] => True
  | b, p, x :: t => x ≤ b ∧ BoundR (b + if p ≤ x then 1 else 0) x t

private theorem boundR_iff : ∀ (b p : ℕ) (t : List ℕ),
    BoundR b p t ↔ ∀ j (h : j < t.length), t[j] ≤ b + wasc (p :: t.take j)
  | b, p, [] => by simp [BoundR]
  | b, p, x :: t => by
    rw [BoundR, boundR_iff]
    constructor
    · rintro ⟨hx, ht⟩ j hj
      cases j with
      | zero => simpa [wordWeakAscents] using hx
      | succ j =>
        have := ht j (by simpa using hj)
        simp only [getElem_cons_succ, take_succ_cons, wasc_cons_cons]
        omega
    · intro h
      refine ⟨by have := h 0 (by simp); simpa [wordWeakAscents] using this, fun j hj => ?_⟩
      have := h (j + 1) (by simpa using hj)
      simp only [getElem_cons_succ, take_succ_cons, wasc_cons_cons] at this
      omega

private theorem iwas_zero_cons_iff (t : List ℕ) :
    IsWeakAscentSeq (0 :: t) ↔ BoundR 1 0 t := by
  rw [boundR_iff]
  unfold IsWeakAscentSeq
  constructor
  · rintro ⟨-, h⟩ j hj
    have := h (j + 1) (by simpa using hj)
    simpa [take_succ_cons, Nat.add_comm] using this
  · intro h
    refine ⟨fun _ => rfl, fun i hi => ?_⟩
    cases i with
    | zero => simp
    | succ j =>
      have := h j (by simpa using hi)
      simpa [take_succ_cons, Nat.add_comm] using this

private theorem boundR_replicate_zero (m b : ℕ) (t : List ℕ) :
    BoundR b 0 (replicate m 0 ++ t) ↔ BoundR (b + m) 0 t := by
  induction m generalizing b with
  | zero => simp
  | succ m ih =>
    rw [replicate_succ, cons_append, BoundR, ih]
    simp only [zero_le, true_and, ite_true]
    rw [Nat.add_assoc, Nat.add_comm 1 m]

private theorem sublist_zero_cons_of_replicate {m : ℕ} (hm : 1 ≤ m) (r : List ℕ) :
    0 :: r <+ replicate m 0 ++ r := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hm
  rw [Nat.add_comm, replicate_succ, cons_append]
  exact (List.sublist_append_right _ r).cons_cons 0

private theorem avoid_replicate_zero {m : ℕ} (hm : 1 ≤ m) (r : List ℕ) :
    Avoid (replicate m 0 ++ r) ↔ Avoid (0 :: r) := by
  refine ⟨fun h => h.sublist (sublist_zero_cons_of_replicate hm r), fun h => ?_⟩
  intro a b c hs hbad
  obtain ⟨l₁, l₂, he, h₁, h₂⟩ := List.sublist_append_iff.mp hs
  have hz : ∀ x ∈ l₁, x = 0 := fun x hx => List.eq_of_mem_replicate (h₁.subset hx)
  match l₁, he, hz with
  | [], he, _ =>
    simp only [nil_append] at he
    subst he
    exact h (h₂.cons 0) hbad
  | [x], he, hz =>
    simp only [singleton_append, cons.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    have ha : a = 0 := hz a (by simp)
    subst ha
    exact h (h₂.cons_cons 0) hbad
  | [x, y], he, hz =>
    simp only [cons_append, cons.injEq] at he
    obtain ⟨rfl, rfl, -⟩ := he
    have ha : a = 0 := hz a (by simp)
    have hb : b = 0 := hz b (by simp)
    subst ha hb
    simp [Bad] at hbad
  | [x, y, z], he, hz =>
    simp only [cons_append, nil_append, cons.injEq] at he
    obtain ⟨rfl, rfl, rfl, -⟩ := he
    have ha : a = 0 := hz a (by simp)
    have hb : b = 0 := hz b (by simp)
    subst ha hb
    simp [Bad] at hbad
  | _ :: _ :: _ :: _ :: _, he, _ => simp at he

/-- Membership in `W` of a word with `m ≥ 1` leading zeros. -/
private theorem replicate_append_mem_iff {m : ℕ} (hm : 1 ≤ m) (r : List ℕ) :
    replicate m 0 ++ r ∈ WA (m + r.length) ↔ BoundR m 0 r ∧ Avoid (0 :: r) := by
  rw [mem_WA_iff, avoid_replicate_zero hm]
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hm
  rw [Nat.add_comm 1 m, replicate_succ, cons_append, iwas_zero_cons_iff,
    boundR_replicate_zero, Nat.add_comm 1 m]
  have hlen : (0 :: (replicate m 0 ++ r)).length = m + 1 + r.length := by simp; omega
  simp only [hlen, true_and]

private theorem pair_sublist_cons_iff {x b c : ℕ} {L : List ℕ} :
    [b, c] <+ x :: L ↔ [b, c] <+ L ∨ (b = x ∧ c ∈ L) := by
  rw [List.sublist_cons_iff]
  constructor
  · rintro (h | ⟨r, he, hr⟩)
    · exact Or.inl h
    · simp only [cons.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      exact Or.inr ⟨rfl, List.singleton_sublist.mp hr⟩
  · rintro (h | ⟨rfl, hc⟩)
    · exact Or.inl h
    · exact Or.inr ⟨[c], rfl, List.singleton_sublist.mpr hc⟩

private theorem avoid_cons_iff (x : ℕ) (L : List ℕ) :
    Avoid (x :: L) ↔ Avoid L ∧ ∀ ⦃b c : ℕ⦄, [b, c] <+ L → ¬ Bad x b c := by
  constructor
  · intro h
    exact ⟨h.sublist (List.sublist_cons_self x L), fun b c hs => h (hs.cons_cons x)⟩
  · rintro ⟨hL, hx⟩ a b c hs
    rcases List.sublist_cons_iff.mp hs with h | ⟨r, he, hr⟩
    · exact hL h
    · simp only [cons.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      exact hx hr

/-- In a word of `W` that starts with zeros followed by a positive entry, all entries after the
zeros are distinct. -/
private theorem nodup_of_avoid {r : List ℕ} (hav : Avoid (0 :: r))
    (hhead : ∀ h : r ≠ [], r.head h ≠ 0) : r.Nodup := by
  rw [List.nodup_iff_sublist]
  intro y hy
  rcases Nat.eq_zero_or_pos y with rfl | hpos
  · obtain ⟨h, t, rfl⟩ : ∃ h t, r = h :: t := by
      cases r with
      | nil => simp at hy
      | cons h t => exact ⟨h, t, rfl⟩
    have hh : h ≠ 0 := hhead (by simp)
    have ht : [0, 0] <+ t := by
      rcases List.sublist_cons_iff.mp hy with h' | ⟨r', he, hr'⟩
      · exact h'
      · simp only [cons.injEq] at he
        exact absurd he.1.symm hh
    exact hav ((ht.cons_cons h).cons 0) (Or.inr ⟨by omega, by omega⟩)
  · exact hav (hy.cons_cons 0) (Or.inl ⟨hpos, rfl⟩)

/-- Bad triples with a first entry `0` are exactly repeated positive entries. -/
private theorem bad_zero_iff (b c : ℕ) : Bad 0 b c ↔ 0 < b ∧ b = c := by
  simp [Bad]

private theorem avoid_zero_cons_of_nodup {L : List ℕ} (hL : Avoid L) (hn : L.Nodup) :
    Avoid (0 :: L) := by
  rw [avoid_cons_iff]
  refine ⟨hL, fun b c hs hbad => ?_⟩
  rw [bad_zero_iff] at hbad
  obtain ⟨-, rfl⟩ := hbad
  exact List.nodup_iff_sublist.mp hn b hs

/-- Transfer of the weak ascent bound along a map preserving the order of the entries. -/
private theorem boundR_map {f : ℕ → ℕ} {b b' : ℕ} :
    ∀ {L : List ℕ} {p p' c : ℕ}, OrdOn f L →
      (∀ h : L ≠ [], (p ≤ L.head h ↔ p' ≤ f (L.head h))) →
      (∀ x ∈ L, ∀ c, x ≤ b + c → f x ≤ b' + c) →
      BoundR (b + c) p L → BoundR (b' + c) p' (L.map f)
  | [], _, _, _, _, _, _, _ => trivial
  | x :: t, p, p', c, hord, hhead, hbd, ⟨hx, ht⟩ => by
    have hpx : (p ≤ x ↔ p' ≤ f x) := hhead (by simp)
    refine ⟨hbd x (by simp) c hx, ?_⟩
    have key : (if p' ≤ f x then 1 else 0) = (if p ≤ x then 1 else 0) := by
      simp only [hpx]
    rw [key, Nat.add_assoc]
    rw [Nat.add_assoc] at ht
    refine boundR_map (hord.mono (List.subset_cons_self _ _)) ?_
      (fun y hy => hbd y (List.mem_cons_of_mem _ hy)) ht
    intro h
    exact (hord x (by simp) _ (List.mem_cons_of_mem _ (List.head_mem h))).symm

private def inc (u : ℕ) : ℕ := if u = 0 then 0 else u + 1

private theorem inc_strictMono : StrictMono inc := by
  intro a b hab
  unfold inc
  split_ifs <;> omega

private theorem ordOn_pred_of_not_one {l : List ℕ} (h : 1 ∉ l) : OrdOn (· - 1) l := by
  intro a ha b hb
  have : a ≠ 1 := fun e => h (e ▸ ha)
  have : b ≠ 1 := fun e => h (e ▸ hb)
  simp only
  omega

private theorem ordOn_pred_of_pos {l : List ℕ} (h : ∀ x ∈ l, 0 < x) : OrdOn (· - 1) l := by
  intro a ha b hb
  have := h a ha
  have := h b hb
  simp only
  omega

private theorem finite_bounded_lists (n B : ℕ) :
    {l : List ℕ | l.length ≤ n ∧ ∀ x ∈ l, x ≤ B}.Finite := by
  apply ((List.finite_length_le (Fin (B + 1)) n).image (List.map Fin.val)).subset
  rintro l ⟨hl, hB⟩
  refine ⟨l.pmap (fun x hx => (⟨x, Nat.lt_succ_of_le hx⟩ : Fin (B + 1))) hB, ?_, ?_⟩
  · simpa using hl
  · simp [List.map_pmap]

private theorem bad_one_imp {b c : ℕ} (h : Bad 1 b c) : b = c := by
  unfold Bad at h
  omega

private theorem avoid_zero_one_cons {L : List ℕ} (hL : Avoid L) (hn : L.Nodup) (h1 : 1 ∉ L) :
    Avoid (0 :: 1 :: L) := by
  rw [avoid_cons_iff, avoid_cons_iff]
  refine ⟨⟨hL, fun b c hs hbad => ?_⟩, fun b c hs hbad => ?_⟩
  · obtain rfl := bad_one_imp hbad
    exact List.nodup_iff_sublist.mp hn b hs
  · rw [bad_zero_iff] at hbad
    obtain ⟨-, rfl⟩ := hbad
    rcases pair_sublist_cons_iff.mp hs with h | ⟨rfl, hb⟩
    · exact List.nodup_iff_sublist.mp hn b h
    · exact h1 hb

private theorem avoid_zero_one_zero_cons {L : List ℕ} (hL : Avoid L) (hn : L.Nodup)
    (h2 : ∀ x ∈ L, 2 ≤ x) : Avoid (0 :: 1 :: 0 :: L) := by
  have h0 : Avoid (0 :: L) := avoid_zero_cons_of_nodup hL hn
  rw [avoid_cons_iff, avoid_cons_iff]
  refine ⟨⟨h0, fun b c hs hbad => ?_⟩, fun b c hs hbad => ?_⟩
  · obtain rfl := bad_one_imp hbad
    rcases pair_sublist_cons_iff.mp hs with h | ⟨rfl, hb⟩
    · exact List.nodup_iff_sublist.mp hn b h
    · exact absurd (h2 0 hb) (by omega)
  · rw [bad_zero_iff] at hbad
    obtain ⟨hpos, rfl⟩ := hbad
    rcases pair_sublist_cons_iff.mp hs with h | ⟨rfl, hb⟩
    · rcases pair_sublist_cons_iff.mp h with h' | ⟨rfl, -⟩
      · exact List.nodup_iff_sublist.mp hn b h'
      · exact absurd hpos (by omega)
    · rcases List.mem_cons.mp hb with h' | h'
      · exact absurd h' (by omega)
      · exact absurd (h2 1 h') (by omega)

private theorem wasc_zero_cons_map {f : ℕ → ℕ} {r : List ℕ} (h : OrdOn f r) :
    wasc (0 :: r.map f) = wasc (0 :: r) := by
  rcases eq_or_ne r [] with rfl | hr
  · rfl
  · rw [wasc_zero_cons (by simpa using hr), wasc_zero_cons hr, wasc_map h]

private theorem desc_zero_cons_map {f : ℕ → ℕ} {r : List ℕ} (h : OrdOn f r) :
    desc (0 :: r.map f) = desc r := by
  rw [desc_zero_cons, desc_map h]

/-- Canonical description of a word of `W`: `m ≥ 1` zeros followed by `r`, which does not
start with `0`. -/
private def Good (m : ℕ) (r : List ℕ) : Prop :=
  1 ≤ m ∧ (∀ h : r ≠ [], r.head h ≠ 0) ∧ BoundR m 0 r ∧ Avoid (0 :: r)

/-- Canonical pairs with `L` weak ascents and `k` descents; the flag says whether `0` occurs
after the leading zeros. -/
private def PS (L k : ℕ) (z : Bool) : Set (ℕ × List ℕ) :=
  {q | Good q.1 q.2 ∧ q.1 - 1 + wasc (0 :: q.2) = L ∧ desc q.2 = k ∧ (0 ∈ q.2 ↔ z = true)}

/-- The value `1` is skipped. -/
private def opA (q : ℕ × List ℕ) : ℕ × List ℕ := (q.1 + 1, q.2.map inc)
/-- The value `1` is the first positive entry, and is not a descent top. -/
private def opB (q : ℕ × List ℕ) : ℕ × List ℕ := (q.1, 1 :: q.2.map inc)
/-- The value `1` is the first descent bottom. -/
private def opC (q : ℕ × List ℕ) : ℕ × List ℕ := (q.1 + 1, q.2.map (· + 1))
/-- The value `1` is the first positive entry and the first descent top, followed by `0`. -/
private def opD (q : ℕ × List ℕ) : ℕ × List ℕ := (q.1, 1 :: 0 :: q.2.map (· + 1))

private theorem Good.nodup {m : ℕ} {r : List ℕ} (h : Good m r) : r.Nodup :=
  nodup_of_avoid h.2.2.2 h.2.1

private theorem Good.avoid {m : ℕ} {r : List ℕ} (h : Good m r) : Avoid r :=
  h.2.2.2.sublist (List.sublist_cons_self 0 r)

private theorem inc_le (x : ℕ) : inc x ≤ x + 1 := by unfold inc; split_ifs <;> omega

private theorem inc_eq_zero_iff (x : ℕ) : inc x = 0 ↔ x = 0 := by
  unfold inc; split_ifs with h <;> simp [h]

private theorem inc_ne_one (x : ℕ) : inc x ≠ 1 := by unfold inc; split_ifs <;> omega

private theorem good_opA {m : ℕ} {r : List ℕ} (h : Good m r) : Good (m + 1) (r.map inc) := by
  obtain ⟨hm, hh, hb, hav⟩ := h
  refine ⟨by omega, fun hne => ?_, ?_, ?_⟩
  · rw [List.head_map, Ne, inc_eq_zero_iff]
    exact hh _
  · have := boundR_map (f := inc) (b := m) (b' := m + 1) (p := 0) (p' := 0) (c := 0)
      (ordOn_of_strictMono inc_strictMono r) (fun _ => by simp)
      (fun x _ c hx => by have := inc_le x; omega) (by simpa using hb)
    simpa using this
  · have e : (0 :: r).map inc = 0 :: r.map inc := by simp [inc]
    rw [← e, avoid_map (ordOn_of_strictMono inc_strictMono _)]
    exact hav

private theorem good_opB {m : ℕ} {r : List ℕ} (h : Good m r) : Good m (1 :: r.map inc) := by
  have hn := h.nodup
  have hr := h.avoid
  obtain ⟨hm, hh, hb, hav⟩ := h
  refine ⟨hm, fun _ => by simp, ⟨hm, ?_⟩, ?_⟩
  · have := boundR_map (f := inc) (b := m) (b' := m + 1) (p := 0) (p' := 1) (c := 0)
      (ordOn_of_strictMono inc_strictMono r)
      (fun hne => by
        have := hh hne
        simp only [zero_le, true_iff]
        unfold inc; split_ifs <;> omega)
      (fun x _ c hx => by have := inc_le x; omega) (by simpa using hb)
    simpa using this
  · refine avoid_zero_one_cons ((avoid_map (ordOn_of_strictMono inc_strictMono r)).mpr hr)
      (hn.map inc_strictMono.injective) ?_
    simp only [List.mem_map, not_exists, not_and]
    exact fun x _ => inc_ne_one x

private theorem good_opC {m : ℕ} {r : List ℕ} (h : Good m r) :
    Good (m + 1) (r.map (· + 1)) := by
  have hn := h.nodup
  have hr := h.avoid
  obtain ⟨hm, hh, hb, hav⟩ := h
  refine ⟨by omega, fun hne => by simp, ?_, ?_⟩
  · have := boundR_map (f := (· + 1)) (b := m) (b' := m + 1) (p := 0) (p' := 0) (c := 0)
      (ordOn_of_strictMono (fun _ _ h => Nat.succ_lt_succ h) r) (fun _ => by simp)
      (fun x _ c hx => by omega) (by simpa using hb)
    simpa using this
  · exact avoid_zero_cons_of_nodup
      ((avoid_map (ordOn_of_strictMono (fun _ _ h => Nat.succ_lt_succ h) r)).mpr hr)
      (hn.map (fun _ _ h => Nat.succ_injective h))

private theorem good_opD {m : ℕ} {r : List ℕ} (h : Good m r) (h0 : 0 ∉ r) :
    Good m (1 :: 0 :: r.map (· + 1)) := by
  have hn := h.nodup
  have hr := h.avoid
  obtain ⟨hm, hh, hb, hav⟩ := h
  refine ⟨hm, fun _ => by simp, ⟨hm, by omega, ?_⟩, ?_⟩
  · have := boundR_map (f := (· + 1)) (b := m) (b' := m + 1) (p := 0) (p' := 0) (c := 0)
      (ordOn_of_strictMono (fun _ _ h => Nat.succ_lt_succ h) r) (fun _ => by simp)
      (fun x _ c hx => by omega) (by simpa using hb)
    simpa using this
  · refine avoid_zero_one_zero_cons
      ((avoid_map (ordOn_of_strictMono (fun _ _ h => Nat.succ_lt_succ h) r)).mpr hr)
      (hn.map (fun _ _ h => Nat.succ_injective h)) ?_
    simp only [List.mem_map, forall_exists_index, and_imp]
    rintro _ x hx rfl
    have : x ≠ 0 := fun e => h0 (e ▸ hx)
    omega

private theorem ordOn_succ (l : List ℕ) : OrdOn (· + 1) l :=
  ordOn_of_strictMono (fun _ _ h => Nat.succ_lt_succ h) l

private theorem ordOn_inc (l : List ℕ) : OrdOn inc l := ordOn_of_strictMono inc_strictMono l

private theorem wasc_one_cons_map_inc {r : List ℕ} (hh : ∀ h : r ≠ [], r.head h ≠ 0) :
    wasc (1 :: r.map inc) = wasc (0 :: r) := by
  rcases eq_or_ne r [] with rfl | hr
  · rfl
  · have h1 : 1 ≤ (r.map inc).head (by simpa using hr) := by
      rw [List.head_map]
      have := hh hr
      unfold inc; split_ifs <;> omega
    rw [wasc_cons_of_le _ h1, wasc_map (ordOn_inc r), wasc_zero_cons hr]

private theorem desc_one_cons_map_inc {r : List ℕ} (hh : ∀ h : r ≠ [], r.head h ≠ 0) :
    desc (1 :: r.map inc) = desc r := by
  rcases eq_or_ne r [] with rfl | hr
  · rfl
  · have h1 : 1 ≤ (r.map inc).head (by simpa using hr) := by
      rw [List.head_map]
      have := hh hr
      unfold inc; split_ifs <;> omega
    rw [desc_cons_of_le _ h1, desc_map (ordOn_inc r)]

private theorem opA_mem {L k : ℕ} {z : Bool} {q : ℕ × List ℕ} (hq : q ∈ PS L k z) :
    opA q ∈ PS (L + 1) k z := by
  obtain ⟨m, r⟩ := q
  obtain ⟨hg, hL, hk, hz⟩ := hq
  have hm := hg.1
  refine ⟨good_opA hg, ?_, ?_, ?_⟩
  · simp only [opA] at hL ⊢
    rw [wasc_zero_cons_map (ordOn_inc r)]
    omega
  · simp only [opA] at hk ⊢
    rw [desc_map (ordOn_inc r)]
    exact hk
  · simp only [opA, List.mem_map, inc_eq_zero_iff, exists_eq_right] at hz ⊢
    exact hz

private theorem opB_mem {L k : ℕ} {z : Bool} {q : ℕ × List ℕ} (hq : q ∈ PS L k z) :
    opB q ∈ PS (L + 1) k z := by
  obtain ⟨m, r⟩ := q
  obtain ⟨hg, hL, hk, hz⟩ := hq
  have hm := hg.1
  have hh := hg.2.1
  refine ⟨good_opB hg, ?_, ?_, ?_⟩
  · simp only [opB] at hL ⊢
    rw [wasc_cons_cons, wasc_one_cons_map_inc hh]
    simp only [zero_le, ite_true]
    omega
  · simp only [opB] at hk ⊢
    rw [desc_one_cons_map_inc hh]
    exact hk
  · simp only [opB, List.mem_cons, List.mem_map, inc_eq_zero_iff, exists_eq_right] at hz ⊢
    simpa using hz

private theorem opC_mem {L k : ℕ} {q : ℕ × List ℕ} (hq : q ∈ PS L k true) :
    opC q ∈ PS (L + 1) k false := by
  obtain ⟨m, r⟩ := q
  obtain ⟨hg, hL, hk, hz⟩ := hq
  have hm := hg.1
  refine ⟨good_opC hg, ?_, ?_, ?_⟩
  · simp only [opC] at hL ⊢
    rw [wasc_zero_cons_map (ordOn_succ r)]
    omega
  · simp only [opC] at hk ⊢
    rw [desc_map (ordOn_succ r)]
    exact hk
  · simp [opC]

private theorem opD_mem {L k : ℕ} {q : ℕ × List ℕ} (hq : q ∈ PS L k false) :
    opD q ∈ PS (L + 1) (k + 1) true := by
  obtain ⟨m, r⟩ := q
  obtain ⟨hg, hL, hk, hz⟩ := hq
  have hm := hg.1
  have h0 : 0 ∉ r := by simpa using hz
  refine ⟨good_opD hg h0, ?_, ?_, ?_⟩
  · simp only [opD] at hL ⊢
    rw [wasc_cons_cons, wasc_cons_cons, wasc_zero_cons_map (ordOn_succ r)]
    simp only [zero_le, ite_true, Nat.one_ne_zero, Nat.le_zero, ite_false]
    omega
  · simp only [opD] at hk ⊢
    rw [desc_cons_cons, desc_zero_cons_map (ordOn_succ r)]
    simp only [Nat.zero_lt_one, ite_true]
    omega
  · simp [opD]

private theorem wasc_cons_congr {a a' : ℕ} {l : List ℕ}
    (h : ∀ hl : l ≠ [], (a ≤ l.head hl ↔ a' ≤ l.head hl)) : wasc (a :: l) = wasc (a' :: l) := by
  cases l with
  | nil => rfl
  | cons b t =>
    have hb := h (by simp)
    simp only [head_cons] at hb
    rw [wasc_cons_cons, wasc_cons_cons]
    simp only [hb]

private theorem desc_cons_congr {a a' : ℕ} {l : List ℕ}
    (h : ∀ hl : l ≠ [], (l.head hl < a ↔ l.head hl < a')) : desc (a :: l) = desc (a' :: l) := by
  cases l with
  | nil => rfl
  | cons b t =>
    have hb := h (by simp)
    simp only [head_cons] at hb
    rw [desc_cons_cons, desc_cons_cons]
    simp only [hb]

private theorem map_pred_inc {l : List ℕ} (h : 1 ∉ l) : (l.map (· - 1)).map inc = l := by
  rw [List.map_map]
  conv_rhs => rw [← List.map_id l]
  apply List.map_congr_left
  intro x hx
  have : x ≠ 1 := fun e => h (e ▸ hx)
  simp only [Function.comp, inc, id]
  split_ifs <;> omega

private theorem map_pred_succ {l : List ℕ} (h : 0 ∉ l) : (l.map (· - 1)).map (· + 1) = l := by
  rw [List.map_map]
  conv_rhs => rw [← List.map_id l]
  apply List.map_congr_left
  intro x hx
  have : x ≠ 0 := fun e => h (e ▸ hx)
  simp only [Function.comp, id]
  omega

private theorem pair_sublist_of_mem {a b : ℕ} :
    ∀ {l : List ℕ}, a ∈ l → b ∈ l → a ≠ b → [a, b] <+ l ∨ [b, a] <+ l
  | [], ha, _, _ => by simp at ha
  | x :: l, ha, hb, hab => by
    rcases List.mem_cons.mp ha with rfl | ha'
    · have hb' : b ∈ l := (List.mem_cons.mp hb).resolve_left (Ne.symm hab)
      exact Or.inl ((List.singleton_sublist.mpr hb').cons_cons a)
    rcases List.mem_cons.mp hb with rfl | hb'
    · exact Or.inr ((List.singleton_sublist.mpr ha').cons_cons b)
    rcases pair_sublist_of_mem ha' hb' hab with h | h
    · exact Or.inl (h.cons x)
    · exact Or.inr (h.cons x)

private theorem not_mem_zero_of_desc_eq_zero :
    ∀ {r : List ℕ}, (∀ h : r ≠ [], r.head h ≠ 0) → desc r = 0 → 0 ∉ r
  | [], _, _ => by simp
  | [a], hh, _ => by
    have := hh (by simp)
    simp only [head_cons] at this
    simpa [eq_comm] using this
  | a :: b :: t, hh, hd => by
    have ha := hh (by simp)
    simp only [head_cons] at ha
    rw [desc_cons_cons] at hd
    have hba : ¬ b < a := by
      intro h
      rw [ite_eq_left h] at hd
      omega
    rw [ite_eq_right hba, Nat.zero_add] at hd
    have ih := not_mem_zero_of_desc_eq_zero (r := b :: t) (fun _ => by simp; omega) hd
    rw [List.mem_cons]
    rintro (h | h)
    · exact ha h.symm
    · exact ih h

private theorem head_le_of_boundR {b p : ℕ} {r : List ℕ} (h : BoundR b p r) (hr : r ≠ []) :
    r.head hr ≤ b := by
  cases r with
  | nil => exact absurd rfl hr
  | cons x t => exact h.1

private theorem mem_PS {L k : ℕ} {z : Bool} {m : ℕ} {r : List ℕ} :
    (m, r) ∈ PS L k z ↔ Good m r ∧ m - 1 + wasc (0 :: r) = L ∧ desc r = k ∧
      (0 ∈ r ↔ z = true) := Iff.rfl

/-- Case `A`: the value `1` does not occur. -/
private theorem back_A {L k : ℕ} {z : Bool} {m : ℕ} {r : List ℕ}
    (hq : (m, r) ∈ PS (L + 1) k z) (h1 : 1 ∉ r) :
    (m - 1, r.map (· - 1)) ∈ PS L k z ∧ opA (m - 1, r.map (· - 1)) = (m, r) := by
  rw [mem_PS] at hq
  obtain ⟨⟨hm, hh, hb, hav⟩, hL, hk, hz⟩ := hq
  have hm2 : 2 ≤ m := by
    rcases eq_or_ne r [] with rfl | hr
    · simp [wordWeakAscents] at hL; omega
    · have h0 := hh hr
      have h1' : r.head hr ≠ 1 := fun e => h1 (e ▸ List.head_mem hr)
      have := head_le_of_boundR hb hr
      omega
  have hord := ordOn_pred_of_not_one h1
  rw [mem_PS]
  refine ⟨⟨⟨by omega, fun hne => ?_, ?_, ?_⟩, ?_, ?_, ?_⟩, ?_⟩
  · have hr : r ≠ [] := by simpa using hne
    rw [List.head_map]
    have h0 := hh hr
    have h1' : r.head hr ≠ 1 := fun e => h1 (e ▸ List.head_mem hr)
    change r.head _ - 1 ≠ 0
    omega
  · have := boundR_map (f := (· - 1)) (b := m) (b' := m - 1) (p := 0) (p' := 0) (c := 0)
      hord (fun _ => by simp) (fun x _ c hx => by show x - 1 ≤ m - 1 + c; omega)
      (by simpa using hb)
    simpa using this
  · have e : (0 :: r).map (· - 1) = 0 :: r.map (· - 1) := by simp
    have hord' : OrdOn (· - 1) (0 :: r) := ordOn_pred_of_not_one (by simpa [eq_comm] using h1)
    rw [← e, avoid_map hord']
    exact hav
  · rw [wasc_zero_cons_map hord]
    omega
  · rw [desc_map hord]
    exact hk
  · rw [← hz, List.mem_map]
    constructor
    · rintro ⟨x, hx, hx0⟩
      have : x ≠ 1 := fun e => h1 (e ▸ hx)
      have : x = 0 := by omega
      exact this ▸ hx
    · intro h0
      exact ⟨0, h0, rfl⟩
  · simp only [opA, Prod.mk.injEq]
    exact ⟨by omega, map_pred_inc h1⟩

/-- Case `B`: the value `1` is the first positive entry, followed by a positive entry or by
nothing. -/
private theorem back_B {L k : ℕ} {z : Bool} {m : ℕ} {r : List ℕ}
    (hq : (m, 1 :: r) ∈ PS (L + 1) k z) (h0 : ∀ h : r ≠ [], r.head h ≠ 0) :
    (m, r.map (· - 1)) ∈ PS L k z ∧ opB (m, r.map (· - 1)) = (m, 1 :: r) := by
  rw [mem_PS] at hq
  have hn := (hq.1).nodup
  obtain ⟨⟨hm, -, ⟨-, hb⟩, hav⟩, hL, hk, hz⟩ := hq
  have h1 : 1 ∉ r := (List.nodup_cons.mp hn).1
  have hord := ordOn_pred_of_not_one h1
  have hhead2 : ∀ hr : r ≠ [], 2 ≤ r.head hr := by
    intro hr
    have := h0 hr
    have h1' : r.head hr ≠ 1 := fun e => h1 (e ▸ List.head_mem hr)
    omega
  have hw : wasc (1 :: r) = wasc (0 :: r) :=
    wasc_cons_congr (fun hr => by have := hhead2 hr; constructor <;> intro <;> omega)
  have hd : desc (1 :: r) = desc r := by
    rw [desc_cons_congr (a' := 0) (fun hr => by
        have := hhead2 hr; constructor <;> intro <;> omega), desc_zero_cons]
  rw [mem_PS]
  refine ⟨⟨⟨hm, fun hne => ?_, ?_, ?_⟩, ?_, ?_, ?_⟩, ?_⟩
  · have hr : r ≠ [] := by simpa using hne
    rw [List.head_map]
    have := hhead2 hr
    change r.head _ - 1 ≠ 0
    omega
  · have := boundR_map (f := (· - 1)) (b := m + 1) (b' := m) (p := 1) (p' := 0) (c := 0)
      hord (fun hr => by have := hhead2 hr; simp only [zero_le, iff_true]; omega)
      (fun x _ c hx => by show x - 1 ≤ m + c; omega) (by simpa using hb)
    simpa using this
  · have e : (0 :: r).map (· - 1) = 0 :: r.map (· - 1) := by simp
    have hord' : OrdOn (· - 1) (0 :: r) := ordOn_pred_of_not_one (by simpa [eq_comm] using h1)
    rw [← e, avoid_map hord']
    exact hav.sublist ((List.sublist_cons_self 1 r).cons_cons 0)
  · rw [wasc_zero_cons_map hord]
    rw [wasc_cons_cons, hw] at hL
    simp only [zero_le, ite_true] at hL
    omega
  · rw [desc_map hord, ← hd]
    exact hk
  · rw [← hz, List.mem_map, List.mem_cons]
    constructor
    · rintro ⟨x, hx, hx0⟩
      have : x ≠ 1 := fun e => h1 (e ▸ hx)
      have : x = 0 := by omega
      exact Or.inr (this ▸ hx)
    · rintro (h | h)
      · exact absurd h (by omega)
      · exact ⟨0, h, rfl⟩
  · simp only [opB, Prod.mk.injEq, cons.injEq, true_and]
    exact map_pred_inc h1

/-- Case `C`: the value `1` is the first descent bottom. -/
private theorem back_C {L k : ℕ} {m : ℕ} {r : List ℕ}
    (hq : (m, r) ∈ PS (L + 1) k false) (h1 : 1 ∈ r) (hh1 : ∀ h : r ≠ [], r.head h ≠ 1) :
    (m - 1, r.map (· - 1)) ∈ PS L k true ∧ opC (m - 1, r.map (· - 1)) = (m, r) := by
  rw [mem_PS] at hq
  have hn := (hq.1).nodup
  have hr' := (hq.1).avoid
  obtain ⟨⟨hm, hh, hb, hav⟩, hL, hk, hz⟩ := hq
  have h0 : 0 ∉ r := by simpa using hz
  have hpos : ∀ x ∈ r, 0 < x := fun x hx => Nat.pos_of_ne_zero (fun e => h0 (e ▸ hx))
  have hr : r ≠ [] := List.ne_nil_of_mem h1
  have hm2 : 2 ≤ m := by
    have := hh hr
    have := hh1 hr
    have := head_le_of_boundR hb hr
    omega
  have hord := ordOn_pred_of_pos hpos
  rw [mem_PS]
  refine ⟨⟨⟨by omega, fun hne => ?_, ?_, ?_⟩, ?_, ?_, ?_⟩, ?_⟩
  · rw [List.head_map]
    have := hh hr
    have := hh1 hr
    change r.head _ - 1 ≠ 0
    omega
  · have := boundR_map (f := (· - 1)) (b := m) (b' := m - 1) (p := 0) (p' := 0) (c := 0)
      hord (fun _ => by simp) (fun x _ c hx => by show x - 1 ≤ m - 1 + c; omega)
      (by simpa using hb)
    simpa using this
  · refine avoid_zero_cons_of_nodup ((avoid_map hord).mpr hr') ?_
    refine List.Nodup.map_on (fun x hx y hy hxy => ?_) hn
    have := hpos x hx
    have := hpos y hy
    change x - 1 = y - 1 at hxy
    omega
  · rw [wasc_zero_cons_map hord]
    omega
  · rw [desc_map hord]
    exact hk
  · simp only [List.mem_map, iff_true]
    exact ⟨1, h1, rfl⟩
  · simp only [opC, Prod.mk.injEq]
    exact ⟨by omega, map_pred_succ h0⟩

/-- Case `D`: the value `1` is the first positive entry and a descent top, followed by `0`. -/
private theorem back_D {L k : ℕ} {m : ℕ} {r : List ℕ}
    (hq : (m, 1 :: 0 :: r) ∈ PS (L + 1) (k + 1) true) :
    (m, r.map (· - 1)) ∈ PS L k false ∧ opD (m, r.map (· - 1)) = (m, 1 :: 0 :: r) := by
  rw [mem_PS] at hq
  have hn := (hq.1).nodup
  obtain ⟨⟨hm, -, ⟨-, -, hb⟩, hav⟩, hL, hk, -⟩ := hq
  have h1 : 1 ∉ r := fun h => (List.nodup_cons.mp hn).1 (List.mem_cons_of_mem _ h)
  have h0 : 0 ∉ r := (List.nodup_cons.mp (List.nodup_cons.mp hn).2).1
  have hord := ordOn_pred_of_not_one h1
  rw [mem_PS]
  refine ⟨⟨⟨hm, fun hne => ?_, ?_, ?_⟩, ?_, ?_, ?_⟩, ?_⟩
  · have hr : r ≠ [] := by simpa using hne
    rw [List.head_map]
    have h0' : r.head hr ≠ 0 := fun e => h0 (e ▸ List.head_mem hr)
    have h1' : r.head hr ≠ 1 := fun e => h1 (e ▸ List.head_mem hr)
    change r.head _ - 1 ≠ 0
    omega
  · have := boundR_map (f := (· - 1)) (b := m + 1) (b' := m) (p := 0) (p' := 0) (c := 0)
      hord (fun _ => by simp) (fun x _ c hx => by show x - 1 ≤ m + c; omega)
      (by simpa using hb)
    simpa using this
  · have e : (0 :: r).map (· - 1) = 0 :: r.map (· - 1) := by simp
    have hord' : OrdOn (· - 1) (0 :: r) := ordOn_pred_of_not_one (by simpa [eq_comm] using h1)
    rw [← e, avoid_map hord']
    exact hav.sublist (((List.sublist_cons_self 0 r).cons 1).cons_cons 0)
  · rw [wasc_zero_cons_map hord]
    rw [wasc_cons_cons, wasc_cons_cons] at hL
    simp only [zero_le, ite_true, Nat.one_ne_zero, Nat.le_zero, ite_false] at hL
    omega
  · rw [desc_map hord]
    rw [desc_cons_cons, desc_zero_cons] at hk
    simp only [Nat.zero_lt_one, ite_true] at hk
    omega
  · simp only [List.mem_map, Bool.false_eq_true, iff_false, not_exists, not_and]
    intro x hx
    have : x ≠ 0 := fun e => h0 (e ▸ hx)
    have : x ≠ 1 := fun e => h1 (e ▸ hx)
    change ¬ x - 1 = 0
    omega
  · simp only [opD, Prod.mk.injEq, cons.injEq, true_and]
    exact map_pred_succ h0

/-- With a zero after the leading zeros, the value `1` cannot be a descent bottom. -/
private theorem not_C_of_true {L k : ℕ} {m : ℕ} {r : List ℕ}
    (hq : (m, r) ∈ PS L k true) (h1 : 1 ∈ r) (hh1 : ∀ h : r ≠ [], r.head h ≠ 1) : False := by
  obtain ⟨⟨-, hh, -, hav⟩, -, -, hz⟩ := hq
  simp only [iff_true] at hz
  obtain ⟨x, t, rfl⟩ : ∃ x t, r = x :: t := by
    cases r with
    | nil => simp at h1
    | cons x t => exact ⟨x, t, rfl⟩
  have hx0 : x ≠ 0 := hh (by simp)
  have hx1 : x ≠ 1 := hh1 (by simp)
  have h0t : 0 ∈ t := (List.mem_cons.mp hz).resolve_left (Ne.symm hx0)
  have h1t : 1 ∈ t := (List.mem_cons.mp h1).resolve_left (Ne.symm hx1)
  rcases pair_sublist_of_mem h0t h1t (by omega) with h | h
  · exact hav ((h.cons_cons x).cons 0) (Or.inr ⟨by omega, by omega⟩)
  · exact hav ((h.cons_cons x).cons 0) (Or.inr ⟨by omega, by omega⟩)

private theorem eq_one_cons_of_head {r : List ℕ} (hne : r ≠ []) (hh : r.head hne = 1) :
    ∃ r', r = 1 :: r' := by
  cases r with
  | nil => exact absurd rfl hne
  | cons x t =>
    simp only [head_cons] at hh
    exact ⟨t, by rw [hh]⟩

private theorem PS_succ_false (L k : ℕ) :
    PS (L + 1) k false = opA '' PS L k false ∪ opB '' PS L k false ∪ opC '' PS L k true := by
  ext ⟨m, r⟩
  constructor
  · intro hq
    by_cases h1 : 1 ∈ r
    · by_cases hh : ∃ h : r ≠ [], r.head h = 1
      · obtain ⟨hne, hh1⟩ := hh
        obtain ⟨r', rfl⟩ := eq_one_cons_of_head hne hh1
        have h0 : ∀ h : r' ≠ [], r'.head h ≠ 0 := by
          intro h e
          have hz := (mem_PS.mp hq).2.2.2
          simp only [Bool.false_eq_true, iff_false, List.mem_cons] at hz
          exact hz (Or.inr (e ▸ List.head_mem h))
        obtain ⟨hmem, he⟩ := back_B hq h0
        exact Or.inl (Or.inr ⟨_, hmem, he⟩)
      · simp only [not_exists] at hh
        obtain ⟨hmem, he⟩ := back_C hq h1 hh
        exact Or.inr ⟨_, hmem, he⟩
    · obtain ⟨hmem, he⟩ := back_A hq h1
      exact Or.inl (Or.inl ⟨_, hmem, he⟩)
  · rintro ((⟨q, hq, he⟩ | ⟨q, hq, he⟩) | ⟨q, hq, he⟩) <;> rw [← he]
    · exact opA_mem hq
    · exact opB_mem hq
    · exact opC_mem hq

private theorem PS_succ_true (L k : ℕ) :
    PS (L + 1) (k + 1) true =
      opA '' PS L (k + 1) true ∪ opB '' PS L (k + 1) true ∪ opD '' PS L k false := by
  ext ⟨m, r⟩
  constructor
  · intro hq
    by_cases h1 : 1 ∈ r
    · by_cases hh : ∃ h : r ≠ [], r.head h = 1
      · obtain ⟨hne, hh1⟩ := hh
        obtain ⟨r', rfl⟩ := eq_one_cons_of_head hne hh1
        by_cases hz : ∃ r'', r' = 0 :: r''
        · obtain ⟨r'', rfl⟩ := hz
          obtain ⟨hmem, he⟩ := back_D hq
          exact Or.inr ⟨_, hmem, he⟩
        · have h0 : ∀ h : r' ≠ [], r'.head h ≠ 0 := by
            intro h e
            apply hz
            cases r' with
            | nil => exact absurd rfl h
            | cons x t =>
              simp only [head_cons] at e
              exact ⟨t, by rw [e]⟩
          obtain ⟨hmem, he⟩ := back_B hq h0
          exact Or.inl (Or.inr ⟨_, hmem, he⟩)
      · simp only [not_exists] at hh
        exact (not_C_of_true hq h1 hh).elim
    · obtain ⟨hmem, he⟩ := back_A hq h1
      exact Or.inl (Or.inl ⟨_, hmem, he⟩)
  · rintro ((⟨q, hq, he⟩ | ⟨q, hq, he⟩) | ⟨q, hq, he⟩) <;> rw [← he]
    · exact opA_mem hq
    · exact opB_mem hq
    · exact opD_mem hq

private theorem PS_zero_true (L : ℕ) : PS L 0 true = ∅ := by
  ext ⟨m, r⟩
  simp only [Set.mem_empty_iff_false, iff_false]
  intro hq
  rw [mem_PS] at hq
  obtain ⟨⟨-, hh, -, -⟩, -, hk, hz⟩ := hq
  exact not_mem_zero_of_desc_eq_zero hh hk (hz.mpr rfl)

private theorem mem_PS_zero {k : ℕ} {z : Bool} {q : ℕ × List ℕ} (hq : q ∈ PS 0 k z) :
    q = (1, []) ∧ k = 0 ∧ z = false := by
  obtain ⟨m, r⟩ := q
  rw [mem_PS] at hq
  obtain ⟨⟨hm, -, -, -⟩, hL, hk, hz⟩ := hq
  have hr : r = [] := by
    by_contra hr
    rw [wasc_zero_cons hr] at hL
    omega
  subst hr
  refine ⟨by simp only [Prod.mk.injEq, and_true]; omega, by simpa [desc] using hk.symm, ?_⟩
  cases z
  · rfl
  · simp at hz

private theorem one_nil_mem_PS : ((1 : ℕ), ([] : List ℕ)) ∈ PS 0 0 false := by
  rw [mem_PS]
  refine ⟨⟨le_rfl, fun h => absurd rfl h, trivial, fun a b c hs => ?_⟩, rfl, rfl, by simp⟩
  exact absurd hs.length_le (by simp)

private theorem wasc_le_length (l : List ℕ) : wasc l ≤ l.length - 1 := by
  have := wasc_add_desc l
  omega

private theorem PS_subset_box (L k : ℕ) (z : Bool) :
    PS L k z ⊆ {i | i ≤ L + 1} ×ˢ
      {l : List ℕ | l.length ≤ L + k ∧ ∀ x ∈ l, x ≤ 2 * L + k + 1} := by
  rintro ⟨m, r⟩ hq
  rw [mem_PS] at hq
  obtain ⟨⟨hm, -, hb, -⟩, hL, hk, -⟩ := hq
  have hlen : r.length = wasc (0 :: r) + desc r := by
    have := wasc_add_desc (0 :: r)
    rw [desc_zero_cons] at this
    simpa using this.symm
  simp only [Set.mem_prod, Set.mem_ofPred_eq]
  refine ⟨by omega, by omega, fun x hx => ?_⟩
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hx
  have h1 := (boundR_iff m 0 r).mp hb j hj
  have h2 := wasc_le_length (0 :: r.take j)
  simp only [length_cons, length_take] at h2
  omega

private theorem PS_finite (L k : ℕ) (z : Bool) : (PS L k z).Finite :=
  ((Set.finite_le_nat _).prod (finite_bounded_lists _ _)).subset (PS_subset_box L k z)

private theorem opA_injective : Function.Injective opA := by
  rintro ⟨m, r⟩ ⟨m', r'⟩ h
  simp only [opA, Prod.mk.injEq] at h
  exact Prod.ext (by simpa using h.1) (List.map_injective_iff.mpr inc_strictMono.injective h.2)

private theorem opB_injective : Function.Injective opB := by
  rintro ⟨m, r⟩ ⟨m', r'⟩ h
  simp only [opB, Prod.mk.injEq, cons.injEq, true_and] at h
  exact Prod.ext h.1 (List.map_injective_iff.mpr inc_strictMono.injective h.2)

private theorem opC_injective : Function.Injective opC := by
  rintro ⟨m, r⟩ ⟨m', r'⟩ h
  simp only [opC, Prod.mk.injEq] at h
  exact Prod.ext (by simpa using h.1)
    (List.map_injective_iff.mpr (fun _ _ e => Nat.succ_injective e) h.2)

private theorem opD_injective : Function.Injective opD := by
  rintro ⟨m, r⟩ ⟨m', r'⟩ h
  simp only [opD, Prod.mk.injEq, cons.injEq, true_and] at h
  exact Prod.ext h.1 (List.map_injective_iff.mpr (fun _ _ e => Nat.succ_injective e) h.2)

private theorem one_not_mem_opA (q : ℕ × List ℕ) : 1 ∉ (opA q).2 := by
  simp only [opA, List.mem_map, not_exists, not_and]
  exact fun x _ => inc_ne_one x

private theorem disjoint_A_B (S T : Set (ℕ × List ℕ)) : Disjoint (opA '' S) (opB '' T) := by
  rw [Set.disjoint_left]
  rintro _ ⟨q, -, rfl⟩ ⟨q', -, he⟩
  apply one_not_mem_opA q
  rw [← he]
  simp [opB]

private theorem disjoint_A_true (S : Set (ℕ × List ℕ)) {T : Set (ℕ × List ℕ)}
    (f : ℕ × List ℕ → ℕ × List ℕ) (hf : ∀ q ∈ T, 1 ∈ (f q).2) :
    Disjoint (opA '' S) (f '' T) := by
  rw [Set.disjoint_left]
  rintro _ ⟨q, -, rfl⟩ ⟨q', hq', he⟩
  apply one_not_mem_opA q
  rw [← he]
  exact hf q' hq'

private theorem one_mem_opC {L k : ℕ} {q : ℕ × List ℕ} (hq : q ∈ PS L k true) :
    1 ∈ (opC q).2 := by
  obtain ⟨m, r⟩ := q
  have hz := (mem_PS.mp hq).2.2.2
  simp only [iff_true] at hz
  simp only [opC, List.mem_map]
  exact ⟨0, hz, rfl⟩

private theorem disjoint_B_C {L k : ℕ} (S : Set (ℕ × List ℕ)) :
    Disjoint (opB '' S) (opC '' PS L k true) := by
  rw [Set.disjoint_left]
  rintro _ ⟨q, -, rfl⟩ ⟨⟨m, r⟩, hq', he⟩
  rw [mem_PS] at hq'
  obtain ⟨⟨-, hh, -, -⟩, -, -, hz⟩ := hq'
  simp only [iff_true] at hz
  have hr : r ≠ [] := List.ne_nil_of_mem hz
  obtain ⟨x, t, rfl⟩ : ∃ x t, r = x :: t := by
    cases r with
    | nil => exact absurd rfl hr
    | cons x t => exact ⟨x, t, rfl⟩
  have hx : x ≠ 0 := hh (by simp)
  simp only [opB, opC, List.map_cons, Prod.mk.injEq, cons.injEq] at he
  omega

private theorem disjoint_B_D {L k : ℕ} (T : Set (ℕ × List ℕ)) :
    Disjoint (opB '' PS L (k + 1) true) (opD '' T) := by
  rw [Set.disjoint_left]
  rintro _ ⟨⟨m, r⟩, hq, rfl⟩ ⟨q', -, he⟩
  rw [mem_PS] at hq
  obtain ⟨⟨-, hh, -, -⟩, -, -, -⟩ := hq
  cases r with
  | nil => simp [opB, opD] at he
  | cons x t =>
    have hx : x ≠ 0 := hh (by simp)
    simp only [opB, opD, List.map_cons, Prod.mk.injEq, cons.injEq, true_and] at he
    exact hx ((inc_eq_zero_iff x).mp he.2.1.symm)

private theorem ncard_PS_succ_false (L k : ℕ) :
    (PS (L + 1) k false).ncard = 2 * (PS L k false).ncard + (PS L k true).ncard := by
  have hA := (PS_finite L k false).image opA
  have hB := (PS_finite L k false).image opB
  have hC := (PS_finite L k true).image opC
  rw [PS_succ_false, Set.ncard_union_eq (Set.disjoint_union_left.mpr
      ⟨disjoint_A_true _ opC (fun q hq => one_mem_opC hq), disjoint_B_C _⟩) (hA.union hB) hC,
    Set.ncard_union_eq (disjoint_A_B _ _) hA hB,
    Set.ncard_image_of_injective _ opA_injective, Set.ncard_image_of_injective _ opB_injective,
    Set.ncard_image_of_injective _ opC_injective]
  ring

private theorem ncard_PS_succ_true (L k : ℕ) :
    (PS (L + 1) (k + 1) true).ncard =
      2 * (PS L (k + 1) true).ncard + (PS L k false).ncard := by
  have hA := (PS_finite L (k + 1) true).image opA
  have hB := (PS_finite L (k + 1) true).image opB
  have hD := (PS_finite L k false).image opD
  rw [PS_succ_true, Set.ncard_union_eq (Set.disjoint_union_left.mpr
      ⟨disjoint_A_true _ opD (fun q _ => by simp [opD]), disjoint_B_D _⟩) (hA.union hB) hD,
    Set.ncard_union_eq (disjoint_A_B _ _) hA hB,
    Set.ncard_image_of_injective _ opA_injective, Set.ncard_image_of_injective _ opB_injective,
    Set.ncard_image_of_injective _ opD_injective]
  ring

private theorem choose_pow_step (L j : ℕ) :
    (L + 1).choose (j + 1) * 2 ^ (L + 1 - (j + 1)) =
      2 * (L.choose (j + 1) * 2 ^ (L - (j + 1))) + L.choose j * 2 ^ (L - j) := by
  rw [Nat.choose_succ_succ', show L + 1 - (j + 1) = L - j by omega]
  rcases Nat.lt_or_ge L (j + 1) with h | h
  · rw [Nat.choose_eq_zero_of_lt h]
    ring
  · rw [show L - j = (L - (j + 1)) + 1 by omega, pow_succ]
    ring

private theorem ncard_PS (L : ℕ) : ∀ k : ℕ,
    (PS L k false).ncard = L.choose (2 * k) * 2 ^ (L - 2 * k) ∧
      (PS L (k + 1) true).ncard = L.choose (2 * k + 1) * 2 ^ (L - (2 * k + 1)) := by
  induction L with
  | zero =>
    intro k
    have hT : PS 0 (k + 1) true = ∅ := by
      ext q
      simp only [Set.mem_empty_iff_false, iff_false]
      intro hq
      exact absurd (mem_PS_zero hq).2.1 (by omega)
    refine ⟨?_, by rw [hT]; simp⟩
    cases k with
    | zero =>
      have : PS 0 0 false = {((1 : ℕ), ([] : List ℕ))} := by
        ext q
        constructor
        · intro hq
          exact (mem_PS_zero hq).1
        · rintro rfl
          exact one_nil_mem_PS
      rw [this]
      simp
    | succ k =>
      have : PS 0 (k + 1) false = ∅ := by
        ext q
        simp only [Set.mem_empty_iff_false, iff_false]
        intro hq
        exact absurd (mem_PS_zero hq).2.1 (by omega)
      rw [this, Set.ncard_empty, Nat.choose_eq_zero_of_lt (by omega), Nat.zero_mul]
  | succ L ih =>
    intro k
    constructor
    · rw [ncard_PS_succ_false]
      cases k with
      | zero =>
        rw [PS_zero_true, Set.ncard_empty, (ih 0).1]
        simp [pow_succ]
        ring
      | succ k =>
        rw [(ih (k + 1)).1, (ih k).2, show 2 * (k + 1) = 2 * k + 1 + 1 by ring,
          choose_pow_step L (2 * k + 1)]
    · rw [ncard_PS_succ_true, (ih k).2, (ih k).1, choose_pow_step L (2 * k)]

private theorem exists_canonical : ∀ t : List ℕ, ∃ m r, 1 ≤ m ∧
    (∀ h : r ≠ [], r.head h ≠ 0) ∧ 0 :: t = replicate m 0 ++ r
  | [] => ⟨1, [], le_rfl, fun h => absurd rfl h, rfl⟩
  | x :: t => by
    by_cases hx : x = 0
    · subst hx
      obtain ⟨m, r, hm, hr, he⟩ := exists_canonical t
      exact ⟨m + 1, r, by omega, hr, by rw [he, replicate_succ, cons_append]⟩
    · exact ⟨1, x :: t, le_rfl, fun _ => hx, rfl⟩

private theorem canonical_unique : ∀ {m m' : ℕ} {r r' : List ℕ},
    (∀ h : r ≠ [], r.head h ≠ 0) → (∀ h : r' ≠ [], r'.head h ≠ 0) →
      replicate m 0 ++ r = replicate m' 0 ++ r' → m = m' ∧ r = r'
  | 0, 0, r, r', _, _, h => ⟨rfl, by simpa using h⟩
  | 0, m' + 1, r, r', hr, _, h => by
    simp only [replicate_succ, nil_append, cons_append, replicate_zero] at h
    subst h
    exact absurd rfl (hr (by simp))
  | m + 1, 0, r, r', _, hr', h => by
    simp only [replicate_succ, nil_append, cons_append, replicate_zero] at h
    subst h
    exact absurd rfl (hr' (by simp))
  | m + 1, m' + 1, r, r', hr, hr', h => by
    simp only [replicate_succ, cons_append, cons.injEq, true_and] at h
    obtain ⟨h1, h2⟩ := canonical_unique hr hr' h
    exact ⟨by omega, h2⟩

private theorem wasc_replicate_zero_append : ∀ {m : ℕ}, 1 ≤ m → ∀ r : List ℕ,
    wasc (replicate m 0 ++ r) = m - 1 + wasc (0 :: r)
  | 0, hm, _ => absurd hm (by omega)
  | 1, _, r => by simp
  | m + 2, _, r => by
    rw [replicate_succ, cons_append, wasc_zero_cons (by simp),
      wasc_replicate_zero_append (m := m + 1) (by omega) r]
    omega

private theorem desc_replicate_zero_append : ∀ (m : ℕ) (r : List ℕ),
    desc (replicate m 0 ++ r) = desc r
  | 0, r => by simp
  | m + 1, r => by
    rw [replicate_succ, cons_append, desc_zero_cons, desc_replicate_zero_append m r]

/-- Reassemble a word from its leading zeros and the rest. -/
private def asm (q : ℕ × List ℕ) : List ℕ := replicate q.1 0 ++ q.2

private theorem asm_injOn (L k : ℕ) : Set.InjOn asm (PS L k false ∪ PS L k true) := by
  rintro ⟨m, r⟩ hq ⟨m', r'⟩ hq' he
  have hr : ∀ h : r ≠ [], r.head h ≠ 0 := by
    rcases hq with hq | hq <;> exact (mem_PS.mp hq).1.2.1
  have hr' : ∀ h : r' ≠ [], r'.head h ≠ 0 := by
    rcases hq' with hq' | hq' <;> exact (mem_PS.mp hq').1.2.1
  obtain ⟨h1, h2⟩ := canonical_unique hr hr' he
  exact Prod.ext h1 h2

private theorem PS_disjoint_flag (L k : ℕ) : Disjoint (PS L k false) (PS L k true) := by
  rw [Set.disjoint_left]
  rintro ⟨m, r⟩ hq hq'
  have h1 := (mem_PS.mp hq).2.2.2
  have h2 := (mem_PS.mp hq').2.2.2
  simp only [Bool.false_eq_true, iff_false, iff_true] at h1 h2
  exact h1 h2

private theorem WA_desc_eq_image {N k : ℕ} (hk : k + 1 ≤ N) :
    {v | v ∈ WA N ∧ desc v = k} = asm '' (PS (N - 1 - k) k false ∪ PS (N - 1 - k) k true) := by
  ext v
  constructor
  · rintro ⟨hv, hd⟩
    have hv' := mem_WA_iff.mp hv
    obtain ⟨t, rfl⟩ : ∃ t, v = 0 :: t := by
      cases v with
      | nil => simp at hv'; omega
      | cons x t =>
        have := hv'.2.1.1 (by simp)
        simp only [getElem_cons_zero] at this
        exact ⟨t, by rw [this]⟩
    obtain ⟨m, r, hm, hr, he⟩ := exists_canonical t
    rw [he] at hv hd
    have hlen : m + r.length = N := by
      have := (mem_WA_iff.mp hv).1
      simpa using this
    rw [← hlen, replicate_append_mem_iff hm] at hv
    have hw := wasc_add_desc (replicate m 0 ++ r)
    rw [wasc_replicate_zero_append hm, desc_replicate_zero_append] at hw
    rw [desc_replicate_zero_append] at hd
    simp only [length_append, length_replicate] at hw
    have hmem : ∀ z : Bool, (0 ∈ r ↔ z = true) → (m, r) ∈ PS (N - 1 - k) k z := by
      intro z hz
      rw [mem_PS]
      exact ⟨⟨hm, hr, hv.1, hv.2⟩, by omega, hd, hz⟩
    refine ⟨(m, r), ?_, by rw [he]; rfl⟩
    by_cases h0 : 0 ∈ r
    · exact Or.inr (hmem true (by simpa using h0))
    · exact Or.inl (hmem false (by simpa using h0))
  · rintro ⟨⟨m, r⟩, hq, rfl⟩
    have hq' : Good m r ∧ m - 1 + wasc (0 :: r) = N - 1 - k ∧ desc r = k := by
      rcases hq with hq | hq <;> exact ⟨(mem_PS.mp hq).1, (mem_PS.mp hq).2.1, (mem_PS.mp hq).2.2.1⟩
    obtain ⟨⟨hm, -, hb, hav⟩, hL, hd⟩ := hq'
    have hlen : r.length = wasc (0 :: r) + desc r := by
      have := wasc_add_desc (0 :: r)
      rw [desc_zero_cons] at this
      simpa using this.symm
    have hmN : m + r.length = N := by omega
    refine ⟨?_, ?_⟩
    · change replicate m 0 ++ r ∈ WA N
      rw [← hmN, replicate_append_mem_iff hm]
      exact ⟨hb, hav⟩
    · change desc (replicate m 0 ++ r) = k
      rw [desc_replicate_zero_append, hd]

/-- The number of words of `W` of length `N` with `k` descents. -/
private def dcount (N k : ℕ) : ℕ :=
  (N - 1 - k).choose (2 * k) * 2 ^ (N - 1 - k - 2 * k) +
    if k = 0 then 0 else (N - 1 - k).choose (2 * k - 1) * 2 ^ (N - 1 - k - (2 * k - 1))

private theorem ncard_WA_desc {N k : ℕ} (hk : k + 1 ≤ N) :
    {v | v ∈ WA N ∧ desc v = k}.ncard = dcount N k := by
  rw [WA_desc_eq_image hk, Set.InjOn.ncard_image (asm_injOn _ _),
    Set.ncard_union_eq (PS_disjoint_flag _ _) (PS_finite _ _ _) (PS_finite _ _ _),
    (ncard_PS _ k).1, dcount]
  congr 1
  cases k with
  | zero => simp [PS_zero_true]
  | succ k =>
    rw [(ncard_PS _ k).2]
    simp only [Nat.add_one_ne_zero, ite_false]
    congr 2

private theorem wasc_le_append : ∀ (l₁ l₂ : List ℕ), wasc l₁ ≤ wasc (l₁ ++ l₂)
  | [], _ => Nat.zero_le _
  | [_], _ => Nat.zero_le _
  | a :: b :: t, l₂ => by
    have := wasc_le_append (b :: t) l₂
    simp only [cons_append] at this ⊢
    rw [wasc_cons_cons, wasc_cons_cons]
    omega

private theorem wasc_append_singleton_le : ∀ (l : List ℕ) (x : ℕ), wasc (l ++ [x]) ≤ wasc l + 1
  | [], _ => Nat.zero_le _
  | [a], x => by simp [wordWeakAscents]; split_ifs <;> omega
  | a :: b :: t, x => by
    have := wasc_append_singleton_le (b :: t) x
    simp only [cons_append] at this ⊢
    rw [wasc_cons_cons, wasc_cons_cons]
    omega

private theorem wasc_take_le (l : List ℕ) (i : ℕ) : wasc (l.take i) ≤ wasc l := by
  conv_rhs => rw [← List.take_append_drop i l]
  exact wasc_le_append _ _

private theorem take_succ_eq {v : List ℕ} {i : ℕ} (h : i < v.length) :
    v.take (i + 1) = v.take i ++ [v[i]] := by
  rw [List.take_add_one, List.getElem?_eq_getElem h]
  rfl

/-- In a weak ascent sequence every entry is at most the number of weak ascents. -/
private theorem entry_le_wasc {v : List ℕ} (hv : IsWeakAscentSeq v) : ∀ x ∈ v, x ≤ wasc v := by
  have key : ∀ i (h : i < v.length), v[i] ≤ wasc (v.take (i + 1)) := by
    intro i
    induction i with
    | zero =>
      intro h
      rw [hv.1 h]
      exact Nat.zero_le _
    | succ i ih =>
      intro h
      have hb := hv.2 (i + 1) h
      have hprev := ih (by omega)
      have e : v.take (i + 1 + 1) = v.take i ++ [v[i], v[i + 1]] := by
        rw [take_succ_eq h, take_succ_eq (by omega : i < v.length), List.append_assoc]
        rfl
      rw [e, wasc_append_pair, ← take_succ_eq (by omega : i < v.length)]
      split_ifs with hle
      · omega
      · have := Nat.lt_of_not_le hle
        omega
  intro x hx
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
  exact (key i hi).trans (wasc_take_le v _)

private theorem iwas_take {w : List ℕ} (hw : IsWeakAscentSeq w) (i : ℕ) :
    IsWeakAscentSeq (w.take i) := by
  refine ⟨fun h => ?_, fun j h => ?_⟩
  · rw [List.getElem_take]
    exact hw.1 _
  · rw [List.getElem_take, List.take_take]
    have hj : j < i := by simp at h; omega
    rw [min_eq_left hj.le]
    exact hw.2 j (by simp at h; omega)

private theorem take_mem_WA {w : List ℕ} {n : ℕ} (hw : w ∈ WA n) {i : ℕ} (hi : i ≤ n) :
    w.take i ∈ WA i := by
  rw [mem_WA_iff] at hw ⊢
  exact ⟨by simp [hw.1, hi], iwas_take hw.2.1 i, hw.2.2.sublist (List.take_sublist i w)⟩

private theorem append_mem_WA {v : List ℕ} {N : ℕ} (hv : v ∈ WA N) (hN : 1 ≤ N) {x : ℕ}
    (hx : x ≤ wasc v + 1) (hbad : ∀ ⦃a b : ℕ⦄, [a, b] <+ v → ¬ Bad a b x) :
    v ++ [x] ∈ WA (N + 1) := by
  rw [mem_WA_iff] at hv ⊢
  obtain ⟨hlen, hiw, hav⟩ := hv
  refine ⟨by simp [hlen], ⟨fun h => ?_, fun i h => ?_⟩, ?_⟩
  · rw [List.getElem_append_left (by omega)]
    exact hiw.1 _
  · simp only [length_append, length_cons, length_nil] at h
    rcases Nat.lt_or_ge i v.length with hi | hi
    · rw [List.getElem_append_left hi, List.take_append_of_le_length hi.le]
      exact hiw.2 i hi
    · have hi' : i = v.length := by omega
      subst hi'
      rw [List.getElem_append_right le_rfl, List.take_left' rfl]
      simpa using hx
  · intro a b c hs
    obtain ⟨l₁, l₂, he, h₁, h₂⟩ := List.sublist_append_iff.mp hs
    rcases List.sublist_singleton.mp h₂ with rfl | rfl
    · simp only [append_nil] at he
      subst he
      exact hav h₁
    · obtain ⟨rfl, rfl⟩ : l₁ = [a, b] ∧ c = x := by
        have := he.symm
        simp only [List.append_eq_cons_iff, cons.injEq] at this
        rcases l₁ with _ | ⟨a', _ | ⟨b', _ | ⟨c', l⟩⟩⟩ <;> simp_all
      exact hbad h₁

private theorem boundR_mono : ∀ {b b' p : ℕ} {t : List ℕ}, b ≤ b' → BoundR b p t → BoundR b' p t
  | _, _, _, [], _, _ => trivial
  | _, _, _, x :: t, hbb, ⟨hx, ht⟩ => ⟨hx.trans hbb, boundR_mono (by omega) ht⟩

private theorem replicate_zero_append_mem {v : List ℕ} {N : ℕ} (hv : v ∈ WA N) (hN : 1 ≤ N)
    (s : ℕ) : replicate s 0 ++ v ∈ WA (s + N) := by
  have hv' := mem_WA_iff.mp hv
  obtain ⟨t, rfl⟩ : ∃ t, v = 0 :: t := by
    cases v with
    | nil => simp at hv'; omega
    | cons x t =>
      have := hv'.2.1.1 (by simp)
      simp only [getElem_cons_zero] at this
      exact ⟨t, by rw [this]⟩
  obtain ⟨m, r, hm, -, he⟩ := exists_canonical t
  rw [he] at hv ⊢
  have hlen : m + r.length = N := by simpa using (mem_WA_iff.mp hv).1
  rw [← hlen, replicate_append_mem_iff hm] at hv
  rw [← List.append_assoc, ← List.replicate_add, ← hlen,
    show s + (m + r.length) = s + m + r.length by omega,
    replicate_append_mem_iff (by omega)]
  exact ⟨boundR_mono (by omega) hv.1, hv.2⟩

private theorem getD_mem_of_lt {w : List ℕ} {i : ℕ} (h : i < w.length) : w.getD i 0 ∈ w := by
  rw [List.getD_eq_getElem _ _ h]
  exact List.getElem_mem h

private theorem drop_eq_getD_cons {w : List ℕ} {i : ℕ} (h : i < w.length) :
    w.drop i = w.getD i 0 :: w.drop (i + 1) := by
  rw [List.drop_eq_getElem_cons h, List.getD_eq_getElem _ _ h]

private theorem eq_take_append_one {w : List ℕ} {n : ℕ} (hlen : w.length = n) (hn : 1 ≤ n) :
    w = w.take (n - 1) ++ [w.getD (n - 1) 0] := by
  conv_lhs => rw [← List.take_append_drop (n - 1) w]
  rw [drop_eq_getD_cons (by omega), show n - 1 + 1 = n by omega,
    List.drop_eq_nil_of_le (by omega)]

private theorem eq_take_append_two {w : List ℕ} {n : ℕ} (hlen : w.length = n) (hn : 2 ≤ n) :
    w = w.take (n - 2) ++ [w.getD (n - 2) 0, w.getD (n - 1) 0] := by
  conv_lhs => rw [← List.take_append_drop (n - 2) w]
  rw [drop_eq_getD_cons (by omega), drop_eq_getD_cons (by omega),
    show n - 2 + 1 = n - 1 by omega, show n - 1 + 1 = n by omega,
    List.drop_eq_nil_of_le (by omega)]

private theorem eq_take_append_three {w : List ℕ} {n : ℕ} (hlen : w.length = n) (hn : 3 ≤ n) :
    w = w.take (n - 3) ++ [w.getD (n - 3) 0, w.getD (n - 2) 0, w.getD (n - 1) 0] := by
  conv_lhs => rw [← List.take_append_drop (n - 3) w]
  rw [drop_eq_getD_cons (by omega), drop_eq_getD_cons (by omega), drop_eq_getD_cons (by omega),
    show n - 3 + 1 = n - 2 by omega, show n - 2 + 1 = n - 1 by omega,
    show n - 1 + 1 = n by omega, List.drop_eq_nil_of_le (by omega)]

private theorem big_chain {w : List ℕ} {n : ℕ} (hw : w ∈ WA n) :
    ∀ d i, n - 1 - i = d → IsBigEntry w i →
      IsBigEntry w (n - 1) ∨ (IsBigEntry w (n - 2) ∧ w.getD (n - 1) 0 < w.getD (n - 2) 0) := by
  have hlen : w.length = n := (mem_WA_iff.mp hw).1
  intro d
  induction d with
  | zero =>
    intro i hd hbig
    have hin := hbig.2.1
    have : i = n - 1 := by omega
    subst this
    exact Or.inl hbig
  | succ d ih =>
    intro i hd hbig
    have hi1 := hbig.1
    have hin := hbig.2.1
    rcases isBigEntry_succ_or_descent n w hw (i + 1) (by omega) (by omega)
      (by simpa using hbig) with h | ⟨hdesc, hall⟩
    · exact ih (i + 1) (by omega) h
    · by_cases hi : i + 2 = n
      · right
        have e1 : i = n - 2 := by omega
        have e2 : i + 1 = n - 1 := by omega
        subst e1
        rw [e2, show n - 1 - 1 = n - 2 by omega] at hdesc
        exact ⟨hbig, hdesc⟩
      · left
        exact hall n (by omega) le_rfl

/-- If every entry is below the number of weak ascents, there is no big entry. -/
private theorem no_big_of_slack {w : List ℕ} {n : ℕ} (hw : w ∈ WA n)
    (hs : ∀ x ∈ w, x + 1 ≤ wasc w) (i : ℕ) : ¬ IsBigEntry w i := by
  intro hbig
  have hlen : w.length = n := (mem_WA_iff.mp hw).1
  have hin := hbig.2.1
  have hi1 := hbig.1
  rcases big_chain hw _ i rfl hbig with h | ⟨h, hdesc⟩
  · have e := eq_take_append_one hlen (by omega)
    have h1 := wasc_append_singleton_le (w.take (n - 1)) (w.getD (n - 1) 0)
    rw [← e] at h1
    have h2 := hs _ (getD_mem_of_lt (show n - 1 < w.length by omega))
    have h3 := h.2.2
    omega
  · have e := eq_take_append_two hlen (by omega)
    have h1 := wasc_append_pair (w.take (n - 2)) (w.getD (n - 2) 0) (w.getD (n - 1) 0)
    rw [← e, ite_eq_right (by omega)] at h1
    have h2 := wasc_append_singleton_le (w.take (n - 2)) (w.getD (n - 2) 0)
    have h3 := hs _ (getD_mem_of_lt (show n - 2 < w.length by omega))
    have h4 := h.2.2
    omega

/-- Removing a leading zero from a word of `W` with slack. -/
private theorem tail_mem_of_slack {w : List ℕ} {n : ℕ} (hw : w ∈ WA n) (hne : w ≠ [])
    (hs : ∀ x ∈ w, x + 1 ≤ wasc w) :
    ∃ w', w = 0 :: w' ∧ w' ∈ WA (n - 1) ∧ wasc w = wasc w' + 1 := by
  have hnb := no_big_of_slack hw hs
  obtain ⟨hlen, hiw, hav⟩ := mem_WA_iff.mp hw
  obtain ⟨w', rfl⟩ : ∃ w', w = 0 :: w' := by
    cases w with
    | nil => exact absurd rfl hne
    | cons x t =>
      have := hiw.1 (by simp)
      simp only [getElem_cons_zero] at this
      exact ⟨t, by rw [this]⟩
  have hw'ne : w' ≠ [] := by
    rintro rfl
    have := hs 0 (by simp)
    simp [wordWeakAscents] at this
  have hstrict : ∀ i (h : i < w'.length), w'[i] ≤ wasc (0 :: w'.take i) := by
    intro i h
    have hb := hiw.2 (i + 1) (by simp; omega)
    simp only [getElem_cons_succ, take_succ_cons] at hb
    have hnot := hnb (i + 1)
    unfold IsBigEntry at hnot
    simp only [take_succ_cons, getD_cons_succ, List.getD_eq_getElem _ _ h, length_cons] at hnot
    have : ¬ w'[i] = wasc (0 :: take i w') + 1 := fun e => hnot ⟨by omega, by omega, e⟩
    omega
  refine ⟨w', rfl, ?_, wasc_zero_cons hw'ne⟩
  rw [mem_WA_iff]
  refine ⟨by simp at hlen; omega, ⟨fun h => ?_, fun i h => ?_⟩,
    hav.sublist (List.sublist_cons_self 0 w')⟩
  · have := hstrict 0 h
    simp only [take_zero] at this
    simpa [wordWeakAscents] using this
  · have := hstrict i h
    rcases Nat.eq_zero_or_pos i with rfl | hi
    · simp only [take_zero] at this ⊢
      simp only [wordWeakAscents] at this ⊢
      omega
    · rw [wasc_zero_cons (List.ne_nil_of_length_pos (by rw [List.length_take]; omega))] at this
      exact this

private theorem pair_sublist_append_singleton {a b x : ℕ} {l : List ℕ}
    (h : [a, b] <+ l ++ [x]) : [a, b] <+ l ∨ (a ∈ l ∧ b = x) := by
  obtain ⟨l₁, l₂, he, h₁, h₂⟩ := List.sublist_append_iff.mp h
  rcases List.sublist_singleton.mp h₂ with rfl | rfl
  · simp only [append_nil] at he
    exact Or.inl (he ▸ h₁)
  · rcases l₁ with _ | ⟨a', _ | ⟨b', l⟩⟩
    · simp at he
    · simp only [singleton_append, cons.injEq, and_true] at he
      obtain ⟨rfl, rfl⟩ := he
      exact Or.inr ⟨List.singleton_sublist.mp h₁, rfl⟩
    · simp at he

private theorem lastDescentTop_eq_sub_one {w : List ℕ} {n : ℕ} (hlen : w.length = n)
    (hn : 2 ≤ n) (h : w.getD (n - 1) 0 < w.getD (n - 2) 0) : lastDescentTop w = n - 1 := by
  unfold lastDescentTop
  apply le_antisymm
  · apply Finset.sup_le
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_range] at hi
    omega
  · have hmem : n - 2 ∈ (Finset.range (w.length - 1)).filter
        (fun i => w.getD (i + 1) 0 < w.getD i 0) := by
      simp only [Finset.mem_filter, Finset.mem_range]
      refine ⟨by omega, ?_⟩
      rwa [show n - 2 + 1 = n - 1 by omega]
    calc n - 1 = n - 2 + 1 := by omega
      _ ≤ _ := Finset.le_sup (f := fun i => i + 1) hmem

private theorem lastDescentTop_eq_sub_two {w : List ℕ} {n : ℕ} (hlen : w.length = n)
    (hn : 3 ≤ n) (h1 : w.getD (n - 2) 0 < w.getD (n - 3) 0)
    (h2 : ¬ w.getD (n - 1) 0 < w.getD (n - 2) 0) : lastDescentTop w = n - 2 := by
  unfold lastDescentTop
  apply le_antisymm
  · apply Finset.sup_le
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_range] at hi
    have : i ≠ n - 2 := by
      rintro rfl
      rw [show n - 2 + 1 = n - 1 by omega] at hi
      exact h2 hi.2
    change i + 1 ≤ n - 2
    omega
  · have hmem : n - 3 ∈ (Finset.range (w.length - 1)).filter
        (fun i => w.getD (i + 1) 0 < w.getD i 0) := by
      simp only [Finset.mem_filter, Finset.mem_range]
      refine ⟨by omega, ?_⟩
      rwa [show n - 3 + 1 = n - 2 by omega]
    calc n - 2 = n - 3 + 1 := by omega
      _ ≤ _ := Finset.le_sup (f := fun i => i + 1) hmem

private theorem not_last_desc_of_lastDescentTop {w : List ℕ} {n : ℕ} (hlen : w.length = n)
    (hn : 2 ≤ n) (h : lastDescentTop w = n - 2) : ¬ w.getD (n - 1) 0 < w.getD (n - 2) 0 := by
  intro hd
  have := lastDescentTop_eq_sub_one hlen hn hd
  omega

private theorem desc_eq_zero_of_all_zero : ∀ {v : List ℕ}, (∀ x ∈ v, x = 0) → desc v = 0
  | [], _ => rfl
  | [_], _ => rfl
  | a :: b :: t, h => by
    have ha := h a (by simp)
    have hb := h b (by simp)
    subst ha hb
    rw [desc_cons_cons, desc_eq_zero_of_all_zero (fun x hx => h x (List.mem_cons_of_mem _ hx))]
    simp

/-- `0`, then `v`, then the largest allowed value and that value minus one. -/
private def uWord (v : List ℕ) : List ℕ := (0 :: v) ++ [wasc (0 :: v) + 1, wasc (0 :: v)]

private theorem uWord_injective : Function.Injective uWord := by
  intro v v' h
  have := List.append_inj_left' h rfl
  simpa using this

private theorem getD_append_at {l t : List ℕ} {i : ℕ} :
    (l ++ t).getD (l.length + i) 0 = t.getD i 0 := by
  rw [List.getD_append_right _ _ _ _ (by omega)]
  congr 1
  omega

private theorem exists_ne_zero_of_desc {v : List ℕ} (hd : 1 ≤ desc v) : ∃ x ∈ v, x ≠ 0 := by
  by_contra h
  push Not at h
  have := desc_eq_zero_of_all_zero h
  omega

private theorem eq_zero_cons_of_mem {w : List ℕ} {n : ℕ} (hw : w ∈ WA n) (hn : 1 ≤ n) :
    ∃ t, w = 0 :: t := by
  obtain ⟨hlen, hiw, -⟩ := mem_WA_iff.mp hw
  cases w with
  | nil => simp at hlen; omega
  | cons x t =>
    have := hiw.1 (by simp)
    simp only [getElem_cons_zero] at this
    exact ⟨t, by rw [this]⟩

private theorem uWord_mem {n : ℕ} {v : List ℕ} (hv : v ∈ WA (n - 3)) (hd : 1 ≤ desc v) :
    uWord v ∈ quadrupleUSet n 1 := by
  obtain ⟨hlenv, hiw, -⟩ := mem_WA_iff.mp hv
  have hv2 : 2 ≤ v.length := by
    by_contra h
    have : desc v = 0 := by
      match v, h with
      | [], _ => rfl
      | [_], _ => rfl
      | _ :: _ :: _, h => simp at h
    omega
  have hN : 1 ≤ n - 3 := by omega
  have hvle := entry_le_wasc hiw
  have hvne : v ≠ [] := List.ne_nil_of_length_pos (by omega)
  have hw0 : wasc (0 :: v) = wasc v + 1 := wasc_zero_cons hvne
  have hwd := wasc_add_desc v
  have hle0 : ∀ x ∈ 0 :: v, x ≤ wasc v := by
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact Nat.zero_le _
    · exact hvle x hx
  have h0v : 0 :: v ∈ WA (1 + (n - 3)) := by
    simpa using replicate_zero_append_mem hv hN 1
  have h1 : (0 :: v) ++ [wasc (0 :: v) + 1] ∈ WA (1 + (n - 3) + 1) := by
    refine append_mem_WA h0v (by omega) le_rfl (fun a b hs hbad => ?_)
    have ha := hle0 a (hs.subset (by simp))
    have hb := hle0 b (hs.subset (by simp))
    unfold Bad at hbad
    omega
  have h2 : ((0 :: v) ++ [wasc (0 :: v) + 1]) ++ [wasc (0 :: v)] ∈
      WA (1 + (n - 3) + 1 + 1) := by
    refine append_mem_WA h1 (by omega) ?_ (fun a b hs hbad => ?_)
    · have := wasc_le_append (0 :: v) [wasc (0 :: v) + 1]
      omega
    · rcases pair_sublist_append_singleton hs with h | ⟨ha, rfl⟩
      · have ha := hle0 a (h.subset (by simp))
        have hb := hle0 b (h.subset (by simp))
        unfold Bad at hbad
        omega
      · have ha := hle0 a ha
        unfold Bad at hbad
        omega
  have hwe : uWord v = ((0 :: v) ++ [wasc (0 :: v) + 1]) ++ [wasc (0 :: v)] := by
    simp [uWord]
  have hlen : (uWord v).length = n := by simp [uWord]; omega
  have hpos : (0 :: v).length = n - 2 := by simp; omega
  have g1 : (uWord v).getD (n - 2) 0 = wasc (0 :: v) + 1 := by
    rw [uWord, ← hpos, show (0 :: v).length = (0 :: v).length + 0 from rfl, getD_append_at]
    rfl
  have g2 : (uWord v).getD (n - 1) 0 = wasc (0 :: v) := by
    rw [uWord, show n - 1 = (0 :: v).length + 1 by simp; omega, getD_append_at]
    rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hwe, show n = 1 + (n - 3) + 1 + 1 by omega]
    exact h2
  · exact lastDescentTop_eq_sub_one hlen (by omega) (by rw [g1, g2]; omega)
  · refine ⟨n - 2, by omega, by omega, by rw [hlen]; omega, ?_⟩
    rw [g1, uWord, List.take_left' hpos]
  · obtain ⟨x, hx, hx0⟩ := exists_ne_zero_of_desc hd
    obtain ⟨q, hq, rfl⟩ := List.getElem_of_mem hx
    refine ⟨q + 1, by omega, ?_⟩
    rw [uWord, List.getD_append _ _ _ _ (by simp; omega), getD_cons_succ,
      List.getD_eq_getElem _ _ hq]
    exact hx0
  · rw [g1]
    omega
  · rw [g1, g2]

private theorem exists_uWord {n : ℕ} {w : List ℕ} (hw : w ∈ quadrupleUSet n 1) :
    ∃ v, (v ∈ WA (n - 3) ∧ 1 ≤ desc v) ∧ uWord v = w := by
  obtain ⟨hwW, -, ⟨i, hi, hbig⟩, ⟨p, hp, hpz⟩, hne, heq⟩ := hw
  obtain ⟨hlen, hiw, hav⟩ := mem_WA_iff.mp hwW
  have hn3 : 3 ≤ n := by omega
  have e2 := eq_take_append_two hlen (by omega)
  have hbigM : IsBigEntry w (n - 2) := by
    rcases big_chain hwW _ i rfl hbig with h | ⟨h, -⟩
    · exfalso
      have h1 := h.2.2
      have e1 := eq_take_append_one hlen (by omega)
      have hMmem : w.getD (n - 2) 0 ∈ w.take (n - 1) := by
        rw [List.getD_eq_getElem _ _ (by omega)]
        rw [List.mem_iff_getElem]
        exact ⟨n - 2, by simp; omega, by simp⟩
      have := entry_le_wasc (iwas_take hiw (n - 1)) _ hMmem
      omega
    · exact h
  have hMu : w.getD (n - 2) 0 = wasc (w.take (n - 2)) + 1 := hbigM.2.2
  have hu : w.take (n - 2) ∈ WA (n - 2) := take_mem_WA hwW (by omega)
  have hule : ∀ x ∈ w.take (n - 2), x ≤ wasc (w.take (n - 2)) :=
    entry_le_wasc (mem_WA_iff.mp hu).2.1
  have hx : w.getD p 0 ∈ w.take (n - 2) := by
    rw [List.getD_eq_getElem _ _ (by omega), List.mem_iff_getElem]
    exact ⟨p, by simp; omega, by simp⟩
  have hM2 : 2 ≤ w.getD (n - 2) 0 := by
    have := hule _ hx
    omega
  obtain ⟨t, ht⟩ := eq_zero_cons_of_mem hwW (by omega)
  have hut : w.take (n - 2) = 0 :: t.take (n - 3) := by
    rw [ht, show n - 2 = n - 3 + 1 by omega, List.take_succ_cons]
  have hyu : w.getD (n - 1) 0 ∉ w.take (n - 2) := by
    intro hyu
    have hy0 : w.getD (n - 1) 0 ≠ 0 := by omega
    rw [hut] at hyu
    have hyt : w.getD (n - 1) 0 ∈ t.take (n - 3) :=
      (List.mem_cons.mp hyu).resolve_left hy0
    have hsub : [0, w.getD (n - 1) 0] <+ w.take (n - 2) := by
      rw [hut]
      exact (List.singleton_sublist.mpr hyt).cons_cons 0
    have hsub3 : [0, w.getD (n - 1) 0, w.getD (n - 1) 0] <+ w := by
      have hy : [w.getD (n - 1) 0] <+ [w.getD (n - 2) 0, w.getD (n - 1) 0] :=
        List.singleton_sublist.mpr (List.mem_cons_of_mem _ (List.mem_singleton_self _))
      have := hsub.append hy
      rw [← e2] at this
      exact this
    exact hav hsub3 (Or.inl ⟨by omega, rfl⟩)
  have hs : ∀ x ∈ w.take (n - 2), x + 1 ≤ wasc (w.take (n - 2)) := by
    intro x hx'
    have := hule x hx'
    have : x ≠ w.getD (n - 1) 0 := fun e => hyu (e ▸ hx')
    omega
  have hune : w.take (n - 2) ≠ [] := by rw [hut]; simp
  obtain ⟨v, huv, hv, hwv⟩ := tail_mem_of_slack hu hune hs
  have hvlen : v.length = n - 3 := by
    have := (mem_WA_iff.mp hv).1
    omega
  have hvne : v ≠ [] := by
    rintro rfl
    rw [huv] at hwv
    simp [wordWeakAscents] at hwv
  have hvpos := List.length_pos_of_ne_nil hvne
  refine ⟨v, ⟨by rw [show n - 3 = n - 2 - 1 by omega]; exact hv, ?_⟩, ?_⟩
  · by_contra h0
    have hd0 : desc v = 0 := by omega
    have := wasc_add_desc v
    omega
  · rw [uWord, ← huv, show wasc (w.take (n - 2)) = w.getD (n - 1) 0 by omega,
      show w.getD (n - 1) 0 + 1 = w.getD (n - 2) 0 by omega]
    exact e2.symm

private theorem quadrupleUSet_eq_image (n : ℕ) :
    quadrupleUSet n 1 = uWord '' {v | v ∈ WA (n - 3) ∧ 1 ≤ desc v} := by
  ext w
  constructor
  · intro hw
    exact exists_uWord hw
  · rintro ⟨v, ⟨hv, hd⟩, rfl⟩
    exact uWord_mem hv hd

private theorem ncard_eq_sum_fibers {α β : Type*} {S : Set α} (hS : S.Finite)
    (f : α → β) (t : Finset β) (ht : ∀ x ∈ S, f x ∈ t) :
    S.ncard = ∑ k ∈ t, {x | x ∈ S ∧ f x = k}.ncard := by
  classical
  rw [← hS.coe_toFinset, Set.ncard_coe_finset,
    Finset.card_eq_sum_card_fiberwise (f := f) (t := t) (fun x hx => ht x (by simpa using hx))]
  apply Finset.sum_congr rfl
  intro k _
  rw [← Set.ncard_coe_finset]
  congr 1
  ext x
  simp

private theorem WA_finite (N : ℕ) : (WA N).Finite := by
  apply (finite_bounded_lists N N).subset
  intro v hv
  obtain ⟨hlen, hiw, -⟩ := mem_WA_iff.mp hv
  refine ⟨hlen.le, fun x hx => ?_⟩
  have := entry_le_wasc hiw x hx
  have := wasc_le_length v
  omega

private theorem ncard_U_eq_sum (n : ℕ) :
    (quadrupleUSet n 1).ncard = ∑ k ∈ Finset.Icc 1 (n - 4), dcount (n - 3) k := by
  have hfin : {v | v ∈ WA (n - 3) ∧ 1 ≤ desc v}.Finite :=
    (WA_finite (n - 3)).subset (fun v hv => hv.1)
  rw [quadrupleUSet_eq_image, Set.ncard_image_of_injective _ uWord_injective,
    ncard_eq_sum_fibers hfin desc (Finset.Icc 1 (n - 4))]
  · apply Finset.sum_congr rfl
    intro k hk
    have hk' := Finset.mem_Icc.mp hk
    rw [← ncard_WA_desc (by omega)]
    congr 1
    ext v
    constructor
    · rintro ⟨⟨hv, -⟩, rfl⟩
      exact ⟨hv, rfl⟩
    · rintro ⟨hv, rfl⟩
      exact ⟨⟨hv, hk'.1⟩, rfl⟩
  · rintro v ⟨hv, hd⟩
    have := wasc_add_desc v
    have hl := (mem_WA_iff.mp hv).1
    simp only [Finset.mem_Icc]
    omega

private theorem card_U (n : ℕ) :
    (quadrupleUSet n 1).ncard = ∑ k ∈ Finset.Icc 1 (n / 3 - 1),
      (Nat.choose (n - k - 4) (2 * k) * 2 ^ (n - 3 * k - 4) +
        Nat.choose (n - k - 4) (2 * k - 1) * 2 ^ (n - 3 * k - 3)) := by
  rw [ncard_U_eq_sum]
  have h1 : ∑ k ∈ Finset.Icc 1 (n - 4), dcount (n - 3) k =
      ∑ k ∈ Finset.Icc 1 (n - 4), (Nat.choose (n - k - 4) (2 * k) * 2 ^ (n - 3 * k - 4) +
        Nat.choose (n - k - 4) (2 * k - 1) * 2 ^ (n - 3 * k - 3)) := by
    apply Finset.sum_congr rfl
    intro k hk
    simp only [Finset.mem_Icc] at hk
    unfold dcount
    rw [ite_eq_right (by omega : ¬ k = 0), show n - 3 - 1 - k = n - k - 4 by omega,
      show n - k - 4 - 2 * k = n - 3 * k - 4 by omega,
      show n - k - 4 - (2 * k - 1) = n - 3 * k - 3 by omega]
  rw [h1]
  symm
  apply Finset.sum_subset
  · intro k hk
    simp only [Finset.mem_Icc] at hk ⊢
    omega
  · intro k hk hk'
    simp only [Finset.mem_Icc, not_and, not_le] at hk hk'
    have h3 : n < 3 * k + 3 := by
      have := hk' hk.1
      omega
    rw [Nat.choose_eq_zero_of_lt (by omega), Nat.choose_eq_zero_of_lt (by omega)]
    simp

private theorem wasc_append_of_le {u : List ℕ} (hu : u ≠ []) {x : ℕ} (h : ∀ y ∈ u, y ≤ x) :
    wasc (u ++ [x]) = wasc u + 1 := by
  have e := List.dropLast_append_getLast hu
  have hlast := h _ (List.getLast_mem hu)
  rw [← e, List.append_assoc, singleton_append, wasc_append_pair, ite_eq_left hlast]

/-- Removing `t` leading zeros from a word of `W` with enough slack. -/
private theorem strip_zeros : ∀ (t : ℕ) {u : List ℕ} {N : ℕ}, u ∈ WA N → u ≠ [] →
    (∀ z ∈ u, z + t ≤ wasc u) →
      ∃ v, u = replicate t 0 ++ v ∧ v ∈ WA (N - t) ∧ wasc u = wasc v + t ∧ v ≠ []
  | 0, u, N, hu, hne, _ => ⟨u, rfl, by simpa using hu, rfl, hne⟩
  | t + 1, u, N, hu, hne, hs => by
    obtain ⟨u', rfl, hu', hw⟩ :=
      tail_mem_of_slack hu hne (fun z hz => by have := hs z hz; omega)
    have hu'ne : u' ≠ [] := by
      rintro rfl
      have := hs 0 (by simp)
      simp [wordWeakAscents] at this
    obtain ⟨v, rfl, hv, hwv, hvne⟩ := strip_zeros t hu' hu'ne (fun z hz => by
      have := hs z (List.mem_cons_of_mem _ hz)
      omega)
    refine ⟨v, by simp [replicate_succ], by simpa [Nat.sub_sub, Nat.add_comm] using hv, by omega,
      hvne⟩

/-- `s` zeros, then `v`, then `c + 1`, `c` and `c + 1 + j`, where `c = wasc (0 :: v)`. -/
private def vWord (s j : ℕ) (v : List ℕ) : List ℕ :=
  (replicate s 0 ++ v) ++ [wasc (0 :: v) + 1, wasc (0 :: v), wasc (0 :: v) + 1 + j]

private theorem vWord_mem {n s j N : ℕ} {v : List ℕ} (hs : 1 ≤ s) (hv : v ∈ WA N) (hN : 1 ≤ N)
    (hn : n = s + N + 3) (hj : 1 ≤ j) (hjs : j + (if desc v = 0 then 1 else 0) ≤ s) :
    vWord s j v ∈ quadrupleVSet n 1 := by
  obtain ⟨hlenv, hiw, -⟩ := mem_WA_iff.mp hv
  have hvne : v ≠ [] := List.ne_nil_of_length_pos (by omega)
  have hvle := entry_le_wasc hiw
  have hw0 : wasc (0 :: v) = wasc v + 1 := wasc_zero_cons hvne
  have hwd := wasc_add_desc v
  have hu : replicate s 0 ++ v ∈ WA (s + N) := replicate_zero_append_mem hv hN s
  have hune : replicate s 0 ++ v ≠ [] := by simp [hvne]
  have hwu : wasc (replicate s 0 ++ v) = s - 1 + wasc (0 :: v) := wasc_replicate_zero_append hs v
  have hule : ∀ x ∈ replicate s 0 ++ v, x ≤ wasc v := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · rw [List.eq_of_mem_replicate hx]
      exact Nat.zero_le _
    · exact hvle x hx
  have h1 : (replicate s 0 ++ v) ++ [wasc (0 :: v) + 1] ∈ WA (s + N + 1) := by
    refine append_mem_WA hu (by omega) (by omega) (fun a b hs' hbad => ?_)
    have ha := hule a (hs'.subset (by simp))
    have hb := hule b (hs'.subset (by simp))
    unfold Bad at hbad
    omega
  have hw1 : wasc ((replicate s 0 ++ v) ++ [wasc (0 :: v) + 1]) = s + wasc (0 :: v) := by
    rw [wasc_append_of_le hune (fun y hy => by have := hule y hy; omega)]
    omega
  have h2 : ((replicate s 0 ++ v) ++ [wasc (0 :: v) + 1]) ++ [wasc (0 :: v)] ∈
      WA (s + N + 1 + 1) := by
    refine append_mem_WA h1 (by omega) (by omega) (fun a b hs' hbad => ?_)
    rcases pair_sublist_append_singleton hs' with h | ⟨ha, rfl⟩
    · have ha := hule a (h.subset (by simp))
      have hb := hule b (h.subset (by simp))
      unfold Bad at hbad
      omega
    · have ha := hule a ha
      unfold Bad at hbad
      omega
  have hle2 : ∀ x ∈ ((replicate s 0 ++ v) ++ [wasc (0 :: v) + 1]) ++ [wasc (0 :: v)],
      x ≤ wasc (0 :: v) + 1 := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · rcases List.mem_append.mp hx with hx | hx
      · have := hule x hx
        omega
      · rw [List.mem_singleton.mp hx]
    · rw [List.mem_singleton.mp hx]
      omega
  have h3 : (((replicate s 0 ++ v) ++ [wasc (0 :: v) + 1]) ++ [wasc (0 :: v)]) ++
      [wasc (0 :: v) + 1 + j] ∈ WA (s + N + 1 + 1 + 1) := by
    refine append_mem_WA h2 (by omega) ?_ (fun a b hs' hbad => ?_)
    · have := wasc_le_append ((replicate s 0 ++ v) ++ [wasc (0 :: v) + 1]) [wasc (0 :: v)]
      omega
    · have ha := hle2 a (hs'.subset (by simp))
      have hb := hle2 b (hs'.subset (by simp))
      unfold Bad at hbad
      omega
  have hwe : vWord s j v = (((replicate s 0 ++ v) ++ [wasc (0 :: v) + 1]) ++
      [wasc (0 :: v)]) ++ [wasc (0 :: v) + 1 + j] := by
    simp [vWord]
  have hulen : (replicate s 0 ++ v).length = n - 3 := by simp; omega
  have hlen : (vWord s j v).length = n := by simp [vWord]; omega
  have g3 : (vWord s j v).getD (n - 3) 0 = wasc (0 :: v) + 1 := by
    rw [vWord, show n - 3 = (List.replicate s (0 : ℕ) ++ v).length + 0 by omega,
      getD_append_at]
    rfl
  have g2 : (vWord s j v).getD (n - 2) 0 = wasc (0 :: v) := by
    rw [vWord, show n - 2 = (List.replicate s (0 : ℕ) ++ v).length + 1 by omega,
      getD_append_at]
    rfl
  have g1 : (vWord s j v).getD (n - 1) 0 = wasc (0 :: v) + 1 + j := by
    rw [vWord, show n - 1 = (List.replicate s (0 : ℕ) ++ v).length + 2 by omega,
      getD_append_at]
    rfl
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hwe, show n = s + N + 1 + 1 + 1 by omega]
    exact h3
  · exact lastDescentTop_eq_sub_two hlen (by omega) (by rw [g2, g3]; omega)
      (by rw [g1, g2]; omega)
  · rw [g1]
    split_ifs at hjs with hd <;> omega
  · rw [g2]
    omega
  · rw [g3, g2]

private theorem exists_vWord {n : ℕ} {w : List ℕ} (hw : w ∈ quadrupleVSet n 1) :
    ∃ s j v, 1 ≤ s ∧ v ∈ WA (n - 3 - s) ∧ 1 ≤ n - 3 - s ∧ 1 ≤ j ∧
      j + (if desc v = 0 then 1 else 0) ≤ s ∧ vWord s j v = w := by
  obtain ⟨hwW, hldt, hy3, hne, heq⟩ := hw
  obtain ⟨hlen, hiw, hav⟩ := mem_WA_iff.mp hwW
  have hw00 : w.getD 0 0 = 0 := by
    cases w with
    | nil => rfl
    | cons a t =>
      have := hiw.1 (by simp)
      simpa using this
  have hn4 : 4 ≤ n := by
    by_contra h
    rcases Nat.lt_or_ge n 3 with h3 | h3
    · rw [show n - 2 = 0 by omega, hw00] at hne
      exact hne rfl
    · rw [show n - 3 = 0 by omega, hw00] at heq
      omega
  have e3 := eq_take_append_three hlen (by omega)
  have hnd := not_last_desc_of_lastDescentTop hlen (by omega) hldt
  obtain ⟨t, ht⟩ := eq_zero_cons_of_mem hwW (by omega)
  have hut : w.take (n - 3) = 0 :: t.take (n - 4) := by
    rw [ht, show n - 3 = n - 4 + 1 by omega, List.take_succ_cons]
  -- a triple made of `0`, a later entry of the prefix and an entry of the suffix
  have triple0 : ∀ a b : ℕ, a ∈ w.take (n - 3) → a ≠ 0 →
      [b] <+ [w.getD (n - 3) 0, w.getD (n - 2) 0, w.getD (n - 1) 0] → [0, a, b] <+ w := by
    intro a b ha ha0 hb
    rw [hut] at ha
    have hat : a ∈ t.take (n - 4) := (List.mem_cons.mp ha).resolve_left ha0
    have hsub : [0, a] <+ w.take (n - 3) := by
      rw [hut]
      exact (List.singleton_sublist.mpr hat).cons_cons 0
    have := hsub.append hb
    rw [← e3] at this
    exact this
  have hM2 : 2 ≤ w.getD (n - 3) 0 := by omega
  have hlt : ∀ z ∈ w.take (n - 3), z < w.getD (n - 3) 0 := by
    intro z hz
    by_contra hge
    rcases Nat.eq_or_lt_of_le (Nat.le_of_not_lt hge) with he | hgt
    · have := triple0 z (w.getD (n - 3) 0) hz (by omega)
        (List.singleton_sublist.mpr (by simp))
      rw [← he] at this
      exact hav this (Or.inl ⟨by omega, rfl⟩)
    · have h2 : [w.getD (n - 3) 0, w.getD (n - 2) 0] <+
          [w.getD (n - 3) 0, w.getD (n - 2) 0, w.getD (n - 1) 0] :=
        List.sublist_append_left [w.getD (n - 3) 0, w.getD (n - 2) 0] [w.getD (n - 1) 0]
      have hs3 : [z, w.getD (n - 3) 0, w.getD (n - 2) 0] <+ w := by
        have := (List.singleton_sublist.mpr hz).append h2
        rw [← e3] at this
        exact this
      exact hav hs3 (Or.inr ⟨by omega, by omega⟩)
  have hxu : w.getD (n - 2) 0 ∉ w.take (n - 3) := by
    intro hx
    have := triple0 _ (w.getD (n - 2) 0) hx hne (List.singleton_sublist.mpr (by simp))
    exact hav this (Or.inl ⟨by omega, rfl⟩)
  have hzero : 0 ∈ w.take (n - 3) := by rw [hut]; simp
  have hyx : w.getD (n - 1) 0 ≠ w.getD (n - 2) 0 := by
    intro he
    have hs3 : [0, w.getD (n - 2) 0, w.getD (n - 1) 0] <+ w := by
      have := (List.singleton_sublist.mpr hzero).append
        (by simp : [w.getD (n - 2) 0, w.getD (n - 1) 0] <+
          [w.getD (n - 3) 0, w.getD (n - 2) 0, w.getD (n - 1) 0])
      rw [← e3] at this
      exact this
    exact hav hs3 (Or.inl ⟨by omega, he.symm⟩)
  have hyM : w.getD (n - 1) 0 ≠ w.getD (n - 3) 0 := by
    intro he
    have hs3 : [0, w.getD (n - 3) 0, w.getD (n - 1) 0] <+ w := by
      have := (List.singleton_sublist.mpr hzero).append
        (by simp : [w.getD (n - 3) 0, w.getD (n - 1) 0] <+
          [w.getD (n - 3) 0, w.getD (n - 2) 0, w.getD (n - 1) 0])
      rw [← e3] at this
      exact this
    exact hav hs3 (Or.inl ⟨by omega, he.symm⟩)
  have hu : w.take (n - 3) ∈ WA (n - 3) := take_mem_WA hwW (by omega)
  have hbM : w.getD (n - 3) 0 ≤ wasc (w.take (n - 3)) + 1 := by
    have := hiw.2 (n - 3) (by omega)
    rwa [← List.getD_eq_getElem _ 0] at this
  have htake : w.take (n - 1) = w.take (n - 3) ++ [w.getD (n - 3) 0, w.getD (n - 2) 0] := by
    conv_lhs => rw [e3]
    rw [List.take_append, List.take_of_length_le (by simp; omega)]
    simp only [length_take, hlen]
    rw [show n - 1 - min (n - 3) n = 2 by omega]
    rfl
  have hby : w.getD (n - 1) 0 ≤ wasc (w.take (n - 3)) + 2 := by
    have := hiw.2 (n - 1) (by omega)
    rw [← List.getD_eq_getElem _ 0, htake, wasc_append_pair,
      ite_eq_right (by omega)] at this
    have := wasc_append_singleton_le (w.take (n - 3)) (w.getD (n - 3) 0)
    omega
  have hune : w.take (n - 3) ≠ [] := by rw [hut]; simp
  obtain ⟨v, huv, hv, hwv, hvne⟩ := strip_zeros (wasc (w.take (n - 3)) + 2 - w.getD (n - 3) 0)
    hu hune (fun z hz => by
      have := hlt z hz
      have : z ≠ w.getD (n - 2) 0 := fun e => hxu (e ▸ hz)
      omega)
  have hvlen : v.length = n - 3 - (wasc (w.take (n - 3)) + 2 - w.getD (n - 3) 0) :=
    (mem_WA_iff.mp hv).1
  have hvpos := List.length_pos_of_ne_nil hvne
  have hw0 : wasc (0 :: v) = wasc v + 1 := wasc_zero_cons hvne
  refine ⟨wasc (w.take (n - 3)) + 2 - w.getD (n - 3) 0, w.getD (n - 1) 0 - w.getD (n - 3) 0, v,
    by omega, hv, by omega, by omega, ?_, ?_⟩
  · split_ifs with hd
    · have := wasc_add_desc v
      omega
    · omega
  · rw [vWord, ← huv]
    conv_rhs => rw [e3]
    congr 1
    simp only [cons.injEq, and_true]
    omega

private theorem desc_append_of_le {u : List ℕ} (hu : u ≠ []) {x : ℕ} (h : ∀ y ∈ u, y ≤ x) :
    desc (u ++ [x]) = desc u := by
  have e := List.dropLast_append_getLast hu
  have hlast := h _ (List.getLast_mem hu)
  rw [← e, List.append_assoc, singleton_append, desc_append_pair, ite_eq_right (by omega)]
  rfl

private theorem vWord_length (s j : ℕ) (v : List ℕ) :
    (vWord s j v).length = s + v.length + 3 := by
  simp [vWord]
  omega

private theorem vWord_getD (s j : ℕ) (v : List ℕ) :
    (vWord s j v).getD (s + v.length) 0 = wasc (0 :: v) + 1 := by
  rw [vWord, show s + v.length = (List.replicate s (0 : ℕ) ++ v).length + 0 by simp,
    getD_append_at]
  rfl

private theorem vWord_desc {s j : ℕ} {v : List ℕ} (hv : IsWeakAscentSeq v) (hvne : v ≠ []) :
    desc (vWord s j v) = desc v + 1 := by
  have hvle := entry_le_wasc hv
  have hw0 : wasc (0 :: v) = wasc v + 1 := wasc_zero_cons hvne
  have hule : ∀ x ∈ replicate s 0 ++ v, x ≤ wasc (0 :: v) + 1 := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · rw [List.eq_of_mem_replicate hx]
      exact Nat.zero_le _
    · have := hvle x hx
      omega
  have e : vWord s j v = ((replicate s 0 ++ v) ++ [wasc (0 :: v) + 1]) ++
      [wasc (0 :: v), wasc (0 :: v) + 1 + j] := by
    simp [vWord]
  rw [e, desc_append_pair, ite_eq_right (by omega), List.append_assoc, singleton_append,
    desc_append_pair, ite_eq_left (by omega), desc_append_of_le (by simp [hvne]) hule,
    desc_replicate_zero_append]

private theorem card_V_fiber (n a k : ℕ) (ha : 2 ≤ a) :
    {w | w ∈ quadrupleVSet n 1 ∧ (w.getD (n - 3) 0, desc w - 1) = (a, k)}.ncard =
      dcount (a + k - 1) k * (n - a - k - 2 - if k = 0 then 1 else 0) := by
  have key : {w | w ∈ quadrupleVSet n 1 ∧ (w.getD (n - 3) 0, desc w - 1) = (a, k)} =
      (fun q : List ℕ × ℕ => vWord (n - a - k - 2) q.2 q.1) ''
        ({v | v ∈ WA (a + k - 1) ∧ desc v = k} ×ˢ
          Set.Icc 1 (n - a - k - 2 - if k = 0 then 1 else 0)) := by
    ext w
    constructor
    · rintro ⟨hw, hg⟩
      obtain ⟨s, j, v, hs, hv, hN, hj, hjs, rfl⟩ := exists_vWord hw
      obtain ⟨hlenv, hiw, -⟩ := mem_WA_iff.mp hv
      have hvne : v ≠ [] := List.ne_nil_of_length_pos (by omega)
      have hw0 : wasc (0 :: v) = wasc v + 1 := wasc_zero_cons hvne
      have hwd := wasc_add_desc v
      have hlenw := vWord_length s j v
      have hpos : n - 3 = s + v.length := by
        have := (mem_WA_iff.mp (hw.1)).1
        omega
      rw [Prod.mk.injEq, hpos, vWord_getD, vWord_desc hiw hvne] at hg
      obtain ⟨ha', hk'⟩ := hg
      have hN' : v.length = a + k - 1 := by omega
      have hs' : s = n - a - k - 2 := by omega
      refine ⟨(v, j), ⟨⟨?_, ?_⟩, ?_⟩, by rw [hs']⟩
      · change v ∈ WA (a + k - 1)
        rw [← hN']
        exact mem_WA_iff.mpr ⟨rfl, hiw, (mem_WA_iff.mp hv).2.2⟩
      · change desc v = k
        omega
      · change j ∈ Set.Icc 1 (n - a - k - 2 - if k = 0 then 1 else 0)
        simp only [Set.mem_Icc]
        split_ifs at hjs ⊢ <;> omega
    · rintro ⟨⟨v, j⟩, ⟨⟨hv, hd⟩, hj⟩, rfl⟩
      change v ∈ WA (a + k - 1) at hv
      change desc v = k at hd
      change j ∈ Set.Icc 1 (n - a - k - 2 - if k = 0 then 1 else 0) at hj
      simp only [Set.mem_Icc] at hj
      obtain ⟨hlenv, hiw, -⟩ := mem_WA_iff.mp hv
      have hvne : v ≠ [] := List.ne_nil_of_length_pos (by omega)
      have hw0 : wasc (0 :: v) = wasc v + 1 := wasc_zero_cons hvne
      have hwd := wasc_add_desc v
      have hs1 : 1 ≤ n - a - k - 2 := by split_ifs at hj <;> omega
      refine ⟨vWord_mem hs1 hv (by omega) (by omega) hj.1 (by rw [hd]; split_ifs at hj ⊢ <;> omega),
        ?_⟩
      simp only
      rw [show n - 3 = n - a - k - 2 + v.length by omega, vWord_getD, vWord_desc hiw hvne]
      simp only [Prod.mk.injEq]
      omega
  rw [key, Set.InjOn.ncard_image, Set.ncard_prod, ncard_WA_desc (by omega)]
  · congr 1
    rw [← Finset.coe_Icc, Set.ncard_coe_finset, Nat.card_Icc]
    omega
  · rintro ⟨v, j⟩ ⟨⟨hv, -⟩, -⟩ ⟨v', j'⟩ ⟨⟨hv', -⟩, -⟩ he
    simp only at he
    have hl : (replicate (n - a - k - 2) 0 ++ v).length =
        (replicate (n - a - k - 2) 0 ++ v').length := by
      simp [(mem_WA_iff.mp hv).1, (mem_WA_iff.mp hv').1]
    obtain ⟨h1, h2⟩ := List.append_inj he hl
    have hvv : v = v' := List.append_cancel_left h1
    subst hvv
    simp only [cons.injEq, and_true, true_and, Nat.add_left_cancel_iff] at h2
    rw [h2]

private theorem dcount_zero (a : ℕ) : dcount (a + 0 - 1) 0 = 2 ^ (a - 2) := by
  unfold dcount
  simp only [Nat.mul_zero, Nat.choose_zero_right, Nat.one_mul, ite_true, Nat.add_zero,
    Nat.sub_zero]
  congr 1

private theorem dcount_pos {a k : ℕ} (hk : 1 ≤ k) :
    dcount (a + k - 1) k =
      Nat.choose (a - 2) (2 * k) * 2 ^ (a - 2 * k - 2) +
        Nat.choose (a - 2) (2 * k - 1) * 2 ^ (a - 2 * k - 1) := by
  unfold dcount
  rw [ite_eq_right (by omega : ¬ k = 0), show a + k - 1 - 1 - k = a - 2 by omega,
    show a - 2 - 2 * k = a - 2 * k - 2 by omega,
    show a - 2 - (2 * k - 1) = a - 2 * k - 1 by omega]

private theorem card_V (n : ℕ) :
    (quadrupleVSet n 1).ncard =
      ∑ a ∈ Finset.Icc 2 (n - 4), 2 ^ (a - 2) * (n - a - 3) +
        ∑ a ∈ Finset.Icc 2 (n - 4), ∑ k ∈ Finset.Icc 1 (min (n - 3 - a) ((a - 1) / 2)),
          (Nat.choose (a - 2) (2 * k) * 2 ^ (a - 2 * k - 2) +
            Nat.choose (a - 2) (2 * k - 1) * 2 ^ (a - 2 * k - 1)) * (n - k - a - 2) := by
  have hfin : (quadrupleVSet n 1).Finite := (WA_finite n).subset (fun w hw => hw.1)
  rw [ncard_eq_sum_fibers hfin (fun w => (w.getD (n - 3) 0, desc w - 1))
    (Finset.Icc 2 (n - 4) ×ˢ insert 0 (Finset.Icc 1 n))]
  · rw [Finset.sum_product, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro a ha
    have ha' := Finset.mem_Icc.mp ha
    rw [Finset.sum_insert (by simp)]
    congr 1
    · rw [card_V_fiber n a 0 ha'.1, dcount_zero, ite_eq_left (rfl : (0 : ℕ) = 0)]
      congr 1
    · have h1 : ∑ k ∈ Finset.Icc 1 n,
          {w | w ∈ quadrupleVSet n 1 ∧ (w.getD (n - 3) 0, desc w - 1) = (a, k)}.ncard =
          ∑ k ∈ Finset.Icc 1 n, (Nat.choose (a - 2) (2 * k) * 2 ^ (a - 2 * k - 2) +
            Nat.choose (a - 2) (2 * k - 1) * 2 ^ (a - 2 * k - 1)) * (n - k - a - 2) := by
        apply Finset.sum_congr rfl
        intro k hk
        have hk' := Finset.mem_Icc.mp hk
        rw [card_V_fiber n a k ha'.1, dcount_pos hk'.1, ite_eq_right (by omega : ¬ k = 0)]
        congr 1
        omega
      rw [h1]
      symm
      apply Finset.sum_subset
      · intro k hk
        simp only [Finset.mem_Icc] at hk ⊢
        omega
      · intro k hk hk'
        simp only [Finset.mem_Icc, not_and, not_le] at hk hk'
        have := hk' hk.1
        rcases Nat.lt_or_ge (n - 3 - a) k with h | h
        · rw [show n - k - a - 2 = 0 by omega, Nat.mul_zero]
        · have h2 : (a - 1) / 2 < k := by omega
          rw [Nat.choose_eq_zero_of_lt (by omega), Nat.choose_eq_zero_of_lt (by omega)]
          simp
  · intro w hw
    obtain ⟨s, j, v, hs, hv, hN, hj, hjs, rfl⟩ := exists_vWord hw
    obtain ⟨hlenv, hiw, -⟩ := mem_WA_iff.mp hv
    have hvne : v ≠ [] := List.ne_nil_of_length_pos (by omega)
    have hw0 : wasc (0 :: v) = wasc v + 1 := wasc_zero_cons hvne
    have hwd := wasc_add_desc v
    have hpos : n - 3 = s + v.length := by
      have := (mem_WA_iff.mp hw.1).1
      rw [vWord_length] at this
      omega
    simp only [Finset.mem_product, Finset.mem_Icc, Finset.mem_insert]
    rw [hpos, vWord_getD, vWord_desc hiw hvne]
    split_ifs at hjs with hd <;> omega

private theorem sum_two_pow_Icc (m : ℕ) : ∑ a ∈ Finset.Icc 2 (m + 1), 2 ^ (a - 2) + 1 = 2 ^ m := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_Icc_succ_top (by omega), show m + 1 + 1 - 2 = m by omega, pow_succ]
    omega

private theorem sum_two_pow_mul_Icc (m : ℕ) :
    ∑ a ∈ Finset.Icc 2 (m + 1), 2 ^ (a - 2) * (m + 2 - a) + m + 2 = 2 ^ (m + 1) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_Icc_succ_top (by omega), show m + 1 + 1 - 2 = m by omega,
      show m + 1 + 2 - (m + 1 + 1) = 1 by omega]
    have h1 : ∑ a ∈ Finset.Icc 2 (m + 1), 2 ^ (a - 2) * (m + 1 + 2 - a) =
        ∑ a ∈ Finset.Icc 2 (m + 1), 2 ^ (a - 2) * (m + 2 - a) +
          ∑ a ∈ Finset.Icc 2 (m + 1), 2 ^ (a - 2) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro a ha
      have := (Finset.mem_Icc.mp ha).2
      rw [show m + 1 + 2 - a = (m + 2 - a) + 1 by omega]
      ring
    rw [h1]
    have h2 := sum_two_pow_Icc m
    rw [pow_succ (2 : ℕ) (m + 1), pow_succ (2 : ℕ) m] at *
    omega

/-- The first sum in the formula for `V`, evaluated in closed form. -/
private theorem sum_two_pow_mul (n : ℕ) (hn : 4 ≤ n) :
    ∑ a ∈ Finset.Icc 2 (n - 4), 2 ^ (a - 2) * (n - a - 3) + n = 2 ^ (n - 4) + 3 := by
  rcases Nat.eq_or_lt_of_le hn with rfl | hn5
  · simp
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 5 := ⟨n - 5, by omega⟩
    have h := sum_two_pow_mul_Icc m
    have e : ∑ a ∈ Finset.Icc 2 (m + 5 - 4), 2 ^ (a - 2) * (m + 5 - a - 3) =
        ∑ a ∈ Finset.Icc 2 (m + 1), 2 ^ (a - 2) * (m + 2 - a) := by
      rw [show m + 5 - 4 = m + 1 by omega]
      apply Finset.sum_congr rfl
      intro a ha
      rw [show m + 5 - a - 3 = m + 2 - a by omega]
    rw [e, show m + 5 - 4 = m + 1 by omega]
    omega

end quadrupleUSet_quadrupleVSet_card_formulas

open quadrupleUSet_quadrupleVSet_card_formulas in
/-- **Sum formulas for $|U_{n,1}|$ and $|V_{n,1}|$ (Proposition 2).** For every natural number
$n$ let $f(n, a) = \min(n - 3 - a, \lfloor (a - 1)/2 \rfloor)$ and
$$
S(n) = \sum_{a=2}^{n-4} \sum_{k=1}^{f(n,a)} \left( \binom{a-2}{2k} 2^{a-2k-2} +
\binom{a-2}{2k-1} 2^{a-2k-1} \right) (n - k - a - 2).
$$
Then for every $n \ge 1$
$$
|U_{n,1}| = \sum_{k=1}^{\lfloor n/3 \rfloor - 1} \left( \binom{n-k-4}{2k} 2^{n-3k-4} +
\binom{n-k-4}{2k-1} 2^{n-3k-3} \right)
$$
and
$$
|V_{n,1}| = \sum_{a=2}^{n-4} 2^{a-2} (n - a - 3) + S(n),
$$
and for every $n \ge 4$
$$
|V_{n,1}| = 2^{n-4} - n + 3 + S(n).
$$

A sum whose upper limit is below its lower limit is empty, and an exponent such as
$n - 3k - 4$ is negative only where the binomial coefficient multiplying it is $0$; such a
term is $0$. The last formula is stated only for $n \ge 4$: at $n = 3$ the expression
$2^{n-4} - n + 3$ equals $1/2$, while $\sum_{a=2}^{n-4} 2^{a-2} (n - a - 3)$ is $0$.

Source: David Callan and Toufik Mansour, *Ascent Sequences and Weak Ascent Sequences
Avoiding a Quadruple of Length-3 Patterns*, INTEGERS 25 (2025), Article A80,
Proposition 2 (`integers-2025-A80-prop-2`). -/
public theorem quadrupleUSet_quadrupleVSet_card_formulas :
    (∀ n : ℕ, 1 ≤ n →
      (quadrupleUSet n 1).ncard =
        ∑ k ∈ Finset.Icc 1 (n / 3 - 1),
          (Nat.choose (n - k - 4) (2 * k) * 2 ^ (n - 3 * k - 4) +
            Nat.choose (n - k - 4) (2 * k - 1) * 2 ^ (n - 3 * k - 3))) ∧
    (∀ n : ℕ, 1 ≤ n →
      (quadrupleVSet n 1).ncard =
        ∑ a ∈ Finset.Icc 2 (n - 4), 2 ^ (a - 2) * (n - a - 3) +
          ∑ a ∈ Finset.Icc 2 (n - 4), ∑ k ∈ Finset.Icc 1 (min (n - 3 - a) ((a - 1) / 2)),
            (Nat.choose (a - 2) (2 * k) * 2 ^ (a - 2 * k - 2) +
              Nat.choose (a - 2) (2 * k - 1) * 2 ^ (a - 2 * k - 1)) * (n - k - a - 2)) ∧
    ∀ n : ℕ, 4 ≤ n →
      ((quadrupleVSet n 1).ncard : ℤ) =
        2 ^ (n - 4) - n + 3 +
          ∑ a ∈ Finset.Icc 2 (n - 4), ∑ k ∈ Finset.Icc 1 (min (n - 3 - a) ((a - 1) / 2)),
            ((Nat.choose (a - 2) (2 * k) * 2 ^ (a - 2 * k - 2) +
              Nat.choose (a - 2) (2 * k - 1) * 2 ^ (a - 2 * k - 1)) * (n - k - a - 2) : ℕ) := by
  refine ⟨fun n _ => card_U n, fun n _ => card_V n, fun n hn => ?_⟩
  have h := sum_two_pow_mul n hn
  rw [card_V n]
  generalize ∑ a ∈ Finset.Icc 2 (n - 4), 2 ^ (a - 2) * (n - a - 3) = A at h ⊢
  have hA : (A : ℤ) = 2 ^ (n - 4) - n + 3 := by
    have : ((A + n : ℕ) : ℤ) = ((2 ^ (n - 4) + 3 : ℕ) : ℤ) := by rw [h]
    push_cast at this
    linarith
  rw [Nat.cast_add, hA, Nat.cast_sum]

end MetaMathlibExt

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Set.Card
public import MathlibExt.Combinatorics.Enumerative.AscentSequenceQuadruplePatterns
import Mathlib.Data.List.Basic

/-!
# Weak-ascent Wilf equivalence in Class 205

Reversing and complementing a decreasing segment gives a length-preserving bijection
between the two families of weak ascent sequences in Class 205. The segment starts at
the first maximum and ends at the last smaller letter. Avoidance forces it to be weakly
decreasing. If the maximum occurs again after the segment, only its two endpoint values
can occur in the segment.
-/

namespace MetaMathlibExt
namespace weakAscent_wilf_class205

open List

private def patterns : Bool → Finset (List ℕ)
  | false => {[1, 0, 0], [1, 0, 2], [1, 2, 0], [2, 0, 1]}
  | true => {[1, 0, 2], [1, 1, 0], [1, 2, 0], [2, 0, 1]}

private def Bad (side : Bool) (a b c : ℕ) : Prop :=
  (b < a ∧ a < c) ∨ (c < a ∧ a < b) ∨ (b < c ∧ c < a) ∨
    (if side then a = b ∧ c < a else b = c ∧ b < a)

private def Avoid (side : Bool) (w : List ℕ) : Prop :=
  ∀ ⦃a b c⦄, [a, b, c] <+ w → ¬ Bad side a b c

private theorem contains_triple {w : List ℕ} {x y z : ℕ} :
    ContainsPattern w [x, y, z] ↔ ∃ a b c, [a, b, c] <+ w ∧
      ((a < b ↔ x < y) ∧ (b < a ↔ y < x) ∧ (a < c ↔ x < z) ∧ (c < a ↔ z < x) ∧
        (b < c ↔ y < z) ∧ (c < b ↔ z < y)) := by
  constructor
  · rintro ⟨s, hs, hl, ho⟩
    obtain ⟨a, b, c, rfl⟩ : ∃ a b c, s = [a, b, c] := by
      exact List.length_eq_three.mp hl
    refine ⟨a, b, c, hs, ?_⟩
    simp only [length_cons, length_nil, Nat.forall_lt_succ_left] at ho
    simpa [List.getD, and_assoc, and_left_comm, and_comm] using ho
  · rintro ⟨a, b, c, hs, ho⟩
    refine ⟨[a, b, c], hs, rfl, ?_⟩
    simp only [length_cons, length_nil, Nat.forall_lt_succ_left]
    simpa [List.getD, and_assoc, and_left_comm, and_comm] using ho

private theorem avoid_iff (s : Bool) (w : List ℕ) :
    (∀ p ∈ patterns s, ¬ ContainsPattern w p) ↔ Avoid s w := by
  cases s <;> simp [patterns, contains_triple, Avoid, Bad] <;> grind

private theorem Avoid.sub {s : Bool} {u w : List ℕ} (h : Avoid s w) (hs : u <+ w) :
    Avoid s u := fun _ _ _ ht => h (ht.trans hs)

private theorem avoid_cons_min {s : Bool} {a : ℕ} {w : List ℕ} (h : Avoid s w)
    (hm : ∀ x ∈ w, a ≤ x) : Avoid s (a :: w) := by
  intro b c d ht
  rcases List.cons_sublist_cons'.mp ht with ht' | ⟨rfl, hpair⟩
  · exact h ht'
  · have hc := hm c (hpair.subset (by simp))
    have hd := hm d (hpair.subset (by simp))
    cases s <;> simp [Bad] <;> omega

private theorem avoid_prepend {s : Bool} {p w : List ℕ} (hp : p.Pairwise (· ≤ ·))
    (hle : ∀ x ∈ p, ∀ y ∈ w, x ≤ y) (hw : Avoid s w) : Avoid s (p ++ w) := by
  induction p with
  | nil => exact hw
  | cons a p ih =>
    obtain ⟨ha, hp⟩ := pairwise_cons.mp hp
    apply avoid_cons_min (ih hp (fun _ hx => hle _ (.tail _ hx)))
    simpa only [mem_append, or_imp, forall_and] using
      ⟨ha, hle a (.head _)⟩

/-- Split at the first maximum and remove the final copies of that maximum.
The remaining segment starts at the maximum and ends at the last smaller letter. -/
private def turn (w : List ℕ) : List ℕ :=
  let H := w.max?.getD 0
  let p := w.takeWhile (· != H)
  let r := (w.dropWhile (· != H)).tail.reverse
  match r.dropWhile (· == H) with
  | [] => w
  | m :: v => p ++ H :: (v.map (H + m - ·) ++ m :: r.takeWhile (· == H))

private def block (H m : ℕ) (v : List ℕ) : List ℕ := H :: (v ++ [m])

private theorem max_eq {p v : List ℕ} {H : ℕ} (hp : ∀ a ∈ p, a < H)
    (hv : ∀ a ∈ v, a ≤ H) : (p ++ H :: v).max? = some H := by
  apply List.max?_eq_some_iff.mpr
  exact ⟨by simp, by simpa only [mem_append, mem_cons, or_imp, forall_and,
    forall_eq, le_refl, true_and] using And.intro (fun a ha => (hp a ha).le) hv⟩

private theorem turn_flat (p : List ℕ) (H k : ℕ) (hp : ∀ a ∈ p, a < H) :
    turn (p ++ H :: replicate k H) = p ++ H :: replicate k H := by
  have h := max_eq hp (v := replicate k H) (by simp +contextual)
  have hp' : ∀ a ∈ p, (a != H) = true := by simpa using fun a ha => (hp a ha).ne
  simp [turn, h, dropWhile_append_of_pos hp']

private theorem turn_block (p v : List ℕ) (H m k : ℕ) (hp : ∀ a ∈ p, a < H)
    (hm : m < H) (hv : ∀ a ∈ v, a ≤ H) :
    turn (p ++ (block H m v ++ replicate k H)) =
      p ++ (block H m (v.reverse.map (H + m - ·)) ++ replicate k H) := by
  have h := max_eq (v := (v ++ [m]) ++ replicate k H) hp (by
    simp only [mem_append, mem_singleton, mem_replicate]
    grind)
  have hp' : ∀ a ∈ p, (a != H) = true := by simpa using fun a ha => (hp a ha).ne
  have hk : ∀ a ∈ replicate k H, (a == H) = true := by simp +contextual
  simp only [turn, block, cons_append, h, Option.getD_some, dropWhile_append_of_pos hp',
    takeWhile_append_of_pos hp']
  simp [reverse_append, dropWhile_append_of_pos hk, takeWhile_append_of_pos hk, hm.ne]

private theorem triple_append {a b c : ℕ} {u v : List ℕ} :
    [a, b, c] <+ u ++ v ↔ [a, b, c] <+ u ∨ ([a, b] <+ u ∧ c ∈ v) ∨
      (a ∈ u ∧ [b, c] <+ v) ∨ [a, b, c] <+ v := by
  rw [sublist_append_iff]
  simp [cons_eq_append_iff, or_and_right, exists_or, and_assoc, or_comm, or_left_comm, or_assoc]

private theorem pair_append {a b : ℕ} {u v : List ℕ} :
    [a, b] <+ u ++ v ↔ [a, b] <+ u ∨ (a ∈ u ∧ b ∈ v) ∨ [a, b] <+ v := by
  rw [sublist_append_iff]
  simp [cons_eq_append_iff, or_and_right, exists_or, and_assoc, or_comm, or_left_comm]

private theorem sorted_before_max {s : Bool} {p tail : List ℕ} {H : ℕ}
    (hp : ∀ a ∈ p, a < H) (hw : Avoid s (p ++ H :: tail)) : p.Pairwise (· ≤ ·) := by
  apply pairwise_of_forall_sublist
  intro a b hab
  have h := hw (triple_append.mpr (Or.inr (Or.inl ⟨hab, mem_cons_self⟩)))
  have ha := hp a (hab.subset (by simp))
  dsimp [Bad] at h
  omega

private theorem split_tail (H : ℕ) (l : List ℕ) :
    (∃ k, l = replicate k H) ∨
      ∃ v m k, m ≠ H ∧ l = (v ++ [m]) ++ replicate k H := by
  induction l with
  | nil => exact .inl ⟨0, rfl⟩
  | cons a l ih =>
    obtain ⟨k, rfl⟩ | ⟨v, m, k, hm, rfl⟩ := ih
    · by_cases ha : a = H
      · exact .inl ⟨k + 1, by simp [replicate_succ, ha]⟩
      · exact .inr ⟨[], a, k, ha, rfl⟩
    · exact .inr ⟨a :: v, m, k, hm, rfl⟩

/-- The first maximum and the last smaller letter bound the decreasing block.
A later return to the maximum forces the block to use only its two endpoints. -/
private theorem block_constraints {s : Bool} {p v : List ℕ} {H m k : ℕ}
    (hp : ∀ a ∈ p, a < H) (hm : m < H) (hv : ∀ a ∈ v, a ≤ H)
    (hw : Avoid s (p ++ (block H m v ++ replicate k H))) :
    (∀ x ∈ p, x ≤ m) ∧ (∀ x ∈ v, m ≤ x) ∧ v.Pairwise (· ≥ ·) ∧
      (k ≠ 0 → ∀ x ∈ v, x = m ∨ x = H) := by
  have hb : Avoid s (block H m v) :=
    (hw.sub (sublist_append_right ..)).sub (sublist_append_left ..)
  have hlow (x) (hx : x ∈ v) : m ≤ x := by
    have ht : [H, x, m] <+ block H m v := by
      apply Sublist.cons_cons
      exact pair_append.mpr (.inr (.inl ⟨hx, by simp⟩))
    have := hb ht
    dsimp [Bad] at this
    omega
  refine ⟨?_, hlow, pairwise_of_forall_sublist ?_, ?_⟩
  · intro x hx
    have ht : [H, m] <+ block H m v := by simp [block]
    have h := hw (triple_append.mpr (.inr (.inr (.inl
      ⟨hx, sublist_append_of_sublist_left ht⟩))))
    have := hp x hx
    dsimp [Bad] at h
    omega
  · intro a b hab
    have ha := hlow a (hab.subset (by simp))
    have hb' := hv b (hab.subset (by simp))
    -- A rise below the maximum gives 201. A rise back to the maximum gives 120,
    -- unless it starts at the minimum, in which case 100 or 110 occurs.
    have h₁ := hb (Sublist.cons_cons H (sublist_append_of_sublist_left hab))
    have h₂ := hb ((triple_append.mpr (.inr (.inl ⟨hab, (by simp : m ∈ [m])⟩))).cons H)
    have h₃ := hb (Sublist.cons_cons H
      (pair_append.mpr (.inr (.inl ⟨hab.subset (by simp : a ∈ [a, b]), (by simp : m ∈ [m])⟩))))
    have h₄ := hb (Sublist.cons_cons H
      (pair_append.mpr (.inr (.inl ⟨hab.subset (by simp : b ∈ [a, b]), (by simp : m ∈ [m])⟩))))
    cases s <;> simp only [Bad, Bool.false_eq_true, ite_false, ite_true] at * <;> omega
  · intro hk x hx
    have hpair : [x, m] <+ block H m v :=
      (pair_append.mpr (.inr (.inl ⟨hx, by simp⟩))).cons H
    have ht := hw.sub (sublist_append_right ..)
    have h := ht (triple_append.mpr (.inr (.inl ⟨hpair, mem_replicate.mpr ⟨hk, rfl⟩⟩)))
    have := hv x hx
    have := hlow x hx
    dsimp [Bad] at h
    omega

private def reflect (H m : ℕ) (v : List ℕ) := v.reverse.map (H + m - ·)

private theorem reflect_block (H m : ℕ) (v : List ℕ) :
    reflect H m (block H m v) = block H m (reflect H m v) := by
  simp [reflect, block, reverse_append]

private theorem reflect_twice {H m : ℕ} {v : List ℕ} (hv : ∀ x ∈ v, x ≤ H) :
    reflect H m (reflect H m v) = v := by
  simp only [reflect, map_reverse, reverse_reverse, map_map]
  conv_rhs => rw [← map_id v]
  apply map_congr_left
  intro x hx
  simp only [Function.comp_apply, id_eq]
  have := hv x hx
  omega

private theorem avoid_reflect {s : Bool} {H m : ℕ} {u : List ℕ}
    (hu : u.Pairwise (· ≥ ·)) (hmax : ∀ x ∈ u, x ≤ H) (hw : Avoid s u) :
    Avoid (!s) (reflect H m u) := by
  intro a b c ht
  obtain ⟨l, hl, he⟩ := sublist_map_iff.mp ht
  obtain ⟨x, y, z, rfl⟩ : ∃ x y z, l = [x, y, z] := by
    apply length_eq_three.mp
    simpa using (congrArg length he).symm
  have hs : [z, y, x] <+ u := by simpa using sublist_reverse_iff.mp hl
  have hb := hw hs
  have hd := hu.sublist hs
  have hle := fun t (ht : t ∈ [z, y, x]) => hmax t (hs.subset ht)
  have hx := hle x (by simp)
  have hy := hle y (by simp)
  have hz := hle z (by simp)
  simp at hd
  simp only [map_cons, map_nil, cons.injEq, and_true] at he
  cases s <;> simp [Bad] at hb ⊢ <;> omega

private theorem avoid_attach_max {s : Bool} {H m k : ℕ} {u : List ℕ} (hm : m ≤ H)
    (hu : Avoid s u) (hb : k ≠ 0 → ∀ x ∈ u, x = m ∨ x = H) :
    Avoid s (u ++ replicate k H) := by
  intro a b c ht
  rcases triple_append.mp ht with ht | ⟨hab, hc⟩ | ⟨ha, hbc⟩ | ht
  · exact hu ht
  · obtain ⟨hk, rfl⟩ := mem_replicate.mp hc
    have := hb hk a (hab.subset (by simp))
    have := hb hk b (hab.subset (by simp))
    cases s <;> simp [Bad] <;> omega
  · obtain ⟨hk, rfl⟩ := mem_replicate.mp (hbc.subset (by simp : b ∈ [b, c]))
    have := eq_of_mem_replicate (hbc.subset (by simp : c ∈ [b, c]))
    have := hb hk a ha
    cases s <;> simp [Bad] <;> omega
  · have := eq_of_mem_replicate (ht.subset (by simp : a ∈ [a, b, c]))
    have := eq_of_mem_replicate (ht.subset (by simp : b ∈ [a, b, c]))
    have := eq_of_mem_replicate (ht.subset (by simp : c ∈ [a, b, c]))
    cases s <;> simp [Bad] <;> omega

private theorem weakAscents_le_append (p v : List ℕ) :
    wordWeakAscents p ≤ wordWeakAscents (p ++ v) := by
  induction p using wordWeakAscents.induct with
  | case1 => exact Nat.zero_le _
  | case2 => exact Nat.zero_le _
  | case3 a b p ih => simpa only [cons_append, wordWeakAscents, Nat.add_le_add_iff_left] using ih

/-- Once a permitted maximum has appeared, any continuation bounded by it
satisfies the weak-ascent inequalities. -/
private theorem weak_replace {p w v : List ℕ} {H : ℕ} (hw : IsWeakAscentSeq (p ++ H :: w))
    (hv : ∀ x ∈ v, x ≤ H) : IsWeakAscentSeq (p ++ H :: v) := by
  have hH := hw.2 p.length (by simp)
  simp only [getElem_append_right le_rfl, Nat.sub_self, getElem_cons_zero, take_append_length] at hH
  rw [← singleton_append (x := H) (l := w), ← append_assoc] at hw
  rw [← singleton_append (x := H) (l := v), ← append_assoc]
  let q := p ++ [H]
  change IsWeakAscentSeq (q ++ w) at hw
  change IsWeakAscentSeq (q ++ v)
  have hq : 0 < q.length := by simp [q]
  constructor
  · intro _
    have hz := hw.1 (by simp; omega)
    rw [getElem_append_left hq] at hz ⊢
    exact hz
  · intro i hi
    by_cases hl : i < q.length
    · have h := hw.2 i (by simp; omega)
      rw [getElem_append_left hl, take_append_of_le_length hl.le] at h ⊢
      exact h
    · rw [getElem_append_right (by omega : q.length ≤ i)]
      have hi' : i - q.length < v.length := by simp only [length_append] at hi; omega
      have hx := hv _ (getElem_mem hi')
      have hp : p <+: (q ++ v).take i := by
        apply prefix_take_iff.mpr
        refine ⟨(prefix_append p [H]).trans (prefix_append q v), ?_⟩
        simp [q] at hl
        omega
      obtain ⟨r, hr⟩ := hp
      rw [← hr]
      have := weakAscents_le_append p r
      omega

private theorem turn_on_block {s : Bool} {p v : List ℕ} {H m k : ℕ}
    (hp : ∀ a ∈ p, a < H) (hm : m < H) (hv : ∀ a ∈ v, a ≤ H)
    (hw : Avoid s (p ++ (block H m v ++ replicate k H)))
    (hweak : IsWeakAscentSeq (p ++ (block H m v ++ replicate k H))) :
    let w := p ++ (block H m v ++ replicate k H)
    (turn w).length = w.length ∧ IsWeakAscentSeq (turn w) ∧ Avoid (!s) (turn w) ∧
      turn (turn w) = w := by
  obtain ⟨hpre, hmin, hdec, hbinary⟩ := block_constraints hp hm hv hw
  have href : ∀ x ∈ reflect H m v, m ≤ x ∧ x ≤ H := by
    intro x hx
    obtain ⟨a, ha, rfl⟩ := mem_map.mp hx
    rw [mem_reverse] at ha
    have := hmin a ha
    have := hv a ha
    omega
  have he := turn_block p v H m k hp hm hv
  change turn _ = p ++ (block H m (reflect H m v) ++ replicate k H) at he
  dsimp only
  rw [he]
  refine ⟨by simp [block, reflect], weak_replace hweak ?_, ?_, ?_⟩
  · change ∀ x ∈ (reflect H m v ++ [m]) ++ replicate k H, x ≤ H
    simp only [mem_append, mem_singleton, mem_replicate]
    grind
  · apply avoid_prepend (sorted_before_max hp hw)
    · simp only [block, mem_append, mem_cons, mem_nil_iff, or_false, mem_replicate]
      grind
    · apply avoid_attach_max hm.le
      · rw [← reflect_block]
        apply avoid_reflect
        · simpa [block, pairwise_append, or_imp, forall_and, and_assoc] using
            (show (∀ a ∈ v, H ≥ a) ∧ H ≥ m ∧ v.Pairwise (· ≥ ·) ∧ ∀ a ∈ v, a ≥ m from
              ⟨hv, hm.le, hdec, hmin⟩)
        · simp only [block, mem_cons, mem_append]
          grind
        · exact (hw.sub (sublist_append_right ..)).sub (sublist_append_left ..)
      · intro hk x hx
        simp only [block, mem_cons, mem_append, mem_nil_iff, or_false, reflect, mem_map,
          mem_reverse] at hx
        obtain rfl | ⟨y, hy, rfl⟩ | rfl := hx
        · exact .inr rfl
        · rcases hbinary hk y hy with rfl | rfl <;> omega
        · exact .inl rfl
  · rw [turn_block _ _ _ _ _ hp hm (fun x hx => (href x hx).2)]
    rw [← reflect, reflect_twice hv]

private theorem turn_spec {s : Bool} {w : List ℕ} (hw : Avoid s w) (hweak : IsWeakAscentSeq w) :
    (turn w).length = w.length ∧ IsWeakAscentSeq (turn w) ∧ Avoid (!s) (turn w) ∧
      turn (turn w) = w := by
  by_cases hn : w = []
  · subst w
    refine ⟨rfl, hweak, ?_, rfl⟩
    intro a b c h
    change [a, b, c] <+ [] at h
    cases h
  let H := w.max hn
  obtain ⟨p, tail, he, hnot⟩ := eq_append_cons_of_mem (max_mem hn)
  change w = p ++ H :: tail at he
  change H ∉ p at hnot
  have hmax : ∀ a ∈ p ++ H :: tail, a ≤ H := by
    rw [← he]
    exact fun _ ha => le_max_of_mem ha
  have hp : ∀ a ∈ p, a < H := by
    intro a ha
    exact lt_of_le_of_ne (hmax a (mem_append_left _ ha)) (fun h => hnot (h ▸ ha))
  rw [he] at hw hweak ⊢
  obtain ⟨k, rfl⟩ | ⟨v, m, k, hne, rfl⟩ := split_tail H tail
  · rw [turn_flat _ _ _ hp]
    refine ⟨rfl, hweak, avoid_prepend (sorted_before_max hp hw) ?_ ?_, turn_flat _ _ _ hp⟩
    · intro x hx y hy
      have := hp x hx
      simp only [mem_cons, mem_replicate] at hy
      omega
    · intro a b c ht
      have hall : ∀ x ∈ H :: replicate k H, x = H := by simp +contextual
      have := hall a (ht.subset (by simp))
      have := hall b (ht.subset (by simp))
      have := hall c (ht.subset (by simp))
      cases s <;> simp [Bad] <;> omega
  · apply turn_on_block hp _ _ hw hweak
    · exact lt_of_le_of_ne (hmax m (by simp)) hne
    · exact fun x hx => hmax x (by simp [hx])

end weakAscent_wilf_class205

open weakAscent_wilf_class205

/-- **Weak-ascent Wilf equivalence in Class 205.** For every natural number $n$, the number of
weak ascent sequences of length $n$ avoiding every pattern in $\{100, 102, 120, 201\}$ equals the
number avoiding every pattern in $\{102, 110, 120, 201\}$.

That is, the two sets are WA-Wilf equivalent.

Source: David Callan and Toufik Mansour, *Ascent Sequences and Weak Ascent Sequences
Avoiding a Quadruple of Length-3 Patterns*, INTEGERS 25 (2025), Article A80,
Theorem 9 (`integers-2025-A80-thm-9`). -/
public theorem weakAscent_wilf_class205 (n : ℕ) :
    (weakAscentAvoiders {[1, 0, 0], [1, 0, 2], [1, 2, 0], [2, 0, 1]} n).ncard =
      (weakAscentAvoiders {[1, 0, 2], [1, 1, 0], [1, 2, 0], [2, 0, 1]} n).ncard := by
  have maps (s : Bool) (w : List ℕ) (hw : w ∈ weakAscentAvoiders (patterns s) n) :
      turn w ∈ weakAscentAvoiders (patterns (!s)) n ∧ turn (turn w) = w := by
    obtain ⟨hlen, hweak, hav⟩ := hw
    obtain ⟨hl, hs, ha, hi⟩ := turn_spec ((avoid_iff s w).mp hav) hweak
    exact ⟨⟨hl.trans hlen, hs, (avoid_iff ..).mpr ha⟩, hi⟩
  apply Set.ncard_congr'
  exact {
    toFun := fun w => ⟨turn w, (maps false w w.property).1⟩
    invFun := fun w => ⟨turn w, (maps true w w.property).1⟩
    left_inv := fun w => Subtype.ext (maps false w w.property).2
    right_inv := fun w => Subtype.ext (maps true w w.property).2 }

end MetaMathlibExt

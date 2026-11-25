/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Sups
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination

/-!
# The bound for 2-intersecting families of half-size sets

`twoIntersectingHalfSetsBound_holds` proves the sharp bound in Erdős Problem 83.
Take a maximum shifted family and shorten the prefix witnessing its intersections one point
at a time. If a point beyond the first half is essential, averaging over compatible traces
gives a larger family. Applying the same argument to complements in reverse order excludes
all sets meeting the first half in exactly half their elements.

Source: T. F. Bloom, Erdős Problems, Problem #83, https://www.erdosproblems.com/83 (status PROVED
(LEAN)). UnsolvedMath record UM-30006715 (`EP-83`), dataset ulamai/UnsolvedMath v1.8.0.

The bound is stated without division or truncated subtraction as `2 |F| + C(2n, n)² ≤ C(4n, 2n)`
(`C(4n, 2n) - C(2n, n)²` is even). It is attained by the `2n`-sets with at least `n + 1` elements in
`[2n]`. Compared with the formal-conjectures statement `ErdosProblems/83.lean` (equivalent; no code
imported).
-/

@[expose] public section

namespace MathlibExt.Combinatorics.TwoIntersectingHalfSetsErdosProblem83Wanted

/-- **Erdős Problem 83.** The assertion that, for every natural number $n$, every family $F$ of
$2n$-element subsets of $\{0, \dots, 4n-1\}$ such that $|A \cap B| \ge 2$ for all $A, B \in F$
(including $A = B$) satisfies $2|F| + \binom{2n}{n}^2 \le \binom{4n}{2n}$, that is,
$|F| \le \frac{1}{2}\left(\binom{4n}{2n} - \binom{2n}{n}^2\right)$. -/
def twoIntersectingHalfSetsBound : Prop :=
  ∀ (n : ℕ) (F : Finset (Finset (Fin (4 * n)))), (∀ A ∈ F, A.card = 2 * n) →
    (∀ A ∈ F, ∀ B ∈ F, 2 ≤ (A ∩ B).card) →
      2 * F.card + (2 * n).choose n ^ 2 ≤ (4 * n).choose (2 * n)

open Finset

variable {α : Type*} [DecidableEq α] [Fintype α]

private def TwoIntersectingOn (P : Finset α) (F : Finset (Finset α)) : Prop :=
  ∀ A ∈ F, ∀ B ∈ F, 2 ≤ ((A ∩ P) ∩ (B ∩ P)).card

private def HasMaximumCard (k : ℕ) (F : Finset (Finset α)) : Prop :=
  ∀ H : Finset (Finset α), (H : Set (Finset α)).Sized k → TwoIntersectingOn univ H → H.card ≤ F.card

private def Shifted (r : α → ℕ) (F : Finset (Finset α)) : Prop :=
  ∀ A ∈ F, ∀ x ∈ A, ∀ y ∉ A, r y < r x → insert y (A.erase x) ∈ F

-- The k-sets whose intersection with P is exactly T.
private def layer (k : ℕ) (P T : Finset α) : Finset (Finset α) :=
  (univ.powersetCard k).filter (fun A ↦ A ∩ P = T)

private lemma mem_layer {k : ℕ} {P T A : Finset α} :
    A ∈ layer k P T ↔ A.card = k ∧ A ∩ P = T := by simp [layer]

private lemma card_layer {k : ℕ} {P T : Finset α} (hT : T ⊆ P) (hk : T.card ≤ k) :
    (layer k P T).card = Pᶜ.card.choose (k - T.card) := by
  rw [← card_powersetCard]
  apply card_nbij' (fun A ↦ A \ P) (fun U ↦ U ∪ T)
  · intro A hA
    obtain ⟨ha, ht⟩ := mem_layer.mp hA
    refine mem_powersetCard.mpr ⟨by intro a ha; simpa using (mem_sdiff.mp ha).2, ?_⟩
    dsimp
    have he := card_sdiff_add_card_inter A P
    rw [ht, ha] at he
    omega
  · intro U hU
    obtain ⟨hu, hc⟩ := mem_powersetCard.mp hU
    have hd : Disjoint U P := disjoint_left.mpr (fun a ha ↦ mem_compl.mp (hu ha))
    apply mem_layer.mpr
    rw [card_union_of_disjoint (hd.mono_right hT), hc, union_inter_distrib_right,
      disjoint_iff_inter_eq_empty.mp hd, inter_eq_left.mpr hT, empty_union]
    exact ⟨by omega, rfl⟩
  · intro A hA
    dsimp
    rw [← (mem_layer.mp hA).2, sdiff_union_inter]
  · intro U hU
    have hu := (mem_powersetCard.mp hU).1
    ext a
    simp only [mem_sdiff, mem_union]
    exact ⟨fun h ↦ h.1.resolve_right (fun ht ↦ h.2 (hT ht)),
      fun h ↦ ⟨Or.inl h, mem_compl.mp (hu h)⟩⟩

-- A conflicting pair of traces must cover the prefix. Otherwise a shift replaces the
-- distinguished common element by a prefix element outside both sets.
omit [Fintype α] in
private lemma conflict {P A B : Finset α} {F : Finset (Finset α)} {x : α} {r : α → ℕ}
    (hg : TwoIntersectingOn (insert x P) F) (hs : Shifted r F) (hx : x ∉ P)
    (hr : ∀ y ∈ P, r y < r x) (ha : A ∈ F) (hb : B ∈ F)
    (h : ((A ∩ P) ∩ (B ∩ P)).card < 2) :
    x ∈ A ∧ x ∈ B ∧ ((A ∩ P) ∩ (B ∩ P)).card = 1 ∧ (A ∩ P) ∪ (B ∩ P) = P := by
  have hg' := hg _ ha _ hb
  have e : (A ∩ insert x P) ∩ (B ∩ insert x P) =
      if x ∈ A ∧ x ∈ B then insert x ((A ∩ P) ∩ (B ∩ P)) else (A ∩ P) ∩ (B ∩ P) := by
    split_ifs <;> ext y <;> simp_all only [mem_inter, mem_insert] <;> grind
  rw [e] at hg'
  split_ifs at hg' with hab
  · have hn : x ∉ (A ∩ P) ∩ (B ∩ P) := by simp [hx]
    rw [card_insert_of_notMem hn] at hg'
    refine ⟨hab.1, hab.2, by omega, Subset.antisymm
      (union_subset inter_subset_right inter_subset_right) ?_⟩
    intro y hy
    by_contra h'
    have hya : y ∉ A := fun hya ↦ h' (mem_union_left _ (mem_inter.mpr ⟨hya, hy⟩))
    have hyb : y ∉ B := fun hyb ↦ h' (mem_union_right _ (mem_inter.mpr ⟨hyb, hy⟩))
    have hz := hg _ (hs _ ha _ hab.1 _ hya (hr _ hy)) _ hb
    have he : ((insert y (A.erase x) ∩ insert x P) ∩ (B ∩ insert x P)) =
        (A ∩ P) ∩ (B ∩ P) := by
      ext a
      simp only [mem_inter, mem_insert, mem_erase]
      grind
    rw [he] at hz
    omega
  · omega

-- Count selections horizontally and vertically to obtain one choice with improved weight.
private lemma improve {β γ : Type*} {I : Finset β} {C : Finset γ} (w v : β → ℕ)
    (pick : γ → β → Prop) [∀ c t, Decidable (pick c t)]
    (hw : ∀ t ∈ I, v t * C.card ≤ w t * (C.filter (pick · t)).card)
    (h : ∃ t ∈ I, v t * C.card < w t * (C.filter (pick · t)).card) :
    ∃ c ∈ C, (∑ t ∈ I, v t) < ∑ t ∈ I.filter (pick c), w t := by
  apply exists_lt_of_sum_lt (f := fun _ ↦ ∑ t ∈ I, v t)
    (g := fun c ↦ ∑ t ∈ I.filter (pick c), w t)
  simp only [sum_const, nsmul_eq_mul, sum_filter]
  rw [sum_comm, Nat.mul_comm, sum_mul]
  simp_rw [← sum_filter, sum_const, nsmul_eq_mul]
  simpa only [Nat.cast_id, mul_comm] using sum_lt_sum hw h

private def choices (d : ℕ) (P : Finset α) := range (2 * d) ×ˢ P

-- A conflicting pair has sizes summing to p + 1. For unequal sizes, give the two
-- traces disjoint intervals at opposite ends of [0, 2d). For equal sizes, both
-- traces cannot omit the same chosen point, since their union is the whole prefix.
private def pick (k p d : ℕ) (c : ℕ × α) (T : Finset α) : Prop :=
  if 2 * T.card < p + 1 then c.1 < 2 * (k - T.card) + 1
  else if p + 1 < 2 * T.card then 2 * d ≤ c.1 + (2 * (k - T.card) + 1)
  else c.2 ∉ T

omit [Fintype α] in
private lemma pick_disjoint {k p d : ℕ} {P T U : Finset α} {c : ℕ × α}
    (hc : c ∈ choices d P) (hd : p + d = 2 * k)
    (ht : T.card ≤ k) (hu : U.card ≤ k)
    (huv : T ∪ U = P) (hcard : T.card + U.card = p + 1)
    (h₁ : pick k p d c T) (h₂ : pick k p d c U) : False := by
  obtain ⟨hq, hy⟩ := mem_product.mp hc
  simp only [mem_range] at hq
  have hmem : c.2 ∈ T ∨ c.2 ∈ U := mem_union.mp (huv ▸ hy)
  unfold pick at h₁ h₂
  split_ifs at h₁ h₂ <;> first | omega | grind

-- A trace of size s that requires the next point occupies a fraction (k - s) / d
-- of its layer. The selection probability strictly exceeds this fraction, including
-- in the equal-size case, where it is (p - s) / p.
open scoped Classical in
omit [DecidableEq α] [Fintype α] in
private lemma count_pick {k p d : ℕ} {P T : Finset α}
    (hp : P.card = p) (hd : p + d = 2 * k) (hk : Even k) (hpk : k ≤ p)
    (hT : T ⊆ P) (ht : T.card < k) (hr : k - T.card < d) :
    (d - 1).choose (k - T.card - 1) * (choices d P).card <
    d.choose (k - T.card) * ((choices d P).filter (pick k p d · T)).card := by
  classical
  let s := T.card
  let b := k - s
  have hb : 0 < b := by dsimp [b, s]; omega
  have hbd : b < d := hr
  have hw : 0 < d.choose b := Nat.choose_pos hbd.le
  have hid : d * (d - 1).choose (b - 1) = d.choose b * b := by
    simpa only [show d - 1 + 1 = d by omega, show b - 1 + 1 = b by omega] using
      Nat.add_one_mul_choose_eq (d - 1) (b - 1)
  have hC : (choices d P).card = 2 * d * p := by simp [choices, hp]
  rw [hC]
  change (d - 1).choose (b - 1) * (2 * d * p) < d.choose b * _
  calc
    _ = d.choose b * (2 * b * p) := by linear_combination (2 * p) * hid
    _ < _ := by
      apply Nat.mul_lt_mul_of_pos_left _ hw
      have low : 2 * b + 1 ≤ 2 * d := by omega
      have hp0 : 0 < p := by dsimp [b, s] at hb; omega
      by_cases hs : 2 * T.card < p + 1
      · have eq : (choices d P).filter (pick k p d · T) = range (2 * b + 1) ×ˢ P := by
          ext c
          simp only [choices, pick, ite_eq_left hs, mem_filter, mem_product, mem_range]
          change (_ ∧ _) ∧ c.1 < 2 * b + 1 ↔ _
          grind
        rw [eq, card_product, card_range, hp]
        nlinarith [hp0]
      by_cases hs' : p + 1 < 2 * T.card
      · have eq : (choices d P).filter (pick k p d · T) =
            Ico (2 * d - (2 * b + 1)) (2 * d) ×ˢ P := by
          ext c
          simp only [choices, pick, ite_eq_right hs, ite_eq_left hs', mem_filter, mem_product,
            mem_range, mem_Ico]
          change (_ ∧ _) ∧ 2 * d ≤ c.1 + (2 * b + 1) ↔ _
          grind
        rw [eq, card_product, Nat.card_Ico, hp]
        have : 2 * d - (2 * d - (2 * b + 1)) = 2 * b + 1 := by omega
        rw [this]
        nlinarith [hp0]
      · have eq : (choices d P).filter (pick k p d · T) = range (2 * d) ×ˢ (P \ T) := by
          ext c
          simp [choices, pick, hs, hs', and_assoc]
        rw [eq, card_product, card_range, card_sdiff_of_subset hT, hp]
        have he : 2 * s = p + 1 := by dsimp [s]; omega
        obtain ⟨m, hm⟩ := hk
        have hpos : k < p := by omega
        have he' : p - T.card + s = p := Nat.sub_add_cancel (hp ▸ card_le_card hT)
        have hb' : b + s = k := Nat.sub_add_cancel ht.le
        nlinarith [show 0 < p - k by omega, Nat.sub_add_cancel hpk]

-- If intersections are already witnessed in a prefix longer than half the ground set,
-- the last element of that prefix is redundant for a maximum shifted family.
private lemma shorten {k : ℕ} {F : Finset (Finset α)} {P : Finset α} {r : α → ℕ} {x : α}
    (hsize : Fintype.card α = 2 * k) (hk : Even k) (hpk : k ≤ P.card) (hx : x ∉ P)
    (hr : ∀ y ∈ P, r y < r x) (hF : (F : Set (Finset α)).Sized k) (hmax : HasMaximumCard k F)
    (hs : Shifted r F) (hg : TwoIntersectingOn (insert x P) F) : TwoIntersectingOn P F := by
  classical
  by_contra hnot
  -- Traces in conflict need the last point in every original extension.
  let I := F.image (· ∩ P)
  let bad (T : Finset α) := ∃ U ∈ I, (T ∩ U).card < 2
  let d := Pᶜ.card
  have hd : P.card + d = 2 * k := by
    simp [d, card_compl, ← hsize, Nat.add_sub_of_le (card_le_univ P)]
  have trace_mem {A : Finset α} (ha : A ∈ F) : A ∩ P ∈ I := mem_image_of_mem _ ha
  have orig {T : Finset α} (ht : T ∈ I) : ∃ A ∈ F, A ∩ P = T := mem_image.mp ht
  have sub {T : Finset α} (ht : T ∈ I) : T ⊆ P := by
    obtain ⟨A, _, rfl⟩ := orig ht
    exact inter_subset_right
  have bound {T : Finset α} (ht : T ∈ I) : T.card ≤ k := by
    obtain ⟨A, ha, rfl⟩ := orig ht
    exact (card_le_card inter_subset_left).trans (hF ha).le
  have clash {T U : Finset α} (ht : T ∈ I) (hu : U ∈ I) (h : (T ∩ U).card < 2) :
      T ∪ U = P ∧ T.card + U.card = P.card + 1 := by
    obtain ⟨A, ha, rfl⟩ := orig ht
    obtain ⟨B, hb, rfl⟩ := orig hu
    obtain ⟨_, _, hi, he⟩ := conflict hg hs hx hr ha hb h
    have hc := card_inter_add_card_union (A ∩ P) (B ∩ P)
    rw [hi, he] at hc
    exact ⟨he, by omega⟩
  have forced {A : Finset α} (ha : A ∈ F) (ht : bad (A ∩ P)) : x ∈ A := by
    obtain ⟨U, hu, ht⟩ := ht
    obtain ⟨B, hb, rfl⟩ := orig hu
    exact (conflict hg hs hx hr ha hb ht).1
  have strict {T : Finset α} (ht : T ∈ I) (hb : bad T) : T.card < k := by
    obtain ⟨A, ha, rfl⟩ := orig ht
    have hn : x ∉ A ∩ P := by simp [hx]
    have hsub : insert x (A ∩ P) ⊆ A := insert_subset (forced ha hb) inter_subset_left
    have he := card_le_card hsub
    rw [card_insert_of_notMem hn, hF ha] at he
    omega
  -- Keep every conflict-free trace and fill the whole layer of each selected trace.
  let accept (c : ℕ × α) (T : Finset α) := ¬bad T ∨ pick k P.card d c T
  let w (T : Finset α) := (layer k P T).card
  let v (T : Finset α) := (F.filter (fun A ↦ A ∩ P = T)).card
  have hv {T : Finset α} (ht : T ∈ I) (hb : bad T) :
      v T ≤ (d - 1).choose (k - T.card - 1) := by
    have hn : x ∉ T := fun hh ↦ hx (sub ht hh)
    have hle : (F.filter (fun A ↦ A ∩ P = T)) ⊆ layer k (insert x P) (insert x T) := by
      intro A ha
      obtain ⟨ha, he⟩ := mem_filter.mp ha
      refine mem_layer.mpr ⟨hF ha, ?_⟩
      have hxa := forced ha (he ▸ hb)
      ext a
      simp only [mem_inter, mem_insert, ← he]
      grind
    have he := card_le_card hle
    rw [card_layer (insert_subset_insert _ (sub ht)) (by
      rw [card_insert_of_notMem hn]; exact strict ht hb)] at he
    have hd' : (insert x P)ᶜ.card = d - 1 := by
      simp only [d, card_compl, card_insert_of_notMem hx]
      omega
    simpa only [hd', card_insert_of_notMem hn, Nat.sub_add_eq] using he
  have gain {T : Finset α} (ht : T ∈ I) (hb : bad T) :
      v T * (choices d P).card < w T * ((choices d P).filter (accept · T)).card := by
    have hsmall : k - T.card < d := by
      obtain ⟨U, hu, hi⟩ := hb
      have he := (clash ht hu hi).2
      have hb' := bound hu
      have ht' := strict ht ⟨U, hu, hi⟩
      omega
    have he := count_pick rfl hd hk hpk (sub ht) (strict ht hb) hsmall
    have hw : w T = d.choose (k - T.card) := card_layer (sub ht) (bound ht)
    simpa [hw, accept, hb] using
      lt_of_le_of_lt (Nat.mul_le_mul_right _ (hv ht hb)) he
  have weak (T : Finset α) (ht : T ∈ I) :
      v T * (choices d P).card ≤ w T * ((choices d P).filter (accept · T)).card := by
    by_cases hb : bad T
    · exact (gain ht hb).le
    · have he : (choices d P).filter (accept · T) = choices d P := by simp [accept, hb]
      rw [he]
      apply Nat.mul_le_mul_right
      apply card_le_card
      intro A ha
      obtain ⟨ha, he⟩ := mem_filter.mp ha
      exact mem_layer.mpr ⟨hF ha, he⟩
  have some_bad : ∃ T ∈ I, bad T := by
    unfold TwoIntersectingOn at hnot
    push Not at hnot
    obtain ⟨A, ha, B, hb, hh⟩ := hnot
    exact ⟨_, trace_mem ha, _, trace_mem hb, hh⟩
  obtain ⟨T, ht, hb⟩ := some_bad
  obtain ⟨c, hc, hgain⟩ :=
    improve (C := choices d P) (I := I) w v accept weak ⟨T, ht, gain ht hb⟩
  let J := I.filter (accept c)
  -- The selected layers give a larger admissible family, contradicting maximality.
  let G := J.biUnion (layer k P)
  have hG {A : Finset α} (hA : A ∈ G) : A.card = k ∧ A ∩ P ∈ J := by
    obtain ⟨T, ht, h⟩ := mem_biUnion.mp hA
    obtain ⟨hk, rfl⟩ := mem_layer.mp h
    exact ⟨hk, ht⟩
  have hgood : TwoIntersectingOn univ G := by
    intro A ha B hb
    simp only [inter_univ]
    apply le_trans _ (card_le_card (show (A ∩ P) ∩ (B ∩ P) ⊆ A ∩ B by
      exact inter_subset_inter inter_subset_left inter_subset_left))
    by_contra! hi
    obtain ⟨ha', h₁⟩ := mem_filter.mp (hG ha).2
    obtain ⟨hb', h₂⟩ := mem_filter.mp (hG hb).2
    have badA : bad (A ∩ P) := ⟨_, hb', hi⟩
    have badB : bad (B ∩ P) := ⟨_, ha', by rwa [inter_comm]⟩
    obtain ⟨hu, hc'⟩ := clash ha' hb' hi
    exact pick_disjoint hc hd (bound ha') (bound hb') hu hc'
      (h₁.resolve_left (not_not_intro badA)) (h₂.resolve_left (not_not_intro badB))
  have he : G.card = ∑ T ∈ J, w T := by
    apply card_biUnion
    intro t _ u _ hne
    exact disjoint_left.mpr fun A ha hb ↦ hne ((mem_layer.mp ha).2.symm.trans (mem_layer.mp hb).2)
  have hf : F.card = ∑ T ∈ I, v T := card_eq_sum_card_image (· ∩ P) F
  have hle := hmax G (fun _ ha ↦ (hG ha).1) hgood
  exact (hf ▸ he ▸ hle).not_gt hgain

private def replacePoint (x y : α) (A : Finset α) := insert y (A.erase x)

omit [Fintype α] in
private lemma card_replace {A : Finset α} {x y : α} (hx : x ∈ A) (hy : y ∉ A) :
    (replacePoint x y A).card = A.card := by
  have h := card_erase_add_one hx
  rwa [replacePoint, card_insert_of_notMem (fun h ↦ hy (mem_of_mem_erase h))]

-- Among the largest families, minimize the sum of the ranks of all their elements.
private lemma exists_shifted_maximum (k : ℕ) (r : α → ℕ) :
    ∃ F : Finset (Finset α), (F : Set (Finset α)).Sized k ∧ TwoIntersectingOn univ F ∧
      HasMaximumCard k F ∧ Shifted r F := by
  classical
  let families := univ.filter (fun F : Finset (Finset α) ↦
    (F : Set (Finset α)).Sized k ∧ TwoIntersectingOn univ F)
  have hne : families.Nonempty := ⟨∅, mem_filter.mpr ⟨mem_univ _, by simp [TwoIntersectingOn]⟩⟩
  obtain ⟨M, hM, hm⟩ := exists_max_image families card hne
  let best := families.filter (fun F ↦ F.card = M.card)
  let weight (A : Finset α) := ∑ a ∈ A, r a
  obtain ⟨F, hF, hmin⟩ := exists_min_image best (fun H ↦ ∑ A ∈ H, weight A)
    ⟨M, mem_filter.mpr ⟨hM, rfl⟩⟩
  obtain ⟨hFam, hcard⟩ := mem_filter.mp hF
  obtain ⟨hsize, hgood⟩ := (mem_filter.mp hFam).2
  refine ⟨F, hsize, hgood, fun H hu hg ↦ hcard ▸ hm H (mem_filter.mpr ⟨mem_univ _, hu, hg⟩), ?_⟩
  intro S hS x hx y hy hyr
  by_contra hfail
  let shift := replacePoint x y
  let moves (A : Finset α) := x ∈ A ∧ y ∉ A ∧ shift A ∉ F
  let f (A : Finset α) := if moves A then shift A else A
  have reverse (A : Finset α) (h : moves A) : replacePoint y x (shift A) = A := by
    obtain ⟨hh, hh', _⟩ := h
    ext a
    simp only [replacePoint, shift, mem_insert, mem_erase]
    grind
  have inj : Set.InjOn f F := by
    intro A ha B hb he
    unfold f at he
    split_ifs at he with hA hB hB
    · rw [← reverse A hA, ← reverse B hB, he]
    · exact (hA.2.2 (he ▸ hb)).elim
    · exact (hB.2.2 (he ▸ ha)).elim
    · exact he
  have unif : ((F.image f) : Set (Finset α)).Sized k := by
    intro B hb
    obtain ⟨A, ha, rfl⟩ := mem_image.mp hb
    dsimp [f]
    split_ifs with h
    · exact (card_replace h.1 h.2.1).trans (hsize ha)
    · exact hsize ha
  have inter (A B : Finset α) : shift A ∩ shift B = shift (A ∩ B) := by
    ext a
    simp only [shift, replacePoint, mem_insert, mem_erase, mem_inter]
    grind
  have good {A B : Finset α} (ha : A ∈ F) (hb : B ∈ F) : 2 ≤ (A ∩ B).card := by
    simpa using hgood _ ha _ hb
  have mixed {A B : Finset α} (ha : A ∈ F) (hb : B ∈ F) (hA : moves A) (hB : ¬ moves B) :
      2 ≤ (shift A ∩ B).card := by
    by_cases hxb : x ∈ B
    · by_cases hyb : y ∈ B
      · have he : shift A ∩ B = shift (A ∩ B) := by
          ext a
          simp only [shift, replacePoint, mem_insert, mem_erase, mem_inter]
          grind
        rw [he, card_replace (mem_inter.mpr ⟨hA.1, hxb⟩) (fun h ↦ hA.2.1 (mem_inter.mp h).1)]
        exact good ha hb
      · have hsb : shift B ∈ F := by_contra (fun hn ↦ hB ⟨hxb, hyb, hn⟩)
        apply (good ha hsb).trans (card_le_card ?_)
        intro a hh
        simp only [shift, replacePoint, mem_insert, mem_erase, mem_inter] at hh ⊢
        have := hA.2.1
        grind
    · apply (good ha hb).trans (card_le_card ?_)
      intro a hh
      simp only [shift, replacePoint, mem_insert, mem_erase, mem_inter] at hh ⊢
      grind
  have hg : TwoIntersectingOn univ (F.image f) := by
    intro A ha B hb
    obtain ⟨A, hA₀, rfl⟩ := mem_image.mp ha
    obtain ⟨B, hB₀, rfl⟩ := mem_image.mp hb
    simp only [inter_univ, f]
    split_ifs with hA hB hB
    · rw [inter, card_replace (mem_inter.mpr ⟨hA.1, hB.1⟩) (fun h ↦ hA.2.1 (mem_inter.mp h).1)]
      exact good hA₀ hB₀
    · exact mixed hA₀ hB₀ hA hB
    · rw [inter_comm]
      exact mixed hB₀ hA₀ hB hA
    · exact good hA₀ hB₀
  have hnew : F.image f ∈ best := mem_filter.mpr
    ⟨mem_filter.mpr ⟨mem_univ _, unif, hg⟩, (card_image_of_injOn inj).trans hcard⟩
  have lower {A : Finset α} (h : moves A) : weight (shift A) < weight A := by
    have hw := sum_erase_add A r h.1
    simp only [weight, shift, replacePoint, sum_insert (fun hh ↦ h.2.1 (mem_of_mem_erase hh))]
    omega
  have he : ∑ A ∈ F.image f, weight A < ∑ A ∈ F, weight A := by
    rw [sum_image inj]
    apply sum_lt_sum
    · intro A _
      dsimp [f]
      split_ifs with h
      · exact (lower h).le
      · rfl
    · refine ⟨S, hS, ?_⟩
      have h : moves S := ⟨hx, hy, hfail⟩
      simpa only [f, ite_eq_left h] using lower h
  exact (hmin _ hnew).not_gt he

private lemma intersect_on_half {k : ℕ} {r : α → ℕ} {P : Finset α} {F : Finset (Finset α)}
    (hsize : Fintype.card α = 2 * k) (hk : Even k) (hp : P.card = k)
    (hr : Function.Injective r) (horder : ∀ y ∈ P, ∀ x ∉ P, r y < r x)
    (hu : (F : Set (Finset α)).Sized k) (hm : HasMaximumCard k F)
    (hs : Shifted r F) (hg : TwoIntersectingOn univ F) : TwoIntersectingOn P F := by
  suffices ∀ Q, P ⊆ Q → TwoIntersectingOn Q F → TwoIntersectingOn P F from this _ (subset_univ _) hg
  intro Q
  induction Q using Finset.strongInductionOn with
  | _ Q ih =>
    intro hPQ hQ
    by_cases he : P = Q
    · rwa [he]
    have hlt := card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hPQ, he⟩)
    obtain ⟨z, hz, hz'⟩ := exists_mem_notMem_of_card_lt_card hlt
    obtain ⟨x, hx, hmax⟩ := exists_max_image (Q \ P) r ⟨z, mem_sdiff.mpr ⟨hz, hz'⟩⟩
    obtain ⟨hxQ, hxP⟩ := mem_sdiff.mp hx
    have hsub : P ⊆ Q.erase x := by
      intro a ha
      exact mem_erase.mpr ⟨fun hh ↦ hxP (hh ▸ ha), hPQ ha⟩
    apply ih _ (erase_ssubset hxQ) hsub
    apply shorten hsize hk (hp ▸ card_le_card hsub) (notMem_erase _ _) _ hu hm hs
    · rwa [insert_erase hxQ]
    · intro y hy
      obtain ⟨hyx, hyQ⟩ := mem_erase.mp hy
      by_cases hyP : y ∈ P
      · exact horder _ hyP _ hxP
      · exact lt_of_le_of_ne (hmax _ (mem_sdiff.mpr ⟨hyQ, hyP⟩)) (fun hh ↦ hyx (hr hh))

private lemma compls_good {k : ℕ} {F : Finset (Finset α)} (hsize : Fintype.card α = 2 * k)
    (hu : (F : Set (Finset α)).Sized k) (hg : TwoIntersectingOn univ F) :
    (F.compls : Set (Finset α)).Sized k ∧ TwoIntersectingOn univ F.compls := by
  have hc : (F.compls : Set (Finset α)).Sized k := by
    simpa only [hsize, show 2 * k - k = k by omega] using hu.compls
  refine ⟨hc, ?_⟩
  intro A ha B hb
  have hi := hg _ (mem_compls.mp ha) _ (mem_compls.mp hb)
  simp only [inter_univ, ← compl_union, card_compl] at hi
  simp only [inter_univ]
  have he := card_inter_add_card_union A B
  rw [hc ha, hc hb] at he
  omega

private lemma compls_maximum {k : ℕ} {F : Finset (Finset α)} (hsize : Fintype.card α = 2 * k)
    (hm : HasMaximumCard k F) : HasMaximumCard k F.compls := by
  intro G hu hg
  obtain ⟨hu', hg'⟩ := compls_good hsize hu hg
  simpa only [card_compls] using hm _ hu' hg'

private lemma compls_shifted {F : Finset (Finset α)} {r s : α → ℕ} (hs : Shifted r F)
    (hr : ∀ x y, s y < s x → r x < r y) : Shifted s F.compls := by
  intro A ha x hx y hy hxy
  have h := hs _ (mem_compls.mp ha) _ (mem_compl.mpr hy) _ (by simpa using hx) (hr x y hxy)
  apply mem_compls.mpr
  convert h using 1
  ext a
  simp only [mem_compl, mem_insert, mem_erase]
  grind

-- A maximum family contains every uniform extension of each of its witnessing traces.
private lemma saturated {k : ℕ} {F : Finset (Finset α)} {P A B : Finset α}
    (hu : (F : Set (Finset α)).Sized k) (hm : HasMaximumCard k F) (hg : TwoIntersectingOn P F)
    (ha : A ∈ F) (hb : B.card = k) (he : B ∩ P = A ∩ P) : B ∈ F := by
  classical
  by_contra hB
  let G := insert B F
  have htrace {C : Finset α} (hc : C ∈ G) : ∃ D ∈ F, C ∩ P = D ∩ P := by
    rcases mem_insert.mp hc with rfl | hc
    · exact ⟨_, ha, he⟩
    · exact ⟨_, hc, rfl⟩
  have hsize : (G : Set (Finset α)).Sized k := by
    intro C hc
    rcases mem_insert.mp hc with rfl | hc
    · exact hb
    · exact hu hc
  have hgood : TwoIntersectingOn univ G := by
    intro C hc D hd
    obtain ⟨U, hU, heU⟩ := htrace hc
    obtain ⟨V, hV, heV⟩ := htrace hd
    have h := hg _ hU _ hV
    rw [← heU, ← heV] at h
    simp only [inter_univ]
    exact h.trans (card_le_card (inter_subset_inter inter_subset_left inter_subset_left))
  have hle := hm G hsize hgood
  change (insert B F).card ≤ _ at hle
  rw [card_insert_of_notMem hB] at hle
  omega

private lemma not_balanced {n : ℕ} {F : Finset (Finset α)} {P A : Finset α}
    (hsize : Fintype.card α = 4 * n) (hp : P.card = 2 * n)
    (hu : (F.compls : Set (Finset α)).Sized (2 * n)) (hm : HasMaximumCard (2 * n) F.compls)
    (hg : TwoIntersectingOn P F) (hg' : TwoIntersectingOn Pᶜ F.compls) (ha : A ∈ F)
    (hA : A.card = 2 * n) : (A ∩ P).card ≠ n := by
  intro he
  -- Switch membership on P while keeping the part outside P fixed.
  let B := (P \ A) ∪ (A \ P)
  have hb : B.card = 2 * n := by
    have h₁ := card_sdiff_add_card_inter P A
    have h₂ := card_sdiff_add_card_inter A P
    rw [inter_comm, he, hp] at h₁
    rw [he, hA] at h₂
    have hd : Disjoint (P \ A) (A \ P) := disjoint_left.mpr
      (fun _ h₁ h₂ ↦ (mem_sdiff.mp h₁).2 (mem_sdiff.mp h₂).1)
    dsimp [B]
    rw [card_union_of_disjoint hd]
    omega
  have he' : Bᶜ ∩ Pᶜ = Aᶜ ∩ Pᶜ := by
    ext a
    simp only [B, mem_compl, mem_inter, mem_union, mem_sdiff]
    tauto
  have hb' : Bᶜ ∈ F.compls := saturated hu hm hg' (by simpa using ha : Aᶜ ∈ F.compls)
    (by rw [card_compl, hsize, hb]; omega) he'
  have hh := hg A ha B (by simpa using hb')
  have hz : (A ∩ P) ∩ (B ∩ P) = ∅ := by
    ext a
    simp only [B, mem_inter, mem_union, mem_sdiff, notMem_empty, iff_false]
    tauto
  simp [hz] at hh

-- The family, its complements and the balanced layer are pairwise disjoint.
private lemma count_balanced {n : ℕ} (P : Finset α) (hsize : Fintype.card α = 4 * n)
    (hp : P.card = 2 * n) (F : Finset (Finset α)) (hu : (F : Set (Finset α)).Sized (2 * n))
    (hg : TwoIntersectingOn univ F) (hn : ∀ A ∈ F, (A ∩ P).card ≠ n) :
    2 * F.card + (2 * n).choose n ^ 2 ≤ (4 * n).choose (2 * n) := by
  classical
  let balanced := (P.powersetCard n).biUnion (layer (2 * n) P)
  have hb {A : Finset α} (ha : A ∈ balanced) : A.card = 2 * n ∧ (A ∩ P).card = n := by
    obtain ⟨T, ht, h⟩ := mem_biUnion.mp ha
    obtain ⟨hs, he⟩ := mem_layer.mp h
    exact ⟨hs, he ▸ (mem_powersetCard.mp ht).2⟩
  have hbal : balanced.card = (2 * n).choose n ^ 2 := by
    have hf (T : Finset α) (ht : T ∈ P.powersetCard n) :
        (layer (2 * n) P T).card = (2 * n).choose n := by
      obtain ⟨hT, hcard⟩ := mem_powersetCard.mp ht
      rw [card_layer hT (by omega), card_compl, hp, hsize, hcard,
        show 4 * n - 2 * n = 2 * n by omega, show 2 * n - n = n by omega]
    have hd : (P.powersetCard n : Set (Finset α)).PairwiseDisjoint (layer (2 * n) P) := by
      intro t _ u _ hne
      exact disjoint_left.mpr fun A ha hb ↦ hne ((mem_layer.mp ha).2.symm.trans (mem_layer.mp hb).2)
    rw [show balanced.card = _ from card_biUnion hd, sum_congr rfl hf]
    simp [card_powersetCard, hp, pow_two]
  have hsize' : Fintype.card α = 2 * (2 * n) := by omega
  have hc := (compls_good hsize' hu hg).1
  have hd : Disjoint F F.compls := by
    apply disjoint_left.mpr
    intro A ha ha'
    have h := hg _ ha _ (mem_compls.mp ha')
    simp at h
  have hd' : Disjoint (F ∪ F.compls) balanced := by
    apply disjoint_left.mpr
    intro A hA hbal'
    have h := (hb hbal').2
    rcases mem_union.mp hA with ha | ha
    · exact hn A ha h
    · apply hn _ (mem_compls.mp ha)
      have he : Aᶜ ∩ P = P \ A := by ext; simp [and_comm]
      have hh := card_sdiff_add_card_inter P A
      rw [inter_comm, h, hp] at hh
      rw [he]
      omega
  have hsub : (F ∪ F.compls) ∪ balanced ⊆ univ.powersetCard (2 * n) := by
    intro A hA
    refine mem_powersetCard.mpr ⟨subset_univ _, ?_⟩
    rcases mem_union.mp hA with ha | ha
    · exact (mem_union.mp ha).elim (fun h ↦ hu h) (fun h ↦ hc h)
    · exact (hb ha).1
  have hle := card_le_card hsub
  rw [card_union_of_disjoint hd', card_union_of_disjoint hd, card_compls, hbal,
    card_powersetCard, card_univ, hsize] at hle
  omega

/--
**Bound for 2-intersecting families of half-size sets (Erdős Problem 83).** For every natural
number $n$, every family $F$ of $2n$-element subsets of $\{0, \dots, 4n-1\}$ such that
$|A \cap B| \ge 2$ for all $A, B \in F$ (including $A = B$) satisfies
$2|F| + \binom{2n}{n}^2 \le \binom{4n}{2n}$, that is,
$|F| \le \frac{1}{2}\left(\binom{4n}{2n} - \binom{2n}{n}^2\right)$.

Ahlswede and Khachatrian proved this as a case of their complete intersection theorem, which
determines the largest $t$-intersecting families of $k$-element subsets of an $m$-element set. The
bound is attained by the $2n$-element sets with at least $n + 1$ elements in $\{0, \dots, 2n-1\}$.

Source: T. F. Bloom, Erdős Problems,
Problem #83, https://www.erdosproblems.com/83 (status PROVED (LEAN)); resolution: R. Ahlswede and L.
H. Khachatrian, The complete intersection theorem for systems of finite sets, European J. Combin. 18
(1997), 125-136, erdosproblems.com/83: for 2 ≤ t ≤ k ≤ m and r with 1/(r + 1) ≤ (m - 2k + 2t -
2)/((t - 1)(k - t + 1)) < 1/r, the largest family of k-subsets of [m] with pairwise intersections of
size at least t consists of the k-sets with at least t + r elements of {1, …, t + 2r}; for m = 4n, k
= 2n, t = 2 the ratio is 2/(2n - 1), so r = n - 1 and the family is the 2n-sets with at least n + 1
elements of [2n], https://doi.org/10.1006/eujc.1995.0092.
-/
theorem twoIntersectingHalfSetsBound_holds : twoIntersectingHalfSetsBound := by
  classical
  intro n F hF hI
  have hgood : TwoIntersectingOn univ F := by simpa only [TwoIntersectingOn, inter_univ] using hI
  by_cases hn : n = 0
  · subst n
    have he : F = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro A ha
      have hg := hgood A ha A ha
      simp [hF A ha] at hg
    simp [he]
  let cut : Fin (4 * n) := ⟨2 * n, by omega⟩
  let P := Iio cut
  let r (x : Fin (4 * n)) := x.val
  let s (x : Fin (4 * n)) := 4 * n - 1 - x.val
  have hr : Function.Injective r := Fin.val_injective
  have hs : Function.Injective s := by
    intro a b he
    apply Fin.ext
    have := a.isLt
    have := b.isLt
    dsimp [s] at he
    omega
  have hsize : Fintype.card (Fin (4 * n)) = 2 * (2 * n) := by simp; omega
  have hp : P.card = 2 * n := Fin.card_Iio cut
  have hp' : Pᶜ.card = 2 * n := by rw [card_compl, hp, hsize]; omega
  have hrev {x y : Fin (4 * n)} : s y < s x ↔ r x < r y := by
    have := x.isLt
    have := y.isLt
    dsimp [r, s]
    omega
  obtain ⟨G, hu, hg, hm, hshift⟩ := exists_shifted_maximum (2 * n) r
  have hP : TwoIntersectingOn P G := intersect_on_half hsize (even_two_mul _) hp hr (by
    intro y hy x hx
    have hy' := mem_Iio.mp hy
    have hx' : ¬x < cut := fun h ↦ hx (mem_Iio.mpr h)
    exact lt_of_lt_of_le hy' (le_of_not_gt hx')) hu hm hshift hg
  obtain ⟨hu', hg'⟩ := compls_good hsize hu hg
  have hm' := compls_maximum hsize hm
  have hP' : TwoIntersectingOn Pᶜ G.compls := intersect_on_half hsize (even_two_mul _) hp' hs (by
    intro y hy x hx
    apply hrev.mpr
    have hy' : ¬y < cut := fun h ↦ (mem_compl.mp hy) (mem_Iio.mpr h)
    have hx' : x < cut := mem_Iio.mp (by simpa using hx : x ∈ P)
    exact lt_of_lt_of_le hx' (le_of_not_gt hy')) hu' hm'
      (compls_shifted hshift (fun _ _ h ↦ hrev.mp h)) hg'
  have hb := count_balanced P (Fintype.card_fin _) hp G hu hg
    (fun A ha ↦ not_balanced (Fintype.card_fin _) hp hu' hm' hP hP' ha (hu ha))
  have hle := hm F (fun A ha ↦ hF A ha) hgood
  omega

end MathlibExt.Combinatorics.TwoIntersectingHalfSetsErdosProblem83Wanted

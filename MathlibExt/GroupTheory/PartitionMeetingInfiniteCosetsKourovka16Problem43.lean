/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Partitions of `⊕_{ω₁} ℤ/3ℤ` meeting every infinite coset (Kourovka Notebook Problem 16.43)

Kourovka Notebook, Archive of Solved Problems, Problem 16.43 (E. G. Zelenyuk): is there a partition
of the group `⊕_{ω₁} ℤ/3ℤ` into three subsets whose complements do not contain cosets modulo
infinite subgroups? (There is a partition into two such subsets.)
-/

module

import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Nat.ModEq
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.Group.Finsupp
public import Mathlib.SetTheory.Cardinal.Aleph

/-!
# A three-coloring meeting every infinite coset

We specialize Zelenyuk's argument to exponent three. For each support size, a selector
marks one rank in each complete interval from a fixed sequence of intervals. The color
is the number of changes between consecutive marked values, taken modulo three.

For a coset, finite restrictions give disjoint subgroup vectors. An increasing sequence
of their minima determines a cut. Two blocks supply marked ranks below the cut. For the
third block, nested prefixes and common padding let us avoid marking any old coordinate
above the cut. This leaves two independently adjustable boundaries between three marked
blocks, giving every residue.

See Y. Zelenyuk, J. Combin. Theory Ser. A 115 (2008), 331–339,
[doi:10.1016/j.jcta.2007.05.002](https://doi.org/10.1016/j.jcta.2007.05.002), and the
public reproduction in Lethulwe, §5.2, Lemma 5.2.6, Theorem 5.2.11 and Corollary 5.2.15.
-/

namespace MathlibExt.GroupTheory.PartitionMeetingInfiniteCosetsKourovka16Problem43Wanted

open Finset

/-- The selector intervals have lengths `1², 2², 3², …`. -/
private def start : ℕ → ℕ
  | 0 => 0
  | j + 1 => start j + (j + 1) * (j + 1)

private lemma start_strictMono : StrictMono start := by
  apply strictMono_nat_of_lt_succ
  intro j
  simp [start]

private lemma self_le_start (j : ℕ) : j ≤ start j := by
  induction j with
  | zero => simp [start]
  | succ j ih => exact Nat.succ_le_of_lt (ih.trans_lt (start_strictMono (Nat.lt_succ_self j)))

/-- In each complete interval, mark one rank; use the size modulo the interval's spacing. -/
private def mark (j n : ℕ) : ℕ := start j + (n % (j + 1)) * (j + 1)

private def selected (n r : ℕ) : Prop := ∃ j, start (j + 1) ≤ n ∧ r = mark j n

private lemma start_le_mark (j n : ℕ) : start j ≤ mark j n := Nat.le_add_right ..

private lemma mark_add_le (j n : ℕ) : mark j n + (j + 1) ≤ start (j + 1) := by
  have h : n % (j + 1) + 1 ≤ j + 1 := Nat.succ_le_of_lt (Nat.mod_lt n (Nat.succ_pos j))
  calc
    mark j n + (j + 1) = start j + (n % (j + 1) + 1) * (j + 1) := by
      rw [mark, Nat.add_mul, Nat.one_mul, Nat.add_assoc]
    _ ≤ start (j + 1) := Nat.add_le_add_left (Nat.mul_le_mul_right (j + 1) h) (start j)

private lemma mark_lt_next (j n : ℕ) : mark j n < start (j + 1) := by
  have h := mark_add_le j n
  omega

/-- Beyond `start C`, nearby ranks cannot both be selected at distinct nearby sizes. -/
private lemma selected_separated {C n m r s : ℕ} (hnm : n < m) (hm : m ≤ n + C)
    (hr : start C ≤ r) (hrs : r ≤ s) (hs : s ≤ r + C) :
    selected n r → ¬ selected m s := by
  rintro ⟨j, _, rfl⟩ ⟨k, _, rfl⟩
  have hj : C ≤ j := by
    by_contra! h
    exact (not_lt_of_ge hr) ((mark_lt_next j n).trans_le (start_strictMono.monotone (by omega)))
  have hjk : j = k := by
    rcases lt_trichotomy j k with h | h | h
    · have hgap := (mark_add_le j n).trans
        ((start_strictMono.monotone (Nat.succ_le_of_lt h)).trans (start_le_mark k m))
      omega
    · exact h
    · have hgap := (mark_lt_next k m).trans_le
        ((start_strictMono.monotone (Nat.succ_le_of_lt h)).trans (start_le_mark j n))
      omega
  subst k
  have hdvd : j + 1 ∣ mark j m - mark j n := by
    unfold mark
    rw [Nat.add_sub_add_left, ← Nat.sub_mul]
    exact dvd_mul_left _ _
  have he : mark j n = mark j m := by
    by_contra! h
    have hpos : 0 < mark j m - mark j n := by omega
    have := Nat.le_of_dvd hpos hdvd
    omega
  have hmod : n ≡ m [MOD j + 1] := by
    apply Nat.eq_of_mul_eq_mul_right (Nat.succ_pos j)
    simpa only [mark, Nat.add_left_cancel_iff] using he
  have := Nat.le_of_dvd (m := j + 1) (n := m - n) (by omega) (hmod.dvd' )
  omega

section OrderedSupport

variable {ι : Type*} [LinearOrder ι]

private def rank (s : Finset ι) (a : ι) : ℕ := (s.filter (· < a)).card

private noncomputable def marks (s : Finset ι) : Finset ι := by
  classical
  exact s.filter (fun a ↦ selected s.card (rank s a))

private lemma mem_marks {s : Finset ι} {a : ι} :
    a ∈ marks s ↔ a ∈ s ∧ selected s.card (rank s a) := by
  classical
  simp [marks]

private lemma rank_lt_card {s : Finset ι} {a : ι} (ha : a ∈ s) : rank s a < s.card := by
  exact card_lt_card (Finset.ssubset_iff_subset_ne.2 ⟨filter_subset _ _, by
    intro h
    have := h ▸ ha
    exact (lt_irrefl a) (mem_filter.1 this).2⟩)

private lemma rank_strictMonoOn (s : Finset ι) : StrictMonoOn (rank s) (s : Set ι) := by
  intro a ha b hb hab
  apply card_lt_card
  refine Finset.ssubset_iff_subset_ne.2 ⟨?_, ?_⟩
  · intro x hx
    obtain ⟨hxs, hxa⟩ := mem_filter.1 hx
    exact mem_filter.2 ⟨hxs, hxa.trans hab⟩
  · intro h
    have hm : a ∈ s.filter (· < b) := mem_filter.2 ⟨ha, hab⟩
    rw [← h] at hm
    exact (lt_irrefl a) (mem_filter.1 hm).2

private lemma exists_rank (s : Finset ι) {n : ℕ} (hn : n < s.card) :
    ∃ a ∈ s, rank s a = n := by
  let f : s → Fin s.card := fun a ↦ ⟨rank s a, rank_lt_card a.2⟩
  have hf : Function.Injective f := by
    intro a b hab
    exact Subtype.ext (rank_strictMonoOn s |>.injOn a.2 b.2 (congrArg Fin.val hab))
  have hs : Function.Surjective f :=
    (Fintype.bijective_iff_injective_and_card f).2 ⟨hf, by simp⟩ |>.2
  obtain ⟨a, ha⟩ := hs ⟨n, hn⟩
  exact ⟨a, a.2, congrArg Fin.val ha⟩

/-- Any interval of ranks of the form `[a, start (a + 2))` contains a marked rank,
provided it lies wholly in the support. -/
private lemma exists_mark_in_rank_interval (s : Finset ι) {a b : ℕ}
    (hab : start (a + 2) ≤ b) (hbs : b ≤ s.card) :
    ∃ i ∈ marks s, a ≤ rank s i ∧ rank s i < b := by
  have hlt : mark (a + 1) s.card < b := (mark_lt_next _ _).trans_le hab
  obtain ⟨i, hi, hir⟩ := exists_rank s (hlt.trans_le hbs)
  refine ⟨i, mem_marks.2 ⟨hi, a + 1, hab.trans hbs, hir⟩, ?_, hir ▸ hlt⟩
  rw [hir]
  exact (Nat.le_succ a).trans ((self_le_start _).trans (start_le_mark _ _))

end OrderedSupport


section DisjointBlocks

variable {ι : Type*}

private abbrev Vec (ι : Type*) := ι →₀ ZMod 3

private lemma exists_disjoint_vector (H : AddSubgroup (Vec ι)) (hH : (H : Set (Vec ι)).Infinite)
    (F : Finset ι) : ∃ z ∈ H, z ≠ 0 ∧ Disjoint F z.support := by
  let restrict (y : Vec ι) : F → ZMod 3 := fun a ↦ y a
  obtain ⟨a, ha, b, hb, hab, he⟩ := hH.exists_ne_map_eq_of_mapsTo
    (Set.mapsTo_univ _ _) (Set.finite_univ (α := F → ZMod 3))
  change restrict a = restrict b at he
  refine ⟨a - b, H.sub_mem ha hb, sub_ne_zero.mpr hab, Finset.disjoint_left.2 ?_⟩
  intro i hi hz
  exact (Finsupp.mem_support_iff.1 hz) (sub_eq_zero.mpr (congrFun he ⟨i, hi⟩))

/-- Repeatedly take a nonzero vector in the kernel of restriction to the support already used. -/
private lemma exists_disjoint_sequence (H : AddSubgroup (Vec ι))
    (hH : (H : Set (Vec ι)).Infinite) :
    ∃ v : ℕ → Vec ι, (∀ n, v n ∈ H) ∧ (∀ n, (v n).support.Nonempty) ∧
      Pairwise (fun m n ↦ Disjoint (v m).support (v n).support) := by
  classical
  choose z hz hne hd using exists_disjoint_vector H hH
  let used : ℕ → Finset ι := Nat.rec ∅ (fun _ F ↦ F ∪ (z F).support)
  let v (n : ℕ) := z (used n)
  have hused (n : ℕ) : used (n + 1) = used n ∪ (v n).support := rfl
  have hmono : Monotone used := monotone_nat_of_le_succ fun n ↦ by
    rw [hused]; exact subset_union_left
  have hbefore (m n : ℕ) (hmn : m < n) : Disjoint (v m).support (v n).support :=
    (hd (used n)).mono_left <| (show (v m).support ⊆ used (m + 1) by
      rw [hused]; exact subset_union_right).trans (hmono (Nat.succ_le_of_lt hmn))
  refine ⟨v, fun n ↦ hz (used n), fun n ↦ Finsupp.support_nonempty_iff.2 (hne (used n)), ?_⟩
  intro m n hmn
  rcases lt_or_gt_of_ne hmn with h | h
  · exact hbefore m n h
  · exact (hbefore n m h).symm

variable [LinearOrder ι]

/-- Take the minimum among the remaining terms, and then discard up to and including its index. -/
private lemma increasing_subsequence [WellFoundedLT ι] {a : ℕ → ι} (ha : Function.Injective a) :
    ∃ f : ℕ → ℕ, StrictMono f ∧ StrictMono (a ∘ f) := by
  have hex (n : ℕ) : ∃ m ≥ n, ∀ k ≥ n, a m ≤ a k := by
    let S : Set ι := a '' Set.Ici n
    obtain ⟨_, ⟨m, hm, rfl⟩, hmin⟩ :=
      wellFounded_lt.has_min S ⟨a n, n, Set.mem_Ici.2 le_rfl, rfl⟩
    exact ⟨m, Set.mem_Ici.1 hm, fun k hk ↦ le_of_not_gt (hmin (a k) ⟨k, Set.mem_Ici.2 hk, rfl⟩)⟩
  choose pick hp hmin using hex
  let firstAllowed : ℕ → ℕ := Nat.rec 0 (fun _ n ↦ pick n + 1)
  let f := pick ∘ firstAllowed
  have hstep (n : ℕ) : f n < f (n + 1) := hp (firstAllowed (n + 1))
  have hfrom (n : ℕ) : firstAllowed n ≤ f (n + 1) := (hp (firstAllowed n)).trans (hstep n).le
  refine ⟨f, strictMono_nat_of_lt_succ hstep, strictMono_nat_of_lt_succ (fun n ↦ ?_)⟩
  exact lt_of_le_of_ne (hmin _ _ (hfrom n)) (fun h ↦ (hstep n).ne (ha h))

omit [LinearOrder ι] in
private lemma eventually_forall_finset (F : Finset ι) {p : ι → ℕ → Prop}
    (h : ∀ a ∈ F, ∃ n, ∀ k ≥ n, p a k) : ∃ n, ∀ k ≥ n, ∀ a ∈ F, p a k := by
  classical
  induction F using Finset.induction_on with
  | empty => exact ⟨0, by simp⟩
  | @insert a F _ ih =>
    obtain ⟨n, hn⟩ := h a (mem_insert_self _ _)
    obtain ⟨m, hm⟩ := ih (fun b hb ↦ h b (mem_insert_of_mem hb))
    refine ⟨max n m, fun k hk b hb ↦ ?_⟩
    rcases mem_insert.1 hb with rfl | hb
    · exact hn k ((le_max_left _ _).trans hk)
    · exact hm k ((le_max_right _ _).trans hk) b hb

/-- A downward-closed cut together with the supply of subgroup vectors above every finite
set of coordinates below the cut. The supply can also avoid any finite set of coordinates. -/
private structure BlockSupply (H : AddSubgroup (Vec ι)) where
  lower : ι → Prop
  lower_lt : ∀ {a b : ι}, lower a → ¬ lower b → a < b
  next : ∀ F : Finset ι, ∃ z ∈ H, Disjoint F z.support ∧
    (∃ a ∈ z.support, lower a) ∧ ∀ a ∈ F, lower a → ∀ b ∈ z.support, a < b

private lemma nonempty_blockSupply [WellFoundedLT ι] (H : AddSubgroup (Vec ι))
    (hH : (H : Set (Vec ι)).Infinite) : Nonempty (BlockSupply H) := by
  obtain ⟨u, hu, hne, hd⟩ := exists_disjoint_sequence H hH
  let amin (n : ℕ) : ι := (u n).support.min' (hne n)
  have hmem (n : ℕ) : amin n ∈ (u n).support := min'_mem _ _
  have ha : Function.Injective amin := by
    intro m n he
    by_contra h
    exact (Finset.disjoint_left.1 (hd h) (hmem m)) (he ▸ hmem n)
  obtain ⟨f, hf, hmono⟩ := increasing_subsequence ha
  let a := amin ∘ f
  let v := u ∘ f
  let lower (b : ι) := ∃ n, b < a n
  have hlo : ∀ {b c}, lower b → ¬ lower c → b < c := by
    rintro b c ⟨n, hn⟩ hc
    exact hn.trans_le (le_of_not_gt (fun h ↦ hc ⟨n, h⟩))
  refine ⟨⟨lower, hlo, ?_⟩⟩
  intro F
  obtain ⟨N, hN⟩ := eventually_forall_finset F (p := fun b k ↦
    b ∉ (v k).support ∧ (lower b → b < a k)) (fun b _ ↦ by
      have hav : ∃ n, ∀ k ≥ n, b ∉ (v k).support := by
        by_cases hex : ∃ m, b ∈ (v m).support
        · obtain ⟨m, hm⟩ := hex
          exact ⟨m + 1, fun k hk ↦ Finset.disjoint_left.1
            (hd (hf.injective.ne (show m ≠ k by omega))) hm⟩
        · exact ⟨0, fun k _ hk ↦ hex ⟨k, hk⟩⟩
      obtain ⟨n, hn⟩ := hav
      by_cases hl : lower b
      · obtain ⟨m, hm⟩ := hl
        exact ⟨max n m, fun k hk ↦ ⟨hn k ((le_max_left _ _).trans hk),
          fun _ ↦ hm.trans_le (hmono.monotone ((le_max_right _ _).trans hk))⟩⟩
      · exact ⟨n, fun k hk ↦ ⟨hn k hk, fun h ↦ (hl h).elim⟩⟩)
  have hN' := hN N le_rfl
  refine ⟨v N, hu (f N), Finset.disjoint_left.2 (fun b hb ↦ (hN' b hb).1),
    ⟨a N, hmem (f N), N + 1, hmono (Nat.lt_succ_self _)⟩, ?_⟩
  intro b hb hl c hc
  exact ((hN' b hb).2 hl).trans_le (min'_le _ _ hc)

private noncomputable def BlockSupply.below {H : AddSubgroup (Vec ι)} (S : BlockSupply H)
    (F : Finset ι) : Finset ι := by
  classical
  exact F.filter S.lower

private lemma BlockSupply.mem_below {H : AddSubgroup (Vec ι)} (S : BlockSupply H)
    {F : Finset ι} {a : ι} : a ∈ S.below F ↔ a ∈ F ∧ S.lower a := by
  classical
  simp [BlockSupply.below]

private lemma BlockSupply.below_mono {H : AddSubgroup (Vec ι)} (S : BlockSupply H)
    {F G : Finset ι} (h : F ⊆ G) : S.below F ⊆ S.below G := fun _ ha ↦
  S.mem_below.2 ⟨h (S.mem_below.1 ha).1, (S.mem_below.1 ha).2⟩

private lemma BlockSupply.below_subset {H : AddSubgroup (Vec ι)} (S : BlockSupply H)
    (F : Finset ι) : S.below F ⊆ F := fun _ ha ↦ (S.mem_below.1 ha).1

private lemma BlockSupply.below_union {H : AddSubgroup (Vec ι)} (S : BlockSupply H)
    (F G : Finset ι) : S.below (F ∪ G) = S.below F ∪ S.below G := by
  classical
  exact filter_union _ _ _

/-- Accumulate a block with at least `n` coordinates below the cut, all above the old lower
coordinates, and with its entire support disjoint from the old support. -/
private lemma BlockSupply.grow {H : AddSubgroup (Vec ι)} (S : BlockSupply H)
    (F : Finset ι) (n : ℕ) : ∃ z ∈ H, Disjoint F z.support ∧ n ≤ (S.below z.support).card ∧
      ∀ a ∈ S.below F, ∀ b ∈ z.support, a < b := by
  classical
  induction n with
  | zero => exact ⟨0, H.zero_mem, by simp, Nat.zero_le _, by simp⟩
  | succ n ih =>
    obtain ⟨y, hy, hdy, hcy, hoy⟩ := ih
    obtain ⟨z, hz, hdz, ⟨c, hc, hl⟩, hoz⟩ := S.next (F ∪ y.support)
    obtain ⟨hdF, hdY⟩ := Finset.disjoint_union_left.1 hdz
    refine ⟨y + z, H.add_mem hy hz, ?_, ?_, ?_⟩ <;> rw [Finsupp.support_add_eq hdY]
    · exact Finset.disjoint_union_right.2 ⟨hdy, hdF⟩
    · rw [S.below_union, card_union_of_disjoint
        (hdY.mono (S.below_subset _) (S.below_subset _))]
      have := card_pos.2 (show (S.below z.support).Nonempty from ⟨c, S.mem_below.2 ⟨hc, hl⟩⟩)
      omega
    · intro a ha b hb
      rcases mem_union.1 hb with hb | hb
      · exact hoy a ha b hb
      · exact hoz a (mem_union_left _ (S.mem_below.1 ha).1) (S.mem_below.1 ha).2 b hb

end DisjointBlocks


section MarkedBlocks

variable {ι : Type*} [LinearOrder ι] {H : AddSubgroup (Vec ι)}

private lemma rank_mono_support {A B : Finset ι} (h : A ⊆ B) (a : ι) : rank A a ≤ rank B a :=
  card_le_card (filter_subset_filter _ h)

private lemma rank_union_le [DecidableEq ι] (A B : Finset ι) (a : ι) :
    rank (A ∪ B) a ≤ rank A a + B.card := by
  rw [rank, filter_union]
  exact (card_union_le _ _).trans (Nat.add_le_add_left (card_le_card (filter_subset _ _)) _)

/-- The marked point witnessing a full selector interval between two initial segments. -/
private lemma exists_mark_between (T A B : Finset ι) (hB : B ⊆ T)
    (hAord : ∀ a ∈ A, ∀ b ∈ T, b ∉ A → a < b)
    (hBord : ∀ a ∈ B, ∀ b ∈ T, b ∉ B → a < b)
    (hsize : start (A.card + 2) ≤ B.card) : ∃ a ∈ marks T, a ∈ B ∧ a ∉ A := by
  obtain ⟨a, ha, hlo, hhi⟩ := exists_mark_in_rank_interval T hsize (card_le_card hB)
  have haT := (mem_marks.1 ha).1
  refine ⟨a, ha, ?_, ?_⟩
  · by_contra h
    exact (not_le_of_gt hhi) (card_le_card (show B ⊆ T.filter (· < a) from
      fun b hb ↦ mem_filter.2 ⟨hB hb, hBord b hb a haT h⟩))
  · intro h
    have hsub : T.filter (· < a) ⊆ A.filter (· < a) := by
      intro b hb
      have ⟨hbT, hba⟩ := mem_filter.1 hb
      have hbA : b ∈ A := not_not.mp fun h ↦ hba.not_gt (hAord a ‹a ∈ A› b hbT h)
      exact mem_filter.2 ⟨hbA, hba⟩
    exact (not_le_of_gt ((card_le_card hsub).trans_lt (rank_lt_card h))) hlo

/-- After appending blocks above the old lower support, that support is still an initial
segment of the combined support. -/
private lemma BlockSupply.initial_below [DecidableEq ι] (S : BlockSupply H) {F G : Finset ι}
    (horder : ∀ a ∈ S.below F, ∀ b ∈ G, a < b) :
    ∀ a ∈ S.below F, ∀ b ∈ F ∪ G, b ∉ S.below F → a < b := by
  intro a ha b hb hnot
  rcases mem_union.1 hb with hb | hb
  · exact S.lower_lt (S.mem_below.1 ha).2 (fun h ↦ hnot (S.mem_below.2 ⟨hb, h⟩))
  · exact horder a ha b hb

/-- Nested prefix sums of disjoint nonempty supports above the old lower support. -/
private lemma BlockSupply.prefixes (S : BlockSupply H) (F : Finset ι) :
    ∃ p : ℕ → Vec ι, (∀ n, p n ∈ H) ∧ (∀ n, Disjoint F (p n).support) ∧
      StrictMono (fun n ↦ (p n).support) ∧
      ∀ n, ∀ a ∈ S.below F, ∀ b ∈ (p n).support, a < b := by
  classical
  choose z hz hd hn ho using S.next
  let p : ℕ → Vec ι := Nat.rec 0 (fun _ y ↦ y + z (F ∪ y.support))
  have hdF (n : ℕ) := (Finset.disjoint_union_left.1 (hd (F ∪ (p n).support))).1
  have hdP (n : ℕ) := (Finset.disjoint_union_left.1 (hd (F ∪ (p n).support))).2
  have hstep (n : ℕ) : (p (n + 1)).support = (p n).support ∪ (z (F ∪ (p n).support)).support :=
    Finsupp.support_add_eq (hdP n)
  have hmono : StrictMono (fun n ↦ (p n).support) := by
    apply strictMono_nat_of_lt_succ
    intro n
    rw [hstep]
    refine Finset.ssubset_iff_subset_ne.2 ⟨subset_union_left, ?_⟩
    obtain ⟨a, ha, _⟩ := hn (F ∪ (p n).support)
    intro he
    exact Finset.disjoint_left.1 (hdP n) (he ▸ mem_union_right (p n).support ha) ha
  refine ⟨p, ?_, ?_, hmono, ?_⟩
  · intro n
    induction n with
    | zero => exact H.zero_mem
    | succ n ih => exact H.add_mem ih (hz _)
  · intro n
    induction n with
    | zero => simp [p]
    | succ n ih => rw [hstep, Finset.disjoint_union_right]; exact ⟨ih, hdF n⟩
  · intro n
    induction n with
    | zero => simp [p]
    | succ n ih =>
      intro a ha b hb
      rw [hstep] at hb
      rcases mem_union.1 hb with hb | hb
      · exact ih a ha b hb
      · exact ho _ a (mem_union_left _ (S.mem_below.1 ha).1) (S.mem_below.1 ha).2 b hb

/-- A forbidden point of large rank can appear in at most one of closely spaced nested supports.
With one more candidate than forbidden points, some support avoids them all. -/
private lemma exists_avoiding_marks (bad : Finset ι) (C : ℕ)
    (T : Fin (bad.card + 1) → Finset ι) (hmono : StrictMono T)
    (hsize : ∀ i j, (T j).card ≤ (T i).card + C)
    (hrank : ∀ i j a, rank (T j) a ≤ rank (T i) a + C)
    (hlarge : ∀ i a, a ∈ bad → start C ≤ rank (T i) a) :
    ∃ i, Disjoint bad (marks (T i)) := by
  classical
  by_contra! h
  choose f hf using fun i ↦ Finset.not_disjoint_iff.1 (h i)
  let g (i : Fin (bad.card + 1)) : bad := ⟨f i, (hf i).1⟩
  have hg : Function.Injective g := by
    have hne (i j : Fin (bad.card + 1)) (hij : i < j) : f i ≠ f j := by
      intro he
      have ht := hmono hij
      have hi := (mem_marks.1 (hf i).2).2
      have hj := (mem_marks.1 (hf j).2).2
      rw [← he] at hj
      exact selected_separated (card_lt_card ht) (hsize i j) (hlarge i _ (hf i).1)
        (rank_mono_support (le_of_lt ht) _) (hrank i j _) hi hj
    intro i j he
    rcases lt_trichotomy i j with hij | hij | hij
    · exact (hne i j hij (congrArg Subtype.val he)).elim
    · exact hij
    · exact (hne j i hij (congrArg Subtype.val he.symm)).elim
  have hcard := Fintype.card_le_of_injective g hg
  simp at hcard

/-- First choose nested prefixes, then choose one common padding block. Each of its low
coordinates is below every forbidden point, so even the shortest candidate has large ranks
there. All changes in size and rank come from the fixed, finite prefix pool. -/
private lemma BlockSupply.grow_avoiding (S : BlockSupply H) (F : Finset ι) (N : ℕ) :
    ∃ z ∈ H, Disjoint F z.support ∧ N ≤ (S.below z.support).card ∧
      (∀ a ∈ S.below F, ∀ b ∈ z.support, a < b) ∧
      ∀ a ∈ F, a ∈ marks (F ∪ z.support) → S.lower a := by
  classical
  let bad := F.filter (fun a ↦ ¬ S.lower a)
  let k := bad.card
  obtain ⟨p, hp, hdis, hmono, horder⟩ := S.prefixes F
  let C := (p k).support.card
  obtain ⟨q, hq, hdq, hqsize, hqord⟩ := S.grow (F ∪ (p k).support) (max N (start C))
  obtain ⟨hdqF, hdqP⟩ := Finset.disjoint_union_left.1 hdq
  let A := F ∪ q.support
  let T (i : Fin (k + 1)) := A ∪ (p i).support
  have hsubset (i : Fin (k + 1)) : (p i).support ⊆ (p k).support :=
    hmono.monotone (Nat.le_of_lt_succ i.isLt)
  have hdA (i : Fin (k + 1)) : Disjoint A (p i).support :=
    Finset.disjoint_union_left.2 ⟨hdis i, hdqP.symm.mono_right (hsubset i)⟩
  have hTcard (i : Fin (k + 1)) : (T i).card = A.card + (p i).support.card :=
    card_union_of_disjoint (hdA i)
  have hTmono : StrictMono T := by
    intro i j hij
    have hs := hmono (show i.val < j.val from hij)
    refine lt_of_le_of_ne (union_subset_union_right (s := A) (le_of_lt hs)) (fun he ↦ ?_)
    have hc := congrArg Finset.card he
    rw [hTcard, hTcard] at hc
    exact (card_lt_card hs).ne (Nat.add_left_cancel hc)
  obtain ⟨i, hi⟩ := exists_avoiding_marks bad C T hTmono (fun i j ↦ by
    have h := card_le_card (hsubset j)
    rw [hTcard, hTcard]
    change (p j).support.card ≤ C at h
    omega) (fun i j a ↦ by
      have hs : T j ⊆ T i ∪ (p k).support := union_subset
        (subset_union_left.trans subset_union_left) ((hsubset j).trans subset_union_right)
      exact (rank_mono_support hs a).trans (rank_union_le _ _ _)) (fun i a ha ↦ by
        have hs : S.below q.support ⊆ (T i).filter (· < a) := by
          intro b hb
          have ⟨hbq, hbl⟩ := S.mem_below.1 hb
          exact mem_filter.2 ⟨mem_union_left _ (mem_union_right _ hbq),
            S.lower_lt hbl (mem_filter.1 ha).2⟩
        exact (le_max_right _ _).trans (hqsize.trans (card_le_card hs)))
  have hdqi := hdqP.mono_left (hsubset i)
  have hsupport : (q + p i).support = q.support ∪ (p i).support :=
    Finsupp.support_add_eq hdqi.symm
  refine ⟨q + p i, H.add_mem hq (hp i), ?_, ?_, ?_, ?_⟩ <;> rw [hsupport]
  · exact Finset.disjoint_union_right.2 ⟨hdqF, hdis i⟩
  · exact (le_max_left _ _).trans (hqsize.trans
      (card_le_card (S.below_mono subset_union_left)))
  · intro a ha b hb
    rcases mem_union.1 hb with hb | hb
    · exact hqord a (S.below_mono subset_union_left ha) b hb
    · exact horder i a ha b hb
  · intro a ha hm
    by_contra hn
    exact Finset.disjoint_left.1 hi (mem_filter.2 ⟨ha, hn⟩)
      (by simpa only [T, A, union_assoc] using hm)

end MarkedBlocks


section Changes

private def signed {α : Type*} [Neg α] (e : Bool) (a : α) : α := if e then -a else a

private lemma signed_not (e : Bool) (a : ZMod 3) : signed (!e) a = -signed e a := by
  cases e <;> simp [signed]

private def edge (a b : ZMod 3) : ZMod 3 := if a = b then 0 else 1

private lemma edge_signed (e : Bool) (a b : ZMod 3) :
    edge (signed e a) (signed e b) = edge a b := by
  cases e <;> simp [edge, signed]

private lemma edge_self (a : ZMod 3) : edge a a = 0 := by simp [edge]

private lemma edge_neg (a : ZMod 3) (ha : a ≠ 0) : edge a (-a) = 1 := by
  have h : ∀ t : ZMod 3, t ≠ 0 → edge t (-t) = 1 := by decide
  exact h a ha

private lemma edge_neg_left (a : ZMod 3) (ha : a ≠ 0) : edge (-a) a = 1 := by
  simpa using edge_neg (-a) (neg_ne_zero.mpr ha)

private lemma exists_sign (a b : ZMod 3) (ha : a ≠ 0) (hb : b ≠ 0) :
    ∃ e : Bool, signed e b = a := by
  have h : ∀ x y : ZMod 3, x ≠ 0 → y ≠ 0 → ∃ e : Bool, signed e y = x := by decide
  exact h a b ha hb

private lemma signed_ne_zero (e : Bool) {a : ZMod 3} (ha : a ≠ 0) : signed e a ≠ 0 := by
  cases e <;> simpa [signed] using ha

/-- The number of sign changes, reduced modulo three, starting with the preceding value `a`. -/
private def changesFrom (a : ZMod 3) : List (ZMod 3) → ZMod 3
  | [] => 0
  | b :: l => edge a b + changesFrom b l

private def changes : List (ZMod 3) → ZMod 3
  | [] => 0
  | a :: l => changesFrom a l

private lemma changesFrom_append (a : ZMod 3) (l r : List (ZMod 3)) :
    changesFrom a (l ++ r) = changesFrom a l + changesFrom (l.getLastD a) r := by
  induction l generalizing a with
  | nil => simp [changesFrom]
  | cons b l ih => simp only [List.cons_append, changesFrom, ih, List.getLastD_cons, add_assoc]

private lemma changes_append_cons (l : List (ZMod 3)) (hl : l ≠ [])
    (b : ZMod 3) (r : List (ZMod 3)) :
    changes (l ++ b :: r) = changes l + edge (l.getLast hl) b + changesFrom b r := by
  cases l with
  | nil => exact (hl rfl).elim
  | cons a l => simp only [List.cons_append, changes, changesFrom_append, List.getLast_eq_getLastD,
      changesFrom, add_assoc]

private lemma changesFrom_signed (e : Bool) (a : ZMod 3) (l : List (ZMod 3)) :
    changesFrom (signed e a) (l.map (signed e)) = changesFrom a l := by
  induction l generalizing a with
  | nil => rfl
  | cons b l ih => simp only [List.map_cons, changesFrom, edge_signed, ih]

/-- Match both boundaries, then flip just the final block or just the middle block to add
respectively one or two changes. Negating a block does not affect its internal changes. -/
private lemma changes_three_blocks (l y z : List (ZMod 3)) (hl : l ≠ []) (hy : y ≠ [])
    (hz : z ≠ []) (hnl : l.getLast hl ≠ 0) (hny : ∀ b ∈ y, b ≠ 0)
    (hnz : ∀ b ∈ z, b ≠ 0) (i : ZMod 3) :
    ∃ e f : Bool, changes ((l ++ y.map (signed e)) ++ z.map (signed f)) = i := by
  cases y with
  | nil => exact (hy rfl).elim
  | cons b y =>
    cases z with
    | nil => exact (hz rfl).elim
    | cons c z =>
      let a := l.getLast hl
      let d := y.getLastD b
      obtain ⟨e, he⟩ := exists_sign a b hnl (hny b (by simp))
      have hd : signed e d ≠ 0 := signed_ne_zero e (hny d List.getLastD_mem_cons)
      obtain ⟨f, hf⟩ := exists_sign (signed e d) c hd (hnz c (by simp))
      let base := changes l + changesFrom b y + changesFrom c z
      have eval (s t : Bool) :
          changes ((l ++ (b :: y).map (signed s)) ++ (c :: z).map (signed t)) =
            base + edge a (signed s b) + edge (signed s d) (signed t c) := by
        simp only [List.map_cons]
        rw [changes_append_cons _ (by simp), changes_append_cons l hl,
          List.getLast_append_right (by simp), List.getLast_eq_getLastD, List.getLastD_map,
          changesFrom_signed, changesFrom_signed]
        dsimp [base, a, d]
        ac_rfl
      have residues : ∀ t : ZMod 3, t = 0 ∨ t = 1 ∨ t = 1 + 1 := by decide
      have hi : i = base + (i - base) := by rw [add_comm, sub_add_cancel]
      rcases residues (i - base) with h | h | h
      · exact ⟨e, f, by rw [eval, he, hf, edge_self, edge_self, hi, h, add_zero, add_zero]⟩
      · refine ⟨e, !f, ?_⟩
        rw [eval, he, signed_not, hf, edge_self, edge_neg _ hd, hi, h, add_zero]
      · refine ⟨!e, f, ?_⟩
        rw [eval, signed_not, signed_not, he, hf, edge_neg _ hnl, edge_neg_left _ hd,
          hi, h, add_assoc]

end Changes


section Coloring

variable {ι : Type*} [LinearOrder ι]

private lemma sort_union_of_lt [DecidableEq ι] (A B : Finset ι)
    (h : ∀ a ∈ A, ∀ b ∈ B, a < b) : (A ∪ B).sort = A.sort ++ B.sort := by
  apply (A ∪ B).sortedLT_sort.eq_of_mem_iff
  · exact List.sortedLT_append.2 ⟨A.sortedLT_sort, B.sortedLT_sort,
      fun a ha b hb ↦ h a ((mem_sort _).1 ha) b ((mem_sort _).1 hb)⟩
  · intro a
    simp

private lemma BlockSupply.marked_piece {H : AddSubgroup (Vec ι)} (S : BlockSupply H)
    [DecidableEq ι] {F B T : Finset ι} (hsub : F ∪ B ⊆ T)
    (hF : ∀ a ∈ S.below F, ∀ b ∈ T, b ∉ S.below F → a < b)
    (hB : ∀ a ∈ S.below (F ∪ B), ∀ b ∈ T, b ∉ S.below (F ∪ B) → a < b)
    (hsize : start ((S.below F).card + 2) ≤ (S.below B).card) :
    ((marks T) ∩ B).Nonempty := by
  obtain ⟨a, ha, hlo, hn⟩ := exists_mark_between T (S.below F) (S.below (F ∪ B))
    ((S.below_subset _).trans hsub) hF hB
    (hsize.trans (card_le_card (S.below_mono subset_union_right)))
  obtain ⟨hab, hl⟩ := S.mem_below.1 hlo
  refine ⟨a, mem_inter.2 ⟨ha, ?_⟩⟩
  exact (mem_union.1 hab).resolve_left (fun h ↦ hn (S.mem_below.2 ⟨h, hl⟩))

omit [LinearOrder ι] in
private lemma support_signed (e : Bool) (x : Vec ι) : (signed e x).support = x.support := by
  cases e <;> simp [signed]

omit [LinearOrder ι] in
private lemma signed_apply (e : Bool) (x : Vec ι) (a : ι) : signed e x a = signed e (x a) := by
  cases e <;> simp [signed]

omit [LinearOrder ι] in
private lemma signed_mem {H : AddSubgroup (Vec ι)} {x : Vec ι} (hx : x ∈ H) (e : Bool) :
    signed e x ∈ H := by
  cases e
  · exact hx
  · exact H.neg_mem hx

omit [LinearOrder ι] in
private lemma add_apply_left {x y : Vec ι} (hd : Disjoint x.support y.support) {a : ι}
    (ha : a ∈ x.support) : (x + y) a = x a := by
  rw [Finsupp.add_apply, Finsupp.notMem_support_iff.1 (Finset.disjoint_left.1 hd ha), add_zero]

omit [LinearOrder ι] in
private lemma add_apply_right {x y : Vec ι} (hd : Disjoint x.support y.support) {a : ι}
    (ha : a ∈ y.support) : (x + y) a = y a := by
  rw [add_comm, add_apply_left hd.symm ha]

private noncomputable def color (x : Vec ι) : ZMod 3 :=
  changes ((marks x.support).sort.map x)

/-- The color of an arbitrary translate is controlled by three consecutive nonempty lists
of marked coordinates. Their full supports can interleave above the cut; no old marked
coordinate is allowed there. -/
private lemma exists_color_in_coset [WellFoundedLT ι] (H : AddSubgroup (Vec ι))
    (hH : (H : Set (Vec ι)).Infinite) (x : Vec ι) (i : ZMod 3) :
    ∃ h ∈ H, color (x + h) = i := by
  classical
  obtain ⟨S⟩ := nonempty_blockSupply H hH
  let A₀ := x.support
  obtain ⟨y, hy, hdy, hyN, hyo⟩ := S.grow A₀ (start ((S.below A₀).card + 2))
  let A₁ := A₀ ∪ y.support
  obtain ⟨z, hz, hdz, hzN, hzo⟩ := S.grow A₁ (start ((S.below A₁).card + 2))
  let A₂ := A₁ ∪ z.support
  obtain ⟨w, hw, hdw, hwN, hwo, hupper⟩ := S.grow_avoiding A₂ (start ((S.below A₂).card + 2))
  let T := A₂ ∪ w.support
  let M := marks T
  have h₀₁ : A₀ ⊆ A₁ := subset_union_left
  have h₁₂ : A₁ ⊆ A₂ := subset_union_left
  have h₂T : A₂ ⊆ T := subset_union_left
  have hinit₀ : ∀ a ∈ S.below A₀, ∀ b ∈ T, b ∉ S.below A₀ → a < b := by
    have hor : ∀ a ∈ S.below A₀, ∀ b ∈ y.support ∪ (z.support ∪ w.support), a < b := by
      intro a ha b hb
      rcases mem_union.1 hb with hb | hb
      · exact hyo a ha b hb
      rcases mem_union.1 hb with hb | hb
      · exact hzo a (S.below_mono h₀₁ ha) b hb
      · exact hwo a (S.below_mono (h₀₁.trans h₁₂) ha) b hb
    simpa only [T, A₂, A₁, union_assoc] using S.initial_below hor
  have hinit₁ : ∀ a ∈ S.below A₁, ∀ b ∈ T, b ∉ S.below A₁ → a < b := by
    have hor : ∀ a ∈ S.below A₁, ∀ b ∈ z.support ∪ w.support, a < b := by
      intro a ha b hb
      rcases mem_union.1 hb with hb | hb
      · exact hzo a ha b hb
      · exact hwo a (S.below_mono h₁₂ ha) b hb
    simpa only [T, A₂, union_assoc] using S.initial_below hor
  have hinit₂ : ∀ a ∈ S.below A₂, ∀ b ∈ T, b ∉ S.below A₂ → a < b := S.initial_below hwo
  have hinitT : ∀ a ∈ S.below T, ∀ b ∈ T, b ∉ S.below T → a < b := by
    intro a ha b hb hnb
    exact S.lower_lt (S.mem_below.1 ha).2 (fun h ↦ hnb (S.mem_below.2 ⟨hb, h⟩))
  let L₀ := M ∩ x.support
  let L₁ := M ∩ y.support
  let L₂ := M ∩ z.support
  let L₃ := M ∩ w.support
  have hn₁ : L₁.Nonempty := S.marked_piece (h₁₂.trans h₂T) hinit₀ hinit₁ hyN
  have hn₂ : L₂.Nonempty := S.marked_piece h₂T hinit₁ hinit₂ hzN
  have hn₃ : L₃.Nonempty := S.marked_piece Subset.rfl hinit₂ hinitT hwN
  have hM : M = ((L₀ ∪ L₁) ∪ L₂) ∪ L₃ := by
    ext a
    have hfwd (ha : a ∈ M) : a ∈ T := (mem_marks.1 ha).1
    change a ∈ M ↔ a ∈ _
    simp only [L₀, L₁, L₂, L₃, mem_union, mem_inter, ← and_or_left]
    exact ⟨fun h ↦ ⟨h, by simpa only [T, A₂, A₁, A₀, mem_union] using hfwd h⟩, And.left⟩
  have hsort₀₁ : (L₀ ∪ L₁).sort = L₀.sort ++ L₁.sort := by
    apply sort_union_of_lt
    intro a ha b hb
    have ⟨ham, hax⟩ := mem_inter.1 ha
    exact hyo a (S.mem_below.2 ⟨hax, hupper a (h₁₂ (h₀₁ hax)) ham⟩) b (mem_inter.1 hb).2
  have hsort₁₂ : ((L₀ ∪ L₁) ∪ L₂).sort = (L₀ ∪ L₁).sort ++ L₂.sort := by
    apply sort_union_of_lt
    intro a ha b hb
    have ha₁ : a ∈ A₁ := by
      rcases mem_union.1 ha with ha | ha
      · exact mem_union_left _ (mem_inter.1 ha).2
      · exact mem_union_right _ (mem_inter.1 ha).2
    have haM : a ∈ M := by
      rcases mem_union.1 ha with ha | ha <;> exact (mem_inter.1 ha).1
    exact hzo a (S.mem_below.2 ⟨ha₁, hupper a (h₁₂ ha₁) haM⟩) b (mem_inter.1 hb).2
  have hsort₂₃ : (((L₀ ∪ L₁) ∪ L₂) ∪ L₃).sort = ((L₀ ∪ L₁) ∪ L₂).sort ++ L₃.sort := by
    apply sort_union_of_lt
    intro a ha b hb
    have ha₂ : a ∈ A₂ := by
      rcases mem_union.1 ha with ha | ha
      · apply mem_union_left
        rcases mem_union.1 ha with ha | ha
        · exact mem_union_left _ (mem_inter.1 ha).2
        · exact mem_union_right _ (mem_inter.1 ha).2
      · exact mem_union_right _ (mem_inter.1 ha).2
    have haM : a ∈ M := by
      rcases mem_union.1 ha with ha | ha
      · rcases mem_union.1 ha with ha | ha <;> exact (mem_inter.1 ha).1
      · exact (mem_inter.1 ha).1
    exact hwo a (S.mem_below.2 ⟨ha₂, hupper a ha₂ haM⟩) b (mem_inter.1 hb).2
  have hsort : M.sort = ((L₀.sort ++ L₁.sort) ++ L₂.sort) ++ L₃.sort := by
    rw [hM, hsort₂₃, hsort₁₂, hsort₀₁]
  let l := L₀.sort.map x ++ L₁.sort.map y
  let q := L₂.sort.map z
  let r := L₃.sort.map w
  have nonzero {L : Finset ι} {u : Vec ι} (hL : L ⊆ u.support) :
      ∀ t ∈ L.sort.map u, t ≠ 0 := by
    intro t ht
    obtain ⟨a, ha, rfl⟩ := List.mem_map.1 ht
    exact Finsupp.mem_support_iff.1 (hL ((mem_sort _).1 ha))
  have nonempty_map {L : Finset ι} (hL : L.Nonempty) (u : Vec ι) : L.sort.map u ≠ [] := by
    obtain ⟨a, ha⟩ := hL
    exact List.ne_nil_of_mem (List.mem_map.2 ⟨a, (mem_sort _).2 ha, rfl⟩)
  have hl : l ≠ [] := fun h ↦ nonempty_map hn₁ y (List.append_eq_nil_iff.1 h).2
  have hl0 : l.getLast hl ≠ 0 := by
    rcases List.mem_append.1 (List.getLast_mem hl) with h | h
    · exact nonzero inter_subset_right _ h
    · exact nonzero inter_subset_right _ h
  obtain ⟨e, f, hcol⟩ := changes_three_blocks l q r hl (nonempty_map hn₂ z) (nonempty_map hn₃ w)
    hl0 (nonzero inter_subset_right) (nonzero inter_subset_right) i
  refine ⟨y + signed e z + signed f w, H.add_mem (H.add_mem hy (signed_mem hz e)) (signed_mem hw f),
    ?_⟩
  let g₁ := x + y
  let g₂ := g₁ + signed e z
  let g := g₂ + signed f w
  have hgs₁ : g₁.support = A₁ := Finsupp.support_add_eq hdy
  have hd₂ : Disjoint g₁.support (signed e z).support := by rwa [hgs₁, support_signed]
  have hgs₂ : g₂.support = A₂ := by
    simp only [g₂, Finsupp.support_add_eq hd₂, hgs₁, support_signed, A₂]
  have hd₃ : Disjoint g₂.support (signed f w).support := by rwa [hgs₂, support_signed]
  have hgs : g.support = T := by
    simp only [g, Finsupp.support_add_eq hd₃, hgs₂, support_signed, T]
  have hmap₀ : L₀.sort.map g = L₀.sort.map x := by
    apply List.map_congr_left
    intro a ha
    have hax := (mem_inter.1 ((mem_sort _).1 ha)).2
    have ha₁ : a ∈ g₁.support := hgs₁ ▸ h₀₁ hax
    have ha₂ : a ∈ g₂.support := hgs₂ ▸ h₁₂ (h₀₁ hax)
    exact (add_apply_left hd₃ ha₂).trans ((add_apply_left hd₂ ha₁).trans (add_apply_left hdy hax))
  have hmap₁ : L₁.sort.map g = L₁.sort.map y := by
    apply List.map_congr_left
    intro a ha
    have hay := (mem_inter.1 ((mem_sort _).1 ha)).2
    have ha₁' : a ∈ A₁ := mem_union_right _ hay
    have ha₁ : a ∈ g₁.support := hgs₁ ▸ ha₁'
    have ha₂ : a ∈ g₂.support := hgs₂ ▸ h₁₂ ha₁'
    exact (add_apply_left hd₃ ha₂).trans ((add_apply_left hd₂ ha₁).trans (add_apply_right hdy hay))
  have hmap₂ : L₂.sort.map g = q.map (signed e) := by
    rw [List.map_map]
    apply List.map_congr_left
    intro a ha
    have haz := (mem_inter.1 ((mem_sort _).1 ha)).2
    have ha₂ : a ∈ g₂.support := hgs₂ ▸ mem_union_right A₁ haz
    have hase : a ∈ (signed e z).support := support_signed e z ▸ haz
    exact (add_apply_left hd₃ ha₂).trans ((add_apply_right hd₂ hase).trans (signed_apply e z a))
  have hmap₃ : L₃.sort.map g = r.map (signed f) := by
    rw [List.map_map]
    apply List.map_congr_left
    intro a ha
    have haw := (mem_inter.1 ((mem_sort _).1 ha)).2
    have hasf : a ∈ (signed f w).support := support_signed f w ▸ haw
    exact (add_apply_right hd₃ hasf).trans (signed_apply f w a)
  have heq : x + (y + signed e z + signed f w) = g := by simp only [g, g₂, g₁, add_assoc]
  rw [heq, color, hgs, ← show M = marks T from rfl, hsort, List.map_append, List.map_append,
    List.map_append, hmap₀, hmap₁, hmap₂, hmap₃]
  exact hcol

end Coloring

@[expose] public section

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 16.43 (E. G.
Zelenyuk). UnsolvedMath record UM-00701235 (`KOU-16.43`), dataset ulamai/UnsolvedMath v1.8.0.

`⊕_{ω₁} ℤ/3ℤ` is the group `ι →₀ ZMod 3` of finitely supported functions on an index set `ι` of
cardinality `ℵ₁`. A partition into three subsets is a colouring `c : G → Fin 3`; the complement of a
part contains no coset of an infinite subgroup exactly when the part meets every such coset.
-/

/-- **Kourovka 16.43: partitioning $\bigoplus_{\omega_1} \mathbb{Z}/3\mathbb{Z}$ into three parts
meeting every infinite coset.** The proposition that for every set $I$ of cardinality $\aleph_1$,
the group $A = \bigoplus_{i \in I} \mathbb{Z}/3\mathbb{Z}$ of finitely supported functions from $I$
to $\mathbb{Z}/3\mathbb{Z}$ can be partitioned into three subsets $A_0, A_1, A_2$ such that for
every infinite subgroup $H$ of $A$ and every $x \in A$, the coset $x + H$ meets each $A_i$. -/
def threePartitionMeetsInfiniteCosets : Prop :=
  ∀ ι : Type, Cardinal.mk ι = Cardinal.aleph 1 →
    ∃ c : (ι →₀ ZMod 3) → Fin 3, ∀ H : AddSubgroup (ι →₀ ZMod 3),
      (H : Set (ι →₀ ZMod 3)).Infinite → ∀ (x : ι →₀ ZMod 3) (i : Fin 3), ∃ h ∈ H, c (x + h) = i

/--
**A partition of $\bigoplus_{\omega_1} \mathbb{Z}/3\mathbb{Z}$ into three parts meeting every
infinite coset.** Let $I$ be a set of cardinality $\aleph_1$ and let $A = \bigoplus_{i \in I}
\mathbb{Z}/3\mathbb{Z}$ be the group of finitely supported functions from $I$ to
$\mathbb{Z}/3\mathbb{Z}$. Then $A$ can be partitioned into three subsets $A_0, A_1, A_2$ such that
for every infinite subgroup $H$ of $A$ and every $x \in A$, the coset $x + H$ meets each $A_i$.

The Kourovka Archive records more: every infinite abelian group with finitely many involutions can
be partitioned into infinitely many subsets such that every coset modulo an infinite subgroup meets
each subset of the partition.

Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 16.43 (E. G.
Zelenyuk); resolution: Y. Zelenyuk, J. Combin. Theory Ser. A 115 (2008), 331-339, Kourovka Archive,
Problem 16.43 (Yes; moreover every infinite abelian group with finitely many involutions can be
partitioned into infinitely many subsets such that every coset modulo an infinite subgroup meets
each subset).
-/
public theorem threePartitionMeetsInfiniteCosets_holds :
    threePartitionMeetsInfiniteCosets := by
  classical
  intro ι _
  obtain ⟨order, wellFounded⟩ := exists_wellFoundedLT ι
  let _ : LinearOrder ι := order
  let _ : WellFoundedLT ι := wellFounded
  refine ⟨fun x ↦ (ZMod.finEquiv 3).symm (color x), fun H hH x i ↦ ?_⟩
  obtain ⟨h, hh, hc⟩ := exists_color_in_coset H hH x (ZMod.finEquiv 3 i)
  exact ⟨h, hh, (congrArg (ZMod.finEquiv 3).symm hc).trans ((ZMod.finEquiv 3).symm_apply_apply i)⟩

end

end MathlibExt.GroupTheory.PartitionMeetingInfiniteCosetsKourovka16Problem43Wanted

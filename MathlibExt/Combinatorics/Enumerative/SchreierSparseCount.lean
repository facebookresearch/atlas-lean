/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Combinatorics.Enumerative.Partition.Basic
public import Mathlib.Data.Finset.Sort
public import Mathlib.Order.Interval.Finset.Nat

/-!
# Counting Schreier sparse sets

The number of Schreier sparse sets with maximum `n ≥ 1` is the partition number of `n - 1`.
The bijection of Beanland and Chu increments each consecutive gap and adds one part of size
one for each unit by which the minimum exceeds the cardinality.
-/

set_option autoImplicit false

@[expose] public section

namespace MathlibExt.Combinatorics.Enumerative.SchreierTypeSetsWanted

/-- **Schreier sets.** A finite set $A$ of natural numbers is *Schreier* if $|A| \le a$ for
every $a \in A$; equivalently, $A$ is empty or $\min A \ge |A|$. -/
def IsSchreier (A : Finset ℕ) : Prop := ∀ a ∈ A, A.card ≤ a

instance (A : Finset ℕ) : Decidable (IsSchreier A) := by
  unfold IsSchreier; infer_instance

/-- **Sparse sets.** A finite set of natural numbers is *sparse* if the differences between
consecutive elements in increasing order are non-decreasing. -/
def IsSparse (A : Finset ℕ) : Prop :=
  ∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A, a < b → b < c →
    (∀ x ∈ A, a < x → b ≤ x) → (∀ x ∈ A, b < x → c ≤ x) →
      b - a ≤ c - b

instance (A : Finset ℕ) : Decidable (IsSparse A) := by
  unfold IsSparse; infer_instance

/-- **The partition number $p(u)$.** For a natural number $u$, $p(u)$ is the number of partitions
of $u$, that is, of multisets of positive integers summing to $u$; in particular $p(0) = 1$. -/
def partitionCount (u : ℕ) : ℕ := Fintype.card (Nat.Partition u)

/-- **Number of Schreier sparse sets with maximum $n$.** For a natural number $n$, $|F_n|$ is the
number of sets $F \subseteq \{1, \dots, n\}$ with $n \in F$ that are Schreier and sparse. -/
def schreierSparseCount (n : ℕ) : ℕ :=
  ((Finset.Icc 1 n).powerset.filter (fun F => IsSchreier F ∧
    IsSparse F ∧ n ∈ F)).card

-- Removing the minimum preserves every consecutive triple except the first.
private theorem sparse_cons {a b c : ℕ} {t : List ℕ}
    (hs : (a :: b :: c :: t).Pairwise (· < ·)) :
    IsSparse (a :: b :: c :: t).toFinset ↔
      b - a ≤ c - b ∧ IsSparse (b :: c :: t).toFinset := by
  obtain ⟨hab, ht⟩ := List.pairwise_cons_cons_iff_of_trans.mp hs
  have hbc := (List.pairwise_cons_cons_iff_of_trans.mp ht).1
  have hct := List.pairwise_cons.mp (List.pairwise_cons.mp ht).2 |>.1
  simp only [IsSparse, List.mem_toFinset, List.mem_cons]
  constructor
  · intro h
    constructor
    · apply h a (by simp) b (by simp) c (by simp) hab hbc <;> grind
    · intro x hx y hy z hz hxy hyz h₁ h₂
      apply h x (Or.inr hx) y (Or.inr hy) z (Or.inr hz) hxy hyz <;> grind
  · rintro ⟨hgap, htail⟩ x hx y hy z hz hxy hyz h₁ h₂
    rcases hx with rfl | hx
    · have : y = b := by grind
      have : z = c := by grind
      grind
    · apply htail x hx y (by grind) z (by grind) hxy hyz <;> grind

-- The partial sums start at the prescribed minimum and end at the maximum.
private abbrev points (a : ℕ) (ds : List ℕ) := ds.scanl (· + ·) a

private theorem mem_bounds {a x : ℕ} {ds : List ℕ} (hx : x ∈ points a ds) :
    a ≤ x ∧ x ≤ a + ds.sum := by
  induction ds generalizing a with
  | nil => simp_all [points]
  | cons d ds ih =>
    simp only [points, List.scanl_cons, List.mem_cons] at hx
    rcases hx with rfl | hx
    · simp
    · have := ih hx
      simp only [List.sum_cons]
      omega

private theorem endpoints_mem (a : ℕ) (ds : List ℕ) :
    a ∈ points a ds ∧ a + ds.sum ∈ points a ds := by
  induction ds generalizing a with
  | nil => simp [points]
  | cons d ds ih =>
    simpa [points, Nat.add_assoc] using
      (show a ∈ a :: points (a + d) ds ∧ a + d + ds.sum ∈ a :: points (a + d) ds from
        ⟨List.mem_cons_self, List.mem_cons_of_mem _ (ih _).2⟩)

private theorem points_sorted (a : ℕ) {ds : List ℕ} (hp : ∀ d ∈ ds, 0 < d) :
    (points a ds).Pairwise (· < ·) := by
  induction ds generalizing a with
  | nil => simp [points]
  | cons d ds ih =>
    rw [points, List.scanl_cons]
    refine List.pairwise_cons.mpr ⟨?_, ih _ (fun x hx => hp _ (.tail _ hx))⟩
    intro x hx
    exact lt_of_lt_of_le (Nat.lt_add_of_pos_right (hp d (.head _))) (mem_bounds hx).1

private theorem points_sparse_iff (a : ℕ) {ds : List ℕ} (hp : ∀ d ∈ ds, 0 < d) :
    IsSparse (points a ds).toFinset ↔ ds.Pairwise (· ≤ ·) := by
  induction ds generalizing a with
  | nil => simp [points, IsSparse]
  | cons d ds ih =>
    cases ds with
    | nil => simp [points, IsSparse]
    | cons e es =>
      rw [List.pairwise_cons_cons_iff_of_trans]
      rw [← ih (a + d) (fun x hx => hp _ (.tail _ hx))]
      have hs := points_sorted a hp
      have he : points (a + d + e) es = (a + d + e) :: (points (a + d + e) es).tail := by
        cases es <;> simp [points]
      simp only [points, List.scanl_cons] at hs ⊢
      unfold points at he
      rw [he] at hs ⊢
      simpa using sparse_cons hs

private theorem exists_points (a : ℕ) (t : List ℕ) (hs : (a :: t).Pairwise (· < ·)) :
    ∃ ds, (∀ d ∈ ds, 0 < d) ∧ points a ds = a :: t := by
  induction t generalizing a with
  | nil => exact ⟨[], by simp, by simp [points]⟩
  | cons b t ih =>
    obtain ⟨hab, ht⟩ := List.pairwise_cons_cons_iff_of_trans.mp hs
    obtain ⟨ds, hp, hd⟩ := ih b ht
    refine ⟨(b - a) :: ds, ?_, ?_⟩
    · simpa using And.intro (Nat.sub_pos_of_lt hab) hp
    · simpa only [points, List.scanl_cons, Nat.add_sub_of_le hab.le] using congrArg (a :: ·) hd

private theorem points_inj {a b : ℕ} {ds es : List ℕ} (h : points a ds = points b es) :
    a = b ∧ ds = es := by
  have hab : a = b := by simpa [points] using congrArg List.head? h
  subst b
  refine ⟨rfl, ?_⟩
  induction ds generalizing a es with
  | nil => simpa [points, List.scanl_iff_nil] using h.symm
  | cons d ds ih =>
    cases es with
    | nil => simp [points] at h
    | cons e es =>
      simp only [points, List.scanl_cons, List.cons.injEq, true_and] at h
      have : a + d = a + e := by simpa using congrArg List.head? h
      obtain rfl : d = e := by omega
      rw [ih h]

-- With maximum u + 1, the padding and the incremented gaps together sum to u.
private structure GapData (u : ℕ) where
  ones : ℕ
  gaps : List ℕ
  positive : ∀ d ∈ gaps, 0 < d
  ordered : gaps.Pairwise (· ≤ ·)
  total : ones + gaps.length + gaps.sum = u

private abbrev GapData.start {u : ℕ} (c : GapData u) := c.ones + c.gaps.length + 1

private abbrev family (n : ℕ) :=
  (Finset.Icc 1 n).powerset.filter (fun F => IsSchreier F ∧ IsSparse F ∧ n ∈ F)

private def GapData.toSet {u : ℕ} (c : GapData u) : family (u + 1) := by
  let xs := points c.start c.gaps
  have hlast : c.start + c.gaps.sum = u + 1 := by
    unfold GapData.start
    have := c.total
    omega
  have ends := endpoints_mem c.start c.gaps
  have hcard : xs.toFinset.card = c.gaps.length + 1 := by
    rw [List.toFinset_card_of_nodup (points_sorted c.start c.positive).sortedLT.nodup]
    simp [points]
  refine ⟨xs.toFinset, Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr ?_, ?_, ?_, ?_⟩⟩
  · intro x hx
    obtain ⟨lo, hi⟩ := mem_bounds (List.mem_toFinset.mp hx : x ∈ points c.start c.gaps)
    exact Finset.mem_Icc.mpr ⟨(Nat.succ_le_succ (Nat.zero_le _)).trans lo, hi.trans_eq hlast⟩
  · intro x hx
    have hstart : c.gaps.length + 1 ≤ c.start := Nat.succ_le_succ (Nat.le_add_left _ _)
    exact hcard.le.trans (hstart.trans (mem_bounds (List.mem_toFinset.mp hx)).1)
  · exact (points_sparse_iff _ c.positive).mpr c.ordered
  · exact List.mem_toFinset.mpr (hlast ▸ ends.2)

private theorem GapData.toSet_bijective (u : ℕ) :
    Function.Bijective (GapData.toSet (u := u)) := by
  constructor
  · intro c d h
    have sort_points (v : GapData u) : v.toSet.val.sort = points v.start v.gaps := by
      have hs := (points_sorted v.start v.positive).sortedLT
      exact (List.toFinset_sort _ hs.nodup).mpr hs.sortedLE.pairwise
    have he := congrArg (fun v : family (u + 1) => v.val.sort) h
    rw [sort_points, sort_points] at he
    obtain ⟨hstart, hgaps⟩ := points_inj he
    cases c
    cases d
    simp_all [GapData.start]
  · rintro ⟨F, hF⟩
    obtain ⟨hsub, hsch, hsp, hmax⟩ := Finset.mem_filter.mp hF
    replace hsub := Finset.mem_powerset.mp hsub
    have hs := F.sortedLT_sort.pairwise
    cases he : F.sort with
    | nil =>
      have hm : u + 1 ∈ F.sort := (Finset.mem_sort _).mpr hmax
      simp [he] at hm
    | cons a t =>
      rw [he] at hs
      obtain ⟨ds, hp, hds⟩ := exists_points a t hs
      have hlist := hds.trans he.symm
      have heq : (points a ds).toFinset = F := by simp [hlist]
      have hlen : ds.length + 1 = F.card := by
        simpa [points] using congrArg List.length hlist
      obtain ⟨ha, hend⟩ := endpoints_mem a ds
      have mem_iff (x : ℕ) : x ∈ points a ds ↔ x ∈ F := by simp [hlist]
      have hmin := hsch a ((mem_iff _).mp ha)
      have hlast := (Finset.mem_Icc.mp (hsub ((mem_iff _).mp hend))).2
      have hbound := (mem_bounds ((mem_iff _).mpr hmax)).2
      let c : GapData u := {
        ones := a - (ds.length + 1)
        gaps := ds
        positive := hp
        ordered := (points_sparse_iff a hp).mp (heq ▸ hsp)
        total := by omega }
      have hstart : c.start = a := by dsimp [c, GapData.start]; omega
      refine ⟨c, Subtype.ext ?_⟩
      change (points c.start ds).toFinset = F
      rwa [hstart]

private def partList (k : ℕ) (ds : List ℕ) : List ℕ := List.replicate k 1 ++ ds.map Nat.succ

private theorem partList_sum (k : ℕ) (ds : List ℕ) :
    (partList k ds).sum = k + ds.length + ds.sum := by
  have h : (ds.map Nat.succ).sum = ds.length + ds.sum := by
    induction ds with
    | nil => rfl
    | cons d ds ih => simp only [List.map_cons, List.sum_cons, ih, List.length_cons]; omega
  simp [partList, h, Nat.add_assoc]

private theorem partList_sorted (k : ℕ) {ds : List ℕ} (hs : ds.Pairwise (· ≤ ·)) :
    (partList k ds).Pairwise (· ≤ ·) := by
  apply List.pairwise_append.mpr
  refine ⟨List.pairwise_replicate_of_refl, hs.map Nat.succ (fun _ _ => Nat.succ_le_succ), ?_⟩
  intro a ha b hb
  obtain rfl := List.eq_of_mem_replicate ha
  obtain ⟨b, _, rfl⟩ := List.mem_map.mp hb
  omega

private theorem partList_inj {k m : ℕ} {ds es : List ℕ}
    (hd : ∀ x ∈ ds, 0 < x) (he : ∀ x ∈ es, 0 < x) (h : partList k ds = partList m es) :
    k = m ∧ ds = es := by
  have recover (k : ℕ) (gs : List ℕ) (hp : ∀ x ∈ gs, 0 < x) :
      (partList k gs).filter (1 < ·) = gs.map Nat.succ := by
    simpa [partList] using hp
  have hg := congrArg (List.filter (decide <| 1 < ·)) h
  rw [recover _ _ hd, recover _ _ he] at hg
  have hds : ds = es := List.map_injective_iff.mpr Nat.succ_injective hg
  exact ⟨by simpa [partList, hds] using congrArg List.length h, hds⟩

private theorem exists_partList (xs : List ℕ) (hp : ∀ x ∈ xs, 0 < x)
    (hs : xs.Pairwise (· ≤ ·)) :
    ∃ k ds, (∀ d ∈ ds, 0 < d) ∧ ds.Pairwise (· ≤ ·) ∧ partList k ds = xs := by
  induction xs with
  | nil => exact ⟨0, [], by simp, by simp, rfl⟩
  | cons x xs ih =>
    by_cases hx : x = 1
    · subst x
      obtain ⟨k, ds, hd, hs', h⟩ := ih (fun y hy => hp y (.tail _ hy)) hs.tail
      refine ⟨k + 1, ds, hd, hs', ?_⟩
      simpa [partList, List.replicate_succ] using congrArg (1 :: ·) h
    · have hlarge : ∀ y ∈ x :: xs, 1 < y := by
        have := hp x (.head _)
        have := List.pairwise_cons.mp hs |>.1
        grind
      refine ⟨0, (x :: xs).map Nat.pred, ?_, hs.map Nat.pred (fun _ _ => Nat.pred_le_pred), ?_⟩
      · intro d hd
        obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hd
        exact Nat.lt_pred_iff.mpr (hlarge y hy)
      · simp only [partList, List.replicate_zero, List.nil_append, List.map_map]
        exact List.map_congr_left (fun y hy => Nat.succ_pred_eq_of_pos (hp y hy)) |>.trans
          (List.map_id _)

private def GapData.toPartition {u : ℕ} (c : GapData u) : Nat.Partition u where
  parts := partList c.ones c.gaps
  parts_pos := by
    intro x hx
    change x ∈ partList c.ones c.gaps at hx
    rcases List.mem_append.mp hx with hx | hx
    · simp [List.eq_of_mem_replicate hx]
    · obtain ⟨d, _, rfl⟩ := List.mem_map.mp hx
      exact Nat.succ_pos _
  parts_sum := (Multiset.sum_coe _).trans ((partList_sum _ _).trans c.total)

private theorem GapData.toPartition_bijective (u : ℕ) :
    Function.Bijective (GapData.toPartition (u := u)) := by
  constructor
  · intro c d h
    have he := congrArg Nat.Partition.parts h
    have hp := Multiset.coe_eq_coe.mp he
    have hl := hp.eq_of_pairwise' (partList_sorted c.ones c.ordered)
      (partList_sorted d.ones d.ordered)
    obtain ⟨hk, hg⟩ := partList_inj c.positive d.positive hl
    cases c
    cases d
    simp_all
  · intro p
    obtain ⟨k, ds, hd, hs, h⟩ := exists_partList p.parts.sort
      (fun x hx => p.parts_pos ((Multiset.mem_sort _).mp hx)) (Multiset.pairwise_sort _ _)
    have he : (↑(partList k ds) : Multiset ℕ) = p.parts := by simp [h]
    have hsum := congrArg Multiset.sum he
    simp only [Multiset.sum_coe, partList_sum, p.parts_sum] at hsum
    exact ⟨⟨k, ds, hd, hs, hsum⟩, Nat.Partition.ext he⟩

/-- **Counting Schreier sparse sets by partition numbers.** For every integer $n \ge 1$, the
number of Schreier sparse sets $F \subseteq \{1, \dots, n\}$ with $n \in F$ equals $p(n - 1)$,
the number of partitions of $n - 1$.

Source: Kevin Beanland and Hùng Việt Chu, "On Schreier-Type
Sets, Partitions, and Compositions", Corollary 3. -/
theorem schreierSparseCount_eq (n : ℕ) (hn : 1 ≤ n) :
    schreierSparseCount n = partitionCount (n - 1) := by
  obtain _ | u := n
  · omega
  change (family (u + 1)).card = Fintype.card (Nat.Partition u)
  rw [← Fintype.card_coe]
  exact Fintype.card_congr ((Equiv.ofBijective _ (GapData.toSet_bijective u)).symm.trans
    (Equiv.ofBijective _ (GapData.toPartition_bijective u)))

end MathlibExt.Combinatorics.Enumerative.SchreierTypeSetsWanted

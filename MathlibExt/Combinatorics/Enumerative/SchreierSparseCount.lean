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
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Multiset

/-!
# Counting Schreier sparse sets

The number of Schreier sparse sets with maximum `n ≥ 1` is the partition number of `n - 1`.
The bijection of Beanland and Chu increments each consecutive gap and adds one part of size
one for each unit by which the minimum exceeds the cardinality.

For `k ≥ 2`, the sparse `ℓ`-strong Schreier sets with maximum `n + 1` and `k + 1` elements whose
two largest gaps are equal are as many as the partitions of `n` into exactly `k` parts, all at
least `ℓ + 1`. The bijection of Beanland and Chu adds `ℓ` to every gap, then adds the excess of
the minimum over `ℓ k + 1` to one of the two largest parts.
When `n ≥ ℓ + 1`, summing over `k ≥ 2` and adding the one-part partition gives the total count.

## References

* Kevin Beanland and Hùng Việt Chu, *On Schreier-Type Sets, Partitions, and Compositions*,
  Journal of Integer Sequences 27 (2024), Article 24.4.4, pp. 1–13, Corollaries 3, 12 and 13.
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

/-! ### Refined Schreier sets with a given number of elements -/

/-- **Strong Schreier sets.** For a natural number $\ell$, a finite set $A$ of natural numbers is
*$\ell$-strong Schreier* if $\ell |A| + 1 \le a + \ell$ for every $a \in A$; equivalently, $A$ is
empty or $\min A \ge \ell |A| - \ell + 1$. -/
def IsStrongSchreier (l : ℕ) (A : Finset ℕ) : Prop :=
  ∀ a ∈ A, l * A.card + 1 ≤ a + l

instance (l : ℕ) (A : Finset ℕ) : Decidable (IsStrongSchreier l A) := by
  unfold IsStrongSchreier; infer_instance

/-- **Partitions with a given number of parts, all at least a given size.** For natural numbers
$n$, $\ell$ and $k$, $|E_{n,\ell,k}|$ is the number of partitions of $n$ into exactly $k$ parts,
all of which are at least $\ell$. -/
def partitionMinPartExactCount (n l k : ℕ) : ℕ :=
  ((Nat.Partition.restricted n (fun x => l ≤ x)).filter
    (fun P => P.parts.card = k)).card

/-- **The refined Schreier family $F_{n,\ell}$.** For natural numbers $n$ and $\ell$, a finite
set $A$ of natural numbers belongs to $F_{n,\ell}$ if $n + 1$ is the largest element of $A$,
$A$ has at least three elements, $A$ is sparse and $\ell$-strong Schreier, and the two largest
elements $a < b$ of $A$ below $n + 1$ satisfy $n + 1 + a = 2b$. -/
def IsRefinedSchreier (n l : ℕ) (A : Finset ℕ) : Prop :=
  n + 1 ∈ A ∧ (∀ x ∈ A, x ≤ n + 1) ∧ 3 ≤ A.card ∧ IsSparse A ∧
    IsStrongSchreier l A ∧
      ∃ a ∈ A, ∃ b ∈ A, a < b ∧ b < n + 1 ∧
        (∀ x ∈ A, x ≤ b ∨ x = n + 1) ∧
          (∀ x ∈ A, x ≤ a ∨ x = b ∨ x = n + 1) ∧
            n + 1 + a = 2 * b

instance (n l : ℕ) (A : Finset ℕ) :
    Decidable (IsRefinedSchreier n l A) := by
  unfold IsRefinedSchreier; infer_instance

/-- **Refined Schreier sets with a given number of elements.** For natural numbers $n$ and
$\ell$, let $F_{n,\ell}$ be the family of finite sets $A$ of natural numbers such that $A$ has
largest element $n + 1$ and at least three elements, $A$ is sparse (the differences of
consecutive elements, in increasing order, are non-decreasing) and $\ell$-strong Schreier
($\ell|A| + 1 \le a + \ell$ for every $a \in A$), and the second and third largest elements
$b > a$ of $A$ satisfy $n + 1 + a = 2b$. For a natural number $k$, $|F_{n,\ell,k}|$ is the
number of sets in $F_{n,\ell}$ with exactly $k$ elements. -/
def refinedSchreierCardCount (n l k : ℕ) : ℕ :=
  ((Finset.Icc 0 (n + 1)).powerset.filter
    (fun A => IsRefinedSchreier n l A ∧ A.card = k)).card

private theorem foldl_add_eq (a : ℕ) (ds : List ℕ) : ds.foldl (· + ·) a = a + ds.sum := by
  induction ds generalizing a with
  | nil => simp
  | cons d ds ih => simp [ih, Nat.add_assoc]

-- Two final gaps add two final points.
private theorem mem_points_append_pair {a d e x : ℕ} {ds : List ℕ} :
    x ∈ points a (ds ++ [d, e]) ↔
      x ∈ points a ds ∨ x = a + ds.sum + d ∨ x = a + ds.sum + d + e := by
  simp [points, List.scanl_append, foldl_add_eq]

private theorem sum_map_add (l : ℕ) (ds : List ℕ) :
    (ds.map (· + l)).sum = ds.sum + l * ds.length := by
  induction ds with
  | nil => simp
  | cons d ds ih =>
    simp only [List.map_cons, List.sum_cons, ih, List.length_cons, Nat.mul_succ]
    omega

-- A list with at least two entries ends with two entries.
private theorem exists_append_pair (xs : List ℕ) (h : 2 ≤ xs.length) :
    ∃ ys u v, xs = ys ++ [u, v] := by
  rcases hr : xs.reverse with _ | ⟨v, _ | ⟨u, rest⟩⟩
  · have := congrArg List.length hr
    rw [List.length_reverse] at this
    simp only [List.length_nil] at this
    omega
  · have := congrArg List.length hr
    rw [List.length_reverse] at this
    simp only [List.length_cons, List.length_nil] at this
    omega
  · refine ⟨rest.reverse, u, v, ?_⟩
    rw [← List.reverse_reverse xs, hr]
    simp

-- A refined set with `k + 1` elements starts at `l * k + 1 + extra`, and its gaps are `low`
-- followed by two equal largest gaps `top`; the partition has parts `low + l`, `top + l` and
-- `top + extra + l`.
private structure RefinedData (n l k : ℕ) where
  extra : ℕ
  top : ℕ
  low : List ℕ
  top_pos : 0 < top
  positive : ∀ d ∈ low, 0 < d
  ordered : low.Pairwise (· ≤ ·)
  le_top : ∀ d ∈ low, d ≤ top
  length : low.length + 2 = k
  total : l * k + extra + low.sum + 2 * top = n

private abbrev RefinedData.start {n l k : ℕ} (c : RefinedData n l k) := l * k + 1 + c.extra

private abbrev RefinedData.gaps {n l k : ℕ} (c : RefinedData n l k) := c.low ++ [c.top, c.top]

private theorem RefinedData.gaps_positive {n l k : ℕ} (c : RefinedData n l k) :
    ∀ d ∈ c.gaps, 0 < d := by
  intro d hd
  rcases List.mem_append.mp hd with hd | hd
  · exact c.positive d hd
  · have : d = c.top := by simpa using hd
    exact this ▸ c.top_pos

private abbrev refinedFamily (n l k : ℕ) :=
  (Finset.Icc 0 (n + 1)).powerset.filter (fun A => IsRefinedSchreier n l A ∧ A.card = k)

private def RefinedData.toSet {n l k : ℕ} (c : RefinedData n l k) :
    refinedFamily n l (k + 1) := by
  let A := (points c.start c.gaps).toFinset
  have hstart : c.start = l * k + 1 + c.extra := rfl
  have hlen := c.length
  have hlast : c.start + c.low.sum + c.top + c.top = n + 1 := by
    have := c.total
    omega
  have hcard : A.card = k + 1 := by
    rw [List.toFinset_card_of_nodup (points_sorted c.start c.gaps_positive).sortedLT.nodup]
    simp [points, ← c.length]
  have hmem (x : ℕ) : x ∈ A ↔ x ∈ points c.start c.low ∨ x = c.start + c.low.sum + c.top ∨
      x = c.start + c.low.sum + c.top + c.top := by
    simp only [A, List.mem_toFinset]
    exact mem_points_append_pair
  have hs : c.start + c.low.sum ∈ points c.start c.low := (endpoints_mem _ _).2
  have htop := c.top_pos
  -- every point is at least the start, and the last three points are the largest
  have hbound (x : ℕ) (hx : x ∈ A) : c.start ≤ x ∧ (x ≤ c.start + c.low.sum ∨
      x = c.start + c.low.sum + c.top ∨ x = c.start + c.low.sum + c.top + c.top) := by
    rcases (hmem x).mp hx with hx | rfl | rfl
    · exact ⟨(mem_bounds hx).1, Or.inl (mem_bounds hx).2⟩
    · exact ⟨by omega, Or.inr (Or.inl rfl)⟩
    · exact ⟨by omega, Or.inr (Or.inr rfl)⟩
  refine ⟨A, Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr ?_, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, hcard⟩⟩
  · intro x hx
    have := hbound x hx
    rw [Finset.mem_Icc]
    omega
  · exact (hmem _).mpr (Or.inr (Or.inr hlast.symm))
  · intro x hx
    have := hbound x hx
    omega
  · omega
  · refine (points_sparse_iff _ c.gaps_positive).mpr (List.pairwise_append.mpr
      ⟨c.ordered, by simp, fun a ha b hb => ?_⟩)
    have : b = c.top := by simpa using hb
    exact this ▸ c.le_top a ha
  · intro x hx
    have := (hbound x hx).1
    rw [hcard, Nat.mul_succ]
    omega
  · refine ⟨c.start + c.low.sum, (hmem _).mpr (Or.inl hs), c.start + c.low.sum + c.top,
      (hmem _).mpr (Or.inr (Or.inl rfl)), by omega, by omega, fun x hx => ?_, fun x hx => ?_,
      by omega⟩
    · have := hbound x hx
      omega
    · have := hbound x hx
      omega

private theorem RefinedData.toSet_bijective (n l k : ℕ) (hk : 2 ≤ k) :
    Function.Bijective (RefinedData.toSet (n := n) (l := l) (k := k)) := by
  constructor
  · intro c d h
    have sort_points (v : RefinedData n l k) : v.toSet.val.sort = points v.start v.gaps := by
      have hs := (points_sorted v.start v.gaps_positive).sortedLT
      exact (List.toFinset_sort _ hs.nodup).mpr hs.sortedLE.pairwise
    have he := congrArg (fun v : refinedFamily n l (k + 1) => v.val.sort) h
    simp only [sort_points] at he
    obtain ⟨hstart, hgaps⟩ := points_inj he
    obtain ⟨hlow, htop⟩ := List.append_inj' hgaps rfl
    have htop' : c.top = d.top := by simpa using htop
    have hextra : c.extra = d.extra := by
      simp only [RefinedData.start] at hstart
      omega
    cases c
    cases d
    simp_all
  · rintro ⟨A, hA⟩
    obtain ⟨-, ⟨hmax, hle, -, hsp, hstrong, a', ha', b, hb, hab, hbn, hb_top, ha_top, hrel⟩,
      hcard⟩ := Finset.mem_filter.mp hA
    have hs := A.sortedLT_sort.pairwise
    cases he : A.sort with
    | nil =>
      have hm : n + 1 ∈ A.sort := (Finset.mem_sort _).mpr hmax
      simp [he] at hm
    | cons a t =>
      rw [he] at hs
      obtain ⟨ds, hp, hds⟩ := exists_points a t hs
      have hlist := hds.trans he.symm
      have mem_iff (x : ℕ) : x ∈ points a ds ↔ x ∈ A := by simp [hlist]
      have hlen : ds.length + 1 = A.card := by
        simpa [points] using congrArg List.length hlist
      obtain ⟨low, d, e, rfl⟩ := exists_append_pair ds (by omega)
      have hd : 0 < d := hp d (by simp)
      have he' : 0 < e := hp e (by simp)
      have hord := (points_sparse_iff a hp).mp (by
        have heq : (points a (low ++ [d, e])).toFinset = A := by simp [hlist]
        exact heq ▸ hsp)
      obtain ⟨hlow_ord, hde, hcross⟩ := List.pairwise_append.mp hord
      have hmem (x : ℕ) : x ∈ A ↔ x ∈ points a low ∨ x = a + low.sum + d ∨
          x = a + low.sum + d + e := by
        rw [← mem_iff]
        exact mem_points_append_pair
      have hbound (x : ℕ) (hx : x ∈ A) : a ≤ x ∧ (x ≤ a + low.sum ∨
          x = a + low.sum + d ∨ x = a + low.sum + d + e) := by
        rcases (hmem x).mp hx with hx | rfl | rfl
        · exact ⟨(mem_bounds hx).1, Or.inl (mem_bounds hx).2⟩
        · exact ⟨by omega, Or.inr (Or.inl rfl)⟩
        · exact ⟨by omega, Or.inr (Or.inr rfl)⟩
      have hs_mem : a + low.sum ∈ A := (hmem _).mpr (Or.inl (endpoints_mem _ _).2)
      have hsd_mem : a + low.sum + d ∈ A := (hmem _).mpr (Or.inr (Or.inl rfl))
      have hsde_mem : a + low.sum + d + e ∈ A := (hmem _).mpr (Or.inr (Or.inr rfl))
      have h1 := hle _ hsde_mem
      have h2 := hbound _ hmax
      have h3 := hbound _ hb
      have h4 := hbound _ ha'
      have h5 := hb_top _ hsd_mem
      have h6 := ha_top _ hs_mem
      have ha_mem : a ∈ A := (mem_iff a).mp (endpoints_mem a _).1
      have h7 := hstrong a ha_mem
      rw [hcard, Nat.mul_succ] at h7
      have hlen' : low.length + 2 = k := by
        simp only [List.length_append, List.length_cons, List.length_nil] at hlen
        omega
      -- the last two gaps are equal
      have hed : e = d := by omega
      subst hed
      let c : RefinedData n l k := {
        extra := a - (l * k + 1)
        top := e
        low := low
        top_pos := hd
        positive := fun x hx => hp x (by simp [hx])
        ordered := hlow_ord
        le_top := fun x hx => hcross x hx e (by simp)
        length := hlen'
        total := by omega }
      have hstart : c.start = a := by
        simp only [c, RefinedData.start]
        omega
      refine ⟨c, Subtype.ext ?_⟩
      change (points c.start (low ++ [e, e])).toFinset = A
      rw [hstart]
      simp [hlist]

private abbrev partFamily (n l k : ℕ) :=
  (Nat.Partition.restricted n (fun x => l + 1 ≤ x)).filter (fun P => P.parts.card = k)

private abbrev RefinedData.partsList {n l k : ℕ} (c : RefinedData n l k) : List ℕ :=
  c.low.map (· + l) ++ [c.top + l, c.top + c.extra + l]

private theorem RefinedData.partsList_sorted {n l k : ℕ} (c : RefinedData n l k) :
    c.partsList.Pairwise (· ≤ ·) := by
  refine List.pairwise_append.mpr ⟨List.pairwise_map.mpr (c.ordered.imp (by omega)),
    by simp, fun x hx y hy => ?_⟩
  obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hx
  have := c.le_top z hz
  simp at hy
  omega

private def RefinedData.toPartition {n l k : ℕ} (c : RefinedData n l k) : partFamily n l k := by
  have hall : ∀ x ∈ c.partsList, l + 1 ≤ x := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hx
      have := c.positive z hz
      omega
    · have := c.top_pos
      simp at hx
      omega
  have hsum : c.partsList.sum = n := by
    have := c.total
    have hmul : l * (c.low.length + 2) = l * k := congrArg (l * ·) c.length
    rw [Nat.mul_add] at hmul
    simp only [RefinedData.partsList, List.sum_append, sum_map_add, List.sum_cons, List.sum_nil]
    omega
  refine ⟨⟨c.partsList, fun hx => ?_, ?_⟩, ?_⟩
  · have := hall _ (Multiset.mem_coe.mp hx)
    omega
  · rw [Multiset.sum_coe]
    exact hsum
  · simp only [partFamily, Nat.Partition.restricted, Finset.mem_filter, Finset.mem_univ, true_and,
      Multiset.mem_coe, Multiset.coe_card]
    refine ⟨hall, ?_⟩
    simpa using c.length

private theorem RefinedData.toPartition_bijective (n l k : ℕ) (hk : 2 ≤ k) :
    Function.Bijective (RefinedData.toPartition (n := n) (l := l) (k := k)) := by
  constructor
  · intro c d h
    have he : (c.partsList : Multiset ℕ) = d.partsList :=
      congrArg (fun v : partFamily n l k => v.val.parts) h
    have hl := (Multiset.coe_eq_coe.mp he).eq_of_pairwise' c.partsList_sorted d.partsList_sorted
    obtain ⟨hlow, htail⟩ := List.append_inj' hl rfl
    have hlow' : c.low = d.low := List.map_injective_iff.mpr (add_left_injective l) hlow
    simp only [List.cons.injEq, and_true] at htail
    have htop : c.top = d.top := by omega
    have hextra : c.extra = d.extra := by omega
    cases c
    cases d
    simp_all
  · rintro ⟨P, hP⟩
    simp only [partFamily, Nat.Partition.restricted, Finset.mem_filter, Finset.mem_univ,
      true_and] at hP
    obtain ⟨hge, hcard⟩ := hP
    have hsorted : (P.parts.sort).Pairwise (· ≤ ·) := Multiset.pairwise_sort _ _
    have hxsP : ((P.parts.sort : List ℕ) : Multiset ℕ) = P.parts := Multiset.sort_eq _ _
    have hlen : (P.parts.sort).length = k := by
      rw [Multiset.length_sort]
      exact hcard
    obtain ⟨ys, u, v, hdec⟩ := exists_append_pair P.parts.sort (by omega)
    have hmem (x : ℕ) (hx : x ∈ ys ++ [u, v]) : l + 1 ≤ x :=
      hge x ((Multiset.mem_sort _).mp (hdec ▸ hx))
    have hsum : ys.sum + u + v = n := by
      have := congrArg Multiset.sum hxsP
      rw [Multiset.sum_coe, P.parts_sum, hdec] at this
      simpa [Nat.add_assoc] using this
    rw [hdec] at hsorted hlen
    obtain ⟨hys, huv, hcross⟩ := List.pairwise_append.mp hsorted
    have huv' : u ≤ v := by simpa using huv
    have hyu (y : ℕ) (hy : y ∈ ys) : y ≤ u := hcross y hy u (by simp)
    have hyl (y : ℕ) (hy : y ∈ ys) : l + 1 ≤ y := hmem y (by simp [hy])
    have hul : l + 1 ≤ u := hmem u (by simp)
    have hback : (ys.map (· - l)).map (· + l) = ys := by
      rw [List.map_map]
      conv_rhs => rw [← List.map_id ys]
      refine List.map_congr_left (fun y hy => ?_)
      have := hyl y hy
      simp only [Function.comp_apply, id_eq]
      omega
    have hsum' : (ys.map (· - l)).sum + l * ys.length = ys.sum := by
      have := sum_map_add l (ys.map (· - l))
      rw [hback, List.length_map] at this
      omega
    have hlen' : ys.length + 2 = k := by
      simpa using hlen
    refine ⟨{
      extra := v - u
      top := u - l
      low := ys.map (· - l)
      top_pos := by omega
      positive := ?_
      ordered := ?_
      le_top := ?_
      length := by simpa using hlen'
      total := ?_ }, ?_⟩
    · intro d hd
      obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hd
      have := hyl y hy
      omega
    · exact List.pairwise_map.mpr (hys.imp (fun h => Nat.sub_le_sub_right h l))
    · intro d hd
      obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hd
      exact Nat.sub_le_sub_right (hyu y hy) l
    · rw [← hlen', Nat.mul_add]
      omega
    · apply Subtype.ext
      apply Nat.Partition.ext
      change ((List.map (· + l) (List.map (· - l) ys) ++
        [u - l + l, u - l + (v - u) + l] : List ℕ) : Multiset ℕ) = P.parts
      rw [hback, ← hxsP, hdec]
      have h1 : u - l + l = u := by omega
      have h2 : u - l + (v - u) + l = v := by omega
      rw [h1, h2]

-- The source states the identity for `n ≥ ℓ + 1`; the bijection does not need this bound.
set_option linter.unusedVariables false in
/-- **Partitions with a fixed number of large parts and refined Schreier sets.** Let $n$,
$\ell$ and $k$ be natural numbers with $n \ge \ell + 1$ and $k \ge 2$. Let $F_{n,\ell}$ be the
family of finite sets $A$ of natural numbers such that $A$ has largest element $n + 1$ and at
least three elements, $A$ is sparse (the differences of consecutive elements, in increasing
order, are non-decreasing) and $\ell$-strong Schreier ($\ell|A| + 1 \le a + \ell$ for every
$a \in A$), and the second and third largest elements $b > a$ of $A$ satisfy
$n + 1 + a = 2b$. Then the number $|E_{n,\ell+1,k}|$ of partitions of $n$ into exactly $k$
parts, all at least $\ell + 1$, equals the number $|F_{n,\ell,k+1}|$ of sets in $F_{n,\ell}$
with exactly $k + 1$ elements.

Source: Kevin Beanland and Hùng Việt Chu, "On Schreier-Type
Sets, Partitions, and Compositions", Corollary 12. -/
theorem partitionMinPartExactCount_eq_refined (n l k : ℕ)
    (hn : l + 1 ≤ n) (hk : 2 ≤ k) :
    partitionMinPartExactCount n (l + 1) k =
      refinedSchreierCardCount n l (k + 1) := by
  change (partFamily n l k).card = (refinedFamily n l (k + 1)).card
  rw [← Fintype.card_coe, ← Fintype.card_coe (refinedFamily n l (k + 1))]
  exact Fintype.card_congr
    ((Equiv.ofBijective _ (RefinedData.toPartition_bijective n l k hk)).symm.trans
      (Equiv.ofBijective _ (RefinedData.toSet_bijective n l k hk)))

/-! ### Total counts -/

/-- **Partitions with all parts at least a given size.** For natural numbers $n$ and $\ell$,
$|E_{n,\ell}|$ is the number of partitions of $n$ all of whose parts are at least $\ell$. -/
def partitionMinPartCount (n l : ℕ) : ℕ :=
  (Nat.Partition.restricted n (fun x => l ≤ x)).card

/-- **Refined Schreier count.** For natural numbers $n$ and $\ell$, $|F_{n,\ell}|$ is the number of
finite sets $A$ of natural numbers such that $n + 1 \in A$, every element of $A$ is at most
$n + 1$, $A$ has at least three elements, $A$ is sparse and $\ell$-strong Schreier, and the two
largest elements $a < b$ of $A$ below $n + 1$ satisfy $n + 1 + a = 2b$. Every such set is
contained in $\{0, \dots, n + 1\}$. -/
def refinedSchreierCount (n l : ℕ) : ℕ :=
  ((Finset.Icc 0 (n + 1)).powerset.filter
    (IsRefinedSchreier n l)).card

private theorem partitionMinPartExactCount_one (n l : ℕ) (hn : l + 1 ≤ n) :
    partitionMinPartExactCount n (l + 1) 1 = 1 := by
  have hp := Nat.Partition.indiscrete_parts (n := n) (by omega)
  have hf : partFamily n l 1 = {Nat.Partition.indiscrete n} := by
    ext P
    simp only [partFamily, Nat.Partition.restricted, Finset.mem_filter, Finset.mem_univ,
      true_and, Finset.mem_singleton]
    constructor
    · rintro ⟨-, hcard⟩
      obtain ⟨a, ha⟩ := Multiset.card_eq_one.mp hcard
      have hsum := P.parts_sum
      rw [ha, Multiset.sum_singleton] at hsum
      exact Nat.Partition.ext (by rw [hp, ha, hsum])
    · rintro rfl
      simp [hp, hn]
  change (partFamily n l 1).card = 1
  rw [hf, Finset.card_singleton]

/-- **Partitions into large parts and the refined Schreier family.** Let $n$ and $\ell$ be
natural numbers with $n \ge \ell + 1$. Let $F_{n,\ell}$ be the family of finite sets $A$ of
natural numbers such that $A$ has largest element $n + 1$ and at least three elements, $A$ is
sparse (the differences of consecutive elements, in increasing order, are non-decreasing) and
$\ell$-strong Schreier ($\ell|A| + 1 \le a + \ell$ for every $a \in A$), and the second and
third largest elements $b > a$ of $A$ satisfy $n + 1 + a = 2b$. Then the number
$|E_{n,\ell+1}|$ of partitions of $n$ into parts that are all at least $\ell + 1$ equals
$|F_{n,\ell}| + 1$.

Source: Kevin Beanland and Hùng Việt Chu, "On Schreier-Type
Sets, Partitions, and Compositions", Corollary 13. -/
theorem partitionMinPartCount_eq_refined_add_one (n l : ℕ)
    (hn : l + 1 ≤ n) :
    partitionMinPartCount n (l + 1) = refinedSchreierCount n l + 1 := by
  have hp : partitionMinPartCount n (l + 1) =
      ∑ k ∈ insert 1 (Finset.Icc 2 (n + 1)), partitionMinPartExactCount n (l + 1) k := by
    unfold partitionMinPartCount
    refine Finset.card_eq_sum_card_fiberwise (f := fun P : Nat.Partition n => P.parts.card) ?_
    intro P _
    have hpos : 0 < P.parts.card := by
      apply Nat.pos_of_ne_zero
      intro hzero
      have hz := Multiset.card_eq_zero.mp hzero
      have hn0 : n ≠ 0 := by omega
      exact hn0 (by simpa [hz] using P.parts_sum.symm)
    have hle : P.parts.card ≤ n := by
      simpa [P.parts_sum] using Multiset.card_nsmul_le_sum (a := 1) (fun _ hx => P.parts_pos hx)
    simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_Icc]
    omega
  have hf : refinedSchreierCount n l =
      ∑ j ∈ Finset.Icc 3 (n + 2), refinedSchreierCardCount n l j := by
    unfold refinedSchreierCount
    rw [Finset.card_eq_sum_card_fiberwise (f := Finset.card) (t := Finset.Icc 3 (n + 2))]
    · simp only [refinedSchreierCardCount, Finset.filter_filter, and_comm]
    · intro A hA
      obtain ⟨hsub, href⟩ := Finset.mem_filter.mp hA
      refine Finset.mem_Icc.mpr ⟨href.2.2.1, ?_⟩
      simpa using Finset.card_le_card (Finset.mem_powerset.mp hsub)
  have hsum : (∑ k ∈ Finset.Icc 2 (n + 1), partitionMinPartExactCount n (l + 1) k) =
      ∑ j ∈ Finset.Icc 3 (n + 2), refinedSchreierCardCount n l j := by
    refine Finset.sum_bij (fun k _ => k + 1) ?_ ?_ ?_ ?_
    · intro k hk
      simp only [Finset.mem_Icc] at hk ⊢
      omega
    · intro a _ b _ h
      exact Nat.add_right_cancel h
    · intro j hj
      rw [Finset.mem_Icc] at hj
      exact ⟨j - 1, Finset.mem_Icc.mpr (by omega), by omega⟩
    · intro k hk
      exact partitionMinPartExactCount_eq_refined n l k hn (Finset.mem_Icc.mp hk).1
  rw [hp, Finset.sum_insert (by simp), partitionMinPartExactCount_one n l hn, hsum, hf, add_comm]

end MathlibExt.Combinatorics.Enumerative.SchreierTypeSetsWanted

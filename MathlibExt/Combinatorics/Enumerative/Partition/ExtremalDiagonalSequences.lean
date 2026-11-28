/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Enumerative.Partition.DiagonalSequences
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Combinatorics.Enumerative.Partition.YoungDiagram
import Mathlib.Data.List.GetD
import Mathlib.Data.List.Range

/-!
# Diagonal sequences of the maximal and minimal partitions

The two conjugate partitions associated with a diagonal normal form realize that form,
and its entries are the parts of the minimal partition with multiplicity.

The number of partitions with a given diagonal sequence is a product of binomial
coefficients. Row `i` of a partition, counted from `0`, ends on the diagonal `αᵢ + i`, where
`αᵢ = 0` for the rows past the last part. The diagonal sequence fixes the multiset of these
ends for the rows `0, …, L`, where `L` is its last nonzero index, and the ends form a word
that ends at `L` and whose steps go up by at most one. Conversely, every such arrangement of
that multiset comes from exactly one partition of the class. Deleting the smallest letter `a`
leaves a word of the same kind; the deleted letters stand in blocks immediately before the
letters `a + 1`, so the word is recovered from the shorter word and the sizes of the blocks.
When the number of parts is the staircase height, the zero rows form a fixed suffix, and
removing it leaves an arrangement with one fewer copy of each letter and no prescribed ending.

For a diagonal normal form of staircase height `q ≥ 1` with arbitrary natural multiplicities
`s₁, …, s_q` after the staircase, capping each at two preserves the size of the diagonal class.
In the binomial product, deleting a copy from three equal consecutive heights removes a unit
factor.

## References

* Michael Neubauer and Harmony Vargas, *Diagonal Sequences of Integer Partitions*, INTEGERS 25
  (2025), Article A60, pp. 1–17. Corollary 3 (p. 5), Proposition 8 (p. 10), Theorem 1 (p. 12),
  and Corollary 6 (5) (p. 13).
* The staircase sum uses the same reduction to `Finset.sum_range_id` as `staircase_sum` in
  `MathlibExt.Combinatorics.Enumerative.Partition.OverpartitionMexSum`.
-/

namespace MetaMathlibExt

namespace diagonalSequence_max_eq_min_and_multiset

open Finset

-- The rows meeting a fixed column form an initial segment of the row indices.
private theorem lt_count_rows {f : ℕ → ℕ} (hf : Antitone f) (n i b : ℕ) :
    i < ((Multiset.range n).map f).countP (b ≤ ·) ↔ i < n ∧ b ≤ f i := by
  rw [Multiset.countP_map]
  change i < ((range n).filter fun j => b ≤ f j).card ↔ _
  constructor
  · intro h
    have hin := (card_filter_le (range n) (fun j => b ≤ f j)).trans_eq (card_range n)
    refine ⟨by omega, ?_⟩
    by_contra! hlt
    have hsub : ((range n).filter fun j => b ≤ f j) ⊆ range i := by
      intro j hj
      apply mem_range.mpr
      by_contra! hle
      exact hlt.not_ge ((mem_filter.mp hj).2.trans (hf hle))
    have := (card_le_card hsub).trans_eq (card_range i)
    omega
  · rintro ⟨hin, hb⟩
    have hsub : range (i + 1) ⊆ (range n).filter fun j => b ≤ f j := by
      intro j hj
      have hji : j ≤ i := Nat.le_of_lt_succ (mem_range.mp hj)
      exact mem_filter.mpr ⟨mem_range.mpr (hji.trans_lt hin), hb.trans (hf hji)⟩
    simpa using card_le_card hsub

-- Transposing a cell interchanges its row and column while preserving its diagonal.
private theorem conjugate_cell (rows : Multiset ℕ) (i j : ℕ) :
    j < (conjugateParts rows).countP (i + 1 ≤ ·) ↔ i < rows.countP (j < ·) := by
  have anti : Antitone (fun k : ℕ => rows.countP (k < ·)) := by
    intro a b hab
    dsimp only
    rw [Multiset.countP_eq_card_filter, Multiset.countP_eq_card_filter]
    exact Multiset.card_le_card (Multiset.monotone_filter_right rows fun _ h => hab.trans_lt h)
  rw [conjugateParts, lt_count_rows anti]
  constructor
  · exact And.right
  · intro h
    obtain ⟨x, hx, hj⟩ := Multiset.countP_pos.mp (Nat.zero_lt_of_lt h)
    exact ⟨hj.trans_le (Multiset.le_sup hx), h⟩

private theorem diagonal_conjugate (rows : Multiset ℕ) :
    diagonalSequence rows = diagonalSequence (conjugateParts rows) := by
  funext k
  unfold diagonalSequence
  let flip (i : ℕ) := k + 1 - i
  have flip_mem {i} (hi : i ∈ Icc 1 k) : flip i ∈ Icc 1 k := by
    simp only [mem_Icc, flip] at *
    omega
  have invol {i} (hi : i ∈ Icc 1 k) : flip (flip i) = i := by
    simp only [mem_Icc, flip] at *
    omega
  have cell {i} (hi : i ∈ Icc 1 k) :
      flip i ≤ (conjugateParts rows).countP (i ≤ ·) ↔ i ≤ rows.countP (flip i ≤ ·) := by
    obtain ⟨a, ha⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt (mem_Icc.mp hi).1)
    obtain ⟨b, hb⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt (mem_Icc.mp (flip_mem hi)).1)
    rw [hb, ha]
    exact conjugate_cell rows a b
  apply card_bij (fun i _ => flip i)
  · intro i hi
    obtain ⟨hit, hc⟩ := mem_filter.mp hi
    refine mem_filter.mpr ⟨flip_mem hit, ?_⟩
    change flip i ≤ (conjugateParts rows).countP (flip (flip i) ≤ ·)
    rw [invol hit]
    exact (cell hit).mpr hc
  · intro i hi j hj h
    simpa only [invol (mem_filter.mp hi).1, invol (mem_filter.mp hj).1] using congrArg flip h
  · intro j hj
    obtain ⟨hjt, hc⟩ := mem_filter.mp hj
    refine ⟨flip j, mem_filter.mpr ⟨flip_mem hjt, ?_⟩, invol hjt⟩
    exact (cell (flip_mem hjt)).mp (by simpa only [invol hjt] using hc)

-- The weakly decreasing tail consists of a block of length s j at each height j.
private def blocks (q : ℕ) (s : ℕ → ℕ) : List ℕ :=
  (List.range q).reverse.flatMap fun j => List.replicate (s (j + 1)) (j + 1)

private theorem blocks_succ (q : ℕ) (s : ℕ → ℕ) :
    blocks (q + 1) s = List.replicate (s (q + 1)) (q + 1) ++ blocks q s := by
  simp [blocks, List.range_succ]

private theorem le_blocks_getD (q : ℕ) (s : ℕ → ℕ) (h m : ℕ) (hh : 0 < h) :
    h ≤ (blocks q s).getD m 0 ↔ h ≤ q ∧ m < ∑ j ∈ Icc h q, s j := by
  induction q generalizing m with
  | zero => simp [blocks, hh.ne']
  | succ q ih =>
    rw [blocks_succ]
    by_cases hm : m < s (q + 1)
    · rw [List.getD_append _ _ _ _ (by simpa using hm), List.getD_replicate _ hm]
      refine ⟨fun hq => ⟨hq, ?_⟩, And.left⟩
      rw [sum_Icc_succ_top hq]
      omega
    · rw [List.getD_append_right _ _ _ _ (by simpa using Nat.le_of_not_gt hm),
        List.length_replicate, ih]
      by_cases hq : h ≤ q
      · rw [sum_Icc_succ_top (by omega : h ≤ q + 1)]
        omega
      · by_cases heq : h = q + 1
        · subst h
          simp [hm]
        · omega

-- At height h the normal form occupies exactly the diagonals from h to
-- q + s h + ... + s q, including both endpoints.
private theorem le_normalForm (q : ℕ) (s : ℕ → ℕ) (h k : ℕ) (hh : 0 < h) :
    h ≤ diagonalOfList (diagonalNormalForm q s) k ↔
      h ≤ k ∧ h ≤ q ∧ k ≤ q + ∑ j ∈ Icc h q, s j := by
  cases k with
  | zero => simp [diagonalOfList, hh.ne']
  | succ k =>
    change h ≤ (List.range' 1 q ++ blocks q s).getD k 0 ↔ _
    by_cases hk : k < q
    · have hlen : k < (List.range' 1 q).length := by simpa using hk
      rw [List.getD_append _ _ _ _ hlen, List.getD_eq_getElem _ _ hlen, List.getElem_range'_1]
      omega
    · rw [List.getD_append_right _ _ _ _ (by simpa using Nat.le_of_not_gt hk),
        List.length_range', le_blocks_getD _ _ _ _ hh]
      omega

private theorem diagonal_max (q : ℕ) (s : ℕ → ℕ) :
    diagonalSequence ↑(diagonalMaxPartition q s) = diagonalOfList (diagonalNormalForm q s) := by
  let row (i : ℕ) := q - i + ∑ j ∈ Icc (i + 1) q, s j
  have anti : Antitone row := by
    intro a b hab
    exact Nat.add_le_add (Nat.sub_le_sub_left hab q)
      (sum_le_sum_of_subset (Icc_subset_Icc (by omega) le_rfl))
  funext k
  unfold diagonalSequence
  -- Row i meets diagonal k precisely when the normal form there has height at least i.
  suffices ((Icc 1 k).filter fun i =>
      i ≤ (↑(diagonalMaxPartition q s) : Multiset ℕ).countP (k + 1 - i ≤ ·)) =
      Icc 1 (diagonalOfList (diagonalNormalForm q s) k) by
    rw [this, Nat.card_Icc]
    omega
  ext i
  simp only [mem_filter, mem_Icc]
  cases i with
  | zero => simp
  | succ i =>
    rw [le_normalForm _ _ _ _ (by omega)]
    simp only [diagonalMaxPartition, ← Multiset.map_coe, Multiset.coe_range]
    change (_ ∧ i < ((Multiset.range q).map row).countP (k + 1 - (i + 1) ≤ ·)) ↔ _
    rw [lt_count_rows anti]
    dsimp [row]
    omega

private theorem normalForm_parts (q : ℕ) (s : ℕ → ℕ) :
    (↑(diagonalNormalForm q s) : Multiset ℕ) = ↑(diagonalMinPartition q s) := by
  change ↑(List.range' 1 q ++ blocks q s) = (↑(blocks q fun k => s k + 1) : Multiset ℕ)
  induction q with
  | zero => rfl
  | succ q ih =>
    simp only [← Multiset.coe_add] at ih
    rw [List.range'_concat, blocks_succ, blocks_succ]
    simp only [one_mul, Nat.one_add, ← Multiset.coe_add, Multiset.coe_replicate,
      Multiset.replicate_succ, Multiset.coe_singleton, ← Multiset.singleton_add]
    rw [← ih]
    ac_rfl

end diagonalSequence_max_eq_min_and_multiset

open diagonalSequence_max_eq_min_and_multiset in
/-- **Equal diagonal sequences of the maximal and minimal partitions.** Let $q \ge 0$ and
$s_1, \dots, s_q \ge 0$ be natural numbers, write $v^{(m)}$ for $m$ copies of $v$, and let
$\bar\alpha$ and $\underline\alpha$ be the partitions with parts
$\bar\alpha_i = q - i + 1 + s_i + s_{i+1} + \dots + s_q$ for $1 \le i \le q$ and
$\underline\alpha = (q^{(s_q + 1)}, (q-1)^{(s_{q-1} + 1)}, \dots, 1^{(s_1 + 1)})$. Then
$\bar\alpha$ and $\underline\alpha$ have the same diagonal sequence; this diagonal sequence,
indexed from $0$, is $(0, 1, 2, \dots, q, q^{(s_q)}, \dots, 1^{(s_1)}, 0, 0, \dots)$; and the
multiset of its nonzero entries $1, 2, \dots, q, q^{(s_q)}, \dots, 1^{(s_1)}$ equals the multiset
of parts of $\underline\alpha$.

Source: Michael Neubauer and Harmony Vargas, *Diagonal Sequences of Integer Partitions*,
INTEGERS 25 (2025), Article A60, Corollary 3. -/
public theorem diagonalSequence_max_eq_min_and_multiset (q : ℕ) (s : ℕ → ℕ) :
    diagonalSequence ↑(diagonalMaxPartition q s) =
        diagonalSequence ↑(diagonalMinPartition q s) ∧
      diagonalSequence ↑(diagonalMinPartition q s) = diagonalOfList (diagonalNormalForm q s) ∧
      (↑(diagonalNormalForm q s) : Multiset ℕ) = ↑(diagonalMinPartition q s) := by
  have h := diagonal_conjugate (↑(diagonalMaxPartition q s))
  rw [conjugateParts_diagonalMaxPartition] at h
  exact ⟨h, h.symm.trans (diagonal_max q s), normalForm_parts q s⟩

namespace card_diagonalClass_eq_prod_choose

open Finset

/-! ### Words whose steps go up by at most one -/

-- Steps of the word go up by at most one.
private abbrev Vn (w : List ℕ) : Prop := w.IsChain fun x y => y ≤ x + 1

-- The words with letters `F`, steps up by at most one, and last letter `top`.
private def words (F : Multiset ℕ) (top : ℕ) : Set (List ℕ) :=
  {w | (w : Multiset ℕ) = F ∧ Vn w ∧ w.getLast? = some top}

-- The weak compositions of `n` into `k` parts.
private def comps (n k : ℕ) : Set (List ℕ) := {g | g.length = k ∧ g.sum = n}

private def incHead : List ℕ → List ℕ
  | [] => []
  | g :: gs => (g + 1) :: gs

private theorem incHead_injective : Function.Injective incHead := by
  intro g h hgh
  cases g <;> cases h <;> simp_all [incHead]

private theorem ncard_comps (k : ℕ) : ∀ n, (comps n (k + 1)).ncard = (n + k).choose n := by
  induction k with
  | zero =>
    intro n
    have : comps n 1 = {[n]} := by
      ext g
      simp only [comps, Set.mem_ofPred_eq, Set.mem_singleton_iff, List.length_eq_one_iff]
      constructor
      · rintro ⟨⟨a, rfl⟩, h⟩
        simp_all
      · rintro rfl
        exact ⟨⟨n, rfl⟩, by simp⟩
    simp [this]
  | succ k ihk =>
    intro n
    induction n with
    | zero =>
      have : comps 0 (k + 1 + 1) = {List.replicate (k + 2) 0} := by
        ext g
        simp only [comps, Set.mem_ofPred_eq, Set.mem_singleton_iff, List.sum_eq_zero_iff,
          List.eq_replicate_iff]
      simp [this]
    | succ n ihn =>
      have hsplit : comps (n + 1) (k + 1 + 1) =
          (List.cons 0 '' comps (n + 1) (k + 1)) ∪ (incHead '' comps n (k + 1 + 1)) := by
        ext g
        simp only [comps, Set.mem_union, Set.mem_image, Set.mem_ofPred_eq]
        constructor
        · rintro ⟨hlen, hsum⟩
          match g, hlen, hsum with
          | 0 :: g', hlen, hsum =>
            exact Or.inl ⟨g', ⟨by simpa using hlen, by simpa using hsum⟩, rfl⟩
          | (x + 1) :: g', hlen, hsum =>
            refine Or.inr ⟨x :: g', ⟨by simpa using hlen, ?_⟩, rfl⟩
            simp only [List.sum_cons] at hsum ⊢
            omega
        · rintro (⟨g', ⟨hlen, hsum⟩, rfl⟩ | ⟨g', ⟨hlen, hsum⟩, rfl⟩)
          · exact ⟨by simpa using hlen, by simpa using hsum⟩
          · match g', hlen, hsum with
            | x :: g'', hlen, hsum =>
              refine ⟨by simpa [incHead] using hlen, ?_⟩
              simp only [incHead, List.sum_cons] at hsum ⊢
              omega
      have hA := ihk (n + 1)
      have hB := ihn
      have hA' : (List.cons 0 '' comps (n + 1) (k + 1)).ncard = (n + 1 + k).choose (n + 1) := by
        rw [Set.ncard_image_of_injective _ (List.cons_injective), hA]
      have hB' : (incHead '' comps n (k + 1 + 1)).ncard = (n + (k + 1)).choose n := by
        rw [Set.ncard_image_of_injective _ incHead_injective, hB]
      have hposA : 0 < (List.cons 0 '' comps (n + 1) (k + 1)).ncard := by
        rw [hA']
        exact Nat.choose_pos (by omega)
      have hposB : 0 < (incHead '' comps n (k + 1 + 1)).ncard := by
        rw [hB']
        exact Nat.choose_pos (by omega)
      rw [hsplit, Set.ncard_union_eq ?_ (Set.finite_of_ncard_pos hposA)
        (Set.finite_of_ncard_pos hposB), hA', hB']
      · rw [show n + 1 + (k + 1) = (n + k + 1) + 1 by omega, Nat.choose_succ_succ,
          show n + 1 + k = n + k + 1 by omega, show n + (k + 1) = n + k + 1 by omega,
          Nat.succ_eq_add_one]
        omega
      · rw [Set.disjoint_left]
        rintro g ⟨g', _, rfl⟩ ⟨g'', _, h⟩
        cases g'' <;> simp [incHead] at h

/-! ### Peeling off the smallest letter -/

-- For each occurrence of `a + 1`, the number of letters `a` immediately before it.
private def runs (a : ℕ) : List ℕ → List ℕ
  | [] => []
  | y :: ys => if y = a then incHead (runs a ys) else if y = a + 1 then 0 :: runs a ys
      else runs a ys

-- Put `g j` letters `a` immediately before the `j`-th occurrence of `a + 1`.
private def expand (a : ℕ) : List ℕ → List ℕ → List ℕ
  | [], _ => []
  | y :: ys, g => if y = a + 1 then List.replicate (g.headD 0) a ++ y :: expand a ys g.tail
      else y :: expand a ys g

private theorem length_runs (a : ℕ) (w : List ℕ) : (runs a w).length = w.count (a + 1) := by
  induction w with
  | nil => rfl
  | cons y ys ih =>
    by_cases h1 : y = a
    · subst h1
      have : (runs y ys).length = (incHead (runs y ys)).length := by
        cases runs y ys <;> rfl
      simp [runs, ← this, ih]
    · by_cases h2 : y = a + 1
      · subst h2
        simp [runs, ih]
      · simp [runs, h1, h2, ih]

-- Words in which every letter is at least `a` and the last letter is not `a`.
private def Good (a : ℕ) (w : List ℕ) : Prop :=
  Vn w ∧ (∀ x ∈ w, a ≤ x) ∧ ∀ x ∈ w.getLast?, x ≠ a

private theorem Good.tail {a y : ℕ} {ys : List ℕ} (h : Good a (y :: ys)) : Good a ys := by
  refine ⟨(List.isChain_cons.mp h.1).2, fun x hx => h.2.1 x (List.mem_cons_of_mem _ hx), ?_⟩
  intro x hx
  apply h.2.2 x
  rw [List.getLast?_cons, hx]
  rfl

private theorem Good.ne_nil {a y : ℕ} {ys : List ℕ} (h : Good a (y :: ys)) (hy : y = a) :
    ys ≠ [] := by
  rintro rfl
  exact h.2.2 y rfl hy

private theorem Good.head_le {a y : ℕ} {ys : List ℕ} (h : Good a (y :: ys)) (hy : y = a) :
    ∀ x ∈ ys.head?, x ≤ a + 1 := by
  intro x hx
  have := (List.isChain_cons.mp h.1).1 x hx
  omega

-- After a block of letters `a`, the next letter other than `a` is `a + 1`.
private theorem head?_filter {a : ℕ} : ∀ {ys : List ℕ}, Good a ys → ys ≠ [] →
    (∀ x ∈ ys.head?, x ≤ a + 1) → (ys.filter (· ≠ a)).head? = some (a + 1)
  | [], _, hne, _ => absurd rfl hne
  | z :: zs, hg, _, hh => by
    by_cases hz : z = a
    · rw [List.filter_cons, ite_eq_right (by simpa using hz)]
      exact head?_filter hg.tail (hg.ne_nil hz) (hg.head_le hz)
    · have hle := hh z rfl
      have hge := hg.2.1 z List.mem_cons_self
      have hza : z = a + 1 := by omega
      rw [List.filter_cons, ite_eq_left (by simpa using hz)]
      simp [hza]

private theorem runs_ne_nil {a : ℕ} {ys : List ℕ} (hg : Good a ys) (hne : ys ≠ [])
    (hh : ∀ x ∈ ys.head?, x ≤ a + 1) : runs a ys ≠ [] := by
  have hmem : a + 1 ∈ ys :=
    (List.mem_filter.mp (List.mem_of_mem_head? (head?_filter hg hne hh))).1
  intro h
  have := length_runs a ys
  rw [h, List.length_nil] at this
  exact (List.count_pos_iff.mpr hmem).ne this

private theorem sum_runs {a : ℕ} : ∀ {w : List ℕ}, Good a w → (runs a w).sum = w.count a
  | [], _ => rfl
  | y :: ys, hg => by
    by_cases h1 : y = a
    · subst h1
      have hne := runs_ne_nil hg.tail (hg.ne_nil rfl) (hg.head_le rfl)
      have ih := sum_runs hg.tail
      obtain ⟨g, gs, hgs⟩ := List.exists_cons_of_ne_nil hne
      simp only [runs, List.count_cons, beq_self_eq_true, ite_true]
      rw [hgs] at ih ⊢
      simp only [incHead, List.sum_cons] at ih ⊢
      omega
    · by_cases h2 : y = a + 1
      · subst h2
        simp [runs, sum_runs hg.tail]
      · simp [runs, h1, h2, sum_runs hg.tail]

private theorem expand_succ {a : ℕ} {w : List ℕ} (hw : w.head? = some (a + 1)) (g : ℕ)
    (gs : List ℕ) : expand a w ((g + 1) :: gs) = a :: expand a w (g :: gs) := by
  cases w with
  | nil => simp at hw
  | cons x xs =>
    obtain rfl : x = a + 1 := by simpa using hw
    simp [expand, List.replicate_succ]

private theorem expand_filter_runs {a : ℕ} : ∀ {w : List ℕ}, Good a w →
    expand a (w.filter (· ≠ a)) (runs a w) = w
  | [], _ => rfl
  | y :: ys, hg => by
    by_cases h1 : y = a
    · subst h1
      have hne := runs_ne_nil hg.tail (hg.ne_nil rfl) (hg.head_le rfl)
      have hhead := head?_filter hg.tail (hg.ne_nil rfl) (hg.head_le rfl)
      have ih := expand_filter_runs hg.tail
      obtain ⟨g, gs, hgs⟩ := List.exists_cons_of_ne_nil hne
      rw [List.filter_cons, ite_eq_right (by simp), runs, ite_eq_left rfl, hgs, incHead,
        expand_succ hhead, ← hgs, ih]
    · by_cases h2 : y = a + 1
      · subst h2
        rw [List.filter_cons, ite_eq_left (by simp), runs, ite_eq_right h1,
          ite_eq_left rfl, expand, ite_eq_left rfl, List.headD_cons, List.tail_cons,
          List.replicate_zero, List.nil_append, expand_filter_runs hg.tail]
      · rw [List.filter_cons, ite_eq_left (by simpa using h1), runs, ite_eq_right h1,
          ite_eq_right h2, expand, ite_eq_right h2, expand_filter_runs hg.tail]

private theorem filter_expand {a : ℕ} : ∀ {w : List ℕ} (g : List ℕ), (∀ x ∈ w, a + 1 ≤ x) →
    (expand a w g).filter (· ≠ a) = w
  | [], _, _ => rfl
  | y :: ys, g, hw => by
    have hy : y ≠ a := by have := hw y List.mem_cons_self; omega
    have ih (g' : List ℕ) := filter_expand (a := a) (w := ys) g'
      (fun x hx => hw x (List.mem_cons_of_mem _ hx))
    by_cases h : y = a + 1
    · rw [expand, ite_eq_left h, List.filter_append, List.filter_cons,
        ite_eq_left (by simpa using hy), ih, List.filter_eq_nil_iff.mpr (by simp)]
      rfl
    · rw [expand, ite_eq_right h, List.filter_cons, ite_eq_left (by simpa using hy), ih]

private theorem runs_replicate_append (a n : ℕ) (l : List ℕ) :
    runs a (List.replicate n a ++ l) = incHead^[n] (runs a l) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.replicate_succ, List.cons_append, runs, ite_eq_left rfl, ih,
      Function.iterate_succ_apply']

private theorem incHead_iterate (n : ℕ) (gs : List ℕ) : incHead^[n] (0 :: gs) = n :: gs := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', ih, incHead]

private theorem runs_expand {a : ℕ} : ∀ {w : List ℕ} {g : List ℕ}, (∀ x ∈ w, a + 1 ≤ x) →
    g.length = w.count (a + 1) → runs a (expand a w g) = g
  | [], g, _, hg => by
    rw [List.count_nil, List.length_eq_zero_iff] at hg
    subst hg
    rfl
  | y :: ys, g, hw, hg => by
    have hy : y ≠ a := by have := hw y List.mem_cons_self; omega
    have hw' : ∀ x ∈ ys, a + 1 ≤ x := fun x hx => hw x (List.mem_cons_of_mem _ hx)
    by_cases h : y = a + 1
    · subst h
      rw [List.count_cons, ite_eq_left (by simp)] at hg
      cases g with
      | nil => simp at hg
      | cons g0 gs =>
        rw [expand, ite_eq_left rfl, runs_replicate_append, runs, ite_eq_right hy,
          ite_eq_left rfl, List.tail_cons, runs_expand hw' (by simpa using hg), List.headD_cons]
        exact incHead_iterate g0 gs
    · rw [List.count_cons, ite_eq_right (by simpa using h), Nat.add_zero] at hg
      rw [expand, ite_eq_right h, runs, ite_eq_right hy, ite_eq_right h, runs_expand hw' hg]

private theorem coe_expand {a : ℕ} : ∀ {w : List ℕ} {g : List ℕ}, g.length = w.count (a + 1) →
    (expand a w g : Multiset ℕ) = w + Multiset.replicate g.sum a
  | [], g, hg => by
    rw [List.count_nil, List.length_eq_zero_iff] at hg
    subst hg
    rfl
  | y :: ys, g, hg => by
    by_cases h : y = a + 1
    · subst h
      rw [List.count_cons, ite_eq_left (by simp)] at hg
      cases g with
      | nil => simp at hg
      | cons g0 gs =>
        rw [expand, ite_eq_left rfl, ← Multiset.coe_add, ← Multiset.cons_coe, List.tail_cons,
          coe_expand (by simpa using hg)]
        simp only [List.headD_cons, List.sum_cons, Multiset.coe_replicate,
          ← Multiset.cons_coe, Multiset.replicate_add]
        rw [Multiset.add_cons, Multiset.cons_add, add_left_comm]
    · rw [List.count_cons, ite_eq_right (by simpa using h), Nat.add_zero] at hg
      rw [expand, ite_eq_right h, ← Multiset.cons_coe, coe_expand hg, ← Multiset.cons_coe,
        Multiset.cons_add]

private theorem vn_replicate_append (a n : ℕ) {l : List ℕ} (hl : Vn l)
    (hh : ∀ x ∈ l.head?, x ≤ a + 1) : Vn (List.replicate n a ++ l) := by
  induction n with
  | zero => simpa using hl
  | succ n ih =>
    rw [List.replicate_succ, List.cons_append]
    apply List.IsChain.cons ih
    intro x hx
    cases n with
    | zero => exact hh x (by simpa using hx)
    | succ n =>
      rw [List.replicate_succ, List.cons_append] at hx
      simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hx
      omega

private theorem vn_expand {a : ℕ} : ∀ {w : List ℕ} (g : List ℕ), Vn w → (∀ x ∈ w, a + 1 ≤ x) →
    Vn (expand a w g) ∧ ∀ x ∈ (expand a w g).head?, x = a ∨ x ∈ w.head?
  | [], _, _, _ => ⟨List.isChain_nil, by simp [expand]⟩
  | y :: ys, g, hv, hw => by
    have hy := hw y List.mem_cons_self
    have hw' : ∀ x ∈ ys, a + 1 ≤ x := fun x hx => hw x (List.mem_cons_of_mem _ hx)
    have hv' := (List.isChain_cons.mp hv).2
    have hstep := (List.isChain_cons.mp hv).1
    by_cases h : y = a + 1
    · obtain ⟨ih1, ih2⟩ := vn_expand (a := a) g.tail hv' hw'
      have htail : Vn (y :: expand a ys g.tail) := by
        apply List.IsChain.cons ih1
        intro x hx
        rcases ih2 x hx with rfl | hx'
        · omega
        · exact hstep x hx'
      rw [expand, ite_eq_left h]
      refine ⟨vn_replicate_append a _ htail (by simp [h]), ?_⟩
      intro x hx
      cases hg : g.headD 0 with
      | zero => simp_all
      | succ m =>
        rw [hg, List.replicate_succ, List.cons_append] at hx
        simp_all
    · obtain ⟨ih1, ih2⟩ := vn_expand (a := a) g hv' hw'
      rw [expand, ite_eq_right h]
      refine ⟨List.IsChain.cons ih1 ?_, by simp⟩
      intro x hx
      rcases ih2 x hx with rfl | hx'
      · omega
      · exact hstep x hx'

private theorem getLast?_expand {a : ℕ} : ∀ (w g : List ℕ),
    (expand a w g).getLast? = w.getLast?
  | [], _ => rfl
  | y :: ys, g => by
    by_cases h : y = a + 1
    · rw [expand, ite_eq_left h, List.getLast?_append, List.getLast?_cons, List.getLast?_cons,
        getLast?_expand ys]
      rfl
    · rw [expand, ite_eq_right h, List.getLast?_cons, List.getLast?_cons, getLast?_expand ys]

private theorem vn_filter {a : ℕ} : ∀ {w : List ℕ}, Vn w → (∀ x ∈ w, a ≤ x) →
    Vn (w.filter (· ≠ a)) ∧ ∀ y, (∀ x ∈ w.head?, x ≤ y + 1) →
      ∀ x ∈ (w.filter (· ≠ a)).head?, x ≤ max y a + 1
  | [], _, _ => ⟨List.isChain_nil, by simp⟩
  | z :: zs, hv, hw => by
    have hz := hw z List.mem_cons_self
    obtain ⟨ih1, ih2⟩ := vn_filter (a := a) (List.isChain_cons.mp hv).2
      (fun x hx => hw x (List.mem_cons_of_mem _ hx))
    have hstep := (List.isChain_cons.mp hv).1
    by_cases h : z = a
    · rw [List.filter_cons, ite_eq_right (by simpa using h)]
      refine ⟨ih1, fun y hy x hx => ?_⟩
      have := ih2 z hstep x hx
      have := hy z rfl
      omega
    · rw [List.filter_cons, ite_eq_left (by simpa using h)]
      refine ⟨List.IsChain.cons ih1 fun x hx => ?_, fun y hy x hx => ?_⟩
      · have := ih2 z hstep x hx
        omega
      · simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hx
        have := hy z rfl
        omega

private theorem getLast?_filter_ne {a top : ℕ} {w : List ℕ} (hw : w.getLast? = some top)
    (htop : top ≠ a) : (w.filter (· ≠ a)).getLast? = some top := by
  rw [List.getLast?_filter]
  obtain ⟨l, rfl⟩ := List.getLast?_eq_some_iff.mp hw
  rw [List.reverse_append, List.reverse_singleton, List.singleton_append, List.find?_cons]
  simp [htop]

private theorem ncard_words_peel (a c top : ℕ) (F : Multiset ℕ) (htop : a + 1 ≤ top)
    (hF : ∀ x ∈ F, a + 1 ≤ x) :
    (words (Multiset.replicate c a + F) top).ncard =
      (words F top).ncard * (comps c (F.count (a + 1))).ncard := by
  rw [← Set.ncard_prod]
  have hgood : ∀ w ∈ words (Multiset.replicate c a + F) top, Good a w := by
    rintro w ⟨hcoe, hv, hlast⟩
    refine ⟨hv, fun x hx => ?_, fun x hx => ?_⟩
    · have hx' : x ∈ (w : Multiset ℕ) := Multiset.mem_coe.mpr hx
      rw [hcoe, Multiset.mem_add] at hx'
      rcases hx' with hx' | hx'
      · rw [Multiset.eq_of_mem_replicate hx']
      · have := hF x hx'
        omega
    · rw [hlast, Option.mem_def, Option.some.injEq] at hx
      omega
  apply Set.ncard_congr (fun w _ => (w.filter (· ≠ a), runs a w))
  · rintro w hw
    obtain ⟨hcoe, hv, hlast⟩ := hw
    have hg := hgood w ⟨hcoe, hv, hlast⟩
    refine ⟨⟨?_, (vn_filter hv hg.2.1).1, getLast?_filter_ne hlast (by omega)⟩, ?_, ?_⟩
    · rw [← Multiset.filter_coe, hcoe, Multiset.filter_add,
        Multiset.filter_eq_nil.mpr (fun x hx => by simp [Multiset.eq_of_mem_replicate hx]),
        Multiset.filter_eq_self.mpr (fun x hx => by have := hF x hx; simp; omega), zero_add]
    · rw [length_runs, ← Multiset.coe_count, hcoe, Multiset.count_add,
        Multiset.count_replicate, ite_eq_right (by omega), zero_add]
    · rw [sum_runs hg, ← Multiset.coe_count, hcoe, Multiset.count_add,
        Multiset.count_replicate_self, Multiset.count_eq_zero.mpr
          (fun hx => by have := hF a hx; omega), add_zero]
  · intro w₁ w₂ hw₁ hw₂ h
    simp only [Prod.mk.injEq] at h
    rw [← expand_filter_runs (hgood w₁ hw₁), ← expand_filter_runs (hgood w₂ hw₂), h.1, h.2]
  · rintro ⟨w, g⟩ ⟨⟨hcoe, hv, hlast⟩, hlen, hsum⟩
    have hw : ∀ x ∈ w, a + 1 ≤ x := fun x hx => hF x (by rw [← hcoe]; exact hx)
    have hlen' : g.length = w.count (a + 1) := by rw [hlen, ← Multiset.coe_count, hcoe]
    refine ⟨expand a w g, ⟨?_, (vn_expand g hv hw).1, by rw [getLast?_expand, hlast]⟩, ?_⟩
    · rw [coe_expand hlen', hcoe, hsum, add_comm]
    · simp only [Prod.mk.injEq]
      exact ⟨filter_expand g hw, runs_expand hw hlen'⟩

private theorem words_replicate {a c : ℕ} (hc : 0 < c) :
    words (Multiset.replicate c a) a = {List.replicate c a} := by
  ext w
  simp only [words, Set.mem_ofPred_eq, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hcoe, -, -⟩
    rw [← Multiset.coe_replicate, Multiset.coe_eq_coe] at hcoe
    exact List.perm_replicate.mp hcoe
  · rintro rfl
    refine ⟨Multiset.coe_replicate _ _, ?_, by rw [List.getLast?_replicate, ite_eq_right hc.ne']⟩
    refine List.isChain_iff_getElem.mpr fun i hi => ?_
    simp

private theorem ncard_words (r : ℕ) : ∀ (a : ℕ) (c : ℕ → ℕ), (∀ m ∈ Icc a (a + r), 0 < c m) →
    (words (∑ m ∈ Icc a (a + r), Multiset.replicate (c m) m) (a + r)).ncard =
      ∏ m ∈ Ico a (a + r), (c m + c (m + 1) - 1).choose (c m) := by
  induction r with
  | zero =>
    intro a c hc
    simp only [Nat.add_zero, Icc_self, sum_singleton, Ico_self, prod_empty]
    rw [words_replicate (hc a (by simp)), Set.ncard_singleton]
  | succ r ih =>
    intro a c hc
    have hIcc : Icc a (a + (r + 1)) = insert a (Icc (a + 1) (a + 1 + r)) := by
      ext m
      simp only [mem_insert, mem_Icc]
      omega
    have hIco : Ico a (a + (r + 1)) = insert a (Ico (a + 1) (a + 1 + r)) := by
      ext m
      simp only [mem_insert, mem_Ico]
      omega
    rw [hIcc, sum_insert (by simp), hIco, prod_insert (by simp),
      show a + (r + 1) = a + 1 + r by omega]
    have hF : ∀ x ∈ ∑ m ∈ Icc (a + 1) (a + 1 + r), Multiset.replicate (c m) m, a + 1 ≤ x := by
      intro x hx
      obtain ⟨m, hm, hxm⟩ := Multiset.mem_sum.mp hx
      rw [Multiset.eq_of_mem_replicate hxm]
      exact (mem_Icc.mp hm).1
    have hcount : (∑ m ∈ Icc (a + 1) (a + 1 + r), Multiset.replicate (c m) m).count (a + 1) =
        c (a + 1) := by
      rw [Multiset.count_sum', sum_eq_single (a + 1)]
      · simp
      · intro m _ hm
        rw [Multiset.count_replicate, ite_eq_right hm]
      · intro h
        exact absurd (by simp : a + 1 ∈ Icc (a + 1) (a + 1 + r)) h
    rw [ncard_words_peel a (c a) _ _ (by omega) hF, ih (a + 1) c (fun m hm => hc m (by
      simp only [mem_Icc] at hm ⊢; omega)), hcount]
    obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (hc (a + 1) (by simp)).ne'
    rw [hk, ncard_comps k (c a), mul_comm, show c a + (k + 1) - 1 = c a + k by omega]

-- Unlike `words`, these arrangements have no prescribed last letter.
private def freeWords (F : Multiset ℕ) : Set (List ℕ) :=
  {w | (w : Multiset ℕ) = F ∧ Vn w}

-- A sentinel `a + 1` makes a trailing run of `a`s peel just like the other runs.
private theorem ncard_freeWords_eq_words (a : ℕ) (F : Multiset ℕ) (hF : ∀ x ∈ F, a ≤ x) :
    (freeWords F).ncard = (words (F + {a + 1}) (a + 1)).ncard := by
  apply Set.ncard_congr (fun w _ => w ++ [a + 1])
  · rintro w ⟨hcoe, hv⟩
    refine ⟨by rw [← Multiset.coe_add, hcoe, Multiset.coe_singleton], ?_, by simp⟩
    apply hv.append (by simp)
    intro x hx y hy
    have hxF : x ∈ F := hcoe ▸ Multiset.mem_coe.mpr (List.mem_of_mem_getLast? hx)
    have := hF x hxF
    simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hy
    omega
  · intro u v _ _ h
    exact (List.append_left_inj _).mp h
  · rintro w ⟨hcoe, hv, hlast⟩
    obtain ⟨u, rfl⟩ := List.getLast?_eq_some_iff.mp hlast
    rw [← Multiset.coe_add, Multiset.coe_singleton, add_left_inj] at hcoe
    exact ⟨u, ⟨hcoe, hv.left_of_append⟩, rfl⟩

private theorem ncard_freeWords (r : ℕ) : ∀ (a : ℕ) (b : ℕ → ℕ),
    (freeWords (∑ m ∈ Icc a (a + r), Multiset.replicate (b m) m)).ncard =
      ∏ m ∈ Ico a (a + r), (b m + b (m + 1)).choose (b m) := by
  induction r with
  | zero =>
    intro a b
    simp only [Nat.add_zero, Icc_self, sum_singleton, Ico_self, prod_empty]
    have h : freeWords (Multiset.replicate (b a) a) = {List.replicate (b a) a} := by
      ext w
      simp only [freeWords, Set.mem_ofPred_eq, Set.mem_singleton_iff]
      constructor
      · rintro ⟨hcoe, _⟩
        rw [← Multiset.coe_replicate, Multiset.coe_eq_coe] at hcoe
        exact List.perm_replicate.mp hcoe
      · rintro rfl
        refine ⟨Multiset.coe_replicate _ _, List.isChain_iff_getElem.mpr fun i hi => ?_⟩
        simp
    rw [h, Set.ncard_singleton]
  | succ r ih =>
    intro a b
    have hIcc : Icc a (a + (r + 1)) = insert a (Icc (a + 1) (a + 1 + r)) := by
      ext m
      simp only [mem_insert, mem_Icc]
      omega
    have hIco : Ico a (a + (r + 1)) = insert a (Ico (a + 1) (a + 1 + r)) := by
      ext m
      simp only [mem_insert, mem_Ico]
      omega
    let F := ∑ m ∈ Icc (a + 1) (a + 1 + r), Multiset.replicate (b m) m
    have hF : ∀ x ∈ F, a + 1 ≤ x := by
      intro x hx
      obtain ⟨m, hm, hxm⟩ := Multiset.mem_sum.mp hx
      rw [Multiset.eq_of_mem_replicate hxm]
      exact (mem_Icc.mp hm).1
    have hcount : F.count (a + 1) = b (a + 1) := by
      dsimp only [F]
      rw [Multiset.count_sum', sum_eq_single (a + 1)]
      · simp
      · intro m _ hm
        rw [Multiset.count_replicate, ite_eq_right hm]
      · intro h
        exact absurd (by simp : a + 1 ∈ Icc (a + 1) (a + 1 + r)) h
    have hall : ∀ x ∈ Multiset.replicate (b a) a + F, a ≤ x := by
      intro x hx
      rcases Multiset.mem_add.mp hx with hx | hx
      · rw [Multiset.eq_of_mem_replicate hx]
      · exact (hF x hx).trans' (Nat.le_succ a)
    have hsentinel : ∀ x ∈ F + {a + 1}, a + 1 ≤ x := by
      intro x hx
      rcases Multiset.mem_add.mp hx with hx | hx
      · exact hF x hx
      · rw [Multiset.mem_singleton.mp hx]
    rw [hIcc, sum_insert (by simp), hIco, prod_insert (by simp)]
    change (freeWords (Multiset.replicate (b a) a + F)).ncard = _
    rw [ncard_freeWords_eq_words a _ hall, add_assoc, ncard_words_peel a (b a) _ _ le_rfl hsentinel,
      ← ncard_freeWords_eq_words a F (fun x hx => (hF x hx).trans' (Nat.le_succ a)),
      Multiset.count_add, hcount, Multiset.count_singleton_self, ncard_comps, mul_comm]
    rw [ih a.succ b]

/-! ### From partitions to words -/

open YoungDiagram

private theorem coe_rowLens {n : ℕ} (β : Nat.Partition n) :
    ((ofPartition β).rowLens : Multiset ℕ) = β.parts := by
  rw [rowLens_ofPartition_eq_sort_parts, Multiset.sort_eq]

private theorem rowLen_eq_zero {μ : YoungDiagram} {i : ℕ} (hi : μ.colLen 0 ≤ i) :
    μ.rowLen i = 0 := by
  by_contra h
  exact absurd (mem_iff_lt_colLen.mp (mem_iff_lt_rowLen.mpr (Nat.pos_of_ne_zero h)))
    (not_lt.mpr hi)

-- The diagonal sequence counts the rows `i < k` whose last cell lies on a diagonal `≥ k`.
private theorem diagonalSequence_eq {n : ℕ} (β : Nat.Partition n) (k : ℕ) :
    diagonalSequence β.parts k =
      ((range k).filter fun i => k ≤ (ofPartition β).rowLen i + i).card := by
  have hrows : Icc 1 k = (range k).map (addRightEmbedding 1) := by
    ext i
    simp only [mem_Icc, mem_map, mem_range, addRightEmbedding_apply]
    constructor
    · intro h
      exact ⟨i - 1, by omega, by omega⟩
    · rintro ⟨j, hj, rfl⟩
      omega
  have hparts : β.parts = (Multiset.range ((ofPartition β).colLen 0)).map
      (ofPartition β).rowLen := by
    rw [← coe_rowLens, rowLens, ← Multiset.map_coe, Multiset.coe_range]
  rw [diagonalSequence, hrows, filter_map, card_map, hparts]
  congr 1
  apply filter_congr
  intro i hi
  have hik := mem_range.mp hi
  simp only [Function.comp_apply, addRightEmbedding_apply]
  rw [show k + 1 - (i + 1) = k - i by omega, Nat.add_one_le_iff,
    diagonalSequence_max_eq_min_and_multiset.lt_count_rows
      (fun _ _ h => (ofPartition β).rowLen_anti _ _ h)]
  constructor
  · rintro ⟨-, h⟩
    omega
  · intro h
    refine ⟨?_, by omega⟩
    by_contra hc
    rw [rowLen_eq_zero (not_lt.mp hc)] at h
    omega

-- The diagonals on which the rows `0, …, L` end.
private def rowEnds {n : ℕ} (β : Nat.Partition n) (L : ℕ) : List ℕ :=
  (List.range (L + 1)).map fun i => (ofPartition β).rowLen i + i

private theorem length_rowEnds {n : ℕ} (β : Nat.Partition n) (L : ℕ) :
    (rowEnds β L).length = L + 1 := by
  simp [rowEnds]

private theorem getElem_rowEnds {n : ℕ} (β : Nat.Partition n) (L i : ℕ)
    (hi : i < (rowEnds β L).length) :
    (rowEnds β L)[i] = (ofPartition β).rowLen i + i := by
  simp [rowEnds]

private theorem vn_rowEnds {n : ℕ} (β : Nat.Partition n) (L : ℕ) : Vn (rowEnds β L) := by
  refine List.isChain_iff_getElem.mpr fun i hi => ?_
  rw [getElem_rowEnds, getElem_rowEnds]
  have := (ofPartition β).rowLen_anti i (i + 1) (by omega)
  omega

private theorem getLast?_rowEnds {n : ℕ} (β : Nat.Partition n) (L : ℕ) :
    (rowEnds β L).getLast? = some ((ofPartition β).rowLen L + L) := by
  simp [rowEnds, List.getLast?_map, List.getLast?_range]

private theorem add_le_of_diagonalSequence {n : ℕ} {β : Nat.Partition n} {L : ℕ}
    (h : diagonalSequence β.parts (L + 1) = 0) {i : ℕ} (hi : i ≤ L) :
    (ofPartition β).rowLen i + i ≤ L := by
  rw [diagonalSequence_eq, card_eq_zero, filter_eq_empty_iff] at h
  have := h (mem_range.mpr (by omega : i < L + 1))
  omega

private theorem rowLen_eq_zero_of_diagonalSequence {n : ℕ} {β : Nat.Partition n} {L : ℕ}
    (h : diagonalSequence β.parts (L + 1) = 0) {i : ℕ} (hi : L ≤ i) :
    (ofPartition β).rowLen i = 0 := by
  have h1 := add_le_of_diagonalSequence h le_rfl
  have h2 := (ofPartition β).rowLen_anti L i hi
  omega

-- Among the letters at least `k`, the rows `i < k` give `d_k`; each row `i ≥ k` is one more.
private theorem countP_rowEnds {n : ℕ} (β : Nat.Partition n) (L : ℕ)
    (hfit : ∀ i, L < i → (ofPartition β).rowLen i = 0) (k : ℕ) :
    (rowEnds β L : Multiset ℕ).countP (k ≤ ·) = diagonalSequence β.parts k + (L + 1 - k) := by
  rw [rowEnds, ← Multiset.map_coe, Multiset.coe_range, Multiset.countP_map,
    diagonalSequence_eq]
  change ((range (L + 1)).filter fun i => k ≤ (ofPartition β).rowLen i + i).card = _
  have hsplit : (range (L + 1)).filter (fun i => k ≤ (ofPartition β).rowLen i + i) =
      (range k).filter (fun i => k ≤ (ofPartition β).rowLen i + i) ∪ Ico k (L + 1) := by
    ext i
    simp only [mem_filter, mem_range, mem_union, mem_Ico]
    constructor
    · rintro ⟨h1, h2⟩
      by_cases hik : i < k
      · exact Or.inl ⟨hik, h2⟩
      · exact Or.inr ⟨by omega, h1⟩
    · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
      · refine ⟨?_, h2⟩
        by_contra hc
        have := hfit i (by omega)
        omega
      · exact ⟨h2, by omega⟩
  rw [hsplit, card_union_of_disjoint, Nat.card_Ico]
  rw [disjoint_left]
  intro i h1 h2
  simp only [mem_filter, mem_range, mem_Ico] at h1 h2
  omega

private theorem countP_le_eq (M : Multiset ℕ) (m : ℕ) :
    M.countP (m ≤ ·) = M.count m + M.countP (m + 1 ≤ ·) := by
  induction M using Multiset.induction_on with
  | empty => simp
  | cons x M ih =>
    rw [Multiset.countP_cons, Multiset.count_cons, Multiset.countP_cons, ih]
    split_ifs <;> omega

private theorem eq_of_countP_le {M N : Multiset ℕ}
    (h : ∀ k, M.countP (k ≤ ·) = N.countP (k ≤ ·)) : M = N := by
  ext m
  have h1 := countP_le_eq M m
  have h2 := countP_le_eq N m
  have h3 := h m
  have h4 := h (m + 1)
  omega

private theorem sum_map_range (f : ℕ → ℕ) (m : ℕ) :
    ((List.range m).map f).sum = ∑ i ∈ range m, f i := by
  induction m with
  | zero => rfl
  | succ m ih => rw [List.range_succ, List.map_append, List.sum_append, ih, sum_range_succ]; simp

private theorem card_eq_sum_rowLen {μ : YoungDiagram} {N : ℕ}
    (h : ∀ i, N ≤ i → μ.rowLen i = 0) : μ.card = ∑ i ∈ range N, μ.rowLen i := by
  have hcol : μ.colLen 0 ≤ N := by
    by_contra hc
    have hmem : (N, 0) ∈ μ := mem_iff_lt_colLen.mpr (by omega)
    have := mem_iff_lt_rowLen.mp hmem
    rw [h N le_rfl] at this
    omega
  rw [← sum_rowLens_eq_card, rowLens, sum_map_range]
  apply sum_subset (range_subset_range.mpr hcol)
  intro i _ hi
  exact rowLen_eq_zero (not_lt.mp (by simpa using hi))

private theorem getElem_le_add {w : List ℕ} (hw : Vn w) {i : ℕ} :
    ∀ {j : ℕ} (hij : i ≤ j) (hj : j < w.length), w[j] ≤ w[i]'(by omega) + (j - i)
  | 0, hij, hj => by
    obtain rfl : i = 0 := by omega
    omega
  | j + 1, hij, hj => by
    rcases Nat.eq_or_lt_of_le hij with rfl | hlt
    · omega
    · have ih := getElem_le_add hw (i := i) (j := j) (by omega) (by omega)
      have hs := List.isChain_iff_getElem.mp hw j hj
      omega

private theorem rowLen_ofRowLens_getD {l : List ℕ} (hl : l.SortedGE) (i : ℕ) :
    (ofRowLens l hl).rowLen i = l.getD i 0 := by
  by_cases hi : i < l.length
  · rw [List.getD_eq_getElem _ _ hi]
    exact rowLen_ofRowLens ⟨i, hi⟩
  · rw [List.getD_eq_default _ _ (not_lt.mp hi)]
    by_contra h
    have hmem := mem_iff_lt_rowLen.mpr (Nat.pos_of_ne_zero h)
    rw [mem_ofRowLens] at hmem
    obtain ⟨h', _⟩ := hmem
    exact hi h'

private theorem mem_diagonalClass_iff {n : ℕ} {p β : Nat.Partition n} :
    β ∈ diagonalClass p ↔ diagonalSequence β.parts = diagonalSequence p.parts := by
  simp [diagonalClass]

-- The partitions in the class of `p` correspond to the words with the letters of
-- `rowEnds p L` that end at `L`.
private theorem rowEnds_bijOn {n : ℕ} (p : Nat.Partition n) (L : ℕ)
    (hL' : diagonalSequence p.parts (L + 1) = 0) :
    Set.BijOn (fun β => rowEnds β L) (↑(diagonalClass p) : Set (Nat.Partition n))
      (words (rowEnds p L) L) := by
  have hfit : ∀ {β : Nat.Partition n}, β ∈ diagonalClass p →
      ∀ i, L ≤ i → (ofPartition β).rowLen i = 0 := by
    intro β hβ i hi
    rw [mem_diagonalClass_iff] at hβ
    exact rowLen_eq_zero_of_diagonalSequence (by rw [hβ]; exact hL') hi
  have hfitp : ∀ i, L ≤ i → (ofPartition p).rowLen i = 0 :=
    fun i hi => rowLen_eq_zero_of_diagonalSequence hL' hi
  refine ⟨?_, ?_, ?_⟩
  · intro β hβ
    have hβ' := mem_diagonalClass_iff.mp hβ
    refine ⟨eq_of_countP_le fun k => ?_, vn_rowEnds β L, ?_⟩
    · rw [countP_rowEnds β L (fun i hi => hfit hβ i hi.le),
        countP_rowEnds p L (fun i hi => hfitp i hi.le), hβ']
    · rw [getLast?_rowEnds, hfit hβ L le_rfl, Nat.zero_add]
  · intro β hβ γ hγ h
    have hrow : ∀ i, (ofPartition β).rowLen i = (ofPartition γ).rowLen i := by
      intro i
      by_cases hi : i ≤ L
      · have h1 := getElem_rowEnds β L i (by rw [length_rowEnds]; omega)
        have h2 := getElem_rowEnds γ L i (by rw [length_rowEnds]; omega)
        simp only [h] at h1
        omega
      · rw [hfit hβ i (by omega), hfit hγ i (by omega)]
    have hμ : ofPartition β = ofPartition γ := by
      apply YoungDiagram.ext
      ext ⟨i, j⟩
      change (i, j) ∈ ofPartition β ↔ (i, j) ∈ ofPartition γ
      rw [mem_iff_lt_rowLen, mem_iff_lt_rowLen, hrow]
    exact Nat.Partition.ext (by rw [← coe_rowLens, ← coe_rowLens γ, hμ])
  · rintro w ⟨hcoe, hv, hlast⟩
    have hlen : w.length = L + 1 := by
      rw [← Multiset.coe_card, hcoe, Multiset.coe_card, length_rowEnds]
    have hwL : w[L]'(by omega) = L := by
      rw [List.getLast?_eq_getElem?, hlen, Nat.add_sub_cancel,
        List.getElem?_eq_getElem (by omega)] at hlast
      exact Option.some.inj hlast
    have hge : ∀ i (hi : i < w.length), i ≤ w[i] := by
      intro i hi
      have := getElem_le_add hv (i := i) (j := L) (by omega) (by omega)
      omega
    set f : ℕ → ℕ := fun i => w.getD i 0 - i with hf
    have hanti : Antitone f := by
      intro i j hij
      simp only [hf]
      by_cases hj : j < w.length
      · rw [List.getD_eq_getElem _ _ hj, List.getD_eq_getElem _ _ (by omega)]
        have := getElem_le_add hv hij hj
        omega
      · rw [List.getD_eq_default _ _ (not_lt.mp hj)]
        omega
    set l := (List.range (L + 1)).map f with hl
    have hsorted : l.SortedGE := by
      apply List.Pairwise.sortedGE
      rw [hl, List.pairwise_map]
      exact List.pairwise_lt_range.imp fun hij => hanti hij.le
    set μ := ofRowLens l hsorted
    have hrow : ∀ i, μ.rowLen i = if i < L + 1 then w.getD i 0 - i else 0 := by
      intro i
      rw [rowLen_ofRowLens_getD]
      split_ifs with hi
      · rw [List.getD_eq_getElem _ _ (by simpa [hl] using hi)]
        simp [hl, hf]
      · rw [List.getD_eq_default _ _ (by simp [hl]; omega)]
    have hcard : μ.card = n := by
      have hzero : ∀ i, L + 1 ≤ i → μ.rowLen i = 0 := fun i hi => by
        rw [hrow, ite_eq_right (by omega)]
      have hzerop : ∀ i, L + 1 ≤ i → (ofPartition p).rowLen i = 0 :=
        fun i hi => hfitp i (by omega)
      rw [card_eq_sum_rowLen hzero]
      have hn := card_eq_sum_rowLen hzerop
      rw [card_ofPartition] at hn
      have hsum : w.sum = (rowEnds p L).sum := by
        rw [← Multiset.sum_coe, hcoe, Multiset.sum_coe]
      have hw : w = (List.range (L + 1)).map fun i => w.getD i 0 := by
        apply List.ext_getElem (by simp [hlen])
        intro i h1 h2
        simp only [List.getElem_map, List.getElem_range]
        rw [List.getD_eq_getElem _ _ h1]
      rw [hw, rowEnds, sum_map_range, sum_map_range, sum_add_distrib] at hsum
      have h1 : ∑ i ∈ range (L + 1), μ.rowLen i + ∑ i ∈ range (L + 1), i =
          ∑ i ∈ range (L + 1), w.getD i 0 := by
        rw [← sum_add_distrib]
        apply sum_congr rfl
        intro i hi
        have hi' := mem_range.mp hi
        rw [hrow, ite_eq_left hi', List.getD_eq_getElem _ _ (by omega)]
        have := hge i (by omega)
        omega
      omega
    set β := μ.toPartition hcard
    have hμβ : ofPartition β = μ := ofPartition_toPartition hcard
    have hends : rowEnds β L = w := by
      apply List.ext_getElem (by rw [length_rowEnds, hlen])
      intro i h1 h2
      rw [getElem_rowEnds, hμβ, hrow, ite_eq_left (by rw [length_rowEnds] at h1; exact h1),
        List.getD_eq_getElem _ _ h2]
      have := hge i h2
      omega
    refine ⟨β, mem_diagonalClass_iff.mpr (funext fun k => ?_), hends⟩
    have hfitβ : ∀ i, L < i → (ofPartition β).rowLen i = 0 := by
      intro i hi
      rw [hμβ, hrow, ite_eq_right (by omega)]
    have h1 := countP_rowEnds β L hfitβ k
    have h2 := countP_rowEnds p L (fun i hi => hfitp i hi.le) k
    rw [hends, hcoe] at h1
    omega

private theorem card_diagonalClass_eq_ncard_words {n : ℕ} (p : Nat.Partition n) (L : ℕ)
    (hL' : diagonalSequence p.parts (L + 1) = 0) :
    (diagonalClass p).card = (words (rowEnds p L) L).ncard := by
  rw [← Set.ncard_coe_finset]
  exact (rowEnds_bijOn p L hL').ncard_eq

private theorem getLast?_cons_of_ne_nil {y : ℕ} {ys : List ℕ} (h : ys ≠ []) :
    (y :: ys).getLast? = ys.getLast? := by
  rw [List.getLast?_cons]
  cases hl : ys.getLast? with
  | none => exact absurd (List.getLast?_eq_none_iff.mp hl) h
  | some t => rfl

-- A word whose steps go up by at most one and which ends at `top` takes every value between
-- any of its letters and `top`.
private theorem mem_of_le_of_le {m top : ℕ} : ∀ {w : List ℕ} {x : ℕ}, Vn w → x ∈ w →
    w.getLast? = some top → x ≤ m → m ≤ top → m ∈ w
  | [], _, _, hx, _, _, _ => absurd hx List.not_mem_nil
  | y :: ys, x, hv, hx, hlast, hxm, hmt => by
    rcases List.mem_cons.mp hx with rfl | hx
    · by_cases hm : m = x
      · exact hm ▸ List.mem_cons_self
      · have hne : ys ≠ [] := by
          rintro rfl
          simp only [List.getLast?_singleton, Option.some.injEq] at hlast
          omega
        obtain ⟨z, zs, hzs⟩ := List.exists_cons_of_ne_nil hne
        have hz : z ≤ x + 1 := (List.isChain_cons.mp hv).1 z (by simp [hzs])
        apply List.mem_cons_of_mem
        apply mem_of_le_of_le (List.isChain_cons.mp hv).2 (x := z) (by simp [hzs])
          (by rw [← getLast?_cons_of_ne_nil hne]; exact hlast) (by omega) hmt
    · have hne : ys ≠ [] := List.ne_nil_of_mem hx
      exact List.mem_cons_of_mem _ (mem_of_le_of_le (List.isChain_cons.mp hv).2 hx
        (by rw [← getLast?_cons_of_ne_nil hne]; exact hlast) hxm hmt)

private theorem staircase_le_last {n : ℕ} {p : Nat.Partition n} {q L : ℕ}
    (hq : ∀ j ∈ Icc 1 q, diagonalSequence p.parts j = j)
    (hL' : diagonalSequence p.parts (L + 1) = 0) : q ≤ L := by
  by_contra h
  have := hq (L + 1) (mem_Icc.mpr ⟨by omega, by omega⟩)
  omega

-- Each letter on the decreasing side occurs once more than the drop of the diagonal sequence.
private theorem rowEnds_eq_sum_replicate {n : ℕ} (p : Nat.Partition n) (q L : ℕ)
    (hq : ∀ j ∈ Icc 1 q, diagonalSequence p.parts j = j)
    (hq' : diagonalSequence p.parts (q + 1) ≠ q + 1) (hL : diagonalSequence p.parts L ≠ 0)
    (hL' : diagonalSequence p.parts (L + 1) = 0) :
    (rowEnds p L : Multiset ℕ) = ∑ m ∈ Icc q L, Multiset.replicate
      (diagonalSequence p.parts m - diagonalSequence p.parts (m + 1) + 1) m := by
  have hfitp : ∀ i, L ≤ i → (ofPartition p).rowLen i = 0 :=
    fun i hi => rowLen_eq_zero_of_diagonalSequence hL' hi
  have hqL := staircase_le_last hq hL'
  -- Every letter of the word of `p` lies between `q` and `L`.
  have hmem : ∀ x ∈ rowEnds p L, q ≤ x ∧ x ≤ L := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
    have hi' := List.mem_range.mp hi
    refine ⟨?_, add_le_of_diagonalSequence hL' (by omega)⟩
    by_cases hiq : i < q
    · have hdq : diagonalSequence p.parts q = q := hq q (mem_Icc.mpr ⟨by omega, le_rfl⟩)
      rw [diagonalSequence_eq] at hdq
      exact filter_card_eq (hdq.trans (card_range q).symm) i (mem_range.mpr hiq)
    · omega
  -- Some letter is at most `q`.
  obtain ⟨i₀, hi₀, hv₀⟩ : ∃ i < q + 1, (ofPartition p).rowLen i + i ≤ q := by
    by_contra! h
    have hall : ∀ i ∈ range (q + 1), q + 1 ≤ (ofPartition p).rowLen i + i :=
      fun i hi => h i (mem_range.mp hi)
    exact hq' (by rw [diagonalSequence_eq, filter_true_of_mem hall, card_range])
  have hx₀ : (ofPartition p).rowLen i₀ + i₀ ∈ rowEnds p L :=
    List.mem_map.mpr ⟨i₀, List.mem_range.mpr (by omega), rfl⟩
  have hlastp : (rowEnds p L).getLast? = some L := by
    rw [getLast?_rowEnds, hfitp L le_rfl, Nat.zero_add]
  have hcount : ∀ m ≤ L, (rowEnds p L : Multiset ℕ).count m =
      diagonalSequence p.parts m + 1 - diagonalSequence p.parts (m + 1) := by
    intro m hm
    have h1 := countP_rowEnds p L (fun i hi => hfitp i hi.le) m
    have h2 := countP_rowEnds p L (fun i hi => hfitp i hi.le) (m + 1)
    have h3 := countP_le_eq (rowEnds p L : Multiset ℕ) m
    omega
  -- After the staircase the diagonal sequence does not increase.
  have hanti : ∀ m ∈ Icc q L, diagonalSequence p.parts (m + 1) ≤ diagonalSequence p.parts m := by
    intro m hm
    obtain ⟨hqm, hmL⟩ := mem_Icc.mp hm
    rcases eq_or_lt_of_le hmL with rfl | hmL'
    · rw [hL']
      exact (Nat.pos_of_ne_zero hL).le
    have hin := mem_of_le_of_le (vn_rowEnds p L) hx₀ hlastp (by omega) hmL'.le
    have h1 := hcount m hmL'.le
    have h2 : 0 < (rowEnds p L : Multiset ℕ).count m :=
      Multiset.count_pos.mpr (Multiset.mem_coe.mpr hin)
    omega
  ext m
  rw [Multiset.count_sum']
  by_cases hm : m ∈ Icc q L
  · rw [sum_eq_single m (fun j _ hj => by rw [Multiset.count_replicate, ite_eq_right hj])
      (fun h => absurd hm h), Multiset.count_replicate_self, hcount m (mem_Icc.mp hm).2]
    have := hanti m hm
    omega
  · rw [sum_eq_zero (fun j hj => by
      rw [Multiset.count_replicate, ite_eq_right (by rintro rfl; exact hm hj)])]
    rw [Multiset.count_eq_zero, Multiset.mem_coe]
    intro hin
    exact hm (mem_Icc.mpr (hmem m hin))

private theorem colLen_zero_eq_card_parts {n : ℕ} (β : Nat.Partition n) :
    (ofPartition β).colLen 0 = β.parts.card := by
  rw [← length_rowLens, ← coe_rowLens, Multiset.coe_card]

private theorem le_card_parts_of_staircase {n : ℕ} {β : Nat.Partition n} {q : ℕ}
    (hq : ∀ j ∈ Icc 1 q, diagonalSequence β.parts j = j) : q ≤ β.parts.card := by
  by_contra! h
  have hd := hq q (mem_Icc.mpr ⟨by omega, le_rfl⟩)
  rw [diagonalSequence_eq] at hd
  have hrow := filter_card_eq (hd.trans (card_range q).symm) β.parts.card (mem_range.mpr h)
  rw [rowLen_eq_zero (colLen_zero_eq_card_parts β).le, Nat.zero_add] at hrow
  omega

-- The zero rows contribute the fixed suffix `q, q + 1, …, L`.
private theorem drop_rowEnds_eq_range_iff {n : ℕ} (β : Nat.Partition n) {q L : ℕ} (hqL : q ≤ L) :
    (rowEnds β L).drop q = List.range' q (L + 1 - q) ↔ β.parts.card ≤ q := by
  constructor
  · intro h
    have hi : q < (rowEnds β L).length := by rw [length_rowEnds]; omega
    have hhead := congrArg List.head? h
    rw [List.drop_eq_getElem_cons hi, List.head?_cons, List.head?_range',
      ite_eq_right (by omega), Option.some.injEq, getElem_rowEnds] at hhead
    by_contra! hc
    have hpos := mem_iff_lt_rowLen.mp
      (mem_iff_lt_colLen.mpr (by simpa only [colLen_zero_eq_card_parts] using hc) :
        (q, 0) ∈ ofPartition β)
    omega
  · intro h
    apply List.ext_getElem (by rw [List.length_drop, length_rowEnds, List.length_range'])
    intro i _ _
    rw [List.getElem_drop, getElem_rowEnds, List.getElem_range'_1,
      rowLen_eq_zero (by rw [colLen_zero_eq_card_parts]; omega), Nat.zero_add]

-- Removing the fixed suffix subtracts one copy of each letter between `q` and `L`.
private theorem card_diagonalClass_filter_eq_ncard_freeWords {n : ℕ} (p : Nat.Partition n)
    (q L : ℕ) (hq : ∀ j ∈ Icc 1 q, diagonalSequence p.parts j = j)
    (hq' : diagonalSequence p.parts (q + 1) ≠ q + 1) (hL : diagonalSequence p.parts L ≠ 0)
    (hL' : diagonalSequence p.parts (L + 1) = 0) :
    ((diagonalClass p).filter fun β => β.parts.card = q).card =
      (freeWords (∑ m ∈ Icc q L, Multiset.replicate
        (diagonalSequence p.parts m - diagonalSequence p.parts (m + 1)) m)).ncard := by
  have hqL := staircase_le_last hq hL'
  let F := ∑ m ∈ Icc q L, Multiset.replicate
    (diagonalSequence p.parts m - diagonalSequence p.parts (m + 1)) m
  let t := List.range' q (L + 1 - q)
  have ht : (t : Multiset ℕ) = (Icc q L).val := by
    have heq : t.toFinset = Icc q L := by
      ext m
      simp only [t, List.mem_toFinset, List.mem_range', Nat.one_mul, mem_Icc]
      exact ⟨fun ⟨i, _, _⟩ => by omega, fun h => ⟨m - q, by omega, by omega⟩⟩
    rw [← heq, List.toFinset_val, List.dedup_eq_self.mpr (by simp [t, List.nodup_range'])]
  have hF : (rowEnds p L : Multiset ℕ) = F + t := by
    rw [rowEnds_eq_sum_replicate p q L hq hq' hL hL', ht, ← sum_multiset_singleton]
    simp only [F, Multiset.replicate_add, Multiset.replicate_one, sum_add_distrib]
  have hlenF : F.card = q := by
    have h := congrArg Multiset.card hF
    simp only [Multiset.coe_card, length_rowEnds, Multiset.card_add, t, List.length_range'] at h
    omega
  have hsplit (β : Nat.Partition n) (hβ : β.parts.card ≤ q) :
      (rowEnds β L).take q ++ t = rowEnds β L := by
    change (rowEnds β L).take q ++ List.range' q (L + 1 - q) = rowEnds β L
    rw [← (drop_rowEnds_eq_range_iff β hqL).mpr hβ, List.take_append_drop]
  have hb := rowEnds_bijOn p L hL'
  rw [← Set.ncard_coe_finset]
  change _ = (freeWords F).ncard
  apply Set.ncard_congr (fun β _ => (rowEnds β L).take q)
  · intro β hβ
    obtain ⟨hβ, hcard⟩ := mem_filter.mp hβ
    obtain ⟨hcoe, hv, _⟩ := hb.mapsTo hβ
    have he := congrArg (fun w : List ℕ => (w : Multiset ℕ)) (hsplit β hcard.le)
    rw [← Multiset.coe_add, hcoe, hF, add_left_inj] at he
    exact ⟨he, hv.take q⟩
  · intro β γ hβ hγ heq
    obtain ⟨hβ, hβq⟩ := mem_filter.mp hβ
    obtain ⟨hγ, hγq⟩ := mem_filter.mp hγ
    apply hb.injOn hβ hγ
    change rowEnds β L = rowEnds γ L
    rw [← hsplit β hβq.le, ← hsplit γ hγq.le, heq]
  · rintro u ⟨hu, hv⟩
    have hlen : u.length = q := by rw [← Multiset.coe_card, hu, hlenF]
    have htlast : t.getLast? = some L := by
      rw [List.getLast?_eq_getElem?, show t.length - 1 = L - q by simp [t]; omega,
        List.getElem?_eq_getElem (by simp [t]; omega)]
      simp only [t, List.getElem_range'_1]
      congr 1
      omega
    have htchain : Vn t := by
      apply List.isChain_iff_getElem.mpr
      intro i _
      simp only [t, List.getElem_range'_1]
      omega
    have hchain : Vn (u ++ t) := by
      apply hv.append htchain
      intro x hx y hy
      have hxF : x ∈ F := hu ▸ Multiset.mem_coe.mpr (List.mem_of_mem_getLast? hx)
      obtain ⟨m, hm, hxm⟩ := Multiset.mem_sum.mp hxF
      have hxm := Multiset.eq_of_mem_replicate hxm
      have hhead : t.head? = some q := by
        change (List.range' q (L + 1 - q)).head? = some q
        rw [List.head?_range', ite_eq_right (by omega)]
      rw [hhead] at hy
      simp only [Option.mem_def, Option.some.injEq] at hy
      have := (mem_Icc.mp hm).1
      omega
    obtain ⟨β, hβ, hends⟩ := hb.surjOn (a := u ++ t)
      ⟨by rw [← Multiset.coe_add, hu, hF], hchain, by simp [List.getLast?_append, htlast]⟩
    change rowEnds β L = u ++ t at hends
    have hle : β.parts.card ≤ q := (drop_rowEnds_eq_range_iff β hqL).mp (by
      rw [hends, List.drop_left' hlen])
    have hge : q ≤ β.parts.card := le_card_parts_of_staircase (by
      rw [mem_diagonalClass_iff.mp hβ]
      exact hq)
    exact ⟨β, mem_filter.mpr ⟨hβ, le_antisymm hle hge⟩, by rw [hends, List.take_left' hlen]⟩

end card_diagonalClass_eq_prod_choose

open card_diagonalClass_eq_prod_choose Finset in
/-- **Number of partitions with a given diagonal sequence.** Let $\alpha$ be a partition of $n$
with diagonal sequence $\delta(\alpha) = (d_j)_{j \ge 1}$, set $d_0 = 0$, and let $q, L \ge 0$ be
integers with $d_j = j$ for all $1 \le j \le q$, $d_{q+1} \ne q + 1$, $d_L \ne 0$ and
$d_{L+1} = 0$. Put $b_i = \max(d_i - d_{i+1}, 0)$. Then the number of partitions of $n$ whose
diagonal sequence equals $\delta(\alpha)$ is
$$\prod_{i=q}^{L-1} \binom{b_i + b_{i+1} + 1}{b_i + 1}.$$

Source: Michael Neubauer and Harmony Vargas, *Diagonal Sequences of Integer Partitions*,
INTEGERS 25 (2025), Article A60, Theorem 1. -/
public theorem card_diagonalClass_eq_prod_choose {n : ℕ} (p : Nat.Partition n) (q L : ℕ)
    (hq : ∀ j ∈ Finset.Icc 1 q, diagonalSequence p.parts j = j)
    (hq' : diagonalSequence p.parts (q + 1) ≠ q + 1) (hL : diagonalSequence p.parts L ≠ 0)
    (hL' : diagonalSequence p.parts (L + 1) = 0) :
    (diagonalClass p).card =
      ∏ i ∈ Finset.Ico q L,
        ((diagonalSequence p.parts i - diagonalSequence p.parts (i + 1)) +
            (diagonalSequence p.parts (i + 1) - diagonalSequence p.parts (i + 2)) + 1).choose
          (diagonalSequence p.parts i - diagonalSequence p.parts (i + 1) + 1) := by
  have hqL := staircase_le_last hq hL'
  have hF := rowEnds_eq_sum_replicate p q L hq hq' hL hL'
  have hwords := ncard_words (L - q) q
    (fun m => diagonalSequence p.parts m - diagonalSequence p.parts (m + 1) + 1)
    (fun m _ => Nat.succ_pos _)
  rw [show q + (L - q) = L by omega] at hwords
  rw [card_diagonalClass_eq_ncard_words p L hL', hF, hwords]
  apply prod_congr rfl
  intro i _
  rw [show i + 1 + 1 = i + 2 from rfl]
  congr 1
  omega

open card_diagonalClass_eq_prod_choose Finset in
/-- **Partitions in a diagonal class with as many parts as the initial staircase.** Let $\alpha$
be a partition of $n$ with diagonal sequence $\delta(\alpha) = (d_j)_{j \ge 1}$, set $d_0 = 0$,
and let $q, L \ge 0$ be integers with $d_j = j$ for all $1 \le j \le q$, $d_{q+1} \ne q + 1$,
$d_L \ne 0$ and $d_{L+1} = 0$. Put $b_i = \max(d_i - d_{i+1}, 0)$. Then the number of partitions
of $n$ with exactly $q$ parts whose diagonal sequence equals $\delta(\alpha)$ is
$$\prod_{i=q}^{L-1} \binom{b_i + b_{i+1}}{b_i}.$$

Source: Michael Neubauer and Harmony Vargas, *Diagonal Sequences of Integer Partitions*,
INTEGERS 25 (2025), Article A60, Proposition 8. -/
public theorem card_diagonalClass_filter_card_parts_eq_q {n : ℕ} (p : Nat.Partition n)
    (q L : ℕ) (hq : ∀ j ∈ Finset.Icc 1 q, diagonalSequence p.parts j = j)
    (hq' : diagonalSequence p.parts (q + 1) ≠ q + 1) (hL : diagonalSequence p.parts L ≠ 0)
    (hL' : diagonalSequence p.parts (L + 1) = 0) :
    ((diagonalClass p).filter fun β => β.parts.card = q).card =
      ∏ i ∈ Finset.Ico q L,
        ((diagonalSequence p.parts i - diagonalSequence p.parts (i + 1)) +
            (diagonalSequence p.parts (i + 1) - diagonalSequence p.parts (i + 2))).choose
          (diagonalSequence p.parts i - diagonalSequence p.parts (i + 1)) := by
  rw [card_diagonalClass_filter_eq_ncard_freeWords p q L hq hq' hL hL']
  have h := ncard_freeWords (L - q) q
    (fun i => diagonalSequence p.parts i - diagonalSequence p.parts (i + 1))
  rw [Nat.add_sub_of_le (staircase_le_last hq hL')] at h
  exact h

namespace card_diagonalClassOf_min_two

open Finset diagonalSequence_max_eq_min_and_multiset

-- Start at the last staircase entry. The default 0 accounts for the final drop to zero.
private def tailWeight (l : List ℕ) : ℕ :=
  ∏ i ∈ range (l.length - 1),
    let a := l.getD i 0 - l.getD (i + 1) 0
    let b := l.getD (i + 1) 0 - l.getD (i + 2) 0
    (a + b + 1).choose (a + 1)

private theorem tailWeight_cons_cons (a b : ℕ) (l : List ℕ) :
    tailWeight (a :: b :: l) =
      ((a - b) + (b - l.getD 0 0) + 1).choose (a - b + 1) * tailWeight (b :: l) := by
  unfold tailWeight
  rw [show (a :: b :: l).length - 1 = ((b :: l).length - 1) + 1 by simp,
    prod_range_succ', mul_comm]
  rfl

-- Removing one of three equal entries deletes the factor for two consecutive zero drops.
private theorem tailWeight_triple (pre suf : List ℕ) (x : ℕ) :
    tailWeight (pre ++ x :: x :: x :: suf) = tailWeight (pre ++ x :: x :: suf) := by
  induction pre with
  | nil =>
    simp only [List.nil_append, tailWeight_cons_cons, List.getD_cons_zero, Nat.sub_self,
      Nat.zero_add, Nat.choose_self, one_mul]
  | cons a pre ih =>
    cases pre with
    | nil =>
      simp only [List.cons_append, List.nil_append] at ih ⊢
      rw [tailWeight_cons_cons a, tailWeight_cons_cons a, ih]
      simp only [List.getD_cons_zero]
    | cons b pre =>
      simp only [List.cons_append] at ih ⊢
      rw [tailWeight_cons_cons a, tailWeight_cons_cons a, ih]
      cases pre <;> rfl

private theorem tailWeight_replicate_min_two (pre suf : List ℕ) (x k : ℕ) :
    tailWeight (pre ++ List.replicate k x ++ suf) =
      tailWeight (pre ++ List.replicate (min k 2) x ++ suf) := by
  by_cases hk : k ≤ 2
  · rw [min_eq_left hk]
  have hk' : 2 ≤ k := by omega
  rw [min_eq_right hk']
  clear hk
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hk'
  clear hk'
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [← ih, show 2 + (m + 1) = m + 3 by omega, show 2 + m = m + 2 by omega]
    simpa only [List.replicate_succ, List.cons_append, List.append_assoc] using
      tailWeight_triple pre (List.replicate m x ++ suf) x

private theorem tailWeight_blocks_min_two (q : ℕ) (s : ℕ → ℕ) (pre : List ℕ) :
    tailWeight (pre ++ blocks q s) = tailWeight (pre ++ blocks q (fun j => min (s j) 2)) := by
  induction q generalizing pre with
  | zero => rfl
  | succ q ih =>
    simp only [blocks_succ, ← List.append_assoc]
    rw [tailWeight_replicate_min_two, ih]

private theorem sum_blocks (q : ℕ) (s : ℕ → ℕ) :
    (blocks q s).sum = ∑ j ∈ Icc 1 q, j * s j := by
  induction q with
  | zero => simp [blocks]
  | succ q ih =>
    rw [blocks_succ, List.sum_append, List.sum_const_nat, ih,
      sum_Icc_succ_top (by omega : 1 ≤ q + 1), Nat.mul_comm (s (q + 1)), Nat.add_comm]

private theorem card_eq_tailWeight (q : ℕ) (s : ℕ → ℕ) :
    (diagonalClassOf ((q + 1) * (q + 2) / 2 + ∑ j ∈ Icc 1 (q + 1), j * s j)
      (diagonalOfList (diagonalNormalForm (q + 1) s))).card =
        tailWeight ((q + 1) :: blocks (q + 1) s) := by
  have hpos (x : ℕ) (hx : x ∈ diagonalMinPartition (q + 1) s) : 0 < x := by
    unfold diagonalMinPartition at hx
    obtain ⟨j, _, hxj⟩ := List.mem_flatMap.mp hx
    rw [(List.mem_replicate.mp hxj).2]
    exact Nat.succ_pos _
  have hsum : (diagonalMinPartition (q + 1) s).sum =
      (q + 1) * (q + 2) / 2 + ∑ j ∈ Icc 1 (q + 1), j * s j := by
    change (blocks (q + 1) (fun j => s j + 1)).sum = _
    rw [sum_blocks]
    conv_lhs => simp only [Nat.mul_add, Nat.mul_one, sum_add_distrib]
    have htri : ∑ j ∈ Icc 1 (q + 1), j = (q + 1) * (q + 2) / 2 := by
      simpa [sum_range_id, Ico_add_one_right_eq_Icc, Nat.mul_comm] using
        (sum_range_eq_add_Ico id (Nat.zero_lt_succ (q + 1))).symm
    rw [htri, Nat.add_comm]
  let p : Nat.Partition ((q + 1) * (q + 2) / 2 + ∑ j ∈ Icc 1 (q + 1), j * s j) :=
    { parts := ↑(diagonalMinPartition (q + 1) s)
      parts_pos := fun hx => hpos _ (Multiset.mem_coe.mp hx)
      parts_sum := by simpa using hsum }
  obtain ⟨_, hd, hparts⟩ := diagonalSequence_max_eq_min_and_multiset (q + 1) s
  change diagonalSequence p.parts = _ at hd
  have hclass : diagonalClassOf _ (diagonalOfList (diagonalNormalForm (q + 1) s)) =
      diagonalClass p := by
    rw [← hd]
    rfl
  have hsplit : diagonalNormalForm (q + 1) s =
      List.range' 1 q ++ ((q + 1) :: blocks (q + 1) s) := by
    change List.range' 1 (q + 1) ++ blocks (q + 1) s = _
    rw [List.range'_concat]
    simp [List.append_assoc, Nat.add_comm]
  let L := (diagonalNormalForm (q + 1) s).length
  have hlen : L - (q + 1) = ((q + 1) :: blocks (q + 1) s).length - 1 := by
    simp only [L, hsplit, List.length_append, List.length_range', List.length_cons]
    omega
  have hget (i : ℕ) : diagonalOfList (diagonalNormalForm (q + 1) s) (q + 1 + i) =
      ((q + 1) :: blocks (q + 1) s).getD i 0 := by
    rw [diagonalOfList, hsplit]
    change ((0 :: List.range' 1 q) ++ _).getD _ _ = _
    rw [List.getD_append_right _ _ _ _ (by simp)]
    simp
  have hstair (j : ℕ) (hj : j ∈ Icc 1 (q + 1)) : diagonalSequence p.parts j = j := by
    rw [hd]
    obtain ⟨hj₁, hj₂⟩ := mem_Icc.mp hj
    have hlo := (le_normalForm (q + 1) s j j hj₁).mpr ⟨le_rfl, hj₂, by omega⟩
    by_contra hne
    have hhi : j + 1 ≤ diagonalOfList (diagonalNormalForm (q + 1) s) j := by omega
    have := (le_normalForm (q + 1) s (j + 1) j (by omega)).mp hhi
    omega
  have hnext : diagonalSequence p.parts (q + 1 + 1) ≠ q + 1 + 1 := by
    rw [hd]
    intro heq
    have hle : q + 1 + 1 ≤ diagonalOfList (diagonalNormalForm (q + 1) s) (q + 1 + 1) :=
      heq.ge
    have := (le_normalForm (q + 1) s _ _ (by omega)).mp hle
    omega
  have hlast : diagonalSequence p.parts L ≠ 0 := by
    rw [hd, diagonalOfList]
    have hL : 0 < L := by simp [L, hsplit]
    obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero hL.ne'
    have hm' : m < (diagonalNormalForm (q + 1) s).length := by omega
    rw [hm, List.getD_cons_succ, List.getD_eq_getElem _ _ hm']
    have hmem := List.getElem_mem hm'
    rw [← Multiset.mem_coe, hparts] at hmem
    exact (hpos _ (Multiset.mem_coe.mp hmem)).ne'
  have hend : diagonalSequence p.parts (L + 1) = 0 := by
    rw [hd, diagonalOfList, List.getD_cons_succ]
    exact List.getD_eq_default _ _ le_rfl
  rw [hclass, card_diagonalClass_eq_prod_choose p (q + 1) L hstair hnext hlast hend, hd,
    prod_Ico_eq_prod_range, hlen, tailWeight]
  apply prod_congr rfl
  intro i _
  rw [Nat.add_assoc (q + 1) i 1, Nat.add_assoc (q + 1) i 2]
  simp only [hget]

end card_diagonalClassOf_min_two

open card_diagonalClassOf_min_two diagonalSequence_max_eq_min_and_multiset in
/-- **Capping the multiplicities of a diagonal sequence at two.** For $m \ge 0$ and a sequence
$s = (s_1, s_2, \dots)$ of natural numbers, let $d(m, s)$ be the sequence
$(1, 2, \dots, m, m^{(s_m)}, (m-1)^{(s_{m-1})}, \dots, 1^{(s_1)})$ followed by zeros, where
$v^{(r)}$ means $r$ copies of $v$, and let $n(m, s) = m(m+1)/2 + \sum_{j=1}^{m} j s_j$. Let
$q \ge 1$ and $\sigma_j = \min(s_j, 2)$ for all $j$. Then the number of partitions of $n(q, s)$
with diagonal sequence $d(q, s)$ equals the number of partitions of $n(q, \sigma)$ with diagonal
sequence $d(q, \sigma)$.

Source: Michael Neubauer and Harmony Vargas, *Diagonal Sequences of Integer Partitions*,
INTEGERS 25 (2025), Article A60, Corollary 6 (5). -/
public theorem card_diagonalClassOf_min_two (q : ℕ) (hq : 1 ≤ q) (s : ℕ → ℕ) :
    (diagonalClassOf (q * (q + 1) / 2 + ∑ j ∈ Finset.Icc 1 q, j * s j)
        (diagonalOfList (diagonalNormalForm q s))).card =
      (diagonalClassOf (q * (q + 1) / 2 + ∑ j ∈ Finset.Icc 1 q, j * min (s j) 2)
        (diagonalOfList (diagonalNormalForm q fun j => min (s j) 2))).card := by
  obtain ⟨q, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : q ≠ 0)
  rw [card_eq_tailWeight, card_eq_tailWeight]
  exact tailWeight_blocks_min_two (q + 1) s [q + 1]

end MetaMathlibExt

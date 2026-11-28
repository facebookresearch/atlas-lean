/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Basic.Real.Basic
public import MathlibExt.GameTheory.PenultsOfTak
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fin.Embedding
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic.Linarith

/-!
# Lower bounds for Impartial Tak penults

`MetaMathlibExt.impartialTak_penult_card_ge_weightedCross` bounds the size of a penult by
counting the cells covered as one grows the occupied region accessible from the edge.
`MetaMathlibExt.impartialTak_penult_card_ge_quarter` deduces the quarter lower bound from it.

For every Impartial Tak penult $S$ on an $n \times n$ board and every window at $(r,c)$ with
$r + 5, c + 5 \le n$, `impartialTak_penult_weightedCross` gives total weight at least $7$ under
the weights of Figure 10(c). The local check enumerates all patterns of weight at most $6$, with
the zero-weight corners treated as occupied. In each pattern it finds an interior hole separated
from the occupied boundary by a cut closed under adjacency to occupied cells. Placing a token in
that hole cannot introduce a winning reply in a penult, by `not_takPenult_of_cut`.

## References

* Boris Alexeev, Paul Ellis, Michael Richter, and Thotsaporn Aek Thanatipanonda,
  [*The Penults of Tak: Adventures in Impartial, Normal-Play, Positional Games*](https://math.colgate.edu/~integers/zg1/zg1.pdf),
  INTEGERS 25 (2025), Article G1, pp. 1–18, Propositions 10 and 12–14, and Figure 10(c).
-/

namespace MetaMathlibExt

private abbrev Cell (n : ℕ) := Fin n × Fin n

private def onEdge {n : ℕ} (p : Cell n) : Prop :=
  p.1.val = 0 ∨ p.1.val + 1 = n ∨ p.2.val = 0 ∨ p.2.val + 1 = n

namespace impartialTak_penult_card_ge_weightedCross

private theorem adjacent_symm {n : ℕ} {p q : Cell n} (h : takAdjacent p q) :
    takAdjacent q p := by
  simpa only [takAdjacent_iff_dist_eq_one, Nat.dist_comm] using h

private noncomputable def neighbors {n : ℕ} (p : Cell n) : Finset (Cell n) := by
  classical
  exact Finset.univ.filter (takAdjacent p)

private theorem mem_neighbors {n : ℕ} {p q : Cell n} :
    q ∈ neighbors p ↔ takAdjacent p q := by
  classical
  simp [neighbors]

private theorem card_neighbors_le {n : ℕ} (p : Cell n) : (neighbors p).card ≤ 4 := by
  let offsets : Finset (ℕ × ℕ) :=
    {(p.1.val, p.2.val + 1), (p.1.val, p.2.val - 1),
      (p.1.val + 1, p.2.val), (p.1.val - 1, p.2.val)}
  calc
    _ ≤ offsets.card := by
      apply Finset.card_le_card_of_injOn (fun q : Cell n => (q.1.val, q.2.val))
      · intro q hq
        have h := mem_neighbors.mp hq
        simp only [offsets, Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq]
        simp only [takAdjacent_iff_dist_eq_one, Nat.dist] at h
        omega
      · intro a _ b _ h
        exact Prod.ext (Fin.ext (congrArg Prod.fst h)) (Fin.ext (congrArg Prod.snd h))
    _ ≤ 4 := Finset.card_le_four

private noncomputable def covered {n : ℕ} (A : Finset (Cell n)) : Finset (Cell n) := by
  classical
  exact Finset.univ.filter fun p => p ∈ A ∨ ∃ a ∈ A, takAdjacent a p

private theorem mem_covered {n : ℕ} {A : Finset (Cell n)} {p : Cell n} :
    p ∈ covered A ↔ p ∈ A ∨ ∃ a ∈ A, takAdjacent a p := by
  classical
  simp [covered]

-- The new token and its neighbor in A were both covered before the insertion.
private theorem covered_insert_bound {n : ℕ} (D A : Finset (Cell n)) {s a : Cell n}
    (ha : a ∈ A) (has : takAdjacent a s) :
    (D ∩ covered (insert s A)).card ≤ (D ∩ covered A).card + 3 := by
  classical
  have hsub : D ∩ covered (insert s A) ⊆ (D ∩ covered A) ∪ (neighbors s).erase a := by
    intro p hp
    obtain ⟨hpD, hp⟩ := Finset.mem_inter.mp hp
    by_cases hc : p ∈ covered A
    · exact Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨hpD, hc⟩)
    apply Finset.mem_union_right
    have hpa : p ≠ a := fun h => hc (h ▸ mem_covered.mpr (Or.inl ha))
    refine Finset.mem_erase.mpr ⟨hpa, mem_neighbors.mpr ?_⟩
    rcases mem_covered.mp hp with h | ⟨b, hb, hbp⟩
    · rcases Finset.mem_insert.mp h with rfl | h
      · exact (hc (mem_covered.mpr (.inr ⟨a, ha, has⟩))).elim
      · exact (hc (mem_covered.mpr (.inl h))).elim
    · rcases Finset.mem_insert.mp hb with rfl | hb
      · exact hbp
      · exact (hc (mem_covered.mpr (.inr ⟨b, hb, hbp⟩))).elim
  have he := Finset.card_erase_of_mem (mem_neighbors.mpr (adjacent_symm has))
  have hdeg := card_neighbors_le s
  exact (Finset.card_le_card hsub).trans ((Finset.card_union_le _ _).trans (by omega))

-- Grow the part of the board accessible from the edge through tokens. Each
-- insertion costs at most three new covered cells. At saturation each remaining
-- uncovered cell is a token: playing an empty one could not create an ult.
private theorem count_from_edge {n : ℕ} {S : Finset (Cell n)}
    (hS : placementPenult takHasRoad S)
    (D A : Finset (Cell n)) (hedge : ∀ x, onEdge x → x ∈ A) :
    D.card ≤ (D ∩ covered A).card + 3 * (S \ A).card := by
  classical
  by_cases grow : ∃ s ∈ S, s ∈ covered A ∧ s ∉ A
  · obtain ⟨s, hs, hcov, hsA⟩ := grow
    obtain ⟨a, ha, has⟩ := (mem_covered.mp hcov).resolve_left hsA
    have hdiff : S \ insert s A = (S \ A).erase s := by
      ext
      simp
      tauto
    have hcard := Finset.card_erase_of_mem (Finset.mem_sdiff.mpr ⟨hs, hsA⟩)
    have hpos := Finset.card_pos.mpr ⟨s, Finset.mem_sdiff.mpr ⟨hs, hsA⟩⟩
    have ih := count_from_edge hS D (insert s A)
      (fun x hx => Finset.mem_insert_of_mem (hedge x hx))
    have hbound := covered_insert_bound D A ha has
    rw [hdiff, hcard] at ih
    omega
  · have hclosed : ∀ s ∈ S, s ∈ covered A → s ∈ A := by simpa using grow
    have hsub : D ⊆ (D ∩ covered A) ∪ (S \ A) := by
      intro p hp
      by_cases hc : p ∈ covered A
      · exact Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨hp, hc⟩)
      by_cases hs : p ∈ S
      · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr
          ⟨hs, fun ha => hc (mem_covered.mpr (.inl ha))⟩)
      refine (not_takPenult_of_cut (A := (A : Set (Cell n))) hs
        (fun h => hc (mem_covered.mpr (.inl h))) (fun x _ hx => hedge x hx) ?_ hS).elim
      intro x hx y hy hxy
      have hcov := mem_covered.mpr (.inr ⟨x, hx, hxy⟩)
      rcases Finset.mem_insert.mp hy with rfl | hy
      · exact (hc hcov).elim
      · exact hclosed y hy hcov
    exact (Finset.card_le_card hsub).trans ((Finset.card_union_le _ _).trans (by omega))
termination_by (S \ A).card
decreasing_by
  rw [hdiff, hcard]
  omega

-- Shifting both indices by two enumerates the cells outside the two outer
-- layers, precisely the square that the initial boundary fails to cover.
private def inset {n : ℕ} (hn : 5 ≤ n) : Fin (n - 4) ↪ Fin n where
  toFun i := ⟨i.val + 2, by have := i.isLt; omega⟩
  inj' := by
    intro i j h
    apply Fin.ext
    simpa using congrArg Fin.val h

private theorem inset_val {n : ℕ} (hn : 5 ≤ n) (i : Fin (n - 4)) :
    (inset hn i).val = i.val + 2 := rfl

private theorem count_inset {n : ℕ} (hn : 5 ≤ n) {S : Finset (Cell n)}
    (hS : placementPenult takHasRoad S) : (n - 4) ^ 2 ≤ 3 * S.card := by
  classical
  let A : Finset (Cell n) := Finset.univ.filter onEdge
  let D := Finset.univ.map ((inset hn).prodMap (inset hn))
  have hcount := count_from_edge hS D A (by simp [A])
  have hempty : D ∩ covered A = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro p hp
    obtain ⟨hD, hc⟩ := Finset.mem_inter.mp hp
    obtain ⟨⟨i, j⟩, _, rfl⟩ := Finset.mem_map.mp hD
    have hi := i.isLt
    have hj := j.isLt
    rcases mem_covered.mp hc with h | ⟨a, ha, hadj⟩
    · simp [A, onEdge, Function.Embedding.prodMap, inset_val] at h
      omega
    · simp [A, onEdge] at ha
      simp [takAdjacent_iff_dist_eq_one, Nat.dist, Function.Embedding.prodMap, inset_val] at hadj
      omega
  rw [hempty] at hcount
  have hsize : D.card = (n - 4) ^ 2 := by simp [D, sq]
  have hle : (S \ A).card ≤ S.card := Finset.card_le_card Finset.sdiff_subset
  simp only [Finset.card_empty, Nat.zero_add, hsize] at hcount
  exact hcount.trans (Nat.mul_le_mul_left 3 hle)

end impartialTak_penult_card_ge_weightedCross

section WeightedCross

private abbrev Slot := Fin 25
private abbrev Mask := BitVec 25

-- Slots and mask bits are numbered in row-major order, starting at zero.
private abbrev coord : Slot ≃ Fin 5 × Fin 5 := (finProdFinEquiv (m := 5) (n := 5)).symm

private def weight (i : Slot) : ℕ := weightedCrossWeight (coord i).1.val (coord i).2.val

private def interior (i : Slot) : Prop :=
  0 < (coord i).1.val ∧ (coord i).1.val < 4 ∧ 0 < (coord i).2.val ∧ (coord i).2.val < 4

private def innerMask : Mask := 0b00000_01110_01110_01110_00000
private def cornerMask : Mask := 0b10001_00000_00000_00000_10001
private def beforeLastColumn : Mask := 0b01111_01111_01111_01111_01111
private def afterFirstColumn : Mask := 0b11110_11110_11110_11110_11110

private theorem innerMask_spec : ∀ i : Slot, innerMask.getLsbD i = true ↔ interior i := by
  unfold interior
  decide

-- The column masks prevent horizontal steps from wrapping around a row.
private def neighbors (s : Mask) : Mask :=
  ((s &&& beforeLastColumn) <<< (1 : ℕ)) ||| ((s &&& afterFirstColumn) >>> (1 : ℕ)) |||
    (s <<< (5 : ℕ)) ||| (s >>> (5 : ℕ))

private theorem neighbor_bit {f : Mask} {i j : Slot}
    (h : takAdjacent (coord i) (coord j)) (hi : f.getLsbD i = true) :
    (neighbors f).getLsbD j = true := by
  have geom : ∀ i j : Slot,
      Nat.dist (coord i).1.val (coord j).1.val + Nat.dist (coord i).2.val (coord j).2.val = 1 →
      (1 ≤ j.val ∧ i.val = j.val - 1 ∧ beforeLastColumn.getLsbD i = true) ∨
      (i.val = 1 + j.val ∧ afterFirstColumn.getLsbD i = true) ∨
      (5 ≤ j.val ∧ i.val = j.val - 5) ∨ i.val = 5 + j.val := by decide
  have hj := j.isLt
  simp only [neighbors, BitVec.getLsbD_or, BitVec.getLsbD_and,
    BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ushiftRight, hj, decide_true, Bool.true_and]
  rcases geom i j (takAdjacent_iff_dist_eq_one.mp h) with
    ⟨hj', e, hm⟩ | ⟨e, hm⟩ | ⟨hj', e⟩ | e
  · simp [← e, hi, hm, Nat.not_lt.mpr hj']
  · simp [← e, hi, hm]
  · simp [← e, hi, Nat.not_lt.mpr hj']
  · simp [← e, hi]

private def extend (s f : Mask) : Mask := f ||| (s &&& neighbors f)

private def flood (s : Mask) : ℕ → Mask
  | 0 => s &&& ~~~innerMask
  | k + 1 => extend s (flood s k)

private theorem bit_flood_of_boundary {s : Mask} {i : Slot} (hi : ¬ interior i)
    (hs : s.getLsbD i = true) (k : ℕ) : (flood s k).getLsbD i = true := by
  induction k with
  | zero =>
    have h : innerMask.getLsbD i = false := Bool.eq_false_iff.mpr (mt (innerMask_spec i).mp hi)
    simp only [flood, BitVec.getLsbD_and, BitVec.getLsbD_not, h, hs, i.isLt,
      decide_true, Bool.not_false, Bool.and_self]
  | succ k ih => simp [flood, extend, ih]

-- Try the occupied set itself first: it suffices if some interior Cross is empty.
-- Otherwise grow from the occupied boundary. Check stability, not just the round count.
private def uncovered (s f : Mask) : Bool := (s ||| neighbors f) &&& innerMask != innerMask

private def good (s : Mask) : Bool :=
  uncovered s s || (let f := flood s 3; (extend s f == f) && uncovered s f)

private theorem uncovered_sound {s f : Mask} (h : uncovered s f = true) :
    ∃ i : Slot, interior i ∧ s.getLsbD i = false ∧ (neighbors f).getLsbD i = false := by
  classical
  have hne : (s ||| neighbors f) &&& innerMask ≠ innerMask := by simpa [uncovered] using h
  simp only [ne_eq, BitVec.eq_of_getLsbD_eq_iff] at hne
  push Not at hne
  obtain ⟨i, hi, hdiff⟩ := hne
  refine ⟨⟨i, hi⟩, ?_⟩
  have hm : innerMask.getLsbD i = true := by
    cases e : innerMask.getLsbD i <;> simp_all
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_or, hm, Bool.and_true] at hdiff
  exact ⟨(innerMask_spec ⟨i, hi⟩).mp hm,
    Bool.eq_false_iff.mpr (fun e => hdiff (Bool.or_eq_true_iff.mpr (.inl e))),
    Bool.eq_false_iff.mpr (fun e => hdiff (Bool.or_eq_true_iff.mpr (.inr e)))⟩

private def bit (i : Slot) : Mask := (1 : Mask) <<< i.val

private theorem bit_at (i j : Slot) : (bit i).getLsbD j = decide (j = i) := by
  change ((1#25) <<< i.val).getLsbD j = decide (j = i)
  rw [BitVec.getLsbD_shiftLeft, BitVec.getLsbD_one]
  simp only [j.isLt, decide_true, Bool.true_and, Fin.ext_iff]
  by_cases h : j.val = i.val
  · simp [h]
  · by_cases h' : j.val < i.val
    · simp [h, h']
    · have hsub : j.val - i.val ≠ 0 := by omega
      simp [h, h', hsub]

private def paidSlots : List Slot :=
  (List.finRange 25).filter fun i => !cornerMask.getLsbD i

-- Enumerate both choices at each positive-weight slot, pruning inclusions over budget.
private def check (slots : List Slot) (budget : ℕ) (s : Mask) : Bool :=
  match slots with
  | [] => good s
  | i :: rest => check rest budget s &&
    (if weight i ≤ budget then check rest (budget - weight i) (s ||| bit i) else true)

set_option maxRecDepth 4000 in
set_option maxHeartbeats 10000000 in
-- The kernel reduces the Boolean search across all occupancy patterns within the budget.
private theorem check_paidSlots : check paidSlots 6 cornerMask = true := by decide +kernel

-- The search includes the bits of any subset whose weight is within budget.
private theorem check_sound {slots : List Slot} {T : Finset Slot} (hT : T ⊆ slots.toFinset)
    {b : ℕ} (hb : ∑ i ∈ T, weight i ≤ b) {s : Mask} (h : check slots b s = true) :
    ∃ u : Mask, good u = true ∧ ∀ i : Slot, u.getLsbD i = (s.getLsbD i || decide (i ∈ T)) := by
  induction slots generalizing T b s with
  | nil =>
    have he : T = ∅ := Finset.subset_empty.mp (by simpa using hT)
    exact ⟨s, h, by simp [he]⟩
  | cons x rest ih =>
    simp only [check, Bool.and_eq_true] at h
    by_cases hx : x ∈ T
    · have hsub : T.erase x ⊆ rest.toFinset := by
        intro i hi
        have ⟨hne, hiT⟩ := Finset.mem_erase.mp hi
        simpa [hne] using hT hiT
      have heq : (∑ i ∈ T.erase x, weight i) + weight x = ∑ i ∈ T, weight i :=
        Finset.sum_erase_add _ _ hx
      have hxB : weight x ≤ b := by omega
      have hb' : ∑ i ∈ T.erase x, weight i ≤ b - weight x := by omega
      obtain ⟨u, hu, hbits⟩ := ih hsub hb' (by simpa only [ite_eq_left hxB] using h.2)
      refine ⟨u, hu, fun i => ?_⟩
      rw [hbits i, BitVec.getLsbD_or, bit_at, Bool.or_assoc]
      by_cases hi : i = x
      · subst i
        simp [hx]
      · simp [hi, Finset.mem_erase]
    · have hsub : T ⊆ rest.toFinset := by
        intro i hi
        have hne : i ≠ x := fun e => hx (e ▸ hi)
        simpa [hne] using hT hi
      exact ih hsub hb h.1

-- Recover a closed set of occupied slots and an interior hole not adjacent to it.
private theorem lowWeight_cut (T : Finset Slot) (hT : ∑ i ∈ T, weight i ≤ 6) :
    ∃ (p : Slot) (A : Set Slot), interior p ∧ p ∉ T ∧ A ⊆ (T : Set Slot) ∧
      (∀ i ∈ T, ¬ interior i → i ∈ A) ∧
      (∀ i ∈ A, ∀ j ∈ T, takAdjacent (coord i) (coord j) → j ∈ A) ∧
      (∀ i ∈ A, ¬ takAdjacent (coord i) (coord p)) := by
  let U := T ∩ paidSlots.toFinset
  have hb : ∑ i ∈ U, weight i ≤ 6 :=
    (Finset.sum_le_sum_of_subset Finset.inter_subset_left).trans hT
  obtain ⟨s, hs, hbits⟩ := check_sound (T := U) Finset.inter_subset_right hb check_paidSlots
  have hmem (i : Slot) (hi : i ∈ T) : s.getLsbD i = true := by
    rw [hbits i]
    cases hc : cornerMask.getLsbD i
    · have hiU : i ∈ U := Finset.mem_inter.mpr ⟨hi, by simp only [paidSlots,
          List.mem_toFinset, List.mem_filter, List.mem_finRange, hc, Bool.not_false, and_self]⟩
      simp [hiU]
    · simp
  have hcut : ∃ f : Mask, uncovered s f = true ∧
      (∀ i : Slot, ¬ interior i → s.getLsbD i = true → f.getLsbD i = true) ∧
      (∀ i j : Slot, f.getLsbD i = true → s.getLsbD j = true →
        takAdjacent (coord i) (coord j) → f.getLsbD j = true) := by
    rcases Bool.or_eq_true_iff.mp (show uncovered s s || _ = true from hs) with h | h
    · exact ⟨s, h, fun _ _ hi => hi, fun _ _ _ hj _ => hj⟩
    · let f := flood s 3
      obtain ⟨hstable, hu⟩ : (extend s f == f) = true ∧ uncovered s f = true :=
        Bool.and_eq_true_iff.mp h
      refine ⟨f, hu, fun _ hi hb => bit_flood_of_boundary hi hb 3, fun i j hi hj hxy => ?_⟩
      have he := congrArg (fun m : Mask => m.getLsbD j) (eq_of_beq hstable)
      simpa [extend, hj, neighbor_bit hxy hi] using he.symm
  obtain ⟨f, hu, hedge, hclosed⟩ := hcut
  obtain ⟨p, hp, hps, hpn⟩ := uncovered_sound hu
  refine ⟨p, {i | i ∈ T ∧ f.getLsbD i = true}, hp, fun h => ?_, fun i hi => hi.1,
    fun i hi hiB => ⟨hi, hedge i hiB (hmem i hi)⟩,
    fun i hi j hj hadj => ⟨hj, hclosed i j hi.2 (hmem j hj) hadj⟩, fun i hi hadj => ?_⟩
  · exact Bool.noConfusion ((hmem p h).symm.trans hps)
  · exact Bool.noConfusion ((neighbor_bit hadj hi.2).symm.trans hpn)

private def windowMap {n r c : ℕ} (hr : r + 5 ≤ n) (hc : c + 5 ≤ n) : Slot ↪ Cell n :=
  coord.toEmbedding.trans
    (((Fin.natAddEmb r).trans (Fin.castLEEmb hr)).prodMap
      ((Fin.natAddEmb c).trans (Fin.castLEEmb hc)))

private theorem windowMap_vals {n r c : ℕ} (hr : r + 5 ≤ n) (hc : c + 5 ≤ n) (i : Slot) :
    (windowMap hr hc i).1.val = r + (coord i).1.val ∧
      (windowMap hr hc i).2.val = c + (coord i).2.val := ⟨rfl, rfl⟩

private theorem mem_range_windowMap {n r c : ℕ} (hr : r + 5 ≤ n) (hc : c + 5 ≤ n) {p : Cell n} :
    p ∈ Set.range (windowMap hr hc) ↔
      r ≤ p.1.val ∧ p.1.val < r + 5 ∧ c ≤ p.2.val ∧ p.2.val < c + 5 := by
  constructor
  · rintro ⟨i, rfl⟩
    obtain ⟨hi, hj⟩ := windowMap_vals hr hc i
    have := (coord i).1.isLt
    have := (coord i).2.isLt
    omega
  · rintro ⟨hp₁, hp₂, hp₃, hp₄⟩
    let x : Fin 5 × Fin 5 := (⟨p.1.val - r, by omega⟩, ⟨p.2.val - c, by omega⟩)
    refine ⟨coord.symm x, Prod.ext (Fin.ext ?_) (Fin.ext ?_)⟩
    · rw [(windowMap_vals hr hc _).1, Equiv.apply_symm_apply]
      exact Nat.add_sub_of_le hp₁
    · rw [(windowMap_vals hr hc _).2, Equiv.apply_symm_apply]
      exact Nat.add_sub_of_le hp₃

private theorem windowMap_adjacent {n r c : ℕ} (hr : r + 5 ≤ n) (hc : c + 5 ≤ n)
    {i j : Slot} : takAdjacent (windowMap hr hc i) (windowMap hr hc j) ↔
      takAdjacent (coord i) (coord j) := by
  obtain ⟨hi, hi'⟩ := windowMap_vals hr hc i
  obtain ⟨hj, hj'⟩ := windowMap_vals hr hc j
  rw [takAdjacent_iff_dist_eq_one, takAdjacent_iff_dist_eq_one, hi, hi', hj, hj',
    Nat.dist_add_add_left, Nat.dist_add_add_left]

private theorem not_onEdge_windowInterior {n r c : ℕ} (hr : r + 5 ≤ n) (hc : c + 5 ≤ n)
    {i : Slot} (hi : interior i) : ¬ onEdge (windowMap hr hc i) := by
  obtain ⟨h₁, h₂⟩ := windowMap_vals hr hc i
  unfold interior at hi
  unfold onEdge
  omega

private theorem mem_window_of_adjacent_interior {n r c : ℕ} (hr : r + 5 ≤ n) (hc : c + 5 ≤ n)
    {i : Slot} (hi : interior i) {x : Cell n} (h : takAdjacent x (windowMap hr hc i)) :
    x ∈ Set.range (windowMap hr hc) := by
  obtain ⟨h₁, h₂⟩ := windowMap_vals hr hc i
  rw [takAdjacent_iff_dist_eq_one, h₁, h₂, Nat.dist, Nat.dist] at h
  unfold interior at hi
  rw [mem_range_windowMap]
  omega

private theorem weight_local_eq_weight_window {n r c : ℕ} (hr : r + 5 ≤ n) (hc : c + 5 ≤ n)
    (S : Finset (Cell n)) :
    ∑ i ∈ Finset.univ.filter (fun i => windowMap hr hc i ∈ S), weight i =
      ∑ p ∈ S.filter (fun p => r ≤ p.1.val ∧ p.1.val < r + 5 ∧ c ≤ p.2.val ∧ p.2.val < c + 5),
        weightedCrossWeight (p.1.val - r) (p.2.val - c) := by
  let e := windowMap hr hc
  have he : (Finset.univ.filter fun i => e i ∈ S).map e = S.filter
      (fun p => r ≤ p.1.val ∧ p.1.val < r + 5 ∧ c ≤ p.2.val ∧ p.2.val < c + 5) := by
    ext p
    simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [← mem_range_windowMap hr hc]
    constructor
    · rintro ⟨i, hi, rfl⟩
      exact ⟨hi, ⟨i, rfl⟩⟩
    · rintro ⟨hi, i, rfl⟩
      exact ⟨i, hi, rfl⟩
  rw [← he, Finset.sum_map]
  apply Finset.sum_congr rfl
  intro i _
  obtain ⟨h₁, h₂⟩ := windowMap_vals hr hc i
  simp only [e, h₁, h₂, Nat.add_sub_cancel_left, weight]

/-- **Weighted Cross bound for Impartial Tak penults.** Let $S$ be a penult of Impartial Tak on
the $n \times n$ board, with rows and columns numbered from $0$. For all natural numbers $r, c$
with $r + 5 \le n$ and $c + 5 \le n$, consider the $5 \times 5$ window of rows $r, \dots, r + 4$
and columns $c, \dots, c + 4$, and give each token of $S$ in the window, lying in row $i$ and
column $j$ of the board, the Weighted Cross weight of position $(i - r, j - c)$. Then the tokens
of $S$ in the window have total weight at least $7$.

Source: Boris Alexeev, Paul Ellis, Michael Richter, and Thotsaporn Aek Thanatipanonda, *The
Penults of Tak: Adventures in Impartial, Normal-Play, Positional Games*, INTEGERS 25 (2025),
Article G1, Proposition 13 (`integers-2025-G1-prop-13`). -/
public theorem impartialTak_penult_weightedCross {n : ℕ} {S : Finset (Fin n × Fin n)}
    (hS : placementPenult takHasRoad S) {r c : ℕ} (hr : r + 5 ≤ n) (hc : c + 5 ≤ n) :
    7 ≤ ∑ p ∈ S.filter (fun p => r ≤ (p.1 : ℕ) ∧ (p.1 : ℕ) < r + 5 ∧ c ≤ (p.2 : ℕ) ∧
      (p.2 : ℕ) < c + 5), weightedCrossWeight ((p.1 : ℕ) - r) ((p.2 : ℕ) - c) := by
  classical
  let e := windowMap hr hc
  let T := Finset.univ.filter fun i => e i ∈ S
  have memT (i) : i ∈ T ↔ e i ∈ S := by simp [T]
  rw [← weight_local_eq_weight_window hr hc S]
  by_contra! hsmall
  obtain ⟨p, A, hp, hpT, hAT, hboundary, hclosed, hfree⟩ :=
    lowWeight_cut T (show ∑ i ∈ T, weight i ≤ 6 by
      change (∑ i ∈ Finset.univ.filter (fun i => windowMap hr hc i ∈ S), weight i) ≤ 6
      omega)
  let B : Set (Cell n) := (Set.range e)ᶜ ∪ e '' A
  have hsep (i : Slot) (hi : i ∈ A) : i ∈ T := hAT hi
  have hpS : e p ∉ S := mt (memT p).mpr hpT
  have hpB : e p ∉ B := by
    rintro (hout | ⟨i, hi, heq⟩)
    · exact hout ⟨p, rfl⟩
    · exact hpT (e.injective heq ▸ hsep i hi)
  apply not_takPenult_of_cut hpS hpB _ _ hS
  · intro x hx hxE
    by_cases hxW : x ∈ Set.range e
    · obtain ⟨i, rfl⟩ := hxW
      have hi : ¬ interior i := fun h => not_onEdge_windowInterior hr hc h hxE
      have hxS := (Finset.mem_insert.mp hx).resolve_left (fun eq => hi (e.injective eq ▸ hp))
      exact Or.inr ⟨i, hboundary i ((memT i).mpr hxS) hi, rfl⟩
    · exact Or.inl hxW
  · intro x hx y hy hadj
    by_cases hyW : y ∈ Set.range e
    · obtain ⟨j, rfl⟩ := hyW
      rcases hx with hx | ⟨i, hi, rfl⟩
      · have hj : ¬ interior j := fun h => hx (mem_window_of_adjacent_interior hr hc h hadj)
        have hyS := (Finset.mem_insert.mp hy).resolve_left (fun eq => hj (e.injective eq ▸ hp))
        exact Or.inr ⟨j, hboundary j ((memT j).mpr hyS) hj, rfl⟩
      · have hadj' := (windowMap_adjacent hr hc).mp hadj
        rcases Finset.mem_insert.mp hy with heq | hjS
        · exact (hfree i hi (e.injective heq ▸ hadj')).elim
        · exact Or.inr ⟨j, hclosed i hi j ((memT j).mpr hjS) hadj', rfl⟩
    · exact Or.inl hyW

end WeightedCross

/-- **A $\frac{7}{26}(n - 4)^2$ lower bound for Impartial Tak penults.** Impartial Tak is the
placement game on the $n \times n$ board whose play ends once the tokens contain a road. For every
$n \ge 5$, every Impartial Tak penult $S$ on the $n \times n$ board satisfies
$7(n - 4)^2 \le 26|S|$, that is, it has at least $\frac{7}{26}(n - 4)^2$ tokens.

Source: the journal text layer prints the bound as `26 (n - 4)2` with the numerator lost; the
numerator `7` is the one in arXiv:2408.01837v1, whose statement prints `(7/26)(n - 8)²` but whose
proof (summing the Weighted Cross bound of Proposition 13 over the `(n - 4)²` windows, each cell
carrying total weight at most `26`) concludes `(7/26)(n - 4)²`, matching the journal's `(n - 4)²`.

Source: Boris Alexeev, Paul Ellis, Michael Richter, and Thotsaporn Aek Thanatipanonda, *The
Penults of Tak: Adventures in Impartial, Normal-Play, Positional Games*, INTEGERS 25 (2025),
Article G1, Proposition 14 (`integers-2025-G1-prop-14`). -/
public theorem impartialTak_penult_card_ge_weightedCross {n : ℕ} (hn : 5 ≤ n)
    {S : Finset (Fin n × Fin n)} (hS : placementPenult takHasRoad S) :
    7 * (n - 4) ^ 2 ≤ 26 * S.card := by
  have h := impartialTak_penult_card_ge_weightedCross.count_inset hn hS
  omega

/-- **An $n^2/4$ lower bound for Impartial Tak penults.** Impartial Tak is the placement game on
the $n \times n$ board whose play ends once the tokens contain a road. There is a real constant $C$
such that for every natural number $n$, every Impartial Tak penult on the $n \times n$ board has at
least $n^2/4 - Cn$ tokens; that is, every penult has at least $n^2/4 + O(n)$ tokens.

Source: Boris Alexeev, Paul Ellis, Michael Richter, and Thotsaporn Aek Thanatipanonda, *The
Penults of Tak: Adventures in Impartial, Normal-Play, Positional Games*, INTEGERS 25 (2025),
Article G1, Proposition 12 (`integers-2025-G1-prop-12`). -/
public theorem impartialTak_penult_card_ge_quarter :
    ∃ C : ℝ, ∀ (n : ℕ) (S : Finset (Fin n × Fin n)), placementPenult takHasRoad S →
      (n : ℝ) ^ 2 / 4 - C * n ≤ S.card := by
  refine ⟨3, fun n S hS => ?_⟩
  have hn0 : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  by_cases hn : 5 ≤ n
  · have hn4 : 4 ≤ n := by omega
    have h : (7 : ℝ) * ((n - 4 : ℕ) : ℝ) ^ 2 ≤ 26 * S.card := by
      exact_mod_cast impartialTak_penult_card_ge_weightedCross hn hS
    rw [Nat.cast_sub hn4, Nat.cast_ofNat] at h
    nlinarith only [h, sq_nonneg (n : ℝ), hn0]
  · have hn4 : (n : ℝ) ≤ 4 := by exact_mod_cast (show n ≤ 4 by omega)
    have hsquare : (n : ℝ) ^ 2 ≤ 4 * n := by
      simpa only [pow_two] using mul_le_mul_of_nonneg_right hn4 hn0
    linarith only [hsquare, hn0, Nat.cast_nonneg (α := ℝ) S.card]

end MetaMathlibExt

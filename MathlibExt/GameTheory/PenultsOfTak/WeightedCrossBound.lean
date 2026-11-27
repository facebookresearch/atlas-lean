/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Basic.Real.Basic
public import MathlibExt.GameTheory.PenultsOfTak
import Mathlib.Tactic.Linarith

/-!
# Lower bounds for Impartial Tak penults

`MetaMathlibExt.impartialTak_penult_card_ge_weightedCross` bounds the size of a penult by
counting the cells covered as one grows the occupied region accessible from the edge.
`MetaMathlibExt.impartialTak_penult_card_ge_quarter` deduces the quarter lower bound from it.

## References

* Boris Alexeev, Paul Ellis, Michael Richter, and Thotsaporn Aek Thanatipanonda,
  [*The Penults of Tak: Adventures in Impartial, Normal-Play, Positional Games*](https://math.colgate.edu/~integers/zg1/zg1.pdf),
  INTEGERS 25 (2025), Article G1, pp. 1–18, Proposition 12 and Proposition 14.
-/

namespace MetaMathlibExt.impartialTak_penult_card_ge_weightedCross

private abbrev Cell (n : ℕ) := Fin n × Fin n

private def onEdge {n : ℕ} (p : Cell n) : Prop :=
  p.1.val = 0 ∨ p.1.val + 1 = n ∨ p.2.val = 0 ∨ p.2.val + 1 = n

private theorem adjacent_symm {n : ℕ} {p q : Cell n} (h : takAdjacent p q) :
    takAdjacent q p := by
  unfold takAdjacent at *
  tauto

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
        unfold takAdjacent at h
        grind
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

-- If an interior move p lies beyond the covered region, collapse its side of
-- the board to the reply q. Every edge of the completed road either survives
-- this map or contracts to a point, giving a road after q alone.
private theorem road_after_reply {n : ℕ} {S A : Finset (Cell n)} {p q : Cell n}
    (hedge : ∀ x, onEdge x → x ∈ A) (hp : p ∉ covered A)
    (hclosed : ∀ s ∈ S, s ∈ covered A → s ∈ A)
    (road : takHasRoad (insert q (insert p S))) : takHasRoad (insert q S) := by
  classical
  let f (x : Cell n) := if x ∈ A then x else q
  have hmem {x} (hx : x ∈ insert q (insert p S)) : f x ∈ insert q S := by
    dsimp only [f]
    split_ifs with h
    · rcases Finset.mem_insert.mp hx with rfl | hx
      · exact Finset.mem_insert_self ..
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact (hp (mem_covered.mpr (.inl h))).elim
      · exact Finset.mem_insert_of_mem hx
    · exact Finset.mem_insert_self ..
  have hfix {x y} (hx : x ∈ A) (hy : y ∈ insert q (insert p S)) (hxy : takAdjacent x y) :
      f y = y := by
    have hcov := mem_covered.mpr (.inr ⟨x, hx, hxy⟩)
    rcases Finset.mem_insert.mp hy with rfl | hy
    · simp [f]
    rcases Finset.mem_insert.mp hy with rfl | hy
    · exact (hp hcov).elim
    · simp [f, hclosed y hy hcov]
  obtain ⟨a, ha, b, path, ends⟩ := road
  have haA : a ∈ A := hedge a (by unfold onEdge; tauto)
  have hbA : b ∈ A := hedge b (by unfold onEdge; tauto)
  have walk {z} (w : Relation.ReflTransGen
      (fun x y => takAdjacent x y ∧ y ∈ insert q (insert p S)) a z) :
      z ∈ insert q (insert p S) ∧ Relation.ReflTransGen
        (fun x y => takAdjacent x y ∧ y ∈ insert q S) (f a) (f z) := by
    induction w with
    | refl => exact ⟨ha, .refl⟩
    | @tail x y _ step ih =>
      obtain ⟨hxy, hy⟩ := step
      obtain ⟨hx, prev⟩ := ih
      refine ⟨hy, ?_⟩
      by_cases hxA : x ∈ A
      · have e := hfix hxA hy hxy
        exact prev.tail ⟨by simpa only [e, f, ite_eq_left hxA] using hxy, hmem hy⟩
      by_cases hyA : y ∈ A
      · have e := hfix hyA hx (adjacent_symm hxy)
        exact prev.tail ⟨by simpa only [e, f, ite_eq_left hyA] using hxy, hmem hy⟩
      · simpa only [f, ite_eq_right hxA, ite_eq_right hyA] using prev
  exact ⟨a, by simpa [f, haA] using hmem ha, b,
    by simpa [f, haA, hbA] using (walk path).2, ends⟩

-- Grow the part of the board accessible from the edge through tokens. Each
-- insertion costs at most three new covered cells. At saturation each remaining
-- uncovered cell is a token: playing an empty one could not create an ult.
private theorem count_from_edge {n : ℕ} {S : Finset (Cell n)}
    (hS : placementPenult takHasRoad S)
    (hfull : ∀ p q, insert q (insert p S) ≠ Finset.univ)
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
    have ih := count_from_edge hS hfull D (insert s A)
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
      obtain ⟨q, hq, ht⟩ := (hS.2 p hs).2
      have hroad := ht.resolve_right (hfull p q)
      have hqS : q ∉ S := fun h => hq (Finset.mem_insert_of_mem h)
      exact ((hS.2 q hqS).1 (.inl (road_after_reply hedge hc hclosed hroad))).elim
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
  by_cases hfull : ∃ p q, insert q (insert p S) = Finset.univ
  · -- A board that can be filled in two moves already has at least n² − 2 tokens.
    obtain ⟨p, q, heq⟩ := hfull
    have hcard := congrArg Finset.card heq
    simp only [Finset.card_univ, Fintype.card_prod, Fintype.card_fin] at hcard
    have hle := Finset.card_insert_le q (insert p S)
    have hle' := Finset.card_insert_le p S
    have hn' : 5 * 5 ≤ n * n := Nat.mul_le_mul hn hn
    have hpow : (n - 4) ^ 2 ≤ n * n := by
      rw [sq]
      exact Nat.mul_le_mul (Nat.sub_le ..) (Nat.sub_le ..)
    omega
  · let A : Finset (Cell n) := Finset.univ.filter onEdge
    let D := Finset.univ.map ((inset hn).prodMap (inset hn))
    have hcount := count_from_edge hS (by simpa using hfull) D A (by simp [A])
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
        simp [takAdjacent, Function.Embedding.prodMap, Fin.ext_iff, inset_val] at hadj
        omega
    rw [hempty] at hcount
    have hsize : D.card = (n - 4) ^ 2 := by simp [D, sq]
    have hle : (S \ A).card ≤ S.card := Finset.card_le_card Finset.sdiff_subset
    simp only [Finset.card_empty, Nat.zero_add, hsize] at hcount
    exact hcount.trans (Nat.mul_le_mul_left 3 hle)

end MetaMathlibExt.impartialTak_penult_card_ge_weightedCross

namespace MetaMathlibExt

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

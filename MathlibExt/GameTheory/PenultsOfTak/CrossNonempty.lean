/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.GameTheory.PenultsOfTak

/-!
# Every Cross meets an Impartial Tak penult

If a Cross is empty, adding its center before another move cannot be essential to a road.
-/

namespace MetaMathlibExt

private theorem adjacent_symm {n : ℕ} {p q : Fin n × Fin n} (h : takAdjacent p q) :
    takAdjacent q p := by
  unfold takAdjacent at *
  tauto

-- As in `WeightedCrossBound.lean`, contract edges in the road: the only neighbor of c
-- in the enlarged position can be q. The path relation tests membership only at the
-- destination, so carry source membership in the induction as well.
private theorem road_after_cross_reply {n : ℕ} {S : Finset (Fin n × Fin n)}
    {c q : Fin n × Fin n} (hr : 1 ≤ (c.1 : ℕ)) (hr' : (c.1 : ℕ) + 1 < n)
    (hc : 1 ≤ (c.2 : ℕ)) (hc' : (c.2 : ℕ) + 1 < n) (hqc : q ≠ c)
    (only_reply : ∀ x ∈ insert q (insert c S), takAdjacent x c → x = q)
    (road : takHasRoad (insert q (insert c S))) : takHasRoad (insert q S) := by
  let f (x : Fin n × Fin n) := if x = c then q else x
  have hmem {x} (hx : x ∈ insert q (insert c S)) : f x ∈ insert q S := by
    by_cases hxc : x = c
    · simp [f, hxc]
    · simpa [f, Finset.mem_insert, hxc] using hx
  have hstep {x y} (hx : x ∈ insert q (insert c S)) (hy : y ∈ insert q (insert c S))
      (hxy : takAdjacent x y) :
      Relation.ReflTransGen (fun u v => takAdjacent u v ∧ v ∈ insert q S) (f x) (f y) := by
    by_cases hxc : x = c
    · subst x
      have hyq := only_reply y hy (adjacent_symm hxy)
      subst y
      simp only [f, ite_eq_left rfl, ite_eq_right hqc]
      exact .refl
    by_cases hyc : y = c
    · subst y
      have hxq := only_reply x hx hxy
      subst x
      simp only [f, ite_eq_left rfl, ite_eq_right hqc]
      exact .refl
    exact .single ⟨by simpa [f, hxc, hyc] using hxy, hmem hy⟩
  obtain ⟨a, ha, b, path, ends⟩ := road
  have hac : a ≠ c := by
    rintro rfl
    rcases ends with ⟨h, _⟩ | ⟨h, _⟩ <;> omega
  have hbc : b ≠ c := by
    rintro rfl
    rcases ends with ⟨_, h⟩ | ⟨_, h⟩ <;> omega
  have walk {z} (w : Relation.ReflTransGen
      (fun x y => takAdjacent x y ∧ y ∈ insert q (insert c S)) a z) :
      z ∈ insert q (insert c S) ∧ Relation.ReflTransGen
        (fun x y => takAdjacent x y ∧ y ∈ insert q S) (f a) (f z) := by
    induction w with
    | refl => exact ⟨ha, .refl⟩
    | tail _ edge ih => exact ⟨edge.2, ih.2.trans (hstep ih.1 edge.2 edge.1)⟩
  exact ⟨a, by simpa only [f, ite_eq_right hac] using hmem ha, b,
    by simpa only [f, ite_eq_right hac, ite_eq_right hbc] using (walk path).2, ends⟩

/-- **Every Cross meets an Impartial Tak penult.** Impartial Tak is the placement game on the
$n \times n$ board whose play ends once the tokens contain a road. Let $S$ be an Impartial Tak
penult on the $n \times n$ board and let $c$ be an interior cell, that is, a cell in neither the
first nor the last row and in neither the first nor the last column. Then $S$ contains $c$ or a
cell orthogonally adjacent to $c$: every Cross (an interior cell together with its four
orthogonal neighbours) contains a token.

Source: Boris Alexeev, Paul Ellis, Michael Richter, and Thotsaporn Aek Thanatipanonda, *The
Penults of Tak: Adventures in Impartial, Normal-Play, Positional Games*, INTEGERS 25 (2025),
Article G1, Proposition 8 (`integers-2025-G1-prop-8`). -/
public theorem impartialTak_penult_cross_nonempty {n : ℕ} {S : Finset (Fin n × Fin n)}
    (hS : placementPenult takHasRoad S) (c : Fin n × Fin n) (hr : 1 ≤ (c.1 : ℕ))
    (hr' : (c.1 : ℕ) + 1 < n) (hc : 1 ≤ (c.2 : ℕ)) (hc' : (c.2 : ℕ) + 1 < n) :
    ∃ p ∈ S, p = c ∨ takAdjacent p c := by
  by_contra hcross
  have hcS : c ∉ S := fun h => hcross ⟨c, h, Or.inl rfl⟩
  obtain ⟨q, hq, hterminal⟩ := (hS.2 c hcS).2
  have hqc : q ≠ c := fun h => hq (Finset.mem_insert.mpr (Or.inl h))
  have hqS : q ∉ S := fun h => hq (Finset.mem_insert_of_mem h)
  have only_reply (x) (hx : x ∈ insert q (insert c S)) (hadj : takAdjacent x c) : x = q := by
    rcases Finset.mem_insert.mp hx with hxq | hx
    · exact hxq
    rcases Finset.mem_insert.mp hx with rfl | hx
    · simp [takAdjacent] at hadj
    · exact (hcross ⟨x, hx, Or.inr hadj⟩).elim
  -- The two horizontal neighbors of c are distinct, and at most one is filled by the reply.
  have hnotFull : insert q (insert c S) ≠ Finset.univ := by
    intro hfull
    let l : Fin n × Fin n := (c.1, ⟨(c.2 : ℕ) - 1, by have := c.2.isLt; omega⟩)
    let r : Fin n × Fin n := (c.1, ⟨(c.2 : ℕ) + 1, hc'⟩)
    have hlAdj : takAdjacent l c := Or.inl ⟨rfl, Or.inl (by dsimp [l]; omega)⟩
    have hrAdj : takAdjacent r c := Or.inl ⟨rfl, Or.inr rfl⟩
    have heq : l = r := (only_reply l (by simp [hfull]) hlAdj).trans
      (only_reply r (by simp [hfull]) hrAdj).symm
    have hcol := congrArg (fun p : Fin n × Fin n => (p.2 : ℕ)) heq
    dsimp [l, r] at hcol
    omega
  have hroad := road_after_cross_reply hr hr' hc hc' hqc only_reply
    (hterminal.resolve_right hnotFull)
  exact (hS.2 q hqS).1 (Or.inl hroad)

end MetaMathlibExt

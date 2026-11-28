/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Complexity.NPComplete.PointSetEmbeddabilityDefs

namespace MetaMathlibExt.Complexity.NPComplete.PointSetEmbeddability

open MetaMathlibExt.BitstringEncoding
open GeometricTravelingSalesman (point)

/-- The collinear points `(0, 0)`, `(1, 0)`, `(2, 0)` (each coordinate `p - q` written as the
pair `(p, q)`) with the edges `es`. -/
private abbrev onLine (es : List (ℕ × ℕ)) : PointSetEmbeddabilityInstance :=
  (es, [((0, 0), (0, 0)), ((1, 0), (0, 0)), ((2, 0), (0, 0))])

/-- The path `0 - 1 - 2` on the collinear points. -/
private abbrev path : PointSetEmbeddabilityInstance := onLine [(0, 1), (1, 2)]

/-- The triangle on the collinear points. -/
private abbrev triangle : PointSetEmbeddabilityInstance := onLine [(0, 1), (1, 2), (0, 2)]

private theorem path_wellFormed : WellFormed path := by unfold WellFormed; decide

private theorem triangle_wellFormed : WellFormed triangle := by unfold WellFormed; decide

/-- Vertex `j` sits at `(j, 0)`. -/
private theorem position_eq (es : List (ℕ × ℕ)) (j : Fin 3) :
    position (onLine es) j = (((j : ℕ) : ℝ), (0 : ℝ)) := by
  fin_cases j <;> simp [position, point, GeometricTravelingSalesman.toInt]

/-- A point of the segment from `(a, 0)` to `(b, 0)` lies on the `x`-axis between `a` and
`b`. -/
private theorem mem_segment_axis {a b : ℝ} {p : ℝ × ℝ}
    (h : p ∈ SimpleGraph.Segment (a, 0) (b, 0)) :
    p.2 = 0 ∧ min a b ≤ p.1 ∧ p.1 ≤ max a b := by
  obtain ⟨t, ht0, ht1, h1, h2⟩ := h
  dsimp only at h1 h2
  refine ⟨by simpa using h2, ?_, ?_⟩
  · rcases le_total a b with hab | hab
    · rw [min_eq_left hab]; nlinarith
    · rw [min_eq_right hab]; nlinarith
  · rcases le_total a b with hab | hab
    · rw [max_eq_right hab]; nlinarith
    · rw [max_eq_left hab]; nlinarith

/-- The identity places the path in order along the line: the segments from `(0, 0)` to
`(1, 0)` and from `(1, 0)` to `(2, 0)` meet only at their common endpoint, and no vertex lies
on a segment other than at its endpoints. -/
private theorem path_feasible : PointSetEmbeddabilityFeasible path := by
  refine ⟨Equiv.refl _, ?_, ?_⟩
  · intro v w x y hvw hxy hne p hp
    simp only [Equiv.refl_apply, position_eq] at hp ⊢
    fin_cases v <;> fin_cases w <;> fin_cases x <;> fin_cases y <;>
      simp [Graph, Cslib.Complexity.Karp.edgeGraph] at hvw hxy <;>
      first
        | exact absurd rfl hne
        | exact absurd (Set.pair_comm _ _) hne
        | (obtain ⟨h1, h2⟩ := hp
           obtain ⟨e1, l1, u1⟩ := mem_segment_axis h1
           obtain ⟨-, l2, u2⟩ := mem_segment_axis h2
           obtain ⟨px, py⟩ := p
           simp only [min_def, max_def] at l1 u1 l2 u2
           norm_num at e1 l1 u1 l2 u2 ⊢
           have hx : px = 1 := by linarith
           subst e1 hx
           norm_num)
  · intro v w u hvw hu
    simp only [Equiv.refl_apply, position_eq] at hu
    fin_cases v <;> fin_cases w <;> fin_cases u <;>
      simp [Graph, Cslib.Complexity.Karp.edgeGraph] at hvw <;>
      first
        | (left; rfl)
        | (right; rfl)
        | (obtain ⟨-, l, r⟩ := mem_segment_axis hu
           simp only [min_def, max_def] at l r
           first | (norm_num at l; done) | norm_num at r)

/-- Every edge of the triangle joins two different vertices. -/
private theorem triangle_adj : ∀ a b : Fin 3, a ≠ b → (Graph triangle).Adj a b := by
  intro a b hab
  fin_cases a <;> fin_cases b <;> simp_all [Graph, Cslib.Complexity.Karp.edgeGraph]

/-- The triangle has no embedding on the collinear points: whichever vertex lands on the
middle point `(1, 0)` lies on the segment of the edge between the other two. -/
private theorem triangle_infeasible : ¬ PointSetEmbeddabilityFeasible triangle := by
  rintro ⟨σ, -, hvert⟩
  have hne : σ.symm 0 ≠ σ.symm 2 := σ.symm.injective.ne (by decide)
  have hmid : position triangle (σ (σ.symm 1)) ∈
      SimpleGraph.Segment (position triangle (σ (σ.symm 0)))
        (position triangle (σ (σ.symm 2))) := by
    simp only [Equiv.apply_symm_apply, position_eq]
    exact ⟨1 / 2, by norm_num, by norm_num, by norm_num, by norm_num⟩
  rcases hvert (σ.symm 1) (triangle_adj _ _ hne) hmid with h | h
  · exact absurd (σ.symm.injective h) (by decide)
  · exact absurd (σ.symm.injective h) (by decide)

/-- The pairs `(1, 0)` and `(2, 1)` both encode the integer `1`, so this instance repeats a
point and is malformed. -/
example : ¬ WellFormed ([(0, 1)], [((1, 0), (0, 0)), ((2, 1), (0, 0))]) := by
  unfold WellFormed; decide

/-- An edge listed in both directions is malformed. -/
example : ¬ WellFormed (onLine [(0, 1), (1, 0)]) := by unfold WellFormed; decide

/-- The decision problem accepts the encoding of the path on the collinear points. -/
example : pointSetEmbeddabilityDec (bitEncode path) = true := by
  simp [pointSetEmbeddabilityDec, path_wellFormed, path_feasible]

/-- It rejects the encoding of the triangle on the same points, which is well formed. -/
example : pointSetEmbeddabilityDec (bitEncode triangle) = false := by
  simp [pointSetEmbeddabilityDec, triangle_infeasible]

/-- The triangle is well formed, so infeasibility is what rejects it. -/
example : WellFormed triangle := triangle_wellFormed

/-- It rejects a lone continuation bit, which decodes to no instance. -/
example : pointSetEmbeddabilityDec [true] = false := by
  have h : bitDecode (α := PointSetEmbeddabilityInstance) [true] = none := rfl
  simp [pointSetEmbeddabilityDec, h]

end MetaMathlibExt.Complexity.NPComplete.PointSetEmbeddability

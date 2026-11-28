/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Complexity.NPComplete.MinSumMulticenterUnitPlanarMaxDegreeThreeDefs

namespace MetaMathlibExt.Complexity.NPComplete.MinSumMulticenterUnitPlanarMaxDegreeThree

open MetaMathlibExt.BitstringEncoding (bitDecode bitDecode_bitEncode bitEncode)
open MetaMathlibExt.Complexity.NPComplete.MinSumMulticenter

private theorem accepts_encoding (i : MinSumMulticenterInstance) :
    minSumMulticenterUnitPlanarMaxDegreeThreeDec (bitEncode i) = true ↔
      WellFormed i ∧ MinSumMulticenterFeasible i := by
  simp [minSumMulticenterUnitPlanarMaxDegreeThreeDec, bitDecode_bitEncode]

private theorem rejects_undecodable (bits : List Bool)
    (h : bitDecode (α := MinSumMulticenterInstance) bits = none) :
    minSumMulticenterUnitPlanarMaxDegreeThreeDec bits = false := by
  simp [minSumMulticenterUnitPlanarMaxDegreeThreeDec, h]

/-- A lone continuation bit is a truncated instance encoding. -/
example : minSumMulticenterUnitPlanarMaxDegreeThreeDec [true] = false :=
  rejects_undecodable [true] rfl

/-- One unit edge `{0, 1}`, unit weights, one point, bound `2 / 1`. -/
private abbrev edgeInst : MinSumMulticenterInstance := (2, [(0, 1, 1)], [1, 1], 1, (2, 1))

/-- Two isolated vertices, unit weights, one point, bound `10 / 1`. -/
private abbrev isolatedInst : MinSumMulticenterInstance := (2, [], [1, 1], 1, (10, 1))

/-- Every graph on two vertices is drawn without crossings on a line. -/
private theorem isPlanar_two (G : SimpleGraph (Fin 2)) : G.IsPlanar := by
  refine Or.inr ⟨fun v => ((v : ℝ), 0), ?_, ?_, ?_⟩
  · intro a b h
    simp only [Prod.mk.injEq, and_true, Nat.cast_inj] at h
    exact Fin.ext h
  · intro v w hvw h
    simp only [Prod.mk.injEq, and_true, Nat.cast_inj] at h
    exact G.ne_of_adj hvw (Fin.ext h)
  · intro v w x y hvw hxy hne
    exfalso
    apply hne
    have h1 := G.ne_of_adj hvw
    have h2 := G.ne_of_adj hxy
    simp only [ne_eq, Fin.ext_iff] at h1 h2
    have := v.isLt; have := w.isLt; have := x.isLt; have := y.isLt
    ext z
    have := z.isLt
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Fin.ext_iff]
    omega

open Classical in
/-- Every vertex of a graph on two vertices has degree at most three (indeed at most two). -/
private theorem degree_two (G : SimpleGraph (Fin 2)) (v : Fin 2) : G.degree v ≤ 3 := by
  rw [← SimpleGraph.card_neighborSet_eq_degree]
  have := @Fintype.card_le_of_injective (G.neighborSet v) (Fin 2) _ _ Subtype.val
    Subtype.val_injective
  rw [Fintype.card_fin] at this
  omega

/-- Vertex `0` serves both vertices within distance `1`, for a total bound of `1 + 1 = 2`. -/
example : minSumMulticenterUnitPlanarMaxDegreeThreeDec (bitEncode edgeInst) = true := by
  apply (accepts_encoding _).2
  have hlen : edgeLength edgeInst s(1, 0) = 1 := by decide
  have hadj : (Graph edgeInst).Adj 1 0 := by
    simp [Graph, Cslib.Complexity.Karp.edgeGraph]
  refine ⟨⟨by unfold MinSumMulticenter.WellFormed; decide, by decide, by decide,
    isPlanar_two _, fun v => degree_two _ v⟩, {(0, 0, 0)}, by simp, ?_, ?_⟩
  · intro p hp
    rw [Finset.mem_singleton] at hp
    subst hp
    exact Or.inl ⟨rfl, rfl⟩
  · refine ⟨fun _ => 1, ?_, ?_⟩
    · intro v
      refine ⟨(0, 0, 0), Finset.mem_singleton_self _, ?_⟩
      rcases v with ⟨_ | _ | n, hn⟩
      · exact Or.inl ⟨SimpleGraph.Walk.nil, by simp [walkLength]⟩
      · refine Or.inl ⟨SimpleGraph.Walk.cons hadj SimpleGraph.Walk.nil, ?_⟩
        simp [walkLength, hlen]
      · exact absurd hn (by simp)
    · have hw : ∀ v, (weight edgeInst v : ℝ) = 1 := by
        intro v
        rcases v with ⟨_ | _ | n, hn⟩
        · simp [weight]
        · simp [weight]
        · exact absurd hn (by simp)
      simp [hw]

/-- Without edges no walk joins the two vertices, so one point cannot serve both. -/
example : minSumMulticenterUnitPlanarMaxDegreeThreeDec (bitEncode isolatedInst) = false := by
  rw [Bool.eq_false_iff, ne_eq, accepts_encoding]
  rintro ⟨-, P, hcard, hon, r, hcov, -⟩
  have hwalk : ∀ {u v : Fin 2}, (Graph isolatedInst).Walk u v → u = v := by
    intro u v W
    cases W with
    | nil => rfl
    | cons h _ => simp [Graph, Cslib.Complexity.Karp.edgeGraph] at h
  have hreach : ∀ v : Fin 2, ∀ p ∈ P, ∀ t, DistLE isolatedInst v p t → v = p.1 := by
    intro v p hp t hd
    have hp1 : p.1 = p.2.1 := by
      rcases hon p hp with h | ⟨h, -⟩
      · exact h.1
      · simp [Graph, Cslib.Complexity.Karp.edgeGraph] at h
    rcases hd with ⟨W, -⟩ | ⟨W, -⟩
    · exact hwalk W
    · rw [hp1]; exact hwalk W
  obtain ⟨p, hp, hd⟩ := hcov 0
  obtain ⟨q, hq, hd'⟩ := hcov 1
  have hpq : q = p := Finset.card_le_one.1 hcard q hq p hp
  subst hpq
  exact absurd ((hreach 0 q hp _ hd).trans (hreach 1 q hq _ hd').symm) (by decide)

/-- The isolated-vertex instance is well formed for the restricted problem. -/
example : WellFormed isolatedInst :=
  ⟨by unfold MinSumMulticenter.WellFormed; decide, by decide, by decide, isPlanar_two _,
    fun v => degree_two _ v⟩

/-- An edge of length `2` is malformed here, though plain MIN-SUM MULTICENTER allows it. -/
example :
    minSumMulticenterUnitPlanarMaxDegreeThreeDec (bitEncode
      ((2, [(0, 1, 2)], [1, 1], 1, (1, 1)) : MinSumMulticenterInstance)) = false := by
  rw [Bool.eq_false_iff, ne_eq, accepts_encoding]
  rintro ⟨⟨-, -, h, -⟩, -⟩
  exact absurd (h (0, 1, 2) (by simp)) (by decide)

end MetaMathlibExt.Complexity.NPComplete.MinSumMulticenterUnitPlanarMaxDegreeThree

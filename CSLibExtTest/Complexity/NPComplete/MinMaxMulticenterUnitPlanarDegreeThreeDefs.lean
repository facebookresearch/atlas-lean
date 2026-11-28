/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Complexity.NPComplete.MinMaxMulticenterUnitPlanarDegreeThreeDefs

namespace MetaMathlibExt.Complexity.NPComplete.MinMaxMulticenterUnitPlanarDegreeThree

open MetaMathlibExt.BitstringEncoding (bitDecode bitDecode_bitEncode bitEncode)
open MetaMathlibExt.Complexity.NPComplete.MinMaxMulticenter

private theorem accepts_encoding (i : MinMaxMulticenterInstance) :
    minMaxMulticenterUnitPlanarDegreeThreeDec (bitEncode i) = true ↔
      WellFormed i ∧ MinMaxMulticenterFeasible i := by
  simp [minMaxMulticenterUnitPlanarDegreeThreeDec, bitDecode_bitEncode]

private theorem rejects_undecodable (bits : List Bool)
    (h : bitDecode (α := MinMaxMulticenterInstance) bits = none) :
    minMaxMulticenterUnitPlanarDegreeThreeDec bits = false := by
  simp [minMaxMulticenterUnitPlanarDegreeThreeDec, h]

/-- A lone continuation bit is a truncated instance encoding. -/
example : minMaxMulticenterUnitPlanarDegreeThreeDec [true] = false :=
  rejects_undecodable [true] rfl

/-- One unit edge `{0, 1}`, unit weights, one point, bound `1 / 1`. -/
private abbrev edgeInst : MinMaxMulticenterInstance := (2, [(0, 1, 1)], [1, 1], 1, (1, 1))

/-- Two isolated vertices, unit weights, one point, bound `1 / 1`. -/
private abbrev isolatedInst : MinMaxMulticenterInstance := (2, [], [1, 1], 1, (1, 1))

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

/-- Every vertex of a graph on two vertices has at most three (indeed at most two) neighbors. -/
private theorem ncard_neighborSet_two (G : SimpleGraph (Fin 2)) (v : Fin 2) :
    (G.neighborSet v).ncard ≤ 3 := by
  have := Set.ncard_le_ncard (Set.subset_univ (G.neighborSet v))
  rw [Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin] at this
  omega

/-- Vertex `0` serves vertex `1` across the unit edge, at weighted distance `1`. -/
example : minMaxMulticenterUnitPlanarDegreeThreeDec (bitEncode edgeInst) = true := by
  apply (accepts_encoding _).2
  have hlen : edgeLength edgeInst s(1, 0) = 1 := by decide
  have hadj : (Graph edgeInst).Adj 1 0 := by
    simp [Graph, Cslib.Complexity.Karp.edgeGraph]
  refine ⟨⟨by unfold MinMaxMulticenter.WellFormed; decide, by decide, by decide,
    isPlanar_two _, ncard_neighborSet_two _⟩, {(0, 0, 0)}, by simp, ?_, ?_⟩
  · intro p hp
    rw [Finset.mem_singleton] at hp
    subst hp
    exact Or.inl ⟨rfl, rfl⟩
  · intro v
    refine ⟨(0, 0, 0), Finset.mem_singleton_self _, 1, ?_, ?_⟩
    · rcases v with ⟨_ | _ | n, hn⟩
      · exact Or.inl ⟨SimpleGraph.Walk.nil, by simp [walkLength]⟩
      · refine Or.inl ⟨SimpleGraph.Walk.cons hadj SimpleGraph.Walk.nil, ?_⟩
        simp [walkLength, hlen]
      · exact absurd hn (by simp)
    · rcases v with ⟨_ | _ | n, hn⟩
      · simp [weight]
      · simp [weight]
      · exact absurd hn (by simp)

/-- Without edges no walk joins the two vertices, so one point cannot serve both. -/
example : minMaxMulticenterUnitPlanarDegreeThreeDec (bitEncode isolatedInst) = false := by
  rw [Bool.eq_false_iff, ne_eq, accepts_encoding]
  rintro ⟨-, P, hcard, hon, hcov⟩
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
  obtain ⟨p, hp, r, hd, -⟩ := hcov 0
  obtain ⟨q, hq, s, hd', -⟩ := hcov 1
  have hpq : q = p := Finset.card_le_one.1 hcard q hq p hp
  subst hpq
  exact absurd ((hreach 0 q hp r hd).trans (hreach 1 q hq s hd').symm) (by decide)

/-- The isolated-vertex instance is well formed for the restricted problem. -/
example : WellFormed isolatedInst :=
  ⟨by unfold MinMaxMulticenter.WellFormed; decide, by decide, by decide, isPlanar_two _,
    ncard_neighborSet_two _⟩

/-- An edge of length `2` is malformed here, though plain MIN-MAX MULTICENTER allows it. -/
example :
    minMaxMulticenterUnitPlanarDegreeThreeDec (bitEncode
      ((2, [(0, 1, 2)], [1, 1], 1, (1, 1)) : MinMaxMulticenterInstance)) = false := by
  rw [Bool.eq_false_iff, ne_eq, accepts_encoding]
  rintro ⟨⟨-, -, h, -⟩, -⟩
  exact absurd (h (0, 1, 2) (by simp)) (by decide)

end MetaMathlibExt.Complexity.NPComplete.MinMaxMulticenterUnitPlanarDegreeThree

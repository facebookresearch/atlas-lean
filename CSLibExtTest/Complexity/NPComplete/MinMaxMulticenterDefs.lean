/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Complexity.NPComplete.MinMaxMulticenterDefs

namespace MetaMathlibExt.Complexity.NPComplete.MinMaxMulticenter

open MetaMathlibExt.BitstringEncoding (bitDecode bitDecode_bitEncode bitEncode)

private theorem accepts_encoding (i : MinMaxMulticenterInstance) :
    minMaxMulticenterDec (bitEncode i) = true ↔
      WellFormed i ∧ MinMaxMulticenterFeasible i := by
  simp [minMaxMulticenterDec, bitDecode_bitEncode]

private theorem rejects_undecodable (bits : List Bool)
    (h : bitDecode (α := MinMaxMulticenterInstance) bits = none) :
    minMaxMulticenterDec bits = false := by
  simp [minMaxMulticenterDec, h]

/-- A lone continuation bit is a truncated instance encoding. -/
example : minMaxMulticenterDec [true] = false :=
  rejects_undecodable [true] rfl

/-- One edge `{0, 1}` of length `2`, unit weights, one point, bound `1 / 1`. -/
private abbrev edgeInst : MinMaxMulticenterInstance := (2, [(0, 1, 2)], [1, 1], 1, (1, 1))

/-- Two isolated vertices, unit weights, one point, bound `1 / 1`. -/
private abbrev isolatedInst : MinMaxMulticenterInstance := (2, [], [1, 1], 1, (1, 1))

/-- The midpoint of the edge `{0, 1}` of length `2` is at distance `1` from both endpoints. -/
example : minMaxMulticenterDec (bitEncode edgeInst) = true := by
  apply (accepts_encoding _).2
  have hlen : edgeLength edgeInst s(0, 1) = 2 := by decide
  have hadj : (Graph edgeInst).Adj 0 1 := by
    simp [Graph, Cslib.Complexity.Karp.edgeGraph]
  refine ⟨by unfold WellFormed; decide, {(0, 1, 1)}, by simp, ?_, ?_⟩
  · intro p hp
    rw [Finset.mem_singleton] at hp
    subst hp
    refine Or.inr ⟨hadj, by norm_num, ?_⟩
    rw [hlen]
    norm_num
  · intro v
    refine ⟨(0, 1, 1), Finset.mem_singleton_self _, 1, ?_, ?_⟩
    · rcases v with ⟨_ | _ | n, hn⟩
      · exact Or.inl ⟨SimpleGraph.Walk.nil, by simp [walkLength]⟩
      · refine Or.inr ⟨SimpleGraph.Walk.nil, ?_⟩
        rw [hlen]
        norm_num [walkLength]
        exact one_add_one_eq_two.ge
      · exact absurd hn (by simp)
    · rcases v with ⟨_ | _ | n, hn⟩
      · simp [weight]
      · simp [weight]
      · exact absurd hn (by simp)

/-- Without edges no walk joins the two vertices, so one point cannot serve both. -/
example : minMaxMulticenterDec (bitEncode isolatedInst) = false := by
  rw [Bool.eq_false_iff, ne_eq, accepts_encoding]
  rintro ⟨-, P, hcard, hon, hcov⟩
  have hwalk : ∀ {u v : Fin 2}, (Graph isolatedInst).Walk u v → u = v := by
    intro u v W
    cases W with
    | nil => rfl
    | cons h _ => simp [Graph, Cslib.Complexity.Karp.edgeGraph] at h
  have hreach : ∀ v : Fin 2, ∀ p ∈ P, ∀ r, DistLE isolatedInst v p r → v = p.1 := by
    intro v p hp r hd
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
  have h0 := hreach 0 q hp r hd
  have h1 := hreach 1 q hq s hd'
  exact absurd (h0.trans h1.symm) (by decide)

/-- A zero bound numerator is malformed. -/
example :
    minMaxMulticenterDec (bitEncode
      ((2, [(0, 1, 2)], [1, 1], 1, (0, 1)) : MinMaxMulticenterInstance)) = false := by
  rw [Bool.eq_false_iff, ne_eq, accepts_encoding]
  rintro ⟨⟨-, -, -, -, h, -⟩, -⟩
  exact absurd h (by decide)

end MetaMathlibExt.Complexity.NPComplete.MinMaxMulticenter

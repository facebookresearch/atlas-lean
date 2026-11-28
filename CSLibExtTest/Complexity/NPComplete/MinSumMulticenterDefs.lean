/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Complexity.NPComplete.MinSumMulticenterDefs

namespace MetaMathlibExt.Complexity.NPComplete.MinSumMulticenter

open MetaMathlibExt.BitstringEncoding (bitDecode bitDecode_bitEncode bitEncode)

private theorem accepts_encoding (i : MinSumMulticenterInstance) :
    minSumMulticenterDec (bitEncode i) = true ↔
      WellFormed i ∧ MinSumMulticenterFeasible i := by
  simp [minSumMulticenterDec, bitDecode_bitEncode]

private theorem rejects_undecodable (bits : List Bool)
    (h : bitDecode (α := MinSumMulticenterInstance) bits = none) :
    minSumMulticenterDec bits = false := by
  simp [minSumMulticenterDec, h]

/-- A lone continuation bit is a truncated instance encoding. -/
example : minSumMulticenterDec [true] = false :=
  rejects_undecodable [true] rfl

/-- One edge `{0, 1}` of length `2`, unit weights, one point, bound `2 / 1`. -/
private abbrev edgeInst : MinSumMulticenterInstance := (2, [(0, 1, 2)], [1, 1], 1, (2, 1))

/-- Two isolated vertices, unit weights, one point, bound `10 / 1`. -/
private abbrev isolatedInst : MinSumMulticenterInstance := (2, [], [1, 1], 1, (10, 1))

/-- The midpoint of the edge `{0, 1}` of length `2` is at distance `1` from both endpoints, for
total weighted distance `1 + 1 = 2`. -/
example : minSumMulticenterDec (bitEncode edgeInst) = true := by
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
  · refine ⟨fun _ => 1, ?_, ?_⟩
    · intro v
      refine ⟨(0, 1, 1), Finset.mem_singleton_self _, ?_⟩
      rcases v with ⟨_ | _ | n, hn⟩
      · exact Or.inl ⟨SimpleGraph.Walk.nil, by simp [walkLength]⟩
      · refine Or.inr ⟨SimpleGraph.Walk.nil, ?_⟩
        rw [hlen]
        norm_num [walkLength]
        exact one_add_one_eq_two.ge
      · exact absurd hn (by simp)
    · have hw : ∀ v, (weight edgeInst v : ℝ) = 1 := by
        intro v
        rcases v with ⟨_ | _ | n, hn⟩
        · simp [weight]
        · simp [weight]
        · exact absurd hn (by simp)
      simp [hw]

/-- Without edges no walk joins the two vertices, so one point cannot serve both. -/
example : minSumMulticenterDec (bitEncode isolatedInst) = false := by
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
  have h0 := hreach 0 q hp _ hd
  have h1 := hreach 1 q hq _ hd'
  exact absurd (h0.trans h1.symm) (by decide)

/-- A zero bound numerator is malformed. -/
example :
    minSumMulticenterDec (bitEncode
      ((2, [(0, 1, 2)], [1, 1], 1, (0, 1)) : MinSumMulticenterInstance)) = false := by
  rw [Bool.eq_false_iff, ne_eq, accepts_encoding]
  rintro ⟨⟨-, -, -, -, h, -⟩, -⟩
  exact absurd h (by decide)

end MetaMathlibExt.Complexity.NPComplete.MinSumMulticenter

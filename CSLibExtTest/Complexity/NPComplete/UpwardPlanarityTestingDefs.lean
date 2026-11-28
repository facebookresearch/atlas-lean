/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Complexity.NPComplete.UpwardPlanarityTestingDefs
import Mathlib.Tactic.Linarith

namespace MetaMathlibExt.Complexity.NPComplete.UpwardPlanarityTesting

open MetaMathlibExt.BitstringEncoding (bitDecode bitDecode_bitEncode bitEncode)

private theorem accepts_encoding (i : UpwardPlanarityTestingInstance) :
    upwardPlanarityTestingDec (bitEncode i) = true ↔
      WellFormed i ∧ UpwardPlanarityTestingFeasible i := by
  simp [upwardPlanarityTestingDec, bitDecode_bitEncode]

/-- A lone continuation bit is a truncated instance encoding. -/
example : upwardPlanarityTestingDec [true] = false := by
  have h : bitDecode (α := UpwardPlanarityTestingInstance) [true] = none := rfl
  simp [upwardPlanarityTestingDec, h]

/-- The directed path `0 → 1 → 2`. -/
private abbrev path3 : UpwardPlanarityTestingInstance := (3, [(0, 1), (1, 2)])

/-- The drawing `0 ↦ (0, 0)`, `1 ↦ (1, 1)`, `2 ↦ (0, 2)`. -/
private noncomputable def draw (v : Fin 3) : ℝ × ℝ :=
  if v = 0 then (0, 0) else if v = 1 then (1, 1) else (0, 2)

private theorem arcs (u v : Fin 3) (h : (Graph path3).Adj u v) :
    (u = 0 ∧ v = 1) ∨ (u = 1 ∧ v = 2) := by
  revert u v
  simp only [Graph]
  decide

private theorem vertices (v : Fin 3) : v = 0 ∨ v = 1 ∨ v = 2 := by
  revert v
  decide

/-- The directed path `0 → 1 → 2` has an upward planar drawing with a bend at `1`. -/
example : upwardPlanarityTestingDec (bitEncode path3) = true := by
  apply (accepts_encoding _).2
  refine ⟨⟨by decide, by decide, fun v h => ?_⟩, draw, ?_, ?_, ?_, ?_⟩
  · have key : ∀ u v : Fin 3, Relation.TransGen (Graph path3).Adj u v → u < v := by
      intro u v h
      induction h with
      | single h => rcases arcs _ _ h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
      | tail _ h ih => rcases arcs _ _ h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> omega
    exact lt_irrefl v (key v v h)
  · intro a b h
    rcases vertices a with rfl | rfl | rfl <;> rcases vertices b with rfl | rfl | rfl <;>
      simp [draw, Prod.ext_iff] at h ⊢
  · intro u v h
    rcases arcs u v h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp [draw]
  · intro u v x y huv hxy hne z ⟨hz₁, hz₂⟩
    obtain ⟨t, ht₀, ht₁, hzt₁, hzt₂⟩ := hz₁
    obtain ⟨s, hs₀, hs₁, hzs₁, hzs₂⟩ := hz₂
    rcases arcs u v huv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases arcs x y hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact absurd rfl hne
    · simp [draw] at hzt₁ hzt₂ hzs₁ hzs₂
      have hz : z = (1, 1) := Prod.ext (by linarith) (by linarith)
      simp [draw, hz]
    · simp [draw] at hzt₁ hzt₂ hzs₁ hzs₂
      have hz : z = (1, 1) := Prod.ext (by linarith) (by linarith)
      simp [draw, hz]
    · exact absurd rfl hne
  · intro u v w huv ⟨t, ht₀, ht₁, h₁, h₂⟩
    rcases arcs u v huv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases vertices w with rfl | rfl | rfl <;> simp [draw] at h₁ h₂ ⊢ <;> linarith

/-- The two-cycle `0 → 1 → 0` has no upward drawing: each arc must go strictly up. -/
example : upwardPlanarityTestingDec (bitEncode ((2, [(0, 1), (1, 0)]) :
    UpwardPlanarityTestingInstance)) = false := by
  rw [Bool.eq_false_iff, ne_eq, accepts_encoding]
  rintro ⟨-, f, -, hup, -, -⟩
  have h₀₁ := @hup 0 1 (by simp [Graph])
  have h₁₀ := @hup 1 0 (by simp [Graph])
  linarith

/-- The two-cycle is also rejected as malformed: it is not acyclic. -/
example : ¬ WellFormed ((2, [(0, 1), (1, 0)]) : UpwardPlanarityTestingInstance) := by
  rintro ⟨-, -, hacyc⟩
  exact hacyc 0 (.tail (.single (b := 1) (by simp [Graph])) (by simp [Graph]))

end MetaMathlibExt.Complexity.NPComplete.UpwardPlanarityTesting

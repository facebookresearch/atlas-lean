/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Complexity.NPComplete.SimpleAssemblyLineBalancingDefs

namespace MetaMathlibExt.Complexity.NPComplete.SimpleAssemblyLineBalancing

open MetaMathlibExt.BitstringEncoding (bitDecode bitDecode_bitEncode bitEncode)

private theorem accepts_encoding (i : SimpleAssemblyLineBalancingInstance) :
    simpleAssemblyLineBalancingDec (bitEncode i) = true ↔
      WellFormed i ∧ SimpleAssemblyLineBalancingFeasible i := by
  simp [simpleAssemblyLineBalancingDec, bitDecode_bitEncode]

/-- A lone continuation bit is a truncated instance encoding. -/
example : simpleAssemblyLineBalancingDec [true] = false := by
  have h : bitDecode (α := SimpleAssemblyLineBalancingInstance) [true] = none := rfl
  simp [simpleAssemblyLineBalancingDec, h]

/-- The single arc `0 → 1` has no cycle: every chain of arcs is that one arc. -/
private theorem acyclic_single :
    ∀ v, ¬ Relation.TransGen (fun a b => (a, b) ∈ ([(0, 1)] : List (ℕ × ℕ))) v v := by
  have key : ∀ a b, Relation.TransGen (fun a b => (a, b) ∈ ([(0, 1)] : List (ℕ × ℕ))) a b →
      a = 0 ∧ b = 1 := by
    intro a b h
    induction h with
    | single h => simpa using h
    | tail _ h ih => simp at h; omega
  intro v h
  have := key v v h
  omega

/-- Tasks of times `2, 2, 1` with `0` before `1` fit two stations of cycle time `3`:
tasks `0, 2` at station `0` and task `1` at station `1`. -/
example : simpleAssemblyLineBalancingDec
    (bitEncode (([2, 2, 1], [(0, 1)], 3, 2) : SimpleAssemblyLineBalancingInstance)) = true := by
  refine (accepts_encoding _).2
    ⟨⟨by simp, acyclic_single⟩, fun j => if (j : ℕ) = 1 then 1 else 0, ?_, by decide⟩
  intro a b hab
  simp only [List.mem_singleton, Prod.mk.injEq] at hab
  obtain ⟨ha, hb⟩ := hab
  have ha' : a = 0 := Fin.ext ha
  have hb' : b = 1 := Fin.ext hb
  subst ha' hb'
  decide

/-- Tasks of times `1, 2, 1` fit two stations of cycle time `2` (tasks `0, 2` together, task `1`
alone), but not under the chain `0 → 1 → 2`: task `1` fills its station, so the chain needs
three stations. -/
example : simpleAssemblyLineBalancingDec
      (bitEncode (([1, 2, 1], [], 2, 2) : SimpleAssemblyLineBalancingInstance)) = true ∧
    simpleAssemblyLineBalancingDec
      (bitEncode (([1, 2, 1], [(0, 1), (1, 2)], 2, 2) : SimpleAssemblyLineBalancingInstance)) =
        false := by
  constructor
  · refine (accepts_encoding _).2 ⟨⟨by simp, fun v h => ?_⟩,
      fun j => if (j : ℕ) = 1 then 1 else 0, by simp, by decide⟩
    cases h with
    | single h => simp at h
    | tail _ h => simp at h
  · rw [Bool.eq_false_iff]
    intro h
    obtain ⟨-, f, harc, hcap⟩ := (accepts_encoding _).1 h
    have h01 := harc 0 1 (by simp)
    have h12 := harc 1 2 (by simp)
    revert f
    decide

/-- A self-loop `0 → 0` makes the precedence graph cyclic, so the instance is malformed. -/
example : simpleAssemblyLineBalancingDec
    (bitEncode (([1], [(0, 0)], 1, 1) : SimpleAssemblyLineBalancingInstance)) = false := by
  rw [Bool.eq_false_iff]
  intro h
  exact ((accepts_encoding _).1 h).1.2 0 (Relation.TransGen.single (by simp))

end MetaMathlibExt.Complexity.NPComplete.SimpleAssemblyLineBalancing

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Complexity.NPComplete.HotaruBeamDefs

namespace MetaMathlibExt.Complexity.NPComplete.HotaruBeam

open MetaMathlibExt.BitstringEncoding (bitDecode bitDecode_bitEncode bitEncode)

private theorem accepts_encoding (i : HotaruBeamInstance) :
    hotaruBeamDec (bitEncode i) = true ↔ WellFormed i ∧ HotaruBeamFeasible i := by
  simp [hotaruBeamDec, bitDecode_bitEncode]

/-- A `2 × 2` grid with a firefly at `(0, 0)` facing `+x` numbered `n`, and a firefly at
`(1, 0)` facing `+y` numbered `2`. -/
private abbrev board (n : ℕ) : HotaruBeamInstance :=
  ([true, true], [true, true], [((0, 0), 0, true, n), ((1, 0), 1, true, 2)])

/-- The beams: `(0, 0) → (1, 0)`, and `(1, 0) → (1, 1) → (0, 1) → (0, 0)` with two bends. -/
private def beams : Fin 2 → List (ℕ × ℕ) := fun f =>
  if f.val = 0 then [(1, 0)] else [(1, 1), (0, 1), (0, 0)]

/-- A lone continuation bit is a truncated instance encoding. -/
example : hotaruBeamDec [true] = false := by
  have h : bitDecode (α := HotaruBeamInstance) [true] = none := rfl
  simp [hotaruBeamDec, h]

/-- The two fireflies beam at each other: the first straight into the second (no bend), the
second around the square with two bends, entering the first away from its dot. -/
example : hotaruBeamDec (bitEncode (board 0)) = true := by
  apply (accepts_encoding _).2
  refine ⟨by unfold WellFormed; decide, beams, fun f => ⟨1 - f.val, by show 1 - f.val < 2; omega⟩,
    ?_, ?_, ?_⟩
  · intro ⟨f, hf⟩
    have : f = 0 ∨ f = 1 := by simp at hf; omega
    rcases this with rfl | rfl
    · simp [BeamOK, beams, IsStep, Adjacent, bends]
    · simp [BeamOK, beams, IsStep, Adjacent, bends]
      decide
  · intro ⟨f, hf⟩ ⟨f', hf'⟩ j hj j' hj' heq
    have : f = 0 ∨ f = 1 := by simp at hf; omega
    have : f' = 0 ∨ f' = 1 := by simp at hf'; omega
    rcases ‹f = 0 ∨ f = 1› with rfl | rfl <;> rcases ‹f' = 0 ∨ f' = 1› with rfl | rfl <;>
      simp [beams] at hj hj' heq ⊢
    rcases (show j = 0 ∨ j = 1 by omega) with rfl | rfl <;>
      rcases (show j' = 0 ∨ j' = 1 by omega) with rfl | rfl <;> simp at heq ⊢
  · rw [SimpleGraph.connected_iff_exists_forall_reachable]
    refine ⟨⟨0, by decide⟩, fun ⟨w, hw⟩ => ?_⟩
    have : w = 0 ∨ w = 1 := by simp at hw; omega
    rcases this with rfl | rfl
    · exact SimpleGraph.Reachable.refl _
    · exact SimpleGraph.Adj.reachable (by simp [SimpleGraph.fromRel_adj])

/-- Numbered `1`, the first firefly cannot comply: its first step already reaches the second
firefly, so its beam is a single segment without a bend. -/
example : hotaruBeamDec (bitEncode (board 1)) = false := by
  rw [Bool.eq_false_iff]
  intro hacc
  obtain ⟨-, beam, tgt, hok, -, -⟩ := (accepts_encoding _).1 hacc
  obtain ⟨hne, hstep, -, -, hpass, -, -, hbend⟩ := hok ⟨0, by decide⟩
  simp only [IsStep] at hstep
  have hb0 : (beam ⟨0, by decide⟩).getD 0 (0, 0) = (1, 0) := by
    simp at hstep
    exact hstep
  have hlen : (beam ⟨0, by decide⟩).length ≤ 1 := by
    by_contra h
    exact hpass 0 (by omega) ((1, 0), 1, true, 2) (by simp) hb0
  obtain ⟨b, hb⟩ : ∃ b, beam ⟨0, by decide⟩ = [b] := by
    match h : beam ⟨0, by decide⟩, hne, hlen with
    | [b], _, _ => exact ⟨b, rfl⟩
  rw [hb] at hbend
  simp [bends] at hbend

/-- The no-instance above is well formed, so it is rejected for infeasibility. -/
example : WellFormed (board 1) :=
  by unfold WellFormed; decide

end MetaMathlibExt.Complexity.NPComplete.HotaruBeam

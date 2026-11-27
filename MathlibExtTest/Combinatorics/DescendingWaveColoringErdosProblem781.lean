/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.DescendingWaveColoringErdosProblem781

open MathlibExt.Combinatorics.DescendingWaveColoringErdosProblem781Wanted

-- Equal successive gaps satisfy the descending-wave inequality.
example : IsDescendingWave (fun i : Fin 3 => i.val + 1) := by
  constructor
  · intro i j hij
    exact Nat.add_lt_add_right hij 1
  · intro i j l hij hjl
    change (i.val + 1) + (l.val + 1) ≤ 2 * (j.val + 1)
    omega

-- The points 1, 2, 5 are strictly increasing, but their gaps increase.
example : ¬ IsDescendingWave (fun i : Fin 3 => i.val ^ 2 + 1) := by
  intro hw
  exact (by decide : ¬ 1 + 5 ≤ 2 * 2) (hw.2 0 1 2 rfl rfl)

-- A constant pair satisfies the gap condition but fails strict increase.
example : ¬ IsDescendingWave (fun _ : Fin 2 => 1) := by
  intro hw
  exact (Nat.lt_irrefl 1) (hw.1 (show (0 : Fin 2) < 1 by decide))

-- A singleton wave needs one positive point.
example : ForcesMonochromaticWave 1 1 := by
  intro c
  refine ⟨fun _ => 1, ⟨?_, ?_⟩, fun _ => ⟨le_rfl, le_rfl⟩, c 1, fun _ => rfl⟩
  · exact Subsingleton.strictMono _
  · intros
    exact le_rfl

example : ¬ ForcesMonochromaticWave 1 0 := by
  intro h
  obtain ⟨x, _, hb, _⟩ := h (fun _ => 0)
  have := hb 0
  omega

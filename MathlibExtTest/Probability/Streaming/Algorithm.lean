/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Streaming.Algorithm

@[expose] public section

open MathlibExt.Probability.Streaming

namespace MathlibExtTest.Probability.Streaming

-- A deterministic two-bit counter of the stream length (modulo 4), with a trivial seed.
def counter : StreamingAlgorithm (Fin 3) Unit 2 where
  init _ := 0
  step _ c _ := c + 1
  out _ c := (c : ℕ)

example : counter.output () [0, 2, 2] = 3 := by
  simp [counter, StreamingAlgorithm.output]

-- It computes `F₁ = 3` exactly on that stream, so its failure probability is `0`.
example : counter.failProb (fun l y => y = l.length) [0, 2, 2] = 0 := by
  have h : counter.output () [0, 2, 2] = 3 := by
    simp [counter, StreamingAlgorithm.output]
  simp [StreamingAlgorithm.failProb, h]

/-- The same counter with an empty seed space. -/
def counterEmpty : StreamingAlgorithm (Fin 3) Empty 2 where
  init _ := 0
  step _ c _ := c + 1
  out _ c := (c : ℕ)

/-! The failure probability needs a nonempty seed space: for an empty one, under which every
failure probability would be `0`, it does not elaborate. -/

/--
error: failed to synthesize instance of type class
  Nonempty Empty

Hint: Adding the command `deriving instance Nonempty for Empty` may allow Lean to derive the missing instance.
-/
#guard_msgs in
noncomputable example : ℝ := counterEmpty.failProb (fun _ _ => False) [0]

-- Multiplicities and moments of the stream `0, 2, 2` over `Fin 3`.
example : maxFreq ([0, 2, 2] : List (Fin 3)) = 2 := by decide
example : freqMoment 2 ([0, 2, 2] : List (Fin 3)) = 5 := by decide
-- With Lean's `0 ^ 0 = 1`, `freqMoment 0` is `n = 3`, not the source's `F₀` (here `2`).
example : freqMoment 0 ([0, 2, 2] : List (Fin 3)) = 3 := by decide

end MathlibExtTest.Probability.Streaming

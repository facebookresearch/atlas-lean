/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Tactic.NormNum
import MathlibExt.Combinatorics.ContinuousTuranMonotonicity

open MetaMathlibExt

example {d : ℕ} (P : Set (Fin d → ℝ)) : Monotone (fun n => opxD d n P) :=
  fun _ _ hmn => opxD_mono_left P hmn

-- Both side lengths may be negative.
example (P : Set (Fin 3 → ℝ)) : opxD 3 (-2) P ≤ opxD 3 (-1) P :=
  opxD_mono_left P (by norm_num)

-- Dimension zero is allowed, including at the zero endpoint.
example (P : Set (Fin 0 → ℝ)) : opxD 0 (-1) P ≤ opxD 0 0 P :=
  opxD_mono_left P (by norm_num)

-- For the empty pattern, there are no admissible open sets in either cube.
example : opxD 3 1 ∅ ≤ opxD 3 2 ∅ :=
  opxD_mono_left ∅ (by norm_num)

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.WieferichNineCubes

open MathlibExt.NumberTheory.WieferichNineCubesWanted.NumberTheory

example : IsSumOfCubes 9 0 := wieferich_g_three.1 0

-- The sharpness witness uses two cubes of two and seven cubes of one.
example : IsSumOfCubes 9 23 :=
  ⟨![2, 2, 1, 1, 1, 1, 1, 1, 1], by decide⟩

example : ¬ ∀ n, IsSumOfCubes 8 n := by
  obtain ⟨n, hn⟩ := wieferich_g_three.2
  exact fun h => hn (h n)

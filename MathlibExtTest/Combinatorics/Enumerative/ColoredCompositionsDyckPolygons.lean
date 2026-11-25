/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.ColoredCompositionsDyckPolygons

open MetaMathlibExt

-- Only descents of length two and quadrilateral faces are allowed.
example : coloredDyckPathCount (fun j => if j = 2 then 1 else 0) 4 2 = 2 := by
  decide +kernel

example : coloredPolygonDissectionCount (fun j => if j = 2 then 1 else 0) 4 2 = 3 := by
  decide +kernel

-- The two chords end at the same vertex. The outer chord closes a quadrilateral
-- and the inner one closes a triangle.
example : let D : Finset (ℕ × ℕ) := {(1, 5), (3, 5)}
    dissectionFaceSize D (1, 5) = 4 ∧ dissectionFaceSize D (3, 5) = 3 := by
  decide +kernel

-- At both endpoints k = 1 and k = n, the identity applies to arbitrary colorings.
example (γ : ℕ → ℕ) :
    (4 + 1).choose 1 * coloredDyckPathCount γ 4 1 =
      (4 + 1).choose 1 * coloredPolygonDissectionCount γ 4 1 :=
  choose_mul_coloredDyckPathCount_eq γ (by decide) (by decide)

example (γ : ℕ → ℕ) :
    (4 + 4).choose 4 * coloredDyckPathCount γ 4 4 =
      (4 + 1).choose 4 * coloredPolygonDissectionCount γ 4 4 :=
  choose_mul_coloredDyckPathCount_eq γ (by decide) (by decide)

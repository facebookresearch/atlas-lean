/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsFifthSpatialMatrix

/-! Ungated complete physical Root02 spatial word P, distinct from axis M and E7 T. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix
set_option backward.isDefEq.respectTransparency false

/-- All576 physical entries retain the literal original column order. -/
def generatedTenthSourceSpatialWordLiteralNumerator : Matrix (Fin 24) (Fin 24) ℤ :=
  ![
    ![-1, -1, -1, -1, 2, 0, 0, 0, 1, -1, 0, 0, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1],
    ![0, 0, 0, 0, 1, -1, -1, -1, -2, 0, 1, 1, -1, -1, 0, 0, -1, -1, 0, 0, -1, -1, 0, 0],
    ![0, 0, 0, 0, 1, -1, -1, -1, 0, 2, 1, 1, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0],
    ![1, -1, -1, 1, 0, 0, -2, 0, 1, -1, 0, 0, 0, 0, -1, -1, 0, 0, -1, -1, 0, 0, 1, 1],
    ![-1, 1, 1, 1, 0, 0, 0, 0, 1, -1, 2, 0, 0, 0, -1, 1, 0, 0, -1, 1, 0, 0, -1, 1],
    ![-1, 1, -1, 1, 0, 0, 0, 2, -1, 1, 0, 0, 0, 0, 1, 1, 0, 0, -1, -1, 0, 0, 1, 1],
    ![-1, -1, 1, 1, 0, 2, 0, 0, -1, 1, 0, 0, 0, 0, -1, -1, 0, 0, 1, 1, 0, 0, 1, 1],
    ![-1, 1, 1, 1, 0, 0, 0, 0, 1, -1, 0, 2, 0, 0, 1, -1, 0, 0, 1, -1, 0, 0, 1, -1],
    ![0, 0, 0, 0, 1, 1, -1, 1, 0, 0, 1, -1, 1, 1, 0, 0, -1, -1, 0, 0, -1, 1, 0, -2],
    ![0, 0, -2, 0, -1, 1, 1, -1, 0, 0, 1, 1, -1, 1, 0, 0, 1, -1, 0, 0, -1, 1, 0, 0],
    ![0, -2, 0, 0, -1, -1, 1, 1, 0, 0, 1, 1, 1, -1, 0, 0, -1, 1, 0, 0, -1, 1, 0, 0],
    ![0, 0, 0, 0, 1, 1, -1, 1, 0, 0, -1, 1, -1, -1, 0, 0, 1, 1, 0, 0, -1, 1, -2, 0],
    ![0, 0, 0, -2, -1, 1, -1, 1, 0, 0, 1, 1, -1, 1, 0, 0, -1, 1, 0, 0, 1, -1, 0, 0],
    ![1, 1, 1, -1, 0, 0, 0, 0, -1, -1, 0, 0, 0, 0, 1, -1, 0, 0, -1, 1, 0, 2, 1, 1],
    ![1, 1, 1, -1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, -1, 1, 0, 0, 1, -1, -2, 0, 1, 1],
    ![2, 0, 0, 0, 1, 1, 1, 1, 0, 0, 1, 1, 1, -1, 0, 0, 1, -1, 0, 0, 1, -1, 0, 0],
    ![0, 0, 0, 0, -1, 1, -1, -1, 0, 0, 1, -1, 1, -1, 2, 0, 1, 1, 0, 0, -1, -1, 0, 0],
    ![1, 1, -1, 1, 0, 0, 0, 0, -1, -1, 0, 0, 0, 0, -1, 1, 0, 2, 1, 1, 0, 0, 1, -1],
    ![0, 0, 0, 0, 1, 1, 1, -1, 0, 0, 1, -1, -1, -1, 0, 0, -1, 1, 0, -2, 1, 1, 0, 0],
    ![-1, 1, -1, -1, 0, 0, 0, 0, 1, 1, 0, 0, 0, -2, -1, -1, 0, 0, -1, 1, 0, 0, 1, -1],
    ![0, 0, 0, 0, -1, -1, -1, 1, 0, 0, 1, -1, -1, -1, 0, 0, 1, -1, 2, 0, 1, 1, 0, 0],
    ![0, 0, 0, 0, 1, -1, 1, 1, 0, 0, 1, -1, -1, 1, 0, -2, 1, 1, 0, 0, -1, -1, 0, 0],
    ![1, -1, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, -2, 0, 1, 1, 0, 0, -1, 1, 0, 0, 1, -1],
    ![-1, -1, 1, -1, 0, 0, 0, 0, -1, -1, 0, 0, 0, 0, -1, 1, 2, 0, -1, -1, 0, 0, 1, -1]
  ]

/-- Exact common denominator of the original complete physical word. -/
def generatedTenthSourceSpatialWordLiteralDenominator : ℕ := 4

/-- This literal is P, the physical source map used once in tensor transport. -/
def generatedTenthSourceSpatialWordLiteral : Matrix (Fin 24) (Fin 24) ℚ :=
  fun i j => (generatedTenthSourceSpatialWordLiteralNumerator i j : ℚ) /
    generatedTenthSourceSpatialWordLiteralDenominator

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

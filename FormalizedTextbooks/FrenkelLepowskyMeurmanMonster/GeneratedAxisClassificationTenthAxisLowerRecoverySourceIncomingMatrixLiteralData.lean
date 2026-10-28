/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoverySourceIncomingMatrixGeneric

/-! Ungated complete literal original Root02 rational matrix source cache. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix
set_option backward.isDefEq.respectTransparency false

/-- All576 original incoming matrix numerators are retained in their physical column order. -/
def generatedTenthSourceIncomingMatrixLiteralNumerator : Matrix (Fin 24) (Fin 24) ℤ :=
  ![
    ![11, 0, 0, -1, -1, -1, 1, -1, 0, 1, 1, 0, 1, -1, -1, -1, 0, 0, -1, 1, 1, 0, -1, 0],
    ![0, 9, -1, 0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0, -1, -1, 0, 0, 0, -1, 0, -1],
    ![0, -1, 9, 0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 1, 0, 1],
    ![-1, 0, 0, 11, -1, 1, -1, -1, 0, 1, 1, 0, -1, -1, -1, 1, 0, 0, 1, -1, -1, 0, 1, 0],
    ![-1, 0, 0, -1, 11, 1, 1, 1, 0, -1, -1, 0, -1, 1, -1, -1, 0, 0, -1, 1, -1, 0, 1, 0],
    ![-1, 0, 0, 1, 1, 11, -1, 1, 0, 1, -1, 0, -1, -1, -1, -1, 0, 0, 1, 1, -1, 0, -1, 0],
    ![1, 0, 0, -1, 1, -1, 11, 1, 0, -1, 1, 0, -1, -1, -1, -1, 0, 0, -1, -1, 1, 0, 1, 0],
    ![-1, 0, 0, -1, 1, 1, 1, 11, 0, -1, -1, 0, -1, -1, 1, -1, 0, 0, 1, -1, 1, 0, -1, 0],
    ![0, 1, -1, 0, 0, 0, 0, 0, 9, 0, 0, -1, 0, 0, 0, 0, -1, -1, 0, 0, 0, -1, 0, -1],
    ![1, 0, 0, 1, -1, 1, -1, -1, 0, 11, -1, 0, -1, -1, -1, 1, 0, 0, -1, 1, 1, 0, -1, 0],
    ![1, 0, 0, 1, -1, -1, 1, -1, 0, -1, 11, 0, 1, -1, -1, -1, 0, 0, 1, -1, -1, 0, 1, 0],
    ![0, -1, 1, 0, 0, 0, 0, 0, -1, 0, 0, 9, 0, 0, 0, 0, 1, 1, 0, 0, 0, 1, 0, 1],
    ![1, 0, 0, -1, -1, -1, -1, -1, 0, -1, 1, 0, 11, 1, 1, -1, 0, 0, 1, 1, -1, 0, -1, 0],
    ![-1, 0, 0, -1, 1, -1, -1, -1, 0, -1, -1, 0, 1, 11, 1, 1, 0, 0, -1, 1, -1, 0, 1, 0],
    ![-1, 0, 0, -1, -1, -1, -1, 1, 0, -1, -1, 0, 1, 1, 11, 1, 0, 0, 1, -1, 1, 0, -1, 0],
    ![-1, 0, 0, 1, -1, -1, -1, -1, 0, 1, -1, 0, -1, 1, 1, 11, 0, 0, -1, -1, 1, 0, 1, 0],
    ![0, -1, 1, 0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0, 9, 1, 0, 0, 0, 1, 0, 1],
    ![0, -1, 1, 0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0, 1, 13, 0, 0, 0, 1, 0, -3],
    ![-1, 0, 0, 1, -1, 1, -1, 1, 0, -1, 1, 0, 1, -1, 1, -1, 0, 0, 11, -1, -1, 0, -1, 0],
    ![1, 0, 0, -1, 1, 1, -1, -1, 0, 1, -1, 0, 1, 1, -1, -1, 0, 0, -1, 11, -1, 0, -1, 0],
    ![1, 0, 0, -1, -1, -1, 1, 1, 0, 1, -1, 0, -1, -1, 1, 1, 0, 0, -1, -1, 11, 0, -1, 0],
    ![0, -1, 1, 0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 9, 0, 1],
    ![-1, 0, 0, 1, 1, -1, 1, -1, 0, -1, 1, 0, -1, 1, -1, 1, 0, 0, -1, -1, -1, 0, 11, 0],
    ![0, -1, 1, 0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0, 1, -3, 0, 0, 0, 1, 0, 13]
  ]

/-- The exact common rational denominator of the complete original incoming matrix cache. -/
def generatedTenthSourceIncomingMatrixLiteralDenominator : ℕ := 32

/-- Complete literal rational source matrix; source equality is supplied separately. -/
def generatedTenthSourceIncomingMatrixLiteral : Matrix (Fin 24) (Fin 24) ℚ :=
  fun i j => (generatedTenthSourceIncomingMatrixLiteralNumerator i j : ℚ) /
    generatedTenthSourceIncomingMatrixLiteralDenominator

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

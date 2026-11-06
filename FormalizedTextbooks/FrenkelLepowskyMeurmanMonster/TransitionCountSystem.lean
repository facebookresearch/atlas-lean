/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
The anchored linear counting system used in Höhn–Seysen,
arXiv:2508.01037v1, §§3.1 and 4. Replace one stationary equation by the
known orbit size. An explicit left inverse then proves uniqueness without
an additional Perron–Frobenius argument.
-/
module

public import Mathlib.LinearAlgebra.Matrix.RowCol
public import Mathlib.Data.Rat.Defs

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Matrix

/-- Anchor the first coordinate while retaining the other balance equations. -/
def transitionCountSystem {n : ℕ}
    (M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ) (d : ℚ) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ :=
  (M - d • 1).updateRow 0 ((1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ) 0)

/-- A stationary vector maps to the vector containing only its anchor. -/
theorem transitionCountSystem_mulVec {n : ℕ}
    (M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ) (d : ℚ)
    (v : Fin (n + 1) → ℚ) (hv : M *ᵥ v = d • v) :
    transitionCountSystem M d *ᵥ v = Pi.single 0 (v 0) := by
  have hrow : ((1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ) 0) ⬝ᵥ v = v 0 :=
    congrFun (Matrix.one_mulVec v) 0
  rw [transitionCountSystem, Matrix.updateRow_mulVec, Matrix.sub_mulVec,
    Matrix.smul_mulVec, Matrix.one_mulVec, hv, sub_self, hrow]
  rfl

/-- A checked left inverse makes the stationary vector unique once the first
orbit size is fixed. All mathematical inputs are explicit. -/
theorem transition_count_unique {n : ℕ}
    (M R : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ) (d : ℚ)
    (hR : R * transitionCountSystem M d = 1)
    (v w : Fin (n + 1) → ℚ) (hv : M *ᵥ v = d • v)
    (hw : M *ᵥ w = d • w) (hanchor : v 0 = w 0) : v = w := by
  have hA : transitionCountSystem M d *ᵥ v = transitionCountSystem M d *ᵥ w := by
    rw [transitionCountSystem_mulVec M d v hv, transitionCountSystem_mulVec M d w hw,
      hanchor]
  have h := congrArg (fun u => R *ᵥ u) hA
  simpa only [Matrix.mulVec_mulVec, hR, Matrix.one_mulVec] using h

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

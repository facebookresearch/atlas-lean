/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationOctadIntegralSpanData
public import Mathlib.Tactic.Ring

/-! The intrinsic E8 quadratic form on eight root coordinates. Its normalization
is integer square sum divided by 32, not the ambient Leech half-norm form. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators Matrix
set_option backward.isDefEq.respectTransparency false

/-- The integral Gram matrix divided by sixteen for the actual eight-root basis. -/
def generatedAxisE8FrameGram : Matrix (Fin 8) (Fin 8) ℤ :=
  ![![2, 1, 1, 1, 1, 1, 0, 0],
    ![1, 2, 1, 1, 1, 1, 1, 0],
    ![1, 1, 2, 1, 1, 1, 1, 0],
    ![1, 1, 1, 2, 1, 1, 1, 0],
    ![1, 1, 1, 1, 2, 1, 1, 0],
    ![1, 1, 1, 1, 1, 2, 1, 0],
    ![0, 1, 1, 1, 1, 1, 2, 1],
    ![0, 0, 0, 0, 0, 0, 1, 2]]

/-- The quadratic integer polynomial whose multiple by 32 is the physical square sum. -/
def generatedAxisE8FrameIntegerQuadratic (a : Fin 8 → ℤ) : ℤ :=
  (∑ i, a i ^ 2) + ∑ i, ∑ j, if i < j then
    generatedAxisE8FrameGram i j * a i * a j else 0

/-- The intrinsic binary quadratic form distinguishes root classes from norm-eight classes. -/
def generatedAxisE8FrameQuadratic (a : Fin 8 → ZMod 2) : ZMod 2 :=
  (∑ i, a i) + ∑ i, ∑ j, if i < j then
    (generatedAxisE8FrameGram i j : ZMod 2) * a i * a j else 0

/-- Exact Gram normalization of the actual eight integer roots. -/
theorem generatedAxisE8FrameGram_certificate :
    generatedOctadIntegerRootMatrix.transpose * generatedOctadIntegerRootMatrix =
      16 • generatedAxisE8FrameGram := by
  decide +kernel

set_option maxHeartbeats 2000000 in
-- Eight coordinates and a homogeneous polynomial of degree two are expanded here.
/-- Integer norm and the intrinsic E8 quadratic polynomial agree with the exact scaling. -/
theorem generatedAxisE8FrameIntegerQuadratic_norm (a : Fin 8 → ℤ) :
    (∑ i, (generatedOctadIntegerRootMatrix *ᵥ a) i ^ 2) =
      32 * generatedAxisE8FrameIntegerQuadratic a := by
  simp [generatedOctadIntegerRootMatrix, generatedAxisE8FrameIntegerQuadratic,
    generatedAxisE8FrameGram, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  ring

/-- Reducing root coordinates modulo two reduces the intrinsic integer polynomial. -/
theorem generatedAxisE8FrameQuadratic_cast (a : Fin 8 → ℤ) :
    generatedAxisE8FrameQuadratic (fun i => (a i : ZMod 2)) =
      (generatedAxisE8FrameIntegerQuadratic a : ZMod 2) := by
  have hs : ∀ x : ZMod 2, x ^ 2 = x := by decide +kernel
  simp [generatedAxisE8FrameQuadratic, generatedAxisE8FrameIntegerQuadratic, hs]

/-- Actual norm-eight vectors have singular intrinsic E8 coordinates. -/
theorem generatedAxisE8FrameQuadratic_norm_eight (a : Fin 8 → ℤ)
    (ha : (∑ i, (generatedOctadIntegerRootMatrix *ᵥ a) i ^ 2) = 64) :
    generatedAxisE8FrameQuadratic (fun i => (a i : ZMod 2)) = 0 := by
  have he := generatedAxisE8FrameIntegerQuadratic_norm a
  have hq : generatedAxisE8FrameIntegerQuadratic a = 2 := by omega
  rw [generatedAxisE8FrameQuadratic_cast, hq]
  rfl

/-- Actual minimal root vectors have nonsingular intrinsic E8 coordinates. -/
theorem generatedAxisE8FrameQuadratic_root (a : Fin 8 → ℤ)
    (ha : (∑ i, (generatedOctadIntegerRootMatrix *ᵥ a) i ^ 2) = 32) :
    generatedAxisE8FrameQuadratic (fun i => (a i : ZMod 2)) = 1 := by
  have he := generatedAxisE8FrameIntegerQuadratic_norm a
  have hq : generatedAxisE8FrameIntegerQuadratic a = 1 := by omega
  rw [generatedAxisE8FrameQuadratic_cast, hq]
  rfl

set_option maxHeartbeats 200000000 in
-- Only the 256 binary root-coordinate vectors are enumerated.
set_option maxRecDepth 10000 in
-- Their finite-function enumeration requires deeper reduction.
/-- The intrinsic eight-dimensional E8 form has exactly 135 nonzero singular vectors. -/
theorem generatedAxisE8FrameQuadratic_nonzero_card :
    Nat.card {a : Fin 8 → ZMod 2 // a ≠ 0 ∧ generatedAxisE8FrameQuadratic a = 0} = 135 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

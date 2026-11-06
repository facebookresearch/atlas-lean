/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Exact integer digests of actual finite source root sets under invertible matrix actions. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationOrthogonal3RootsAction
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix Pointwise

/-- The exact base-three encoding of an actual seven-dimensional finite field vector. -/
def y322Orthogonal3VectorCode (v : Fin 7 → ZMod 3) : ℕ :=
  ∑ r : Fin 7, (v r).val * 3 ^ r.val

/-- An integer digest computed from the actual members of a finite seven-dimensional column set. -/
def y322Orthogonal3RootDigest (roots : Finset (Matrix (Fin 7) Unit (ZMod 3))) : ℕ :=
  ∑ v ∈ roots, 2 ^ y322Orthogonal3VectorCode (fun r => v r ())

/-- The exact integer digest sum on the 126 original source columns after a given matrix. -/
def y322Orthogonal3MatrixRootDigest (matrix : Matrix (Fin 7) (Fin 7) (ZMod 3)) : ℕ :=
  ∑ i : Fin 126, 2 ^ y322Orthogonal3VectorCode
    (matrix *ᵥ y322Orthogonal3E7RootCoordinates i)

/-- Exact finite integer digits are assembled without trusting an external numerical assertion. -/
def y322Orthogonal3IntegerDigits (digits : List ℕ) : ℕ :=
  digits.foldr (fun digit acc => digit + 2 ^ 64 * acc) 0

/-- The digest of an actual transported root set is the sum on its 126 actual source columns. -/
theorem y322Orthogonal3RootDigest_action
    (g : Matrix.GeneralLinearGroup (Fin 7) (ZMod 3)) :
    y322Orthogonal3RootDigest (g • y322Orthogonal3E7Roots) =
      ∑ i : Fin 126, 2 ^ y322Orthogonal3VectorCode
        (g.val *ᵥ y322Orthogonal3E7RootCoordinates i) := by
  unfold y322Orthogonal3RootDigest
  rw [y322Orthogonal3E7Roots, Finset.smul_finset_def, Finset.image_image, Finset.sum_image]
  · rfl
  · intro i _ j _ hij
    apply y322Orthogonal3E7RootMatrix_injective
    have h := congrArg (fun x : Matrix (Fin 7) Unit (ZMod 3) => g⁻¹ • x) hij
    simpa only [Function.comp_apply, inv_smul_smul] using h

/-- The actual transported source root set has exactly the finite matrix digest sum. -/
theorem y322Orthogonal3RootDigest_action_matrix
    (g : Matrix.GeneralLinearGroup (Fin 7) (ZMod 3)) :
    y322Orthogonal3RootDigest (g • y322Orthogonal3E7Roots) =
      y322Orthogonal3MatrixRootDigest g.val :=
  y322Orthogonal3RootDigest_action g

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

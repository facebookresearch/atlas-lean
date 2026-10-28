/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Exact natural-arithmetic evaluation of the actual characteristic-three root-set digest. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationOrthogonal3RootDigestFast

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix

/-- The ordinary natural residue of a finite matrix-vector product is its exact coordinate value. -/
theorem y322Orthogonal3MulVec_val (matrix : Matrix (Fin 7) (Fin 7) (ZMod 3))
    (vector : Fin 7 → ZMod 3) (r : Fin 7) :
    ((matrix *ᵥ vector) r).val =
      (∑ c : Fin 7, (matrix r c).val * (vector c).val) % 3 := by
  have h : ((∑ c : Fin 7, (matrix r c).val * (vector c).val : ℕ) : ZMod 3) =
      (matrix *ᵥ vector) r := by
    rw [Nat.cast_sum]
    simp only [Nat.cast_mul, ZMod.natCast_zmod_val]
    rfl
  rw [← h, ZMod.val_natCast]

/-- The exact vector code after a finite source matrix, evaluated using natural residues. -/
def y322Orthogonal3MatrixVectorCodeNat (matrix : Matrix (Fin 7) (Fin 7) (ZMod 3))
    (vector : Fin 7 → ZMod 3) : ℕ :=
  ∑ r : Fin 7, ((∑ c : Fin 7, (matrix r c).val * (vector c).val) % 3) * 3 ^ r.val

/-- Natural residue arithmetic gives the exact original matrix-vector code. -/
theorem y322Orthogonal3MatrixVectorCodeNat_eq (matrix : Matrix (Fin 7) (Fin 7) (ZMod 3))
    (vector : Fin 7 → ZMod 3) :
    y322Orthogonal3MatrixVectorCodeNat matrix vector =
      y322Orthogonal3VectorCode (matrix *ᵥ vector) := by
  simp only [y322Orthogonal3MatrixVectorCodeNat, y322Orthogonal3VectorCode,
    y322Orthogonal3MulVec_val]

/-- Evaluate the full actual source root digest with exact natural arithmetic and binary powers. -/
def y322Orthogonal3MatrixRootDigestNat (matrix : Matrix (Fin 7) (Fin 7) (ZMod 3)) : ℕ :=
  ∑ i : Fin 126, y322ExactTwoPower (y322Orthogonal3MatrixVectorCodeNat
    matrix (y322Orthogonal3E7RootCoordinates i))

/-- The natural-arithmetic algorithm equals the original actual finite root-digest sum. -/
theorem y322Orthogonal3MatrixRootDigestNat_eq (matrix : Matrix (Fin 7) (Fin 7) (ZMod 3)) :
    y322Orthogonal3MatrixRootDigestNat matrix = y322Orthogonal3MatrixRootDigest matrix := by
  simp only [y322Orthogonal3MatrixRootDigestNat, y322Orthogonal3MatrixVectorCodeNat_eq,
    y322ExactTwoPower_eq, y322Orthogonal3MatrixRootDigest]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Concrete invariant coordinate codes for projective vectors over the field of three elements. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationC422Orthogonal3C322Data

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix

/-- Exact base-three encoding of an eight-dimensional field vector. -/
def y422Orthogonal3VectorCode (v : Fin 8 → ZMod 3) : ℕ :=
  ∑ j : Fin 8, (v j).val * 3 ^ j.val

/-- The smaller code of a vector and its negative represents its projective line. -/
def y422Orthogonal3ProjectiveVectorCode (v : Fin 8 → ZMod 3) : ℕ :=
  min (y422Orthogonal3VectorCode v) (y422Orthogonal3VectorCode (-v))

/-- Negation preserves the actual projective vector code. -/
theorem y422Orthogonal3ProjectiveVectorCode_neg (v : Fin 8 → ZMod 3) :
    y422Orthogonal3ProjectiveVectorCode (-v) = y422Orthogonal3ProjectiveVectorCode v := by
  simp only [y422Orthogonal3ProjectiveVectorCode, neg_neg, min_comm]

/-- All nonzero field scalars preserve the actual projective vector code. -/
theorem y422Orthogonal3ProjectiveVectorCode_scalar (u : (ZMod 3)ˣ)
    (v : Fin 8 → ZMod 3) :
    y422Orthogonal3ProjectiveVectorCode
      ((Matrix.GeneralLinearGroup.scalar (Fin 8) u).val *ᵥ v) =
      y422Orthogonal3ProjectiveVectorCode v := by
  have hu : u.val = 1 ∨ u.val = -1 := by
    revert u
    decide +kernel
  rcases hu with hu | hu
  · have hv : (Matrix.GeneralLinearGroup.scalar (Fin 8) u).val *ᵥ v = v := by
      ext j
      change (Matrix.diagonal (fun _ : Fin 8 => u.val) *ᵥ v) j = v j
      simp [hu]
    rw [hv]
  · have hv : (Matrix.GeneralLinearGroup.scalar (Fin 8) u).val *ᵥ v = -v := by
      ext j
      change (Matrix.diagonal (fun _ : Fin 8 => u.val) *ᵥ v) j = -v j
      simp [Matrix.mulVec_diagonal, hu]
    rw [hv, y422Orthogonal3ProjectiveVectorCode_neg]

/-- Equal actual projective matrices give equal projective vector codes on every vector. -/
theorem y422Orthogonal3ProjectiveVectorCode_of_projective_eq
    (A B : Matrix.GeneralLinearGroup (Fin 8) (ZMod 3))
    (h : Matrix.ProjGenLinGroup.mk A = Matrix.ProjGenLinGroup.mk B)
    (v : Fin 8 → ZMod 3) :
    y422Orthogonal3ProjectiveVectorCode (A.val *ᵥ v) =
      y422Orthogonal3ProjectiveVectorCode (B.val *ᵥ v) := by
  obtain ⟨u, hu⟩ := Matrix.ProjGenLinGroup.mk_eq_mk_iff.mp h
  rw [← hu, ← Matrix.GeneralLinearGroup.scalar_commute u A,
    Units.val_mul, ← Matrix.mulVec_mulVec]
  exact (y422Orthogonal3ProjectiveVectorCode_scalar u (A.val *ᵥ v)).symm

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Actual linear lifts and inverse-vector actions of the acyclic original C422 source paths. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationC422TPaths
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationC422Orthogonal3C322Data

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix

/-- The exact linear source-word lift selected by each original acyclic path program. -/
noncomputable def y422Orthogonal3TPathValue : Fin 9033 →
    Matrix.GeneralLinearGroup (Fin 8) (ZMod 3) :=
  y522WordProgramValue y422TPathProgram y422Orthogonal3Generator

/-- The empty source path has the actual identity linear lift. -/
theorem y422Orthogonal3TPathValue_zero : y422Orthogonal3TPathValue 0 = 1 := by
  rw [y422Orthogonal3TPathValue, y522WordProgramValue_eq]
  rw [show y422TPathProgram 0 = .one from rfl]
  rfl

/-- Each actual linear path appends its declared original source reflection. -/
theorem y422Orthogonal3TPathValue_step (i : Fin 9033) (hi : i ≠ 0) :
    y422Orthogonal3TPathValue i =
      y422Orthogonal3TPathValue
        ⟨(y422TPathData i).1, (y422TPathData_prior i hi).trans i.isLt⟩ *
      y422Orthogonal3Generator (y422TPathData i).2 := by
  rw [y422Orthogonal3TPathValue, y522WordProgramValue_eq]
  simp only [y422TPathProgram, dite_eq_right hi, y522InstructionValue]
  rfl

/-- Each selected linear path projects to its actual original source-group image. -/
theorem y422Orthogonal3TPathValue_projective (i : Fin 9033) :
    y422Orthogonal3ProjectiveHom (y422TPathValue i) =
      Matrix.ProjGenLinGroup.mk (y422Orthogonal3TPathValue i) := by
  unfold y422TPathValue y422Orthogonal3TPathValue
  rw [y522WordProgramValue_map, y522WordProgramValue_map]
  congr 1
  funext v
  exact y422Orthogonal3ProjectiveHom_generator v

/-- The actual inverse-action vector of a selected original source path. -/
noncomputable def y422Orthogonal3TPathVector (i : Fin 9033) : Fin 8 → ZMod 3 :=
  ((y422Orthogonal3TPathValue i)⁻¹).val *ᵥ y422Orthogonal3FixedVector

/-- The original empty path has the actual fixed vector as its inverse-action vector. -/
theorem y422Orthogonal3TPathVector_zero :
    y422Orthogonal3TPathVector 0 = y422Orthogonal3FixedVector := by
  rw [y422Orthogonal3TPathVector, y422Orthogonal3TPathValue_zero]
  simp

/-- Inverse source-path vectors obey the exact actual reflection recurrence. -/
theorem y422Orthogonal3TPathVector_step (i : Fin 9033) (hi : i ≠ 0) :
    y422Orthogonal3TPathVector i = y422Orthogonal3Reflection (y422TPathData i).2 *ᵥ
      y422Orthogonal3TPathVector
        ⟨(y422TPathData i).1, (y422TPathData_prior i hi).trans i.isLt⟩ := by
  rw [y422Orthogonal3TPathVector, y422Orthogonal3TPathValue_step i hi, mul_inv_rev,
    Units.val_mul, ← Matrix.mulVec_mulVec]
  rfl

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

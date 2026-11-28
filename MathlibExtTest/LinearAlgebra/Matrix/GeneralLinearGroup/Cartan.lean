/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.LinearAlgebra.Matrix.GeneralLinearGroup.Cartan

open Matrix Matrix.GeneralLinearGroup

#check @Matrix.IsCartanSubalgebra
#check @unitsOfSubalgebra
#check @mem_unitsOfSubalgebra
#check @IsCartanSubgroup
#check @IsSplitCartanSubgroup
#check @IsNonsplitCartanSubgroup
#check @splitCartan
#check @nonsplitCartan

-- `C_s` and `C_ns` contain the scalar matrices.
example (F : Type*) [Field F] (ε : F) (c : Fˣ) :
    Units.map (algebraMap F (Matrix (Fin 2) (Fin 2) F)).toMonoidHom c ∈ splitCartan F ⊓
      nonsplitCartan ε := by
  simp [mem_splitCartan, mem_nonsplitCartan, Matrix.algebraMap_matrix_apply]

-- The normalizer of a Cartan subgroup is Mathlib's `Subgroup.normalizer`.
example (F : Type*) [Field F] (T : Subgroup (GL (Fin 2) F)) (g : GL (Fin 2) F) :
    g ∈ Subgroup.normalizer (T : Set (GL (Fin 2) F)) ↔ ∀ h, h ∈ T ↔ g * h * g⁻¹ ∈ T :=
  Subgroup.mem_normalizer_iff

-- A subalgebra always contains `1`, so `1` lies in its group of units.
example (F : Type*) [Field F] (A : Subalgebra F (Matrix (Fin 2) (Fin 2) F)) :
    (1 : GL (Fin 2) F) ∈ unitsOfSubalgebra A :=
  (unitsOfSubalgebra A).one_mem

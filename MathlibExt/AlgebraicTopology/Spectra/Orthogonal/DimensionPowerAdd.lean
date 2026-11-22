/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.Spectra.Orthogonal.SpherePowerFunctor
public import MathlibExt.AlgebraicTopology.Spectra.Orthogonal.FiniteBijectionMatrix

/-!
# The actual dimension tensor-power add map

The native coordinate reassociation and empty-block unitors are equality maps
of dimensions. This identifies the standard source tensor-power add map with
its literal dimension equality, retaining all original structural matrices.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v

open CategoryTheory MonoidalCategory
open CategoryTheory.MonoidalCategory.TensorPower
open scoped MonoidalClosed

namespace CategoryTheory.Spectra

attribute [local instance] OrthogonalIndex.category OrthogonalIndex.monoidalCategory
attribute [local instance] OrthogonalIndex.enrichedOrdinaryCategory

private theorem finiteBijectionMatrix_eqToHom {m n : OrthogonalIndex} (h : m = n) :
    letI : Category.{v} OrthogonalIndex := OrthogonalIndex.category.{u, v}
    (OrthogonalIndex.matrixPoint.{u, v} (finiteBijectionMatrix (finCongr h)) : m ⟶ n) =
      eqToHom h := by
  let _ : Category.{v} OrthogonalIndex := OrthogonalIndex.category.{u, v}
  cases h
  have h := congrArg OrthogonalIndex.matrixPoint.{u, v} (finiteBijectionMatrix_refl m)
  exact h.trans (OrthogonalIndex.enrichedCategory_id.{u, v} m).symm

/-- The original native associator is the equality map of its actual dimension sum. -/
theorem orthogonalIndex_associator_eqToHom (m n p : OrthogonalIndex) :
    letI : Category.{v} OrthogonalIndex := OrthogonalIndex.category.{u, v}
    letI : MonoidalCategory OrthogonalIndex := OrthogonalIndex.monoidalCategory.{u, v}
    (α_ m n p).hom = eqToHom (Nat.add_assoc m n p) := by
  let _ : Category.{v} OrthogonalIndex := OrthogonalIndex.category.{u, v}
  let _ : MonoidalCategory OrthogonalIndex := OrthogonalIndex.monoidalCategory.{u, v}
  have h := finiteBijectionMatrix_eqToHom.{u, v} (Nat.add_assoc m n p)
  apply Eq.trans _ h
  change OrthogonalIndex.matrixPoint.{u, v} _ = OrthogonalIndex.matrixPoint.{u, v} _
  apply congrArg OrthogonalIndex.matrixPoint.{u, v}
  apply OrthogonalMatrixHom.ext
  ext i j
  rw [finiteBijectionMatrix_apply]
  change (if (finCongr (Nat.add_assoc m n p)).symm i = j then (1 : ℝ) else 0) =
    if i = finCongr (Nat.add_assoc m n p) j then 1 else 0
  simp only [Equiv.symm_apply_eq]

/-- The original native right unitor is the equality map deleting the empty block. -/
theorem orthogonalIndex_rightUnitor_eqToHom (m : OrthogonalIndex) :
    letI : Category.{v} OrthogonalIndex := OrthogonalIndex.category.{u, v}
    letI : MonoidalCategory OrthogonalIndex := OrthogonalIndex.monoidalCategory.{u, v}
    (ρ_ m).hom = eqToHom (Nat.add_zero m) := by
  let _ : Category.{v} OrthogonalIndex := OrthogonalIndex.category.{u, v}
  let _ : MonoidalCategory OrthogonalIndex := OrthogonalIndex.monoidalCategory.{u, v}
  have h := finiteBijectionMatrix_eqToHom.{u, v} (Nat.add_zero m)
  apply Eq.trans _ h
  change OrthogonalIndex.matrixPoint.{u, v} _ = OrthogonalIndex.matrixPoint.{u, v} _
  apply congrArg OrthogonalIndex.matrixPoint.{u, v}
  apply OrthogonalMatrixHom.ext
  ext i j
  rw [finiteBijectionMatrix_apply]
  change (if (finCongr (Nat.add_zero m)).symm i = j then (1 : ℝ) else 0) =
    if i = finCongr (Nat.add_zero m) j then 1 else 0
  simp only [Equiv.symm_apply_eq]

/-- The full source power add map is the equality map of its actual dimension sum. -/
theorem orthogonalDimensionPower_addMap (m n : ℕ) :
    letI : Category.{v} OrthogonalIndex := OrthogonalIndex.category.{u, v}
    letI : MonoidalCategory OrthogonalIndex := OrthogonalIndex.monoidalCategory.{u, v}
    (tensorPowObj_add (1 : OrthogonalIndex) m n).hom =
      eqToHom (show tensorPowObj (1 : OrthogonalIndex) (m + n) =
        tensorPowObj (1 : OrthogonalIndex) m ⊗ tensorPowObj (1 : OrthogonalIndex) n from
          (orthogonalDimensionPower.{v, u} (m + n)).trans
            (congrArg₂ (fun a b : OrthogonalIndex => a + b)
              (orthogonalDimensionPower.{v, u} m).symm
              (orthogonalDimensionPower.{v, u} n).symm)) := by
  let _ : Category.{v} OrthogonalIndex := OrthogonalIndex.category.{u, v}
  let _ : MonoidalCategory OrthogonalIndex := OrthogonalIndex.monoidalCategory.{u, v}
  induction n with
  | zero =>
      apply (cancel_mono (ρ_ (tensorPowObj (1 : OrthogonalIndex) m)).hom).1
      change (ρ_ (tensorPowObj (1 : OrthogonalIndex) m)).inv ≫ _ = _
      rw [Iso.inv_hom_id, orthogonalIndex_rightUnitor_eqToHom]
      change 𝟙 (tensorPowObj (1 : OrthogonalIndex) m) =
        eqToHom (show tensorPowObj (1 : OrthogonalIndex) m =
          tensorPowObj (1 : OrthogonalIndex) m + 0 from (Nat.add_zero _).symm) ≫
          eqToHom (Nat.add_zero _)
      rw [eqToHom_trans]
      rfl
  | succ n h =>
      change ((tensorPowObj_add (1 : OrthogonalIndex) m n).hom ▷ (1 : OrthogonalIndex)) ≫
        (α_ (tensorPowObj (1 : OrthogonalIndex) m)
          (tensorPowObj (1 : OrthogonalIndex) n) (1 : OrthogonalIndex)).hom = _
      rw [h, orthogonalIndex_associator_eqToHom, eqToHom_whiskerRight, eqToHom_trans]
      rfl

end CategoryTheory.Spectra

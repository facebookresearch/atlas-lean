/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.Algebra.Homology.DGCyclicBarModels

/-!
# Tests for cyclic bar models of DG algebras

The last Hochschild face first rotates and then multiplies, the other faces multiply consecutive
factors, and in degree zero inserting the unit after the first factor and then multiplying the first
two factors is the identity (the simplicial identity `d₀ s₀ = id`). The rotation of a model and its
last face are computed from the native tensor rotation. `DGAlgebra` is also available in the
cyclic-bar namespace.
-/

namespace MathlibExtTest.DGCyclicBarModels

open CategoryTheory MonoidalCategory Opposite
open MathlibExt.CategoryTheory.DGModelContracts
open MathlibExt.Algebra.Homology MathlibExt.Algebra.Homology.DGCyclicBarModels

variable {k : Type} [CommRing k] (A : DGAlgebra k)

example : MathlibExt.Algebra.Homology.DGCyclicBarModels.DGAlgebra k = DGAlgebra k := rfl

example (X : Cochains k) : tensorPower X 2 = X ⊗ (X ⊗ 𝟙_ (Cochains k)) := rfl

example (n : ℕ) :
    barFace A n (Fin.last (n + 1)) = (cyclicRotation A.X (n + 1)).hom ≫ internalFace A n 0 := by
  simp [barFace]

example (n : ℕ) (j : Fin (n + 1)) : barFace A n j.castSucc = internalFace A n j := by
  simp [barFace]

theorem degeneracy_zero_comp_face_zero :
    barDegeneracy A 0 0 ≫ barFace A 0 (Fin.castSucc 0) = 𝟙 _ := by
  simp only [barFace, Fin.lastCases_castSucc, barDegeneracy, internalFace, tensorPower,
    tensorHom_id, id_tensorHom, MonoidalCategory.whiskerLeft_comp, Category.assoc]
  rw [associator_inv_naturality_middle_assoc, ← comp_whiskerRight, MonObj.mul_one]
  monoidal

example (B : CyclicBarModel A) (n : ℕ) :
    (modelRotation B n).hom = (B.termIso n).hom ≫ (cyclicRotation A.X n).hom ≫ (B.termIso n).inv :=
  rfl

example (B : CyclicBarModel A) (n : ℕ) :
    B.simplicial.δ (Fin.last (n + 1)) ≫ (B.termIso n).hom =
      (B.termIso (n + 1)).hom ≫ (cyclicRotation A.X (n + 1)).hom ≫ internalFace A n 0 := by
  rw [B.face_eq]
  simp [barFace]

example : IsNonnegativelyGraded A ↔ ∀ i : ℤ, i < 0 → Limits.IsZero (A.X.X i) := Iff.rfl

end MathlibExtTest.DGCyclicBarModels

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.TensorGeneratedMonodromy

@[expose] public noncomputable section

namespace MathlibExtTest.CategoryTheory.TensorGeneratedMonodromy

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory
open MathlibExt.CategoryTheory.TensorGeneratedMonodromy

universe u v

variable (k : Type u) [Field k] (Γ : Type v) [Group Γ] (r : ℕ)
  (ρ : Γ →* Matrix.GeneralLinearGroup (Fin r) k)

/-! ### The generating representation and the generated category -/

-- The displayed matrices act on column vectors by matrix-vector multiplication.
example (γ : Γ) (v : Fin r → k) :
    matrixRepresentation k Γ r ρ γ v = (ρ γ : Matrix (Fin r) (Fin r) k).mulVec v := by
  simp [matrixRepresentation]

-- The category contains tensor products and duals of the generator.
example : Generated k Γ r ρ
    (generatorRepresentation k Γ r ρ ⊗ generatorRepresentation k Γ r ρ) :=
  .tensor .generator .generator

example : Generated k Γ r ρ (FDRep.of (Representation.dual (generatorRepresentation k Γ r ρ).ρ)) :=
  .dual .generator

-- The fibre functor is faithful and monoidal, and its scalar extensions are monoidal.
example : (fibre k Γ r ρ).Faithful := inferInstance

example : (fibre k Γ r ρ).Monoidal := inferInstance

example (S : Type u) [CommRing S] [Algebra k S] : (scalarFibre k Γ r ρ S).Monoidal :=
  inferInstance

/-! ### The affine model inside `GL_r` -/

-- Every invertible matrix satisfies the determinant-inverse relation.
example (S : Type u) [CommRing S] [Algebra k S] (g : Matrix.GeneralLinearGroup (Fin r) S) :
    MvPolynomial.eval₂ (algebraMap k S) (glCoordinates r g) (determinantInverseRelation k r) = 0 :=
  eval₂_determinantInverseRelation k r g

-- The relation belongs to the defining ideal.
example : determinantInverseRelation k r ∈ definingIdeal k Γ r ρ :=
  Submodule.mem_sup_left (Ideal.subset_span rfl)

-- The displayed image points are `k`-points of the model.
example (γ : Γ) : IsMonodromyPoint k Γ r ρ k (ρ γ) := by
  simpa [Matrix.GeneralLinearGroup.map_id] using isMonodromyPoint_image k Γ r ρ k γ

-- Boundary case: for the trivial representation the identity is a point over every algebra.
example (S : Type u) [CommRing S] [Algebra k S] : IsMonodromyPoint k Γ r 1 S 1 := by
  simpa using isMonodromyPoint_image k Γ r 1 S 1

-- Boundary case: with `r = 0` the relation is `u - 1`, and `GL_0` has the single point `1`.
example : determinantInverseRelation k 0 = MvPolynomial.X (Sum.inr ()) - 1 := by
  simp [determinantInverseRelation]

example (S : Type u) [CommRing S] [Algebra k S] (g : Matrix.GeneralLinearGroup (Fin 0) S) :
    g = 1 :=
  Subsingleton.elim _ _

end MathlibExtTest.CategoryTheory.TensorGeneratedMonodromy

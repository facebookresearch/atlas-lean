/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  MathlibExt.AlgebraicTopology.LocalCoefficient.NervePullbackBarFaceDegeneraciesGt
public import
  MathlibExt.AlgebraicTopology.LocalCoefficient.NervePullbackBarDegeneracies
public import MathlibExt.AlgebraicTopology.SimplicialObject.ToSimplicial
public import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex

/-!
# Simplicial and chain assembly for the nerve-pullback coefficient bar

The six previously proved identities package the degree objects, faces, and
degeneracies of the nerve-pullback coefficient bar as `SimplicialObject.Data`
and then as a genuine simplicial object. In a preadditive target, its first
chain-level construction is the unnormalized alternating-face complex.

This file makes no identity-nerve comparison, normalized-chain, homology,
fundamental-groupoid-unit, topological, CGWH, or plus-construction claim.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits Opposite
open scoped Simplicial

universe vG uG vA uA

namespace CategoryTheory.CategoryHomology

variable {G : Type uG} [Category.{vG} G]
variable {A : Type uA} [Category.{vA} A]
variable {X : SSet.{max uG vG}}
variable (φ : X ⟶ CategoryTheory.nerve G) (M : G ⥤ A)
variable [HasCoproducts.{max uG vG} A]

/-- Simplicial data of the coefficient bar restricted along a nerve map. -/
noncomputable def nervePullbackCoefficientData : SimplicialObject.Data A where
  obj := nervePullbackCoefficientObj φ M
  δ := nervePullbackCoefficientFace φ M
  σ := nervePullbackCoefficientDegeneracy φ M
  δ_comp_δ h := nervePullbackCoefficientFace_comp_face φ M _ _ h
  δ_comp_σ_of_le h :=
    nervePullbackCoefficient_face_degeneracy_of_le φ M _ _ h
  δ_comp_σ_self := nervePullbackCoefficient_face_degeneracy_self φ M _
  δ_comp_σ_succ := nervePullbackCoefficient_face_degeneracy_succ φ M _
  δ_comp_σ_of_gt h :=
    nervePullbackCoefficient_face_degeneracy_of_gt φ M _ _ h
  σ_comp_σ h :=
    nervePullbackCoefficientDegeneracy_comp_degeneracy φ M _ _ h

@[simp]
theorem nervePullbackCoefficientData_obj (n : ℕ) :
    (nervePullbackCoefficientData φ M).obj n =
      nervePullbackCoefficientObj φ M n := rfl

@[simp]
theorem nervePullbackCoefficientData_δ {n : ℕ} (i : Fin (n + 2)) :
    (nervePullbackCoefficientData φ M).δ i =
      nervePullbackCoefficientFace φ M i := rfl

@[simp]
theorem nervePullbackCoefficientData_σ {n : ℕ} (i : Fin (n + 1)) :
    (nervePullbackCoefficientData φ M).σ i =
      nervePullbackCoefficientDegeneracy φ M i := rfl

/-- Genuine simplicial object of the coefficient bar restricted along a
nerve map. -/
noncomputable def nervePullbackCoefficientSimplicial : SimplicialObject A :=
  (nervePullbackCoefficientData φ M).toSimplicialObject

@[simp]
theorem nervePullbackCoefficientSimplicial_obj (n : ℕ) :
    (nervePullbackCoefficientSimplicial φ M).obj
        (op (SimplexCategory.mk n)) =
      nervePullbackCoefficientObj φ M n :=
  SimplicialObject.Data.toSimplicialObject_obj_mk
    (nervePullbackCoefficientData φ M) n

@[simp]
theorem nervePullbackCoefficientSimplicial_map_δ
    {n : ℕ} (i : Fin (n + 2)) :
    (nervePullbackCoefficientSimplicial φ M).map
        (SimplexCategory.δ i).op =
      nervePullbackCoefficientFace φ M i :=
  SimplicialObject.Data.toSimplicialObject_map_δ
    (nervePullbackCoefficientData φ M) i

@[simp]
theorem nervePullbackCoefficientSimplicial_map_σ
    {n : ℕ} (i : Fin (n + 1)) :
    (nervePullbackCoefficientSimplicial φ M).map
        (SimplexCategory.σ i).op =
      nervePullbackCoefficientDegeneracy φ M i :=
  SimplicialObject.Data.toSimplicialObject_map_σ
    (nervePullbackCoefficientData φ M) i

section Preadditive

variable [Preadditive A]

/-- Unnormalized alternating-face complex of the nerve-pullback coefficient
bar. -/
noncomputable def nervePullbackCoefficientComplex : ChainComplex A ℕ :=
  (AlgebraicTopology.alternatingFaceMapComplex A).obj
    (nervePullbackCoefficientSimplicial φ M)

@[simp]
theorem nervePullbackCoefficientComplex_X (n : ℕ) :
    (nervePullbackCoefficientComplex φ M).X n =
      nervePullbackCoefficientObj φ M n := rfl

/-- The differential is the alternating sum of the restricted face maps. -/
theorem nervePullbackCoefficientComplex_d (n : ℕ) :
    (nervePullbackCoefficientComplex φ M).d (n + 1) n =
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) •
        nervePullbackCoefficientFace φ M i := by
  change (AlgebraicTopology.AlternatingFaceMapComplex.obj
      (nervePullbackCoefficientSimplicial φ M)).d (n + 1) n = _
  rw [AlgebraicTopology.AlternatingFaceMapComplex.obj_d_eq]
  apply Finset.sum_congr rfl
  intro i _
  rw [show (nervePullbackCoefficientSimplicial φ M).δ i =
      nervePullbackCoefficientFace φ M i from
    SimplicialObject.Data.toSimplicialObject_map_δ
      (nervePullbackCoefficientData φ M) i]
  rfl

end Preadditive

end CategoryTheory.CategoryHomology

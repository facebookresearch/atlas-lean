/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import MathlibExt.CategoryTheory.CategoryHomology.BarFaceDegeneracies
public import MathlibExt.AlgebraicTopology.SimplicialObject.ToSimplicial
public import Mathlib.AlgebraicTopology.DoldKan.Normalized

/-!
# Simplicial coefficient bars and category homology

The coefficient bar face and degeneracy maps satisfy the simplicial
identities and form a simplicial object. Alternating faces and normalized
Moore chains give its chain complexes. For an abelian coefficient category,
category homology with coefficients is the homology of the normalized bar
complex.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.CategoryHomology

variable {C : Type u₁} [Category.{v₁} C]
  {A : Type u₂} [Category.{v₂} A]
  [HasCoproducts.{max u₁ v₁} A]
  (M : CategoryTheory.Functor C A)

/-- Simplicial data of the category bar with covariant coefficients. -/
noncomputable def coefficientBarData : SimplicialObject.Data A where
  obj := coefficientBarObj M
  δ := coefficientBarFace M
  σ := coefficientBarDegeneracy M
  δ_comp_δ h := coefficientBarFace_comp_face M _ _ h
  δ_comp_σ_of_le h := coefficientBar_face_degeneracy_of_le M _ _ h
  δ_comp_σ_self := coefficientBar_face_degeneracy_self M _
  δ_comp_σ_succ := coefficientBar_face_degeneracy_succ M _
  δ_comp_σ_of_gt h := coefficientBar_face_degeneracy_of_gt M _ _ h
  σ_comp_σ h := coefficientBarDegeneracy_comp_degeneracy M _ _ h

/-- Simplicial category bar with covariant coefficients. -/
noncomputable def coefficientBarSimplicial : SimplicialObject A :=
  SimplicialObject.Data.toSimplicialObject (coefficientBarData M)

/-- The degree-n value of the simplicial coefficient bar is its degree-n coproduct bar object. -/
@[simp]
theorem coefficientBarSimplicial_obj (n : ℕ) :
    (coefficientBarSimplicial M).obj (Opposite.op (SimplexCategory.mk n)) =
      coefficientBarObj M n := by
  exact SimplicialObject.Data.toSimplicialObject_obj_mk (coefficientBarData M) n

/-- The simplicial coefficient bar sends a coface generator to the corresponding bar face map. -/
@[simp]
theorem coefficientBarSimplicial_map_δ {n : ℕ} (i : Fin (n + 2)) :
    (coefficientBarSimplicial M).map (SimplexCategory.δ i).op =
      coefficientBarFace M i := by
  exact SimplicialObject.Data.toSimplicialObject_map_δ (coefficientBarData M) i

/-- The simplicial coefficient bar sends a codegeneracy generator to the corresponding bar
degeneracy map. -/
@[simp]
theorem coefficientBarSimplicial_map_σ {n : ℕ} (i : Fin (n + 1)) :
    (coefficientBarSimplicial M).map (SimplexCategory.σ i).op =
      coefficientBarDegeneracy M i := by
  exact SimplicialObject.Data.toSimplicialObject_map_σ (coefficientBarData M) i

section

variable [Preadditive A]

/-- Unnormalized alternating-face coefficient bar complex. -/
noncomputable def coefficientBarComplex : ChainComplex A ℕ :=
  (AlgebraicTopology.alternatingFaceMapComplex A).obj
    (coefficientBarSimplicial M)

end

section

variable [Abelian A]

/-- Normalized coefficient bar complex. -/
noncomputable def normalizedCoefficientBarComplex : ChainComplex A ℕ :=
  (AlgebraicTopology.normalizedMooreComplex A).obj
    (coefficientBarSimplicial M)

/-- Homology of a small category with coefficients in the covariant functor `M`, computed by the
normalized category bar complex. -/
noncomputable abbrev homologyWithCoefficients (n : ℕ) : A :=
  (normalizedCoefficientBarComplex M).homology n

end

end CategoryTheory.CategoryHomology

end

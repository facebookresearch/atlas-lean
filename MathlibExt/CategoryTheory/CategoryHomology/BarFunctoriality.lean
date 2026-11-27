/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import MathlibExt.CategoryTheory.CategoryHomology.BarSimplicial

/-!
# Functoriality of coefficient category bars

A natural transformation of coefficient functors gives maps of bar objects,
simplicial bars, normalized bar complexes and category homology with
coefficients. Their identity and composition laws follow from the coproduct
coordinates. The normalized-complex and homology constructions retain their
abelian coefficient-category hypotheses.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.CategoryHomology

variable {C : Type u₁} [Category.{v₁} C]
  {A : Type u₂} [Category.{v₂} A]
  [HasCoproducts.{max u₁ v₁} A]
  {M N P : CategoryTheory.Functor C A}

/-- Degreewise map of coefficient bar objects induced by a natural transformation of coefficients. -/
noncomputable def coefficientBarMap (α : M ⟶ N) (n : ℕ) :
    coefficientBarObj M n ⟶ coefficientBarObj N n :=
  Limits.Sigma.map (f := coefficientBarFamily N n)
    (g := coefficientBarFamily M n) (fun F ↦ α.app F.left)

/-- Formula for a coefficient bar map on a coproduct summand. -/
@[reassoc (attr := simp)]
theorem coefficientBarι_map (α : M ⟶ N) {n : ℕ}
    (F : ComposableArrows C n) :
    coefficientBarι M F ≫ coefficientBarMap α n =
      α.app F.left ≫ coefficientBarι N F := by
  let η : Discrete.functor (coefficientBarFamily M n) ⟶
      Discrete.functor (coefficientBarFamily N n) :=
    Discrete.natTrans fun X ↦ α.app X.as.left
  change colimit.ι (Discrete.functor (coefficientBarFamily M n))
      (Discrete.mk F) ≫ colimMap η =
    α.app F.left ≫
      colimit.ι (Discrete.functor (coefficientBarFamily N n)) (Discrete.mk F)
  exact ι_colimMap η (Discrete.mk F)

/-- The degreewise coefficient bar map preserves identity natural transformations. -/
@[simp]
theorem coefficientBarMap_id (n : ℕ) :
    coefficientBarMap (𝟙 M) n = 𝟙 _ := by
  apply coefficientBar_hom_ext M
  intro F
  rw [coefficientBarι_map]
  change 𝟙 _ ≫ coefficientBarι M F = coefficientBarι M F ≫ 𝟙 _
  rw [Category.id_comp, Category.comp_id]

/-- The degreewise coefficient bar map preserves composition of coefficient natural
transformations. -/
@[simp]
theorem coefficientBarMap_comp (α : M ⟶ N) (β : N ⟶ P) (n : ℕ) :
    coefficientBarMap (α ≫ β) n =
      coefficientBarMap α n ≫ coefficientBarMap β n := by
  apply coefficientBar_hom_ext M
  intro F
  calc
    coefficientBarι M F ≫ coefficientBarMap (α ≫ β) n =
        (α ≫ β).app F.left ≫ coefficientBarι P F :=
      coefficientBarι_map (α ≫ β) F
    _ = (α.app F.left ≫ β.app F.left) ≫ coefficientBarι P F := rfl
    _ = α.app F.left ≫ (β.app F.left ≫ coefficientBarι P F) :=
      Category.assoc _ _ _
    _ = α.app F.left ≫
        (coefficientBarι N F ≫ coefficientBarMap β n) := by
      rw [coefficientBarι_map]
    _ = (α.app F.left ≫ coefficientBarι N F) ≫
        coefficientBarMap β n := (Category.assoc _ _ _).symm
    _ = (coefficientBarι M F ≫ coefficientBarMap α n) ≫
        coefficientBarMap β n := by rw [coefficientBarι_map]
    _ = coefficientBarι M F ≫
        (coefficientBarMap α n ≫ coefficientBarMap β n) :=
      Category.assoc _ _ _

/-- Coefficient bar maps commute with faces. -/
theorem coefficientBarMap_naturality_face (α : M ⟶ N)
    {n : ℕ} (i : Fin (n + 2)) :
    coefficientBarMap α (n + 1) ≫ coefficientBarFace N i =
      coefficientBarFace M i ≫ coefficientBarMap α n := by
  apply coefficientBar_hom_ext M
  intro F
  have hMapSource := coefficientBarι_map α F
  have hMapTarget := coefficientBarι_map α ((nerve C).δ i F)
  have hFaceM := coefficientBarι_face M i F
  have hFaceN := coefficientBarι_face N i F
  have hNat := α.naturality (faceLeftHom i F)
  change M.map (faceLeftHom i F) ≫ α.app _ =
    α.app _ ≫ N.map (faceLeftHom i F) at hNat
  calc
    coefficientBarι M F ≫
          (coefficientBarMap α (n + 1) ≫ coefficientBarFace N i) =
        (coefficientBarι M F ≫ coefficientBarMap α (n + 1)) ≫
          coefficientBarFace N i := (Category.assoc _ _ _).symm
    _ = (α.app F.left ≫ coefficientBarι N F) ≫
          coefficientBarFace N i := by
      exact congrArg (fun k ↦ k ≫ coefficientBarFace N i) hMapSource
    _ = α.app F.left ≫
          (coefficientBarι N F ≫ coefficientBarFace N i) :=
      Category.assoc _ _ _
    _ = α.app F.left ≫
          (coefficientFaceHom N i F ≫
            coefficientBarι N ((nerve C).δ i F)) := by
      exact congrArg (fun k ↦ α.app F.left ≫ k) hFaceN
    _ = (α.app F.left ≫ coefficientFaceHom N i F) ≫
          coefficientBarι N ((nerve C).δ i F) :=
      (Category.assoc _ _ _).symm
    _ = (coefficientFaceHom M i F ≫
          α.app ((nerve C).δ i F).left) ≫
            coefficientBarι N ((nerve C).δ i F) := by
      exact congrArg (fun k ↦ k ≫ coefficientBarι N ((nerve C).δ i F)) hNat.symm
    _ = coefficientFaceHom M i F ≫
          (α.app ((nerve C).δ i F).left ≫
            coefficientBarι N ((nerve C).δ i F)) :=
      Category.assoc _ _ _
    _ = coefficientFaceHom M i F ≫
          (coefficientBarι M ((nerve C).δ i F) ≫
            coefficientBarMap α n) := by
      exact congrArg (fun k ↦ coefficientFaceHom M i F ≫ k) hMapTarget.symm
    _ = (coefficientFaceHom M i F ≫
          coefficientBarι M ((nerve C).δ i F)) ≫
            coefficientBarMap α n := (Category.assoc _ _ _).symm
    _ = (coefficientBarι M F ≫ coefficientBarFace M i) ≫
            coefficientBarMap α n := by
      exact congrArg (fun k ↦ k ≫ coefficientBarMap α n) hFaceM.symm
    _ = coefficientBarι M F ≫
          (coefficientBarFace M i ≫ coefficientBarMap α n) :=
      Category.assoc _ _ _

/-- Coefficient bar maps commute with degeneracies. -/
theorem coefficientBarMap_naturality_degeneracy (α : M ⟶ N)
    {n : ℕ} (i : Fin (n + 1)) :
    coefficientBarMap α n ≫ coefficientBarDegeneracy N i =
      coefficientBarDegeneracy M i ≫ coefficientBarMap α (n + 1) := by
  apply coefficientBar_hom_ext M
  intro F
  have hMapSource := coefficientBarι_map α F
  have hMapTarget := coefficientBarι_map α ((nerve C).σ i F)
  have hDegM := coefficientBarι_degeneracy M i F
  have hDegN := coefficientBarι_degeneracy N i F
  have hNat := α.naturality (degeneracyLeftHom i F)
  change M.map (degeneracyLeftHom i F) ≫ α.app _ =
    α.app _ ≫ N.map (degeneracyLeftHom i F) at hNat
  calc
    coefficientBarι M F ≫
          (coefficientBarMap α n ≫ coefficientBarDegeneracy N i) =
        (coefficientBarι M F ≫ coefficientBarMap α n) ≫
          coefficientBarDegeneracy N i := (Category.assoc _ _ _).symm
    _ = (α.app F.left ≫ coefficientBarι N F) ≫
          coefficientBarDegeneracy N i := by
      exact congrArg (fun k ↦ k ≫ coefficientBarDegeneracy N i) hMapSource
    _ = α.app F.left ≫
          (coefficientBarι N F ≫ coefficientBarDegeneracy N i) :=
      Category.assoc _ _ _
    _ = α.app F.left ≫
          (coefficientDegeneracyHom N i F ≫
            coefficientBarι N ((nerve C).σ i F)) := by
      exact congrArg (fun k ↦ α.app F.left ≫ k) hDegN
    _ = (α.app F.left ≫ coefficientDegeneracyHom N i F) ≫
          coefficientBarι N ((nerve C).σ i F) :=
      (Category.assoc _ _ _).symm
    _ = (coefficientDegeneracyHom M i F ≫
          α.app ((nerve C).σ i F).left) ≫
            coefficientBarι N ((nerve C).σ i F) := by
      exact congrArg (fun k ↦ k ≫ coefficientBarι N ((nerve C).σ i F)) hNat.symm
    _ = coefficientDegeneracyHom M i F ≫
          (α.app ((nerve C).σ i F).left ≫
            coefficientBarι N ((nerve C).σ i F)) :=
      Category.assoc _ _ _
    _ = coefficientDegeneracyHom M i F ≫
          (coefficientBarι M ((nerve C).σ i F) ≫
            coefficientBarMap α (n + 1)) := by
      exact congrArg (fun k ↦ coefficientDegeneracyHom M i F ≫ k) hMapTarget.symm
    _ = (coefficientDegeneracyHom M i F ≫
          coefficientBarι M ((nerve C).σ i F)) ≫
            coefficientBarMap α (n + 1) := (Category.assoc _ _ _).symm
    _ = (coefficientBarι M F ≫ coefficientBarDegeneracy M i) ≫
            coefficientBarMap α (n + 1) := by
      exact congrArg (fun k ↦ k ≫ coefficientBarMap α (n + 1)) hDegM.symm
    _ = coefficientBarι M F ≫
          (coefficientBarDegeneracy M i ≫ coefficientBarMap α (n + 1)) :=
      Category.assoc _ _ _

/-- Morphism of simplicial coefficient-bar data. -/
noncomputable def coefficientBarDataMap (α : M ⟶ N) :
    coefficientBarData M ⟶ coefficientBarData N where
  app := coefficientBarMap α
  w_δ := coefficientBarMap_naturality_face α
  w_σ := coefficientBarMap_naturality_degeneracy α

/-- The morphism of coefficient simplicial data induced by an identity is the identity. -/
@[simp]
theorem coefficientBarDataMap_id :
    coefficientBarDataMap (𝟙 M) = 𝟙 _ := by
  apply SimplicialObject.Data.Hom.ext
  intro n
  exact coefficientBarMap_id n

/-- Composition of coefficient natural transformations induces composition of their simplicial
data morphisms. -/
@[simp]
theorem coefficientBarDataMap_comp (α : M ⟶ N) (β : N ⟶ P) :
    coefficientBarDataMap (α ≫ β) =
      coefficientBarDataMap α ≫ coefficientBarDataMap β := by
  apply SimplicialObject.Data.Hom.ext
  intro n
  exact coefficientBarMap_comp α β n

/-- Coefficient bar as a functor to simplicial data. -/
noncomputable def coefficientBarDataFunctor :
    (C ⥤ A) ⥤ SimplicialObject.Data A where
  obj := coefficientBarData
  map := coefficientBarDataMap

/-- Coefficient bar as a functor to simplicial objects. -/
noncomputable def coefficientBarSimplicialFunctor :
    (C ⥤ A) ⥤ SimplicialObject A :=
  coefficientBarDataFunctor ⋙ SimplicialObject.Data.toSimplicialFunctor

/-- Simplicial coefficient-bar map induced by a natural transformation. -/
noncomputable def coefficientBarSimplicialMap (α : M ⟶ N) :
    coefficientBarSimplicial M ⟶ coefficientBarSimplicial N :=
  SimplicialObject.Data.toSimplicialNatTrans (coefficientBarDataMap α)

/-- The coefficient simplicial bar functor evaluates to the simplicial bar of its given
coefficient diagram. -/
@[simp]
theorem coefficientBarSimplicialFunctor_obj (M : C ⥤ A) :
    (coefficientBarSimplicialFunctor (C := C) (A := A)).obj M =
      coefficientBarSimplicial M := rfl

/-- The coefficient simplicial bar functor sends a natural transformation to the induced
simplicial bar map. -/
@[simp]
theorem coefficientBarSimplicialFunctor_map (α : M ⟶ N) :
    (coefficientBarSimplicialFunctor (C := C) (A := A)).map α =
      coefficientBarSimplicialMap α := rfl

section

variable [Abelian A]

/-- Normalized coefficient-bar complex as a functor of coefficients. -/
noncomputable def normalizedCoefficientBarComplexFunctor :
    (C ⥤ A) ⥤ ChainComplex A ℕ :=
  coefficientBarSimplicialFunctor ⋙ AlgebraicTopology.normalizedMooreComplex A

/-- The normalized coefficient bar functor evaluates to the normalized bar complex of its
coefficient diagram. -/
@[simp]
theorem normalizedCoefficientBarComplexFunctor_obj (M : C ⥤ A) :
    (normalizedCoefficientBarComplexFunctor (C := C) (A := A)).obj M =
      normalizedCoefficientBarComplex M := rfl

/-- Category homology with coefficients as a functor of the coefficient system. -/
noncomputable def homologyWithCoefficientsFunctor (n : ℕ) :
    (C ⥤ A) ⥤ A :=
  normalizedCoefficientBarComplexFunctor ⋙
    HomologicalComplex.homologyFunctor A (ComplexShape.down ℕ) n

/-- The degree-n coefficient homology functor evaluates to category homology with the given
coefficient diagram. -/
@[simp]
theorem homologyWithCoefficientsFunctor_obj (M : C ⥤ A) (n : ℕ) :
    (homologyWithCoefficientsFunctor (C := C) (A := A) n).obj M =
      homologyWithCoefficients M n := rfl

end
end CategoryTheory.CategoryHomology

end

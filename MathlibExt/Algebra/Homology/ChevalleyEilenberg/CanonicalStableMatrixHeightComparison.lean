/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Algebra.Homology.ChevalleyEilenberg.CanonicalStableMatrixWorkingHeight
public import MathlibExt.Algebra.Homology.ChevalleyEilenberg.CoalgebraWorkingHeightFunctor
public import MathlibExt.Algebra.Homology.HomologicalComplex.UliftPreorderColimit

/-!
# Stable matrix Chevalley–Eilenberg colimits under universe lifting

For a unital algebra over a commutative ring, universe lifting preserves the finite-matrix
Chevalley–Eilenberg colimit. The lifted finite-stage cocone is colimiting, and its comparison
with the lifted complex of the stable matrix Lie algebra is an isomorphism.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits

universe u v z

namespace ChevalleyEilenberg

attribute [local instance 100] LieRing.ofAssociativeRing

variable (k : Type u) [CommRing k] (A : Type v) [Ring A] [Algebra k A]

/-- The finite-matrix diagram is the module-lift image. -/
def matrixComplexFunctorULiftIso :
    matrixComplexFunctor k A ⋙
        (ModuleCat.uliftFunctor.{max u v z, max u v} k).mapHomologicalComplex (ComplexShape.down ℕ) ≅
      matrixComplexFunctorAtHeight.{u,v,max u v z} k A :=
  NatIso.ofComponents (fun m => Iso.refl _) (by
    intro m n h
    change (((ModuleCat.uliftFunctor.{max u v z, max u v} k).mapHomologicalComplex
        (ComplexShape.down ℕ)).map (matrixZeroCornerMap k A (leOfHom h))) ≫ 𝟙 _ =
      𝟙 _ ≫ matrixZeroCornerMapAtHeight.{u,v,max u v z} k A (leOfHom h)
    rw [Category.comp_id, Category.id_comp]
    exact (nativeLiftedComplexMapAtHeight_eq_uliftMap.{u,v,max u v z} k
      (Matrix (Fin m) (Fin m) A) (Matrix.zeroExtendLieHom k A (leOfHom h))).symm)

/-- Finite inclusions form the canonical stable CE cocone at the chosen height. -/
def canonicalStableMatrixCECoconeAtHeight :
    Cocone (matrixComplexFunctorAtHeight.{u,v,max u v z} k A) where
  pt := canonicalStableMatrixCEComplexAtHeight.{u,v,max u v z} k A
  ι :=
    { app := canonicalStableMatrixCEInclusionAtHeight.{u,v,max u v z} k A
      naturality m n h := by
        change matrixZeroCornerMapAtHeight.{u,v,max u v z} k A (leOfHom h) ≫
            canonicalStableMatrixCEInclusionAtHeight.{u,v,max u v z} k A n =
          canonicalStableMatrixCEInclusionAtHeight.{u,v,max u v z} k A m ≫ 𝟙 _
        rw [Category.comp_id]
        exact (nativeLiftedComplexMapAtHeight_comp.{u,v,v,v,max u v z} k
          (Matrix (Fin m) (Fin m) A) (Matrix.zeroExtendLieHom k A (leOfHom h))
          (canonicalStableMatrixLieInclusion k A n)).trans
            (congrArg (nativeLiftedComplexMapAtHeight.{u,v,v,max u v z} k
              (Matrix (Fin m) (Fin m) A))
              (canonicalStableMatrixLieInclusion_zeroCorner k A (leOfHom h))) }

/-- The finite-matrix colimit at the chosen common height. -/
abbrev stableMatrixCEComplexAtHeight : ChainComplex (ModuleCat.{max u v z} k) ℕ :=
  colimit (matrixComplexFunctorAtHeight.{u,v,max u v z} k A)

/-- Canonical inclusions construct the comparison at this working height. -/
def colimitToCanonicalStableMatrixCEAtHeight :
    stableMatrixCEComplexAtHeight.{u,v,z} k A ⟶
      canonicalStableMatrixCEComplexAtHeight.{u,v,max u v z} k A :=
  colimit.desc _ (canonicalStableMatrixCECoconeAtHeight.{u,v,z} k A)

/-- The working-height comparison retains every finite Lie inclusion. -/
@[reassoc]
theorem colimitToCanonicalStableMatrixCEAtHeight_ι (m : ℕ) :
    colimit.ι (matrixComplexFunctorAtHeight.{u,v,max u v z} k A) m ≫
        colimitToCanonicalStableMatrixCEAtHeight.{u,v,z} k A =
      canonicalStableMatrixCEInclusionAtHeight.{u,v,max u v z} k A m :=
  colimit.ι_desc (canonicalStableMatrixCECoconeAtHeight.{u,v,z} k A) m

/-- The universe-lifted canonical Chevalley–Eilenberg cocone is colimiting. -/
def canonicalStableMatrixCEAtHeightIsColimit :
    IsColimit (canonicalStableMatrixCECoconeAtHeight.{u,v,z} k A) := by
  let E := (ModuleCat.uliftFunctor.{max u v z, max u v} k).mapHomologicalComplex (ComplexShape.down ℕ)
  let S := E.mapCocone (canonicalStableMatrixCECocone k A)
  let e := matrixComplexFunctorULiftIso.{u,v,z} k A
  have hS : IsColimit S := isColimitOfPreserves E (canonicalStableMatrixCEIsColimit k A)
  have hp : IsColimit ((Cocone.precompose e.inv).obj S) :=
    (IsColimit.precomposeHomEquiv e.symm S).symm hS
  have w : (Cocone.precompose e.inv).obj S ≅ canonicalStableMatrixCECoconeAtHeight.{u,v,z} k A :=
    Cocone.ext (Iso.refl _) (by
      intro m
      change (𝟙 _ ≫ E.map (canonicalStableMatrixCEInclusion k A m)) ≫ 𝟙 _ =
        canonicalStableMatrixCEInclusionAtHeight.{u,v,max u v z} k A m
      rw [Category.id_comp, Category.comp_id]
      exact (nativeLiftedComplexMapAtHeight_eq_uliftMap.{u,v,max u v z} k
        (Matrix (Fin m) (Fin m) A) (canonicalStableMatrixLieInclusion k A m)).symm)
  exact IsColimit.ofIsoColimit hp w

/-- The common-height finite-matrix colimit is CE of the canonical stable Lie carrier. -/
def canonicalStableMatrixCEIsoAtHeight :
    stableMatrixCEComplexAtHeight.{u,v,z} k A ≅
      canonicalStableMatrixCEComplexAtHeight.{u,v,max u v z} k A :=
  (colimit.isColimit (matrixComplexFunctorAtHeight.{u,v,max u v z} k A)).coconePointUniqueUpToIso
    (canonicalStableMatrixCEAtHeightIsColimit.{u,v,z} k A)

/-- The isomorphism retains exactly the canonical finite-inclusion comparison. -/
theorem canonicalStableMatrixCEIsoAtHeight_hom :
    (canonicalStableMatrixCEIsoAtHeight.{u,v,z} k A).hom =
      colimitToCanonicalStableMatrixCEAtHeight.{u,v,z} k A := rfl

/-- Invertibility of the common-height comparison follows from the colimit property. -/
instance colimitToCanonicalStableMatrixCEAtHeight_isIso :
    IsIso (colimitToCanonicalStableMatrixCEAtHeight.{u,v,z} k A) := by
  rw [← canonicalStableMatrixCEIsoAtHeight_hom]
  infer_instance

end ChevalleyEilenberg

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Homology.Hochschild.NonUnital.ConnesWorkingHeight
public import MathlibExt.Algebra.Homology.Hochschild.NonUnital.ConnesComparison
public import MathlibExt.Algebra.Homology.HomologicalComplex.MapHomologyIso

/-!
# Rational Connes comparison at a specified carrier height

The rational cyclic-to-Connes homology comparison
commutes with module universe lifting, its homology
comparison and the Connes cokernel comparison.
-/

@[expose] public section

noncomputable section

open CategoryTheory

universe u v z

namespace ModuleCat.Algebra.Hochschild.NonUnital

variable (k : Type u) [CommRing k] [Algebra ℚ k]
  (A : Type v) [NonUnitalRing A] [Module k A]
  [IsScalarTower k A A] [SMulCommClass k A A]

/-- Native lifting of the original prescribed rational cyclic-to-Connes homology isomorphism. -/
def cyclicToConnesHomologyIsoAtHeight (n : ℕ) :
    (ModuleCat.uliftFunctor.{max u v z, max u v} k).obj (cyclicHomology k A n) ≅
      connesHomologyAtHeight.{u,v,z} k A n :=
  (ModuleCat.uliftFunctor.{max u v z, max u v} k).mapIso (cyclicToConnesHomologyIso k A n) ≪≫
    (((ModuleCat.uliftFunctor.{max u v z, max u v} k).mapHomologicalComplexHomologyIso
      (ComplexShape.down ℕ) n).app (connesComplex k A)).symm ≪≫
        HomologicalComplex.homologyMapIso (connesComplexLiftIsoAtHeight.{u,v,z} k A) n

/-- The comparison retains the exact native original rational homology map and lift comparisons. -/
theorem cyclicToConnesHomologyIsoAtHeight_hom (n : ℕ) :
    (cyclicToConnesHomologyIsoAtHeight.{u,v,z} k A n).hom =
      (ModuleCat.uliftFunctor.{max u v z, max u v} k).map (cyclicToConnesHomology k A n) ≫
        (((ModuleCat.uliftFunctor.{max u v z, max u v} k).mapHomologicalComplexHomologyIso
          (ComplexShape.down ℕ) n).app (connesComplex k A)).inv ≫
            HomologicalComplex.homologyMap (connesComplexLiftIsoAtHeight.{u,v,z} k A).hom n := rfl

end ModuleCat.Algebra.Hochschild.NonUnital

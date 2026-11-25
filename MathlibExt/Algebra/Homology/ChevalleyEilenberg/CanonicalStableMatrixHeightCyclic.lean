/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Algebra.Homology.ChevalleyEilenberg.CanonicalStableMatrixHeightComparison
public import MathlibExt.Algebra.Homology.HomologicalComplex.MapHomologyIso

/-!
# Universe lifts of stable matrix cyclic homology maps

For a unital algebra over a commutative rational algebra, the stable matrix Lie-homology map
to cyclic homology transports through the homology comparison for module universe lifting.

The target is the universe lift of cyclic homology, and every finite matrix stage retains its
homology comparison.
-/

@[expose] public section

noncomputable section

open CategoryTheory

universe u v z

namespace ChevalleyEilenberg

attribute [local instance 100] LieRing.ofAssociativeRing

variable (k : Type u) [CommRing k] [Algebra ℚ k] (A : Type v) [Ring A] [Algebra k A]

/-- Homology comparison transports the canonical stable matrix HC map. -/
def canonicalStableMatrixCyclicHomologyMapAtHeight (n : ℕ) :
    (canonicalStableMatrixCEComplexAtHeight.{u,v,z} k A).homology (n + 1) ⟶
      (ModuleCat.uliftFunctor.{max u v z, max u v} k).obj
        (ModuleCat.Algebra.Hochschild.NonUnital.cyclicHomology k A n) :=
  (((ModuleCat.uliftFunctor.{max u v z, max u v} k).mapHomologicalComplexHomologyIso
    (ComplexShape.down ℕ) (n + 1)).app (canonicalStableMatrixCEComplex k A)).hom ≫
      (ModuleCat.uliftFunctor.{max u v z, max u v} k).map (canonicalStableMatrixCyclicHomologyMap k A n)

/-- The same comparison carries every finite matrix HC map to this working height. -/
def matrixCyclicHomologyMapAtHeight (m n : ℕ) :
    (matrixComplexAtHeight.{u,v,z} k A m).homology (n + 1) ⟶
      (ModuleCat.uliftFunctor.{max u v z, max u v} k).obj
        (ModuleCat.Algebra.Hochschild.NonUnital.cyclicHomology k A n) :=
  (((ModuleCat.uliftFunctor.{max u v z, max u v} k).mapHomologicalComplexHomologyIso
    (ComplexShape.down ℕ) (n + 1)).app (matrixComplex k A m)).hom ≫
      (ModuleCat.uliftFunctor.{max u v z, max u v} k).map (matrixCyclicHomologyMap k A m n)

/-- Canonical working-height inclusions retain every finite lambda-to-HC map. -/
theorem canonicalStableMatrixCyclicHomologyMapAtHeight_finite (m n : ℕ) :
    HomologicalComplex.homologyMap (canonicalStableMatrixCEInclusionAtHeight.{u,v,z} k A m) (n + 1) ≫
        canonicalStableMatrixCyclicHomologyMapAtHeight.{u,v,z} k A n =
      matrixCyclicHomologyMapAtHeight.{u,v,z} k A m n := by
  let U := ModuleCat.uliftFunctor.{max u v z, max u v} k
  let eM : (matrixComplexAtHeight.{u,v,z} k A m).homology (n + 1) ≅
      U.obj ((matrixComplex k A m).homology (n + 1)) :=
    (U.mapHomologicalComplexHomologyIso (ComplexShape.down ℕ) (n + 1)).app (matrixComplex k A m)
  let eC : (canonicalStableMatrixCEComplexAtHeight.{u,v,z} k A).homology (n + 1) ≅
      U.obj ((canonicalStableMatrixCEComplex k A).homology (n + 1)) :=
    (U.mapHomologicalComplexHomologyIso (ComplexShape.down ℕ) (n + 1)).app
      (canonicalStableMatrixCEComplex k A)
  let a := canonicalStableMatrixCEInclusion k A m
  let i : (matrixComplexAtHeight.{u,v,z} k A m).homology (n + 1) ⟶
      (canonicalStableMatrixCEComplexAtHeight.{u,v,z} k A).homology (n + 1) :=
    HomologicalComplex.homologyMap (canonicalStableMatrixCEInclusionAtHeight.{u,v,z} k A m) (n + 1)
  let t : U.obj ((matrixComplex k A m).homology (n + 1)) ⟶
      U.obj ((canonicalStableMatrixCEComplex k A).homology (n + 1)) :=
    U.map (HomologicalComplex.homologyMap a (n + 1))
  let h : U.obj ((canonicalStableMatrixCEComplex k A).homology (n + 1)) ⟶
      U.obj (ModuleCat.Algebra.Hochschild.NonUnital.cyclicHomology k A n) :=
    U.map (canonicalStableMatrixCyclicHomologyMap k A n)
  have ha : canonicalStableMatrixCEInclusionAtHeight.{u,v,z} k A m =
      (U.mapHomologicalComplex (ComplexShape.down ℕ)).map a :=
    nativeLiftedComplexMapAtHeight_eq_uliftMap.{u,v,z} k (Matrix (Fin m) (Fin m) A)
      (canonicalStableMatrixLieInclusion k A m)
  have hH : i ≫ eC.hom = eM.hom ≫ t := by
    change HomologicalComplex.homologyMap
      (canonicalStableMatrixCEInclusionAtHeight.{u,v,z} k A m) (n + 1) ≫ eC.hom = eM.hom ≫ t
    rw [ha]
    exact U.mapHomologicalComplexHomologyIso_hom_naturality (ComplexShape.down ℕ) (n + 1) a
  have hm : t ≫ h = U.map (matrixCyclicHomologyMap k A m n) :=
    (U.map_comp (HomologicalComplex.homologyMap a (n + 1))
      (canonicalStableMatrixCyclicHomologyMap k A n)).symm.trans
        (U.congr_map (canonicalStableMatrixCyclicHomologyMap_finite k A m n))
  change i ≫ (eC.hom ≫ h) = eM.hom ≫ U.map (matrixCyclicHomologyMap k A m n)
  calc
    _ = (i ≫ eC.hom) ≫ h := (Category.assoc i eC.hom h).symm
    _ = (eM.hom ≫ t) ≫ h :=
      congrArg (fun q : (matrixComplexAtHeight.{u,v,z} k A m).homology (n + 1) ⟶
        U.obj ((canonicalStableMatrixCEComplex k A).homology (n + 1)) => q ≫ h) hH
    _ = eM.hom ≫ (t ≫ h) := Category.assoc eM.hom t h
    _ = _ := congrArg (fun q => eM.hom ≫ q) hm

end ChevalleyEilenberg

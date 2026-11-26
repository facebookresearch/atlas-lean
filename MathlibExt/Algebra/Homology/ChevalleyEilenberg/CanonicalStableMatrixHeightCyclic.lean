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
# Stable Lie-to-cyclic homology maps at a chosen carrier height

Let k be a commutative ℚ-algebra, A an associative unital k-algebra
and H = max(u,v,z). Let U lift k-modules from max(u,v) to H.
The termwise-lift homology comparison
χ_K : H_(n+1)(U(K)) ≅ U(H_(n+1)(K))
transports the stable matrix map Θ_n to
H_(n+1)(C_*^H(Mat_∞(A))) → U(HC_n(A)).

The finite matrix maps are transported by the same comparison,
and the chosen-height finite Lie inclusion square commutes:
Θ_n^H ∘ H_(n+1)(C_*^H(i_m)) = Θ_(m,n)^H.
The target is the lift of cyclic homology of A, and the ring,
algebra and extra-height worlds are independent.
-/

@[expose] public section

noncomputable section

open CategoryTheory

universe u v z

namespace ChevalleyEilenberg

attribute [local instance 100] LieRing.ofAssociativeRing

variable (k : Type u) [CommRing k] [Algebra ℚ k] (A : Type v) [Ring A] [Algebra k A]

/-- For a commutative ℚ-algebra k, an associative unital
k-algebra A and H = max(u,v,z), the chosen-height map is
H_(n+1)(C_*^H(Mat_∞(A))) → U(HC_n(A)).
It is U(Θ_n) composed after the homology comparison
H_(n+1)(U(C_*(Mat_∞(A)))) ≅ U(H_(n+1)(C_*(Mat_∞(A)))). -/
def canonicalStableMatrixCyclicHomologyMapAtHeight (n : ℕ) :
    (canonicalStableMatrixCEComplexAtHeight.{u,v,z} k A).homology (n + 1) ⟶
      (ModuleCat.uliftFunctor.{max u v z, max u v} k).obj
        (ModuleCat.Algebra.Hochschild.NonUnital.cyclicHomology k A n) :=
  (((ModuleCat.uliftFunctor.{max u v z, max u v} k).mapHomologicalComplexHomologyIso
    (ComplexShape.down ℕ) (n + 1)).app (canonicalStableMatrixCEComplex k A)).hom ≫
      (ModuleCat.uliftFunctor.{max u v z, max u v} k).map (canonicalStableMatrixCyclicHomologyMap k A n)

/-- For a commutative ℚ-algebra k, an associative unital
k-algebra A, H = max(u,v,z) and m,n ≥ 0, the finite matrix map is
H_(n+1)(C_*^H(Mat_m(A))) → U(HC_n(A)).
It transports the size-m trace map by the termwise-lift homology
comparison for C_*(Mat_m(A)). -/
def matrixCyclicHomologyMapAtHeight (m n : ℕ) :
    (matrixComplexAtHeight.{u,v,z} k A m).homology (n + 1) ⟶
      (ModuleCat.uliftFunctor.{max u v z, max u v} k).obj
        (ModuleCat.Algebra.Hochschild.NonUnital.cyclicHomology k A n) :=
  (((ModuleCat.uliftFunctor.{max u v z, max u v} k).mapHomologicalComplexHomologyIso
    (ComplexShape.down ℕ) (n + 1)).app (matrixComplex k A m)).hom ≫
      (ModuleCat.uliftFunctor.{max u v z, max u v} k).map (matrixCyclicHomologyMap k A m n)

/-- For a commutative ℚ-algebra k, an associative unital
k-algebra A, H = max(u,v,z) and m,n ≥ 0, the lifted trace maps
satisfy Θ_n^H ∘ H_(n+1)(C_*^H(i_m)) = Θ_(m,n)^H.
Both paths go from finite matrix CE homology in degree n+1
to U(HC_n(A)). -/
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

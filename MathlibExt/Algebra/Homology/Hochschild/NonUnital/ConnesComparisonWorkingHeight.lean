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
# Rational Connes homology comparison at a chosen height

Let k be a commutative ℚ-algebra and A a nonunital k-algebra with
k-bilinear multiplication. For independent carrier worlds u and v and
an arbitrary extra height z, put H = max(u,v,z) and let U be the
k-module universe-lift functor to height H.

The first-column cyclic-to-Connes isomorphism lifts to
U(HC_n(A)) ≅ H_n(Cλ^H(A)), where Cλ^H is the first-column cokernel
formed from the lifted cyclic bicomplex. Its forward map is
H_n(e_Q) ∘ χ_Q⁻¹ ∘ U(χ_A), where χ_A is the rational homology
comparison, χ_Q : H_n(U(Cλ(A))) ≅ U(H_n(Cλ(A))) is the
lift-homology comparison, and e_Q : U(Cλ(A)) ≅ Cλ^H(A) is the
lifted cokernel comparison.
-/

@[expose] public section

noncomputable section

open CategoryTheory

universe u v z

namespace ModuleCat.Algebra.Hochschild.NonUnital

variable (k : Type u) [CommRing k] [Algebra ℚ k]
  (A : Type v) [NonUnitalRing A] [Module k A]
  [IsScalarTower k A A] [SMulCommClass k A A]

/-- For a commutative ℚ-algebra k, a nonunital k-algebra A with
k-bilinear multiplication and H = max(u,v,z), there is an isomorphism
ULift^H HC_n(A) ≅ H_n(Cλ^H(A)) for every n ≥ 0.
It lifts the first-column rational comparison and then uses the
homology and cokernel comparisons for the module universe lift. -/
def cyclicToConnesHomologyIsoAtHeight (n : ℕ) :
    (ModuleCat.uliftFunctor.{max u v z, max u v} k).obj (cyclicHomology k A n) ≅
      connesHomologyAtHeight.{u,v,z} k A n :=
  (ModuleCat.uliftFunctor.{max u v z, max u v} k).mapIso (cyclicToConnesHomologyIso k A n) ≪≫
    (((ModuleCat.uliftFunctor.{max u v z, max u v} k).mapHomologicalComplexHomologyIso
      (ComplexShape.down ℕ) n).app (connesComplex k A)).symm ≪≫
        HomologicalComplex.homologyMapIso (connesComplexLiftIsoAtHeight.{u,v,z} k A) n

/-- Let U be the module lift to H = max(u,v,z), with k a
commutative ℚ-algebra and A a nonunital k-algebra. Write
χ_A : HC_n(A) ≅ H_n(Cλ(A)),
χ_Q : H_n(U(Cλ(A))) ≅ U(H_n(Cλ(A))) and
e_Q : U(Cλ(A)) ≅ Cλ^H(A).
The forward chosen-height comparison is
H_n(e_Q) ∘ χ_Q⁻¹ ∘ U(χ_A.hom).
All maps have the indicated homology or lifted-homology endpoints. -/
theorem cyclicToConnesHomologyIsoAtHeight_hom (n : ℕ) :
    (cyclicToConnesHomologyIsoAtHeight.{u,v,z} k A n).hom =
      (ModuleCat.uliftFunctor.{max u v z, max u v} k).map (cyclicToConnesHomology k A n) ≫
        (((ModuleCat.uliftFunctor.{max u v z, max u v} k).mapHomologicalComplexHomologyIso
          (ComplexShape.down ℕ) n).app (connesComplex k A)).inv ≫
            HomologicalComplex.homologyMap (connesComplexLiftIsoAtHeight.{u,v,z} k A).hom n := rfl

end ModuleCat.Algebra.Hochschild.NonUnital

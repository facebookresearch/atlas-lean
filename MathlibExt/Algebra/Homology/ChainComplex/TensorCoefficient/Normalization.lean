/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Algebra.Homology.ChainComplex.TensorCoefficient
public import MathlibExt.AlgebraicTopology.DoldKan.AdditiveNormalizationCoherence

/-!
# Canonical coefficient tensor and normalization comparison

The existing canonical additive-normalization isomorphism applies to the
native tensor functor for every original coefficient module. Its naturality
in natural transformations makes this comparison natural in coefficient maps.
No exactness or flatness is required to commute tensor and normalization:
the native Moore split pair supplies that comparison.


-/

@[expose] public section

noncomputable section

open CategoryTheory AlgebraicTopology

universe u v t

namespace ChainComplex.TensorCoefficient

variable (R : Type u) [CommRing R] (X : SimplicialObject (ModuleCat.{v} R))

/-- The original degreewise coefficient tensor diagram. -/
def diagramFunctor : ModuleCat.{t} R ⥤ SimplicialObject (ModuleCat.{max v t} R) where
  obj M := X ⋙ (ModuleCat.tensorBifunctorAt.{u, t, v} R).obj M
  map f := CategoryTheory.Functor.whiskerLeft X ((ModuleCat.tensorBifunctorAt.{u, t, v} R).map f)
  map_id M := by
    apply NatTrans.ext
    funext i
    exact NatTrans.congr_app ((ModuleCat.tensorBifunctorAt.{u, t, v} R).map_id M) (X.obj i)
  map_comp f g := by
    apply NatTrans.ext
    funext i
    exact NatTrans.congr_app ((ModuleCat.tensorBifunctorAt.{u, t, v} R).map_comp f g) (X.obj i)

instance diagramFunctor_additive : (diagramFunctor.{u, v, t} R X).Additive where
  map_add {M N f g} := by
    apply NatTrans.ext
    funext i
    exact NatTrans.congr_app
      ((ModuleCat.tensorBifunctorAt.{u, t, v} R).map_add (f := f) (g := g)) (X.obj i)

/-- Normalize the same original coefficient tensor diagram. -/
def normalizedDiagramFunctor :
    ModuleCat.{t} R ⥤ ChainComplex (ModuleCat.{max v t} R) ℕ :=
  diagramFunctor R X ⋙ normalizedMooreComplex (ModuleCat.{max v t} R)

/-- The existing canonical additive comparison, natural in arbitrary coefficients. -/
def normalizationNatIso :
    functor.{u, v, t} R ((normalizedMooreComplex (ModuleCat.{v} R)).obj X) ≅
      normalizedDiagramFunctor R X :=
  NatIso.ofComponents
    (fun M => ((NormalizedQuotient.mooreCompMapIso
      ((ModuleCat.tensorBifunctorAt.{u, t, v} R).obj M)).app X))
    (by
      intro M N f
      exact NormalizedQuotient.mooreCompMapIso_natTrans
        ((ModuleCat.tensorBifunctorAt.{u, t, v} R).map f) X)

/-- The comparison retains the actual native inclusion, alternating map and projection. -/
theorem normalizationNatIso_hom_app (M : ModuleCat.{t} R) :
    (normalizationNatIso R X).hom.app M =
      (((ModuleCat.tensorBifunctorAt.{u, t, v} R).obj M).mapHomologicalComplex
        (ComplexShape.down ℕ)).map (inclusionOfMooreComplexMap X) ≫
      (alternatingFaceMapComplexCompMapHomologicalComplexIso
        ((ModuleCat.tensorBifunctorAt.{u, t, v} R).obj M)).hom.app X ≫
      DoldKan.PInftyToNormalizedMooreComplex
        (X ⋙ (ModuleCat.tensorBifunctorAt.{u, t, v} R).obj M) :=
  NormalizedQuotient.mooreCompMapIso_hom _ X

end ChainComplex.TensorCoefficient

end

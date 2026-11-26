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
# Tensor coefficients commute with normalized Moore chains

Let R be a commutative ring, X a simplicial R-module, and M a coefficient module. There is a
natural chain isomorphism M⊗_R N(X) ≅ N(M⊗_R X), where the coefficient appears first in every
tensor term.

The forward map tensors the normalized Moore inclusion into alternating-face chains, uses the
additive tensor–alternating-chain comparison, and projects to the normalized Moore complex.
The Moore splitting gives this comparison without a flatness assumption, and it is natural in
coefficient maps. The coefficient and simplicial carrier universes are independent.
-/

@[expose] public section

noncomputable section

open CategoryTheory AlgebraicTopology

universe u v t

namespace ChainComplex.TensorCoefficient

variable (R : Type u) [CommRing R] (X : SimplicialObject (ModuleCat.{v} R))

/-- Let R be a commutative ring and X a simplicial object in ModuleCat.{v} R. Define a functor
from ModuleCat.{t} R to simplicial objects in ModuleCat.{max(v,t)} R by M ↦ M⊗_R X. At each
simplex its term is M⊗_R X_Δ, and a coefficient map acts on the first tensor factor. -/
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

/-- For a commutative ring R and simplicial R-module X, define the coefficient functor M ↦ N(M⊗_R
X), where N is normalizedMooreComplex. If X has carrier universe v and M universe t, the
resulting ℕ-indexed chain complex has carrier universe max(v,t). -/
def normalizedDiagramFunctor :
    ModuleCat.{t} R ⥤ ChainComplex (ModuleCat.{max v t} R) ℕ :=
  diagramFunctor R X ⋙ normalizedMooreComplex (ModuleCat.{max v t} R)

/-- Let R be a commutative ring and X a simplicial R-module. The coefficient functors M ↦ M⊗_R
N(X) and M ↦ N(M⊗_R X) are naturally isomorphic as ℕ-indexed chain complexes. The comparison
comes from the additive normalization isomorphism for the functor M⊗_R−, using the normalized
Moore splitting. It requires no flatness of M and is natural in every coefficient map. -/
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

/-- For a commutative ring R, simplicial R-module X, and coefficient module M, the forward map
M⊗N(X) → N(M⊗X) is the composite M⊗N(X) → M⊗C_alt(X) ≅ C_alt(M⊗X) → N(M⊗X). The first arrow
tensors the normalized Moore inclusion, the middle is the additive alternating-face-chain
comparison, and the last is the canonical Dold–Kan projection to normalized Moore chains. -/
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

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Algebra.Category.CommAlgCat.CanonicalPolynomialResolutionComparison
public import MathlibExt.Algebra.Category.CommAlgCat.CotangentPushout.Simplicial

/-!
# Higher cotangent comparisons with a canonical resolution

For a commutative ring `k` and a commutative `k`-algebra `A`, apply the degreewise
higher-form functor to the canonical polynomial resolution and then normalize. In
positive weight `q` the degreewise forms are `A ⊗[P] exteriorPower_P^q Ω(P/k)`; weight
zero uses the regular coefficient module. Weight one recovers the cotangent complex.

If an augmented simplicial algebra `P → const A` has a compatible polynomial splitting
and an additively aspherical augmentation, its higher-form model is chain homotopy
equivalent to the canonical model in every weight. Tensoring this equivalence with an
arbitrary coefficient module preserves the homotopies. The coefficient universe is
independent of the ground-ring and algebra universes.
-/

@[expose] public section

noncomputable section

open CategoryTheory Opposite AlgebraicTopology
open scoped Simplicial

universe u v t

namespace CommAlgCat.CanonicalHigherCotangentComparison

variable (k : Type u) [CommRing k] (A : CommAlgCat.{max u v} k)

/--
The normalized Moore complex of the degreewise weight-`q` higher forms on the canonical
polynomial resolution of `A` over `k`. Exterior powers are formed before normalization;
weight zero uses the regular coefficient-module diagram.
-/
def complex (q : ℕ) : ChainComplex (ModuleCat.{max u v} A) ℕ :=
  (CotangentPushout.higherSimplicialFunctor.{u, v, 0} k A q ⋙
      normalizedMooreComplex (ModuleCat.{max u v} A)).obj
    (CanonicalPolynomialResolutionComparison.canonical k A)

/--
The isomorphism from the canonical weight-one higher-form complex to the cotangent
complex of `A` over `k`, induced by the degreewise identification with Kähler differentials.
-/
def oneIso : complex k A 1 ≅ cotangentComplex k A :=
  (normalizedMooreComplex (ModuleCat.{max u v} A)).mapIso
    (CotangentPushout.higherSimplicialOneIso.{u, v, 0} k A
      (CanonicalPolynomialResolutionComparison.canonical k A))

variable {k A}
  {P : Over ((SimplicialObject.const (CommAlgCat.{max u v} k)).obj A)}
  (s : PolynomialSplitting k P.left) (hP : additiveResolutionCondition k A P)

/--
For a compatible polynomial splitting `s` of `P` and additive asphericity `hP`, the
normalized weight-`q` higher-form complex of `P` is chain homotopy equivalent to the
canonical model. The maps are induced by the two augmented-algebra comparison maps.
-/
def homotopyEquiv (q : ℕ) :
    HomotopyEquiv ((CotangentPushout.higherSimplicialFunctor.{u, v, 0} k A q ⋙
      normalizedMooreComplex (ModuleCat.{max u v} A)).obj P)
      (complex k A q) where
  hom := (normalizedMooreComplex (ModuleCat.{max u v} A)).map
    (CotangentPushout.higherSimplicialMap.{u, v, 0} k A q
      (CanonicalPolynomialResolutionComparison.forward s))
  inv := (normalizedMooreComplex (ModuleCat.{max u v} A)).map
    (CotangentPushout.higherSimplicialMap.{u, v, 0} k A q
      (CanonicalPolynomialResolutionComparison.backward hP))
  homotopyHomInvId := by
    let G := CotangentPushout.higherSimplicialFunctor.{u, v, 0} k A q ⋙
      normalizedMooreComplex (ModuleCat.{max u v} A)
    have h := (CanonicalPolynomialResolutionComparison.forwardBackwardHomotopy s hP).whiskerRight
      (cotangentHigherFunctor.{u, v} k A q)
    have H : _root_.Homotopy
        (G.map (CanonicalPolynomialResolutionComparison.forward s ≫
          CanonicalPolynomialResolutionComparison.backward hP)) (G.map (𝟙 P)) :=
      SimplicialObject.Homotopy.toNormalizedChainHomotopy h
    rw [G.map_comp (CanonicalPolynomialResolutionComparison.forward s)
      (CanonicalPolynomialResolutionComparison.backward hP), G.map_id P] at H
    exact H
  homotopyInvHomId := by
    let G := CotangentPushout.higherSimplicialFunctor.{u, v, 0} k A q ⋙
      normalizedMooreComplex (ModuleCat.{max u v} A)
    have h := (CanonicalPolynomialResolutionComparison.backwardForwardHomotopy s hP).whiskerRight
      (cotangentHigherFunctor.{u, v} k A q)
    have H : _root_.Homotopy
        (G.map (CanonicalPolynomialResolutionComparison.backward hP ≫
          CanonicalPolynomialResolutionComparison.forward s))
        (G.map (𝟙 (CanonicalPolynomialResolutionComparison.canonical k A))) :=
      SimplicialObject.Homotopy.toNormalizedChainHomotopy h
    rw [G.map_comp (CanonicalPolynomialResolutionComparison.backward hP)
      (CanonicalPolynomialResolutionComparison.forward s),
      G.map_id (CanonicalPolynomialResolutionComparison.canonical k A)] at H
    exact H

/--
The chain homotopy equivalence obtained by applying `M ⊗[A] −` to the normalized
weight-`q` comparison associated to `s` and `hP`, with `M` as first tensor factor.
The coefficient module has an independent universe, and no flatness hypothesis is required.
-/
def coefficientHomotopyEquiv (q : ℕ) (M : ModuleCat.{t} A) :
    HomotopyEquiv
      ((((ModuleCat.tensorBifunctorAt.{max u v, t, max u v} A).obj M).mapHomologicalComplex
        (ComplexShape.down ℕ)).obj ((CotangentPushout.higherSimplicialFunctor.{u, v, 0} k A q ⋙
      normalizedMooreComplex (ModuleCat.{max u v} A)).obj P))
      ((((ModuleCat.tensorBifunctorAt.{max u v, t, max u v} A).obj M).mapHomologicalComplex
        (ComplexShape.down ℕ)).obj (complex k A q)) :=
  ((ModuleCat.tensorBifunctorAt.{max u v, t, max u v} A).obj M).mapHomotopyEquiv
    (homotopyEquiv s hP q)

end CommAlgCat.CanonicalHigherCotangentComparison

end

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.AlgebraicGeometry.Sites.FieldContinuousCohomologyDerivedInvariants
public import MathlibExt.AlgebraicGeometry.Sites.FieldGodementCoindCochainComparison
public import MathlibExt.CategoryTheory.Action.DiscreteCoinductionCoefficientNaturality

/-!
# Coinduction invariants and continuous coefficient maps

Apply invariants to the cosimplicial coinduction coresolution and take its alternating coface
complex. This complex is naturally isomorphic to continuous homogeneous cochains of the same
discrete field coefficient.

Coefficient maps commute with the term and complex comparisons. Coefficient-exact sequences
give short exact sequences of these complexes, and their cohomology connecting maps agree
through the comparison.
-/

/-!
# Coefficient maps of invariant coinduction

The term comparisons identify invariant coinduction maps with maps of continuous homogeneous
cochains.
-/
/-!
In each cochain degree, coefficient maps commute with the coinduction-to-homogeneous term
isomorphisms.
-/

@[expose] public section
section
noncomputable section
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits AlgebraicTopology

namespace AlgebraicGeometry.Scheme.DerivedSections
attribute [local instance] IsSepClosure.sep_closed
variable (k Ω : Type u) [Field k] [Field Ω] [Algebra k Ω] [IsSepClosure k Ω]

/-- Functor of invariant coinduction cochains.

Form the coinduction monad coresolution, apply invariants cosimplicially, and take the
alternating coface complex. -/
abbrev fieldCoindInvariantComplexFunctor :
    DiscreteAbelianAction.{u, max u w} Gal(Ω/k) ⥤ CochainComplex AddCommGrpCat.{max u w} ℕ :=
  Monad.coresolutionFunctor (DiscreteAbelianAction.coindMonad.{u, w} Gal(Ω/k)) ⋙
    (CosimplicialObject.whiskering _ _).obj (DiscreteAbelianAction.invariantsFunctor.{u, max u w} (G := Gal(Ω/k))) ⋙
      alternatingCofaceMapComplex AddCommGrpCat.{max u w}

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Invariant coinduction comparison in each degree.

The forward component is the underlying additive invariants map of the coinduction
coresolution term isomorphism. -/
theorem fieldCoindInvariantCochainIso_hom_f
    (M : DiscreteAbelianAction.{u, max u w} Gal(Ω/k)) (n : ℕ) :
    (fieldCoindInvariantCochainIso.{u, w} k Ω M).hom.f n =
      (ContinuousCohomology.discreteCoefficientForget.{max u w}).map
        ((TopRep.invariantsFunctor ℤ Gal(Ω/k)).map
          (DiscreteAbelianAction.coindCoresolutionTermIso.{u, w} Gal(Ω/k) M n).hom) := by
  rw [fieldCoindInvariantCochainIso]
  change 𝟙 _ ≫ _ = _
  rw [Category.id_comp]
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Invariant coinduction coefficient map in each degree.

A coefficient morphism acts by invariants of its monad-coresolution component, followed by
forgetting to additive groups. -/
theorem fieldCoindInvariantComplexFunctor_map_f
    {M N : DiscreteAbelianAction.{u, max u w} Gal(Ω/k)} (f : M ⟶ N) (n : ℕ) :
    ((fieldCoindInvariantComplexFunctor.{u, w} k Ω).map f).f n =
      (ContinuousCohomology.discreteCoefficientForget.{max u w}).map
        ((TopRep.invariantsFunctor ℤ Gal(Ω/k)).map
          (DiscreteAbelianAction.toTopRep.map
            (((Monad.coresolutionFunctor (DiscreteAbelianAction.coindMonad.{u, w} Gal(Ω/k))).map f).app
              (SimplexCategory.mk n)))) := rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Continuous homogeneous coefficient map in each degree.

The coefficient cochain map is the underlying invariants map of the homogeneous resolution map
with identity group homomorphism. -/
theorem fieldNativeCoefficientComplex_map_f
    {M N : DiscreteAbelianAction.{u, max u w} Gal(Ω/k)} (f : M ⟶ N) (n : ℕ) :
    ((ContinuousCohomology.discreteCoefficientCochainFunctor.{u, w}
      (InfiniteGalois.profiniteGalGrp k Ω)).map f).f n =
      (ContinuousCohomology.discreteCoefficientForget.{max u w}).map
        ((TopRep.invariantsFunctor ℤ Gal(Ω/k)).map
          (ContinuousCohomology.resolutionMap (ContinuousMonoidHom.id Gal(Ω/k))
            ((TopRep.resFunctor (MonoidHom.id Gal(Ω/k))).map
              (DiscreteAbelianAction.toTopRep.map f)) (n + 1))) := by
  apply ConcreteCategory.ext
  ext c
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Term comparison commutes with coefficient maps.

In each natural degree, the invariant-coinduction coefficient map followed by comparison
equals comparison followed by the continuous-cochain coefficient map. -/
theorem fieldCoindInvariantCochainIso_coefficient_component
    {M N : DiscreteAbelianAction.{u, max u w} Gal(Ω/k)} (f : M ⟶ N) (n : ℕ) :
    ((fieldCoindInvariantComplexFunctor.{u, w} k Ω).map f).f n ≫
      (fieldCoindInvariantCochainIso.{u, w} k Ω N).hom.f n =
    (fieldCoindInvariantCochainIso.{u, w} k Ω M).hom.f n ≫
      ((ContinuousCohomology.discreteCoefficientCochainFunctor.{u, w}
        (InfiniteGalois.profiniteGalGrp k Ω)).map f).f n := by
  rw [fieldCoindInvariantComplexFunctor_map_f, fieldNativeCoefficientComplex_map_f,
    fieldCoindInvariantCochainIso_hom_f, fieldCoindInvariantCochainIso_hom_f]
  exact DiscreteAbelianAction.coindCoresolutionInvariantTerm_coefficient_naturality.{u, w}
    Gal(Ω/k) f n

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Invariant coinduction complex comparison is natural.

The entire cochain comparison square commutes with every discrete Galois coefficient morphism. -/
theorem fieldCoindInvariantCochainIso_coefficient_naturality
    {M N : DiscreteAbelianAction.{u, max u w} Gal(Ω/k)} (f : M ⟶ N) :
    (fieldCoindInvariantComplexFunctor.{u, w} k Ω).map f ≫
      (fieldCoindInvariantCochainIso.{u, w} k Ω N).hom =
    (fieldCoindInvariantCochainIso.{u, w} k Ω M).hom ≫
      (ContinuousCohomology.discreteCoefficientCochainFunctor.{u, w}
        (InfiniteGalois.profiniteGalGrp k Ω)).map f := by
  apply HomologicalComplex.Hom.ext
  funext n
  exact fieldCoindInvariantCochainIso_coefficient_component.{u, w} k Ω f n

/-- Natural isomorphism from invariant coinduction to continuous cochains.

The coefficient-natural term comparisons assemble to a natural isomorphism of the two cochain-
complex functors. -/
def fieldCoindInvariantCochainNatIso :
    fieldCoindInvariantComplexFunctor.{u, w} k Ω ≅
      ContinuousCohomology.discreteCoefficientCochainFunctor.{u, w}
        (InfiniteGalois.profiniteGalGrp k Ω) :=
  NatIso.ofComponents (fieldCoindInvariantCochainIso.{u, w} k Ω)
    (fieldCoindInvariantCochainIso_coefficient_naturality.{u, w} k Ω)

end AlgebraicGeometry.Scheme.DerivedSections
end

/-!
# Connecting maps of invariant coinduction

Coefficient-exact sequences give short exact sequences of the two cochain complexes.
-/
/-!
The cohomology connecting morphisms in degrees `n` and `n+1` commute with the natural cochain
comparison.
-/
@[expose] public section
section
noncomputable section
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits

private theorem homologyNatIso_connecting
    {A : Type u} [Category A] [Preadditive A]
    {B : Type w} [Category B] [Abelian B]
    (F G : A ⥤ CochainComplex B ℕ) [F.PreservesZeroMorphisms] [G.PreservesZeroMorphisms]
    (e : F ≅ G) (S : ShortComplex A) (hF : (S.map F).ShortExact) (hG : (S.map G).ShortExact)
    (n : ℕ) :
    hF.δ n (n + 1) rfl ≫ HomologicalComplex.homologyMap (e.hom.app S.X₁) (n + 1) =
      HomologicalComplex.homologyMap (e.hom.app S.X₃) n ≫ hG.δ n (n + 1) rfl :=
  HomologicalComplex.HomologySequence.δ_naturality (S.mapNatTrans e.hom) hF hG n (n + 1) rfl

namespace AlgebraicGeometry.Scheme.DerivedSections
attribute [local instance] IsSepClosure.sep_closed
variable (k Ω : Type u) [Field k] [Field Ω] [Algebra k Ω] [IsSepClosure k Ω]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Invariant coinduction cochain functor is additive.

The invariant-coinduction complex functor preserves addition of coefficient morphisms. -/
instance fieldCoindInvariantComplexFunctor_additive :
    (fieldCoindInvariantComplexFunctor.{u, w} k Ω).Additive := by
  let F := ContinuousCohomology.discreteCoefficientCochainFunctor.{u, w}
    (InfiniteGalois.profiniteGalGrp k Ω)
  let : F.Additive := by
    dsimp [F]
    unfold ContinuousCohomology.discreteCoefficientCochainFunctor
    infer_instance
  exact Functor.additive_of_iso (F := F) (fieldCoindInvariantCochainNatIso.{u, w} k Ω).symm

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Coefficient exactness gives an exact invariant coinduction sequence.

A sequence satisfying the continuous-coefficient exactness predicate maps to a short exact
sequence of invariant-coinduction cochain complexes. -/
theorem fieldCoindInvariantComplex_shortExact
    (S : ShortComplex (DiscreteAbelianAction.{u, max u w} Gal(Ω/k)))
    (hS : ContinuousCohomology.DiscreteCoefficientExact.{u, w}
      (G := InfiniteGalois.profiniteGalGrp k Ω) S) :
    (S.map (fieldCoindInvariantComplexFunctor.{u, w} k Ω)).ShortExact := by
  exact ShortComplex.shortExact_of_iso
    (S.mapNatIso (fieldCoindInvariantCochainNatIso.{u, w} k Ω)).symm
    (ContinuousCohomology.discreteCoefficientCochain_shortExact.{u, w}
      (G := InfiniteGalois.profiniteGalGrp k Ω) S hS)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Invariant coinduction and continuous connecting maps agree.

For a coefficient-exact sequence, its invariant-coinduction connecting map followed by the
degree-`n+1` comparison equals the degree-`n` comparison followed by the continuous-cochain
connecting map. -/
theorem fieldCoindInvariantCochainIso_coefficient_connecting
    (S : ShortComplex (DiscreteAbelianAction.{u, max u w} Gal(Ω/k)))
    (hS : ContinuousCohomology.DiscreteCoefficientExact.{u, w}
      (G := InfiniteGalois.profiniteGalGrp k Ω) S) (n : ℕ) :
    (fieldCoindInvariantComplex_shortExact.{u, w} k Ω S hS).δ n (n + 1) rfl ≫
      HomologicalComplex.homologyMap ((fieldCoindInvariantCochainNatIso.{u, w} k Ω).hom.app S.X₁) (n + 1) =
    HomologicalComplex.homologyMap ((fieldCoindInvariantCochainNatIso.{u, w} k Ω).hom.app S.X₃) n ≫
      (ContinuousCohomology.discreteCoefficientCochain_shortExact.{u, w}
      (G := InfiniteGalois.profiniteGalGrp k Ω) S hS).δ n (n + 1) rfl :=
  homologyNatIso_connecting
    (fieldCoindInvariantComplexFunctor.{u, w} k Ω)
    (ContinuousCohomology.discreteCoefficientCochainFunctor.{u, w}
      (InfiniteGalois.profiniteGalGrp k Ω))
    (fieldCoindInvariantCochainNatIso.{u, w} k Ω) S
    (fieldCoindInvariantComplex_shortExact.{u, w} k Ω S hS)
    (ContinuousCohomology.discreteCoefficientCochain_shortExact.{u, w}
      (G := InfiniteGalois.profiniteGalGrp k Ω) S hS) n

end AlgebraicGeometry.Scheme.DerivedSections
end

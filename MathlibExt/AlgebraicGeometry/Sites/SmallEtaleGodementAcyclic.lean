/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.AlgebraicGeometry.Sites.SmallEtaleGodementSections
public import MathlibExt.AlgebraicGeometry.Sites.SmallEtaleSkyscraperAcyclic
public import MathlibExt.CategoryTheory.Pi.Preadditive
public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import Mathlib.CategoryTheory.Abelian.Transfer
public import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products

/-!
# Exactness of Godement stalk and skyscraper functors

Families of additive groups indexed by scheme points form an abelian category with enough
injectives. The skyscraper-product functor is additive, preserves epimorphisms and homology,
and preserves injective objects because its stalk-family left adjoint is exact.

Global sections of a skyscraper product are the product of its coefficients. Products of
additive groups are exact, so every such skyscraper product is acyclic for positive right-
derived global sections. All families and sheaves use coefficient universe `max u w`.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
universe u w

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

namespace AlgebraicGeometry.Scheme.DerivedSections

/-- Point indexed coefficient families have finite products.

The category of additive-group families indexed by scheme points has finite products. -/
instance smallEtaleGodementCoefficientsFiniteProducts (X : Scheme.{u}) :
    HasFiniteProducts (X → AddCommGrpCat.{max u w}) where
  out n := by
    let : HasLimitsOfShape (Discrete (Fin n)) (Discrete X ⥤ AddCommGrpCat.{max u w}) :=
      inferInstance
    exact Adjunction.hasLimitsOfShape_of_equivalence
      (piEquivalenceFunctorDiscrete X AddCommGrpCat.{max u w}).functor

/-- Point indexed coefficient families have an abelian structure.

The componentwise additive-group structure makes the point-family category abelian. -/
@[instance_reducible]
def smallEtaleGodementCoefficientsAbelian (X : Scheme.{u}) :
    Abelian (X → AddCommGrpCat.{max u w}) := by
  letI : Preadditive (X → AddCommGrpCat.{max u w}) :=
    CategoryTheory.Pi.indexedPreadditive (fun _ : X => AddCommGrpCat.{max u w})
  exact abelianOfEquivalence (piEquivalenceFunctorDiscrete X AddCommGrpCat.{max u w}).functor

attribute [instance] smallEtaleGodementCoefficientsAbelian

private theorem familyMonoComponent (X : Scheme.{u})
    {M N : X → AddCommGrpCat.{max u w}} (f : M ⟶ N) [Mono f] (x : X) : Mono (f x) := by
  change Mono (((piEquivalenceFunctorDiscrete X AddCommGrpCat.{max u w}).functor.map f).app
    ⟨x⟩)
  infer_instance

private theorem familyEpiComponent (X : Scheme.{u})
    {M N : X → AddCommGrpCat.{max u w}} (f : M ⟶ N) [Epi f] (x : X) : Epi (f x) := by
  change Epi (((piEquivalenceFunctorDiscrete X AddCommGrpCat.{max u w}).functor.map f).app
    ⟨x⟩)
  infer_instance

private theorem familyMonoOfComponents (X : Scheme.{u})
    {M N : X → AddCommGrpCat.{max u w}} (f : M ⟶ N) (hf : ∀ x, Mono (f x)) : Mono f := by
  let E := (piEquivalenceFunctorDiscrete X AddCommGrpCat.{max u w}).functor
  let : ∀ j : Discrete X, Mono ((E.map f).app j) := fun j => hf j.as
  exact E.mono_of_mono_map (NatTrans.mono_of_mono_app (E.map f))

private theorem injectiveFamily (X : Scheme.{u}) (J : X → AddCommGrpCat.{max u w})
    (hJ : ∀ x, Injective (J x)) : Injective J where
  factors {M N} g f hf := by
    let : ∀ x : X, Mono (f x) := fun x => familyMonoComponent.{u, w} X f x
    let : ∀ x : X, Injective (J x) := hJ
    refine ⟨fun x => Injective.factorThru (g x) (f x), ?_⟩
    funext x
    exact Injective.comp_factorThru (g x) (f x)

/-- Point indexed coefficient families have enough injectives.

Choose injective presentations componentwise to give enough injectives in the point-family
category. -/
instance smallEtaleGodementCoefficientsEnoughInjectives (X : Scheme.{u}) :
    EnoughInjectives (X → AddCommGrpCat.{max u w}) where
  presentation M := by
    let J : X → AddCommGrpCat.{max u w} := fun x => Injective.under (M x)
    let i : M ⟶ J := fun x => Injective.ι (M x)
    have hJ : Injective J := injectiveFamily.{u, w} X J (fun x => inferInstance)
    have hi : Mono i := familyMonoOfComponents.{u, w} X i (fun x => inferInstance)
    exact ⟨{ J := J, injective := hJ, f := i, mono := hi }⟩

set_option backward.isDefEq.respectTransparency.types false in
private theorem evaluatedProductMap_epi (X : Scheme.{u})
    {M N : X → Sheaf X.smallEtaleTopology AddCommGrpCat.{max u w}}
    (f : ∀ x, M x ⟶ N x) (U : X.Etaleᵒᵖ)
    (hf : ∀ x, Epi ((f x).hom.app U)) :
    Epi ((CategoryTheory.Limits.Pi.map f).hom.app U) := by
  let A := AddCommGrpCat.{max u w}
  let E := sheafToPresheaf X.smallEtaleTopology A ⋙
    (CategoryTheory.evaluation X.Etaleᵒᵖ A).obj U
  let eM := PreservesProduct.iso E M
  let eN := PreservesProduct.iso E N
  let a := E.map (CategoryTheory.Limits.Pi.map f)
  let b := CategoryTheory.Limits.Pi.map (fun x : X => E.map (f x))
  have hc : a ≫ eN.hom = eM.hom ≫ b := by
    apply Pi.hom_ext
    intro x
    simp only [a, b, eM, eN, Category.assoc, PreservesProduct.iso_hom,
      Pi.map_π, piComparison_comp_π, ← E.map_comp]
    rw [← Category.assoc, piComparison_comp_π, E.map_comp]
  let : AB4StarOfSize.{u} A := AB4StarOfSize_shrink.{u, w} A
  let t : Discrete.functor (fun x : X => E.obj (M x)) ⟶
      Discrete.functor (fun x : X => E.obj (N x)) :=
    Discrete.natTrans (fun x => E.map (f x.as))
  let : ∀ j : Discrete X, Epi (t.app j) := fun j => hf j.as
  let : Epi t := NatTrans.epi_of_epi_app t
  have hb : Epi b := by
    change Epi ((lim (J := Discrete X) (C := A)).map t)
    infer_instance
  let : Epi b := hb
  have ha : Epi (a ≫ eN.hom) := by
    rw [hc]
    infer_instance
  exact (epi_comp_iff_of_isIso a eN.hom).mp ha

/-- Epimorphic families give surjective skyscraper section maps.

For an epimorphism of coefficient families, the induced skyscraper-product sheaf map is
surjective on sections of each étale object. -/
theorem smallEtaleGodementSkyscrapersMap_component_surjective (X : Scheme.{u})
    {M N : X → AddCommGrpCat.{max u w}} (f : M ⟶ N) [Epi f] (U : X.Etale) :
    Function.Surjective (((smallEtaleGodementSkyscrapers.{u, w} X).map f).hom.app (op U)) := by
  have hf (x : X) : Epi
      (((smallEtaleGeometricPointCommon.{u, w}
        (smallEtaleCanonicalGeometricMorphism X x)).skyscraperSheafFunctor.map (f x)).hom.app
          (op U)) := by
    let : Epi (f x) := familyEpiComponent.{u, w} X f x
    exact (AddCommGrpCat.epi_iff_surjective _).mpr
      (smallEtaleSkyscraperMap_component_surjective.{u, w}
        (smallEtaleCanonicalGeometricMorphism X x) (f x) U)
  exact (AddCommGrpCat.epi_iff_surjective _).mp
    (evaluatedProductMap_epi.{u, w} X (fun x =>
      (smallEtaleGeometricPointCommon.{u, w}
        (smallEtaleCanonicalGeometricMorphism X x)).skyscraperSheafFunctor.map (f x))
      (op U) hf)

/-- Skyscraper product functor preserves epimorphisms.

An epimorphism of coefficient families induces an epimorphism of their product-of-skyscrapers
sheaves. -/
instance smallEtaleGodementSkyscrapersPreservesEpimorphisms (X : Scheme.{u}) :
    (smallEtaleGodementSkyscrapers.{u, w} X).PreservesEpimorphisms where
  preserves f hf := by
    let b := (smallEtaleGodementSkyscrapers.{u, w} X).map f
    let : ∀ U : X.Etaleᵒᵖ, Epi (b.hom.app U) := fun U =>
      (AddCommGrpCat.epi_iff_surjective _).mpr
        (smallEtaleGodementSkyscrapersMap_component_surjective.{u, w} X f U.unop)
    let : Epi b.hom := NatTrans.epi_of_epi_app b.hom
    exact (sheafToPresheaf X.smallEtaleTopology AddCommGrpCat.{max u w}).epi_of_epi_map
      (show Epi b.hom from inferInstance)

/-- Skyscraper product functor is additive.

The product-of-skyscrapers functor preserves addition of family morphisms. -/
instance smallEtaleGodementSkyscrapersAdditive (X : Scheme.{u}) :
    (smallEtaleGodementSkyscrapers.{u, w} X).Additive :=
  Functor.additive_of_preserves_binary_products _

/-- Skyscraper product functor preserves homology.

The functor preserves kernels and epimorphisms and hence preserves homology. -/
instance smallEtaleGodementSkyscrapersPreservesHomology (X : Scheme.{u}) :
    (smallEtaleGodementSkyscrapers.{u, w} X).PreservesHomology :=
  Functor.preservesHomology_of_preservesEpis_and_kernels _

/-- Canonical stalk family functor preserves finite limits.

Finite limits are preserved at each geometric stalk and therefore by the point-family functor. -/
instance smallEtaleGodementStalksPreservesFiniteLimits (X : Scheme.{u}) :
    PreservesFiniteLimits (smallEtaleGodementStalks.{u, w} X) where
  preservesFiniteLimits J := by
    intro _ _
    let L := smallEtaleGodementStalks.{u, w} X
    let E := (piEquivalenceFunctorDiscrete X AddCommGrpCat.{max u w}).functor
    let : PreservesLimitsOfShape J (L ⋙ E) :=
      preservesLimitsOfShape_of_evaluation (L ⋙ E) J (fun j => by
        change PreservesLimitsOfShape J
          ((smallEtaleGeometricPointCommon.{u, w}
            (smallEtaleCanonicalGeometricMorphism X j.as)).sheafFiber
              (A := AddCommGrpCat.{max u w}))
        infer_instance)
    exact preservesLimitsOfShape_of_reflects_of_preserves L E

/-- Canonical stalk family functor is additive.

The stalk-family functor preserves sums of sheaf morphisms componentwise. -/
instance smallEtaleGodementStalksAdditive (X : Scheme.{u}) :
    (smallEtaleGodementStalks.{u, w} X).Additive where
  map_add {P Q} {f g} := by
    funext x
    let p := smallEtaleGeometricPointCommon.{u, w}
      (smallEtaleCanonicalGeometricMorphism X x)
    let : (p.presheafFiber (A := AddCommGrpCat.{max u w})).Additive := by
      dsimp only [GrothendieckTopology.Point.presheafFiber]
      infer_instance
    let : (p.sheafFiber (A := AddCommGrpCat.{max u w})).Additive := by
      dsimp only [GrothendieckTopology.Point.sheafFiber]
      infer_instance
    exact (p.sheafFiber (A := AddCommGrpCat.{max u w})).map_add (f := f) (g := g)

/-- Canonical stalk family functor preserves homology.

The exact geometric stalk functors give preservation of homology by the family functor. -/
instance smallEtaleGodementStalksPreservesHomology (X : Scheme.{u}) :
    (smallEtaleGodementStalks.{u, w} X).PreservesHomology :=
  Functor.preservesHomology_of_preservesEpis_and_kernels _

/-- Skyscraper products of injective families are injective.

The skyscraper-product right adjoint preserves injective objects because its stalk-family left
adjoint preserves monomorphisms. -/
instance smallEtaleGodementSkyscrapersPreservesInjectives (X : Scheme.{u}) :
    (smallEtaleGodementSkyscrapers.{u, w} X).PreservesInjectiveObjects :=
  Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
    (smallEtaleGodementAdjunction.{u, w} X)

/-- Coefficient product functor is a right adjoint.

The product functor on point-indexed additive-group families is right adjoint to the diagonal
functor. -/
instance smallEtaleGodementCoefficientProductRightAdjoint (X : Scheme.{u}) :
    (Pi.functor (C := AddCommGrpCat.{max u w}) X).IsRightAdjoint := by
  change ((piEquivalenceFunctorDiscrete X AddCommGrpCat.{max u w}).functor ⋙
    lim (J := Discrete X) (C := AddCommGrpCat.{max u w})).IsRightAdjoint
  infer_instance

/-- Coefficient products preserve epimorphisms.

A componentwise epimorphism of additive-group families induces an epimorphism of their
products. -/
instance smallEtaleGodementCoefficientProductPreservesEpimorphisms (X : Scheme.{u}) :
    (Pi.functor (C := AddCommGrpCat.{max u w}) X).PreservesEpimorphisms where
  preserves f hf := by
    let A := AddCommGrpCat.{max u w}
    let : AB4StarOfSize.{u} A := AB4StarOfSize_shrink.{u, w} A
    let t := (piEquivalenceFunctorDiscrete X A).functor.map f
    let : Epi t := inferInstance
    change Epi ((lim (J := Discrete X) (C := A)).map t)
    infer_instance

/-- Coefficient product functor is additive.

The point-indexed product functor preserves addition of morphisms. -/
instance smallEtaleGodementCoefficientProductAdditive (X : Scheme.{u}) :
    (Pi.functor (C := AddCommGrpCat.{max u w}) X).Additive :=
  Functor.additive_of_preserves_binary_products _

/-- Coefficient products preserve homology.

Exactness of additive-group products gives preservation of homology by the coefficient product
functor. -/
instance smallEtaleGodementCoefficientProductPreservesHomology (X : Scheme.{u}) :
    (Pi.functor (C := AddCommGrpCat.{max u w}) X).PreservesHomology :=
  Functor.preservesHomology_of_preservesEpis_and_kernels _

private theorem exactDerivedSuccIsZero.{vC, uC, vD, uD}
    {C : Type uC} [Category.{vC} C] [Abelian C] [HasInjectiveResolutions C]
    {D : Type uD} [Category.{vD} D] [Abelian D]
    (F : C ⥤ D) [F.Additive] [F.PreservesHomology] (M : C) (n : ℕ) :
    IsZero ((F.rightDerived (n + 1)).obj M) := by
  let I := injectiveResolution M
  refine IsZero.of_iso ?_ (I.isoRightDerivedObj F (n + 1))
  have hz : IsZero (I.cocomplex.homology (n + 1)) :=
    (HomologicalComplex.exactAt_iff_isZero_homology _ _).mp (I.cocomplex_exactAt_succ n)
  exact IsZero.of_iso (F.map_isZero hz) ((I.cocomplex.sc (n + 1)).mapHomologyIso F)

/-- Skyscraper products have zero positive derived sections.

For any coefficient family `M` and natural `n`, `R^(n+1)Γ` of its product of canonical
geometric skyscrapers is zero. -/
theorem smallEtaleGodementDerivedSections_succ_isZero (X : Scheme.{u})
    (M : X → AddCommGrpCat.{max u w}) (n : ℕ) :
    IsZero (((Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{max u w}).rightDerived
      (n + 1)).obj ((smallEtaleGodementSkyscrapers.{u, w} X).obj M)) := by
  let R := smallEtaleGodementSkyscrapers.{u, w} X
  let Γ := Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{max u w}
  let P := Pi.functor (C := AddCommGrpCat.{max u w}) X
  let I := injectiveResolution M
  let e := (Functor.rightDerivedPrecompIsoWithResolution R Γ (n + 1) I).symm ≪≫
    ((NatIso.rightDerived (smallEtaleGodementSectionsIso.{u, w} X) (n + 1)).app M)
  exact IsZero.of_iso (exactDerivedSuccIsZero P M n) e

end AlgebraicGeometry.Scheme.DerivedSections

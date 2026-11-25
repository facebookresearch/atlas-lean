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

/-! Actual original field native comparison proof components. -/

/-! Original qualified proof block: FieldCoindCoefficientConnector -/
/-! Actual coefficient boundaries of the original coinduction invariant complex. -/

@[expose] public section
section
noncomputable section
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits AlgebraicTopology

namespace AlgebraicGeometry.Scheme.DerivedSections
attribute [local instance] IsSepClosure.sep_closed
variable (k Ω : Type u) [Field k] [Field Ω] [Algebra k Ω] [IsSepClosure k Ω]

/-- The actual invariant alternating complex of the fixed coinduction monad. -/
abbrev fieldCoindInvariantComplexFunctor :
    DiscreteAbelianAction.{u, max u w} Gal(Ω/k) ⥤ CochainComplex AddCommGrpCat.{max u w} ℕ :=
  Monad.coresolutionFunctor (DiscreteAbelianAction.coindMonad.{u, w} Gal(Ω/k)) ⋙
    (CosimplicialObject.whiskering _ _).obj (DiscreteAbelianAction.invariantsFunctor.{u, max u w} (G := Gal(Ω/k))) ⋙
      alternatingCofaceMapComplex AddCommGrpCat.{max u w}

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Each degree map of the fixed original comparison is the actual invariant coinduction term map. -/
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
/-- The coefficient map in each actual coinduction invariant degree is its original term map. -/
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
/-- The SAME original native coefficient complex keeps the stock identity-group resolution map. -/
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
/-- The genuine original coinduction degree square follows from its checked term comparison. -/
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
/-- The fixed original comparison is natural in every actual coefficient map. -/
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

/-- The same actual coefficient-complex comparison as a natural isomorphism. -/
def fieldCoindInvariantCochainNatIso :
    fieldCoindInvariantComplexFunctor.{u, w} k Ω ≅
      ContinuousCohomology.discreteCoefficientCochainFunctor.{u, w}
        (InfiniteGalois.profiniteGalGrp k Ω) :=
  NatIso.ofComponents (fieldCoindInvariantCochainIso.{u, w} k Ω)
    (fieldCoindInvariantCochainIso_coefficient_naturality.{u, w} k Ω)

end AlgebraicGeometry.Scheme.DerivedSections
end

/-! Original qualified proof block: FieldCoindCoefficientDelta -/
/-! Actual coefficient connecting maps of the same original coinduction invariant complex. -/
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
/-- Genuine original coefficient exactness gives a true short exact sequence of the
actual coinduction invariant complexes, through the fixed natural comparison. -/
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
/-- The actual homology connector of the fixed coinduction invariant complexes
agrees with the SAME original native coefficient cochain connector. -/
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

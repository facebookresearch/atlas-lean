/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialSet.CGWHRealization
public import MathlibExt.AlgebraicTopology.TopologicalSpace.CGWH.FiniteZero
public import MathlibExt.CategoryTheory.Monoidal.Pointed.Free
public import MathlibExt.Topology.Category.PointedCGWH.Closed
public import MathlibExt.Topology.Category.PointedCGWH.MonoidalUnit
public import MathlibExt.Topology.Category.PointedCGWH.Singular.HomotopyFunctor
public import Mathlib.AlgebraicTopology.SimplicialCategory.Basic

/-!
# The native singular simplicial enrichment of pointed CGWH spaces

The native free-basepoint functor is strong monoidal from cartesian CGWH
spaces to their original smash product. Its right adjoint therefore has
the canonical lax monoidal structure. The actual native singular functor
preserves finite products by the realization/singular adjunction.

Composing these two structures singularizes the original based mapping
objects. The unit-Hom equivalence is derived from the original adjunctions
and the actual zero-simplex realization, so the enrichment is on the same
pointed CGWH category with independent compact-test and carrier universes.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
universe u v

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped Simplicial MonoidalClosed

namespace PointedCGWH.NativeSimplicial

open SingularHomotopyGeometry

/-- The original free-basepoint functor is strong monoidal for the native smash factory. -/
@[instance_reducible]
def freeBasepointMonoidal : (Under.costar CGWH.point.{u, v}).Monoidal := by
  letI : BraidedCategory CGWH.{u, v} := BraidedCategory.ofCartesianMonoidalCategory
  letI : SymmetricCategory CGWH.{u, v} := inferInstance
  exact (CategoryTheory.Pointed.costarCoreMonoidal
    CGWH.point CGWH.point_isTerminal).toMonoidal

attribute [local instance] freeBasepointMonoidal

/-- The original forgetful functor has the canonical right-adjoint lax structure. -/
@[instance_reducible]
def forgetLaxMonoidal : (Under.forget CGWH.point.{u, v}).LaxMonoidal :=
  (Under.costarAdjForget CGWH.point).rightAdjointLaxMonoidal

/-- The actual underlying singular functor is strong monoidal by its proved right adjunction. -/
@[instance_reducible]
def underlyingSingularMonoidal : (underlyingSingularFunctor.{u, v}).Monoidal := by
  letI : (underlyingSingularFunctor.{u, v}).IsRightAdjoint :=
    SSet.sSetCGWHAdj.{u, v}.isRightAdjoint
  exact Functor.Monoidal.ofChosenFiniteProducts underlyingSingularFunctor

attribute [local instance] forgetLaxMonoidal underlyingSingularMonoidal

/-- The same original pointed singular functor carries the composite canonical lax structure. -/
@[instance_reducible]
def singularLaxMonoidal : (singularFunctor.{u, v}).LaxMonoidal := by
  change (Under.forget CGWH.point.{u, v} ⋙ underlyingSingularFunctor.{u, v}).LaxMonoidal
  infer_instance

attribute [local instance] singularLaxMonoidal

/-- The entire native singular unit is the original composite of the two derived lax units. -/
theorem singular_unit :
    Functor.LaxMonoidal.ε singularFunctor.{u, v} =
      Functor.LaxMonoidal.ε underlyingSingularFunctor ≫
        underlyingSingularFunctor.map (Functor.LaxMonoidal.ε (Under.forget CGWH.point)) := rfl

/-- Every native pointed singular tensorator uses the two original whole lax tensorators. -/
theorem singular_tensorator (X Y : PointedCGWH.{u, v}) :
    Functor.LaxMonoidal.μ singularFunctor X Y =
      Functor.LaxMonoidal.μ underlyingSingularFunctor X.right Y.right ≫
        underlyingSingularFunctor.map (Functor.LaxMonoidal.μ (Under.forget CGWH.point) X Y) := rfl

/-- The actual singular tensorator retains the complete original first product projection. -/
theorem underlying_tensorator_fst (X Y : CGWH.{u, v}) :
    Functor.LaxMonoidal.μ underlyingSingularFunctor X Y ≫
      underlyingSingularFunctor.map (CartesianMonoidalCategory.fst X Y) =
        CartesianMonoidalCategory.fst
          (underlyingSingularFunctor.obj X) (underlyingSingularFunctor.obj Y) :=
  Functor.Monoidal.μ_fst underlyingSingularFunctor X Y

/-- The actual singular tensorator retains the complete original second product projection. -/
theorem underlying_tensorator_snd (X Y : CGWH.{u, v}) :
    Functor.LaxMonoidal.μ underlyingSingularFunctor X Y ≫
      underlyingSingularFunctor.map (CartesianMonoidalCategory.snd X Y) =
        CartesianMonoidalCategory.snd
          (underlyingSingularFunctor.obj X) (underlyingSingularFunctor.obj Y) :=
  Functor.Monoidal.μ_snd underlyingSingularFunctor X Y

/-- Realization of the actual simplicial unit is the original native cartesian unit. -/
def realizationUnitIso : SSet.toCGWH.{u, v}.obj (𝟙_ SSet.{v}) ≅ 𝟙_ CGWH.{u, v} :=
  SSet.toCGWH.mapIso
      (SSet.stdSimplex.isTerminalObj₀.uniqueUpToIso
        CartesianMonoidalCategory.isTerminalTensorUnit).symm ≪≫
    CGWH.finiteRealizationIso (Δ[0] : SSet.{v}) ≪≫
    SSet.toCGWHOfFinite_stdSimplex_zero_iso_point ≪≫
    PointedCGWH.pointIsoTensorUnit

/-- The original native realization/singular adjunction gives the complete unit-Hom equivalence. -/
def underlyingSingularUnitHomEquiv (Y : CGWH.{u, v}) :
    (𝟙_ CGWH.{u, v} ⟶ Y) ≃
      (𝟙_ SSet.{v} ⟶ underlyingSingularFunctor.obj Y) :=
  (realizationUnitIso.symm.homCongr (Iso.refl Y)).trans
    (SSet.sSetCGWHAdj.homEquiv (𝟙_ SSet.{v}) Y)

/-- The complete unit-Hom equivalence is natural in every original CGWH target map. -/
theorem underlyingSingularUnitHomEquiv_naturality
    {X Y : CGWH.{u, v}} (f : X ⟶ Y) (g : 𝟙_ CGWH.{u, v} ⟶ X) :
    underlyingSingularUnitHomEquiv Y (g ≫ f) =
      underlyingSingularUnitHomEquiv X g ≫ underlyingSingularFunctor.map f := by
  change SSet.sSetCGWHAdj.homEquiv _ _ (realizationUnitIso.hom ≫ (g ≫ f)) = _
  rw [← Category.assoc, Adjunction.homEquiv_naturality_right]
  rfl

/-- The natural unit-Hom function is the actual canonical singular lax-unit map. -/
theorem underlyingSingularUnitHomEquiv_apply
    (Y : CGWH.{u, v}) (f : 𝟙_ CGWH.{u, v} ⟶ Y) :
    underlyingSingularUnitHomEquiv Y f =
      Functor.LaxMonoidal.ε underlyingSingularFunctor ≫ underlyingSingularFunctor.map f := by
  have hTerminal : IsTerminal (underlyingSingularFunctor.obj (𝟙_ CGWH.{u, v})) :=
    CartesianMonoidalCategory.isTerminalTensorUnit.isTerminalObj underlyingSingularFunctor
  have hUnit : underlyingSingularUnitHomEquiv (𝟙_ CGWH.{u, v}) (𝟙 _) =
      Functor.LaxMonoidal.ε underlyingSingularFunctor := hTerminal.hom_ext _ _
  simpa only [Category.id_comp, hUnit] using
    underlyingSingularUnitHomEquiv_naturality f (𝟙 (𝟙_ CGWH.{u, v}))

/-- The native free-basepoint adjunction gives the complete forgetful unit-Hom equivalence. -/
def forgetUnitHomEquiv (Y : PointedCGWH.{u, v}) :
    (𝟙_ PointedCGWH.{u, v} ⟶ Y) ≃ (𝟙_ CGWH.{u, v} ⟶ Y.right) :=
  ((Functor.Monoidal.εIso (Under.costar CGWH.point)).homCongr (Iso.refl Y)).trans
    ((Under.costarAdjForget CGWH.point).homEquiv (𝟙_ CGWH.{u, v}) Y)

/-- The complete forgetful unit-Hom function is its actual native right-adjoint lax unit. -/
theorem forgetUnitHomEquiv_apply
    (Y : PointedCGWH.{u, v}) (f : 𝟙_ PointedCGWH.{u, v} ⟶ Y) :
    forgetUnitHomEquiv Y f =
      Functor.LaxMonoidal.ε (Under.forget CGWH.point) ≫ (Under.forget CGWH.point).map f := by
  change (Under.costarAdjForget CGWH.point).homEquiv _ _
    (Functor.OplaxMonoidal.η (Under.costar CGWH.point) ≫ f) = _
  rw [Adjunction.homEquiv_naturality_right]
  rfl

/-- The original pointed singular functor preserves the full unit-Hom type by both adjunctions. -/
def unitHomEquiv (Y : PointedCGWH.{u, v}) :
    (𝟙_ PointedCGWH.{u, v} ⟶ Y) ≃ (𝟙_ SSet.{v} ⟶ singularFunctor.obj Y) :=
  (forgetUnitHomEquiv Y).trans (underlyingSingularUnitHomEquiv Y.right)

/-- Both original unit-Hom functions compose to the actual whole pointed singular function. -/
theorem unitHomEquiv_apply (Y : PointedCGWH.{u, v})
    (f : 𝟙_ PointedCGWH.{u, v} ⟶ Y) :
    unitHomEquiv Y f = Functor.LaxMonoidal.ε singularFunctor ≫ singularFunctor.map f := by
  change underlyingSingularUnitHomEquiv Y.right (forgetUnitHomEquiv Y f) = _
  rw [forgetUnitHomEquiv_apply, underlyingSingularUnitHomEquiv_apply,
    underlyingSingularFunctor.map_comp]
  rfl

/-- Singularization of the original intrinsic based enrichment is on the same native category. -/
@[instance_reducible]
def simplicialCategory : SimplicialCategory PointedCGWH.{u, v} :=
  TransportEnrichment.enrichedOrdinaryCategory PointedCGWH.{u, v}
    singularFunctor unitHomEquiv unitHomEquiv_apply

section EnrichedSource

universe uC vC
variable (C : Type uC) [Category.{vC} C] [EnrichedOrdinaryCategory PointedCGWH.{u, v} C]

/-- The same native singular functor changes any pointed enriched
ordinary source to simplicial sets. -/
@[instance_reducible]
def enrichedOrdinaryCategory : EnrichedOrdinaryCategory SSet.{v} C :=
  TransportEnrichment.enrichedOrdinaryCategory C singularFunctor unitHomEquiv unitHomEquiv_apply

attribute [local instance] enrichedOrdinaryCategory

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Singularization retains the complete original source whiskering map of an enriched category. -/
theorem whiskerRight {X X' : C} (f : X ⟶ X') (Y : C) :
    eHomWhiskerRight SSet.{v} f Y =
      singularFunctor.map (eHomWhiskerRight PointedCGWH.{u, v} f Y) := by
  change (λ_ (singularFunctor.obj (X' ⟶[PointedCGWH.{u, v}] Y))).inv ≫
    (unitHomEquiv (X ⟶[PointedCGWH.{u, v}] X') (eHomEquiv PointedCGWH.{u, v} f) ▷ _) ≫
    (Functor.LaxMonoidal.μ singularFunctor _ _ ≫
      singularFunctor.map (eComp PointedCGWH.{u, v} X X' Y)) =
    singularFunctor.map ((λ_ (X' ⟶[PointedCGWH.{u, v}] Y)).inv ≫
      eHomEquiv PointedCGWH.{u, v} f ▷ _ ≫ eComp PointedCGWH.{u, v} X X' Y)
  rw [unitHomEquiv_apply]
  simp only [Functor.map_comp, MonoidalCategory.comp_whiskerRight, Category.assoc]
  rw [Functor.LaxMonoidal.μ_natural_left_assoc (F := singularFunctor.{u, v}),
    Functor.LaxMonoidal.left_unitality_inv_assoc (F := singularFunctor.{u, v})]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Singularization retains the complete original target whiskering map of an enriched category. -/
theorem whiskerLeft (X : C) {Y Y' : C} (g : Y ⟶ Y') :
    eHomWhiskerLeft SSet.{v} X g =
      singularFunctor.map (eHomWhiskerLeft PointedCGWH.{u, v} X g) := by
  change (ρ_ (singularFunctor.obj (X ⟶[PointedCGWH.{u, v}] Y))).inv ≫
    (_ ◁ unitHomEquiv (Y ⟶[PointedCGWH.{u, v}] Y') (eHomEquiv PointedCGWH.{u, v} g)) ≫
    (Functor.LaxMonoidal.μ singularFunctor _ _ ≫
      singularFunctor.map (eComp PointedCGWH.{u, v} X Y Y')) =
    singularFunctor.map ((ρ_ (X ⟶[PointedCGWH.{u, v}] Y)).inv ≫
      _ ◁ eHomEquiv PointedCGWH.{u, v} g ≫ eComp PointedCGWH.{u, v} X Y Y')
  rw [unitHomEquiv_apply]
  simp only [Functor.map_comp, MonoidalCategory.whiskerLeft_comp, Category.assoc]
  rw [Functor.LaxMonoidal.μ_natural_right_assoc (F := singularFunctor.{u, v}),
    Functor.LaxMonoidal.right_unitality_inv_assoc (F := singularFunctor.{u, v})]

end EnrichedSource

end PointedCGWH.NativeSimplicial

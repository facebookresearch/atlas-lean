/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
/-
Portions of this file are adapted from:

`StacksFrontier/Algebra/Category/ModuleCat/DiscreteTopology.lean`,
`StacksFrontier/Homology/Injectives/Module/ContinuousGroupModules.lean`,
`StacksFrontier/AlgebraicGeometry/EtaleCohomology/GroupCohomology/Continuous.lean`,
`StacksFrontier/AlgebraicGeometry/ContinuousCohomology/Basic.lean`
(AxiomMath/Stacks, revision `c496df0d9beea9deaeabcea8492605f9a0a2313b`); the source files carry
no individual copyright or author notice.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).

Modifications: the discrete continuous module category and its invariants are kept, and its
Mathlib injective-resolution derived realization is exposed; the comparison with the source's
`rightDerivedPlus` realization is a separate source-integration request.
-/
module

public import Mathlib.CategoryTheory.Abelian.Subcategory
public import Mathlib.CategoryTheory.Action.Continuous
public import Mathlib.CategoryTheory.Action.Limits
public import Mathlib.RepresentationTheory.Invariants
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.Algebra.Category.Grp.Abelian

/-!
# The discrete continuous module category used by Axiom

Objects and invariants are the actual source definitions, not an abstract
cohomology carrier. Enough injectives is not postulated as a global instance;
its source construction is recorded explicitly in the interoperability
requests. `derivedCohomology` is the native injective-resolution realization.
-/

@[expose] public noncomputable section

open CategoryTheory Limits ZeroObject

universe u v w

namespace DiscreteGModules

/-- The source's discrete module topology, available only in this scope. -/
scoped instance hasForget₂ModuleCatTopCat (R : Type u) [Ring R] :
    HasForget₂ (ModuleCat.{w} R) TopCat.{w} :=
  { forget₂ := forget (ModuleCat.{w} R) ⋙ TopCat.discrete
    forget_comp := rfl }

open scoped DiscreteGModules

/-- The source category of modules with a discrete continuous group action. -/
abbrev ContinuousModule (R : Type u) [Ring R]
    (G : Type v) [Group G] [TopologicalSpace G] :=
  DiscreteContAction (ModuleCat.{w} R) G

/-- Axiom's `ContinuousGModule` is the integer-coefficient specialization. -/
abbrev ContinuousGModule (G : Type v) [Group G] [TopologicalSpace G] :=
  ContinuousModule.{0, v, w} ℤ G

scoped instance actionDiscreteTopology (R : Type u) [Ring R]
    (G : Type v) [Group G] [TopologicalSpace G]
    (X : Action (ModuleCat.{w} R) G) :
    DiscreteTopology ((forget₂ (Action (ModuleCat.{w} R) G) TopCat).obj X) := ⟨rfl⟩

section Abelian

variable (R : Type u) [Ring R] (G : Type v) [Group G] [TopologicalSpace G]

/-- The underlying topological space of an action on an `R`-module is nonempty: it contains
`0`. -/
instance actionNonempty (X : Action (ModuleCat.{w} R) G) :
    Nonempty ((forget₂ (Action (ModuleCat.{w} R) G) TopCat).obj X) := ⟨(0 : X.V)⟩

/-- A map into a discrete space whose composition with an injection is continuous is itself
continuous: an injection into a discrete space has a continuous left inverse. -/
lemma continuous_of_comp_injective_discrete {X Y : Type w} {Z : Type v}
    [Nonempty X] [TopologicalSpace X] [TopologicalSpace Y] [DiscreteTopology Y]
    [TopologicalSpace Z] (f : X → Y) (hf : Function.Injective f) {g : Z → X}
    (h : Continuous (f ∘ g)) : Continuous g := by
  obtain ⟨s, hs⟩ := hf.hasLeftInverse
  convert (continuous_of_discreteTopology : Continuous s).comp h using 1
  ext z
  exact (hs _).symm

/-- Continuous actions on `R`-modules are closed under subobjects. -/
instance continuousClosedUnderSubobjects :
    ObjectProperty.IsClosedUnderSubobjects
      (Action.IsContinuous (V := ModuleCat.{w} R) (G := G)) where
  prop_of_mono {X Y} f _ hY := by
    have : Mono f.hom := inferInstanceAs (Mono ((Action.forget _ G).map f))
    have hf := (ModuleCat.mono_iff_injective f.hom).mp inferInstance
    rw [Action.isContinuous_def, continuous_prod_of_discrete_right]
    intro x
    apply continuous_of_comp_injective_discrete
      (Y := (forget₂ (Action (ModuleCat.{w} R) G) TopCat).obj Y)
      (fun y : (forget₂ (Action (ModuleCat.{w} R) G) TopCat).obj X => f.hom y) hf
    have h := (continuous_prod_of_discrete_right.mp
      (Action.isContinuous_def Y |>.mp hY)) (f.hom x)
    exact h.congr fun g => (ConcreteCategory.congr_hom (f.comm g) x).symm

/-- Continuous actions on `R`-modules are closed under quotients. -/
instance continuousClosedUnderQuotients :
    ObjectProperty.IsClosedUnderQuotients
      (Action.IsContinuous (V := ModuleCat.{w} R) (G := G)) where
  prop_of_epi {X Y} f _ hX := by
    have : Epi f.hom := inferInstanceAs (Epi ((Action.forget _ G).map f))
    have hf := (ModuleCat.epi_iff_surjective f.hom).mp inferInstance
    rw [Action.isContinuous_def, continuous_prod_of_discrete_right]
    intro y
    obtain ⟨x, rfl⟩ := hf y
    have h := (continuous_prod_of_discrete_right.mp
      (Action.isContinuous_def X |>.mp hX)) x
    have h' := (continuous_of_discreteTopology : Continuous
      (Y := (forget₂ (Action (ModuleCat.{w} R) G) TopCat).obj Y)
      (fun x : (forget₂ (Action (ModuleCat.{w} R) G) TopCat).obj X =>
        (f.hom x : (forget₂ (Action (ModuleCat.{w} R) G) TopCat).obj Y))).comp h
    exact h'.congr fun g => ConcreteCategory.congr_hom (f.comm g) x

/-- Continuous actions on `R`-modules are closed under finite products. -/
instance continuousClosedUnderFiniteProducts :
    ObjectProperty.IsClosedUnderFiniteProducts
      (Action.IsContinuous (V := ModuleCat.{w} R) (G := G)) where
  isClosedUnderLimitsOfShape J _ := ⟨by
    rintro X ⟨p⟩
    have hi := Concrete.to_product_injective_of_isLimit _
      (isLimitOfPreserves (Action.forget (ModuleCat.{w} R) G) p.isLimit)
    rw [Action.isContinuous_def, continuous_prod_of_discrete_right]
    intro x
    apply continuous_of_comp_injective_discrete
      (Y := ∀ j, (forget₂ (Action (ModuleCat.{w} R) G) TopCat).obj (p.diag.obj j))
      (fun y : (forget₂ (Action (ModuleCat.{w} R) G) TopCat).obj X =>
        (fun j => (p.π.app j).hom y :
          ∀ j, (forget₂ (Action (ModuleCat.{w} R) G) TopCat).obj (p.diag.obj j))) hi
    apply continuous_pi
    intro j
    have h := (continuous_prod_of_discrete_right.mp
      (Action.isContinuous_def (p.diag.obj j) |>.mp (p.prop_diag_obj j)))
      ((p.π.app j).hom x)
    exact h.congr fun g => (ConcreteCategory.congr_hom ((p.π.app j).comm g) x).symm⟩

/-- The zero action on an `R`-module is continuous. -/
instance continuousContainsZero :
    ObjectProperty.ContainsZero
      (Action.IsContinuous (V := ModuleCat.{w} R) (G := G)) where
  exists_zero := by
    refine ⟨(0 : Action (ModuleCat.{w} R) G), isZero_zero _, ?_⟩
    have hZ := (Action.forget (ModuleCat.{w} R) G).map_isZero
      (isZero_zero (Action (ModuleCat.{w} R) G))
    have hsub : Subsingleton (0 : Action (ModuleCat.{w} R) G).V :=
      ModuleCat.isZero_iff_subsingleton.mp hZ
    refine ⟨(continuous_const
      (Y := (forget₂ (Action (ModuleCat.{w} R) G) TopCat).obj
        (0 : Action (ModuleCat.{w} R) G))
      (y := (0 : (0 : Action (ModuleCat.{w} R) G).V))).congr fun _ => ?_⟩
    exact hsub.elim _ _

/-- Continuous actions on `R`-modules form an abelian category: they are a full subcategory of
`Action (ModuleCat R) G` containing zero and closed under kernels, cokernels and finite
products. -/
instance contActionAbelian : Abelian (ContAction (ModuleCat.{w} R) G) :=
  inferInstanceAs (Abelian (ObjectProperty.FullSubcategory
    (Action.IsContinuous (V := ModuleCat.{w} R) (G := G))))

/-- Discrete continuous actions on `R`-modules are closed under subobjects. -/
instance discreteClosedUnderSubobjects :
    ObjectProperty.IsClosedUnderSubobjects
      (ContAction.IsDiscrete (V := ModuleCat.{w} R) (G := G)) where
  prop_of_mono _ _ _ := ⟨rfl⟩

/-- Discrete continuous actions on `R`-modules are closed under quotients. -/
instance discreteClosedUnderQuotients :
    ObjectProperty.IsClosedUnderQuotients
      (ContAction.IsDiscrete (V := ModuleCat.{w} R) (G := G)) where
  prop_of_epi _ _ _ := ⟨rfl⟩

/-- Discrete continuous actions on `R`-modules are closed under finite products. -/
instance discreteClosedUnderFiniteProducts :
    ObjectProperty.IsClosedUnderFiniteProducts
      (ContAction.IsDiscrete (V := ModuleCat.{w} R) (G := G)) where
  isClosedUnderLimitsOfShape _ _ := ⟨fun _ _ => ⟨rfl⟩⟩

/-- The zero continuous action on an `R`-module is discrete. -/
instance discreteContainsZero :
    ObjectProperty.ContainsZero
      (ContAction.IsDiscrete (V := ModuleCat.{w} R) (G := G)) where
  exists_zero := ⟨0, isZero_zero _, ⟨rfl⟩⟩

/-- The abelian structure on continuous discrete `R`-`G`-modules, viewed as the full subcategory
of `ContAction (ModuleCat R) G` of discrete objects. -/
@[instance_reducible]
def fullSubcategoryAbelian :
    Abelian (ObjectProperty.FullSubcategory
      (ContAction.IsDiscrete (V := ModuleCat.{w} R) (G := G))) := inferInstance

/-- Continuous discrete `R`-`G`-modules form an abelian category, with the ring, group and
coefficient universes independent. -/
instance abelian : Abelian (ContinuousModule.{u, v, w} R G) :=
  fullSubcategoryAbelian.{u, v, w} R G


end Abelian

/-- The `G`-invariants functor `M ↦ M^G` on discrete continuous modules, valued in abelian groups.
It is left exact, but not exact in general. -/
abbrev invariantsFunctor (G : Type v) [Group G] [TopologicalSpace G] :
    ContinuousGModule.{v, w} G ⥤ AddCommGrpCat.{w} :=
  ObjectProperty.ι _ ⋙ ObjectProperty.ι _ ⋙ Rep.ActionToRep ℤ G ⋙
    Rep.invariantsFunctor ℤ G ⋙ forget₂ (ModuleCat.{w} ℤ) AddCommGrpCat.{w}

instance (G : Type v) [Group G] [TopologicalSpace G] :
    (invariantsFunctor.{v, w} G).Additive where
  map_add := by
    intros
    ext
    rfl

/-- Derived invariants in Mathlib's actual injective-resolution model.
A source provider must install the proved enough-injectives construction. -/
abbrev derivedCohomology (G : Type v) [Group G] [TopologicalSpace G]
    [EnoughInjectives (ContinuousGModule.{v, w} G)] (n : ℕ) :
    ContinuousGModule.{v, w} G ⥤ AddCommGrpCat.{w} :=
  (invariantsFunctor G).rightDerived n

end DiscreteGModules

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.CategoryTheory.DGQuasiFunctorModels
public import MathlibExt.CategoryTheory.PerfectDGModuleModels
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone

/-!
# Actual DG-module shifts, cones and enriched Hom maps

Shift and cone values are the native cochain shifts and mapping cones
at every module point. Every homogeneous module action is fixed,
including the shift sign and the signed first cone block. These models
retain the enhanced module Hom complexes, without substituting ordinary
categorical pullbacks in a homotopy category.

References: Keller, Deriving DG categories, §§2--3;
Brav--Dyckerhoff, arXiv:1606.00619v1, §§2.1/4.2.
The underlying DG/cochain bodies retain their source notices in DGSource.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.CategoryTheory.DGModuleConeShiftModels

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite
open _root_.CategoryTheory.MonoidalCategory
open MathlibExt.DGSource
open MathlibExt.CategoryTheory.DGModelContracts
open MathlibExt.CategoryTheory.DGQuasiFunctorModels
open CochainComplex.HomComplex

universe u
variable {k : Type u} [CommRing k]

/-- The actual closed degree-zero cochain of a DG-module morphism. -/
def moduleCycle {C : DGCat k} {M N : RightModule k C} (f : M ⟶ N) : DGHom k 0 M N :=
  (DGFunctor.homEquivDGCycles k M N f).val

/-- A module morphism supplies its literal enriched unit map. -/
def moduleUnitMap {C : DGCat k} {M N : RightModule k C} (f : M ⟶ N) :
    𝟙_ (Cochains k) ⟶ dgHomComplex k M N :=
  ForgetEnrichment.homTo (Cochains k)
    (dgClosedHomOf k (moduleCycle f) (DGFunctor.homEquivDGCycles k M N f).property)

/-- Native enriched composition computes the actual Hom precomposition map. -/
def homPrecompose {C : DGCat k} {M N : RightModule k C} (f : M ⟶ N) (V : RightModule k C) :
    dgHomComplex k N V ⟶ dgHomComplex k M V :=
  (λ_ (dgHomComplex k N V)).inv ≫ (moduleUnitMap f ⊗ₘ 𝟙 _) ≫ eComp (Cochains k) M N V

/-- Native enriched composition computes the actual Hom postcomposition map. -/
def homPostcompose {C : DGCat k} (M : RightModule k C) {N V : RightModule k C} (f : N ⟶ V) :
    dgHomComplex k M N ⟶ dgHomComplex k M V :=
  (ρ_ (dgHomComplex k M N)).inv ≫ (𝟙 _ ⊗ₘ moduleUnitMap f) ≫ eComp (Cochains k) M N V

/-- The actual shifted module action has the source sign (-1)^(n p). -/
def shiftActionDegree {C : DGCat k} (M : RightModule k C) (n : ℤ)
    (x y : Cᵒᵖ) (p r : ℤ) (a : DGHom k p x y) :
    (M.toEnrichedFunctor.obj x)⟦n⟧.X r ⟶ (M.toEnrichedFunctor.obj y)⟦n⟧.X (r + p) :=
  (n * p).negOnePow •
    ((M.toEnrichedFunctor.obj x).shiftFunctorObjXIso n r (r + n) rfl).hom ≫
      (M.toEnrichedFunctor.dgMap p a : Cochain _ _ p).v (r + n) (r + p + n) (by omega) ≫
      ((M.toEnrichedFunctor.obj y).shiftFunctorObjXIso n (r + p) (r + p + n) rfl).inv

/-- An actual shifted module preserves all values and every homogeneous action. -/
structure ModuleShiftModel {C : DGCat k} (M : RightModule k C) (n : ℤ) where
  module : RightModule k C
  valueIso : ∀ x : Cᵒᵖ, module.toEnrichedFunctor.obj x ≅ (M.toEnrichedFunctor.obj x)⟦n⟧
  action_eq : ∀ (x y : Cᵒᵖ) (p r : ℤ) (a : DGHom k p x y),
    (module.toEnrichedFunctor.dgMap p a : Cochain _ _ p).v r (r + p) rfl ≫
      (valueIso y).hom.f (r + p) =
      (valueIso x).hom.f r ≫ shiftActionDegree M n x y p r a

/-- The shifted projective module retains its actual cofibrancy test. -/
structure CofibrantShiftModel {C : DGCat k} (M : DGDerivedModules k C) (n : ℤ)
    extends ModuleShiftModel M.obj n where
  cofibrant : IsCofibrantModule module

/-- The native cone action is diagonal, with the actual sign on its shifted source block. -/
def coneActionDegree {C : DGCat k} {M N : RightModule k C} (f : M ⟶ N)
    (x y : Cᵒᵖ) (p r : ℤ) (a : DGHom k p x y) :
    (CochainComplex.mappingCone (moduleComponent f x)).X r ⟶
      (CochainComplex.mappingCone (moduleComponent f y)).X (r + p) :=
  (p.negOnePow • (CochainComplex.mappingCone.fst (moduleComponent f x)).val.v r (r + 1) rfl) ≫
      (M.toEnrichedFunctor.dgMap p a : Cochain _ _ p).v (r + 1) (r + p + 1) (by omega) ≫
      (CochainComplex.mappingCone.inl (moduleComponent f y)).v
        (r + p + 1) (r + p) (by omega) +
    (CochainComplex.mappingCone.snd (moduleComponent f x)).v r r (by omega) ≫
      (N.toEnrichedFunctor.dgMap p a : Cochain _ _ p).v r (r + p) rfl ≫
      (CochainComplex.mappingCone.inr (moduleComponent f y)).f (r + p)

/-- The actual DG-module cone fixes both its cochain values and all module-arrow blocks. -/
structure ModuleConeModel {C : DGCat k} {M N : RightModule k C} (f : M ⟶ N) where
  module : RightModule k C
  valueIso : ∀ x : Cᵒᵖ,
    module.toEnrichedFunctor.obj x ≅ CochainComplex.mappingCone (moduleComponent f x)
  action_eq : ∀ (x y : Cᵒᵖ) (p r : ℤ) (a : DGHom k p x y),
    (module.toEnrichedFunctor.dgMap p a : Cochain _ _ p).v r (r + p) rfl ≫
      (valueIso y).hom.f (r + p) =
      (valueIso x).hom.f r ≫ coneActionDegree f x y p r a
  inclusion : N ⟶ module
  inclusion_eq : ∀ (x : Cᵒᵖ) (r : ℤ),
    (moduleComponent inclusion x).f r ≫ (valueIso x).hom.f r =
      (CochainComplex.mappingCone.inr (moduleComponent f x)).f r
  projection : DGHom k 1 module M
  projection_closed : dgDifferential k 1 projection = 0
  projection_eq : ∀ (x : Cᵒᵖ) (r : ℤ),
    (DGFunctor.dgApp k 1 x projection : Cochain _ _ 1).v r (r + 1) rfl =
      (valueIso x).hom.f r ≫ (CochainComplex.mappingCone.fst (moduleComponent f x)).val.v r (r + 1) rfl

/-- A cone of actual cofibrant modules is itself the projective cone model. -/
structure CofibrantConeModel {C : DGCat k} (M N : DGDerivedModules k C) (f : M.obj ⟶ N.obj)
    extends ModuleConeModel f where
  cofibrant : IsCofibrantModule module

/-- A closed homogeneous module map becomes its actual map to the shifted module. -/
structure ShiftedModuleMapModel {C : DGCat k} {M N : RightModule k C} (n : ℤ)
    (a : DGHom k n M N) (closed : dgDifferential k n a = 0) (S : ModuleShiftModel N n) where
  map : M ⟶ S.module
  component_eq : ∀ (x : Cᵒᵖ) (r : ℤ),
    (moduleComponent map x).f r ≫ (S.valueIso x).hom.f r ≫
      ((N.toEnrichedFunctor.obj x).shiftFunctorObjXIso n r (r + n) rfl).hom =
      (DGFunctor.dgApp k n x a : Cochain _ _ n).v r (r + n) rfl

/-- An actual module homotopy equivalence keeps its inverse and both native degree -1 homotopies. -/
structure ModuleHomotopyEquivalence {C : DGCat k} {M N : RightModule k C} (f : M ⟶ N) where
  inverse : N ⟶ M
  left : DGHom k (-1) M M
  right : DGHom k (-1) N N
  left_eq : dgDifferential k (-1) left = moduleCycle (f ≫ inverse) - dgId k M
  right_eq : dgDifferential k (-1) right = moduleCycle (inverse ≫ f) - dgId k N

/-- The actual shifted module morphism is fixed by the native cochain shift at every point. -/
structure ModuleShiftMapModel {C : DGCat k} {M N : RightModule k C} (f : M ⟶ N) (n : ℤ)
    (SM : ModuleShiftModel M n) (SN : ModuleShiftModel N n) where
  map : SM.module ⟶ SN.module
  normalized : ∀ x : Cᵒᵖ,
    moduleComponent map x ≫ (SN.valueIso x).hom =
      (SM.valueIso x).hom ≫ (moduleComponent f x)⟦n⟧'

end MathlibExt.CategoryTheory.DGModuleConeShiftModels

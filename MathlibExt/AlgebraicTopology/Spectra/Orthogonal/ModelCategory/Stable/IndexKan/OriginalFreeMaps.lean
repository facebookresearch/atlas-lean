/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.IndexStabilizationTransport
import MathlibExt.CategoryTheory.Enriched.LeftKanFreeComparison

/-!
# Full original free maps of native orthogonal prolongation

The selected free/Lan isomorphism is the original native Kan
isomorphism. Its whole unit characteristic identifies it with the
reviewed explicit coend transpose. Consequently every original
coefficient morphism and every full source Hom map retains both actual
comparison directions.

The existing all-coefficient stabilization transport gives the exact
original Lan map, including its original coefficient-to-Hom inclusion.
Both mapped free isomorphisms and their complete map squares are then
retained in the actual native level homotopy category.
-/

set_option autoImplicit false
noncomputable section
universe u v

open CategoryTheory CategoryTheory.Limits MonoidalCategory HomotopicalAlgebra
open CategoryTheory.EnrichedFunctorCat
open scoped CGWH.limits CGWH.modelCategory MonoidalClosed

namespace PointedCGWH.Spectra.Orthogonal.IndexKan

open HomotopicalAlgebra.EnrichedProjective.Native
open HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK
open HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK.Actual
open HomotopicalAlgebra.EnrichedProjective.Native.IndexStabilizationTransport

attribute [local instance] PointedCGWH.EnrichedMapping.hasSmallLimits
  MonoidalClosed.enrichedCategorySelf

private abbrev O := CategoryTheory.Spectra.OrthogonalOperatorIndex.{u, v}
private abbrev OC := OrthogonalCarrier.{u, v}

variable {A : Type} [EnrichedCategory PointedCGWH.{u, v} A]

/-- The same complete original native Kan isomorphism on every free coefficient. -/
def originalFreeIso (j : EnrichedFunctor PointedCGWH.{u, v} A O.{u, v}) (a : A) :
    Free.functor (V := PointedCGWH.{u, v}) a ⋙ EnrichedFunctorCat.leftKan j ≅
      Free.functor (V := PointedCGWH.{u, v}) (j.obj a) :=
  HomotopicalAlgebra.EnrichedProjective.Native.Kan.leftKanFreeIso j a

/-- The original comparison is retained as a whole isomorphism, including every map field. -/
theorem originalFreeIso_eq_native
    (j : EnrichedFunctor PointedCGWH.{u, v} A O.{u, v}) (a : A) :
    originalFreeIso j a =
      HomotopicalAlgebra.EnrichedProjective.Native.Kan.leftKanFreeIso j a := rfl

/-- The two original units retain the same full source identity coefficient. -/
theorem originalFreeIso_unit
    (j : EnrichedFunctor PointedCGWH.{u, v} A O.{u, v}) (a : A) (K : PointedCGWH.{u, v}) :
    (Free.adjunction (V := PointedCGWH.{u, v}) a).unit.app K ≫
        component (V := PointedCGWH.{u, v})
          ((EnrichedFunctorCat.leftKanRestrictionAdjunction j).unit.app
            (Free.object (V := PointedCGWH.{u, v}) a K)) a ≫
        component (V := PointedCGWH.{u, v}) ((originalFreeIso j a).hom.app K) (j.obj a) =
      (Free.adjunction (V := PointedCGWH.{u, v}) (j.obj a)).unit.app K :=
  HomotopicalAlgebra.EnrichedProjective.Native.Kan.leftKanFreeIso_unit j a K

/-- The original full free identity and coend counit retain the same entire composition. -/
theorem originalFreeIso_counit
    (j : EnrichedFunctor PointedCGWH.{u, v} A O.{u, v}) (a : A) (E : OC.{u, v}) :
    (originalFreeIso j a).hom.app (E.toEnrichedFunctor.obj (j.obj a)) ≫
        (Free.adjunction (V := PointedCGWH.{u, v}) (j.obj a)).counit.app E =
      (EnrichedFunctorCat.leftKan j).map ((Free.adjunction (V := PointedCGWH.{u, v}) a).counit.app
        ((EnrichedFunctorCat.restriction j).obj E)) ≫
          (EnrichedFunctorCat.leftKanRestrictionAdjunction j).counit.app E :=
  HomotopicalAlgebra.EnrichedProjective.Native.Kan.leftKanFreeIso_counit j a E

/-- Every source component retains the original coefficient-tensored full enriched Hom map. -/
theorem originalFreeIso_full_component
    (j : EnrichedFunctor PointedCGWH.{u, v} A O.{u, v}) (a b : A)
    (K : PointedCGWH.{u, v}) :
    component (V := PointedCGWH.{u, v})
        ((EnrichedFunctorCat.leftKanRestrictionAdjunction j).unit.app
          (Free.object (V := PointedCGWH.{u, v}) a K)) b ≫
      component (V := PointedCGWH.{u, v}) ((originalFreeIso j a).hom.app K) (j.obj b) =
        K ◁ j.map a b :=
  leftKanFreeIso_full_component j a b K

/-- The whole original free unit evaluates the actual enriched source identity. -/
theorem originalFreeUnit_app (a : A) (K : PointedCGWH.{u, v}) :
    (Free.adjunction (V := PointedCGWH.{u, v}) a).unit.app K =
      (ρ_ K).inv ≫ K ◁ eId PointedCGWH.{u, v} a := by
  have h := (Free.adjunction (V := PointedCGWH.{u, v}) a).homEquiv_id K
  rw [Free.adjunction_homEquiv (V := PointedCGWH.{u, v}) a] at h
  change (ρ_ K).inv ≫ K ◁ eId PointedCGWH.{u, v} a ≫
    component (V := PointedCGWH.{u, v}) (𝟙 (Free.object (V := PointedCGWH.{u, v}) a K)) a =
      (Free.adjunction (V := PointedCGWH.{u, v}) a).unit.app K at h
  rw [component_id, Category.comp_id] at h
  exact h.symm

/-- The whole original selected free comparison is the reviewed explicit coend transpose. -/
theorem originalFreeIso_eq_explicit
    (j : EnrichedFunctor PointedCGWH.{u, v} A O.{u, v}) (a : A) :
    originalFreeIso j a = LeftKanFreeComparison.functorIso j a := by
  apply Iso.ext
  apply NatTrans.ext
  apply funext
  intro K
  let Y := Free.object (V := PointedCGWH.{u, v}) (j.obj a) K
  let e := LeftKanFreeComparison.homEquiv j a K Y
  apply e.injective
  have hNative : e ((originalFreeIso j a).hom.app K) =
      (Free.adjunction (V := PointedCGWH.{u, v}) (j.obj a)).unit.app K := by
    change LeftKanFreeComparison.homEquiv j a K Y ((originalFreeIso j a).hom.app K) = _
    rw [LeftKanFreeComparison.homEquiv_apply, Free.evaluate, component_comp,
      restrictionMap_component, leftKanUnit_component]
    let F := Free.object (V := PointedCGWH.{u, v}) a K
    let L := (EnrichedFunctorCat.leftKan j).obj F
    let p : K ⟶ F.toEnrichedFunctor.obj a :=
      (ρ_ K).inv ≫ K ◁ eId PointedCGWH.{u, v} a
    let t : F.toEnrichedFunctor.obj a ⟶ L.toEnrichedFunctor.obj (j.obj a) :=
      leftKanUnitComponent j F a
    let v : L.toEnrichedFunctor.obj (j.obj a) ⟶ Y.toEnrichedFunctor.obj (j.obj a) :=
      component (V := PointedCGWH.{u, v}) ((originalFreeIso j a).hom.app K) (j.obj a)
    have hs : (Free.adjunction (V := PointedCGWH.{u, v}) a).unit.app K = p :=
      originalFreeUnit_app a K
    have ht : component (V := PointedCGWH.{u, v})
        ((EnrichedFunctorCat.leftKanRestrictionAdjunction j).unit.app F) a = t :=
      leftKanRestrictionAdjunction_unit_component j F a
    have hw := congrArg₂
      (fun (s : K ⟶ F.toEnrichedFunctor.obj a)
        (u : F.toEnrichedFunctor.obj a ⟶ L.toEnrichedFunctor.obj (j.obj a)) => s ≫ u ≫ v)
      hs ht
    have hn : (Free.adjunction (V := PointedCGWH.{u, v}) a).unit.app K ≫
        component (V := PointedCGWH.{u, v})
          ((EnrichedFunctorCat.leftKanRestrictionAdjunction j).unit.app F) a ≫ v =
      (Free.adjunction (V := PointedCGWH.{u, v}) (j.obj a)).unit.app K :=
      originalFreeIso_unit j a K
    exact (Category.assoc (ρ_ K).inv (K ◁ eId PointedCGWH.{u, v} a) (t ≫ v)).symm.trans
      (hw.symm.trans hn)
  have hExplicit : e ((LeftKanFreeComparison.functorIso j a).hom.app K) =
      (Free.adjunction (V := PointedCGWH.{u, v}) (j.obj a)).unit.app K := by
    rw [LeftKanFreeComparison.functorIso_hom_app]
    change LeftKanFreeComparison.homEquiv j a K Y (LeftKanFreeComparison.hom j a K) = _
    rw [LeftKanFreeComparison.homEquiv_hom]
    rw [originalFreeUnit_app (j.obj a) K]
    change (ρ_ K).inv ≫ K ◁ eId PointedCGWH.{u, v} (j.obj a) ≫
      component (V := PointedCGWH.{u, v}) (𝟙 Y) (j.obj a) = _
    rw [component_id, Category.comp_id]
  exact hNative.trans hExplicit.symm

/-- The whole forward map is the original Kan transpose of the actual full Hom transformation. -/
theorem originalFreeIso_hom
    (j : EnrichedFunctor PointedCGWH.{u, v} A O.{u, v}) (a : A) (K : PointedCGWH.{u, v}) :
    (originalFreeIso j a).hom.app K = LeftKanFreeComparison.hom j a K := by
  rw [originalFreeIso_eq_explicit, LeftKanFreeComparison.functorIso_hom_app]

/-- The whole inverse is the actual original free extension of the evaluated coend unit. -/
theorem originalFreeIso_inv
    (j : EnrichedFunctor PointedCGWH.{u, v} A O.{u, v}) (a : A) (K : PointedCGWH.{u, v}) :
    (originalFreeIso j a).inv.app K = LeftKanFreeComparison.inv j a K := by
  rw [originalFreeIso_eq_explicit, LeftKanFreeComparison.functorIso_inv_app]

/-- Every original coefficient map preserves the whole original forward coend comparison. -/
theorem originalFreeIso_coefficient
    (j : EnrichedFunctor PointedCGWH.{u, v} A O.{u, v}) (a : A)
    {K T : PointedCGWH.{u, v}} (f : K ⟶ T) :
    (EnrichedFunctorCat.leftKan j).map (Free.coefficientMap a f) ≫ (originalFreeIso j a).hom.app T =
      (originalFreeIso j a).hom.app K ≫ Free.coefficientMap (j.obj a) f :=
  (originalFreeIso j a).hom.naturality f

/-- Every original coefficient map preserves the actual inverse extension direction. -/
theorem originalFreeIso_inv_coefficient
    (j : EnrichedFunctor PointedCGWH.{u, v} A O.{u, v}) (a : A)
    {K T : PointedCGWH.{u, v}} (f : K ⟶ T) :
    Free.coefficientMap (j.obj a) f ≫ (originalFreeIso j a).inv.app T =
      (originalFreeIso j a).inv.app K ≫
        (EnrichedFunctorCat.leftKan j).map (Free.coefficientMap a f) :=
  (originalFreeIso j a).inv.naturality f

/-- Every whole contravariant source Hom point retains the original full index Hom map. -/
theorem originalFreeIso_source
    (j : EnrichedFunctor PointedCGWH.{u, v} A O.{u, v}) {a b : A}
    (e : 𝟙_ PointedCGWH.{u, v} ⟶ (a ⟶[PointedCGWH.{u, v}] b))
    (K : PointedCGWH.{u, v}) :
    (EnrichedFunctorCat.leftKan j).map (Free.sourceMap e K) ≫ (originalFreeIso j a).hom.app K =
      (originalFreeIso j b).hom.app K ≫ Free.sourceMap (e ≫ j.map a b) K := by
  rw [originalFreeIso_hom, originalFreeIso_hom]
  exact LeftKanFreeComparison.hom_source j e K

/-- The complete inverse source square retains the same entire original source Hom point. -/
theorem originalFreeIso_inv_source
    (j : EnrichedFunctor PointedCGWH.{u, v} A O.{u, v}) {a b : A}
    (e : 𝟙_ PointedCGWH.{u, v} ⟶ (a ⟶[PointedCGWH.{u, v}] b))
    (K : PointedCGWH.{u, v}) :
    Free.sourceMap (e ≫ j.map a b) K ≫ (originalFreeIso j a).inv.app K =
      (originalFreeIso j b).inv.app K ≫
        (EnrichedFunctorCat.leftKan j).map (Free.sourceMap e K) := by
  rw [originalFreeIso_inv, originalFreeIso_inv]
  exact LeftKanFreeComparison.inv_source j e K

/-- Every full original coefficient-to-Hom inclusion retains its actual original Lan map. -/
theorem originalFreeIso_stabilization
    (j : EnrichedFunctor PointedCGWH.{u, v} A O.{u, v}) (a b : A)
    (K : PointedCGWH.{u, v}) (D : K ⟶ (a ⟶[PointedCGWH.{u, v}] b)) :
    (EnrichedFunctorCat.leftKan j).map (CurrentFree.stabilization a b K D) ≫
        (originalFreeIso j a).hom.app (𝟙_ PointedCGWH.{u, v}) =
      (originalFreeIso j b).hom.app K ≫
        CurrentFree.stabilization (j.obj a) (j.obj b) K (D ≫ j.map a b) :=
  leftKan_stabilization j a b K D

/-- Both whole free maps give the actual Arrow isomorphism for every original inclusion. -/
def originalStabilizationArrowIso
    (j : EnrichedFunctor PointedCGWH.{u, v} A O.{u, v}) (a b : A)
    (K : PointedCGWH.{u, v}) (D : K ⟶ (a ⟶[PointedCGWH.{u, v}] b)) :
    Arrow.mk ((EnrichedFunctorCat.leftKan j).map (CurrentFree.stabilization a b K D)) ≅
      Arrow.mk (CurrentFree.stabilization (j.obj a) (j.obj b) K (D ≫ j.map a b)) :=
  Arrow.isoMk ((originalFreeIso j b).app K)
    ((originalFreeIso j a).app (𝟙_ PointedCGWH.{u, v}))
      (originalFreeIso_stabilization j a b K D).symm

variable [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]
attribute [local instance] HomotopicalAlgebra.EnrichedProjective.Native.modelCategory

private abbrev HO := toHomotopyCategory OC.{u, v}

/-- The original level Ho carries the same whole original native free isomorphism. -/
def originalFreeHoIso (j : EnrichedFunctor PointedCGWH.{u, v} A O.{u, v})
    (a : A) (K : PointedCGWH.{u, v}) :
    HO.obj ((EnrichedFunctorCat.leftKan j).obj
        (Free.object (V := PointedCGWH.{u, v}) a K)) ≅
      HO.obj (Free.object (V := PointedCGWH.{u, v}) (j.obj a) K) :=
  HO.mapIso ((originalFreeIso j a).app K)

/-- The forward level Ho map is the same entire original free/coend comparison map. -/
theorem originalFreeHoIso_hom
    (j : EnrichedFunctor PointedCGWH.{u, v} A O.{u, v}) (a : A) (K : PointedCGWH.{u, v}) :
    (originalFreeHoIso j a K).hom = HO.map ((originalFreeIso j a).hom.app K) := rfl

/-- The inverse level Ho map is the same actual original inverse coend/free transformation. -/
theorem originalFreeHoIso_inv
    (j : EnrichedFunctor PointedCGWH.{u, v} A O.{u, v}) (a : A) (K : PointedCGWH.{u, v}) :
    (originalFreeHoIso j a K).inv = HO.map ((originalFreeIso j a).inv.app K) := rfl

/-- Every full coefficient map retains both actual original free Ho comparison maps. -/
theorem originalFreeHoIso_coefficient
    (j : EnrichedFunctor PointedCGWH.{u, v} A O.{u, v}) (a : A)
    {K T : PointedCGWH.{u, v}} (f : K ⟶ T) :
    HO.map ((EnrichedFunctorCat.leftKan j).map (Free.coefficientMap a f)) ≫
        (originalFreeHoIso j a T).hom =
      (originalFreeHoIso j a K).hom ≫ HO.map (Free.coefficientMap (j.obj a) f) := by
  rw [originalFreeHoIso_hom, originalFreeHoIso_hom, ← HO.map_comp, ← HO.map_comp]
  exact congrArg (fun q => HO.map q) (originalFreeIso_coefficient j a f)

/-- The inverse coefficient maps retain the whole original free Ho source square. -/
theorem originalFreeHoIso_inv_coefficient
    (j : EnrichedFunctor PointedCGWH.{u, v} A O.{u, v}) (a : A)
    {K T : PointedCGWH.{u, v}} (f : K ⟶ T) :
    HO.map (Free.coefficientMap (j.obj a) f) ≫ (originalFreeHoIso j a T).inv =
      (originalFreeHoIso j a K).inv ≫
        HO.map ((EnrichedFunctorCat.leftKan j).map (Free.coefficientMap a f)) := by
  rw [originalFreeHoIso_inv, originalFreeHoIso_inv, ← HO.map_comp, ← HO.map_comp]
  exact congrArg (fun q => HO.map q) (originalFreeIso_inv_coefficient j a f)

/-- Every actual full source Hom point retains the same original forward square in level Ho. -/
theorem originalFreeHoIso_source
    (j : EnrichedFunctor PointedCGWH.{u, v} A O.{u, v}) {a b : A}
    (e : 𝟙_ PointedCGWH.{u, v} ⟶ (a ⟶[PointedCGWH.{u, v}] b))
    (K : PointedCGWH.{u, v}) :
    HO.map ((EnrichedFunctorCat.leftKan j).map (Free.sourceMap e K)) ≫
        (originalFreeHoIso j a K).hom =
      (originalFreeHoIso j b K).hom ≫ HO.map (Free.sourceMap (e ≫ j.map a b) K) := by
  rw [originalFreeHoIso_hom, originalFreeHoIso_hom, ← HO.map_comp, ← HO.map_comp]
  exact congrArg (fun q => HO.map q) (originalFreeIso_source j e K)

/-- Every full source Hom point retains the actual inverse comparison direction in level Ho. -/
theorem originalFreeHoIso_inv_source
    (j : EnrichedFunctor PointedCGWH.{u, v} A O.{u, v}) {a b : A}
    (e : 𝟙_ PointedCGWH.{u, v} ⟶ (a ⟶[PointedCGWH.{u, v}] b))
    (K : PointedCGWH.{u, v}) :
    HO.map (Free.sourceMap (e ≫ j.map a b) K) ≫ (originalFreeHoIso j a K).inv =
      (originalFreeHoIso j b K).inv ≫
        HO.map ((EnrichedFunctorCat.leftKan j).map (Free.sourceMap e K)) := by
  rw [originalFreeHoIso_inv, originalFreeHoIso_inv, ← HO.map_comp, ← HO.map_comp]
  exact congrArg (fun q => HO.map q) (originalFreeIso_inv_source j e K)

/-- The original level Ho carries every actual coefficient and both original inclusion maps. -/
theorem originalFreeHoIso_stabilization
    (j : EnrichedFunctor PointedCGWH.{u, v} A O.{u, v}) (a b : A)
    (K : PointedCGWH.{u, v}) (D : K ⟶ (a ⟶[PointedCGWH.{u, v}] b)) :
    HO.map ((EnrichedFunctorCat.leftKan j).map (CurrentFree.stabilization a b K D)) ≫
        (originalFreeHoIso j a (𝟙_ PointedCGWH.{u, v})).hom =
      (originalFreeHoIso j b K).hom ≫
        HO.map (CurrentFree.stabilization (j.obj a) (j.obj b) K (D ≫ j.map a b)) := by
  rw [originalFreeHoIso_hom, originalFreeHoIso_hom, ← HO.map_comp, ← HO.map_comp]
  exact congrArg (fun q => HO.map q) (originalFreeIso_stabilization j a b K D)

end PointedCGWH.Spectra.Orthogonal.IndexKan

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import Mathlib.CategoryTheory.Limits.Shapes.Equalizers

@[expose] public section
set_option autoImplicit false
set_option linter.hashCommand false
noncomputable section
universe uV vV uI uR

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Enriched.ProductRelationMapping

variable {V : Type uV} [Category.{vV} V] {I : Type uI} {R : Type uR}

/-- Full component objects and two complete relation families; no inverse law is an input. -/
structure Data where
  /-- The component objects indexed by `I`. -/
  objects : I → V
  /-- The objects in which the two relation components are compared. -/
  relations : R → V
  /-- The source index of each left relation component. -/
  leftIndex : R → I
  /-- The source index of each right relation component. -/
  rightIndex : R → I
  /-- The map from each left component into its relation object. -/
  leftComponent : ∀ r, objects (leftIndex r) ⟶ relations r
  /-- The map from each right component into its relation object. -/
  rightComponent : ∀ r, objects (rightIndex r) ⟶ relations r

/-- Every complete parameter family satisfying the original relation maps. -/
@[ext]
structure Family (d : Data (V := V) (I := I) (R := R)) (P : V) where
  /-- The component maps from the common parameter object. -/
  app : ∀ i, P ⟶ d.objects i
  condition : ∀ r, app (d.leftIndex r) ≫ d.leftComponent r =
    app (d.rightIndex r) ≫ d.rightComponent r

variable (d : Data (V := V) (I := I) (R := R))
  [HasProduct d.objects] [HasProduct d.relations]

/-- The whole original first product relation. -/
def leftMap : (∏ᶜ d.objects) ⟶ ∏ᶜ d.relations :=
  Pi.lift (fun r => Pi.π d.objects (d.leftIndex r) ≫ d.leftComponent r)

/-- The whole original second product relation. -/
def rightMap : (∏ᶜ d.objects) ⟶ ∏ᶜ d.relations :=
  Pi.lift (fun r => Pi.π d.objects (d.rightIndex r) ≫ d.rightComponent r)

/-- Every complete first relation component is retained. -/
theorem leftMap_π (r : R) : leftMap d ≫ Pi.π d.relations r =
    Pi.π d.objects (d.leftIndex r) ≫ d.leftComponent r :=
  Pi.lift_comp_π _ r

/-- Every complete second relation component is retained. -/
theorem rightMap_π (r : R) : rightMap d ≫ Pi.π d.relations r =
    Pi.π d.objects (d.rightIndex r) ≫ d.rightComponent r :=
  Pi.lift_comp_π _ r

variable [HasEqualizer (leftMap d) (rightMap d)]

/-- Actual full mapping object from the original product/equalizer presentation. -/
@[no_expose]
def Hom : V := equalizer (leftMap d) (rightMap d)

/-- Every complete original component projection. -/
@[no_expose]
def π (i : I) : Hom d ⟶ d.objects i :=
  equalizer.ι (leftMap d) (rightMap d) ≫ Pi.π d.objects i

/-- The complete projection is the original equalizer followed by its product projection. -/
theorem π_heq (i : I) :
    HEq (π d i) (equalizer.ι (leftMap d) (rightMap d) ≫ Pi.π d.objects i) := by rfl

/-- Both full original relations hold on the actual mapping object. -/
theorem condition (r : R) : π d (d.leftIndex r) ≫ d.leftComponent r =
    π d (d.rightIndex r) ≫ d.rightComponent r := by
  let i : Hom d ⟶ ∏ᶜ d.objects := equalizer.ι (leftMap d) (rightMap d)
  have hRaw := congrArg (fun z => z ≫ Pi.π d.relations r)
    (equalizer.condition (leftMap d) (rightMap d))
  have h : i ≫ leftMap d ≫ Pi.π d.relations r =
      i ≫ rightMap d ≫ Pi.π d.relations r :=
    (Category.assoc i (leftMap d) (Pi.π d.relations r)).symm.trans
      (hRaw.trans (Category.assoc i (rightMap d) (Pi.π d.relations r)))
  exact (Category.assoc i (Pi.π d.objects (d.leftIndex r)) (d.leftComponent r)).trans
    ((congrArg (fun z => i ≫ z) (leftMap_π d r)).symm.trans
      (h.trans ((congrArg (fun z => i ≫ z) (rightMap_π d r)).trans
        (Category.assoc i (Pi.π d.objects (d.rightIndex r)) (d.rightComponent r)).symm)))

/-- Every full compatible parameter family lifts to the actual original equalizer. -/
@[no_expose]
def lift {P : V} (q : Family d P) : P ⟶ Hom d :=
  equalizer.lift (Pi.lift q.app) (by
    apply Pi.hom_ext
    intro r
    let p : P ⟶ ∏ᶜ d.objects := Pi.lift q.app
    have hLeft : (p ≫ leftMap d) ≫ Pi.π d.relations r =
        q.app (d.leftIndex r) ≫ d.leftComponent r :=
      (Category.assoc p (leftMap d) (Pi.π d.relations r)).trans
        ((congrArg (fun z => p ≫ z) (leftMap_π d r)).trans
          ((Category.assoc p (Pi.π d.objects (d.leftIndex r)) (d.leftComponent r)).symm.trans
            (congrArg (fun z => z ≫ d.leftComponent r)
              (Pi.lift_comp_π q.app (d.leftIndex r)))))
    have hRight : q.app (d.rightIndex r) ≫ d.rightComponent r =
        (p ≫ rightMap d) ≫ Pi.π d.relations r :=
      (congrArg (fun z => z ≫ d.rightComponent r)
        (Pi.lift_comp_π q.app (d.rightIndex r))).symm.trans
        ((Category.assoc p (Pi.π d.objects (d.rightIndex r)) (d.rightComponent r)).trans
          ((congrArg (fun z => p ≫ z) (rightMap_π d r)).symm.trans
            (Category.assoc p (rightMap d) (Pi.π d.relations r)).symm))
    exact hLeft.trans ((q.condition r).trans hRight))

/-- Every full source component of a lifted map is unchanged. -/
theorem lift_π {P : V} (q : Family d P) (i : I) : lift d q ≫ π d i = q.app i := by
  dsimp only [Hom, lift, π]
  rw [← Category.assoc, equalizer.lift_ι, Pi.lift_comp_π]

/-- All full original component projections determine a map into the actual equalizer. -/
theorem hom_ext {P : V} {f g : P ⟶ Hom d} (h : ∀ i, f ≫ π d i = g ≫ π d i) : f = g := by
  apply equalizer.hom_ext
  apply Pi.hom_ext
  intro i
  exact (Category.assoc f (equalizer.ι (leftMap d) (rightMap d)) (Pi.π d.objects i)).trans
    ((h i).trans
      (Category.assoc g (equalizer.ι (leftMap d) (rightMap d)) (Pi.π d.objects i)).symm)

/-- Every map into the actual equalizer produces its complete parameter family. -/
def toFamily {P : V} (f : P ⟶ Hom d) : Family d P where
  app i := f ≫ π d i
  condition r := (Category.assoc _ _ _).trans
    ((congrArg (fun z => f ≫ z) (condition d r)).trans (Category.assoc _ _ _).symm)

/-- The entire original parameter family is recovered. -/
theorem toFamily_lift {P : V} (q : Family d P) : toFamily d (lift d q) = q := by
  apply Family.ext
  funext i
  exact lift_π d q i

/-- The entire original map into the full mapping object is recovered. -/
theorem lift_toFamily {P : V} (f : P ⟶ Hom d) : lift d (toFamily d f) = f := by
  apply hom_ext d
  intro i
  exact lift_π d (toFamily d f) i

/-- Every complete parameter Hom is represented by the original full relation equalizer. -/
def representationEquiv (P : V) : (P ⟶ Hom d) ≃ Family d P where
  toFun := toFamily d
  invFun := lift d
  left_inv := lift_toFamily d
  right_inv := toFamily_lift d

/-- The object is the exact original full product/equalizer presentation. -/
theorem Hom_eq : Hom d = equalizer (leftMap d) (rightMap d) := by rfl

end CategoryTheory.Enriched.ProductRelationMapping

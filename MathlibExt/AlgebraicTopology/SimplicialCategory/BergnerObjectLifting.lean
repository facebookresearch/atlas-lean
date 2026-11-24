/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialCategory.BergnerTwoObjectLifting
import MathlibExt.AlgebraicTopology.SimplicialCategory.CodiscreteEnrichment

/-!
# The genuine empty-to-point Bergner object generator

The original empty enrichment has no objects. The original point has
one individual object with the unit endomorphism Hom. Lifting against
their actual map is precisely surjectivity of the SAME original object
function. No quotient of objects, component surjectivity or model outcome
is supplied. This is generator (i) in HTT, page 858.
-/
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u
open CategoryTheory MonoidalCategory
open scoped Simplicial

namespace CategoryTheory.SimplicialEnrichment.BergnerObjects

/-- The actual original empty simplicial enrichment. -/
abbrev empty : Carrier.{u} := CodiscreteEnrichment.object PEmpty.{u + 1}

/-- The actual one-object original enrichment with its literal unit endomorphism Hom. -/
abbrev point : Carrier.{u} := CodiscreteEnrichment.object PUnit.{u + 1}

/-- The SAME original map that adds the single individual point object. -/
def inclusion : empty.{u} ⟶ point.{u} := CodiscreteEnrichment.map (↾PEmpty.elim)

variable {C D : Carrier.{u}}

/-- The unique full original map out of the empty enrichment. -/
def fromEmpty (C : Carrier.{u}) : empty.{u} ⟶ C where
  obj x := PEmpty.elim x
  map x _ := PEmpty.elim x
  map_id x := PEmpty.elim x
  map_comp x _ _ := PEmpty.elim x

/-- Any two whole original maps from the empty enrichment agree. -/
theorem fromEmpty_unique (F : empty.{u} ⟶ C) : fromEmpty C = F := by
  apply EnrichedFunctor.ext SSet.{u} (C := empty.{u}) (D := C)
    (F := fromEmpty C) (G := F) (fun x => PEmpty.elim x)
  intro x
  exact PEmpty.elim x

/-- The full original point functor selects the given individual object and its original identity. -/
def select (x : C) : point.{u} ⟶ C where
  obj _ := x
  map _ _ := eId SSet.{u} x
  map_id _ := Category.id_comp _
  map_comp _ _ _ :=
    (SSet.WalkingHom.ofMap x x (eId SSet.{u} x)).map_comp
      SSet.WalkingHom.source SSet.WalkingHom.source SSet.WalkingHom.source

theorem select_obj (x : C) : (select x).obj PUnit.unit = x := rfl
theorem select_map (x : C) : (select x).map PUnit.unit PUnit.unit = eId SSet.{u} x := rfl

/-- Reading the actual selected object recovers the SAME whole original point functor. -/
theorem select_readback (F : point.{u} ⟶ C) : select (F.obj PUnit.unit) = F := by
  apply EnrichedFunctor.ext SSet.{u} (C := point.{u}) (D := C)
    (F := select (F.obj PUnit.unit)) (G := F)
    (fun x => congrArg F.obj (Subsingleton.elim PUnit.unit x))
  intro x y
  cases x
  cases y
  change eId SSet.{u} (F.obj PUnit.unit) ≫ 𝟙 _ = F.map PUnit.unit PUnit.unit
  exact (Category.comp_id _).trans ((F.map_id PUnit.unit).symm.trans (Category.id_comp _))

/-- Whole original point functors are exactly individual original objects. -/
def pointHomEquiv (C : Carrier.{u}) : (point.{u} ⟶ C) ≃ C where
  toFun F := F.obj PUnit.unit
  invFun := select
  left_inv := select_readback
  right_inv _ := rfl

/-- The same original target functor keeps the actual selected individual object. -/
theorem select_comp (x : C) (F : C ⟶ D) : select x ≫ F = select (F.obj x) :=
  (select_readback (select x ≫ F)).symm

/-- Right lifting against the actual empty-to-point map detects literal original object surjectivity. -/
theorem hasLiftingProperty_iff (F : C ⟶ D) : HasLiftingProperty inclusion.{u} F ↔ Function.Surjective F.obj := by
  constructor
  · intro h y
    let _ := h
    let sq : CommSq (fromEmpty C) inclusion F (select y) :=
      ⟨(fromEmpty_unique (fromEmpty C ≫ F)).symm.trans (fromEmpty_unique (inclusion ≫ select y))⟩
    exact ⟨sq.lift.obj PUnit.unit, congrArg (fun k : point.{u} ⟶ D => k.obj PUnit.unit) sq.fac_right⟩
  · intro h
    refine ⟨fun {top bottom} _sq => ?_⟩
    obtain ⟨x, hx⟩ := h (bottom.obj PUnit.unit)
    let l : point.{u} ⟶ C := select x
    refine CommSq.HasLift.mk' ⟨l, ?_, ?_⟩
    · exact (fromEmpty_unique (inclusion ≫ l)).symm.trans (fromEmpty_unique top)
    · exact (select_comp x F).trans
        ((congrArg select hx).trans (select_readback bottom))

end CategoryTheory.SimplicialEnrichment.BergnerObjects

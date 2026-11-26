/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialCategory.WalkingHom
import MathlibExt.AlgebraicTopology.SimplicialCategory.StrictCategory

/-!
# The original global two-object Bergner generators

The existing enrichment `WalkingHom X` has the literal forward Hom X,
empty reverse Hom and identity endomorphisms. Tag only its two original
objects by ULift to place it in the actual varying-object Carrier universe.
Every Hom and scalar operator is unchanged. The same full functor
representation retains both individual object images and the original
forward Hom map, including cases where the target images coincide.

These are the [1]_X categories in HTT, page 858, used by Proposition
A.3.2.4. No fixed-object restriction or model outcome is assumed.
-/
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u v w
open CategoryTheory MonoidalCategory
open scoped Simplicial

namespace CategoryTheory.SimplicialEnrichment.BergnerTwoObject

/-- Tag only the original two objects and retain all original Hom objects, identities and composition. -/
@[instance_reducible]
def enrichment (X : SSet.{u}) : EnrichedCategory SSet.{u} (ULift.{u} (SSet.WalkingHom X)) where
  Hom x y := x.down ⟶[SSet.{u}] y.down
  id x := eId SSet.{u} x.down
  comp x y z := eComp SSet.{u} x.down y.down z.down
  id_comp x y := e_id_comp SSet.{u} x.down y.down
  comp_id x y := e_comp_id SSet.{u} x.down y.down
  assoc a b c d := e_assoc SSet.{u} a.down b.down c.down d.down

/-- The SAME original two-object enrichment in the actual global Carrier universe. -/
def object (X : SSet.{u}) : Carrier.{u} := by
  let _ := enrichment X
  exact SimplicialEnrichment.of (ULift.{u} (SSet.WalkingHom X))

/-- The SAME original source object of the two-object category. -/
def source (X : SSet.{u}) : object X := ULift.up SSet.WalkingHom.source
/-- The SAME original target object of the two-object category. -/
def target (X : SSet.{u}) : object X := ULift.up SSet.WalkingHom.target

theorem hom_source_target (X : SSet.{u}) : (source X ⟶[SSet.{u}] target X) = X := rfl
theorem hom_source_source (X : SSet.{u}) : (source X ⟶[SSet.{u}] source X) = 𝟙_ SSet.{u} := rfl
theorem hom_target_target (X : SSet.{u}) : (target X ⟶[SSet.{u}] target X) = 𝟙_ SSet.{u} := rfl
theorem hom_target_source (X : SSet.{u}) :
    (target X ⟶[SSet.{u}] source X) = SSet.WalkingHom.emptyHom.{u} := rfl

variable {X : SSet.{u}} {C : Type v} [EnrichedCategory SSet.{u} C]

/-- Read the original two object labels, keeping every whole Hom map unchanged. -/
def toOriginal (F : EnrichedFunctor SSet.{u} (object X) C) :
    EnrichedFunctor SSet.{u} (SSet.WalkingHom X) C where
  obj x := F.obj (ULift.up x)
  map x y := F.map (ULift.up x) (ULift.up y)
  map_id x := F.map_id (ULift.up x)
  map_comp x y z := F.map_comp (ULift.up x) (ULift.up y) (ULift.up z)

/-- Tag solely the same two original source objects of the supplied whole enriched functor. -/
def fromOriginal (F : EnrichedFunctor SSet.{u} (SSet.WalkingHom X) C) :
    EnrichedFunctor SSet.{u} (object X) C where
  obj x := F.obj x.down
  map x y := F.map x.down y.down
  map_id x := F.map_id x.down
  map_comp x y z := F.map_comp x.down y.down z.down

theorem fromOriginal_toOriginal (F : EnrichedFunctor SSet.{u} (object X) C) :
    fromOriginal (toOriginal F) = F := by
  apply EnrichedFunctor.ext SSet.{u} (fun _ => rfl)
  intro x y
  exact Category.comp_id _

theorem toOriginal_fromOriginal (F : EnrichedFunctor SSet.{u} (SSet.WalkingHom X) C) :
    toOriginal (fromOriginal F) = F := by
  apply EnrichedFunctor.ext SSet.{u} (fun _ => rfl)
  intro x y
  exact Category.comp_id _

/-- The full original two-object map determined by its actual two target objects and original forward Hom. -/
def ofMap (x y : C) (f : X ⟶ x ⟶[SSet.{u}] y) : EnrichedFunctor SSet.{u} (object X) C :=
  fromOriginal (SSet.WalkingHom.ofMap x y f)

theorem ofMap_obj_source (x y : C) (f : X ⟶ x ⟶[SSet.{u}] y) : (ofMap x y f).obj (source X) = x := rfl
theorem ofMap_obj_target (x y : C) (f : X ⟶ x ⟶[SSet.{u}] y) : (ofMap x y f).obj (target X) = y := rfl
theorem ofMap_forward (x y : C) (f : X ⟶ x ⟶[SSet.{u}] y) :
    (ofMap x y f).map (source X) (target X) = f := rfl

/-- Reading both original object images and the forward Hom reconstructs the SAME whole global functor. -/
theorem ofMap_readback (F : EnrichedFunctor SSet.{u} (object X) C) :
    ofMap (F.obj (source X)) (F.obj (target X)) (F.map (source X) (target X)) = F :=
  (congrArg fromOriginal (SSet.WalkingHom.ofMap_readback (toOriginal F))).trans (fromOriginal_toOriginal F)

/-- Every full varying-object map out of [1]_X retains exactly its original two objects and Hom map. -/
def functorEquiv :
    EnrichedFunctor SSet.{u} (object X) C ≃ (Σ x : C, Σ y : C, X ⟶ x ⟶[SSet.{u}] y) where
  toFun F := ⟨F.obj (source X), F.obj (target X), F.map (source X) (target X)⟩
  invFun p := ofMap p.1 p.2.1 p.2.2
  left_inv := ofMap_readback
  right_inv p := by rcases p with ⟨x, y, f⟩; rfl

theorem ofMap_injective (x y : C) : Function.Injective (ofMap (X := X) x y) := by
  intro f g h
  exact SSet.WalkingHom.ofMap_injective x y (congrArg toOriginal h)

/-- Whole original target postcomposition acts on the SAME two objects and entire original Hom map. -/
theorem ofMap_comp {D : Type w} [EnrichedCategory SSet.{u} D]
    (x y : C) (f : X ⟶ x ⟶[SSet.{u}] y) (F : EnrichedFunctor SSet.{u} C D) :
    EnrichedFunctor.comp SSet.{u} (ofMap x y f) F = ofMap (F.obj x) (F.obj y) (f ≫ F.map x y) :=
  (ofMap_readback (EnrichedFunctor.comp SSet.{u} (ofMap x y f) F)).symm

/-- The actual Bergner generator map retains both original object positions and the whole original scalar map. -/
def map {A B : SSet.{u}} (i : A ⟶ B) : object A ⟶ object B := ofMap (source B) (target B) i

theorem map_obj_source {A B : SSet.{u}} (i : A ⟶ B) : (map i).obj (source A) = source B := rfl
theorem map_obj_target {A B : SSet.{u}} (i : A ⟶ B) : (map i).obj (target A) = target B := rfl
theorem map_forward {A B : SSet.{u}} (i : A ⟶ B) : (map i).map (source A) (target A) = i := rfl

theorem map_id (A : SSet.{u}) : map (𝟙 A) = 𝟙 (object A) := ofMap_readback (𝟙 (object A))
theorem map_comp {A B E : SSet.{u}} (i : A ⟶ B) (j : B ⟶ E) :
    map i ≫ map j = map (i ≫ j) := ofMap_comp (source B) (target B) i (map j)

/-- The original global two-object generator construction is a functor at the unchanged scalar universe. -/
def functor : SSet.{u} ⥤ Carrier.{u} where
  obj X := object X
  map i := map i
  map_id X := map_id X
  map_comp i j := (map_comp i j).symm

/-- Whole original scalar precomposition retains both prescribed target objects. -/
theorem map_ofMap {A B : SSet.{u}} (i : A ⟶ B) (x y : C) (f : B ⟶ x ⟶[SSet.{u}] y) :
    EnrichedFunctor.comp SSet.{u} (map i) (ofMap x y f) = ofMap x y (i ≫ f) :=
  ofMap_comp (source B) (target B) i (ofMap x y f)

/-- Full global functors with both original object images prescribed. -/
abbrev FixedEndpoints (x y : C) :=
  {F : EnrichedFunctor SSet.{u} (object X) C // F.obj (source X) = x ∧ F.obj (target X) = y}

/-- Only the two stated object equalities transport the SAME full original forward Hom. -/
def fixedEndpointsEquiv (x y : C) : FixedEndpoints (X := X) x y ≃ (X ⟶ x ⟶[SSet.{u}] y) where
  toFun F := F.val.map (source X) (target X) ≫
    eqToHom (congrArg₂ (fun a b : C => a ⟶[SSet.{u}] b) F.property.1 F.property.2)
  invFun f := ⟨ofMap x y f, rfl, rfl⟩
  left_inv F := by
    rcases F with ⟨F, ha, hb⟩
    cases ha
    cases hb
    exact Subtype.ext (ofMap_readback F)
  right_inv f := Category.comp_id f

end CategoryTheory.SimplicialEnrichment.BergnerTwoObject

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.Spectra.Symmetric.OperatorRestriction

/-!
# Full original morphisms in the sphere-module operator presentation

Every original component is preserved. Whole coend naturality follows from
the complete coefficient squares and the original finite-label squares.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe uV vV

open CategoryTheory Limits MonoidalCategory BraidedCategory
open CategoryTheory.MonoidalCategory

namespace CategoryTheory.Spectra.Symmetric.OperatorCoend

local notation "I" => Operad.SmallFinBijGroupoid

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V] [SymmetricCategory V]
  [HasColimitsOfSize.{0, 0} V]
  [∀ X : V, PreservesColimitsOfSize.{0, 0} (tensorLeft X)] {T : V}

/-- Every original component of a whole enriched operator transformation. -/
def representationMapComponent {X Y : Representation T} (f : X ⟶ Y) (n : I) :
    representationObject X n ⟶ representationObject Y n := by
  letI : EnrichedCategory V I := enrichedCategory T
  exact f.app n

/-- Every original whole transformation retains the complete coend action square. -/
theorem representationMap_comm {X Y : Representation T} (f : X ⟶ Y) (n k : I) :
    (representationMapComponent f n ▷ Hom T n k) ≫ representationAction Y n k =
      representationAction X n k ≫ representationMapComponent f k := by
  let _ : EnrichedCategory V I := enrichedCategory T
  exact f.comm n k

variable [∀ X : V, PreservesColimitsOfSize.{0, 0} (tensorRight X)]

/-- Every original ordinary module morphism retains its whole right-ordered coefficient square. -/
theorem coefficientAction_morphism {d e : SphereData T} (f : d ⟶ e) (a n : I) :
    (f.map.app n ▷ (Operad.SmallFinBijGroupoid.tensorPowerFunctor T).obj a) ≫ coefficientAction e a n =
      coefficientAction d a n ≫ f.map.app (a ⊗ n) := by
  let P := Operad.SmallFinBijGroupoid.tensorPowerFunctor T
  let fn : d.diagram.obj n ⟶ e.diagram.obj n := f.map.app n
  let fan : d.diagram.obj (a ⊗ n) ⟶ e.diagram.obj (a ⊗ n) := f.map.app (a ⊗ n)
  have hp : coefficient d a n ≫ fan = (P.obj a ◁ fn) ≫ coefficient e a n := f.comm a n
  change (fn ▷ P.obj a) ≫ coefficientAction e a n = coefficientAction d a n ≫ fan
  simp only [coefficientAction, Category.assoc]
  slice_lhs 1 2 => rw [braiding_naturality_left]
  simp only [Category.assoc]
  slice_lhs 2 3 => rw [← hp]

/-- Every original ordinary module morphism retains every full labelled coefficient action square. -/
theorem actionLeg_morphism {d e : SphereData T} (f : d ⟶ e) (a n k : I) (g : a ⊗ n ⟶ k) :
    (f.map.app n ▷ (Operad.SmallFinBijGroupoid.tensorPowerFunctor T).obj a) ≫ actionLeg e a n k g =
      actionLeg d a n k g ≫ f.map.app k := by
  let fn : d.diagram.obj n ⟶ e.diagram.obj n := f.map.app n
  let fan : d.diagram.obj (a ⊗ n) ⟶ e.diagram.obj (a ⊗ n) := f.map.app (a ⊗ n)
  let fk : d.diagram.obj k ⟶ e.diagram.obj k := f.map.app k
  have hp : (fn ▷ (Operad.SmallFinBijGroupoid.tensorPowerFunctor T).obj a) ≫ coefficientAction e a n =
      coefficientAction d a n ≫ fan := coefficientAction_morphism f a n
  have hn : d.diagram.map g ≫ fk = fan ≫ e.diagram.map g := f.map.naturality g
  change (fn ▷ (Operad.SmallFinBijGroupoid.tensorPowerFunctor T).obj a) ≫ actionLeg e a n k g =
    actionLeg d a n k g ≫ fk
  simp only [actionLeg, Category.assoc]
  rw [← Category.assoc, hp, Category.assoc, ← hn]

/-- Whole original module morphisms commute with the entire descended operator Hom action. -/
theorem operatorAction_morphism {d e : SphereData T} (f : d ⟶ e) (n k : I) :
    (f.map.app n ▷ Hom T n k) ≫ operatorAction e n k = operatorAction d n k ≫ f.map.app k := by
  let fn : d.diagram.obj n ⟶ e.diagram.obj n := f.map.app n
  let fk : d.diagram.obj k ⟶ e.diagram.obj k := f.map.app k
  apply (isColimitOfPreserves (tensorLeft (d.diagram.obj n)) (colimit.isColimit (diagram T n k))).hom_ext
  intro q
  let P := Operad.SmallFinBijGroupoid.tensorPowerFunctor T
  let j : P.obj q.left ⟶ Hom T n k := generator T q.left n k q.hom
  have hPrefix : (d.diagram.obj n ◁ j) ≫ (fn ▷ Hom T n k) =
      (fn ▷ P.obj q.left) ≫ (e.diagram.obj n ◁ j) := whisker_exchange fn j
  have he : (e.diagram.obj n ◁ j) ≫ operatorAction e n k = actionLeg e q.left n k q.hom :=
    generator_operatorAction e q.left n k q.hom
  have hd : (d.diagram.obj n ◁ j) ≫ operatorAction d n k = actionLeg d q.left n k q.hom :=
    generator_operatorAction d q.left n k q.hom
  have hm : (fn ▷ P.obj q.left) ≫ actionLeg e q.left n k q.hom =
      actionLeg d q.left n k q.hom ≫ fk := actionLeg_morphism f q.left n k q.hom
  change (d.diagram.obj n ◁ j) ≫ (fn ▷ Hom T n k) ≫ operatorAction e n k =
    (d.diagram.obj n ◁ j) ≫ operatorAction d n k ≫ fk
  slice_lhs 1 2 => rw [hPrefix]
  simp only [Category.assoc]
  rw [he, hm, ← Category.assoc, hd]

/-- The original module morphism, with all of its components, as an actual whole operator transformation. -/
def toRepresentationMap {d e : SphereData T} (f : d ⟶ e) : toRepresentation d ⟶ toRepresentation e := by
  letI : EnrichedCategory V I := enrichedCategory T
  exact { app n := f.map.app n, comm := operatorAction_morphism f }

/-- The whole module-to-operator construction is functorial on the exact original carrier. -/
def toRepresentations (T : V) : SphereData T ⥤ Representation T where
  obj := toRepresentation
  map := toRepresentationMap
  map_id d := by
    let _ : EnrichedCategory V I := enrichedCategory T
    apply WholeRepresentation.hom_ext
    intro n
    rfl
  map_comp f g := by
    let _ : EnrichedCategory V I := enrichedCategory T
    apply WholeRepresentation.hom_ext
    intro n
    rfl

/-- Every original morphism component is unchanged by the whole operator functor. -/
theorem toRepresentationMap_component {d e : SphereData T} (f : d ⟶ e) (n : I) :
    representationMapComponent (toRepresentationMap f) n = f.map.app n := rfl

end CategoryTheory.Spectra.Symmetric.OperatorCoend

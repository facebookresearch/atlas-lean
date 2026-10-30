/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Logics.Modal.Kripke

@[expose] public section

set_option autoImplicit false

namespace Cslib.Modal.KripkeTests

/-- The two-world toggle model: each world accesses the other; the unique
atom holds everywhere. -/
def toggleModel : KripkeModel Bool Unit where
  nonempty_world := inferInstance
  rel a b := b = !a
  valuation _ _ := True

/-- The one-world model with a self-loop; the unique atom holds. -/
def pointModel : KripkeModel Unit Unit where
  nonempty_world := inferInstance
  rel _ _ := True
  valuation _ _ := True

/-- Collapsing both toggle worlds to the single point is a (nonidentity)
bounded morphism: atoms agree since the atom holds everywhere, every step
maps to the self-loop, and the self-loop lifts to the toggle step. -/
def collapse : BoundedMorphism toggleModel pointModel where
  toFun := fun _ => ()
  atom_iff := fun _ _ => Iff.rfl
  forth := fun _ => trivial
  back := by
    intro world _ _
    exact ⟨!world, rfl, Subsingleton.elim _ _⟩

/-- The collapse map itself: both worlds go to the point. -/
example : collapse false = () ∧ collapse true = () :=
  ⟨rfl, rfl⟩

/-- Forth condition, exercised directly: the toggle step `false → true`
maps to a point-model step. -/
example : pointModel.rel (collapse false) (collapse true) :=
  collapse.forth (world := false) (next := true) rfl

/-- Back condition, exercised directly: the point-model self-loop at the
image of `false` lifts to the toggle step to `true`. -/
example : ∃ next, toggleModel.rel false next ∧ collapse next = () :=
  collapse.back trivial

/-- Composition with identities, and the composition action on worlds. -/
example : (BoundedMorphism.id pointModel).comp collapse = collapse :=
  BoundedMorphism.id_comp _

example : collapse.comp (BoundedMorphism.id toggleModel) = collapse :=
  BoundedMorphism.comp_id _

example (w : Bool) :
    (BoundedMorphism.id pointModel).comp collapse w = () := rfl

/-- Satisfaction invariance under the collapse, through the public
`BoundedMorphism.satisfies_iff`. -/
example (φ : Formula Unit) (w : Bool) :
    toggleModel.Satisfies w φ ↔ pointModel.Satisfies (collapse w) φ :=
  collapse.satisfies_iff φ w

/-- A concrete satisfaction transfer: `□ atom` holds in the toggle model
because it holds at the point. -/
example (w : Bool) : toggleModel.Satisfies w (.box (.atom ())) := by
  rw [collapse.satisfies_iff]
  intro _ _
  trivial

/-- The collapse is surjective, so global validity agrees between the two
models. -/
example (φ : Formula Unit) : toggleModel.Valid φ ↔ pointModel.Valid φ :=
  collapse.valid_iff_of_surjective (fun _ => ⟨false, Subsingleton.elim _ _⟩) φ

end Cslib.Modal.KripkeTests

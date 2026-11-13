/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Logics.Modal.CslibTranslation

@[expose] public section

/-! # Tests for the CSLib modal translation bridge -/

namespace Cslib.Modal.CslibTranslationTests

open Formula

/-- Constructor translation: atoms. -/
example {Atom : Type*} (p : Atom) :
    Formula.toProposition (Formula.atom p) =
      Logic.Modal.Proposition.atom p :=
  rfl

/-- Constructor translation: falsum. -/
example {Atom : Type*} :
    Formula.toProposition (Formula.bot : Formula Atom) =
      Logic.Modal.Proposition.false :=
  rfl

/-- Constructor translation: implication goes through `Proposition.imp`. -/
example {Atom : Type*} (phi psi : Formula Atom) :
    Formula.toProposition (Formula.imp phi psi) =
      Logic.Modal.Proposition.imp (Formula.toProposition phi) (Formula.toProposition psi) :=
  rfl

/-- Constructor translation: box goes through `dynBox`. -/
example {Atom : Type*} (phi : Formula Atom) :
    Formula.toProposition (Formula.box phi) =
      Logic.HasDynamicBox.dynBox default (Formula.toProposition phi) :=
  rfl

/-- Model round trip: Kripke to CSLib and back is the identity, using
the model's own bundled nonemptiness witness (no ambient instance). -/
example {Atom World : Type*} (k : KripkeModel World Atom) :
    @KripkeModel.ofModel Atom World k.nonempty_world (KripkeModel.toModel k) = k :=
  KripkeModel.ofModel_toModel k

/-- Model round trip: CSLib to Kripke and back is the identity. -/
example {Atom World : Type*} [Nonempty World]
    (m : Logic.Modal.Unimodal.Model World Atom) :
    (KripkeModel.ofModel m).toModel = m :=
  KripkeModel.toModel_ofModel m

/-- A two-world model: the root sees only the second world, where `p` holds. -/
def twoWorld : KripkeModel Bool Unit where
  nonempty_world := ⟨false⟩
  rel w w' := w = false ∧ w' = true
  valuation w _ := w = true

/-- Satisfaction on the concrete model: `□p` holds at the root. -/
example : twoWorld.Satisfies false (Formula.box (Formula.atom ())) := by
  intro next hnext
  exact hnext.2

/-- Satisfaction transfers across the bridge on the concrete model. -/
example : Logic.Modal.Satisfies twoWorld.toModel false
    (Formula.toProposition (Formula.box (Formula.atom ()))) := by
  apply (satisfies_toProposition twoWorld false _).mp
  intro next hnext
  exact hnext.2

end Cslib.Modal.CslibTranslationTests

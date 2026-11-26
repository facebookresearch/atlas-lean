/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import CSLibExt.Logics.Modal.ProvabilityLogic.Completeness

namespace Cslib.Modal

-- Completeness recovers positive introspection from transitivity, for arbitrary atoms.
example {Atom : Type*} (a : Formula Atom) : Derivable Axioms.GL (Formula.axiomFour a) :=
  (derivable_GL_iff_finite _).mpr fun _ _ _ trans _ _ hbox _ hwv t hvt ↦
    hbox t (trans hwv hvt)

-- On the two-world chain, □□⊥ holds at the root but □⊥ fails, even without atoms.
example : ¬Derivable (Axioms.GL (Atom := Empty)) (.imp (.box (.box .bot)) (.box .bot)) := by
  intro h
  let M : KripkeModel (Fin 2) Empty := ⟨inferInstance, (· < ·), fun _ p ↦ p.elim⟩
  have hroot := (derivable_GL_iff_finite _).mp h (Fin 2) M
    (fun hab hbc ↦ lt_trans hab hbc) (fun w ↦ lt_irrefl w) 0
  have hboxbox : M.Satisfies 0 (.box (.box .bot)) := by
    intro v hv t ht
    change (0 : Fin 2) < v at hv
    change v < t at ht
    omega
  exact hroot hboxbox 1 (by decide)

end Cslib.Modal

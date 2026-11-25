/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import CSLibExt.Logics.Modal.ProvabilityLogic.FixedPointExistence

/-! # Tests for the general de Jongh–Sambin theorem -/

namespace Cslib.Modal.FixedPointExistenceTests

-- Two distinct outer boxes and no spare atom: the fixed point must be closed.
example :
    let A := Formula.imp (.box (.atom ())) (.box (Formula.atom ()).neg)
    ∃ H : Formula Unit, H.atoms = ∅ ∧ Derivable Axioms.GL (H.iff (A.subst () H)) := by
  intro A
  obtain ⟨H, hfree, _, heq⟩ := fixedPoint_GL (A := A) (p := ()) ⟨trivial, trivial⟩
  exact ⟨H, Set.eq_empty_iff_forall_notMem.mpr (fun | () => hfree), heq⟩

-- Only the parameter q may survive, even when the atom type has other elements.
example {α : Type*} [DecidableEq α] {p q : α} (hne : q ≠ p) :
    let A := Formula.imp (.atom q) (.imp (.box (.atom p)) (.box (.imp (.atom p) (.atom q))))
    ∃ H : Formula α, H.atoms ⊆ {q} ∧ Derivable Axioms.GL (H.iff (A.subst p H)) := by
  intro A
  obtain ⟨H, hfree, hsub, heq⟩ := fixedPoint_GL (A := A) (p := p) ⟨hne, trivial, trivial⟩
  refine ⟨H, fun t ht ↦ ?_, heq⟩
  have htp : t ≠ p := fun e ↦ hfree (e ▸ ht)
  simpa [A, Formula.atoms, htp] using hsub ht

end Cslib.Modal.FixedPointExistenceTests

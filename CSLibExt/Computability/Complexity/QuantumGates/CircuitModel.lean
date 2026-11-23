/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Complexity.Classes
public import Mathlib.LinearAlgebra.UnitaryGroup

/-!
# Circuit-model well-formedness as unitary-group membership

Atlas gate well-formedness unfolds to qubit order plus membership of the
decoded gate matrix in the unitary group `U(4)`.
-/

@[expose] public section

namespace Cslib.Complexity.Classes

set_option autoImplicit false


/-- Atlas well-formedness is qubit order plus membership of the decoded
matrix in `U(4)`. -/
theorem qGateWellFormed_iff (N : ℕ) (g : QGate) :
    QGateWellFormed N g ↔
      g.1 < g.2.1 ∧ g.2.1 < N ∧
        matrixOfEntries g.2.2 ∈ Matrix.unitaryGroup (Fin 2 × Fin 2) ℂ := by
  constructor
  · intro h
    exact ⟨h.1, h.2.1, Matrix.mem_unitaryGroup_iff'.mpr h.2.2⟩
  · intro h
    exact ⟨h.1, h.2.1, Matrix.mem_unitaryGroup_iff'.mp h.2.2⟩

end Cslib.Complexity.Classes

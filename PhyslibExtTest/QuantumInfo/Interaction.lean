/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.QuantumInfo.Interaction

/-!
# Tests: quantum interaction semantics
-/

@[expose] public section

namespace PhyslibExtTest.QuantumInfo.Interaction

set_option autoImplicit false

open PhyslibExt.QuantumInfo.Interaction

#print axioms value_zero
#print axioms value_le_iff

/-- The always-accept two-outcome measurement. -/
def acceptAllPOVM (d : Type*) [Fintype d] [DecidableEq d] : POVM Bool d where
  mats := fun b => if b then 1 else 0
  nonneg := by
    intro b
    cases b with
    | false => simpa using le_refl (0 : HermitianMat _ _)
    | true =>
      simp [HermitianMat.zero_le_iff]
  normalized := by
    simp [Fintype.sum_bool]

/-- A constant verifier that accepts everything in zero messages has
value `1` at every prover workspace, and value `0` at the empty workspace
because there is no prover. -/
theorem value_zero_acceptAll :
    value (dV := Fin 2) (dM := Fin 2)
        { init := MState.pure (Ket.basis (0, 0)), step := fun i => i.elim0,
          accept := acceptAllPOVM (Fin 2 × Fin 2) } (Fin 2) = 1 ∧
      value (dV := Fin 2) (dM := Fin 2)
        { init := MState.pure (Ket.basis (0, 0)), step := fun i => i.elim0,
          accept := acceptAllPOVM (Fin 2 × Fin 2) } Empty = 0 := by
  constructor
  · rw [value_zero]
    have htr : (MState.pure (Ket.basis ((0, 0) : Fin 2 × Fin 2))).M.trace = 1 :=
      MState.tr _
    apply Prob.ext
    show inner ℝ (1 : HermitianMat (Fin 2 × Fin 2) ℂ)
        (MState.pure (Ket.basis ((0, 0) : Fin 2 × Fin 2))).M = 1
    rw [HermitianMat.one_inner, htr]
  · apply value_of_isEmpty

end PhyslibExtTest.QuantumInfo.Interaction

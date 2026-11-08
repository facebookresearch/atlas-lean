/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.RepresentationTheory.Character
import Mathlib.RepresentationTheory.Maschke

set_option autoImplicit false

/-!
# AlgebraNotes canonical API reuse tests

Canonical trace-character and Maschke APIs. The identity character detects the dimension,
including the zero-dimensional character boundary.
-/

namespace AlgebraNotesApiProbe

private theorem trace_integral {k G V : Type*} [Field k] [Group G] [Finite G]
    [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (ρ : Representation k G V) (g : G) : IsIntegral ℤ (LinearMap.trace k V (ρ g)) :=
  Representation.isIntegral_character ρ g

private theorem self_character_pairing {k G V : Type*} [Field k] [IsAlgClosed k]
    [Group G] [Fintype G] [Invertible (Nat.card G : k)]
    [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (ρ : Representation k G V) [ρ.IsIrreducible] :
    (Nat.card G : k)⁻¹ * ∑ g : G, ρ.character g * ρ.character g⁻¹ = 1 := by
  classical
  have he : Nonempty (ρ.Equiv ρ) := ⟨Representation.Equiv.refl ρ⟩
  simpa [he] using Representation.char_orthonormal ρ ρ

private theorem maschke_complement {k G V : Type*} [Field k] [Group G] [Finite G]
    [NeZero (Nat.card G : k)] [AddCommGroup V] [Module (MonoidAlgebra k G) V]
    (W : Submodule (MonoidAlgebra k G) V) :
    ∃ U : Submodule (MonoidAlgebra k G) V, IsCompl W U :=
  MonoidAlgebra.Submodule.exists_isCompl W

private theorem semisimple_representation {k G V : Type*} [Field k] [Group G] [Finite G]
    [NeZero (Nat.card G : k)] [AddCommGroup V] [Module k V]
    (ρ : Representation k G V) : ρ.IsSemisimpleRepresentation := by
  infer_instance

-- At the identity, the character is one in dimension one and zero in dimension zero.
example : (Representation.trivial ℚ PUnit ℚ).character 1 = 1 := by
  rw [Representation.char_one]
  simp
example : (Representation.trivial ℚ PUnit (Fin 0 → ℚ)).character 1 = 0 := by
  rw [Representation.char_one]
  simp

#print axioms trace_integral
#print axioms self_character_pairing
#print axioms maschke_complement
#print axioms semisimple_representation

end AlgebraNotesApiProbe

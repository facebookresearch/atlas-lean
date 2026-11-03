/-
Copyright (c) 2026 Andres Barei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andres Barei
-/
import Mathlib.Algebra.Group.Idempotent
import Mathlib.Analysis.Complex.Basic
import Section_1_Introduction.A_EvolutionAlgebra
import Section_2_Preliminaries.A_Preliminaries

/-!
# Conjecture 1.1: solvable iff idempotent-free

The original García-Martínez / Pérez-Rodríguez conjecture (paper,
`theconjecture`): every complex evolution algebra (in `Type 0`, which covers
all our constructions) is solvable if and only if it admits no nonzero
idempotent elements. Refuted by `conjecture_false` (Section 2
counterexample).
-/

namespace EvolutionAlgebras

/-- **Paper Conjecture 1.1.** The original García-Martínez / Pérez-Rodríguez
conjecture: every complex evolution algebra (in `Type 0`, which covers all our
constructions) is solvable if and only if it admits no nonzero idempotent
elements. -/
def Conjecture : Prop :=
  ∀ (E : Type 0) [NonUnitalNonAssocSemiring E]
    [NonUnitalNonAssocAlgebra ℂ E] [EvolutionAlgebra ℂ E],
    IsSolvable ℂ E ↔ ¬ ∃ x : E, IsIdempotentElem x ∧ x ≠ 0

end EvolutionAlgebras

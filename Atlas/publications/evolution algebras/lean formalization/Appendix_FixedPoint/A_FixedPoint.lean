/-
Copyright (c) 2026 Andres Barei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andres Barei
-/
import Appendix_FixedPoint.BezoutChain.BridgeToFixedPoint.FixedPointBackend
import Section_2_Preliminaries.A_Preliminaries
import Mathlib.FieldTheory.IsAlgClosed.Basic

/-!
# The projective fixed-point principle

The projective fixed-point principle (paper Theorem `idempotentiff`,
backward direction), proved via the Bézout chain.

It is stated with minimal hypotheses (`Field` for `IsAlgClosed`, plus
`NonUnitalNonAssocSemiring` and `Module` for the submodule language), and
nothing else except the scalar-compatibility instances (`IsScalarTower`,
`SMulCommClass`) that the proof genuinely needs: coordinatizing `E` by a
basis and computing with structure constants requires `•` to be compatible
with `*`. In particular there is no algebra bundle and no `EvolutionAlgebra`
hypothesis. This keeps the statement applicable from the differing
typeclass setups used across the library, so both the idempotent
characterization and the corollary apply it directly.

Proved by discharging the 2-residual unconditionally
(`FixedPointBackend.hres2_unconditional`) and applying the detailed
principle (`fixedPoint_of_idempotent_of_data`, same file), itself proved
through the Bézout spine adapter (`SpineAdapter`).

## Main results

* `EvolutionAlgebras.fixedPoint_of_idempotent`: the principle.
-/

namespace EvolutionAlgebras

variable (K E : Type*) [Field K] [NonUnitalNonAssocSemiring E] [Module K E]

/-- **Paper Theorem 3.3 (proof).** Projective fixed-point principle (paper Theorem
    `idempotentiff`, backward direction):
with `V² = V`, `x ↦ x * x` descends to `ℙ(V)` (as `N(V) = {0}`, nonzero vectors
square to nonzero vectors); over an algebraically closed field it has a fixed point
`[x₀]`, i.e. `x₀ * x₀ = λ • x₀` with `λ ≠ 0`. Finite-dimensionality enters as the
explicit `Module.Finite` hypothesis. The `IsScalarTower` / `SMulCommClass`
instances state the `•`/`*` compatibility the proof uses; it does not
follow from the other hypotheses.

Used in two places: the backward direction of Theorem 3.3 (an idempotent
subspace with `N(V) = 0` yields a nonzero idempotent) and the corollary (a
nonsolvable algebra yields a nonzero idempotent via its stabilized term). -/
theorem fixedPoint_of_idempotent (V : Submodule K E) [IsAlgClosed K]
    [IsScalarTower K E E] [SMulCommClass K E E]
    (hfin : Module.Finite K E) (hV : IsIdempotentSubmodule K E V)
    (hN : absNilpotent K E V = {0}) (hneV : V ≠ ⊥) :
    ∃ x : E, x ∈ V ∧ x ≠ 0 ∧ ∃ lam : K, lam ≠ 0 ∧ x * x = lam • x := by
  exact fixedPoint_of_idempotent_of_data K E V hfin hV hN hneV inferInstance
    inferInstance
    (Appendix_FixedPoint.BezoutChain.FixedPointBackend.hres2_unconditional K E V hN inferInstance
      inferInstance)

end EvolutionAlgebras

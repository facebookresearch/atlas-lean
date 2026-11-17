/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Ported from fairinternal/formal-math at `c3bae57ddba11aa34b3cbc61270f587aa4c40152`.

Original formalization by Metamate (introduced in commit `fc40f70f`);
ported with attribution.
-/

module

public import MathlibExt.Computability.Complexity

/-!
# Canonical complexity definitions

This module is the neutral foundation for the repository's canonical `FinTM2`
complexity classes and polynomial-time many-one reductions. It deliberately
contains no SAT, CNF, Cook-Levin, `TimeM`, multi-tape, or single-tape
development.

The canonical reduction is `Cslib.Complexity.PolyManyOneRed`. The historical
`Cslib.CookLevin.PolyManyOneRed` name is an export alias of that same constant.
-/

@[expose] public section

namespace Cslib.Complexity

export MetaMathlibExt.ComplexityTheory
  (DecisionProblem DecisionComplexityClass IsPolyTimeWithEncoding IsPolyTime P NP coNP)

/-- Polynomial-time many-one reduction between canonical decision problems. -/
def PolyManyOneRed (L₁ L₂ : DecisionProblem) : Prop :=
  ∃ reduce : List Bool → List Bool,
    IsPolyTime reduce ∧ ∀ x, L₁ x = L₂ (reduce x)

end Cslib.Complexity

namespace Cslib.CookLevin

export Cslib.Complexity (PolyManyOneRed)

end Cslib.CookLevin

namespace Cslib.Complexity

/-- NP-hardness under canonical polynomial-time many-one reductions. -/
def NPHard (L : DecisionProblem) : Prop :=
  ∀ A : DecisionProblem, A ∈ NP → PolyManyOneRed A L

/-- Membership in canonical NP together with polynomial-time many-one NP-hardness. -/
def NPComplete (L : DecisionProblem) : Prop :=
  L ∈ NP ∧ NPHard L

/-- Canonical NP-hardness is reduction from every language in canonical NP. -/
theorem npHard_iff {L : DecisionProblem} :
    NPHard L ↔ ∀ A : DecisionProblem, A ∈ NP → PolyManyOneRed A L :=
  Iff.rfl

/-- Canonical NP-completeness is exactly membership and many-one hardness. -/
theorem npComplete_iff {L : DecisionProblem} :
    NPComplete L ↔ L ∈ NP ∧
      ∀ A : DecisionProblem, A ∈ NP → PolyManyOneRed A L :=
  Iff.rfl

end Cslib.Complexity

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Ported from fairinternal/formal-math at `c3bae57ddba11aa34b3cbc61270f587aa4c40152`.

Original formalization by Adam Kiezun, with contributions by Metamate
(consolidation commit `fc40f70f`); ported with attribution.
-/

module

public import CSLibExt.Computability.Complexity.Defs
import MathlibExt.Computability.TuringMachine.Composition

/-!
# Canonical machine complexity

This module supplies the generic lemmas for polynomial-time many-one (Karp)
reductions on the repository's canonical `FinTM2` classes. The neutral
`Complexity.Defs` module owns the canonical definitions and class exports.

Declared `TimeM` costs, multi-tape classes and `SingleTapeP` are separate APIs.
Neither trusted cost annotations nor an unproved machine simulation establish
membership in the classes exported here.
-/

@[expose] public section

namespace Cslib.Complexity.PolyManyOneRed

open Cslib.Complexity

/-- The identity function is a canonical polynomial-time many-one reduction. -/
theorem refl (L : DecisionProblem) : PolyManyOneRed L L :=
  ⟨id, ⟨Turing.idComputableInPolyTime _⟩, fun _ => rfl⟩

/-- Canonical polynomial-time many-one reductions compose. -/
theorem trans {L₁ L₂ L₃ : DecisionProblem}
    (h₁ : PolyManyOneRed L₁ L₂) (h₂ : PolyManyOneRed L₂ L₃) :
    PolyManyOneRed L₁ L₃ := by
  obtain ⟨f, hf, e₁⟩ := h₁
  obtain ⟨g, hg, e₂⟩ := h₂
  exact ⟨g ∘ f, MetaMathlibExt.ComplexityTheory.IsPolyTime.comp hf hg,
    fun x => (e₁ x).trans (e₂ (f x))⟩

end Cslib.Complexity.PolyManyOneRed

namespace Cslib.CookLevin.PolyManyOneRed

export Cslib.Complexity.PolyManyOneRed (refl trans)

end Cslib.CookLevin.PolyManyOneRed

namespace Cslib.Complexity

/-- NP-hardness transfers along a canonical polynomial-time many-one reduction. -/
theorem NPHard.of_polyManyOneRed {L L' : DecisionProblem}
    (hL : NPHard L) (h : PolyManyOneRed L L') : NPHard L' :=
  fun A hA => (hL A hA).trans h

/-- Canonical NP membership and many-one hardness establish NP-completeness. -/
theorem NPComplete.mk {L : DecisionProblem} (hL : L ∈ NP) (hHard : NPHard L) :
    NPComplete L :=
  npComplete_iff.mpr ⟨hL, hHard⟩

/-- A canonically NP-complete language belongs to canonical NP. -/
theorem NPComplete.mem_NP {L : DecisionProblem} (h : NPComplete L) : L ∈ NP :=
  (npComplete_iff.mp h).1

/-- A canonically NP-complete language is many-one NP-hard. -/
theorem NPComplete.npHard {L : DecisionProblem} (h : NPComplete L) : NPHard L :=
  (npComplete_iff.mp h).2

end Cslib.Complexity

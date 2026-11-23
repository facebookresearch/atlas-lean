/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Complexity.Basic

/-!
# Canonical complexity API checks

Alias identity, overlapping namespace resolution, reduction dot notation,
and NP-completeness construction and projections, importing only the shared API.
-/

@[expose] public section

namespace Cslib.Complexity.BasicTests

section CanonicalOnly

open Cslib.Complexity

example (L : DecisionProblem) : PolyManyOneRed L L := PolyManyOneRed.refl L

example {L₁ L₂ L₃ : DecisionProblem}
    (h₁ : PolyManyOneRed L₁ L₂) (h₂ : PolyManyOneRed L₂ L₃) :
    PolyManyOneRed L₁ L₃ := PolyManyOneRed.trans h₁ h₂

example {L₁ L₂ L₃ : DecisionProblem}
    (h₁ : PolyManyOneRed L₁ L₂) (h₂ : PolyManyOneRed L₂ L₃) :
    PolyManyOneRed L₁ L₃ := h₁.trans h₂

example {L L' : DecisionProblem} (hL : NPHard L) (h : PolyManyOneRed L L') :
    NPHard L' := NPHard.of_polyManyOneRed hL h

example {L : DecisionProblem} (hL : L ∈ NP) (hHard : NPHard L) :
    NPComplete L := NPComplete.mk hL hHard

end CanonicalOnly

open Cslib.Complexity MetaMathlibExt.ComplexityTheory Cslib.CookLevin

variable {L L₁ L₂ L₃ : DecisionProblem}

example : Cslib.Complexity.P = MetaMathlibExt.ComplexityTheory.P := rfl
example : Cslib.Complexity.NP = MetaMathlibExt.ComplexityTheory.NP := rfl
example : Cslib.Complexity.coNP = MetaMathlibExt.ComplexityTheory.coNP := rfl

example (f : DecisionProblem) :
    Cslib.Complexity.IsPolyTime f ↔ MetaMathlibExt.ComplexityTheory.IsPolyTime f := Iff.rfl

example : Cslib.Complexity.PolyManyOneRed L₁ L₂ ↔
    Cslib.CookLevin.PolyManyOneRed L₁ L₂ := Iff.rfl

example : L ∈ P ↔ IsPolyTime L := Iff.rfl

example : NPHard L ↔ ∀ A : DecisionProblem, A ∈ NP → PolyManyOneRed A L := Iff.rfl

example : NPComplete L ↔ L ∈ NP ∧
    ∀ A : DecisionProblem, A ∈ NP → PolyManyOneRed A L := Iff.rfl

example : PolyManyOneRed L L := PolyManyOneRed.refl L

example (h₁ : PolyManyOneRed L₁ L₂) (h₂ : PolyManyOneRed L₂ L₃) :
    PolyManyOneRed L₁ L₃ := h₁.trans h₂

example (hL : NPHard L₁) (h : PolyManyOneRed L₁ L₂) : NPHard L₂ :=
  hL.of_polyManyOneRed h

example (hL : L ∈ NP) (hHard : NPHard L) : NPComplete L := NPComplete.mk hL hHard

example (h : NPComplete L) : L ∈ NP := h.mem_NP
example (h : NPComplete L) : NPHard L := h.npHard

end Cslib.Complexity.BasicTests

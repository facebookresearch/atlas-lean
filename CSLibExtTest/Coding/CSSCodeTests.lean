/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Coding.CSSCode

@[expose] public section

/-!
# Tests for CSS codewords

With `C₁ = F₂¹` (the whole space) the codewords are `|c_0⟩ = |0⟩ + |1⟩` and
`|c_1⟩ = |0⟩ - |1⟩`. Since `0 + 1 ∉ C₁^⊥ = {0}`, the orthogonality hypothesis is satisfiable and
the two states are orthogonal; a phase flip maps one to the other.
-/

namespace Cslib.CodingTheory.CSS.Tests

open scoped Matrix
open Cslib.CodingTheory Cslib.CodingTheory.LinearCode

/-- The whole space `F₂¹` as a binary linear code. -/
abbrev full : LinearCode (ZMod 2) (Fin 1) := ⊤

instance : DecidablePred (· ∈ full) := fun _ => isTrue Submodule.mem_top

theorem one_not_mem_dual : (0 : Fin 1 → ZMod 2) + 1 ∉ dual full := by
  intro h
  have := mem_dual.1 h 1 Submodule.mem_top
  revert this
  decide

example : ∑ v, star (codeword full 0 v) * codeword full 1 v = 0 :=
  inner_codeword_eq_zero full one_not_mem_dual

example : pauli 0 1 *ᵥ codeword full 0 = codeword full 1 := by
  rw [pauli_zero_mulVec_codeword, zero_add]

example : codeword full 1 1 = -1 := by
  have h : (1 : Fin 1 → ZMod 2) ⬝ᵥ 1 = 1 := by decide
  simp only [codeword, Submodule.mem_top, ite_true, h, sign_one]

example : ∑ v, star (codeword full 0 v) * codeword full 0 v =
    ((Finset.univ.filter fun v : Fin 1 → ZMod 2 => v ∈ full).card : ℂ) :=
  inner_codeword_self full 0

end Cslib.CodingTheory.CSS.Tests

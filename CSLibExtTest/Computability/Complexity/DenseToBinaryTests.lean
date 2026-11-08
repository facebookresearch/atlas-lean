/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Complexity.CookLevin.BinaryHardness
public meta import CSLibExt.Computability.Complexity.CookLevin.BinaryHardness

/-! Tests for the dense-to-binary SAT translation and its machine. -/

namespace Cslib.Complexity.DenseSAT.ToBinary.Tests

open Turing MetaMathlibExt Cslib.Complexity.DenseSAT Cslib.Complexity.DenseSAT.ToBinary

/-- Step a `TM2` program until it halts, with fuel. -/
private def runF {K : Type} [DecidableEq K] {Γ : K → Type} {Λ σ : Type}
    (M : Λ → TM2.Stmt Γ Λ σ) : ℕ → TM2.Cfg Γ Λ σ → TM2.Cfg Γ Λ σ
  | 0, c => c
  | n + 1, c => match TM2.step M c with
    | some c' => runF M n c'
    | none => c

/-- `(x₀ ∨ ¬x₁) ∧ x₁ ∧ ¬x₀` over three slots; unsatisfiable. -/
private def φ₁ : CNF := [[some true, some false, none], [none, some true, none], [some false,
    none, none]]

/-- `x₂ ∧ (¬x₀ ∨ x₁)` over three slots; satisfiable. -/
private def φ₂ : CNF := [[none, none, some true], [some false, some true, none]]

-- Slot `j` of a length-3 clause is variable `2 ^ (2 - j) - 1`: slots 0, 1, 2 are 3, 1, 0.
#guard binCNF φ₂ = [[(0, true)], [(3, false), (1, true)]]
#guard binCNF φ₁ = [[(3, true), (1, false)], [(1, true)], [(3, false)]]

-- The translation on the dense encoding is the binary encoding of `binCNF`.
#guard binConv (encodeCNF φ₁) = Cslib.CookLevin.encodeCNF (binCNF φ₁)
#guard binConv (encodeCNF φ₂) = Cslib.CookLevin.encodeCNF (binCNF φ₂)
#guard binConv (encodeCNF []) = Cslib.CookLevin.encodeCNF []

-- The binary encoding decodes back to the translated formula.
#guard Cslib.CookLevin.decodeCNF (binConv (encodeCNF φ₂)) = some (binCNF φ₂)

-- The machine computes `binConv`, halting with every other stack empty, on the encodings above
-- and on a malformed input (odd length, trailing unterminated clause).
#guard (runF prog 100000 (initList tm (encodeCNF φ₁))).stk .out = binConv (encodeCNF φ₁)
#guard (runF prog 100000 (initList tm (encodeCNF φ₂))).stk .out = binConv (encodeCNF φ₂)
#guard (runF prog 100000 (initList tm [true, false, false, false, true, true, false])).stk .out =
  binConv [true, false, false, false, true, true, false]
#guard (runF prog 100000 (initList tm (encodeCNF φ₂))).l = none
#guard ((runF prog 100000 (initList tm (encodeCNF φ₂))).stk .K).isEmpty

-- Exact step count: `|w| + 1 + convT w.reverse false 0 0 0` steps, not one fewer.
#guard (runF prog ((encodeCNF φ₂).length + 1 + convT (encodeCNF φ₂).reverse false 0 0 0)
  (initList tm (encodeCNF φ₂))).l = none
#guard (runF prog ((encodeCNF φ₂).length + convT (encodeCNF φ₂).reverse false 0 0 0)
  (initList tm (encodeCNF φ₂))).l ≠ none

end Cslib.Complexity.DenseSAT.ToBinary.Tests

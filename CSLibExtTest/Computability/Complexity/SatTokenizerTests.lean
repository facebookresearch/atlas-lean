/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Complexity.SatTokenizer
public meta import CSLibExt.Computability.Complexity.SatTokenizer

/-! Tests for the SAT verifier's tokenizer machine. -/

namespace Cslib.Complexity.SatVerifier.Tokenizer.Tests

open Turing Cslib.CookLevin Cslib.Complexity.SatVerifier Cslib.Complexity.SatVerifier.Tokenizer

/-- Step `prog` until it reaches `acc` or `rej` (or halts), with fuel. -/
private def runF : ℕ → TM2.Cfg (fun _ : K => Sym) Lab Bool → TM2.Cfg (fun _ : K => Sym) Lab Bool
  | 0, c => c
  | n + 1, c =>
      if c.l = some .acc ∨ c.l = some .rej then c
      else match TM2.step prog c with
        | some c' => runF n c'
        | none => c

/-- The start configuration on formula bits `x` and witness `w`, with markers already on `T` and
`B` that must stay at the bottom. -/
private def init (x w : List Bool) : TM2.Cfg (fun _ : K => Sym) Lab Bool :=
  ⟨some start, false, st (x.map .bit) (w.map .bit) [.dead] [.cl] 0 0⟩

/-- Run within the proved bound `2 |x| + 2`. -/
private def runB (x w : List Bool) : TM2.Cfg (fun _ : K => Sym) Lab Bool :=
  runF (2 * x.length + 2) (init x w)

/-- `(x₀ ∨ ¬x₁) ∧ ¬x₀`: variable 0 occurs twice. -/
private def φ₁ : CNF := [[(0, true), (1, false)], [(0, false)]]

/-- `x₂ ∧ ⊥ ∧ (¬x₃ ∨ ¬x₂)`: an empty clause in the middle. -/
private def φ₂ : CNF := [[(2, true)], [], [(3, false), (2, false)]]

/-- The empty formula. -/
private def φ₃ : CNF := []

-- Accepting runs: label `acc` within the bound, `X` used up, and the exact token, table and
-- witness stacks, above the old contents of `T` and `B`.
#guard (runB (encodeCNF φ₁) [true, false, true]).l = some .acc
#guard (runB (encodeCNF φ₁) [true, false, true]).stk .T = (toks φ₁).reverse ++ [.dead]
#guard (runB (encodeCNF φ₁) [true, false, true]).stk .B =
  tblStk (ents φ₁ [true, false, true]) ++ [.cl]
#guard (runB (encodeCNF φ₁) [true, false, true]).stk .X = []
#guard (runB (encodeCNF φ₁) [true, false, true, false]).stk .W = [.bit false]

-- A witness shorter than the occurrence count: the missing values become `dead`.
#guard (runB (encodeCNF φ₁) [true]).l = some .acc
#guard (runB (encodeCNF φ₁) [true]).stk .B = tblStk (ents φ₁ [true]) ++ [.cl]
#guard tblStk (ents φ₁ [true]) = [.dead, .dead, .bit true, .val true]
#guard (runB (encodeCNF φ₁) [true]).stk .W = []

#guard (runB (encodeCNF φ₂) [false, true]).l = some .acc
#guard (runB (encodeCNF φ₂) [false, true]).stk .T = (toks φ₂).reverse ++ [.dead]
#guard (runB (encodeCNF φ₂) [false, true]).stk .B = tblStk (ents φ₂ [false, true]) ++ [.cl]
#guard (runB (encodeCNF φ₂) [false, true]).stk .CC = []
#guard (runB (encodeCNF φ₂) [false, true]).stk .LC = []

#guard (runB (encodeCNF φ₃) [true]).l = some .acc
#guard (runB (encodeCNF φ₃) [true]).stk .T = [.dead]
#guard (runB (encodeCNF φ₃) [true]).stk .W = [.bit true]

-- A bound with factor 1 would not do: `|x|` steps do not reach `acc`.
#guard (runF (encodeCNF φ₁).length (init (encodeCNF φ₁) [])).l ≠ some .acc

-- Rejected inputs: empty, truncated, trailing bits, and a non-canonical name `[true, false]`.
#guard (runB [] []).l = some .rej
#guard (runB (encodeCNF φ₁).dropLast [true]).l = some .rej
#guard (runB (encodeCNF φ₂ ++ [false]) []).l = some .rej
#guard decodeCNF [true, false, true, false, true, true, true, false, false, true] = none
#guard (runB [true, false, true, false, true, true, true, false, false, true] []).l = some .rej
-- Its canonical neighbour (name `[true]`, i.e. variable 1, negated) is accepted.
#guard decodeCNF [true, false, true, false, true, true, false, false] = some [[(1, false)]]
#guard (runB [true, false, true, false, true, true, false, false] [true]).l = some .acc
#guard (runB [true, false, true, false, true, true, false, false] [true]).stk .T =
  [.cl, .lit false, .bit true, .dead]

end Cslib.Complexity.SatVerifier.Tokenizer.Tests

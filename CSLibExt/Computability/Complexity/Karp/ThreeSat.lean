/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.SatTimeM

/-!
# Karp reductions on the canonical classes: 3SAT and the reduction from SAT

Specification module for SAT ≤ 3SAT on `MetaMathlibExt.ComplexityTheory`. It fixes the language,
the pure reduction, and the stack format the reduction machine produces; the correctness proof,
the machine, and NP membership are separate components.

* `sat3Dec`: binary-index CNF formulas (`Cslib.CookLevin.encodeCNF`) in which every clause has at
  most three literals (`is3`), and which are satisfiable.
* `to3`: clauses of length at most one stay; a clause `a₁ ∨ … ∨ aₖ` with `k ≥ 2` becomes the
  chain `(a₁ ∨ z₁), (¬z₁ ∨ a₂ ∨ z₂), …, (¬z_{k-1} ∨ aₖ)` with fresh variables `zᵢ`. Original
  variable `n` is renamed to `2 n` (`ren`); fresh variable number `u` is `2 ^ (u + 1) + 1`
  (`fresh`, an odd number whose binary code is `true`, `u` times `false`, `true`). Fresh numbers
  are handed out from the last clause backwards (`to3Aux`), the order in which a machine walking
  the token stack `(Cslib.Complexity.SatVerifier.toks φ).reverse` meets the literals.
* `reduce3`: the reduction on bit strings; undecodable input goes to `[]`, which is not in
  `sat3Dec`.

Components:
1. correctness of `to3`: `CNFSat (to3 φ) ↔ CNFSat φ` and `is3 (to3 φ)`;
2. an emitter machine: from the token stack `(toks φ).reverse`, push `encodeCNF (to3 φ)` (so the
   output stack reads it top-first);
3. assembly: `IsPolyTime reduce3`, hence `PolyManyOneRed satDec sat3Dec` and NP-hardness of
   `sat3Dec`; and `sat3Dec ∈ NP` from the SAT verifier with a clause-length filter.
-/

@[expose] public section

namespace Cslib.Complexity.Karp

open Cslib.CookLevin Cslib.Logic.PL

/-- Every clause has at most three literals. -/
def is3 (φ : CNF) : Bool := φ.all fun C => decide (C.length ≤ 3)

open Classical in
/-- 3SAT: the encodings of satisfiable CNF formulas with at most three literals per clause. -/
noncomputable def sat3Dec : MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  decide (∃ φ : CNF, encodeCNF φ = x ∧ is3 φ = true ∧ CNFSat φ)

/-- Original variables are renamed to even numbers. -/
def ren (n : ℕ) : ℕ := 2 * n

/-- Fresh variable number `u`: the odd number `2 ^ (u + 1) + 1`. -/
def fresh (u : ℕ) : ℕ := 2 ^ (u + 1) + 1

/-- A literal with its variable renamed. -/
def renLit (l : ℕ × Bool) : ℕ × Bool := (ren l.1, l.2)

/-- The chain for the literals `l :: ls` after the first one, `z` being the number of the fresh
variable that the previous clause asserts: `(¬z ∨ l ∨ z')` per inner literal, `(¬z ∨ l)` at the
end. Fresh numbers decrease along the chain (they are handed out from its end). -/
def chainTail : List (ℕ × Bool) → ℕ → CNF
  | [], _ => []
  | [l], z => [[(fresh z, false), renLit l]]
  | l :: l' :: ls, z =>
      [(fresh z, false), renLit l, (fresh (z - 1), true)] :: chainTail (l' :: ls) (z - 1)

/-- The clauses replacing one clause, using fresh numbers from `u` on (`u + k - 2` down to `u` for
a clause of length `k ≥ 2`). -/
def chain : CNFClause → ℕ → CNF
  | [], _ => [[]]
  | [l], _ => [[renLit l]]
  | l :: l' :: ls, u =>
      [renLit l, (fresh (u + ls.length), true)] :: chainTail (l' :: ls) (u + ls.length)

/-- Fresh numbers used by one clause. -/
def used (C : CNFClause) : ℕ := C.length - 1

/-- The translation with the next free fresh number, processing the clauses from the last one. -/
def to3Aux : CNF → ℕ × CNF
  | [] => (0, [])
  | C :: φ => let r := to3Aux φ; (r.1 + used C, chain C r.1 ++ r.2)

/-- The SAT-to-3SAT translation. -/
def to3 (φ : CNF) : CNF := (to3Aux φ).2

/-- The reduction on bit strings. -/
def reduce3 (x : List Bool) : List Bool :=
  match decodeCNF x with
  | some φ => encodeCNF (to3 φ)
  | none => []

end Cslib.Complexity.Karp

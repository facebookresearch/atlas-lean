/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# INEQUIVALENCE OF LOOP PROGRAMS WITHOUT NESTING is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [PO14] INEQUIVALENCE OF LOOP
PROGRAMS WITHOUT NESTING;
R. L. Constable, H. B. Hunt III, and S. Sahni, "On the computational complexity of program
scheme equivalence", SIAM Journal on Computing 9 (1980), 396-416, doi:10.1137/0209031
(journal version of Cornell report TR 74-201 (1974), which Garey and Johnson cite; NP-hardness
of equivalence for the Loop 1 language);
D. Tsichritzis, "The equivalence problem of simple programs", Journal of the ACM 17 (1970),
729-738, doi:10.1145/321607.321621 (membership in NP).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import Mathlib.Logic.Function.Basic
public import Mathlib.Logic.Function.Iterate
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.InequivalenceLoopProgramsWithoutNesting

/-!
# INEQUIVALENCE OF LOOP PROGRAMS WITHOUT NESTING is NP-complete

Given a finite set `X` of variables, a subset `Y ⊆ X` of input variables, a specified output
variable `x₀ ∈ X`, and two programs `P₁` and `P₂`, each a sequence of instructions of the form
`x ← y`, `x ← x + 1`, `x ← 0`, `loop x`, and `end` with `x, y ∈ X`, where each `loop`
instruction is followed by a corresponding `end` instruction before any further `loop`
instruction occurs, is there an initial assignment `f : Y → ℤ⁺` such that the two programs halt
with different values for the output variable `x₀`?

Semantics (the Loop language of Meyer and Ritchie, restricted to loop depth `1`, the language
`L₁` of Tsichritzis and the Loop 1 language of Constable, Hunt and Sahni): variables hold
natural numbers; an input variable `y ∈ Y` starts at `f y ≥ 1` and every other variable starts
at `0`; `loop x … end` runs its body as many times as the value of `x` on entering the loop
(changes to `x` inside the body do not change that count). Every such program halts.

The variables are `0, …, n - 1`. An instruction is a triple `(op, x, y)`: `op = 0` is `x ← y`,
`1` is `x ← x + 1`, `2` is `x ← 0`, `3` is `loop x`, and `4` is `end`; operands an instruction
does not use are ignored. `WellFormed` requires opcodes `< 5`, operands `< n`, `Y` a set of
variables, `x₀` a variable, and, in each program, `loop` and `end` alternating, starting with a
`loop` and ending with an `end` (no nesting, no unmatched `loop` or `end`).

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instruction `(op, x, y)`: `x ← y` (`op = 0`), `x ← x + 1` (`1`), `x ← 0` (`2`),
`loop x` (`3`), or `end` (`4`). -/
abbrev Instruction := ℕ × ℕ × ℕ

/-- An instance: the number `n` of variables, the input variables `Y`, the output variable
`x₀`, and the programs `P₁` and `P₂`. -/
abbrev InequivalenceLoopProgramsInstance :=
  ℕ × List ℕ × ℕ × List Instruction × List Instruction

/-- Executes one assignment instruction (`x ← y`, `x ← x + 1`, or `x ← 0`) on the store `s`;
other opcodes leave the store unchanged. -/
def step (s : ℕ → ℕ) (c : Instruction) : ℕ → ℕ :=
  match c.1 with
  | 0 => Function.update s c.2.1 (s c.2.2)
  | 1 => Function.update s c.2.1 (s c.2.1 + 1)
  | 2 => Function.update s c.2.1 0
  | _ => s

/-- Runs a program on the store `s`. The second argument is `none` outside a loop and
`some (x, b)` inside `loop x`, with `b` the body read so far; at the matching `end` the body
runs `s x` times, `s` being the store on entering the loop. -/
def run : (ℕ → ℕ) → Option (ℕ × List Instruction) → List Instruction → ℕ → ℕ
  | s, _, [] => s
  | s, none, c :: p =>
      if c.1 = 3 then run s (some (c.2.1, [])) p else run (step s c) none p
  | s, some (x, b), c :: p =>
      if c.1 = 4 then run ((fun t => b.foldl step t)^[s x] s) none p
      else run s (some (x, b ++ [c])) p

/-- `LoopsUnnested inside p`: reading `p` from outside a loop (`inside = false`) or inside one
(`inside = true`), no `end` occurs outside a loop, no `loop` occurs inside one, and `p` ends
outside a loop. -/
def LoopsUnnested : Bool → List Instruction → Prop
  | inside, [] => inside = false
  | false, c :: p => c.1 ≠ 4 ∧ LoopsUnnested (c.1 == 3) p
  | true, c :: p => c.1 ≠ 3 ∧ LoopsUnnested (c.1 != 4) p

/-- Well-formedness of an instance: `Y` is a set of variables, `x₀` is a variable, every
instruction has an opcode `< 5` and operands `< n`, and both programs have unnested, matched
`loop`/`end` pairs. -/
def WellFormed (i : InequivalenceLoopProgramsInstance) : Prop :=
  i.2.1.Nodup ∧ (∀ y ∈ i.2.1, y < i.1) ∧ i.2.2.1 < i.1 ∧
    (∀ c ∈ i.2.2.2.1 ++ i.2.2.2.2, c.1 < 5 ∧ c.2.1 < i.1 ∧ c.2.2 < i.1) ∧
    LoopsUnnested false i.2.2.2.1 ∧ LoopsUnnested false i.2.2.2.2

/-- Some assignment of positive integers `f` to the input variables (every other variable
starting at `0`) makes the two programs end with different values of `x₀`. -/
def InequivalenceLoopProgramsFeasible (i : InequivalenceLoopProgramsInstance) : Prop :=
  ∃ f : ℕ → ℕ, (∀ y ∈ i.2.1, 0 < f y) ∧
    run (fun x => if x ∈ i.2.1 then f x else 0) none i.2.2.2.1 i.2.2.1 ≠
      run (fun x => if x ∈ i.2.1 then f x else 0) none i.2.2.2.2 i.2.2.1

open Classical in
/-- INEQUIVALENCE OF LOOP PROGRAMS WITHOUT NESTING as a decision problem over bitstrings. -/
noncomputable def inequivalenceLoopProgramsDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := InequivalenceLoopProgramsInstance) x with
  | some i => decide (WellFormed i ∧ InequivalenceLoopProgramsFeasible i)
  | none => false

/-- **INEQUIVALENCE OF LOOP PROGRAMS WITHOUT NESTING is NP-complete.** Source: Garey and
Johnson (1979), [PO14]; Constable, Hunt and Sahni (1974, 1980); Tsichritzis (1970). -/
public theorem_wanted inequivalenceLoopPrograms_npComplete :
    inequivalenceLoopProgramsDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L inequivalenceLoopProgramsDec

end MetaMathlibExt.Complexity.NPComplete.InequivalenceLoopProgramsWithoutNesting

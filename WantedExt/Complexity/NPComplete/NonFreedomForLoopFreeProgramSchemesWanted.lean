/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# NON-FREEDOM FOR LOOP-FREE PROGRAM SCHEMES is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), p. 278, problem [PO19]
NON-FREEDOM FOR LOOP-FREE PROGRAM SCHEMES (credited there to Constable, Hunt,
and Sahni, 1974, a Cornell technical report; transformation from 3SAT);
H. B. Hunt III, R. L. Constable, and S. Sahni, "On the computational complexity
of program scheme equivalence", SIAM Journal on Computing 9 (1980), 396-416,
doi:10.1137/0209031, the journal paper of that work.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Logic.Function.Basic
public import Mathlib.Logic.Relation

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.NonFreedomForLoopFreeProgramSchemes

/-!
# NON-FREEDOM FOR LOOP-FREE PROGRAM SCHEMES is NP-complete

INSTANCE: finite sets `F` and `P` of function and predicate symbols, a set `X` of variables,
and a loop-free monadic program scheme `S` over `F`, `P` and `X`, where such a scheme consists
of a sequence `I₁, I₂, ..., I_m` of instructions of the form `x ← f(y)`,
`if p(x) then goto I_j else goto I_k`, and `halt`, with `x ∈ X`, `f ∈ F` and `p ∈ P`, and must
be such that no directed cycles occur in the corresponding flow graph. QUESTION: is `S`
non-free, i.e., is there a directed path in the flow graph for `S` that can never be followed
in any computation, no matter what the interpretation of the functions and predicates in `F`
and `P` and the initial values for the variables in `X`?

Representation. Instructions are numbered `0, ..., m - 1`; `F`, `P` and `X` are
`{0, ..., |F| - 1}`, `{0, ..., |P| - 1}` and `{0, ..., |X| - 1}`. An instruction is
`(0, x, f, y, 0)` for `x ← f(y)`, `(1, p, x, j, k)` for `if p(x) then goto I_j else goto I_k`,
or `(2, 0, 0, 0, 0)` for `halt`. The flow graph has an arc from an assignment to the next
instruction (an assignment in the last place has no successor and ends the computation) and
from a test to its two targets. An interpretation is a type `D` with a function `D → D` for
each function symbol and a predicate `D → Bool` for each predicate symbol, and the initial
values are a state `X → D`.

Paths start at the first instruction `I₁`, as in the definition of free schemes (every path
from the start of the flow graph is followed by some computation). In a loop-free scheme every
path extends to a maximal one, and an extension of a path that is never followed is never
followed either, so it does not matter whether all paths or only maximal ones are counted.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: `|F|`, `|P|`, `|X|`, and the instruction list of `S` (each instruction
`(kind, a, b, c, d)` as in the module docstring). -/
abbrev NonFreedomForLoopFreeProgramSchemesInstance :=
  ℕ × ℕ × ℕ × List (ℕ × ℕ × ℕ × ℕ × ℕ)

/-- The flow graph of `S`: an arc from an assignment `k` to `k + 1` (when `k + 1 < m`), and
from a test `k` to each of its two targets. -/
def FlowArc (i : NonFreedomForLoopFreeProgramSchemesInstance) (k k' : ℕ) : Prop :=
  (∃ x f y, i.2.2.2[k]? = some (0, x, f, y, 0) ∧ k' = k + 1 ∧ k + 1 < i.2.2.2.length) ∨
    ∃ p x j l, i.2.2.2[k]? = some (1, p, x, j, l) ∧ (k' = j ∨ k' = l)

/-- Well-formedness of an instance: every instruction is an assignment `x ← f(y)` with
`x, y ∈ X` and `f ∈ F`, a test of `p ∈ P` on `x ∈ X` with both targets among the instructions,
or `halt`; and the flow graph has no directed cycle. -/
def WellFormed (i : NonFreedomForLoopFreeProgramSchemesInstance) : Prop :=
  (∀ ins ∈ i.2.2.2,
    (ins.1 = 0 ∧ ins.2.1 < i.2.2.1 ∧ ins.2.2.1 < i.1 ∧ ins.2.2.2.1 < i.2.2.1 ∧
        ins.2.2.2.2 = 0) ∨
      (ins.1 = 1 ∧ ins.2.1 < i.2.1 ∧ ins.2.2.1 < i.2.2.1 ∧ ins.2.2.2.1 < i.2.2.2.length ∧
        ins.2.2.2.2 < i.2.2.2.length) ∨
      ins = (2, 0, 0, 0, 0)) ∧
    ∀ k, ¬ Relation.TransGen (FlowArc i) k k

/-- A directed path in the flow graph starting at the first instruction. -/
def IsFlowPath (i : NonFreedomForLoopFreeProgramSchemesInstance) (π : List ℕ) : Prop :=
  π.head? = some 0 ∧ 0 < i.2.2.2.length ∧ π.IsChain (FlowArc i)

/-- `Follows i fI pI σ π`: the computation of `S` under the interpretation `fI`, `pI`, started
in state `σ` at the first vertex of `π`, follows `π`: each assignment updates the state, and at
each test the next vertex of `π` is the target the predicate's value selects. -/
def Follows (i : NonFreedomForLoopFreeProgramSchemesInstance) {D : Type}
    (fI : ℕ → D → D) (pI : ℕ → D → Bool) : (ℕ → D) → List ℕ → Prop
  | σ, k :: k' :: rest =>
    match i.2.2.2[k]? with
    | some (0, x, f, y, _) => Follows i fI pI (Function.update σ x (fI f (σ y))) (k' :: rest)
    | some (1, p, x, j, l) =>
      (if pI p (σ x) then k' = j else k' = l) ∧ Follows i fI pI σ (k' :: rest)
    | _ => False
  | _, _ => True

/-- `S` is non-free: some directed path from the first instruction is followed by no
computation, for every interpretation and every initial state. -/
def NonFreedomForLoopFreeProgramSchemesFeasible
    (i : NonFreedomForLoopFreeProgramSchemesInstance) : Prop :=
  ∃ π, IsFlowPath i π ∧ ∀ (D : Type) (fI : ℕ → D → D) (pI : ℕ → D → Bool) (σ : ℕ → D),
    ¬ Follows i fI pI σ π

open Classical in
/-- NON-FREEDOM FOR LOOP-FREE PROGRAM SCHEMES as a decision problem over bitstrings. -/
noncomputable def nonFreedomForLoopFreeProgramSchemesDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := NonFreedomForLoopFreeProgramSchemesInstance) x with
  | some i => decide (WellFormed i ∧ NonFreedomForLoopFreeProgramSchemesFeasible i)
  | none => false

/-- **NON-FREEDOM FOR LOOP-FREE PROGRAM SCHEMES is NP-complete.** Source: Garey and Johnson
(1979), [PO19]; Constable, Hunt, and Sahni (1974; journal version 1980). -/
public theorem_wanted nonFreedomForLoopFreeProgramSchemes_npComplete :
    nonFreedomForLoopFreeProgramSchemesDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L nonFreedomForLoopFreeProgramSchemesDec

end MetaMathlibExt.Complexity.NPComplete.NonFreedomForLoopFreeProgramSchemes

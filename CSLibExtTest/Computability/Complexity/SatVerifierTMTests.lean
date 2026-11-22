/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Complexity.SatVerifierTM
public meta import CSLibExt.Computability.Complexity.SatVerifierTM

/-! End-to-end tests for the assembled `TM2` SAT verifier. -/

namespace Cslib.Complexity.SatVerifier.Machine.Tests

open Turing Cslib.CookLevin Cslib.Logic.PL

/-- Step a `TM2` program until it halts, with fuel. -/
private def runF {K : Type} [DecidableEq K] {Γ : K → Type} {Λ σ : Type}
    (M : Λ → TM2.Stmt Γ Λ σ) : ℕ → TM2.Cfg Γ Λ σ → TM2.Cfg Γ Λ σ
  | 0, c => c
  | n + 1, c => match TM2.step M c with
    | some c' => runF M n c'
    | none => c

/-- The host machine's final configuration on `x # w` (`cap`: reject clauses longer than 3). -/
private def finalC (cap : Bool) (x w : List Bool) : TM2.Cfg HΓ HLab Bool :=
  runF (hprog cap) 200000
    ⟨some (.ph .m1), false, initS (Cslib.Complexity.DenseSAT.Verifier.pairEncode (x, w))⟩

/-- The uncapped (SAT) host's final configuration. -/
private def final (x w : List Bool) : TM2.Cfg HΓ HLab Bool := finalC false x w

/-- The output stack after halting. -/
private def out (x w : List Bool) : List Bool := (final x w).stk .out

/-- The capped (3SAT) host's output. -/
private def out3 (x w : List Bool) : List Bool := (finalC true x w).stk .out

/-- `(x₁ ∨ ¬x₂) ∧ ¬x₁`; variable `1` occurs twice. -/
private def φ : CNF := [[(1, true), (2, false)], [(1, false)]]

-- The only satisfying assignment `x₁ = x₂ = false`, listed per occurrence: accept.
#guard out (encodeCNF φ) [false, false, false] = [true]
-- `x₁ = true` falsifies the second clause: reject.
#guard out (encodeCNF φ) [true, false, true] = [false]
-- The first occurrence wins: the third bit disagrees with the first and is ignored.
#guard out (encodeCNF φ) [false, false, true] = [true]
-- A short witness reads missing values as `false`; a long one is truncated.
#guard out (encodeCNF φ) [false] = [true]
#guard out (encodeCNF φ) [false, false, false, true, true] = [true]
-- The machine agrees with `satVerifier` on a batch of witnesses.
#guard [[], [true], [false, true], [true, true, true], [false, true, false]].all fun w =>
  out (encodeCNF φ) w == [(satVerifier (encodeCNF φ, w)).ret]
-- Undecodable formulas are rejected: a non-canonical name, a truncated encoding.
#guard out [true, false, true, false, true, true, true, false, false, true] [] = [false]
#guard out (encodeCNF φ).dropLast [false, false, false] = [false]
-- The empty formula is accepted; a formula with an empty clause is rejected.
#guard out (encodeCNF []) [] = [true]
#guard out (encodeCNF [[(0, true)], []]) [true] = [false]
-- Halting configuration: no label, state `false`, every work stack empty.
#guard (final (encodeCNF φ) [false, false, false]).l = none
#guard (final (encodeCNF φ) [false, false, false]).var = false
#guard [HK.X, .W, .T, .B, .S, .A, .C, .V, .P, .F, .CC, .LC, .X1, .W1, .U].all fun k =>
  match k with
  | .inp | .out => true
  | k => ((final (encodeCNF φ) [true, false, true]).stk k).isEmpty

-- The capped host: clauses of at most three literals pass the filter, longer ones are rejected
-- even when the witness satisfies them.
#guard out3 (encodeCNF φ) [false, false, false] = [true]
#guard out3 (encodeCNF φ) [true, false, true] = [false]
#guard out3 (encodeCNF [[(1, true), (2, true), (3, true), (4, true)]]) [true] = [false]
#guard out (encodeCNF [[(1, true), (2, true), (3, true), (4, true)]]) [true] = [true]
#guard [[], [true], [false, true], [true, true, true]].all fun w =>
  out3 (encodeCNF φ) w == [ans true (encodeCNF φ, w)]

end Cslib.Complexity.SatVerifier.Machine.Tests

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Succinct 3SAT is NEXP-complete

Source:
C. H. Papadimitriou, Computational Complexity, Addison-Wesley, 1994, Theorem 20.3 (succinct
3SAT is NEXP-complete); C. H. Papadimitriou and M. Yannakakis, "A note on succinct
representations of graphs", Information and Control 71 (1986), 181-185.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.Computability.Complexity
public import MathlibExt.Computability.BinaryNatEncoding
public import CSLibExt.Computability.CookLevin
public import CSLibExt.Computability.Complexity.Classes

@[expose] public section

namespace MetaMathlibExt.Complexity.KeyTheorems.SuccinctThreeSATNEXPComplete

open Cslib.Complexity.Classes
open MetaMathlibExt.ComplexityTheory

/-!
# Succinct 3SAT is NEXP-complete

A *succinctly described* 3CNF formula with `2 ^ n` clauses over `2 ^ n` variables is given
by an ordinary circuit `C` with `n + 2` inputs: on input `(i, j)` (clause index `i` in `n`
bits, literal position `j ∈ {0, 1, 2}` in `2` bits), `C` outputs `n + 1` bits, the first `n`
giving the variable index of the `j`-th literal of clause `i` and the last giving its
polarity (`true` positive, `false` negated). The problem asks whether the formula is
satisfiable. It is `NEXP`-complete: guessing the exponentially long assignment and checking
the exponentially many clauses takes nondeterministic exponential time. The descriptor
must be valid (`s3WellFormed`): `C` has at least `n + 1` gates (so the `n + 1` outputs
exist), every gate has the right arity and shape for its kind, every input gate
references an input `< n + 2`, and every non-input gate references only strictly
earlier gates. Without this, missing outputs would silently read as `false`: e.g.
`C = []` would describe three copies of the negative literal on variable `0` in
every clause, so `(n, [])` would be accepted for every `n`, although it is not a
valid succinct-3SAT descriptor.
-/

/-- A gate of a flat Boolean circuit, encoded as `(kind, refs)`: the shared
serial encoding of `Cslib.Complexity.Classes.acGateOfPair`/`acGateToPair`. -/
abbrev S3Gate := ℕ × List ℕ

/-- Values of all gates of an encoded circuit, in order: the shared typed
evaluator `circuitEval` on the decoded gates, with `n + 2` inputs. -/
def s3CircuitEval (C : List S3Gate) (assign : List Bool) (n : ℕ) : List Bool :=
  circuitEval (C.map (acGateOfPair (n := n + 2))) (fun i => assign.getD i.val false)

/-- The last `k` gate values of an encoded circuit on an assignment (its outputs). -/
def s3CircuitOutputs (C : List S3Gate) (assign : List Bool) (k n : ℕ) : List Bool :=
  let vals := s3CircuitEval C assign n
  vals.drop (vals.length - k)

/-- Arity/shape validation for gate `j` of the description circuit on `n + 2`
inputs: input gates reference an input `< n + 2`, constant gates carry a bit
`≤ 1`, and every non-input gate references only strictly earlier gates. -/
def s3ValidGate (C : List S3Gate) (n j : ℕ) : Prop :=
  match C[j]? with
  | some (0, [i]) => i < n + 2
  | some (1, [b]) => b ≤ 1
  | some (2, [a]) => a < j
  | some (3, l) => ∀ a ∈ l, a < j
  | some (4, l) => ∀ a ∈ l, a < j
  | _ => False

/-- Well-formedness of the description circuit `C`: at least `n + 1` gates (so
the `n + 1` outputs exist), every gate arity/shape-valid, and the decoded
circuit is a `WellFormedCircuit`. -/
def s3WellFormed (C : List S3Gate) (n : ℕ) : Prop :=
  n + 1 ≤ C.length ∧
    (∀ j, j < C.length → s3ValidGate C n j) ∧
    WellFormedCircuit (C.map (acGateOfPair (n := n + 2)))

/-- The `n`-bit binary expansion of `i`, least significant bit first. -/
def s3BitsOf (i n : ℕ) : List Bool :=
  (List.range n).map (fun k => decide ((i / 2 ^ k) % 2 = 1))

/-- The number with binary expansion `bs`, least significant bit first. -/
def s3BitsToNum : List Bool → ℕ
  | [] => 0
  | b :: rest => (if b then 1 else 0) + 2 * s3BitsToNum rest

/-- The `j`-th literal of clause `i`: the variable index and polarity output by `C`. -/
def succLiteral (C : List S3Gate) (n i j : ℕ) : ℕ × Bool :=
  let outs := s3CircuitOutputs C (s3BitsOf i n ++ s3BitsOf j 2) (n + 1) n
  (s3BitsToNum (outs.take n), outs.getD n false)

/-- Clause `i` of the succinctly described formula, satisfied by `assign`. -/
def succClauseSat (C : List S3Gate) (n : ℕ) (assign : ℕ → Bool) (i : ℕ) : Prop :=
  ∃ j, j < 3 ∧
    match succLiteral C n i j with
    | (v, pol) => assign v = pol

open Classical in
/-- Succinct 3SAT as a decision problem over bitstrings, decoding to `(n, C)`: is the
succinctly described 3CNF formula satisfiable? Malformed descriptors
(`¬ s3WellFormed C n`) are rejected. -/
noncomputable def succinctThreeSatDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := ℕ × List S3Gate) x with
  | some i => decide (s3WellFormed i.2 i.1 ∧ ∃ assign : ℕ → Bool,
      ∀ c, c < 2 ^ i.1 → succClauseSat i.2 i.1 assign c)
  | none => false

/-- **Succinct 3SAT is NEXP-complete.** Source: C. H. Papadimitriou, Computational
Complexity, Addison-Wesley, 1994, Theorem 20.3 (succinct 3SAT is NEXP-complete); C. H.
Papadimitriou and M. Yannakakis, "A note on succinct representations of graphs", Information
and Control 71 (1986), 181-185. -/
public theorem_wanted succinct_three_sat_nexp_complete :
    succinctThreeSatDec ∈ NEXP ∧ ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
      L ∈ NEXP → Cslib.CookLevin.PolyManyOneRed L succinctThreeSatDec

end MetaMathlibExt.Complexity.KeyTheorems.SuccinctThreeSATNEXPComplete

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

/-- **Encoded gates.** An encoded gate is a pair $(k, r)$ of a natural number $k$, the kind of
the gate, and a list $r$ of natural numbers, its references. This is the (kind, references)
encoding of the gates of a flat Boolean circuit. -/
abbrev S3Gate := ℕ × List ℕ

/-- **Gate values of an encoded circuit.** Let $C = (g_0, \dots, g_{m-1})$ be a list of gates,
each encoded as a (kind, references) pair, let $\alpha$ be a list of booleans and let $n$ be a
natural number. The gate values of $C$ on $\alpha$ are the values $(v_0, \dots, v_{m-1})$ of the
flat Boolean circuit on $n + 2$ inputs obtained by decoding every $g_j$, when input $i$ is given
entry $i$ of $\alpha$, read as false when $i$ is at least the length of $\alpha$. -/
def s3CircuitEval (C : List S3Gate) (assign : List Bool) (n : ℕ) : List Bool :=
  circuitEval (C.map (acGateOfPair (n := n + 2))) (fun i => assign.getD i.val false)

/-- **Outputs of an encoded circuit.** Let $C$ be a list of $m$ gates encoded as
(kind, references) pairs, let $\alpha$ be a list of booleans and let $k$ and $n$ be natural
numbers. The last $k$ outputs of $C$ on $\alpha$ are the last $k$ of the gate values
$(v_0, \dots, v_{m-1})$ of $C$ on $\alpha$ as a circuit on $n + 2$ inputs, that is
$(v_{m-k}, \dots, v_{m-1})$; when $k > m$ they are all $m$ gate values. -/
def s3CircuitOutputs (C : List S3Gate) (assign : List Bool) (k n : ℕ) : List Bool :=
  let vals := s3CircuitEval C assign n
  vals.drop (vals.length - k)

/-- **Valid gates of a succinct 3SAT descriptor.** Let $C$ be a list of gates encoded as
(kind, references) pairs and let $n$ and $j$ be natural numbers. Gate $j$ of $C$ is valid when
$C$ has more than $j$ entries and its entry $j$ (counting from $0$) is one of: $(0, [i])$ with
$i < n + 2$ (an input gate); $(1, [b])$ with $b \le 1$ (a constant gate); $(2, [a])$ with
$a < j$ (a negation gate); or $(3, r)$ or $(4, r)$ where every entry $a$ of $r$ satisfies
$a < j$ (a conjunction or disjunction gate). Every other entry is invalid. -/
def s3ValidGate (C : List S3Gate) (n j : ℕ) : Prop :=
  match C[j]? with
  | some (0, [i]) => i < n + 2
  | some (1, [b]) => b ≤ 1
  | some (2, [a]) => a < j
  | some (3, l) => ∀ a ∈ l, a < j
  | some (4, l) => ∀ a ∈ l, a < j
  | _ => False

/-- **Well-formed succinct 3SAT descriptors.** Let $C$ be a list of gates encoded as
(kind, references) pairs and let $n$ be a natural number. The descriptor $C$ is well-formed for
$n$ when $C$ has at least $n + 1$ gates, every gate of $C$ is valid for $n$, and the flat Boolean
circuit on $n + 2$ inputs obtained by decoding every gate of $C$ is well-formed. -/
def s3WellFormed (C : List S3Gate) (n : ℕ) : Prop :=
  n + 1 ≤ C.length ∧
    (∀ j, j < C.length → s3ValidGate C n j) ∧
    WellFormedCircuit (C.map (acGateOfPair (n := n + 2)))

/-- **Lowest $n$ bits of a number, least significant first.** For natural numbers $i$ and $n$,
this is the list of booleans $(b_0, \dots, b_{n-1})$ of length $n$ in which $b_k$ is true exactly
when $\lfloor i / 2^k \rfloor$ is odd: the $n$ lowest binary digits of $i$, least significant bit
first. -/
def s3BitsOf (i n : ℕ) : List Bool :=
  (List.range n).map (fun k => decide ((i / 2 ^ k) % 2 = 1))

/-- **Value of a list of bits, least significant first.** A list of booleans
$(b_0, \dots, b_{m-1})$ represents the natural number $\sum_{k < m} [b_k]\, 2^k$, where $[b_k]$
is $1$ if $b_k$ is true and $0$ otherwise. -/
def s3BitsToNum : List Bool → ℕ
  | [] => 0
  | b :: rest => (if b then 1 else 0) + 2 * s3BitsToNum rest

/-- **Literals of a succinctly described formula.** Let $C$ be a list of gates encoded as
(kind, references) pairs and let $n$, $i$ and $j$ be natural numbers. Give $C$, as a circuit on
$n + 2$ inputs, the input consisting of the $n$ lowest bits of $i$ followed by the $2$ lowest
bits of $j$, each least significant bit first, and let $(o_0, \dots, o_{p-1})$ be its last
$n + 1$ outputs. Literal $j$ of clause $i$ is the pair $(v, s)$ with
$v = \sum_{k < \min(n, p)} [o_k]\, 2^k$, where $[o_k]$ is $1$ if $o_k$ is true and $0$
otherwise, and polarity $s = o_n$, read as false when $p \le n$. -/
def succLiteral (C : List S3Gate) (n i j : ℕ) : ℕ × Bool :=
  let outs := s3CircuitOutputs C (s3BitsOf i n ++ s3BitsOf j 2) (n + 1) n
  (s3BitsToNum (outs.take n), outs.getD n false)

/-- **Satisfied clauses of a succinctly described formula.** Let $C$ be a list of gates encoded
as (kind, references) pairs, let $n$ and $i$ be natural numbers, and let $\sigma$ assign a
boolean to every natural number. Clause $i$ of the formula described by $C$ for $n$ is satisfied
by $\sigma$ when, for some $j < 3$, literal $j$ of clause $i$ of that formula is a pair $(v, s)$
with $\sigma(v) = s$. -/
def succClauseSat (C : List S3Gate) (n : ℕ) (assign : ℕ → Bool) (i : ℕ) : Prop :=
  ∃ j, j < 3 ∧
    match succLiteral C n i j with
    | (v, pol) => assign v = pol

open Classical in
/-- **Succinct 3SAT.** Succinct 3SAT is the decision problem that accepts a bitstring $x$
exactly when $x$ decodes, under the canonical bitstring encoding, to a pair $(n, C)$ of a natural
number $n$ and a list $C$ of gates encoded as (kind, references) pairs such that $C$ is a
well-formed descriptor for $n$ and some assignment $\sigma$ of booleans to the natural numbers
satisfies clause $c$ of the formula described by $C$ for every $c < 2^n$. Bitstrings that do not
decode are rejected. -/
noncomputable def succinctThreeSatDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := ℕ × List S3Gate) x with
  | some i => decide (s3WellFormed i.2 i.1 ∧ ∃ assign : ℕ → Bool,
      ∀ c, c < 2 ^ i.1 → succClauseSat i.2 i.1 assign c)
  | none => false

/-- **Succinct 3SAT is NEXP-complete.** The succinct 3SAT decision problem lies in NEXP, and every
decision problem in NEXP has a polynomial-time many-one reduction to it.

Source: C. H. Papadimitriou, Computational
Complexity, Addison-Wesley, 1994, Theorem 20.3 (succinct 3SAT is NEXP-complete); C. H.
Papadimitriou and M. Yannakakis, "A note on succinct representations of graphs", Information
and Control 71 (1986), 181-185. -/
public theorem_wanted succinct_three_sat_nexp_complete :
    succinctThreeSatDec ∈ NEXP ∧ ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
      L ∈ NEXP → Cslib.CookLevin.PolyManyOneRed L succinctThreeSatDec

end MetaMathlibExt.Complexity.KeyTheorems.SuccinctThreeSATNEXPComplete

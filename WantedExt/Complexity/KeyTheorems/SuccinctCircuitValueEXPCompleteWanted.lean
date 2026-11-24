/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Succinct Circuit Value is EXP-complete

Source:
C. H. Papadimitriou, Computational Complexity, Addison-Wesley, 1994, Theorem 20.2 (succinct
versions of P-complete problems are EXP-complete); S. A. Cook, "A hierarchy for
nondeterministic time complexity", Journal of Computer and System Sciences 7 (1973),
343-353; R. E. Ladner, "The circuit value problem is log space complete for P", SIGACT
News 7 (1975), 18-20.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.Computability.Complexity
public import MathlibExt.Computability.BinaryNatEncoding
public import CSLibExt.Computability.CookLevin
public import CSLibExt.Computability.Complexity.Classes

@[expose] public section

namespace MetaMathlibExt.Complexity.KeyTheorems.SuccinctCircuitValueEXPComplete

open Cslib.Complexity.Classes
open MetaMathlibExt.ComplexityTheory

/-!
# Succinct Circuit Value is EXP-complete

A *succinctly described* circuit `D` with `2 ^ n` gates is given by an ordinary circuit `C`
with `n` inputs: on input `i` (as `n` bits), `C` outputs the description of gate `i` of `D`:
3 bits of gate type (`0` input, `1` AND, `2` OR, `3` NOT, `4` constant true, `5` constant
false), then `n` bits for the first predecessor index, then `n` bits for the second. The
first `n` gates of `D` are its input gates, fed by the `n`-bit string `x` given as part of
the instance; the problem asks whether the last gate of `D` outputs `true` on `x`. It is
`EXP`-complete: evaluating all `2 ^ n` gates takes exponential time, and every `EXP`
computation can be encoded. This is the EXP-complete analogue of the Circuit Value Problem;
unlike succinct SAT, there is no existential quantification over an exponentially long
assignment, which would make the problem NEXP-complete.
-/

/-- **Encoded gates (Succinct Circuit Value).** An encoded gate is a pair $(k, r)$ of a natural
number $k$, the kind of the gate, and a list $r$ of natural numbers, its references.

These pairs are the shared (kind, references) encoding of gates of flat Boolean circuits. -/
abbrev SCVGate := ℕ × List ℕ

/-- **Gate values of an encoded circuit (Succinct Circuit Value).** Let $C$ be a list of encoded
gates, $a$ a list of booleans and $n \in \mathbb{N}$. Decode each gate of $C$ into a gate of a
flat Boolean circuit on $n$ inputs, and assign to input $j < n$ the entry $a_j$ of $a$, read as
false when $j$ is at least the length of $a$. The result is the list of the values of all gates
of the decoded circuit under this assignment, in order. -/
def scvCircuitEval (C : List SCVGate) (assign : List Bool) (n : ℕ) : List Bool :=
  circuitEval (C.map (acGateOfPair (n := n))) (fun i => assign.getD i.val false)

/-- **Outputs of an encoded circuit (Succinct Circuit Value).** Let $C$ be a list of encoded
gates, $a$ a list of booleans and $k, n \in \mathbb{N}$. Decode each gate of $C$ into a gate of a
flat Boolean circuit on $n$ inputs and evaluate the decoded circuit with input $j < n$ set to the
entry $a_j$ of $a$, read as false when $j$ is at least the length of $a$. The outputs of $C$ on
$a$ are the last $k$ of the resulting gate values, or all of them if $C$ has fewer than $k$
gates. -/
def scvCircuitOutputs (C : List SCVGate) (assign : List Bool) (k n : ℕ) : List Bool :=
  let vals := scvCircuitEval C assign n
  vals.drop (vals.length - k)

/-- **Fixed-length binary expansion (Succinct Circuit Value).** For natural numbers $i$ and $n$,
this is the list of $n$ booleans $(b_0, \dots, b_{n-1})$, least significant bit first, where
$b_k$ is true exactly when $\lfloor i / 2^k \rfloor$ is odd. For $i < 2^n$ it is the $n$-bit
binary expansion of $i$; in general it is the $n$-bit expansion of $i \bmod 2^n$. -/
def scvBitsOf (i n : ℕ) : List Bool :=
  (List.range n).map (fun k => decide ((i / 2 ^ k) % 2 = 1))

/-- **Number with a given binary expansion (Succinct Circuit Value).** A list of booleans
$(b_0, \dots, b_{m-1})$, read least significant bit first, denotes the natural number
$\sum_{k < m} [b_k] \, 2^k$, where $[b_k]$ is $1$ if $b_k$ is true and $0$ otherwise; the empty
list denotes $0$. -/
def scvBitsToNum : List Bool → ℕ
  | [] => 0
  | b :: rest => (if b then 1 else 0) + 2 * scvBitsToNum rest

/-- **Gate description in a succinct circuit (Succinct Circuit Value).** Let $C$ be a list of
encoded gates and let $n, i \in \mathbb{N}$. Decode each gate of $C$ into a gate of a flat
Boolean circuit on $n$ inputs and evaluate it with input $j < n$ set to bit $j$ of $i$, least
significant bit first, that is, true exactly when $\lfloor i / 2^j \rfloor$ is odd. The
description of gate $i$ of the circuit succinctly described by $C$ is the list of the last
$2n + 3$ resulting gate values, or of all of them if $C$ has fewer than $2n + 3$ gates. -/
def succDesc (C : List SCVGate) (n i : ℕ) : List Bool :=
  scvCircuitOutputs C (scvBitsOf i n) (2 * n + 3) n

/-- **Decoded gate description (Succinct Circuit Value).** Let $C$ be a list of encoded gates,
let $n, i \in \mathbb{N}$, and let $d$ be the description of gate $i$ of the circuit succinctly
described by $C$: decode each gate of $C$ into a gate of a flat Boolean circuit on $n$ inputs,
evaluate the decoded circuit with input $j < n$ set to bit $j$ of $i$ (true exactly when
$\lfloor i / 2^j \rfloor$ is odd), and take the last $2n + 3$ gate values, or all of them if $C$
has fewer than $2n + 3$ gates. Read a list of booleans $(b_0, \dots, b_{m-1})$ as the number
$\sum_{k < m} [b_k] \, 2^k$, where $[b_k]$ is $1$ if $b_k$ is true and $0$ otherwise, so the
empty list reads as $0$. The information of gate $i$ is the triple $(t, p_1, p_2)$, where the
gate type $t$ is the number read from the first three entries of $d$, the first predecessor $p_1$
is the number read from the next $n$ entries, and the second predecessor $p_2$ is the number read
from all remaining entries; when $d$ is too short, each part uses only the entries that exist. -/
def succGateInfo (C : List SCVGate) (n i : ℕ) : ℕ × ℕ × ℕ :=
  let outs := succDesc C n i
  (scvBitsToNum (outs.take 3), scvBitsToNum ((outs.drop 3).take n),
    scvBitsToNum (outs.drop (3 + n)))

/-- **Value of a gate of a succinct circuit (Succinct Circuit Value).** Let $C$ be a list of
encoded gates, let $n, i \in \mathbb{N}$, let $x$ be a list of booleans (the input) and let $v$
be a list of booleans (the values of earlier gates), where an entry outside $x$ or $v$ reads as
false. Let $(t, p_1, p_2)$ be the decoded description of gate $i$ of the circuit succinctly
described by $C$. If $i < n$, gate $i$ is an input gate and its value is $x_i$. Otherwise its
value is $v_{p_1} \land v_{p_2}$ if $t = 1$, $v_{p_1} \lor v_{p_2}$ if $t = 2$, $\lnot v_{p_1}$
if $t = 3$, true if $t = 4$, and false for every other $t$, including $t = 0$ and $t = 5$. -/
def succGateVal (C : List SCVGate) (n : ℕ) (x : List Bool) (vs : List Bool)
    (i : ℕ) : Bool :=
  if i < n then x.getD i false
  else match succGateInfo C n i with
    | (1, p₁, p₂) => (vs.getD p₁ false) && (vs.getD p₂ false)
    | (2, p₁, p₂) => (vs.getD p₁ false) || (vs.getD p₂ false)
    | (3, p₁, _) => !(vs.getD p₁ false)
    | (4, _, _) => true
    | (5, _, _) => false
    | _ => false

/-- **Evaluation of a succinct circuit (Succinct Circuit Value).** Let $C$ be a list of encoded
gates, $n \in \mathbb{N}$ and $x$ a list of booleans. The gate values of the circuit with $2^n$
gates succinctly described by $C$ on input $x$ form the list $(v_0, \dots, v_{2^n - 1})$, where
each $v_i$ is the value of gate $i$ given $x$ and the values $(v_0, \dots, v_{i-1})$ of the
earlier gates. -/
def succEval (C : List SCVGate) (n : ℕ) (x : List Bool) : List Bool :=
  (List.range (2 ^ n)).foldl (fun vs i => vs ++ [succGateVal C n x vs i]) []

/-- **Well-formed description circuits (Succinct Circuit Value).** A list $C$ of encoded gates
is a well-formed description circuit on $n$ inputs when $C$ has at least $2n + 3$ gates and the
flat Boolean circuit on $n$ inputs obtained by decoding each gate of $C$ is well-formed, that
is, every gate references only strictly earlier gates.

The length bound guarantees that the $2n + 3$ outputs read as a gate description exist; without
it, missing outputs would silently read as false. -/
def succDescWellFormed (C : List SCVGate) (n : ℕ) : Prop :=
  2 * n + 3 ≤ C.length ∧ WellFormedCircuit (C.map (acGateOfPair (n := n)))

/-- **Well-formed succinct circuit descriptions.** Let $C$ be a list of encoded gates, read as a
flat Boolean circuit on $n$ inputs that describes a circuit $D$ with $2^n$ gates. For each gate
$i$ of $D$, let $t_i$, $p_i$ and $q_i$ be its gate type, first predecessor and second
predecessor, as decoded from the outputs of $C$ on the $n$-bit binary expansion of $i$. The
description is well formed when, for every $i < 2^n$: if $i < n$, then $t_i = 0$ (gate $i$ is an
input gate); and if $i \ge n$, then either $t_i = 4$ or $t_i = 5$ (a constant gate), or
$p_i < i$ and $q_i < i$. -/
def succWellFormed (C : List SCVGate) (n : ℕ) : Prop :=
  ∀ i, i < 2 ^ n →
    if i < n then (succGateInfo C n i).1 = 0
    else match succGateInfo C n i with
      | (4, _, _) => True
      | (5, _, _) => True
      | (_, p₁, p₂) => p₁ < i ∧ p₂ < i

open Classical in
/-- **Succinct Circuit Value.** The decision problem Succinct Circuit Value accepts a bitstring
exactly when it decodes to a triple $(n, C, x)$ of a natural number $n$, a list $C$ of encoded
gates and a bitstring $x$ such that: $x$ has length $n$; $C$ has at least $2n + 3$ gates and,
read as a flat Boolean circuit on $n$ inputs, is well formed; the circuit $D$ with $2^n$ gates
succinctly described by $C$, whose gate $i$ is described by the outputs of $C$ on the $n$-bit
binary expansion of $i$, is well formed; and the last gate of $D$ outputs true when the first
$n$ gates of $D$ are fed the bits of $x$. -/
noncomputable def succinctCircuitValueDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := ℕ × List SCVGate × List Bool) x with
  | some i => decide (i.2.2.length = i.1 ∧ succDescWellFormed i.2.1 i.1 ∧
      succWellFormed i.2.1 i.1 ∧
      (succEval i.2.1 i.1 i.2.2).getLast? = some true)
  | none => false

/-- **Succinct Circuit Value is EXP-complete.** The decision problem Succinct Circuit Value
belongs to the class EXP, and every decision problem in EXP reduces to Succinct Circuit Value
by a polynomial-time many-one reduction.

Source: C. H. Papadimitriou, Computational
Complexity, Addison-Wesley, 1994, Theorem 20.2 (succinct versions of P-complete problems
are EXP-complete); S. A. Cook, "A hierarchy for nondeterministic time complexity",
Journal of Computer and System Sciences 7 (1973), 343-353; R. E. Ladner, "The circuit
value problem is log space complete for P", SIGACT News 7 (1975), 18-20. -/
public theorem_wanted succinct_circuit_value_exp_complete :
    succinctCircuitValueDec ∈ EXP ∧ ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
      L ∈ EXP → Cslib.CookLevin.PolyManyOneRed L succinctCircuitValueDec

end MetaMathlibExt.Complexity.KeyTheorems.SuccinctCircuitValueEXPComplete

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Shannon: most Boolean functions need exponential circuits

Source:
C. E. Shannon, "The synthesis of two-terminal switching circuits", Bell System Technical
Journal 28 (1949), 59-98.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.Computability.Complexity
public import MathlibExt.Computability.BinaryNatEncoding
public import CSLibExt.Computability.CookLevin
public import CSLibExt.Computability.Complexity.Classes


@[expose] public section

namespace MetaMathlibExt.Complexity.KeyTheorems.ShannonHardFunction

open Cslib.Complexity.Classes
open MetaMathlibExt.ComplexityTheory

/-!
# Shannon: most Boolean functions need exponential circuits

For every number of inputs `n ≥ 10`, at least half of all Boolean functions on `n` bits are
hard: no well-formed mod-free circuit of wire count at most `2^n / (10 * n)` computes them.
Most Boolean functions need exponential-size circuits. Wire count is the total number of input
references (each gate's inputs counted with multiplicity), not the gate count: with unbounded
fan-in AND/OR gates, gate count alone does not bound the number of circuits. Circuits are the
shared flat gate lists; a circuit computes `f` when its last gate's value equals `f x` on every
`n`-bit input `x`.
-/


/-- **Wire count of a flat circuit.** The wire count of a flat Boolean circuit on $n$ inputs,
given as a list of gates, is the sum over its gates of the lengths of their predecessor lists:
every reference of a gate to a gate index is counted, with multiplicity, while input variables
and constants contribute nothing and the modulus of a mod gate is not counted. -/
def wireCount {n : ℕ} (C : List (ACGate n)) : ℕ :=
  (C.map gateInputs).flatten.length

/-- **Shannon: most Boolean functions need exponential circuits.** For every natural number
$n \ge 10$, at least $2^{2^n}/2$ of the Boolean functions $f$ on $n$ input bits have the
following property: for every well-formed flat Boolean circuit $C$ on $n$ inputs without mod
gates whose wire count (the total length of the predecessor lists of its gates) is at most
$\lfloor 2^n / (10 n) \rfloor$, there is an input $x \in \{0,1\}^n$ such that $C$ has no
gates or the value of the last gate of $C$ on $x$ differs from $f(x)$.

Source: C. E. Shannon, "The
synthesis of two-terminal switching circuits", Bell System Technical Journal 28 (1949),
59-98. -/
public theorem_wanted shannon_hard_function :
    ∀ n : ℕ, 10 ≤ n →
      (Set.ncard {f : (Fin n → Bool) → Bool | ∀ C : List (ACGate n),
        WellFormedCircuit C → IsModFree C → wireCount C ≤ 2 ^ n / (10 * n) →
          ∃ x : Fin n → Bool, (circuitEval C x).getLast? ≠ some (f x)} ≥
        2 ^ (2 ^ n) / 2)

end MetaMathlibExt.Complexity.KeyTheorems.ShannonHardFunction

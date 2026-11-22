/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Impagliazzo-Wigderson: exponential circuit hardness in E derandomizes BPP

Sources:
R. Impagliazzo and A. Wigderson, "P = BPP if E requires exponential circuits: Derandomizing the
XOR lemma", Proceedings of the 29th Annual ACM Symposium on Theory of Computing (STOC 1997),
220-229.
N. Nisan and A. Wigderson, "Hardness vs randomness", Journal of Computer and System Sciences 49
(1994), 149-167 (FOCS 1988).
S. Vadhan, "Pseudorandomness", Foundations and Trends in Theoretical Computer Science 7 (2012),
Theorem 7.19, Corollary 7.20, Corollary 7.64 (1) and Section 7.9.
-/

module

public import Batteries.Util.ProofWanted
public import MathlibExt.Computability.Complexity
public import MathlibExt.Computability.BinaryNatEncoding
public import CSLibExt.Computability.CookLevin
public import CSLibExt.Computability.Complexity.Classes


@[expose] public section

namespace MetaMathlibExt.Complexity.KeyTheorems.NisanWigderson

open Cslib.Complexity.Classes
open MetaMathlibExt.ComplexityTheory

/-!
# Impagliazzo-Wigderson: exponential circuit hardness in E derandomizes BPP

If `E` contains a function requiring exponential-size mod-free circuits for every input length
(size `≥ 2 ^ (n / c)` for some constant `c`), then `BPP = P`. This worst-case hardness form is the
theorem of Impagliazzo and Wigderson (1997): derandomized hardness amplification turns the hard
function into one that is hard on average, which feeds the Nisan-Wigderson pseudorandom generator.
Nisan and Wigderson (1994) had derived `BPP = P` from exponential *average-case* hardness. Hardness
is stated for well-formed mod-free flat circuits computing the function on `n`-bit inputs. The
declaration keeps its original name `nisan_wigderson`.
-/

/-- **Impagliazzo-Wigderson: exponential circuit hardness in E derandomizes BPP.** If some
`f ∈ E` and some `c > 0` are such that every mod-free circuit computing `f` on all `n`-bit inputs
has at least `2 ^ (n / c)` gates, for every `n`, then `BPP = P` (R. Impagliazzo and
A. Wigderson, "P = BPP if E requires exponential circuits: Derandomizing the XOR lemma", STOC
1997; S. Vadhan, *Pseudorandomness*, Foundations and Trends in Theoretical Computer Science 7
(2012), Corollary 7.64 (1), attributed to Impagliazzo and Wigderson in Section 7.9). The proof
builds the Nisan-Wigderson generator (N. Nisan and A. Wigderson, "Hardness vs randomness", Journal
of Computer and System Sciences 49 (1994), 149-167), which yields `BPP = P` from exponential
average-case hardness (Vadhan, Theorem 7.19 and Corollary 7.20). -/
public theorem_wanted nisan_wigderson :
    (∃ f : List Bool → Bool, f ∈ E ∧ ∃ c : ℕ, 0 < c ∧
      ∀ n : ℕ, ∀ C : List (ACGate n), WellFormedCircuit C → IsModFree C →
        (∀ x : List Bool, x.length = n →
          (circuitEval C (fun i => x.getD (i : ℕ) false)).getLast? = some (f x)) →
            C.length ^ c ≥ 2 ^ n) →
      BPP = MetaMathlibExt.ComplexityTheory.P

end MetaMathlibExt.Complexity.KeyTheorems.NisanWigderson

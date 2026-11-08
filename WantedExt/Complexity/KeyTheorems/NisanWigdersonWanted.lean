/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Nisan-Wigderson: exponential hardness in E derandomizes BPP

Source:
N. Nisan and A. Wigderson, "Hardness vs randomness", Journal of Computer and System Sciences 49
(1994), 149-167 (FOCS 1988).
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
# Nisan-Wigderson: exponential hardness in E derandomizes BPP

If `E` contains a function requiring exponential-size mod-free circuits for every input length
(size `≥ 2 ^ (n / c)` for some constant `c`), then `BPP = P`: the hard function builds a
pseudorandom generator that derandomizes every bounded-error algorithm. Hardness is stated for
well-formed mod-free flat circuits computing the function on `n`-bit inputs.
-/

/-- **Nisan-Wigderson: exponential hardness in E derandomizes BPP.** Source: N. Nisan and A.
Wigderson, "Hardness vs randomness", Journal of Computer and System Sciences 49 (1994),
149-167 (FOCS 1988). -/
public theorem_wanted nisan_wigderson :
    (∃ f : List Bool → Bool, f ∈ E ∧ ∃ c : ℕ, 0 < c ∧
      ∀ n : ℕ, ∀ C : List (ACGate n), WellFormedCircuit C → IsModFree C →
        (∀ x : List Bool, x.length = n →
          (circuitEval C (fun i => x.getD (i : ℕ) false)).getLast? = some (f x)) →
            C.length ^ c ≥ 2 ^ n) →
      BPP = MetaMathlibExt.ComplexityTheory.P

end MetaMathlibExt.Complexity.KeyTheorems.NisanWigderson

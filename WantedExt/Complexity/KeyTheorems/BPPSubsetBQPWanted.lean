/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Classes

/-!
# BPP is contained in BQP

Every bounded-error probabilistic polynomial-time language is decided by a uniform family of
polynomial-size quantum circuits with bounded error: prepare the random string in an equal
superposition and run a reversible version of the polynomial-time verifier, then measure the
output bit; the acceptance probability is unchanged. Not proved here: the argument needs a
compilation of a polynomial-time function (`IsPolyTime`) into polynomial-size reversible
circuits of the 2-local rational gates allowed by `Cslib.Complexity.Classes.BQP` (Toffoli gates
decomposed into controlled-`√NOT` and CNOT gates, and `√NOT` to produce unbiased random bits),
together with its uniform generation in polynomial time.

## Source

E. Bernstein and U. Vazirani, *Quantum complexity theory*, SIAM J. Comput. 26 (1997),
1411–1473; author-hosted version dated September 8, 1997, Theorem 8.2.2 (stated and proved
there for quantum Turing machines).
-/

@[expose] public section

namespace MetaMathlibExt.Complexity.KeyTheorems.BPPSubsetBQP

open Cslib.Complexity.Classes

/-- **BPP is contained in BQP.** Every language decided with bounded error by a probabilistic
polynomial-time verifier (`BPP`) is decided with bounded error by a uniform family of
polynomial-size quantum circuits (`BQP`) (E. Bernstein and U. Vazirani, *Quantum complexity
theory*, SIAM J. Comput. 26 (1997), 1411–1473, Theorem 8.2.2 in the author-hosted version dated
September 8, 1997, where `BQP` is defined by quantum Turing machines; here `BQP` is the circuit
class `Cslib.Complexity.Classes.BQP`). -/
public theorem_wanted bpp_subset_bqp :
    BPP ⊆ BQP

end MetaMathlibExt.Complexity.KeyTheorems.BPPSubsetBQP

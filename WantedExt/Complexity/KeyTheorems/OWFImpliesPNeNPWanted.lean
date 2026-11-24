/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# One-way functions imply P != NP

Source:
O. Goldreich, Foundations of Cryptography, Vol. 1, Cambridge University Press,
2001, Section 2.2 (one-way functions imply P ≠ NP); R. Impagliazzo, "A personal
view of average-case complexity", Proceedings of the Tenth Annual Structure in
Complexities Theory Conference (1995), 134-147 (five worlds).
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.Computability.Complexity
public import MathlibExt.Computability.BinaryNatEncoding
public import CSLibExt.Computability.CookLevin
public import CSLibExt.Computability.Complexity.Classes


@[expose] public section

namespace MetaMathlibExt.Complexity.KeyTheorems.OWFImpliesPNeNP

open Cslib.Complexity.Classes
open MetaMathlibExt.ComplexityTheory

/-!
# One-way functions imply P != NP

If a one-way function family exists, then `P ≠ NP`. Not proved here: the
proof inverts the one-way function prefix by prefix, using the hypothesis
`P = NP` to turn "some extension of this prefix has a preimage" (an `NP`
predicate) into a polynomial-time decision at each step; formalizing that
needs an `NP` verifier for the prefix-extension language, an `IsPolyTime`
decision procedure from `P = NP`, and a polynomial-time probabilistic inverter
built from them (the inverter receives the security parameter `n` explicitly,
as in the shared definition), none of which follows from the definitions alone.
-/

/-- **One-way functions imply P ≠ NP.** If some family $f$, assigning to each natural number $n$
and each $n$-bit string $x$ a bitstring $f_n(x)$, is a one-way function family, then
$\mathrm{P} \neq \mathrm{NP}$.

Source: O. Goldreich, Foundations of
Cryptography, Vol. 1, Cambridge University Press, 2001, Section 2.2 (one-way
functions imply P ≠ NP); R. Impagliazzo, "A personal view of average-case
complexity", Proceedings of the Tenth Annual Structure in Complexities Theory
Conference (1995), 134-147 (five worlds). -/
public theorem_wanted owf_implies_p_ne_np :
    ∀ f : (n : ℕ) → (Fin n → Bool) → List Bool, IsOneWayFunction f → P ≠ NP

end MetaMathlibExt.Complexity.KeyTheorems.OWFImpliesPNeNP

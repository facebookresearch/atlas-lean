/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Sipser-Gács-Lautemann: BPP is in Sigma_2 and Pi_2

Source:
M. Sipser, "A complexity theoretic approach to randomness", Proceedings of the Fifteenth Annual
ACM Symposium on Theory of Computing (STOC 1983), 330-335; P. Gács (unpublished); C. Lautemann,
"BPP and the polynomial hierarchy", Information Processing Letters 17 (1983), 215-217.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.Computability.Complexity
public import MathlibExt.Computability.BinaryNatEncoding
public import CSLibExt.Computability.CookLevin
public import CSLibExt.Computability.Complexity.Classes


@[expose] public section

namespace MetaMathlibExt.Complexity.KeyTheorems.SipserGacs

open Cslib.Complexity.Classes
open MetaMathlibExt.ComplexityTheory

/-!
# Sipser-Gács-Lautemann: BPP is in Sigma_2 and Pi_2

Every bounded-error probabilistic polynomial-time language is in `Σ₂^p ∩ Π₂^p`: bounded-error
randomness can be simulated by two alternating quantifier blocks. `Σ₂^p` and `Π₂^p` are the
alternating-quantifier classes of the shared file.
-/

/-- **Sipser-Gács-Lautemann: BPP is in $\Sigma_2^p$ and $\Pi_2^p$.** Every decision problem in
BPP lies in $\Sigma_2^p$ and in $\Pi_2^p$, the classes of the polynomial hierarchy defined by two
alternating blocks of polynomially bounded quantifiers, beginning with $\exists$ and with
$\forall$ respectively.

Source: M. Sipser, "A complexity
theoretic approach to randomness", Proceedings of the Fifteenth Annual ACM Symposium on
Theory of Computing (STOC 1983), 330-335; P. Gács (unpublished); C. Lautemann, "BPP and
the polynomial hierarchy", Information Processing Letters 17 (1983), 215-217. -/
public theorem_wanted sipser_gacs_lautemann :
    BPP ⊆ SigmaK 2 ∧ BPP ⊆ PiK 2

end MetaMathlibExt.Complexity.KeyTheorems.SipserGacs

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# IP = PSPACE (Shamir)

Source:
A. Shamir, "IP = PSPACE", Journal of the ACM 39 (1992), 869-877 (FOCS 1990); see also C. Lund,
L. Fortnow, H. Karloff, and N. Nisan, "Algebraic methods for interactive proof systems",
Journal of the ACM 39 (1992), 859-868.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.Computability.Complexity
public import MathlibExt.Computability.BinaryNatEncoding
public import CSLibExt.Computability.CookLevin
public import CSLibExt.Computability.Complexity.Classes


@[expose] public section

namespace MetaMathlibExt.Complexity.KeyTheorems.IPEqualsPSPACE

open Cslib.Complexity.Classes
open MetaMathlibExt.ComplexityTheory

/-!
# IP = PSPACE (Shamir)

Interactive polynomial-time proofs capture exactly polynomial space: the interactive-proof
class `IP` of the shared file (polynomially many rounds, polynomially many verifier coins,
completeness at least `2/3`, soundness at most `1/3`) equals `PSPACE`.
-/

/-- **IP = PSPACE (Shamir).** The class $\mathsf{IP}$ of decision problems that have
interactive proofs (a polynomial-time verifier using polynomially many rounds and random coins,
with completeness at least $2/3$ and soundness at most $1/3$ against every prover) equals the
class $\mathrm{PSPACE}$ of decision problems whose languages are decided by multi-tape Turing
machines in polynomial space.

Source: A. Shamir, "IP = PSPACE", Journal of the ACM 39 (1992),
869-877 (FOCS 1990); see also C. Lund, L. Fortnow, H. Karloff, and N. Nisan, "Algebraic
methods for interactive proof systems", Journal of the ACM 39 (1992), 859-868. -/
public theorem_wanted ip_eq_pspace :
    IP = PSPACE

end MetaMathlibExt.Complexity.KeyTheorems.IPEqualsPSPACE

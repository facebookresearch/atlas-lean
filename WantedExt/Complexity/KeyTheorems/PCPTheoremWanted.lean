/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# The PCP theorem: NP = PCP(O(log n), O(1))

Source:
S. Arora, C. Lund, R. Motwani, M. Sudan, and M. Szegedy, "Proof verification and the hardness
of approximation problems", Journal of the ACM 45 (1998), 501-555 (FOCS 1992); S. Arora and S.
Safra, "Probabilistic checking of proofs: a new characterization of NP", Journal of the ACM 45
(1998), 70-122.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.Computability.Complexity
public import MathlibExt.Computability.BinaryNatEncoding
public import CSLibExt.Computability.CookLevin
public import CSLibExt.Computability.Complexity.Classes
public import Mathlib.Data.Nat.Log

@[expose] public section

namespace MetaMathlibExt.Complexity.KeyTheorems.PCPTheorem

open Cslib.Complexity.Classes
open MetaMathlibExt.ComplexityTheory

/-!
# The PCP theorem: NP = PCP(O(log n), O(1))

Every `NP` language has a probabilistically checkable proof using `O(log n)` random bits and
`O(1)` queries to the proof: `NP = PCP(O(log n), O(1))`. `PCP` is the non-adaptive verifier
definition of the shared file; the randomness coefficient and the query constant are
existentially quantified per language, as in the cited theorems: the class is the union over
constants.
-/

/-- **The PCP theorem: NP = PCP(O(log n), O(1)).** Source: S. Arora, C. Lund, R. Motwani, M.
Sudan, and M. Szegedy, "Proof verification and the hardness of approximation problems",
Journal of the ACM 45 (1998), 501-555 (FOCS 1992); S. Arora and S. Safra, "Probabilistic
checking of proofs: a new characterization of NP", Journal of the ACM 45 (1998), 70-122. -/
public theorem_wanted pcp_theorem :
    MetaMathlibExt.ComplexityTheory.NP =
      {L : MetaMathlibExt.ComplexityTheory.DecisionProblem |
        ∃ c q, L ∈ PCP (fun n => c * Nat.log 2 (n + 1)) (fun _ => q)}

end MetaMathlibExt.Complexity.KeyTheorems.PCPTheorem

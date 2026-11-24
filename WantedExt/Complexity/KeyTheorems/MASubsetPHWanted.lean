/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MA is contained in PH

Source:
L. Babai, "Trading group theory for randomness", Proceedings of the Seventeenth
Annual ACM Symposium on Theory of Computing (STOC 1985), 421-429 (MA ⊆ AM,
AM ⊆ Π₂); L. J. Stockmeyer, "The polynomial-time hierarchy", Theoretical
Computer Science 3 (1977), 1-22 (PH); S. Arora and B. Barak, Computational
Complexity: A Modern Approach, 2009, Theorem 5.4 (PH ⊆ PSPACE) and Chapter 8.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.Computability.Complexity
public import MathlibExt.Computability.BinaryNatEncoding
public import CSLibExt.Computability.CookLevin
public import CSLibExt.Computability.Complexity.Classes


@[expose] public section

namespace MetaMathlibExt.Complexity.KeyTheorems.MASubsetPH

open Cslib.Complexity.Classes
open MetaMathlibExt.ComplexityTheory

/-!
# MA is contained in PH

Every Merlin-Arthur language is in the polynomial hierarchy. The route is
`MA ⊆ AM` (error amplification plus a union bound over Merlin's messages),
`AM ⊆ Π₂^p` (Babai's set lower-bound protocol, a separate `WantedExt` entry),
and `Π₂^p ⊆ PH` (a `Π₂` statement is a `Σ₃` statement with a dummy leading
existential block). Not proved here: each step needs a new verifier
(amplified, or with the set lower-bound protocol's quantifiers), and showing
those verifiers are polynomial-time is a Turing-machine construction, not a
definitional unfolding.
-/

/-- **MA is contained in PH.** Every decision problem in the class $\mathsf{MA}$ is in the
polynomial hierarchy $\mathsf{PH}$.

Source: L. Babai, "Trading group theory for randomness",
Proceedings of the Seventeenth Annual ACM Symposium on Theory of Computing
(STOC 1985), 421-429 (MA ⊆ AM, AM ⊆ Π₂); L. J. Stockmeyer, "The polynomial-time
hierarchy", Theoretical Computer Science 3 (1977), 1-22 (PH); S. Arora and
B. Barak, Computational Complexity: A Modern Approach, 2009, Theorem 5.4
(PH ⊆ PSPACE) and Chapter 8. -/
public theorem_wanted ma_subset_ph :
    MA ⊆ PH

end MetaMathlibExt.Complexity.KeyTheorems.MASubsetPH

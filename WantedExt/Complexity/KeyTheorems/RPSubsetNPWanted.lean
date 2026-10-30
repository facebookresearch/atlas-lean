/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# RP is contained in NP

Source:
S. Arora and B. Barak, Computational Complexity: A Modern Approach, 2009, Theorem 7.3
(RP ⊆ NP); M. Sipser, Introduction to the Theory of Computation, 3rd ed., 2013,
Theorem 10.13.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.Computability.Complexity
public import MathlibExt.Computability.BinaryNatEncoding
public import CSLibExt.Computability.CookLevin
public import CSLibExt.Computability.Complexity.Classes


@[expose] public section

namespace MetaMathlibExt.Complexity.KeyTheorems.RPSubsetNP

open Cslib.Complexity.Classes
open MetaMathlibExt.ComplexityTheory

/-!
# RP is contained in NP

Every one-sided-error randomized polynomial-time language is in `NP`: the random
string itself is the witness. Not proved here: the counting definition of `RP`
constrains the verifier only on full-length random strings, while the `NP`
verifier must accept a witness of length at most the bound; the proof pads a
short witness out to full length, and showing the padded verifier is
polynomial-time is a Turing-machine construction (`IsPolyTime` of the padding
map composed with the original verifier), not a logical consequence of the
definitions.
-/

/-- **RP is contained in NP.** Source: S. Arora and B. Barak, Computational Complexity:
A Modern Approach, 2009, Theorem 7.3 (RP ⊆ NP); M. Sipser, Introduction to the
Theory of Computation, 3rd ed., 2013, Theorem 10.13. -/
public theorem_wanted rp_subset_np :
    RP ⊆ NP

end MetaMathlibExt.Complexity.KeyTheorems.RPSubsetNP

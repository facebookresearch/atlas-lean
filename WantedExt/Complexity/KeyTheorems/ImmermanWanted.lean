/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Immerman-Szelepcsenyi theorem: NL = coNL

Source:
N. Immerman, "Nondeterministic space is closed under complementation", SIAM Journal on
Computing 17 (1988), 935-938; R. Szelepcsenyi, "The method of forced enumeration for
nondeterministic automata", Acta Informatica 26 (1988), 279-284.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.Computability.Complexity
public import MathlibExt.Computability.BinaryNatEncoding
public import CSLibExt.Computability.CookLevin
public import CSLibExt.Computability.Complexity.Classes


@[expose] public section

namespace MetaMathlibExt.Complexity.KeyTheorems.Immerman

open Cslib.Complexity.Classes
open MetaMathlibExt.ComplexityTheory

/-!
# Immerman-Szelepcsenyi theorem: NL = coNL

Nondeterministic logarithmic space is closed under complementation: `NL = coNL`, where `coNL`
is the class of complements of `NL` languages (complementation of decision problems). The proof
is inductive counting of reachable configurations.
-/

/-- **Immerman-Szelepcsenyi theorem: NL = coNL.** The complexity class NL is closed under
complementation: a decision problem $L$ belongs to NL if and only if its complement, the decision
problem that is true exactly on the bitstrings where $L$ is false, belongs to NL.

Source: N. Immerman, "Nondeterministic space
is closed under complementation", SIAM Journal on Computing 17 (1988), 935-938; R.
Szelepcsenyi, "The method of forced enumeration for nondeterministic automata", Acta
Informatica 26 (1988), 279-284. -/
public theorem_wanted immerman_szelepcsenyi :
    NL = {L : MetaMathlibExt.ComplexityTheory.DecisionProblem | Lᶜ ∈ NL}

end MetaMathlibExt.Complexity.KeyTheorems.Immerman

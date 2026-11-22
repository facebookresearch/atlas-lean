/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# An oracle separates NP from coNP

Source:
T. Baker, J. Gill, and R. Solovay, "Relativizations of the P =? NP question",
SIAM Journal on Computing 4 (1975), 431-442 (oracles separating NP from coNP);
S. Arora and B. Barak, Computational Complexity: A Modern Approach, 2009,
Chapter 3 (relativization).
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.Computability.Complexity
public import MathlibExt.Computability.BinaryNatEncoding
public import CSLibExt.Computability.CookLevin
public import CSLibExt.Computability.Complexity.Classes


@[expose] public section

namespace MetaMathlibExt.Complexity.KeyTheorems.OracleNPCoNPSeparation

open Cslib.Complexity.Classes
open MetaMathlibExt.ComplexityTheory

/-!
# An oracle separates NP from coNP

Beyond Baker-Gill-Solovay (which separates `P` from `NP` relative to an
oracle): there is an oracle relative to which `NP` is not closed under
complement, i.e. `NP^O ≠ coNP^O`. Not proved here: the proof is a
diagonalization (finite-injury construction) against all relativized `NP`
machines, building the oracle in stages and defeating each machine's
attempt to decide the diagonal language and its complement; formalizing it
needs an enumeration of oracle machines and a stage-by-stage oracle
construction, far beyond the oracle-machine model of the shared file.
-/

/-- **An oracle separates NP from coNP.** There is an oracle $O$, a function from bitstrings to
booleans, such that $\mathrm{NP}^O$ differs from the class $\mathrm{coNP}^O$ of decision problems
$L$ whose complement, the decision problem that accepts exactly the bitstrings that $L$ rejects,
belongs to $\mathrm{NP}^O$.

Source: T. Baker, J. Gill, and
R. Solovay, "Relativizations of the P =? NP question", SIAM Journal on
Computing 4 (1975), 431-442 (oracles separating NP from coNP); S. Arora and
B. Barak, Computational Complexity: A Modern Approach, 2009, Chapter 3
(relativization). -/
public theorem_wanted oracle_np_co_np_separation :
    ∃ O : List Bool → Bool, NPWithOracle O ≠ {L | Lᶜ ∈ NPWithOracle O}

end MetaMathlibExt.Complexity.KeyTheorems.OracleNPCoNPSeparation

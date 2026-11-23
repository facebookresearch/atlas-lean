/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Savitch's theorem: NPSPACE = PSPACE

Source:
W. J. Savitch, "Relationships between nondeterministic and deterministic tape complexities",
Journal of Computer and System Sciences 4 (1970), 177-192.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.Computability.Complexity
public import MathlibExt.Computability.BinaryNatEncoding
public import CSLibExt.Computability.CookLevin
public import CSLibExt.Computability.Complexity.Classes


@[expose] public section

namespace MetaMathlibExt.Complexity.KeyTheorems.Savitch

open Cslib.Complexity.Classes
open MetaMathlibExt.ComplexityTheory

/-!
# Savitch's theorem: NPSPACE = PSPACE

Nondeterministic polynomial space equals deterministic polynomial space. The shared `NPSPACE`
is the nondeterministic multi-tape polynomial-space class; `PSPACE` is the deterministic multi-
tape class.
-/

/-- **Savitch's theorem: NPSPACE = PSPACE.** The complexity class NPSPACE of decision problems
decided in polynomial space by nondeterministic multi-tape Turing machines equals the class
PSPACE of decision problems decided in polynomial space by deterministic multi-tape Turing
machines.

Source: W. J. Savitch, "Relationships between
nondeterministic and deterministic tape complexities", Journal of Computer and System
Sciences 4 (1970), 177-192. -/
public theorem_wanted savitch :
    NPSPACE = PSPACE

end MetaMathlibExt.Complexity.KeyTheorems.Savitch

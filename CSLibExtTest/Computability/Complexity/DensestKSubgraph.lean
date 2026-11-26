/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Computability.Complexity.DensestKSubgraph
import CSLibExt.Computability.Complexity.DensestKSubgraph.Internal.Verifier.Canonical
meta import CSLibExt.Computability.Complexity.DensestKSubgraph.Internal.Verifier.Machine
meta import CSLibExt.Computability.Complexity.DensestKSubgraph.Internal.Verifier.Canonical
meta import MathlibExt.Computability.Complexity
meta import Mathlib.Computability.Encoding

/-! # Execute the actual marked verifier on acceptance and rejection cases -/

open Turing MetaMathlibExt BitstringEncoding
open MetaMathlibExt.Complexity.NPComplete.DensestKSubgraph
open Cslib.Complexity.DensestKSubgraph.Internal VerifierMachine

private def verdictWithin : ℕ → TM2.Cfg Γ Lab Bool → Option Bool
  | 0, _ => none
  | fuel + 1, c =>
    match c.l with
    | some .yes => some true
    | some .no => some false
    | _ => (TM2.step prog c).bind (verdictWithin fuel)

private def runRaw (x w : List Bool) : Option Bool :=
  verdictWithin 20000 ⟨some (.dec (.split .read)), false, init x w⟩

private def runInstance (i : DensestKSubgraphInstance) (w : List Bool) : Option Bool :=
  runRaw (bitEncode i) w

-- Expected .no, rather than exhaustion of the test budget.
#guard runRaw [] [] == some false
#guard runRaw [true] [] == some false
#guard runRaw (delimit (bitEncode (2 : ℕ)) ++ [true]) [] == some false

-- Bounds, empty witnesses and isolated vertices; n and k are still read in binary.
#guard runInstance (0, [], 0, 0) [] == some true
#guard runInstance (0, [], 1, 0) [] == some false
#guard runInstance (0, [], 0, 1) [] == some false
#guard runInstance (2 ^ 40, [], 2 ^ 40, 0) [] == some true
#guard runInstance (2 ^ 40, [(1, 2)], 2 ^ 40, 1) [true] == some true
#guard runInstance (2 ^ 40, [(1, 2)], 2 ^ 40, 2 ^ 39) [true] == some false
#guard runInstance (2, [(0, 1)], 0, 0) [false] == some true

-- The edge count and the distinct-vertex count are different.
#guard runInstance (5, [(3, 1), (1, 4)], 3, 2) [true, true] == some true
#guard runInstance (5, [(3, 1), (1, 4)], 2, 2) [true, true] == some false
#guard runInstance (5, [(3, 1), (1, 4)], 2, 2) [true, false] == some false
#guard runInstance (5, [(3, 1), (1, 4)], 2, 1) [false, true] == some true

-- Malformation is rejected regardless of whether the offending edge is marked.
#guard runInstance (2, [(0, 0)], 0, 0) [false] == some false
#guard runInstance (2, [(2, 0)], 0, 0) [false] == some false
#guard runInstance (2, [(0, 2)], 0, 0) [false] == some false
#guard runInstance (2, [(0, 1), (0, 1)], 0, 0) [false, false] == some false
#guard runInstance (2, [(0, 1), (1, 0)], 0, 0) [false, false] == some false

-- The mask is consumed in lockstep with the explicit edge stream.
#guard runInstance (2, [(0, 1)], 2, 1) [] == some false
#guard runInstance (2, [(0, 1)], 2, 1) [true, false] == some false
#guard runInstance (2, [], 0, 0) [true] == some false

-- Mathlib's total Nat decoder accepts this noncanonical payload as 2.
#guard runRaw (delimit [false] ++ bitEncode (([], 2, 0) : List (ℕ × ℕ) × ℕ × ℕ)) [] == some true

example : densestKSubgraphDec (bitEncode ((2 ^ 40, [], 2 ^ 40, 0) : DensestKSubgraphInstance)) =
    true := (densestKSubgraphDec_iff_marks _).mpr ⟨[], Nat.zero_le _, by decide⟩

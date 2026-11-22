/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Baker-Gill-Solovay: oracles separate and collapse P vs NP

Source:
T. Baker, J. Gill, and R. Solovay, "Relativizations of the P =? NP question", SIAM Journal on
Computing 4 (1975), 431-442.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.Computability.Complexity
public import MathlibExt.Computability.BinaryNatEncoding
public import CSLibExt.Computability.CookLevin
public import CSLibExt.Computability.Complexity.Classes


@[expose] public section

namespace MetaMathlibExt.Complexity.KeyTheorems.BakerGillSolovay

open Cslib.Complexity.Classes
open MetaMathlibExt.ComplexityTheory

/-!
# Baker-Gill-Solovay: oracles separate and collapse P vs NP

There is an oracle relative to which `P ≠ NP`, and there is an oracle relative to which `P =
NP`. Relativized classes are the oracle classes of the shared file, with the oracle given as a
Boolean function. This is the relativization barrier: diagonalization alone cannot settle `P`
vs `NP`.
-/

/-- **Baker-Gill-Solovay: oracles separate and collapse P vs NP.** Source: T. Baker, J. Gill,
and R. Solovay, "Relativizations of the P =? NP question", SIAM Journal on Computing 4
(1975), 431-442. -/
public theorem_wanted baker_gill_solovay :
    (∃ O : List Bool → Bool, PWithOracle O ≠ NPWithOracle O) ∧
      (∃ O : List Bool → Bool, PWithOracle O = NPWithOracle O)

end MetaMathlibExt.Complexity.KeyTheorems.BakerGillSolovay

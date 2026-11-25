/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Crypto.Identification.RewindingSimulator
public import Mathlib.Tactic.NormNum.Prime

/-!
# Tests for the rewinding simulator

Schnorr's protocol in `ZMod 11` written multiplicatively, with the witness `7`, against a
verifier whose challenge is the discrete logarithm of the commitment (a function of the commitment
only): one attempt succeeds and passes a test with probability `1/11` of the real one, and `k`
attempts are within `(10/11)^k` of the real view. Large challenge sets make the simulation slow,
which is why the rewinding argument is used with two-element challenge sets.
-/

@[expose] public section

namespace Cslib.Crypto.RewindingSimulatorTests

open Cslib.Crypto.Framework Cslib.Crypto.Identification Cslib.Crypto.PublicKey

/-- `ZMod 11`, written multiplicatively. -/
abbrev G11 := Multiplicative (ZMod 11)

/-- The generator. -/
abbrev g : G11 := Multiplicative.ofAdd 1

theorem g_pow : g ^ 11 = 1 := by decide

instance : Fact (Nat.Prime 11) := ⟨by norm_num⟩

/-- The statement `y = g ^ 7`. -/
def y : {y : G11 // y ^ 11 = 1} := ⟨gpow g (7 : ZMod 11), by decide⟩

/-- A verifier that asks the discrete logarithm of the commitment. -/
def Vstar : G11 → Unit → ZMod 11 := fun I _ => Multiplicative.toAdd I

example (T : Unit × G11 × ZMod 11 → Bool) :
    winProb ((SigmaProtocol.attemptDist (Schnorr.sigmaSimAt 11 g) y Vstar).map
        fun p => p.1 && T p.2) =
      winProb (((Schnorr.sigma 11 g).realViewDist y 7 Vstar).map T) / 11 := by
  have := (Schnorr.sigma 11 g).winProb_attemptDist (Schnorr.sigma_specialHVZK g_pow)
    (x := y) (w := 7) rfl Vstar T
  simpa using this

example (T : Unit × G11 × ZMod 11 → Bool) (k : ℕ) :
    |winProb ((SigmaProtocol.simulatorK (Schnorr.sigmaSimAt 11 g) y Vstar k).map
        fun o => o.elim false T) -
      winProb (((Schnorr.sigma 11 g).realViewDist y 7 Vstar).map T)| ≤ (1 - 1 / 11) ^ k := by
  have := (Schnorr.sigma 11 g).abs_winProb_simulatorK_sub_le (Schnorr.sigma_specialHVZK g_pow)
    (x := y) (w := 7) rfl Vstar T k
  simpa using this

end Cslib.Crypto.RewindingSimulatorTests

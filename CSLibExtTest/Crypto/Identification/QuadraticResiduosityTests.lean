/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Crypto.Identification.QuadraticResiduosity
public import CSLibExt.Crypto.PublicKey.GoldwasserMicali
public import Mathlib.Tactic.NormNum.Prime

/-!
# Tests for the zero-knowledge proof of quadratic residuosity

In the units modulo `15`: `4 = 2²` is a quadratic residue with witness `2`; with prover coins
`r = 7` the commitment is `49 ≡ 4` and the answers to the bits `0` and `1` are `7` and `14`, both
accepted. `2` is not a quadratic residue modulo `15` (Euler test modulo `3`), so every cheating
prover for `2` passes `m` rounds with probability at most `2^{-m}`. Zero knowledge against a
verifier whose bit is "`u = 4`" is instantiated.
-/

@[expose] public section

namespace Cslib.Crypto.QuadraticResiduosityTests

open Cslib.Crypto.Framework Cslib.Crypto.Identification Cslib.Crypto.Identification.QR

/-- The unit `2` modulo `15`. -/
def two : (ZMod 15)ˣ := ZMod.unitOfCoprime 2 (by norm_num)

/-- The unit `4` modulo `15`. -/
def four : (ZMod 15)ˣ := ZMod.unitOfCoprime 4 (by norm_num)

/-- The unit `7` modulo `15`. -/
def seven : (ZMod 15)ˣ := ZMod.unitOfCoprime 7 (by norm_num)

theorem rel : (sigma (G := (ZMod 15)ˣ)).Rel four two := show two ^ 2 = four by decide

example : ((sigma.commit four two seven : (ZMod 15)ˣ) : ZMod 15) = 4 := by decide
example : ((sigma.respond four two seven true : (ZMod 15)ˣ) : ZMod 15) = 14 := by decide

example (b : Bool) :
    sigma.verify four (sigma.commit four two seven) b (sigma.respond four two seven b) = true :=
  sigma_complete _ _ rel seven b

instance : Fact (Nat.Prime 3) := ⟨by norm_num⟩
instance : Fact (Nat.Prime 5) := ⟨by norm_num⟩

theorem two_not_isSquare : ¬ IsSquare two := by
  rw [Cslib.Crypto.PublicKey.GoldwasserMicali.isSquare_iff_euler (p := 3) (q := 5) (by norm_num)]
  decide

example {R : Type} [Fintype R] [Nonempty R] (a : R → List Bool → (ZMod 15)ˣ)
    (z : R → List Bool → Bool → (ZMod 15)ˣ) (m : ℕ) :
    winProb (sigma.seqCheatGame two a z m) ≤ 1 / 2 ^ m :=
  winProb_seqCheatGame_le two_not_isSquare a z m

/-- A verifier that asks for the bit `1` exactly when the commitment is `4`. -/
def Vstar : (ZMod 15)ˣ → Unit → Bool := fun u _ => decide (u = four)

example (T : Unit × (ZMod 15)ˣ × (ZMod 15)ˣ → Bool) (k : ℕ) :
    |winProb ((SigmaProtocol.simulatorK simAt four Vstar k).map fun o => o.elim false T) -
        winProb ((sigma.realViewDist four two Vstar).map T)| ≤ 1 / 2 ^ k :=
  abs_winProb_simulatorK_sub_le_half_pow rel Vstar T k

end Cslib.Crypto.QuadraticResiduosityTests

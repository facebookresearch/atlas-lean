/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Crypto.SymmetricKey.PRF
public import Mathlib.Data.ZMod.Basic

/-!
# Tests for the PRF reductions

* A two-query algorithm runs as expected and records its queries.
* The keyed function `F k m = k xor m` on bits is not a PRF. The forger that asks for the tag of
  `false` (which is the key) and forges the tag of `true` wins with probability `1`, so
  `macGame_le` forces the PRF advantage of its reduction to be at least `1/2`.
* Encryption with `F k r + m` decrypts correctly, and the CPA bound is instantiated.
* With the zero function, encryption leaks the message: an adversary without queries (`q = 0`)
  wins the CPA game with probability `1`, so its advantage is `1/2`.
* A two-phase adversary whose second phase uses an answer from its first phase (captured by the
  continuation) runs as expected.
-/

@[expose] public section

namespace Cslib.Crypto.PRFTests

open Cslib.Crypto.PRF OracleComp

/-- Query `0`, then query the answer, and output the second answer. -/
def twice : OracleComp (ZMod 5) (ZMod 5) (ZMod 5) :=
  .query 0 fun y => .query y fun z => .done z

example : twice.run (· + 1) = 2 := by decide

example : twice.queries (· + 1) = [0, 1] := by decide

/-- The keyed function `k xor m`. -/
def xorF (k m : Bool) : Bool := xor k m

/-- Ask for the tag of `false`, which is the key, and forge the tag of `true`. -/
def forger : Unit → OracleComp Bool Bool (Bool × Bool) :=
  fun _ => .query false fun t => .done (true, !t)

theorem macGame_forger : macGame xorF forger = PMF.pure true := by
  rw [macGame, ← PMF.map_const (Cslib.Probability.PMF.uniformOfFintype (Bool × Unit)) true]
  congr 1
  funext ω
  revert ω
  decide

/-- Hence `xorF` has PRF advantage at least `1/2` against the reduction. -/
example : 1 / 2 ≤ prfAdvantage xorF (fun r => macReduction [] (forger r)) := by
  have h := macGame_le xorF forger
  rw [macGame_forger, PMF.pure_apply_self, ENNReal.toReal_one] at h
  norm_num at h
  linarith

example (Fk : ZMod 7 → ZMod 3) (m : ZMod 3) (r : ZMod 7) :
    decrypt Fk (encrypt Fk m r) = m :=
  decrypt_encrypt Fk m r

example (F : Bool → ZMod 7 → ZMod 3) (A : CPAAdversary (ZMod 7) (ZMod 3) Unit) :
    cpaAdvantage 2 F A ≤ prfAdvantage F (cpaReduction 2 A) + 2 / (2 * 7) := by
  simpa using cpaAdvantage_le (q := 2) F A

/-- An adversary without encryption queries that reads the message off a ciphertext encrypted
with the zero function. -/
def leakingA : CPAAdversary Unit (ZMod 2) Unit :=
  fun _ => .done ((0, 1), fun c => .done (c.2 == 1))

/-- The zero keyed function. -/
def zeroF (_ : Unit) (_ : Unit) : ZMod 2 := 0

theorem cpaGame_zeroF_leaks : cpaGame 0 zeroF leakingA = PMF.pure true := by
  rw [cpaGame, ← PMF.map_const (Cslib.Probability.PMF.uniformOfFintype
    (Unit × (Fin 0 → Unit) × Unit × Bool × Unit)) true]
  congr 1
  funext ω
  rcases ω with ⟨u₁, ρ, u₂, b, u₃⟩
  cases u₁
  cases u₂
  cases u₃
  have hρ : ρ = Fin.elim0 := Subsingleton.elim _ _
  subst ρ
  cases b <;> decide

example : cpaAdvantage 0 zeroF leakingA = 1 / 2 := by
  rw [cpaAdvantage, cpaGame_zeroF_leaks, PMF.pure_apply_self, ENNReal.toReal_one]
  norm_num

/-- The second phase uses an answer from the first phase, captured by the continuation. -/
def stateA : CPAAdversary Unit (ZMod 2) Unit :=
  fun _ => .query 0 fun first => .done ((0, 0), fun _ => .done (first.2 == 0))

example : cpaGuess (fun _ : Unit => (0 : ZMod 2)) (fun _ : Fin 1 => ()) () true (stateA ()) =
    true := by
  decide

end Cslib.Crypto.PRFTests

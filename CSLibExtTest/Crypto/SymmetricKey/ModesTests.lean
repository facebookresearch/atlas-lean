/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Crypto.SymmetricKey.CBCMAC
public import Mathlib.Tactic.NormNum

/-!
# Tests for counter mode, CBC mode and CBC-MAC

* Counter mode with a toy keyed function on `ZMod 5`: the keystream wraps around the counter
  space, and encryption round-trips.
* With the all-zero keyed function counter mode sends the message in the clear: an adversary
  without queries wins the CPA game with probability `1`, so `ctr_cpaAdvantage_le` forces the
  PRF advantage of its reduction to be at least `1/2`.
* The CPA bound instantiated with `N = 101`, `ℓ = 3`, `q = 2`: the statistical term is
  `2 * 5 / 202`.
* The hypothesis `ℓ ≤ N` matters: with `ℓ = 3` blocks and `N = 2` counters the keystream repeats,
  and the ciphertext leaks the difference of two message blocks.
* Eager sampling (`OracleComp.runTape`): a two-query run on a concrete tape, the failure value on
  a short tape, the unused tape passed to the continuation, and instances of
  `OracleComp.evalPMF_eq_runTape` and `uniformOfFintype_fin_succ_bind`.
* A toy block cipher `x ↦ x + k` on `ZMod 7`, as a keyed `Equiv.Perm`; it is far from a PRP: a two-query distinguisher has
  PRP advantage `1/2` over `ZMod 3`.
* CBC encryption and decryption round-trip; the CBC bound is instantiated.
* CBC-MAC tags, a rejected wrong tag, and the length-extension forgery against variable-length
  CBC-MAC.
-/

@[expose] public section

namespace Cslib.Crypto.ModesTests

open Cslib.Crypto.Framework Cslib.Crypto.Modes

/-! ### Counter mode -/

/-- A toy keyed function from counters mod `5` to `ZMod 7`. -/
def toyF (k : Bool) (x : ZMod 5) : ZMod 7 := if k then (x.val : ZMod 7) + 1 else 2 * (x.val : ZMod 7)

/-- From counter `4` the keystream is evaluated at counters `4, 0, 1`. -/
example : keystream (ℓ := 3) (toyF true) 4 = ![5, 1, 2] := by decide

example : ctrEncrypt (toyF true) ![1, 2, 3] 4 = (4, ![6, 3, 5]) := by decide

example : ctrDecrypt (toyF true) ((4, ![6, 3, 5]) : ZMod 5 × (Fin 3 → ZMod 7)) = ![1, 2, 3] := by
  decide

example : (ctrScheme 3 toyF).Correct := ctrScheme_correct toyF

/-- The all-zero keyed function. -/
def zeroF (_ : Bool) (_ : ZMod 5) : ZMod 7 := 0

/-- Choose the one-block messages `0` and `1` and guess `1` exactly when the ciphertext block is
`1`. No encryption queries. -/
noncomputable def leakAdv : CPAAdversary (Fin 1 → ZMod 7) (ZMod 5 × (Fin 1 → ZMod 7)) Unit where
  coins := Cslib.Probability.PMF.uniformOfFintype Unit
  run _ := .pure ((0, fun _ => 1), fun c => .pure (decide (c.2 = fun _ => 1)))

theorem leakAdv_queryBounded : leakAdv.QueryBounded 0 := fun _ _ => trivial

/-- With the all-zero function the adversary always wins. -/
theorem cpaAdvantage_leakAdv : cpaAdvantage (ctrScheme 1 zeroF) leakAdv = 1 / 2 := by
  have h : cpaGame (ctrScheme 1 zeroF) leakAdv = PMF.pure true := by
    rw [cpaGame_eq_tape (ctrScheme 1 zeroF) (fun k => ctrEncrypt (zeroF k)) rfl (fun _ _ => rfl)
      leakAdv rfl leakAdv_queryBounded]
    rw [← PMF.map_const (Cslib.Probability.PMF.uniformOfFintype
      (Bool × Bool × Unit × (Fin 0 → ZMod 5) × ZMod 5)) true]
    congr 1
    funext ω
    rcases ω with ⟨k, b, r, ρ, rs⟩
    cases b <;> decide +revert
  rw [cpaAdvantage, guessAdvantage, h, winProb_pure]
  norm_num

/-- Hence the all-zero function has PRF advantage at least `1/2` against the reduction. -/
example : 1 / 2 ≤ PRF.prfAdvantage zeroF (ctrReduction leakAdv 0) := by
  have h := ctr_cpaAdvantage_le (by norm_num) zeroF leakAdv rfl leakAdv_queryBounded
  rw [cpaAdvantage_leakAdv] at h
  simpa using h

/-- The CPA bound for `N = 101` counters, `ℓ = 3` blocks and `q = 2` queries. -/
example (F : Bool → ZMod 101 → ZMod 2) (A : CPAAdversary (Fin 3 → ZMod 2)
    (ZMod 101 × (Fin 3 → ZMod 2)) Bool) (hA : A.coins = Cslib.Probability.PMF.uniformOfFintype Bool)
    (hq : A.QueryBounded 2) :
    cpaAdvantage (ctrScheme 3 F) A ≤ PRF.prfAdvantage F (ctrReduction A 2) + 10 / 202 := by
  have h := ctr_cpaAdvantage_le (by norm_num) F A hA hq
  norm_num at h ⊢
  linarith

/-- With `ℓ = 3 > N = 2` the counter range wraps onto itself: blocks `0` and `2` use the same
pad, so their difference is the difference of the message blocks. -/
example (f : ZMod 2 → ZMod 7) (m : Fin 3 → ZMod 7) (ctr : ZMod 2) :
    (ctrEncrypt f m ctr).2 0 - (ctrEncrypt f m ctr).2 2 = m 0 - m 2 := by
  have h : ((2 : ℕ) : ZMod 2) = ((0 : ℕ) : ZMod 2) := by decide
  simp only [ctrEncrypt, keystream, Pi.add_apply]
  rw [show ((((2 : Fin 3) : ℕ)) : ZMod 2) = ((((0 : Fin 3) : ℕ)) : ZMod 2) from h]
  abel

/-! ### Eager sampling (`Framework.Oracle`) -/

/-- Two queries `1` and `2`, answered by `m + r` with the tape entries `r`, and output the sum. -/
def twoQ : OracleComp (ZMod 7) (ZMod 7) (ZMod 7) :=
  .liftBind 1 fun y₀ => .liftBind 2 fun y₁ => .pure (y₀ + y₁)

/-- On the tape `[3, 5]`: `(1 + 3) + (2 + 5) = 11 = 4` in `ZMod 7`. -/
example : OracleComp.runTape (fun m r => m + r) 0 (fun a _ _ => a) twoQ 2 ![3, 5] = 4 := by
  decide

/-- A tape that is too short gives the failure value. -/
example : OracleComp.runTape (fun m r => m + r) 6 (fun a _ _ => a) twoQ 1 ![3] = 6 := by
  decide

/-- With a tape of length `3` the run stops after two queries; the continuation receives the
output `4` and the unused tape `[4]` of length `1`. -/
example : OracleComp.runTape (fun m r => m + r) (0, 0, 0)
    (fun a n ρ => (a, (n : ZMod 7), if h : 0 < n then ρ ⟨0, h⟩ else 0)) twoQ 3 ![3, 5, 4] =
      (4, 1, 4) := by
  decide

/-- `evalPMF_eq_runTape` for the two-query computation over uniform randomness in `ZMod 7`. -/
example : FreeM.evalPMF (fun m => (Cslib.Probability.PMF.uniformOfFintype (ZMod 7)).map
      (fun r => m + r)) twoQ =
    (Cslib.Probability.PMF.uniformOfFintype (Fin 2 → ZMod 7)).bind fun ρ =>
      PMF.pure (OracleComp.runTape (fun m r => m + r) 0 (fun a _ _ => a) twoQ 2 ρ) :=
  OracleComp.evalPMF_eq_runTape _ 0 fun _ _ => trivial

/-- `uniformOfFintype_fin_succ_bind`: a uniform tape of length `2` splits into its head and a
uniform tape of length `1`. -/
example (g : (Fin 2 → Bool) → PMF Bool) :
    (Cslib.Probability.PMF.uniformOfFintype (Fin 2 → Bool)).bind g =
      (Cslib.Probability.PMF.uniformOfFintype Bool).bind fun a =>
        (Cslib.Probability.PMF.uniformOfFintype (Fin 1 → Bool)).bind fun ρ => g (Fin.cons a ρ) :=
  uniformOfFintype_fin_succ_bind g

/-! ### A toy block cipher and the PRP game -/

/-- The shift cipher `x ↦ x + k` on `ZMod n`. -/
def shiftCipher (n : ℕ) : BlockCipher (ZMod n) (ZMod n) := fun k =>
  ⟨fun x => x + k, fun y => y - k, fun _ => add_sub_cancel_right _ _, fun _ => sub_add_cancel _ _⟩

/-- The block cipher is a keyed `Equiv.Perm`: `F_3⁻¹ (2) = 2 - 3 = 6` and `F_3 (6) = 2`. -/
example : (shiftCipher 7 3).symm 2 = 6 ∧ shiftCipher 7 3 6 = 2 := by decide

/-- Query `0` and `1` and accept when the answers differ by `1`. -/
def diffDist (_ : Unit) : OracleComp (ZMod 3) (ZMod 3) Bool :=
  .liftBind 0 fun y₀ => .liftBind 1 fun y₁ => .pure (decide (y₁ - y₀ = 1))

/-- The shift cipher always passes the test. -/
theorem winProb_prpReal_diffDist : winProb (PRP.prpReal (shiftCipher 3) diffDist) = 1 := by
  rw [PRP.prpReal, winProb_map_uniform]
  have h1 : (Finset.univ.filter fun ω : ZMod 3 × Unit =>
      OracleComp.run ⇑(shiftCipher 3 ω.1) (diffDist ω.2) = true).card = 3 := by decide
  have h2 : Fintype.card (ZMod 3 × Unit) = 3 := by decide
  rw [h1, h2]
  norm_num

/-- A uniformly random permutation of `ZMod 3` passes it for `3` of the `6` permutations. -/
theorem winProb_prpRand_diffDist : winProb (PRP.prpRand diffDist) = 1 / 2 := by
  rw [PRP.prpRand, winProb_map_uniform]
  have h1 : (Finset.univ.filter fun ω : Equiv.Perm (ZMod 3) × Unit =>
      OracleComp.run ω.1 (diffDist ω.2) = true).card = 3 := by decide
  have h2 : Fintype.card (Equiv.Perm (ZMod 3) × Unit) = 6 := by decide
  rw [h1, h2]
  norm_num

example : PRP.prpAdvantage (shiftCipher 3) diffDist = 1 / 2 := by
  rw [PRP.prpAdvantage, advantage, winProb_prpReal_diffDist, winProb_prpRand_diffDist]
  norm_num

/-! ### CBC mode -/

/-- With key `3` and IV `5`: `c₁ = 5 + 1 + 3 = 2`, `c₂ = 2 + 2 + 3 = 0` in `ZMod 7`. -/
example : cbcEncrypt (shiftCipher 7 3) ![1, 2] 5 = (5, ![2, 0]) := by decide

example : cbcDecrypt (shiftCipher 7 3).symm ((5, ![2, 0]) : ZMod 7 × (Fin 2 → ZMod 7)) =
    ![1, 2] := by decide

example : (cbcScheme 2 (shiftCipher 7)).Correct := cbcScheme_correct _

example (A : CPAAdversary (Fin 2 → ZMod 7) (ZMod 7 × (Fin 2 → ZMod 7)) Bool)
    (hA : A.coins = Cslib.Probability.PMF.uniformOfFintype Bool) (hq : A.QueryBounded 1) :
    cpaAdvantage (cbcScheme 2 (shiftCipher 7)) A ≤
      PRP.prpAdvantage (shiftCipher 7) (cbcReduction A 1) +
        guessAdvantage (PRP.prpRand (cbcReduction A 1)) :=
  cbc_cpaAdvantage_le _ A hA hq

/-! ### CBC-MAC -/

/-- With key `3`: `t₁ = 0 + 1 + 3 = 4`, `t₂ = 4 + 2 + 3 = 2`, the last CBC block with IV `0`. -/
example : cbcMac (ℓ := 2) (shiftCipher 7 3) ![1, 2] = 2 := by decide

example : cbcMac (ℓ := 2) (shiftCipher 7 3) ![1, 2] =
    (cbcEncrypt (shiftCipher 7 3) ![1, 2] 0).2 1 := by decide

example : (cbcMacScheme 2 (shiftCipher 7)).verify 3 ![1, 2] 2 = true := by decide

/-- A wrong tag is rejected. -/
example : (cbcMacScheme 2 (shiftCipher 7)).verify 3 ![1, 2] 0 = false := by decide

example : (cbcMacScheme 2 (shiftCipher 7)).Correct := cbcMacScheme_correct _

/-- The length-extension forgery against variable-length CBC-MAC succeeds with probability `1`. -/
example : macAdvantage (cbcMacVarScheme (shiftCipher 7)) (lengthExtForger 1) = 1 :=
  macAdvantage_lengthExtForger _ 1

end Cslib.Crypto.ModesTests

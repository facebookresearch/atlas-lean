/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Crypto.PublicKey.DeterministicEav
public import Mathlib.Data.ZMod.Basic

/-!
# Tests for the deterministic-encryption eavesdropping experiment

* The re-encryption adversary against `m ↦ m ^ 3` on `ZMod 23` (injective since
  `gcd(3, 22) = 1`) with messages `4 ≠ 5` has advantage `1/2`, from distinct ciphertexts
  (`eavAdvantage_reEncrypt`) and from injectivity (`eavAdvantage_reEncrypt_of_injective`).
* The distinct-ciphertexts hypothesis is needed: against the constant scheme `Bool → Unit`, whose
  two messages encrypt alike, the same adversary always guesses `true` and has advantage `0`.
* The equal-length condition is needed: on a message space `Bool` with one message of length `1`
  (`false`) and one of length `2` (`true`), the injective scheme `id` is attacked with advantage
  `1/2` when every pair is eligible (the cross-length pair `(false, true)`), but under
  `EqualLength` that pair is ineligible and every adversary has advantage exactly `0`.

These schemes have fixed-length (or single-element) message spaces except the last one, so they
use the trivial eligibility relation `anyPair`.
-/

@[expose] public section

namespace Cslib.Crypto.DeterministicEavTests

open Cslib.Crypto.PublicKey

/-- The trivial eligibility relation (every pair is eligible), for fixed-length message spaces. -/
def anyPair {M : Unit → Type} : (pk : Unit) → M pk → M pk → Prop := fun _ _ _ => True

/-- The cube map on `ZMod 23`, a deterministic one-key scheme. -/
def cube : Unit → ZMod 23 → ZMod 23 := fun _ m => m ^ 3

/-- The re-encryption adversary on the cube scheme with the messages `4` and `5`. -/
abbrev cubeAttack : EavAdversary Unit (fun _ => ZMod 23) (fun _ => ZMod 23) Unit anyPair :=
  reEncrypt cube (fun _ => (4, 5)) fun _ => trivial

/-- Concrete ciphertexts: `4 ↦ 18` and `5 ↦ 10` in `ZMod 23`. -/
example : cube () 4 = 18 ∧ cube () 5 = 10 := by decide

/-- The generic lemma for a deterministic scheme on `ZMod 23` with messages `4 ≠ 5`. -/
example : eavAdvantage (K := Unit) cube id (PMF.pure ()) cubeAttack = 1 / 2 :=
  eavAdvantage_reEncrypt _ _ _ _ _ fun () => by decide

/-- The re-encryption adversary wins with probability `1` on the cube scheme. -/
example : eavGame (K := Unit) cube id (PMF.pure ()) cubeAttack = PMF.pure true :=
  eavGame_reEncrypt _ _ _ _ _ fun () => by decide

/-- The same advantage from injectivity of the cube map on `ZMod 23`. -/
example : eavAdvantage (K := Unit) cube id (PMF.pure ()) cubeAttack = 1 / 2 :=
  eavAdvantage_reEncrypt_of_injective _ _ _ _ _ (fun _ => by unfold cube; decide)
    fun () => by decide

/-- A constant deterministic scheme with two messages and one ciphertext. -/
def const : Unit → Bool → Unit := fun _ _ => ()

/-- The re-encryption adversary on the constant scheme with the messages `false` and `true`. -/
abbrev constAttack : EavAdversary Unit (fun _ => Bool) (fun _ => Unit) Unit anyPair :=
  reEncrypt const (fun _ => (false, true)) fun _ => trivial

/-- Against the constant scheme the re-encryption adversary wins with probability exactly
`1/2`: the hypothesis of `eavGame_reEncrypt` fails and so does its conclusion. -/
theorem const_eavGame :
    eavGame (K := Unit) (M := fun _ => Bool) (C := fun _ => Unit) const id (PMF.pure ())
      constAttack true = 1 / 2 := by
  rw [eavGame, PMF.pure_bind, PMF.map_apply, tsum_fintype]
  simp [const, Fintype.card_bool, one_div, Fintype.sum_prod_type]

/-- Hence the re-encryption adversary has advantage `0` against the constant scheme. -/
example :
    eavAdvantage (K := Unit) (M := fun _ => Bool) (C := fun _ => Unit) const id (PMF.pure ())
      constAttack = 0 := by
  rw [eavAdvantage, const_eavGame]
  norm_num

/-! ### The equal-length condition -/

/-- A message space with one message of each of two lengths: `false` has length `1`, `true` has
length `2`. -/
def twoLen : Bool → ℕ := fun b => if b then 2 else 1

/-- Length determines the message on the two-length message space. -/
theorem twoLen_injective : Function.Injective twoLen := by decide

/-- The equal-length eligibility relation on the two-length message space. -/
abbrev twoLenEligible : (pk : Unit) → Bool → Bool → Prop := EqualLength fun _ => twoLen

/-- The identity scheme on `Bool`, injective (correct) and deterministic. -/
def idEnc : Unit → Bool → Bool := fun _ b => b

/-- The cross-length pair `(false, true)` is not eligible. -/
example : ¬ twoLenEligible () false true := by unfold twoLenEligible EqualLength; decide

/-- Without the equal-length condition the cross-length pair `(false, true)` is a valid
challenge and the re-encryption adversary has advantage `1/2` against the injective scheme. -/
example : eavAdvantage (K := Unit) (M := fun _ => Bool) (C := fun _ => Bool) idEnc id
    (PMF.pure ())
    (reEncrypt (Eligible := anyPair) idEnc (fun _ => (false, true)) fun _ => trivial) = 1 / 2 :=
  eavAdvantage_reEncrypt_of_injective _ _ _ _ _ (fun _ _ _ h => h) fun () => by decide

/-- With the equal-length condition every eligible pair on the two-length message space is of
the form `(m, m)`, so **every** adversary, with any coins, wins with probability exactly `1/2`. -/
theorem twoLen_eavGame {R : Type} [Fintype R] [Nonempty R]
    (A : EavAdversary Unit (fun _ => Bool) (fun _ => Bool) R twoLenEligible) :
    eavGame (K := Unit) idEnc id (PMF.pure ()) A true = 1 / 2 := by
  have hpick : ∀ r b, pick (A.choose () r) b = (A.choose () r).1 := by
    intro r b
    have h := A.eligible () r
    have heq : (A.choose () r).1 = (A.choose () r).2 := twoLen_injective h
    cases b <;> simp [pick, heq]
  rw [eavGame, PMF.pure_bind, PMF.map_apply, tsum_fintype, Fintype.sum_prod_type]
  simp only [hpick, Cslib.Probability.PMF.uniformOfFintype_apply, idEnc, id]
  have hb : ∀ r, (∑ b : Bool, if true = (A.guess () (A.choose () r).1 r == b) then
      ((Fintype.card (R × Bool) : ENNReal))⁻¹ else 0) =
      ((Fintype.card (R × Bool) : ENNReal))⁻¹ := by
    intro r
    rw [Fintype.sum_bool]
    cases A.guess () (A.choose () r).1 r <;> simp
  rw [Finset.sum_congr rfl fun r _ => hb r, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    Fintype.card_prod, Fintype.card_bool, Nat.cast_mul]
  have h0 : (Fintype.card R : ENNReal) ≠ 0 := by simp
  have ht : (Fintype.card R : ENNReal) ≠ ⊤ := ENNReal.natCast_ne_top _
  rw [ENNReal.mul_inv (Or.inl h0) (Or.inl ht), ← mul_assoc, ENNReal.mul_inv_cancel h0 ht, one_mul,
    one_div]
  norm_num

/-- Hence under the equal-length condition every adversary against the injective two-length
scheme has advantage `0`: the counterexample to the unrestricted game. -/
example {R : Type} [Fintype R] [Nonempty R]
    (A : EavAdversary Unit (fun _ => Bool) (fun _ => Bool) R twoLenEligible) :
    eavAdvantage (K := Unit) idEnc id (PMF.pure ()) A = 0 := by
  rw [eavAdvantage, twoLen_eavGame]
  norm_num

end Cslib.Crypto.DeterministicEavTests

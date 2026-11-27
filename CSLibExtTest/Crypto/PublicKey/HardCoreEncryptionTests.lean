/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Crypto.PublicKey.HardCoreEncryption

/-!
# Tests for encryption from a hard-core predicate

The toy instance on the domain `ZMod 5` with the permutation `x ↦ x + 2` (its own trapdoor
inverse `y ↦ y - 2`) and the predicate "`x` is `0`": the scheme is correct, a ciphertext decrypts
as computed by hand, and the per-adversary identity and the semantic-security corollary are
instantiated (the latter with the trivial error `ε = 1/2`, the only one available against
unbounded predictors: `half_le_of_forall_predict_le`).
-/

@[expose] public section

namespace Cslib.Crypto.HardCoreEncryptionTests

open Cslib.Crypto.Framework Cslib.Crypto.PublicKey.SemanticSecurity
open Cslib.Crypto.PublicKey.HardCoreEncryption

/-- The permutation `x ↦ x + 2` of `ZMod 5`. -/
def shift : Unit → ZMod 5 ≃ ZMod 5 := fun _ => Equiv.addRight 2

/-- Its trapdoor inverse. -/
def unshift : Unit → ZMod 5 → ZMod 5 := fun _ y => y - 2

/-- The predicate "`x` is `0`". -/
def isZero : Unit → ZMod 5 → Bool := fun _ x => decide (x = 0)

/-- The point key distribution. -/
noncomputable def gen : PMF (Unit × Unit) := PMF.pure ((), ())

example : (scheme gen shift unshift isZero).Correct :=
  scheme_correct fun _ _ x => by simp [shift, unshift]

/-- The ciphertext `(p(3), 1 ⊕ b(3)) = (0, 1)` of the bit `1` with randomness `3` decrypts to
`1`. -/
example : (scheme gen shift unshift isZero).dec ((), ()) (0, true) = some true := by
  simp [scheme, unshift, isZero]
  decide

example {R : Type} (coins : PMF R) (A : Unit → ZMod 5 × Bool → R → Bool) :
    indAdvantage (scheme gen shift unshift isZero) coins A false true =
      2 * |winProb (predictGame gen shift isZero (predictorCoins coins) (predictor A)) - 1 / 2| :=
  indAdvantage_eq_two_mul_predictAdvantage gen shift unshift isZero coins A

end Cslib.Crypto.HardCoreEncryptionTests

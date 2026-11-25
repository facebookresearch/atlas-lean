/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Prime.Basic

@[expose] public section

namespace Nat

/-- **Natural numbers with the same prime divisors.** Natural numbers $a$ and $b$ have the same
prime support when every prime $p$ divides $a$ if and only if it divides $b$. -/
def SamePrimeSupport (a b : ℕ) : Prop := ∀ p : ℕ, p.Prime → (p ∣ a ↔ p ∣ b)

theorem samePrimeSupport_refl (a : ℕ) : SamePrimeSupport a a :=
  fun _ _ => Iff.rfl

theorem SamePrimeSupport.symm {a b : ℕ} (h : SamePrimeSupport a b) :
    SamePrimeSupport b a :=
  fun p hp => Iff.symm (h p hp)

theorem SamePrimeSupport.trans {a b c : ℕ} (h1 : SamePrimeSupport a b)
    (h2 : SamePrimeSupport b c) : SamePrimeSupport a c :=
  fun p hp => Iff.trans (h1 p hp) (h2 p hp)

end Nat

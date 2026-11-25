/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.EvenPseudoprimeWieferich
import MathlibExt.NumberTheory.WieferichPrime
import Mathlib.Tactic.NormNum.Prime

namespace MetaMathlibExt.EvenPseudoprimeWieferichTest

open MathlibExt.NumberTheory

-- The congruence makes `p` a Wieferich prime in the sense of `Nat.IsWieferichPrime`.
example {N p : ℕ} (hN : IsEvenPseudoprime N) (hp : p.Prime) (hpN : p ^ 2 ∣ N) :
    p.IsWieferichPrime :=
  (Nat.isWieferichPrime_iff_modEq p).mpr ⟨hp, (evenPseudoprime_wieferich_of_sq_dvd hN hp hpN).1⟩

-- The prime `2`: no even pseudoprime is divisible by `4`.
example {N : ℕ} (hN : IsEvenPseudoprime N) : ¬ 4 ∣ N := fun h => by
  have := (evenPseudoprime_wieferich_of_sq_dvd hN Nat.prime_two (by simpa using h)).2
  omega

-- `1093` is a Wieferich prime, so the bound `3511 ≤ p`, not the congruence, excludes it.
example : 2 ^ (1093 - 1) ≡ 1 [MOD 1093 ^ 2] := by
  decide +kernel

-- Below `3511`, only `n = 1093` has `2 ^ (n - 1) % n ^ 2 = 1`; as `1093 % 8 = 5`, the residue of
-- `p` modulo `8` is what excludes it in the proof of the bound.
set_option maxRecDepth 20000 in
example : ∀ n < 3511, 0 < n → 2 ^ (n - 1) % n ^ 2 = 1 → n = 1093 := by
  decide +kernel

example {N : ℕ} (hN : IsEvenPseudoprime N) : ¬ 1093 ^ 2 ∣ N := fun h => by
  have := (evenPseudoprime_wieferich_of_sq_dvd hN (by norm_num) h).2
  omega

-- The bound is attained by a Wieferich prime: `p = 3511` satisfies both conclusions.
example : 2 ^ (3511 - 1) ≡ 1 [MOD 3511 ^ 2] ∧ 3511 ≤ 3511 :=
  ⟨by decide +kernel, le_rfl⟩

-- Lehmer's even pseudoprime `161038 = 2 * 73 * 1103` satisfies the hypothesis on `N`.
example : IsEvenPseudoprime 161038 :=
  ⟨by decide, by decide, by decide +kernel⟩

end MetaMathlibExt.EvenPseudoprimeWieferichTest

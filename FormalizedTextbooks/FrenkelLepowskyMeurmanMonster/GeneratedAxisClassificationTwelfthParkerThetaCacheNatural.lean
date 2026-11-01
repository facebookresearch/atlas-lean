/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthParkerThetaCacheActual

/-! The complete original Parker theta depends on precisely its twelve original source bits.
Modulo-label lookup therefore preserves the full natural cocode mask for arbitrary inputs. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

private theorem theta_period (n : ℕ) : parkerThetaMask (n % 4096) = parkerThetaMask n := by
  have h : ∀ j : Fin 12, (n % 4096).testBit j.val = n.testBit j.val := by
    intro j
    change (n % 2 ^ 12).testBit j.val = n.testBit j.val
    simp only [Nat.testBit_mod_two_pow, j.isLt, decide_true, Bool.true_and]
  unfold parkerThetaMask
  simp_rw [h]

/-- The original Parker mask evaluated at its exact twelve-bit source label. -/
def generatedTwelfthParkerThetaCacheNatural (n : ℕ) : ℕ :=
  generatedTwelfthParkerThetaCache ⟨n % 4096, Nat.mod_lt _ (by decide)⟩

/-- Every arbitrary natural source argument retains its entire original Parker cocode mask. -/
theorem generatedTwelfth_parker_theta_cache_natural_actual (n : ℕ) :
    generatedTwelfthParkerThetaCacheNatural n = parkerThetaMask n := by
  rw [generatedTwelfthParkerThetaCacheNatural, generatedTwelfth_parker_theta_cache_actual]
  exact theta_period n

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthXiShortCache

/-! Exact finite physical certificates give the actual corrected short action. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix
set_option backward.isDefEq.respectTransparency false

/-- The cached integer transport certificate gives genuine normalized transport up to sign. -/
theorem generatedFifthXiShortCached_transport (r s : generatedFifthXiShortCachedLabel)
    (c : ℤ) (hc : c = 1 ∨ c = -1)
    (h : ∀ i : Fin 24, (co1XiNumerator *ᵥ generatedFifthXiShortCachedIntegral r) i =
      2 * c * generatedFifthXiShortCachedIntegral s i) :
    xiSpinLocalFiber.val.2.val
        (griessShortVector (generatedFifthXiEvenShortIndex (generatedFifthXiShortCachedEven r))) =
      griessShortVector (generatedFifthXiEvenShortIndex (generatedFifthXiShortCachedEven s)) ∨
    xiSpinLocalFiber.val.2.val
        (griessShortVector (generatedFifthXiEvenShortIndex (generatedFifthXiShortCachedEven r))) =
      -griessShortVector (generatedFifthXiEvenShortIndex (generatedFifthXiShortCachedEven s)) := by
  have hv := generatedFifthXiShort_physical_of_certificate
    (generatedFifthXiEvenShortIndex (generatedFifthXiShortCachedEven r))
    (generatedFifthXiEvenShortIndex (generatedFifthXiShortCachedEven s)) c
    (by simpa only [generatedFifthXiShortCachedIntegral_actual] using h)
  rcases hc with rfl | rfl
  · exact Or.inl (by simpa using hv)
  · exact Or.inr (by simpa using hv)

/-- A cached transport and its actual phase give the full genuine short operator coordinate. -/
theorem generatedFifthXiShortCached_operator (r s : generatedFifthXiShortCachedLabel)
    (c : ℤ) (hc : c = 1 ∨ c = -1)
    (h : ∀ i : Fin 24, (co1XiNumerator *ᵥ generatedFifthXiShortCachedIntegral r) i =
      2 * c * generatedFifthXiShortCachedIntegral s i)
    (p : ZMod 2)
    (hp : generatedFifthXiEvenShortPhase (generatedFifthXiShortCachedEven r)
      (generatedFifthXiShortCachedEven s) = p) (X : GriessShortIndex → ℝ) :
    localShortOperator generatedFifthXiCorrectedFiber X
        (generatedFifthXiEvenShortIndex (generatedFifthXiShortCachedEven s)) =
      qSign p * X (generatedFifthXiEvenShortIndex (generatedFifthXiShortCachedEven r)) := by
  simpa only [hp] using generatedFifthXiEvenShort_operator _ _
    (generatedFifthXiShortCached_transport r s c hc h) X

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

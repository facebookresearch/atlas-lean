/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Geometry.LimitingHodgeStructures

@[expose] public section

/-!
# Tests for limiting Hodge data

The exponential cover is invariant under the deck translation, which acts on
the inverse image of every open; restricting an equivariant section restricts
the underlying function. With nilpotency bound `b = 1` the logarithm vanishes,
the exponential is the identity and the monodromy filtration is the pure one,
jumping from `⊥` to `⊤` at the weight. For a square-zero logarithm (`b = 2`)
the monodromy filtration has the expected steps
`0 ⊆ im N ⊆ ker N ⊆ V` in degrees `w - 2, w - 1, w, w + 1`.
-/

noncomputable section

open CategoryTheory Opposite TopologicalSpace
open MathlibExt.Geometry.RationalHodgeStructures
open MathlibExt.Geometry.LimitingHodgeStructures

namespace MathlibExtTest.Geometry.LimitingHodgeStructures

example (z : upperHalfPlane) : exponentialCover (deck z) = exponentialCover z :=
  exponentialCover_deck z

example (U : Opens puncturedDisk) (z : coveredOpen U) : (deckOnOpen U z).1 = deck z.1 :=
  rfl

/-- Restriction of equivariant sections restricts the underlying functions. -/
example (V : ModuleCat.{0} ℚ) (T : V ≃ₗ[ℚ] V) {U W : Opens puncturedDisk} (h : W ≤ U)
    (s : equivariantSections V T U) (z : coveredOpen W) :
    (((equivariantPresheaf V T).map (homOfLE h).op) s).1 z = s.1 ⟨z.1, h z.2⟩ :=
  rfl

section Filtration

variable {V : ModuleCat.{0} ℚ} (w : ℤ)

/-- With `N = 0` and bound `b = 1`, the filtration is zero below the weight. -/
example : monodromyWeight (0 : Module.End ℚ V) 1 w (w - 1) = ⊥ := by
  simp [monodromyWeight, Module.End.one_eq_id]

/-- With `N = 0` and bound `b = 1`, the filtration is everything at the weight. -/
example : monodromyWeight (0 : Module.End ℚ V) 1 w w = ⊤ := by
  simp [monodromyWeight, Module.End.one_eq_id]

private theorem iSup_two {α : Type*} [CompleteLattice α] (f : Fin 2 → α) :
    ⨆ i, f i = f 0 ⊔ f 1 :=
  le_antisymm (iSup_le (Fin.forall_fin_two.2 ⟨le_sup_left, le_sup_right⟩))
    (sup_le (le_iSup f 0) (le_iSup f 1))

variable {N : Module.End ℚ V} (hN : N ^ 2 = 0)
include hN

private theorem range_le_ker : LinearMap.range N ≤ LinearMap.ker N := by
  rintro _ ⟨v, rfl⟩
  rw [LinearMap.mem_ker, ← Module.End.mul_apply, ← pow_two, hN, LinearMap.zero_apply]

private theorem ker_sq : LinearMap.ker (N ^ 2) = ⊤ := by
  rw [hN, LinearMap.ker_zero]

example : monodromyWeight N 2 w (w - 2) = ⊥ := by
  rw [monodromyWeight, iSup_two]
  simp [Module.End.one_eq_id]

example : monodromyWeight N 2 w (w - 1) = LinearMap.range N := by
  simp only [monodromyWeight]
  rw [show (⨆ j : Fin 2, LinearMap.ker (N ^ (w - 1 - w + (j : ℤ) + 1).toNat) ⊓
      LinearMap.range (N ^ (j : ℕ))) =
      (LinearMap.ker (N ^ 0) ⊓ LinearMap.range (N ^ 0)) ⊔
        (LinearMap.ker (N ^ 1) ⊓ LinearMap.range (N ^ 1)) from by
    rw [iSup_two]
    congr 3 <;> simp]
  simpa [Module.End.one_eq_id] using range_le_ker hN

example : monodromyWeight N 2 w w = LinearMap.ker N := by
  simp only [monodromyWeight]
  rw [show (⨆ j : Fin 2, LinearMap.ker (N ^ (w - w + (j : ℤ) + 1).toNat) ⊓
      LinearMap.range (N ^ (j : ℕ))) =
      (LinearMap.ker (N ^ 1) ⊓ LinearMap.range (N ^ 0)) ⊔
        (LinearMap.ker (N ^ 2) ⊓ LinearMap.range (N ^ 1)) from by
    rw [iSup_two]
    congr 3 <;> simp]
  simpa [Module.End.one_eq_id, ker_sq hN] using range_le_ker hN

example : monodromyWeight N 2 w (w + 1) = ⊤ := by
  simp only [monodromyWeight]
  rw [show (⨆ j : Fin 2, LinearMap.ker (N ^ (w + 1 - w + (j : ℤ) + 1).toNat) ⊓
      LinearMap.range (N ^ (j : ℕ))) =
      (LinearMap.ker (N ^ 2) ⊓ LinearMap.range (N ^ 0)) ⊔
        (LinearMap.ker (N ^ 3) ⊓ LinearMap.range (N ^ 1)) from by
    rw [iSup_two]
    congr 3 <;> simp]
  simp [Module.End.one_eq_id, ker_sq hN]

end Filtration

section Logarithm

variable {V : ModuleCat.{0} ℚ} (C : RationalComplexification V) {r : ℕ}
  (e : C.complexSpace ≃ₗ[ℂ] EuclideanSpace ℂ (Fin r)) {w : ℤ}
  (H : PolarizedPeriodVariation C e w)

/-- With nilpotency bound `b = 1` the deck operator is the identity and both
logarithms vanish. -/
example : rationalLog C e H 1 = 0 := by simp [rationalLog]

example : complexLog C e H 1 = 0 := by simp [complexLog]

/-- With bound `b = 1` the truncated exponential is the identity. -/
example (N : Module.End ℂ C.complexSpace) (z : ℂ) : nilpotentExp C N 1 z = 1 := by
  simp [nilpotentExp]

/-- With bound `b = 2` the logarithm is `T - 1`. -/
example : rationalLog C e H 2 = H.rationalDeck.toLinearMap - 1 := by
  simp [rationalLog, Finset.sum_range_succ]

end Logarithm

end MathlibExtTest.Geometry.LimitingHodgeStructures

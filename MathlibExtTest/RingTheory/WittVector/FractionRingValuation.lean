/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.RingTheory.WittVector.FractionRingValuation

/-!
# Tests for the `p`-adic valuation on the fraction field of Witt vectors
-/

open WittVector
open scoped Isocrystal

namespace MathlibExtTest.RingTheory.WittVector.FractionRingValuation

variable (p : ℕ) [Fact p.Prime]

section PerfectField

variable (k : Type*) [Field k] [CharP k p] [PerfectRing k p]

example : FractionRing.addValuation p k (p : K(p, k)) = 1 := by
  simp

example (x : K(p, k)) :
    FractionRing.addValuation p k (φ(p, k) x) = FractionRing.addValuation p k x := by
  simp

example (x : K(p, k)) :
    FractionRing.addValuation p k (φ(p, k) (φ(p, k) x)) = FractionRing.addValuation p k x := by
  simp

example (x : K(p, k)) :
    FractionRing.addValuation p k ((FractionRing.frobenius p k).symm x) =
      FractionRing.addValuation p k x := by
  simp

example : (FractionRing.addValuation p k).comap φ(p, k) = FractionRing.addValuation p k :=
  FractionRing.addValuation_comap_frobenius p k

example (m : ℤ) (u : (WittVector p k)ˣ) :
    FractionRing.addValuation p k
      ((p : K(p, k)) ^ m * algebraMap (WittVector p k) K(p, k) u) = m :=
  FractionRing.addValuation_p_zpow_mul_unit p k m u

example (u : (WittVector p k)ˣ) :
    FractionRing.addValuation p k (algebraMap (WittVector p k) K(p, k) u) = 0 := by
  simp

example (x : WittVector p k) :
    0 ≤ FractionRing.addValuation p k (algebraMap (WittVector p k) K(p, k) x) :=
  FractionRing.addValuation_algebraMap_nonneg p k x

example (x : K(p, k)) (hx : x ≠ 0) : FractionRing.addValuation p k x ≠ ⊤ :=
  (FractionRing.addValuation_eq_top_iff p k).not.2 hx

example : FractionRing.addValuation p k 0 = ⊤ :=
  (FractionRing.addValuation_eq_top_iff p k).2 rfl

-- The value at `p ^ 2 ∈ 𝕎 k`, computed through `IsDiscreteValuationRing.addVal`.
example :
    FractionRing.addValuation p k
      (algebraMap (WittVector p k) K(p, k) ((p : WittVector p k) ^ 2)) = 2 := by
  rw [FractionRing.addValuation_algebraMap, IsDiscreteValuationRing.addVal_pow,
    IsDiscreteValuationRing.addVal_uniformizer (WittVector.irreducible p)]
  rfl

end PerfectField

section ZMod

-- The value at `p ^ 3`.
example : FractionRing.addValuation p (ZMod p) ((p : K(p, ZMod p)) ^ 3) = 3 := by
  rw [FractionRing.addValuation_p_pow]
  rfl

-- The value at `p⁻¹`.
example : FractionRing.addValuation p (ZMod p) (p : K(p, ZMod p))⁻¹ = -1 := by
  rw [AddValuation.map_inv, FractionRing.addValuation_p]

-- The value at `p ^ (-2)`, after applying the Frobenius.
example :
    FractionRing.addValuation p (ZMod p) (φ(p, ZMod p) ((p : K(p, ZMod p)) ^ (-2 : ℤ))) = -2 := by
  rw [FractionRing.addValuation_frobenius, FractionRing.addValuation_p_zpow]
  rfl

-- Frobenius invariance at `p ^ (-3) * (-1)`, where `-1` is a unit of `WittVector p (ZMod p)`.
example :
    FractionRing.addValuation p (ZMod p)
        (φ(p, ZMod p) ((p : K(p, ZMod p)) ^ (-3 : ℤ) *
          algebraMap (WittVector p (ZMod p)) K(p, ZMod p) ↑(-1 : (WittVector p (ZMod p))ˣ))) =
      -3 := by
  rw [FractionRing.addValuation_frobenius, FractionRing.addValuation_p_zpow_mul_unit]
  rfl

end ZMod

end MathlibExtTest.RingTheory.WittVector.FractionRingValuation

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Exact binary dot-functional kernel counts for the actual hyperbolic coordinates. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Definitions
public import Mathlib.LinearAlgebra.Isomorphisms
public import Mathlib.LinearAlgebra.Quotient.Card

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Dot product with a specified binary vector, as a genuine linear functional. -/
def monsterGeometryBinaryDot {n : ℕ} (a : Fin n → ZMod 2) :
    (Fin n → ZMod 2) →ₗ[ZMod 2] ZMod 2 where
  toFun b := ∑ i, a i * b i
  map_add' b c := by simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' c b := by
    change (∑ i, a i * (c * b i)) = c * ∑ i, a i * b i
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring

/-- A nonzero binary dot functional reaches both actual field elements. -/
theorem monsterGeometryBinaryDot_surjective {n : ℕ} (a : Fin n → ZMod 2) (ha : a ≠ 0) :
    Function.Surjective (monsterGeometryBinaryDot a) := by
  have hi : ∃ i, a i ≠ 0 := by
    by_contra h
    apply ha
    funext i
    exact not_not.mp (not_exists.mp h i)
  obtain ⟨i, hi⟩ := hi
  have hbits : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide +kernel
  have hai : a i = 1 := (hbits (a i)).resolve_left hi
  intro c
  refine ⟨Pi.single i c, ?_⟩
  change (∑ j, a j * (Pi.single i c : Fin n → ZMod 2) j) = c
  rw [Finset.sum_eq_single i]
  · simp only [Pi.single_eq_same, hai, one_mul]
  · intro j _ hj
    simp only [Pi.single_apply, ite_eq_right hj, mul_zero]
  · exact fun h => (h (Finset.mem_univ i)).elim

/-- The quotient/kernel cardinal identity counts every zero of a nonzero binary dot functional. -/
theorem monsterGeometryBinaryDot_ker_card_mul {n : ℕ} (a : Fin n → ZMod 2) (ha : a ≠ 0) :
    Nat.card (monsterGeometryBinaryDot a).ker * 2 = 2 ^ n := by
  have hq := Nat.card_congr
    ((monsterGeometryBinaryDot a).quotKerEquivOfSurjective
      (monsterGeometryBinaryDot_surjective a ha)).toEquiv
  have hc := (monsterGeometryBinaryDot a).ker.card_eq_card_quotient_mul_card
  rw [hq] at hc
  simpa only [Nat.card_fun, Nat.card_eq_fintype_card, Fintype.card_fun,
    Fintype.card_fin, ZMod.card] using hc.symm

/-- A nonzero functional on the literal twelve-bit half-space has exactly 2048 zeroes. -/
theorem monsterGeometryBinaryDot_twelve_ker_card (a : Fin 12 → ZMod 2) (ha : a ≠ 0) :
    Nat.card (monsterGeometryBinaryDot a).ker = 2048 := by
  have hc := monsterGeometryBinaryDot_ker_card_mul a ha
  norm_num only at hc
  omega

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

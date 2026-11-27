/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Additive.BoseSet
import Mathlib.FieldTheory.Finite.GaloisField

/-! # Tests for affine equivalence of Bose sets -/

namespace MathlibExtTest.BoseSet

open MetaMathlibExt
open scoped IntermediateField

private abbrev F := ZMod 3
private abbrev K := GaloisField 3 2

private theorem degree_of_order_eight {x : K} (hx : orderOf x = 8) :
    (minpoly F x).natDegree = 2 := by
  have hdvd := Module.finrank_dvd_finrank_right F F⟮x⟯ K
  rw [IntermediateField.adjoin.finrank (Algebra.IsIntegral.isIntegral x),
    GaloisField.finrank 3 (by decide)] at hdvd
  refine (Nat.prime_two.eq_one_or_self_of_dvd _ hdvd).resolve_left ?_
  intro h
  obtain ⟨a, rfl⟩ := minpoly.natDegree_eq_one_iff.mp h
  have ha : a ≠ 0 := by rintro rfl; simp at hx
  have hpow := congrArg (algebraMap F K) (ZMod.pow_card_sub_one_eq_one ha)
  rw [map_pow, map_one, ← orderOf_dvd_iff_pow_eq_one, hx] at hpow
  exact (by decide : ¬8 ∣ 3 - 1) hpow

-- Modulo eight, the norm exponent is four and Frobenius multiplies exponents by three.
example : ∃ θ : K, orderOf θ = 8 ∧
    ZModAffinelyEquivalent (boseSet F 2 θ 1) (boseSet F 2 θ 5) ∧
    ZModAffinelyEquivalent (boseSet F 2 θ 3) (boseSet F 2 θ 1) := by
  classical
  let _ : Fintype K := Fintype.ofFinite _
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := Kˣ)
  have hc : Nat.card K = 9 := GaloisField.card 3 2 (by decide)
  rw [Nat.card_units, hc] at hg
  have hθ : orderOf (g : K) = Fintype.card K - 1 := by
    rw [orderOf_units, hg, Fintype.card_eq_nat_card, hc]
  have hdeg (k : ℕ) (hk : Nat.Coprime 8 k) : (minpoly F ((g : K) ^ k)).natDegree = 2 := by
    apply degree_of_order_eight
    rw [← Units.val_pow_eq_pow_val, orderOf_units, orderOf_pow, hg, hk.gcd_eq_one, Nat.div_one]
  refine ⟨g, by rwa [orderOf_units], ?_, ?_⟩
  · apply zModAffinelyEquivalent_boseSet (by decide) (GaloisField.finrank 3 (by decide)) hθ
      (hdeg 1 (by decide)) (hdeg 5 (by decide))
    exact Or.inl (by decide)
  · apply zModAffinelyEquivalent_boseSet (by decide) (GaloisField.finrank 3 (by decide)) hθ
      (hdeg 3 (by decide)) (hdeg 1 (by decide))
    exact Or.inr (Or.inr ⟨1, by rw [ZMod.ringChar_zmod_n]; decide⟩)

-- At height zero a negative residue uses its absolute value as exponent.
example (θ : K) : -3 ∈ boseSet F 0 θ 3 := by
  refine (mem_boseSet ..).mpr ⟨0, ?_⟩
  rw [map_zero, add_zero]
  rfl

end MathlibExtTest.BoseSet

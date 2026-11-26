/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Additive.SingerSet
import Mathlib.FieldTheory.Finite.GaloisField

/-! # Tests for affine equivalence of Singer sets -/

namespace MathlibExtTest.SingerSet

open MetaMathlibExt
open scoped IntermediateField

private abbrev F := ZMod 2
private abbrev K := GaloisField 2 3

private theorem degree_of_order_seven {x : K} (hx : orderOf x = 7) :
    (minpoly F x).natDegree = 3 := by
  have hdvd := Module.finrank_dvd_finrank_right F F⟮x⟯ K
  rw [IntermediateField.adjoin.finrank (Algebra.IsIntegral.isIntegral x),
    GaloisField.finrank 2 (by decide)] at hdvd
  refine (Nat.prime_three.eq_one_or_self_of_dvd _ hdvd).resolve_left ?_
  intro h
  obtain ⟨a, rfl⟩ := minpoly.natDegree_eq_one_iff.mp h
  rcases (show ∀ a : F, a = 0 ∨ a = 1 by decide) a with rfl | rfl <;> simp at hx

-- Reciprocal generators in the cubic extension satisfy the mixed relation with r = w = 0.
example : ∃ θ : K, orderOf θ = 7 ∧
    ZModAffinelyEquivalent (singerSet F 2 θ 1) (singerSet F 2 θ 6) := by
  classical
  let _ : Fintype K := Fintype.ofFinite _
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := Kˣ)
  have hc : Nat.card K = 8 := GaloisField.card 2 3 (by decide)
  have hθ : orderOf (g : K) = 7 := by rw [orderOf_units, hg, Nat.card_units, hc]
  have h₆ : orderOf ((g : K) ^ 6) = 7 := by
    rw [← Units.val_pow_eq_pow_val, orderOf_units, orderOf_pow, ← orderOf_units, hθ]
    decide
  refine ⟨g, hθ, zModAffinelyEquivalent_singerSet (by decide) (GaloisField.finrank 2 (by decide))
    (by rwa [Fintype.card_eq_nat_card, hc]) (by simpa using degree_of_order_seven hθ)
    (degree_of_order_seven h₆) (.inr (.inr (.inr ?_)))⟩
  refine ⟨0, 1, 0, Or.inr one_ne_zero, 1, ?_⟩
  simpa only [map_one, map_zero, zero_mul, one_mul, zero_add, add_zero, hθ] using
    (pow_orderOf_eq_one (g : K)).symm

-- With b = 0 the plane collapses to the base field. Only residue zero represents its unit.
example (θ : K) (hθ : orderOf θ = 7) : singerSet F 2 θ 0 = {0} := by
  have hθ₀ : θ ≠ 0 := by rintro rfl; simp at hθ
  have hM : (Fintype.card F ^ (2 + 1) - 1) / (Fintype.card F - 1) = 7 := by
    rw [ZMod.card]; decide
  ext a
  rw [mem_singerSet, Set.mem_singleton_iff]
  constructor
  · rintro ⟨u, v, huv⟩
    have ha : θ ^ a.val = 1 := by
      simp only [pow_zero, mul_one, ← map_add] at huv
      generalize u + v = c at huv
      rcases (show ∀ a : F, a = 0 ∨ a = 1 by decide) c with rfl | rfl
      · exact (pow_ne_zero _ hθ₀ (huv.trans (map_zero _))).elim
      · exact huv.trans (map_one _)
    have hdvd := orderOf_dvd_iff_pow_eq_one.mpr ha
    rw [hθ, ← hM] at hdvd
    have : NeZero ((Fintype.card F ^ (2 + 1) - 1) / (Fintype.card F - 1)) := ⟨by omega⟩
    exact (ZMod.val_eq_zero _).mp (Nat.eq_zero_of_dvd_of_lt hdvd a.val_lt)
  · rintro rfl
    exact ⟨0, 1, by simp⟩

end MathlibExtTest.SingerSet

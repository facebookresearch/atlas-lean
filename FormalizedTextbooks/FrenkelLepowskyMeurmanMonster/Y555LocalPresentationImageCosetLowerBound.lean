/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Constructive finite image lower bounds from distinct actual subgroup coset witnesses. -/
module

public import Mathlib.GroupTheory.Index
public import Mathlib.GroupTheory.GroupAction.Basic

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- Distinct actual right cosets give a finite ambient group order lower bound. -/
theorem y322FiniteGroup_card_ge_of_cosets {G : Type*} [Group G] [Finite G] {size : ℕ}
    (K : Subgroup G) (representative : Fin size → G)
    (separated : ∀ i j : Fin size, representative i * (representative j)⁻¹ ∈ K → i = j) :
    Nat.card K * size ≤ Nat.card G := by
  have hi : Function.Injective
      (fun i : Fin size => (QuotientGroup.mk (representative i)⁻¹ : G ⧸ K)) := by
    intro i j hij
    apply separated i j
    simpa only [inv_inv] using QuotientGroup.eq.mp hij
  have hindex : size ≤ K.index := by
    simpa only [Subgroup.index_eq_card, Nat.card_fin] using Nat.card_le_card_of_injective _ hi
  calc
    Nat.card K * size ≤ Nat.card K * K.index := Nat.mul_le_mul_left _ hindex
    _ = Nat.card G := K.card_mul_index

/-- Distinct transported fixed points certify distinct actual right cosets and an order bound. -/
theorem y322FiniteGroup_card_ge_of_orbit {G X : Type*} [Group G] [Finite G]
    [MulAction G X] {size : ℕ} (K : Subgroup G) (point : X)
    (fixed : ∀ k ∈ K, k • point = point) (representative : Fin size → G)
    (distinct : Function.Injective (fun i => (representative i)⁻¹ • point)) :
    Nat.card K * size ≤ Nat.card G := by
  apply y322FiniteGroup_card_ge_of_cosets K representative
  intro i j hij
  apply distinct
  have h := congrArg (fun x => (representative i)⁻¹ • x)
    (fixed (representative i * (representative j)⁻¹) hij)
  simpa only [mul_smul, inv_smul_smul] using h.symm

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

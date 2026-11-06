/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Interior commutation for the closing reflection of a type A chain. -/
module
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555TypeAParabolicOrderInsertion
@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- The closing reflection of a chain is the last generator transported along its prefix. -/
def typeAClosingReflection {G : Type*} [Group G] (s : ℕ → G) (n : ℕ) : G :=
  (typeAInsertion s 0 n)⁻¹ * s n * typeAInsertion s 0 n

/-- The closing reflection is an involution solely from the simple-generator square relation. -/
theorem typeAClosingReflection_square {G : Type*} [Group G] {s : ℕ → G} {n : ℕ}
    (h : TypeAChainRelations s (n + 1)) :
    typeAClosingReflection s n * typeAClosingReflection s n = 1 := by
  unfold typeAClosingReflection
  calc
    _ = (typeAInsertion s 0 n)⁻¹ * (s n * s n) * typeAInsertion s 0 n := by group
    _ = 1 := by rw [h.square n (by omega)]; group

/-- The closing reflection commutes with every interior simple generator of the chain. -/
theorem typeAClosingReflection_commute_interior {G : Type*} [Group G]
    {s : ℕ → G} {n : ℕ} (h : TypeAChainRelations s (n + 1))
    (j : ℕ) (hj : 0 < j) (hjn : j < n) :
    Commute (typeAClosingReflection s n) (s j) := by
  have ht := typeAInsertion_interior h 0 n j (by omega) hj (by omega)
  have hc : s n * s (j - 1) = s (j - 1) * s n :=
    (h.commute (j - 1) n (by omega) (by omega) (by omega)).symm
  have he : typeAInsertion s 0 n * s j * (typeAInsertion s 0 n)⁻¹ = s (j - 1) := by
    rw [ht]
    group
  change typeAClosingReflection s n * s j = s j * typeAClosingReflection s n
  unfold typeAClosingReflection
  calc
    _ = (typeAInsertion s 0 n)⁻¹ * s n * (typeAInsertion s 0 n * s j) := by group
    _ = (typeAInsertion s 0 n)⁻¹ * s n * (s (j - 1) * typeAInsertion s 0 n) := by rw [ht]
    _ = (typeAInsertion s 0 n)⁻¹ * s (j - 1) * s n * typeAInsertion s 0 n := by
      simpa only [mul_assoc] using
        congrArg (fun a => (typeAInsertion s 0 n)⁻¹ * a * typeAInsertion s 0 n) hc
    _ = (typeAInsertion s 0 n)⁻¹ *
        (typeAInsertion s 0 n * s j * (typeAInsertion s 0 n)⁻¹) *
        s n * typeAInsertion s 0 n := by rw [he]
    _ = _ := by group

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

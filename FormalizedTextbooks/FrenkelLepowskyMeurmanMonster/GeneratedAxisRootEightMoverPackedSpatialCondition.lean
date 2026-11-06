/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightMoverPackedHighPairGeneric
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightMoverSpatialAction

/-! Exact original mover tensor boundaries and positive spatial coefficients. -/
@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000

/-- The complete signed word equation uses the actual positive spatial matrix in output/input order. -/
def generatedRootEightMoverPackedSpatialCondition (i : Fin 24) (a : Fin 256) : Prop :=
  let w := fun j => generatedRootEightMoverTensorFinalWords j
    ⟨a.val / 16, by omega⟩ ⟨a.val % 16, Nat.mod_lt _ (by decide)⟩
  let t := generatedRootEightMoverTensorSourceWords i
    ⟨a.val / 16, by omega⟩ ⟨a.val % 16, Nat.mod_lt _ (by decide)⟩
  (∀ j : Fin 24, w j < 65536 ^ 16 ∧ w j &&& generatedRootEightPackedWideUpperMask = 0) ∧
    t < 65536 ^ 16 ∧ t &&& generatedRootEightPackedWideUpperMask = 0 ∧
      (∑ j : Fin 24, generatedRootEightMoverSpatialNumerator i j *
        generatedRootEightPackedWideBiasedWord (w j)) =
          64 * generatedRootEightPackedWideBiasedWord t

set_option maxHeartbeats 64000000 in
/-- Every genuine spatial row has the complete required coefficient budget. -/
theorem generatedRootEight_mover_packed_spatial_budget : ∀ i : Fin 24,
    (∑ j : Fin 24, |generatedRootEightMoverSpatialNumerator i j|) + |(64 : ℤ)| < 256 := by
  decide +kernel

/-- Whole-word spatial equations imply all original actual tensor coordinates. -/
theorem generatedRootEight_mover_packed_spatial_of_condition
    (h : ∀ i a, generatedRootEightMoverPackedSpatialCondition i a) (n : Fin 4096) (i : Fin 24) :
    (∑ j : Fin 24, generatedRootEightMoverSpatialNumerator i j *
      generatedRootEightMoverTensorFinalInteger n j) =
        64 * generatedRootEightMoverTensorSourceInteger n i := by
  let a : Fin 256 := ⟨n.val / 16, by omega⟩
  let z : Fin 16 := ⟨n.val % 16, Nat.mod_lt _ (by decide)⟩
  have hn : generatedRootEightMoverPackedPrefixIndex a z = n := by
    apply Fin.ext
    dsimp [generatedRootEightMoverPackedPrefixIndex, a, z]
    omega
  have ha := h i a
  unfold generatedRootEightMoverPackedSpatialCondition at ha
  have he := generatedRootEight_packed_wide_biased_bounded _ _
    (generatedRootEightMoverSpatialNumerator i) 64
    (generatedRootEight_mover_packed_spatial_budget i)
    (fun j => (ha.1 j).1) ha.2.1 (fun j => (ha.1 j).2) ha.2.2.1 ha.2.2.2 z
  rw [← hn]
  change (∑ j : Fin 24, generatedRootEightMoverSpatialNumerator i j *
    generatedRootEightMoverPackedCoordinate (generatedRootEightMoverTensorFinalWords j)
      (generatedRootEightMoverPackedPrefixIndex a z)) =
        64 * generatedRootEightMoverPackedCoordinate (generatedRootEightMoverTensorSourceWords i)
          (generatedRootEightMoverPackedPrefixIndex a z)
  simp_rw [generatedRootEight_mover_packed_prefix_coordinate]
  exact he

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

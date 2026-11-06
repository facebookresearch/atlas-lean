/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryPackedBoundaryData

/-! Ungated complete two-fixer boundary certificates. No declaration has passed Lean. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

/-- All sixty-four complete original spin prefixes in one of four exhaustive packets. -/
def generatedTenthPackedBoundaryPacketPrefix (b : Fin 4) (u : Fin 64) : Fin 256 :=
  ⟨64 * b.val + u.val, by omega⟩

/-- The entire original input word is bounded, with every signed coefficient retained. -/
def GeneratedTenthPackedBoundaryInputPacketCondition (j : Fin 24) (b : Fin 4) : Prop :=
  ∀ u : Fin 64, generatedTenthPackedBoundaryAbsMax (generatedTenthPackedBoundaryInputWord j
    (generatedTenthPackedBoundaryPacketPrefix b u)) ≤ 176

/-- Both original stage-zero and final-pair words keep their complete signed magnitude bounds. -/
def GeneratedTenthPackedBoundaryStagePacketCondition (g : Fin 2) (j : Fin 24) (b : Fin 4) : Prop :=
  ∀ u : Fin 64,
    generatedTenthPackedBoundaryAbsMax (generatedTenthPackedBoundaryStageWord g 0 j
      (generatedTenthPackedBoundaryPacketPrefix b u)) ≤ 144 ∧
    generatedTenthPackedBoundaryAbsMax (generatedTenthPackedBoundaryStageWord g
      (generatedTenthTwoFixerTensorPairs g).length j
        (generatedTenthPackedBoundaryPacketPrefix b u)) ≤ 176

/-- Complete genuine inverse-right labels and quadratic signs retain every physical row weight. -/
def GeneratedTenthPackedBoundaryStartPacketCondition (g : Fin 2) (j : Fin 24) (b : Fin 4) : Prop :=
  ∀ u : Fin 64,
    (∑ k : Fin 24, generatedTenthTwoFixerTensorNumerator g j k *
      generatedRootEightPackedSignedWord (generatedTenthPackedBoundaryPreWord g k
        (generatedTenthPackedBoundaryPacketPrefix b u))) =
      (generatedTenthTwoFixerTensorDenominator g : ℤ) *
        generatedRootEightPackedSignedWord (generatedTenthPackedBoundaryStageWord g 0 j
          (generatedTenthPackedBoundaryPacketPrefix b u))

/-- Complete inverse-left, quadratic and central Pauli signs keep both original final equations. -/
def GeneratedTenthPackedBoundaryFinishPacketCondition (g : Fin 2) (j : Fin 24) (b : Fin 4) : Prop :=
  ∀ u : Fin 64,
    generatedRootEightPackedSignedWord (generatedTenthPackedBoundaryPostWord g j
      (generatedTenthPackedBoundaryPacketPrefix b u)) =
      generatedRootEightPackedSignedWord (generatedTenthPackedBoundaryInputWord j
        (generatedTenthPackedBoundaryPacketPrefix b u)) ∧
    generatedTenthPackedBoundaryStageWord g ((generatedTenthTwoFixerTensorPairs g).length + 1)
      j (generatedTenthPackedBoundaryPacketPrefix b u) =
        generatedTenthPackedBoundaryInputWord j (generatedTenthPackedBoundaryPacketPrefix b u)

private theorem prefix_recover (a : Fin 256) :
    generatedTenthPackedBoundaryPacketPrefix ⟨a.val / 64, by omega⟩
      ⟨a.val % 64, Nat.mod_lt _ (by decide)⟩ = a := by
  apply Fin.ext
  dsimp [generatedTenthPackedBoundaryPacketPrefix]
  omega

/-- The complete input and both stage word predicates follow from the exact four-packet cover. -/
theorem generatedTenth_packed_boundary_bounds_of_packets
    (hi : ∀ j b, GeneratedTenthPackedBoundaryInputPacketCondition j b)
    (hs : ∀ g j b, GeneratedTenthPackedBoundaryStagePacketCondition g j b) :
    GeneratedTenthPackedBoundaryBounds := by
  refine ⟨?_, ?_, ?_⟩
  · intro j a
    have h := hi j ⟨a.val / 64, by omega⟩ ⟨a.val % 64, Nat.mod_lt _ (by decide)⟩
    simpa only [prefix_recover] using h
  · intro g j a
    have h := hs g j ⟨a.val / 64, by omega⟩ ⟨a.val % 64, Nat.mod_lt _ (by decide)⟩
    simpa only [prefix_recover] using h.1
  · intro g j a
    have h := hs g j ⟨a.val / 64, by omega⟩ ⟨a.val % 64, Nat.mod_lt _ (by decide)⟩
    simpa only [prefix_recover] using h.2

/-- Every original genuine weighted Start word equation is covered by the exact packets. -/
theorem generatedTenth_packed_boundary_start_of_packets
    (h : ∀ g j b, GeneratedTenthPackedBoundaryStartPacketCondition g j b) :
    GeneratedTenthPackedBoundaryStartWords := by
  intro g j a
  have hh := h g j ⟨a.val / 64, by omega⟩ ⟨a.val % 64, Nat.mod_lt _ (by decide)⟩
  simpa only [prefix_recover] using hh

/-- Every genuine post equation and original final cache identity is covered by the exact
packets. -/
theorem generatedTenth_packed_boundary_finish_of_packets
    (h : ∀ g j b, GeneratedTenthPackedBoundaryFinishPacketCondition g j b) :
    GeneratedTenthPackedBoundaryFinishWords := by
  intro g j a
  have hh := h g j ⟨a.val / 64, by omega⟩ ⟨a.val % 64, Nat.mod_lt _ (by decide)⟩
  simpa only [prefix_recover] using hh

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

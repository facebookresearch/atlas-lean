/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsShortMasks
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsSparseCocode

/-! Exact eight-column cocode evaluation for the original preferred short lifts. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative

/-- The original short mask with its octad syndrome evaluated on eight occupied coordinates. -/
def generatedAxisGlobalShortSparseMask : GriessShortIndex → ℕ
  | Sum.inr (Sum.inl (j, e)) => generatedAxisGlobalSourceMaskJoin
      (Nat.xor (generatedAxisGlobalOctadCodeData j).val
        (generatedAxisGlobalOmegaMask (griessOctadOmegaCoefficient e)))
      (Nat.xor (parkerThetaMask (generatedAxisGlobalOctadCodeData j).val)
        (generatedAxisGlobalSparseCocodeMask (generatedAxisGlobalOctadCoordinatesData j)
          (trialityEvenMask e)))
  | r => generatedAxisGlobalShortMask r

/-- Eight-column evaluation retains every binary coordinate of the original short dictionary. -/
theorem generatedAxisGlobalShortSparseMask_decode (r : GriessShortIndex) :
    monsterCo1GeometryBinaryMaskDecode (n := 24) (generatedAxisGlobalShortSparseMask r) =
      monsterCo1GeometryBinaryMaskDecode (n := 24) (generatedAxisGlobalShortMask r) := by
  rcases r with p | (⟨j, e⟩ | p)
  · rfl
  · have hc : Function.Injective (generatedAxisGlobalOctadCoordinatesData j) := by
      intro a b h
      apply golayOctadCoordinate_injective j
      simpa only [generatedAxisGlobalOctadCoordinatesData_actual] using h
    change monsterCo1GeometryBinaryMaskDecode
      (generatedAxisGlobalSourceMaskJoin _ (Nat.xor _
        (generatedAxisGlobalSparseCocodeMask (generatedAxisGlobalOctadCoordinatesData j)
          (trialityEvenMask e)))) =
      monsterCo1GeometryBinaryMaskDecode
        (generatedAxisGlobalSourceMaskJoin _ (Nat.xor _
          (generatedAxisGlobalCocodeMask (generatedAxisGlobalOctadNegativeMask j e))))
    simp only [generatedAxisGlobalSourceMaskJoin_decode,
      monsterCo1GeometryBinaryMaskDecode_xor,
      generatedAxisGlobalSparseCocodeMask_decode _ hc, generatedAxisGlobalCocodeMask_decode]
    rfl
  · rfl

/-- The sparse mask is the full actual preferred-Q element with its original central section. -/
theorem generatedAxisGlobalShortSparseMask_Q_actual (r : GriessShortIndex) :
    generatedAxisGlobalShortQFinite r =
      generatedAxisGlobalQMask (generatedAxisGlobalShortSparseMask r) := by
  apply NormalizedCocycleExtension.Extension.ext
  · apply toAdd.injective
    exact ((generatedAxisGlobalShortSparseMask_decode r).trans
      (generatedAxisGlobalShortMask_decode r)).symm
  · exact generatedAxisGlobalShortQFinite_positive r

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

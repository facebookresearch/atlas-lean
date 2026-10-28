/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthQOrbit
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisQImageInvariance

/-! The genuine local stabilizer preserves the exact 32-class binary image of its Q intersection. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
open Multiplicative

/-- The actual binary image of the full local fifth-axis Q intersection. -/
def generatedFifthAxisBinaryImage : Submodule (ZMod 2) (Fin 24 → ZMod 2) :=
  localNormalQImage (MulAction.stabilizer H generatedFifthAxis)

/-- The binary image consists of exactly the 32 literal translation and modulation pairs. -/
theorem generatedFifth_axis_binary_image_mem (v : Fin 24 → ZMod 2) :
    v ∈ generatedFifthAxisBinaryImage ↔ ∃ b : ZMod 2, ∃ k : Fin 16,
      Fin.append (b • (Pi.single 11 1 : SpinIndex))
        (golayLabelCoefficients (generatedFifthModulationLabels k)) = v := by
  constructor
  · rintro ⟨q, hq, hv⟩
    change q ∈ generatedFifthAxisQStabilizer at hq
    rw [generatedFifth_axis_Q_stabilizer_eq] at hq
    obtain ⟨b, k, rfl⟩ := (generatedFifth_tensor_Q_mem_iff q).mp hq
    refine ⟨b, k, ?_⟩
    exact ofAdd.injective hv
  · rintro ⟨b, k, rfl⟩
    exact mem_localNormalQImage_of_mem (MulAction.stabilizer H generatedFifthAxis)
      (generatedFifthQCandidate b k) (generatedFifth_candidate_full_fixed b k)

/-- Every genuine local axis stabilizer element preserves this exact binary image. -/
theorem generatedFifth_axis_binary_image_invariant (h : H)
    (hh : rhoLocal h generatedFifthAxis = generatedFifthAxis)
    (v : Fin 24 → ZMod 2) (hv : v ∈ generatedFifthAxisBinaryImage) :
    co1BinaryAction (projH h) v ∈ generatedFifthAxisBinaryImage :=
  generatedAxisQImage_invariant (MulAction.stabilizer H generatedFifthAxis) h hh v hv

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

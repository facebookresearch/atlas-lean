/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthSpreadSystemColumns
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisE8FrameSystemsOrbitBasis

/-! Exact compact source-label equations determine the entire original subspace action. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix
set_option backward.isDefEq.respectTransparency false

/-- A compact source equation is the original binary action on its actual root-coordinate basis. -/
theorem generatedNinth_spread_system_basis_of_label (g : Fin 18) (k : Fin 270) (j : Fin 4)
    (hlabel : sixthFrameOrbitMaskApply (generatedNinthSpreadColumns g)
      (generatedAxisE8FrameSystemBasisLabels k j).val =
        (generatedAxisE8FrameSystemCandidateLabel (generatedNinthSpreadSystemTarget g k)
          (generatedNinthSpreadSystemCoefficient g k j)).val) :
    generatedFifthSectionGeneratorBinary g *ᵥ generatedAxisE8FrameSystemCandidateBasis k j =
      generatedAxisE8FrameSystemCandidateMap (generatedNinthSpreadSystemTarget g k)
        (generatedNinthSpreadSystemCoefficient g k j) := by
  rw [← generatedNinth_spread_columns_eq g]
  change sixthFrameOrbitColumnMatrix (generatedNinthSpreadColumns g) *ᵥ
    monsterCo1GeometryBinaryMaskDecode (generatedAxisE8FrameSystemBasisLabels k j).val = _
  rw [← sixthFrameOrbitMaskApply_decode, hlabel, generatedAxisE8FrameSystemCandidateMap_bits]
  rfl

/-- Four checked source equations determine the whole genuine lattice-quotient system image. -/
theorem generatedNinth_spread_system_action_of_labels (g : Fin 18) (k : Fin 270)
    (hlabel : ∀ j : Fin 4, sixthFrameOrbitMaskApply (generatedNinthSpreadColumns g)
      (generatedAxisE8FrameSystemBasisLabels k j).val =
        (generatedAxisE8FrameSystemCandidateLabel (generatedNinthSpreadSystemTarget g k)
          (generatedNinthSpreadSystemCoefficient g k j)).val) :
    generatedAxisE8FrameSystemOrbitLetter g • generatedAxisE8ActualFrameSystemCandidate k =
      generatedAxisE8ActualFrameSystemCandidate (generatedNinthSpreadSystemTarget g k) := by
  apply generatedAxisE8ActualFrameSystemCandidate_action_eq_of_basis
  intro j
  change leechModTwoAction (generatedFifthSectionGenerator g)
    (generatedAxisE8FrameRootEmbedding (generatedAxisE8FrameSystemCandidateBasis k j)) ∈ _
  rw [generatedFifthSectionGenerator_binary,
    generatedNinth_spread_system_basis_of_label g k j (hlabel j)]
  exact Submodule.mem_map.mpr ⟨_, ⟨generatedNinthSpreadSystemCoefficient g k j, rfl⟩, rfl⟩

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

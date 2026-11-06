/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthTensorSourceStages

/-! All original physical coordinates of the eight genuine source tensor factors. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- Complete original physical integer factor vectors at all three nontrivial source stages. -/
def generatedTwelfthTensorSourceSpatialNumerator : Fin 4 → Fin 8 → Fin 24 → ℤ :=
  ![![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0,
    0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0]], ![![-1, -1, 1, 1, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![-1, 1, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, -1, -1, -1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, -1, 1, 1, 0, 0, 0,
    0], ![0, 0, 0, 0, 1, -1, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, -1, -1, -1, -1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    -1, 1, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0]], ![![1, -1, -1, -3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 1, -1, -1, 1, 0, 0, 0, 0], ![1, -1, 3, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, -1,
    1, 0, 0, 0, 0], ![0, 0, 0, 0, 1, -1, -1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 1, -1, -1,
    1], ![0, 0, 0, 0, 1, -1, 1, -1, -1, 1, -1, 1, -1, 1, 1, -1, 0, 0, 0, 0, 1, -1, 1, -1], ![0,
    0, 0, 0, -1, 1, 1, -1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, -1, 1, 1, -1], ![-1, 1, 1, -1,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 1, 3, 0, 0, 0, 0], ![0, 0, 0, 0, 1, -1, 1, -1,
    1, -1, 1, -1, 1, -1, -1, 1, 0, 0, 0, 0, 1, -1, 1, -1], ![1, -1, -1, 1, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 1, -1, 3, 1, 0, 0, 0, 0]], ![![-1, 1, 1, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, -1, 1, 1, -1, 0, 0, 0, 0], ![-1, 1, -3, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1,
    1, -1, 0, 0, 0, 0], ![0, 0, 0, 0, -1, 1, 1, -1, -1, -1, -1, -1, -1, -1, -1, -1, 0, 0, 0, 0,
    -1, 1, 1, -1], ![0, 0, 0, 0, -1, 1, -1, 1, 1, -1, 1, -1, 1, -1, -1, 1, 0, 0, 0, 0, -1, 1,
    -1, 1], ![0, 0, 0, 0, 1, -1, -1, 1, -1, -1, -1, -1, -1, -1, -1, -1, 0, 0, 0, 0, 1, -1, -1,
    1], ![1, -1, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, -1, -3, 0, 0, 0, 0], ![0, 0,
    0, 0, -1, 1, -1, 1, -1, 1, -1, 1, -1, 1, 1, -1, 0, 0, 0, 0, -1, 1, -1, 1], ![-1, 1, 1, -1,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, -3, -1, 0, 0, 0, 0]]]

/-- Every genuine initial physical factor has exactly the full displayed coordinate vector. -/
theorem generatedTwelfth_tensor_source_initial_spatial : ∀ (r : Fin 8) (i : Fin 24),
    generatedTwelfthTensorSourceSpatial r i = generatedTwelfthTensorSourceSpatialNumerator 0 r i := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthRepresentative

/-! The genuine full-axis local stabilizer and its actual extraspecial intersection. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- The original ninth-axis stabilizer in the genuine local group. -/
def generatedNinthLocalAxisStabilizer : Subgroup H :=
  MulAction.stabilizer H generatedNinthAxis

/-- Its intersection with the actual extraspecial subgroup. -/
def generatedNinthAxisQStabilizer : Subgroup Q :=
  generatedNinthLocalAxisStabilizer.comap inclQ

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

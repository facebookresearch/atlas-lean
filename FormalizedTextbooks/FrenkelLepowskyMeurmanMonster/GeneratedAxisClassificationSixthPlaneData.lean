/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthMatrix

/-! Literal rank-two coordinate geometry for the actual sixth watermark. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix BigOperators

/-- The three coordinates on which the actual rooted plane is supported. -/
def generatedSixthPlaneSupport (i : Fin 24) : Prop := i = 16 ∨ i = 17 ∨ i = 19

instance (i : Fin 24) : Decidable (generatedSixthPlaneSupport i) := by
  unfold generatedSixthPlaneSupport
  infer_instance

/-- Three times the orthogonal projection onto the sum-zero plane on the selected triple. -/
def generatedSixthPlaneNumerator : Matrix (Fin 24) (Fin 24) ℤ := fun i j =>
  if generatedSixthPlaneSupport i ∧ generatedSixthPlaneSupport j then
    if i = j then 2 else -1
  else 0

/-- The selected genuine norm-four root in unscaled Leech integer coordinates. -/
def generatedSixthPlaneRoot (i : Fin 24) : ℤ :=
  4 * (if i = 16 then 1 else 0) - 4 * (if i = 17 then 1 else 0)

/-- The literal numerator satisfies its projection equation in the ordinary kernel. -/
theorem generatedSixth_plane_numerator_square :
    generatedSixthPlaneNumerator * generatedSixthPlaneNumerator =
      (3 : ℤ) • generatedSixthPlaneNumerator := by
  decide +kernel

/-- The genuine root lies in the selected plane, with exact integer scaling. -/
theorem generatedSixth_plane_numerator_root :
    generatedSixthPlaneNumerator *ᵥ generatedSixthPlaneRoot =
      (3 : ℤ) • generatedSixthPlaneRoot := by
  decide +kernel

/-- The rooted vector has the authentic shortest-vector integer norm. -/
theorem generatedSixth_plane_root_square :
    ∑ i, generatedSixthPlaneRoot i ^ 2 = 32 := by
  decide +kernel

/-- The numerator is symmetric, as required for an orthogonal projection. -/
theorem generatedSixth_plane_numerator_symm :
    generatedSixthPlaneNumerator.transpose = generatedSixthPlaneNumerator := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

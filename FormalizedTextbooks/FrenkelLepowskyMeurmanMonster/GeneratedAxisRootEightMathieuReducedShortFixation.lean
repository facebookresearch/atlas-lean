/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightMathieuReducedShortCertificate
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightMathieuReducedTensorFixation

/-! Complete actual short fixation from the genuine canonical cache binding.
The tensor fixation of the reduced pair is already unconditional. -/
@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000

/-- Every actual short coordinate, including zeros, is fixed by each of the four actual fibers. -/
theorem generatedRootEight_mathieu_reduced_short_fixation (g : Fin 4)
    (hC : ∀ r : GriessShortIndex,
      (griessConwayEncode generatedRootEightCanonicalPositiveAxis).2.1 r =
        (generatedRootEightCanonicalShortCachedNumerator r : ℝ) / 256) :
    localShortRepresentation (generatedRootEightMathieuReducedShortFiber g)
      (griessConwayEncode generatedRootEightCanonicalPositiveAxis).2.1 =
        (griessConwayEncode generatedRootEightCanonicalPositiveAxis).2.1 :=
  generatedRootEight_mathieu_reduced_short_fixation_of_binding g hC
    (generatedRootEight_mathieu_reduced_short_certificate g)

/-- The two actual reduced certified fibers meet their entire original short obligation. -/
theorem generatedRootEight_mathieu_reduced_short_condition_of_binding (j : Fin 2)
    (hC : ∀ r : GriessShortIndex,
      (griessConwayEncode generatedRootEightCanonicalPositiveAxis).2.1 r =
        (generatedRootEightCanonicalShortCachedNumerator r : ℝ) / 256) :
    generatedRootEightMathieuReducedShortCondition j := by
  fin_cases j
  · exact congrFun (generatedRootEight_mathieu_reduced_short_fixation 0 hC)
  · exact congrFun (generatedRootEight_mathieu_reduced_short_fixation 1 hC)

/-- Complete short cache binding closes both reduced actual whole-axis fixer attainments;
the only selectable phase is a genuine central Q element. -/
theorem generatedRootEight_mathieu_reduced_whole_axis_fixers_of_short_binding (j : Fin 2)
    (hC : ∀ r : GriessShortIndex,
      (griessConwayEncode generatedRootEightCanonicalPositiveAxis).2.1 r =
        (generatedRootEightCanonicalShortCachedNumerator r : ℝ) / 256) :
    ∃ c : ZMod 2,
      rhoLocal (inclQ (qCentral c) * generatedRootEightMathieuReducedCertifiedLocal j)
        generatedRootEightCanonicalPositiveAxis = generatedRootEightCanonicalPositiveAxis :=
  generatedRootEight_mathieu_reduced_tensor_source_fixer_of_short j
    (generatedRootEight_mathieu_reduced_short_condition_of_binding j hC)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

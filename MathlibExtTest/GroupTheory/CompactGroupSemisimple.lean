/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.GroupTheory.CompactGroupSemisimple
import Mathlib.Analysis.Complex.Circle
import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-! # Tests for complete reducibility of compact group representations -/

namespace MathlibExt.GroupTheory.CompactGroupSemisimpleWanted
namespace RepresentationTheory.CompactGroupSemisimple

-- The circle rotates both complex coordinates of this four-dimensional real representation.
example (W : Subrepresentation (Representation.ofDistribMulAction ℝ Circle (ℂ × ℂ))) :
    ∃ K, IsCompl W K :=
  (compact_group_semisimple _ continuous_smul).exists_isCompl W

-- An indiscrete group can be non-Hausdorff and still satisfies the compact group hypotheses.
example {G : Type*} [Group G] [TopologicalSpace G] [IndiscreteTopology G] :
    (Representation.trivial ℝ G (ℝ × ℝ)).IsSemisimpleRepresentation :=
  compact_group_semisimple _ continuous_snd

end RepresentationTheory.CompactGroupSemisimple
end MathlibExt.GroupTheory.CompactGroupSemisimpleWanted

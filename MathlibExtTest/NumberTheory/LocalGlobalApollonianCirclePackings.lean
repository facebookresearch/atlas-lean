/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.NumberTheory.LocalGlobalApollonianCirclePackings

namespace MathlibExt.NumberTheory.LocalGlobalApollonianCirclePackingsWanted
namespace LocalGlobalApollonianCirclePackings

private def seed : integralPrimitiveDescartesQuadruple := ⟨![-3, 5, 8, 8], by decide⟩

-- Check the seed and the full integer-square statement, in particular its zero case.
example : ∀ n : ℤ, n ^ 2 ∉ curvatureSet ⟦seed⟧ := theorem_1_6

example : (0 : ℤ) ∉ curvatureSet ⟦seed⟧ := by simpa [seed] using theorem_1_6 0

-- The exact orbit still contains the curvature obtained by reflecting the first entry.
example : (45 : ℤ) ∈ curvatureSet ⟦seed⟧ := by
  let s : TransformationGroup :=
    ⟨S₁, Subgroup.mem_sup_left (Subgroup.subset_closure (by simp))⟩
  simp only [curvatureSet, Set.mem_iUnion, Set.mem_range]
  refine ⟨s • seed, ?_, 0, ?_⟩
  · rw [MulAction.orbitRel.Quotient.orbit_mk]
    exact ⟨s, rfl⟩
  · decide

end LocalGlobalApollonianCirclePackings
end MathlibExt.NumberTheory.LocalGlobalApollonianCirclePackingsWanted

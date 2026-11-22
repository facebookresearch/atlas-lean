/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.WalkingAdjunction.JoinSliceWeakFunctoriality
import MathlibExt.AlgebraicTopology.SimplicialCategory.WalkingAdjunction.JoinPathSliceFibrations
import MathlibExt.AlgebraicTopology.SimplicialCategory.WalkingAdjunction.TerminalSliceCriterion

/-!
# Intrinsic terminality along an actual categorical equivalence

The original terminal-boundary condition is the existing whole
slice-projection lifting criterion. Since that projection is a genuine
categorical fibration, the native trivial-fibration class dictionary
identifies terminality with categorical weakness of the projection.
The proved whole slice map and its original projection square then
transport terminality by two-out-of-three, retaining the exact point.
-/

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory
open scoped Simplicial

namespace SSet.WalkingAdjunction

/-- In a quasicategory, the intrinsic terminal-boundary condition is
equivalent to weakness of its actual categorical-fibrant slice projection. -/
theorem rightTerminalVertex_iff_slice_categoricalEquivalence
    (H : SSet.{u}) [Quasicategory H] (t : (Δ[0] : SSet.{u}) ⟶ H) :
    RightTerminalVertex t ↔ categoricalEquivalences (sliceOver.proj H t) := by
  constructor
  · intro ht
    exact ((categoricalFibrations_and_categoricalEquivalences_iff
      (sliceOver.proj H t)).mpr
        ((rightTerminalVertex_iff_slice_rlp_I t).mp ht)).2
  · intro hw
    exact (rightTerminalVertex_iff_slice_rlp_I t).mpr
      ((categoricalFibrations_and_categoricalEquivalences_iff
        (sliceOver.proj H t)).mp ⟨categoricalFibrations_sliceOver_proj H t, hw⟩)

/-- An actual categorical equivalence between quasicategories preserves
and reflects intrinsic terminality of the identical original point map. -/
theorem rightTerminalVertex_iff_map_of_categoricalEquivalence
    {X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y]
    (p : X ⟶ Y) (hp : categoricalEquivalences p)
    (t : (Δ[0] : SSet.{u}) ⟶ X) :
    RightTerminalVertex t ↔ RightTerminalVertex (t ≫ p) := by
  rw [rightTerminalVertex_iff_slice_categoricalEquivalence X t,
    rightTerminalVertex_iff_slice_categoricalEquivalence Y (t ≫ p)]
  have hslice := sliceOver_map_categoricalEquivalence t p hp
  have hn := sliceOver.map_proj X t p
  constructor
  · intro ht
    have hpost : categoricalEquivalences (sliceOver.proj X t ≫ p) :=
      (categoricalEquivalences.postcomp_iff _ _ hp).mpr ht
    exact (categoricalEquivalences.precomp_iff _ _ hslice).mp (hn.symm ▸ hpost)
  · intro ht
    have hpre : categoricalEquivalences
        (sliceOver.map X t p ≫ sliceOver.proj Y (t ≫ p)) :=
      (categoricalEquivalences.precomp_iff _ _ hslice).mpr ht
    exact (categoricalEquivalences.postcomp_iff _ _ hp).mp (hn ▸ hpre)

end SSet.WalkingAdjunction

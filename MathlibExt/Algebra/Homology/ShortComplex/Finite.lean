/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.Ab
/-!
# Finiteness of homology of short complexes of abelian groups

For a short complex in `AddCommGrpCat`, finiteness of the middle group
implies finiteness of homology. Its cycles embed into the middle group,
and its homology is a quotient of the cycles.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u w

namespace CategoryTheory.ShortComplex

/-- Homology of a short complex of abelian groups is finite if its middle group is finite. -/
theorem ab_finiteHomology_of_finite_middle
    (S : ShortComplex AddCommGrpCat.{u}) [_root_.Finite S.X₂] : _root_.Finite S.homology := by
  letI : _root_.Finite S.cycles := _root_.Finite.of_injective S.iCycles
    ((AddCommGrpCat.mono_iff_injective _).mp inferInstance)
  exact _root_.Finite.of_surjective S.homologyπ
    ((AddCommGrpCat.epi_iff_surjective _).mp inferInstance)

end CategoryTheory.ShortComplex


end

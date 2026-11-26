/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.GroupTheory.SolubleTorsionLengthKourovka19Problem23Wanted

@[expose] public section

namespace MathlibExt.GroupTheory.SolubleTorsionLengthKourovka19Problem23Wanted

/-- The proved theorem has exactly the stated type. -/
example : existsFinitelyPresentedSolubleTorsionLengthGtTwo :=
  existsFinitelyPresentedSolubleTorsionLengthGtTwo_holds

/-- The zeroth term of the torsion series is the trivial subgroup. -/
example (G : Type*) [Group G] : torsionSeries G 0 = ⊥ := rfl

/-- Every torsion element lies in the first term of the torsion series. -/
example (G : Type*) [Group G] (g : G) (hg : IsOfFinOrder g) : g ∈ torsionSeries G 1 := by
  apply Subgroup.subset_normalClosure
  obtain ⟨n, hn, hgn⟩ := isOfFinOrder_iff_pow_eq_one.mp hg
  exact ⟨n, hn, Subgroup.mem_bot.mpr hgn⟩

/-- The trivial group does not have torsion length greater than two. -/
example : ¬ TorsionLengthGtTwo (Multiplicative (ZMod 1)) := by
  rintro ⟨g, hg, -⟩
  exact hg (by
    have h1 : g = 1 := Subsingleton.elim g 1
    rw [h1]
    exact Subgroup.one_mem _)

end MathlibExt.GroupTheory.SolubleTorsionLengthKourovka19Problem23Wanted

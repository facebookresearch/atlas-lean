/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Matroid.DegreeMap

namespace MathlibExt.Combinatorics.MatroidHodgeTheoryWanted.DegreeMapTest

open MathlibExt.Combinatorics.Matroid.Chow

-- A free matroid on one element has rank one. Its empty flag contributes the unit.
example :
    ∃! d : ChowRing (Matroid.freeOn (Set.univ : Set (Fin 1))) →ₗ[ℝ] ℝ,
      IsDegreeMap (Matroid.freeOn (Set.univ : Set (Fin 1))) 0 d ∧ d 1 = 1 := by
  let M := Matroid.freeOn (Set.univ : Set (Fin 1))
  have : M.Loopless := Matroid.loopless_iff_forall_not_isLoop.mpr
    (fun e _ => Matroid.freeOn_not_isLoop _ e)
  have hr : M.eRank = 0 + 1 := by
    simp [M, Matroid.eRank_freeOn]
  obtain ⟨d, hd, hu⟩ := existsUnique_isDegreeMap M 0 hr
  refine ⟨d, ⟨hd, ?_⟩, fun e he => hu e he.1⟩
  simpa using hd.2 (Fin.elim0 : Fin 0 → ProperFlat M) (Subsingleton.strictMono _)

-- At rank two, every proper-flat generator has degree one and the unit has degree zero.
example {α : Type*} (M : Matroid α) [M.Finite] [M.Loopless]
    (hr : M.eRank = 2) :
    ∃ d : ChowRing M →ₗ[ℝ] ℝ, d 1 = 0 ∧ ∀ F : ProperFlat M, d (x M F) = 1 := by
  obtain ⟨d, hd, _⟩ := existsUnique_isDegreeMap M 1 hr
  refine ⟨d, hd.1 0 (by decide) 1
    ⟨1, MvPolynomial.isHomogeneous_one (ProperFlat M) ℝ, by simp⟩, fun F => ?_⟩
  simpa using hd.2 (fun _ : Fin 1 => F) (Subsingleton.strictMono _)

end MathlibExt.Combinatorics.MatroidHodgeTheoryWanted.DegreeMapTest

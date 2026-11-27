/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
The exact-source consumer below is adapted from:

`Theorems/Thm_LanglandsTunnell_ncard_charpoly_coeff_pair_eq_ncard_symm_pair_
of_finrank_eq_three.lean`
and
`P2M/Sol/S_LanglandsTunnell_ncard_charpoly_coeff_pair_eq_ncard_symm_pair_
of_finrank_eq_three.lean`
(https://github.com/anthropics/fermats-last-theorem):
Compared with the source files at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`.
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits:
Mathlib — https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
-/

import MathlibExt.FieldTheory.Finite.CharpolyCoeffPair

namespace CharpolyCoeffPairTest

/-- Exact-source consumer: the original statement, with its original
binders (`Type`, not `Type*`), is exactly the new theorem. -/
theorem exactSource
    (F : Type) [Field F] [Fintype F] (F' : Type) [Field F'] [Algebra F F'] [Fintype F']
    (h3 : Module.finrank F F' = 3) (t s : F) :
    {y : F' | -(LinearMap.charpoly (Algebra.lmul F F' y)).coeff 2 = t ∧
        (LinearMap.charpoly (Algebra.lmul F F' y)).coeff 1 = s}.ncard
      = {r : F × F × F | r.1 + r.2.1 + r.2.2 = t ∧
          r.1 * r.2.1 + r.2.1 * r.2.2 + r.2.2 * r.1 = s}.ncard :=
  ncard_charpoly_coeff_pair_eq_ncard_symm_pair_of_finrank_eq_three F F' h3 t s

/-- Higher-universe consumer: the new theorem also applies to fields
living in `Type 1`, which the original `Type` statement could not express. -/
theorem exactSourceUniverseOne
    (F : Type 1) [Field F] [Fintype F] (F' : Type 1) [Field F'] [Algebra F F'] [Fintype F']
    (h3 : Module.finrank F F' = 3) (t s : F) :
    {y : F' | -(LinearMap.charpoly (Algebra.lmul F F' y)).coeff 2 = t ∧
        (LinearMap.charpoly (Algebra.lmul F F' y)).coeff 1 = s}.ncard
      = {r : F × F × F | r.1 + r.2.1 + r.2.2 = t ∧
          r.1 * r.2.1 + r.2.1 * r.2.2 + r.2.2 * r.1 = s}.ncard :=
  ncard_charpoly_coeff_pair_eq_ncard_symm_pair_of_finrank_eq_three F F' h3 t s

/-- Boundary example: the degree hypothesis matters. For the degree-one
extension `ZMod 2` over itself, the two counts at `t = s = 0` are `0` and
`1`, so the conclusion fails without `finrank = 3`. -/
example :
    {y : ZMod 2 | -(LinearMap.charpoly (Algebra.lmul (ZMod 2) (ZMod 2) y)).coeff 2 = 0 ∧
        (LinearMap.charpoly (Algebra.lmul (ZMod 2) (ZMod 2) y)).coeff 1 = 0}.ncard
      ≠ {r : ZMod 2 × ZMod 2 × ZMod 2 | r.1 + r.2.1 + r.2.2 = 0 ∧
          r.1 * r.2.1 + r.2.1 * r.2.2 + r.2.2 * r.1 = 0}.ncard := by
  have hleft :
      {y : ZMod 2 | -(LinearMap.charpoly (Algebra.lmul (ZMod 2) (ZMod 2) y)).coeff 2 = 0 ∧
          (LinearMap.charpoly (Algebra.lmul (ZMod 2) (ZMod 2) y)).coeff 1 = 0} = ∅ := by
    ext y
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]
    intro _
    have hdeg : (LinearMap.charpoly (Algebra.lmul (ZMod 2) (ZMod 2) y)).natDegree = 1 := by
      rw [LinearMap.charpoly_natDegree, Module.finrank_self]
    have hcoeff : (LinearMap.charpoly (Algebra.lmul (ZMod 2) (ZMod 2) y)).coeff 1 = 1 := by
      rw [← hdeg]
      exact (LinearMap.charpoly_monic _).coeff_natDegree
    rw [hcoeff]
    exact one_ne_zero
  rw [hleft, Set.ncard_empty, Set.ncard_eq_toFinset_card']
  simp only [Set.toFinset_setOf]
  have hmem : (0, 0, 0) ∈ Finset.univ.filter
      (fun r : ZMod 2 × ZMod 2 × ZMod 2 => r.1 + r.2.1 + r.2.2 = 0 ∧
        r.1 * r.2.1 + r.2.1 * r.2.2 + r.2.2 * r.1 = 0) := by
    simp
  have hpos := Finset.card_pos.mpr ⟨(0, 0, 0), hmem⟩
  omega

end CharpolyCoeffPairTest

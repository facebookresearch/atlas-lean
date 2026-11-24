/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.SimpleGraph.AlgebraicGraphTheory.AlternatingThreeCycleCayleyGraph

/-! # Tests for the generators of the alternating 3-cycle Cayley graph -/

namespace MathlibExtTest.AlternatingThreeCycleCayleyGraph

open MathlibExt.GroupTheory.IntegralCayleyGraphsKourovka19Problem50Wanted

-- Below degree three there is no third point.
example {n : ℕ} (hn : n < 3) : threeCyclesOneTwo n = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  rintro g ⟨a, b, k, ha, hb, hk, he⟩
  omega

private def cycle : Equiv.Perm (Fin 3) :=
  Equiv.swap 0 1 * Equiv.swap 1 2

-- At degree three the forward set consists of a single, oriented cycle.
example : threeCyclesOneTwo 3 = {cycle} := by
  ext g
  constructor
  · rintro ⟨a, b, k, ha, hb, hk, he⟩
    have ea : a = 0 := Fin.ext ha
    have eb : b = 1 := Fin.ext hb
    have ek : k = 2 := Fin.ext (by change k.val = 2; omega)
    simpa [ea, eb, ek, cycle] using he
  · rintro rfl
    exact ⟨0, 1, 2, rfl, rfl, by decide, rfl⟩

-- After including the inverse, the graph at the first allowed degree is the triangle.
example : SimpleGraph.mulCayley
    {g : alternatingGroup (Fin 3) | g.val ∈ threeCyclesOneTwo 3 ∨
      g.val⁻¹ ∈ threeCyclesOneTwo 3} = ⊤ := by
  ext x y
  rw [SimpleGraph.mulCayley_adj, SimpleGraph.top_adj]
  apply and_iff_left_of_imp
  revert x y
  unfold threeCyclesOneTwo
  simp only [Set.mem_ofPred_eq]
  decide

end MathlibExtTest.AlternatingThreeCycleCayleyGraph

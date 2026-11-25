/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Combinatorics.SimpleGraph.Star
import MathlibExt.Combinatorics.SimpleGraph.ErdosProblem800

namespace MathlibExtTest.Combinatorics.SimpleGraph.ErdosProblem800

open MathlibExt.Combinatorics.ErdosProblem800Wanted _root_.SimpleGraph

-- The same constant works for a triangle and stars of every size.
example : ∃ C > (0 : ℝ),
    (diagonalGraphRamsey (⊤ : SimpleGraph (Fin 3)) : ℝ) ≤ C * 3 ∧
      ∀ n : ℕ, (diagonalGraphRamsey (starGraph (0 : Fin (n + 1))) : ℝ) ≤ C * (n + 1) := by
  obtain ⟨C, hC, hbound⟩ := conjecture_holds
  refine ⟨C, hC, ?_, ?_⟩
  · apply hbound 3 (Fin 3) ⊤ (Fintype.card_fin 3)
    intro u v _ hdeg
    have hlt := (⊤ : SimpleGraph (Fin 3)).degree_lt_card_verts u
    exact hlt.not_ge (by simpa using hdeg.1)
  · intro n
    have h := hbound (n + 1) (Fin (n + 1)) (starGraph 0) (Fintype.card_fin _) (by
      intro u v huv hdeg
      by_cases hu : u = 0
      · have hv : v ≠ 0 := fun h => huv.ne (hu.trans h.symm)
        rw [degree_starGraph_of_ne_center hv] at hdeg
        omega
      · rw [degree_starGraph_of_ne_center hu] at hdeg
        omega)
    exact_mod_cast h

-- On an empty vertex type the theorem gives a zero bound.
example : diagonalGraphRamsey (⊥ : SimpleGraph (Fin 0)) = 0 := by
  obtain ⟨C, _, hbound⟩ := conjecture_holds
  have h := hbound 0 (Fin 0) ⊥ (Fintype.card_fin _) (fun u => Fin.elim0 u)
  have hzero : (diagonalGraphRamsey (⊥ : SimpleGraph (Fin 0)) : ℝ) ≤ 0 := by simpa using h
  exact Nat.eq_zero_of_le_zero (by exact_mod_cast hzero)

end MathlibExtTest.Combinatorics.SimpleGraph.ErdosProblem800

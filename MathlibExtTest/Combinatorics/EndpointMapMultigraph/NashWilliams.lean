/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.EndpointMapMultigraph.NashWilliams

@[expose] public section

namespace EndpointMapMultigraphNashWilliamsTest

open EndpointMapMultigraph Matrix

/-- The path `0 - 1 - 2` with unit conductances. -/
abbrev e₁ : Fin 2 → Fin 3 := ![0, 1]
/-- Second endpoints of the path `0 - 1 - 2`. -/
abbrev e₂ : Fin 2 → Fin 3 := ![1, 2]

theorem reach02 : (underlyingGraph e₁ e₂).Reachable 0 2 :=
  ((underlyingGraph_adj_of_ne e₁ e₂ (e := 0) (by decide)).reachable).trans
    ((underlyingGraph_adj_of_ne e₁ e₂ (e := 1) (by decide)).reachable)

/-- The first edge alone separates `0` from `2`. -/
theorem separates_first : Separates e₁ e₂ {0} 0 2 := by
  intro h
  have key : ∀ c, Relation.ReflTransGen (AdjacentUsing e₁ e₂ (Finset.univ \ {0})) 0 c → c = 0 := by
    intro c hc
    induction hc with
    | refl => rfl
    | tail _ hbc ih =>
      subst ih
      unfold AdjacentUsing at hbc
      obtain ⟨e, he, h'⟩ := hbc
      fin_cases e <;> simp_all
  exact absurd (key 2 h) (by decide)

/-- The second edge alone separates `0` from `2`. -/
theorem separates_second : Separates e₁ e₂ {1} 0 2 := by
  intro h
  have key : ∀ c, Relation.ReflTransGen (AdjacentUsing e₁ e₂ (Finset.univ \ {1})) 0 c →
      c = 0 ∨ c = 1 := by
    intro c hc
    induction hc with
    | refl => exact Or.inl rfl
    | tail _ hbc ih =>
      unfold AdjacentUsing at hbc
      obtain ⟨e, he, h'⟩ := hbc
      rcases ih with rfl | rfl <;> fin_cases e <;> simp_all
  rcases key 2 h with h2 | h2 <;> exact absurd h2 (by decide)

/-- Nash-Williams on the path: the two single-edge cutsets give `1 + 1 ≤ R_eff(0, 2)`, which is
sharp since `R_eff(0, 2) = 2`. -/
example : (2 : ℝ) ≤ effectiveResistance e₁ e₂ (fun _ => 1) 0 2 := by
  have h := sum_inv_le_effectiveResistance e₁ e₂ (w := fun _ => 1) (fun _ => one_pos)
    (by decide) (by decide) reach02 (Finset.univ : Finset (Fin 2)) (fun k => {k})
    (by intro i _ j _ hij; simpa [Function.onFun] using hij)
    (by intro k _; fin_cases k
        · exact separates_first
        · exact separates_second)
  simpa [Fin.sum_univ_two] using h.trans_eq' (by norm_num)

end EndpointMapMultigraphNashWilliamsTest

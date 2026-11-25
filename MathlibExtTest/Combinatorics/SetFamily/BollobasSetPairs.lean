/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.SetFamily.BollobasSetPairs

@[expose] public section

open Finset MathlibExt.Combinatorics.SetFamily.BollobasSetPairs

namespace MathlibExtTest.Combinatorics.SetFamily.BollobasSetPairs

/-- The extremal system: the `a`-subsets `S` of `Fin (a + b)` paired with their complements form a
set-pair system, so the uniform bound applies to it (and is attained, since there are exactly
`C(a + b, a)` such subsets). -/
example (a b : ℕ) :
    #(powersetCard a (univ : Finset (Fin (a + b)))) ≤ (a + b).choose a := by
  refine card_le_choose _ id (fun S => Sᶜ) a b (fun S hS => (mem_powersetCard.1 hS).2)
    (fun S hS => ?_) (fun S _ => disjoint_compl_right) ?_
  · simp [card_compl, (mem_powersetCard.1 hS).2]
  · intro S hS T hT hST hd
    apply hST
    have hsub : S ⊆ T := fun x hx => by
      by_contra hxT
      exact disjoint_left.1 hd hx (mem_compl.2 hxT)
    exact eq_of_subset_of_card_le hsub
      (by rw [(mem_powersetCard.1 hS).2, (mem_powersetCard.1 hT).2])

/-- A non-uniform system with two pairs: `({0}, {1, 2})` and `({1}, {0})`; the weights are
`C(3, 1)⁻¹ + C(2, 1)⁻¹ = 1/3 + 1/2 ≤ 1`. -/
example : ∑ i ∈ ({0, 1} : Finset ℕ),
    ((#({i} : Finset ℕ) + #(if i = 0 then ({1, 2} : Finset ℕ) else {0})).choose
      #({i} : Finset ℕ) : ℚ)⁻¹ ≤ 1 :=
  sum_inv_choose_le_one _ (fun i => {i}) (fun i => if i = 0 then {1, 2} else {0})
    (by decide) (by decide)

/-- The bridge reproduces Mathlib's LYM inequality for an antichain of subsets of `Fin 3`. -/
example (𝒜 : Finset (Finset (Fin 3))) (h𝒜 : IsAntichain (· ⊆ ·) (SetLike.coe 𝒜)) :
    ∑ S ∈ 𝒜, ((Fintype.card (Fin 3)).choose #S : ℚ)⁻¹ ≤ 1 :=
  lym_of_sum_inv_choose_le_one h𝒜

end MathlibExtTest.Combinatorics.SetFamily.BollobasSetPairs

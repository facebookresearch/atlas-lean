/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import
  MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.Joyal.ShuffleCobase

/-! Tests for the `Δ[n] ⊗ Δ[2]` shuffle infrastructure of packet
T52 (landed prefix): shuffle-chain arithmetic, coordinate values
and ranges of the top simplices `τ_{a,b}`. -/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalClosed MonoidalCategory Opposite

open scoped Simplicial

namespace SSet

section Signatures

#check @SSet.shuffleSnd
#check @SSet.shuffleFst
#check @SSet.shuffleSnd_eq_zero
#check @SSet.shuffleSnd_eq_one
#check @SSet.shuffleSnd_eq_two
#check @SSet.shuffleFst_add_snd
#check @SSet.shuffleFst_eq_iff
#check @SSet.shuffleFst_le_of_le
#check @SSet.shuffleSnd_succ_left
#check @SSet.shuffleSnd_succ_right
#check @SSet.shuffleSnd_pred_left
#check @SSet.shuffleSnd_pred_right
#check @SSet.shuffleTau
#check @SSet.shuffleTauMap
#check @SSet.shuffleTau_objEquiv_fst_val
#check @SSet.shuffleTau_objEquiv_snd_val
#check @SSet.shuffleTau_objEquiv_apply_eq_iff
#check @SSet.mem_range_shuffleTau_objEquiv

end Signatures

section Arithmetic

/-- Threshold values of `shuffleSnd 1 3` and the
`fst + snd = t` identity, at concrete positions. -/
example : shuffleSnd 1 3 0 = 0 := rfl

example : shuffleSnd 1 3 1 = 0 := rfl

example : shuffleSnd 1 3 2 = 1 := rfl

example : shuffleSnd 1 3 4 = 1 := rfl

example : shuffleSnd 1 3 5 = 2 := rfl

example : shuffleFst 1 3 5 + shuffleSnd 1 3 5 = 5 :=
  shuffleFst_add_snd 1 3 5

example : shuffleSnd 1 3 4 = 1 :=
  shuffleSnd_eq_one.2 ⟨by omega, by omega⟩

example (hab : (2 : ℕ) ≤ 5) : shuffleFst 2 5 7 = 5 ↔
    (7 = 5 ∧ 5 ≤ 2) ∨ (7 = 5 + 1 ∧ 2 ≤ 5 ∧ 5 ≤ 5) ∨ (7 = 5 + 2 ∧ 5 ≤ 5) :=
  shuffleFst_eq_iff hab

end Arithmetic

section Ranges

/-- `(0,1)` and `(4,2)` are in the range of `τ_{1,3}` over
`Δ[5]`; `(5,0)` is not. -/
example : ((0 : Fin 6), (0 : Fin 3)) ∈
    Set.range (prodStdSimplex.objEquiv.{u}
      (shuffleTau 5 1 3 (by omega) (by omega))) :=
  (mem_range_shuffleTau_objEquiv (by omega) (by omega)).2
    (Or.inl ⟨rfl, by decide⟩)

example : (⟨4, by omega⟩, (2 : Fin 3)) ∈
    Set.range (prodStdSimplex.objEquiv.{u}
      (shuffleTau 5 1 3 (by omega) (by omega))) :=
  (mem_range_shuffleTau_objEquiv (by omega) (by omega)).2
    (Or.inr (Or.inr ⟨rfl, by decide⟩))

example : (⟨5, by omega⟩, (0 : Fin 3)) ∉
    Set.range (prodStdSimplex.objEquiv.{u}
      (shuffleTau 5 1 3 (by omega) (by omega))) := by
  rw [mem_range_shuffleTau_objEquiv (by omega) (by omega)]
  rintro (⟨-, h⟩ | ⟨h, -⟩ | ⟨h, -⟩)
  · exact absurd h (by decide)
  · exact absurd h (by decide)
  · exact absurd h (by decide)

/-- Values of `τ_{0,0}` over `Δ[0]`: the chain is
`(0,0), (0,1), (0,2)`. -/
example (t : Fin 3) :
    ((prodStdSimplex.objEquiv.{u}
      (shuffleTau 0 0 0 (by omega) (by omega)) t).1).val = 0 := by
  rw [shuffleTau_objEquiv_fst_val]
  have ht := t.2
  unfold shuffleFst shuffleSnd
  split_ifs <;> omega

end Ranges

end SSet

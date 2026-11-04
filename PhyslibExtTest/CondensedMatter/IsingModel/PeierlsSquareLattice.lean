/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.CondensedMatter.IsingModel.PeierlsSquareLattice

/-!
# Tests for `PhyslibExt.CondensedMatter.IsingModel.OuterContourWindingClose`

* At infinite temperature (`β = 0`) the plus-boundary box measure on `ℤ^d` makes the origin minus
  with probability exactly `1/2`, in every box (`probOriginMinus_beta_zero`).
* `peierls_probOriginMinus_le_uniform` gives a `β₀` beyond which the origin is minus with
  probability `≤ twoPeierlsBound 2 β < 1/2`, uniformly in the box. Combined with the previous item,
  every such `β₀` is positive: the bound is a genuine low-temperature statement and cannot hold at
  `β = 0`.
* `peierls_long_range_order_spinCompatibleFill` applies at `β₀` and every box.
-/

@[expose] public section

namespace PhyslibExtTest.CondensedMatter.IsingModel.OuterContourWindingClose

open _root_.StatMech _root_.StatMech.Ising _root_.StatMech.Lattice

/-- At `β = 0`, flipping the origin spin preserves the box probabilities, so the origin is minus
with probability `1/2` under the plus-boundary box measure, in every box. -/
lemma probOriginMinus_beta_zero (d n : ℕ) :
    probOriginMinus (plusField d) n (bondFinsetTouch d n) 0 0 = 1 / 2 := by
  set o : {x // x ∈ box d n} := ⟨origin d, origin_mem_box n⟩
  set p := fvProb (plusField d) n (bondFinsetTouch d n) 0 0
  -- At `β = 0` every inside configuration has the same probability.
  have hconst : ∀ τ τ', p τ = p τ' := fun τ τ' => by
    simp [p, fvProb, fvWeight]
  -- Flipping the origin spin.
  let e : ({x // x ∈ box d n} → Bool) ≃ ({x // x ∈ box d n} → Bool) :=
    { toFun := fun τ => Function.update τ o (!τ o)
      invFun := fun τ => Function.update τ o (!τ o)
      left_inv := fun τ => by ext x; by_cases hx : x = o <;> simp [hx]
      right_inv := fun τ => by ext x; by_cases hx : x = o <;> simp [hx] }
  have hglue : ∀ τ : {x // x ∈ box d n} → Bool, glue (plusField d) τ (origin d) = τ o :=
    fun τ => glue_mem _ _ (origin_mem_box n)
  have hflip : (∑ τ, if τ o = false then p τ else 0) = ∑ τ, if τ o = true then p τ else 0 := by
    rw [← Equiv.sum_comp e]
    refine Finset.sum_congr rfl fun τ _ => ?_
    simp only [e, Equiv.coe_fn_mk, Function.update_self, Bool.not_eq_false']
    split_ifs <;> first | rfl | exact hconst _ _
  have hsum : (∑ τ, if τ o = false then p τ else 0) + (∑ τ, if τ o = true then p τ else 0) = 1 := by
    rw [← Finset.sum_add_distrib, ← fvProb_sum_eq_one (plusField d) n (bondFinsetTouch d n) 0 0]
    refine Finset.sum_congr rfl fun τ _ => ?_
    cases τ o <;> simp [p]
  unfold probOriginMinus
  simp only [hglue]
  change (∑ τ, if τ o = false then p τ else 0) = 1 / 2
  linarith

-- The Peierls bound: for `β ≥ β₀` the origin is minus with probability below `1/2`, in every box.
example : ∃ β₀ : ℝ, ∀ β : ℝ, β₀ ≤ β → ∀ n : ℕ,
    probOriginMinus (plusField 2) n (bondFinsetTouch 2 n) β 0 < 1 / 2 := by
  obtain ⟨β₀, hβ₀⟩ := peierls_probOriginMinus_le_uniform
  exact ⟨β₀, fun β hβ n => ((hβ₀ β hβ).2 n).trans_lt (hβ₀ β hβ).1⟩

-- Every threshold `β₀` in the Peierls bound is positive: the bound fails at `β = 0`.
example (β₀ : ℝ) (hβ₀ : ∀ β : ℝ, β₀ ≤ β → twoPeierlsBound 2 β < 1 / 2 ∧
      ∀ n : ℕ, probOriginMinus (plusField 2) n (bondFinsetTouch 2 n) β 0 ≤ twoPeierlsBound 2 β) :
    0 < β₀ := by
  by_contra hle
  have h := hβ₀ 0 (not_lt.mp hle)
  have := (h.2 0).trans_lt h.1
  rw [probOriginMinus_beta_zero] at this
  exact lt_irrefl _ this

-- The (weak) long-range order statement applies at its threshold, in every box.
example : ∃ β₀ : ℝ, ∀ n : ℕ, plusMeasure 2 n β₀ 0 ≠ minusMeasure 2 n β₀ 0 := by
  obtain ⟨β₀, hβ₀⟩ := peierls_long_range_order_spinCompatibleFill
  exact ⟨β₀, fun n => hβ₀ n β₀ le_rfl⟩

end PhyslibExtTest.CondensedMatter.IsingModel.OuterContourWindingClose

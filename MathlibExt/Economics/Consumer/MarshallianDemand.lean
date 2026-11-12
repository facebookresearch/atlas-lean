/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Normed.Order.Lattice
public import Mathlib.Data.Matrix.Mul

@[expose] public section

/-!
# Budget sets and existence of Marshallian demand (Atlas EC02.T01)

Source: J. Levin, *Consumer Theory*, Stanford Econ 202 lecture notes (2004), §1 (budget set
`B(p, w) = {x ∈ ℝⁿ₊ : p · x ≤ w}`), §2, Proposition 1 (if `p ≫ 0` then `B(p, w)` is compact) and
Proposition 2 (Existence: if `u` is continuous and `p ≫ 0`, the consumer problem has a
solution). Continuity is only needed on the budget set; nonemptiness of `B(p, w)` is a stated
hypothesis (it holds iff `w ≥ 0`).
-/

namespace MathlibExt.Economics.Consumer

/-- The budget set `B(p, w) = {x ∈ ℝ^L_+ : p · x ≤ w}` (Levin, *Consumer Theory*, §1): nonnegative
bundles whose cost at prices `p` is at most the wealth `w`. -/
def budgetSet {L : Type*} [Fintype L] (p : L → ℝ) (w : ℝ) : Set (L → ℝ) :=
  {x | 0 ≤ x ∧ p ⬝ᵥ x ≤ w}

/-- Marshallian demand `x(p, w)` (Levin, *Consumer Theory*, §2): the set of solutions of the
consumer problem `max u(x)` subject to `x ∈ B(p, w)`. It is a correspondence (a set of bundles),
not a function. -/
def marshallianDemand {L : Type*} [Fintype L] (u : (L → ℝ) → ℝ) (p : L → ℝ) (w : ℝ) :
    Set (L → ℝ) :=
  {x | x ∈ budgetSet p w ∧ ∀ y ∈ budgetSet p w, u y ≤ u x}

/-- Each coordinate of a budget-feasible bundle is bounded by `|w| / p l`: the term
`p l * x l` is at most the whole (nonnegative-term) dot product, which is at most `w ≤ |w|`. -/
theorem coord_le_of_mem_budgetSet {L : Type*} [Fintype L] {p : L → ℝ} {w : ℝ} {x : L → ℝ}
    (hp : ∀ l, 0 < p l) (hx : x ∈ budgetSet p w) (l : L) : x l ≤ |w| / p l := by
  obtain ⟨hyle, hcost⟩ := hx
  have hterm : p l * x l ≤ p ⬝ᵥ x :=
    Finset.single_le_sum (fun i _ => mul_nonneg (le_of_lt (hp i)) (hyle i)) (Finset.mem_univ l)
  have hle : p l * x l ≤ |w| := le_trans hterm (le_trans hcost (le_abs_self w))
  rw [le_div_iff₀ (hp l)]
  calc x l * p l = p l * x l := mul_comm _ _
    _ ≤ |w| := hle

/-- Levin, Proposition 1: with strictly positive prices the budget set is compact. -/
theorem isCompact_budgetSet {L : Type*} [Fintype L] {p : L → ℝ} (hp : ∀ l, 0 < p l) (w : ℝ) :
    IsCompact (budgetSet p w) := by
  apply Metric.isCompact_of_isClosed_isBounded
  · have hnonneg : IsClosed {x : L → ℝ | 0 ≤ x} := by
      have heq : {x : L → ℝ | 0 ≤ x} = ⋂ l, {x | (0 : ℝ) ≤ x l} := by
        ext x
        simp [Pi.le_def]
      rw [heq]
      exact isClosed_iInter fun l => isClosed_le continuous_const (continuous_apply l)
    have hcont : Continuous fun x : L → ℝ => p ⬝ᵥ x := by
      simp only [dotProduct]
      exact continuous_finsetSum _ fun l _ => continuous_const.mul (continuous_apply l)
    have hcost : IsClosed {x : L → ℝ | p ⬝ᵥ x ≤ w} := isClosed_le hcont continuous_const
    have heq : budgetSet p w = {x : L → ℝ | 0 ≤ x} ∩ {x : L → ℝ | p ⬝ᵥ x ≤ w} :=
      Set.ext fun x => Iff.rfl
    rw [heq]
    exact hnonneg.inter hcost
  · have hsub : budgetSet p w ⊆ {x : L → ℝ | ∀ l, x l ∈ Set.Icc 0 (|w| / p l)} := by
      intro x hx l
      exact ⟨hx.1 l, coord_le_of_mem_budgetSet hp hx l⟩
    exact (isCompact_pi_infinite (s := fun l : L => Set.Icc (0 : ℝ) (|w| / p l))
      fun l => isCompact_Icc).isBounded.subset hsub

/-- Levin, Proposition 2 (Existence): a utility continuous on a nonempty budget set with strictly
positive prices attains its maximum there, so Marshallian demand is nonempty. -/
theorem marshallianDemand_nonempty {L : Type*} [Fintype L] {u : (L → ℝ) → ℝ} {p : L → ℝ}
    {w : ℝ} (hp : ∀ l, 0 < p l) (hB : (budgetSet p w).Nonempty)
    (hu : ContinuousOn u (budgetSet p w)) : (marshallianDemand u p w).Nonempty := by
  obtain ⟨x, hxm, hmax⟩ := (isCompact_budgetSet hp w).exists_isMaxOn hB hu
  exact ⟨x, hxm, fun y hy => Filter.eventually_principal.mp hmax y hy⟩

end MathlibExt.Economics.Consumer

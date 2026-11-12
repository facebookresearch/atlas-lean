/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Economics.Consumer.TwoGood
public import MathlibExt.Economics.SecondWelfareTheorem

@[expose] public section

/-!
# Existence of Marshallian demand (Atlas EC02.T01)

Source: J. Levin, *Consumer Theory*, Stanford Econ 202 lecture notes (2004), §1 (budget set
`B(p, w) = {x ∈ ℝⁿ₊ : p · x ≤ w}`), §2, Proposition 1 (if `p ≫ 0` then `B(p, w)` is compact) and
Proposition 2 (Existence: if `u` is continuous and `p ≫ 0`, the consumer problem has a
solution). Here the consumption set is `ℝ^L_+` (`SecondWelfareTheorem.consumptionSet L`),
continuity is only needed on the budget set, and nonemptiness of `B(p, w)` is a stated
hypothesis (it holds iff `w ≥ 0`).
-/

namespace MathlibExt.Economics.Consumer

open Matrix

open SecondWelfareTheorem (consumptionSet)

/-- Each coordinate of a budget-feasible bundle is bounded by `|w| / p l`. -/
theorem coord_le_of_mem_budgetSet_consumptionSet {L : Type*} [Fintype L] {p : L → ℝ}
    {w : ℝ} {x : L → ℝ} (hp : ∀ l, 0 < p l)
    (hx : x ∈ budgetSet (consumptionSet L) p w) (l : L) : x l ≤ |w| / p l := by
  obtain ⟨hxmem, hcost⟩ := hx
  have hxnn : ∀ i, 0 ≤ x i := hxmem
  have hterm : p l * x l ≤ p ⬝ᵥ x :=
    Finset.single_le_sum (fun i _ => mul_nonneg (le_of_lt (hp i)) (hxnn i))
      (Finset.mem_univ l)
  have hle : p l * x l ≤ |w| := le_trans hterm (le_trans hcost (le_abs_self w))
  rw [le_div_iff₀ (hp l)]
  calc x l * p l = p l * x l := mul_comm _ _
    _ ≤ |w| := hle

/-- Levin, Proposition 1: with strictly positive prices the budget set in `ℝ^L_+` is compact. -/
theorem isCompact_budgetSet_consumptionSet {L : Type*} [Fintype L] {p : L → ℝ}
    (hp : ∀ l, 0 < p l) (w : ℝ) : IsCompact (budgetSet (consumptionSet L) p w) := by
  apply Metric.isCompact_of_isClosed_isBounded
  · have hnonneg : IsClosed (consumptionSet L) := by
      have heq : consumptionSet L = ⋂ l, {x : L → ℝ | (0 : ℝ) ≤ x l} := by
        ext x
        simp only [MathlibExt.Economics.SecondWelfareTheorem.consumptionSet,
          Set.mem_ofPred_eq, Set.mem_iInter]
      rw [heq]
      exact isClosed_iInter fun l => isClosed_le continuous_const (continuous_apply l)
    have hcont : Continuous fun x : L → ℝ => p ⬝ᵥ x := by
      simp only [dotProduct]
      exact continuous_finsetSum _ fun l _ => continuous_const.mul (continuous_apply l)
    have hcost : IsClosed {x : L → ℝ | p ⬝ᵥ x ≤ w} := isClosed_le hcont continuous_const
    have heq : budgetSet (consumptionSet L) p w =
        consumptionSet L ∩ {x : L → ℝ | p ⬝ᵥ x ≤ w} :=
      Set.ext fun x => Iff.rfl
    rw [heq]
    exact hnonneg.inter hcost
  · have hsub : budgetSet (consumptionSet L) p w ⊆
        {x : L → ℝ | ∀ l, x l ∈ Set.Icc 0 (|w| / p l)} := by
      intro x hx l
      have hxnn : ∀ i, 0 ≤ x i := hx.1
      exact ⟨hxnn l, coord_le_of_mem_budgetSet_consumptionSet hp hx l⟩
    exact (isCompact_pi_infinite (s := fun l : L => Set.Icc (0 : ℝ) (|w| / p l))
      fun l => isCompact_Icc).isBounded.subset hsub

/-- Levin, Proposition 2 (Existence): a utility continuous on a nonempty budget set in `ℝ^L_+`
with strictly positive prices attains its maximum there, so a Marshallian demand exists. -/
theorem exists_isMarshallianDemand {L : Type*} [Fintype L] {u : (L → ℝ) → ℝ} {p : L → ℝ}
    {w : ℝ} (hp : ∀ l, 0 < p l) (hB : (budgetSet (consumptionSet L) p w).Nonempty)
    (hu : ContinuousOn u (budgetSet (consumptionSet L) p w)) :
    ∃ x, IsMarshallianDemand u (consumptionSet L) p w x := by
  obtain ⟨x, hxm, hmax⟩ := (isCompact_budgetSet_consumptionSet hp w).exists_isMaxOn hB hu
  exact ⟨x, hxm, fun y hy => Filter.eventually_principal.mp hmax y hy⟩

end MathlibExt.Economics.Consumer
